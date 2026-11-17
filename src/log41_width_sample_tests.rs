//! Bounded column-kernel sample; deliberately no proof, opening, or full setup.
use super::*;
use blake2::{Blake2b512, Digest};
use serde_json::json;
use std::sync::atomic::{AtomicU64, Ordering};

const ROWS: usize = 8;
const NU: usize = 3;
const LOG41_SIGMA: usize = 21;
static NEXT: AtomicU64 = AtomicU64::new(0);

fn weights() -> Vec<ArkFr> {
    [1u64, 3, 7, 11, 17, 23, 31, 47]
        .into_iter()
        .map(|n| ArkFr(Fr::from(n)))
        .collect()
}

fn fixture(width: usize) -> Vec<u8> {
    assert!(width >= 8 && width.is_power_of_two());
    let row_bytes = width / 8;
    let mut bytes = vec![0; ROWS * row_bytes];
    // Zero; one-hot first/window/byte/final-column boundaries; alternating; dense.
    for (row, col) in [(1, 0), (2, 3), (3, 4), (4, 7), (5, width - 1)] {
        bytes[row * row_bytes + col / 8] |= 1 << (col % 8);
    }
    bytes[6 * row_bytes..7 * row_bytes].fill(0x55);
    let mut state = 0x9e37_79b9_7f4a_7c15u64;
    for byte in &mut bytes[7 * row_bytes..] {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        *byte = state as u8;
    }
    bytes
}

struct FixtureFile(PathBuf);
impl FixtureFile {
    fn new(bytes: &[u8]) -> Self {
        let path = std::env::temp_dir().join(format!(
            "log41-width-{}-{}.bits",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .unwrap();
        file.write_all(bytes).unwrap();
        file.sync_all().unwrap();
        Self(path)
    }
}
impl Drop for FixtureFile {
    fn drop(&mut self) {
        std::fs::remove_file(&self.0).unwrap();
    }
}

fn reference_product(bytes: &[u8], width: usize, left: &[ArkFr]) -> Vec<ArkFr> {
    (0..width)
        .map(|column| {
            let mut value = Fr::zero();
            for row in 0..ROWS {
                if bytes[row * (width / 8) + column / 8] & (1 << (column % 8)) != 0 {
                    value += left[row].0;
                }
            }
            ArkFr(value)
        })
        .collect()
}

#[test]
fn log41_width_g1_prefix_controls() {
    for log_n in [0, 1, 5, 6, 10] {
        let setup = pcs::generate_setup(log_n).unwrap();
        let (prefix, stats) =
            pcs::g1_primary_prefix_for_width_test(log_n, setup.prover.g1_vec.len()).unwrap();
        assert_eq!(prefix, setup.prover.g1_vec);
        for (point, original) in prefix.iter().zip(&setup.prover.g1_vec) {
            assert_eq!(
                pcs::encode(&point.0).unwrap(),
                pcs::encode(&original.0).unwrap()
            );
        }
        let unique = prefix
            .iter()
            .map(|p| pcs::encode(&p.0).unwrap())
            .collect::<std::collections::HashSet<_>>();
        assert_eq!(unique.len(), prefix.len());
        assert_eq!(stats.points_capacity, prefix.len());
        assert!(stats.sampling_attempts >= prefix.len());
        assert!(prefix.iter().all(|point| !point.0.is_zero()));
    }
    let (a, _) = pcs::g1_primary_prefix_for_width_test(41, 8).unwrap();
    let (b, _) = pcs::g1_primary_prefix_for_width_test(41, 8).unwrap();
    let (other_dimension, _) = pcs::g1_primary_prefix_for_width_test(24, 8).unwrap();
    assert_eq!(a, b);
    assert_ne!(a, other_dimension);
    assert!(pcs::g1_primary_prefix_for_width_test(42, 1).is_err());
    assert!(pcs::g1_primary_prefix_for_width_test(0, 2).is_err());
    let mut first = None;
    let (injected, stats) =
        pcs::g1_primary_prefix_for_width_test_with(41, 2, |index, attempt, point| {
            match (index, attempt) {
                (0, 0) => *point = G1Projective::zero(),
                (0, 1) => first = Some(*point),
                (1, 0) => *point = first.unwrap(),
                _ => {}
            }
        })
        .unwrap();
    assert_eq!(stats.sampling_attempts, 4);
    assert!(injected.iter().all(|p| !p.0.is_zero()));
    assert_ne!(injected[0], injected[1]);
    let exhausted = pcs::g1_primary_prefix_for_width_test_with(41, 1, |_, _, point| {
        *point = G1Projective::zero()
    });
    assert_eq!(exhausted.unwrap_err(), "G1 generator admission failed");
}

#[test]
fn log41_width_borrowed_table_exact_semantics() {
    let setup = pcs::generate_setup(10).unwrap();
    for width in [0usize, 1, 2, 3, 4, 5, 7, 8, 31, 32] {
        for chunk in [16, 48, 32768] {
            let (old_windows, old_table, _) =
                commit_subset_table_chunked(&setup, width, chunk).unwrap();
            let (windows, table, _) =
                commit_subset_table_chunked_from_g1(&setup.prover.g1_vec, width, chunk).unwrap();
            let tuples = |ws: &[CommitWindow]| {
                ws.iter()
                    .map(|w| (w.start, w.width, w.table_offset))
                    .collect::<Vec<_>>()
            };
            assert_eq!(tuples(&windows), tuples(&old_windows));
            assert_eq!(table, old_table);
            // Independent direct sum for every entry, including zero and partial windows.
            for window in &windows {
                for mask in 0..1usize << window.width {
                    let mut expected = G1Projective::zero();
                    for bit in 0..window.width {
                        if mask & (1 << bit) != 0 {
                            expected += setup.prover.g1_vec[window.start + bit].0;
                        }
                    }
                    assert_eq!(table[window.table_offset + mask], expected.into_affine());
                }
            }
        }
    }
    assert!(commit_subset_table_chunked_from_g1(&setup.prover.g1_vec, 33, 16).is_err());
    for chunk in [0, 15, 17, 32784] {
        assert!(commit_subset_table_chunked_from_g1(&setup.prover.g1_vec, 8, chunk).is_err());
    }
}

fn run_sample(sigma: usize) {
    let started = Instant::now();
    let width = 1usize << sigma;
    let row_bytes = width / 8;
    let max_batch_bytes = 3 * row_bytes; // 3 + 3 + 2 rows, including a partial last batch.
    let bytes = fixture(width);
    let file = FixtureFile::new(&bytes);
    let source = PackedFile::open(&file.0, NU + sigma).unwrap();
    let fixture_seconds = started.elapsed().as_secs_f64();
    assert_eq!(source.input_len(), ROWS * width);
    let phase = Instant::now();
    let (g1, g1_stats) = pcs::g1_primary_prefix_for_width_test(41, width).unwrap();
    let g1_prefix_seconds = phase.elapsed().as_secs_f64();
    eprintln!(
        "{}",
        json!({"phase":"g1-primary-prefix-only", "width":width,
        "seconds":g1_prefix_seconds,"stats":format!("{g1_stats:?}"),
        "full_setup":false,"g2_points":0,"verifier_setup":false})
    );
    let phase = Instant::now();
    let (windows, table, table_stats) =
        commit_subset_table_chunked_from_g1(&g1, width, SUBSET_CHUNK_ENTRIES).unwrap();
    let table_seconds = phase.elapsed().as_secs_f64();
    assert_eq!(table.len(), 4 * width);
    assert_eq!(
        table_stats.projective_capacity,
        (4 * width).min(SUBSET_CHUNK_ENTRIES)
    );
    eprintln!(
        "{}",
        json!({"phase":"subset-table", "seconds":table_seconds,
        "entries":table.len(),"normalization_calls":table_stats.normalization_calls})
    );
    source.reset_io_metrics();
    let phase = Instant::now();
    let rows =
        commit_rows_batched_with_limit(&source, &windows, &table, width, ROWS, max_batch_bytes)
            .unwrap();
    let commit_seconds = phase.elapsed().as_secs_f64();
    let commit_io = source.io_metrics_snapshot();
    assert_eq!(commit_io.read_calls, 3);
    assert_eq!(commit_io.read_bytes, bytes.len() as u64);
    assert_eq!(rows[0], ArkG1(G1Projective::zero()));
    for (row, column) in [(1, 0), (2, 3), (3, 4), (4, 7), (5, width - 1)] {
        assert_eq!(rows[row], g1[column]);
    }
    let left = weights();
    source.reset_io_metrics();
    let phase = Instant::now();
    let product = source
        .vector_product_with_limit(&left, NU, sigma, max_batch_bytes)
        .unwrap();
    let product_seconds = phase.elapsed().as_secs_f64();
    let product_io = source.io_metrics_snapshot();
    assert_eq!(product_io.read_calls, 3);
    assert_eq!(product_io.read_bytes, bytes.len() as u64);
    let phase = Instant::now();
    assert_eq!(product, reference_product(&bytes, width, &left));
    let reference_seconds = phase.elapsed().as_secs_f64();
    let phase = Instant::now();
    // Each changed input is isolated; unchanged dense/alternating rows are controls.
    for final_column in [false, true] {
        let mut mutated = bytes.clone();
        if final_column {
            mutated[5 * row_bytes + (width - 1) / 8] ^= 1 << ((width - 1) % 8);
        } else {
            for byte in 0..row_bytes {
                mutated.swap(row_bytes + byte, 2 * row_bytes + byte);
            }
        }
        let changed_file = FixtureFile::new(&mutated);
        let changed = PackedFile::open(&changed_file.0, NU + sigma).unwrap();
        let changed_rows = commit_rows_batched_with_limit(
            &changed,
            &windows,
            &table,
            width,
            ROWS,
            max_batch_bytes,
        )
        .unwrap();
        let changed_product = changed
            .vector_product_with_limit(&left, NU, sigma, max_batch_bytes)
            .unwrap();
        assert_eq!(changed_product, reference_product(&mutated, width, &left));
        assert_ne!(changed_product, product);
        for row in 0..ROWS {
            if (final_column && row == 5) || (!final_column && (row == 1 || row == 2)) {
                assert_ne!(changed_rows[row], rows[row]);
            } else {
                assert_eq!(changed_rows[row], rows[row]);
            }
        }
        if final_column {
            assert_eq!(changed_rows[5], rows[0]);
            assert_eq!(
                product[width - 1].0 - changed_product[width - 1].0,
                left[5].0
            );
            assert_eq!(&product[..width - 1], &changed_product[..width - 1]);
        } else {
            assert_eq!(changed_rows[1], rows[2]);
            assert_eq!(changed_rows[2], rows[1]);
        }
    }
    for budget in [0, row_bytes - 1] {
        assert!(
            commit_rows_batched_with_limit(&source, &windows, &table, width, ROWS, budget).is_err()
        );
        assert!(source
            .vector_product_with_limit(&left, NU, sigma, budget)
            .is_err());
    }
    let short_file = FixtureFile::new(&bytes[..bytes.len() - 1]);
    assert!(PackedFile::open(&short_file.0, NU + sigma)
        .err()
        .unwrap()
        .contains("length mismatch"));
    // Deliberate test-only admission bypass to reach read_exact failures in both kernels.
    let short = PackedFile {
        file: RefCell::new(File::open(&short_file.0).unwrap()),
        log_n: NU + sigma,
        io_metrics: Arc::new(Mutex::new(PackedIoSnapshot::default())),
    };
    assert!(
        commit_rows_batched_with_limit(&short, &windows, &table, width, ROWS, max_batch_bytes)
            .unwrap_err()
            .starts_with("packed read:")
    );
    assert!(short
        .vector_product_with_limit(&left, NU, sigma, max_batch_bytes)
        .unwrap_err()
        .starts_with("packed read:"));
    let negatives_seconds = phase.elapsed().as_secs_f64();
    eprintln!(
        "{}",
        json!({"diagnostic":"log41-column-width-kernels", "log_n_file":NU+sigma,
        "nu":NU,"sigma":sigma,"g1_domain_log_n":41,"rows":ROWS,"width":width,
        "fixture_bytes":bytes.len(),"fixture_write_bytes":4*bytes.len()-1,
        "fixture_seconds":fixture_seconds,"g1_prefix_seconds":g1_prefix_seconds,
        "table_seconds":table_seconds,"commit_seconds":commit_seconds,"product_seconds":product_seconds,
        "reference_seconds":reference_seconds,"negatives_seconds":negatives_seconds,
        "total_seconds":started.elapsed().as_secs_f64(),
        "commit_io":format!("{commit_io:?}"),"product_io":format!("{product_io:?}"),
        "allocation_capacities":{"g1_bytes":g1_stats.points_capacity*std::mem::size_of::<ArkG1>(),
            "admission_entries":g1_stats.admission_capacity,"admission_compressed_bytes":g1_stats.compressed_capacity_bytes,
            "windows_bytes":table_stats.windows_capacity*std::mem::size_of::<CommitWindow>(),
            "table_bytes":table_stats.table_capacity*std::mem::size_of::<ark_bn254::G1Affine>(),
            "projective_chunk_bytes":table_stats.projective_capacity*std::mem::size_of::<G1Projective>(),
            "affine_chunk_bytes":table_stats.affine_chunk_capacity_max*std::mem::size_of::<ark_bn254::G1Affine>(),
            "kernel_read_batch_bytes":max_batch_bytes,"product_bytes":product.capacity()*std::mem::size_of::<ArkFr>()},
        "allocation_scope":"explicit vector capacities, not allocator peak or RSS; admission hash buckets/control and rayon scratch excluded",
        "full_setup":false,"proof_or_opening":false,"full_log41_traversal":false})
    );
}

#[test]
fn log41_width_small_kernel_controls() {
    run_sample(5);
}

#[test]
#[ignore = "manual G1-only throughput preflight before any actual-width kernel run"]
fn log41_width_g1_preflight_8192() {
    const COUNT: usize = 1 << 13;
    let started = Instant::now();
    let (points, stats) = pcs::g1_primary_prefix_for_width_test(41, COUNT).unwrap();
    let seconds = started.elapsed().as_secs_f64();
    let mut digest = Blake2b512::new();
    for point in &points {
        digest.update(pcs::encode(&point.0).unwrap());
    }
    let digest = digest
        .finalize()
        .iter()
        .map(|b| format!("{b:02X}"))
        .collect::<String>();
    let (replay, _) = pcs::g1_primary_prefix_for_width_test(41, 32).unwrap();
    assert_eq!(&points[..32], &replay);
    eprintln!(
        "{}",
        json!({"diagnostic":"log41-g1-prefix-preflight", "points":COUNT,
        "seconds":seconds,"points_per_second":COUNT as f64/seconds,
        "linear_full_width_seconds_estimate":seconds*((1usize<<LOG41_SIGMA)/COUNT) as f64,
        "points_capacity_bytes":stats.points_capacity*std::mem::size_of::<ArkG1>(),
        "admission_entries":stats.admission_capacity,"compressed_capacity_bytes":stats.compressed_capacity_bytes,
        "sampling_attempts":stats.sampling_attempts,"io_bytes":0,
        "compressed_g1_blake2b512":digest,
        "full_setup":false,"table_built":false,"proof_or_opening":false,
        "estimate_scope":"prefix throughput extrapolation only; no actual-width or full-setup evidence"})
    );
}

#[test]
#[ignore = "manual resource-bounded log41-width kernel sample; no full setup or proof"]
fn log41_width_sample_8_rows_sigma21() {
    assert_eq!(ROWS * (1usize << LOG41_SIGMA) / 8, 2 * 1024 * 1024);
    run_sample(LOG41_SIGMA);
}

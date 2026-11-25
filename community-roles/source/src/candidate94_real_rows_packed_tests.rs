//! Bounded real-frame row join to the existing PackedFile PCS kernels.
//! A selected-row vector product is only a partial contribution to log41 V.
use super::*;
use crate::native_prefix_auth_plan::role0_sha256;
use dory_pcs::primitives::poly::compute_left_right_vectors;
use std::time::{Instant, SystemTime, UNIX_EPOCH};

const LOG_N: usize = 27;
const NU: usize = 6;
const SIGMA: usize = 21;
const ROWS: usize = 1 << NU;
const WIDTH: usize = 1 << SIGMA;
const ROW_BYTES: usize = WIDTH / 8;
const FILE_BYTES: usize = ROWS * ROW_BYTES;
const GLOBAL_NU: usize = 20;
const HEADER_DOMAIN_ROWS: usize = 1_827_840 / 2;

fn phase(name: &str) {
    println!("CANDIDATE94_PHASE phase={name}");
    std::io::stdout().flush().expect("candidate94 phase flush");
}

fn bit_at(bytes: &[u8], column: usize) -> u64 {
    u64::from((bytes[column / 8] >> (column % 8)) & 1)
}

fn eq_at(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::from(1u64), |weight, (bit, value)| {
        weight * if index >> bit & 1 == 1 { *value } else { Fr::from(1u64) - *value }
    })
}

fn direct_g1(bytes: &[u8], g1: &[ArkG1]) -> ArkG1 {
    let mut result = G1Projective::zero();
    for (byte_index, byte) in bytes.iter().enumerate() {
        let mut remaining = *byte;
        while remaining != 0 {
            let bit = remaining.trailing_zeros() as usize;
            result += g1[byte_index * 8 + bit].0;
            remaining &= remaining - 1;
        }
    }
    ArkG1(result)
}

struct SampleFile(PathBuf);
impl SampleFile {
    fn write(rows: &[(usize, Vec<u8>)], short_last_byte: bool, label: &str) -> Self {
        let nonce = SystemTime::now().duration_since(UNIX_EPOCH).unwrap().as_nanos();
        let path = std::env::temp_dir().join(format!(
            "nipopow-candidate94-{}-{nonce}-{label}.bits", std::process::id()
        ));
        let mut file = OpenOptions::new().write(true).create_new(true).open(&path)
            .expect("create once candidate94 packed sample");
        assert_eq!(rows.len(), ROWS);
        for (position, (_, bytes)) in rows.iter().enumerate() {
            assert_eq!(bytes.len(), ROW_BYTES);
            let written = if short_last_byte && position == ROWS - 1 {
                &bytes[..ROW_BYTES - 1]
            } else {
                bytes.as_slice()
            };
            file.write_all(written).expect("write candidate94 row");
        }
        file.sync_all().expect("sync candidate94 sample");
        drop(file);
        Self(path)
    }

    fn finish(mut self) {
        let path = std::mem::take(&mut self.0);
        std::fs::remove_file(&path).expect("remove candidate94 packed sample");
    }
}
impl Drop for SampleFile {
    fn drop(&mut self) {
        if !self.0.as_os_str().is_empty() {
            let _ = std::fs::remove_file(&self.0);
        }
    }
}

fn assert_sample_file_metadata(metadata: &std::fs::Metadata) {
    assert!(metadata.is_file() && !metadata.file_type().is_symlink(),
            "candidate94 packed sample must be a regular file");
    assert_eq!(metadata.len(), FILE_BYTES as u64, "candidate94 packed sample size");
    #[cfg(windows)] {
        use std::os::windows::fs::MetadataExt;
        assert_eq!(metadata.file_attributes() & 0x00000400, 0,
                   "candidate94 packed sample must not be a reparse point");
    }
}

fn sample_file_receipt(file: &SampleFile, rows: &[(usize, Vec<u8>)]) -> [u8; 32] {
    let before = std::fs::symlink_metadata(&file.0)
        .expect("candidate94 packed sample path metadata before read");
    assert_sample_file_metadata(&before);
    let mut options = OpenOptions::new();
    options.read(true);
    #[cfg(windows)] {
        use std::os::windows::fs::OpenOptionsExt;
        options.share_mode(0x00000001); // FILE_SHARE_READ; deny mutation/deletion while open.
    }
    let mut opened = options.open(&file.0).expect("open bounded candidate94 packed sample");
    let opened_before = opened.metadata().expect("opened candidate94 sample metadata");
    assert_sample_file_metadata(&opened_before);
    let mut bytes = vec![0u8; FILE_BYTES];
    opened.read_exact(&mut bytes).expect("read exact bounded candidate94 packed sample");
    let mut trailing = [0u8; 1];
    assert_eq!(opened.read(&mut trailing).expect("candidate94 packed sample EOF read"), 0,
               "candidate94 packed sample has trailing data");
    let opened_after = opened.metadata().expect("opened candidate94 sample restat");
    assert_sample_file_metadata(&opened_after);
    let after = std::fs::symlink_metadata(&file.0)
        .expect("candidate94 packed sample path metadata after read");
    assert_sample_file_metadata(&after);
    for (slot, (_, expected)) in rows.iter().enumerate() {
        assert_eq!(&bytes[slot * ROW_BYTES..(slot + 1) * ROW_BYTES], expected.as_slice(),
                   "candidate94 packed sample row slot={slot}");
    }
    role0_sha256(&bytes).expect("candidate94 packed sample SHA-256")
}

fn assert_mutant_probe(
    changed: &[(usize, Vec<u8>)], left: &[ArkFr],
    baseline: &[ArkFr], column: usize, delta: Fr, label: &str,
) {
    assert_ne!(delta, Fr::zero(), "mutant must change a weighted bit");
    let file = SampleFile::write(changed, false, label);
    let receipt = sample_file_receipt(&file, changed);
    let source = PackedFile::open_with_limit(&file.0, LOG_N, LOG_N).unwrap();
    let actual = source.vector_product_with_limit(left, NU, SIGMA, MAX_COMMIT_READ_BATCH_BYTES)
        .expect("mutant packed vector product");
    assert_eq!(actual[column].0, baseline[column].0 + delta,
               "isolated {label} weighted-column delta");
    assert_ne!(actual[column], baseline[column], "{label} must not preserve V");
    assert_eq!(sample_file_receipt(&file, changed), receipt,
               "{label} sample changed during packed reads");
    drop(actual);
    drop(source);
    file.finish();
}

pub(crate) fn run(rows: Vec<(usize, Vec<u8>)>) {
    let started = Instant::now();
    assert_eq!(rows.len(), ROWS);
    assert!(rows.windows(2).all(|pair| pair[0].0 < pair[1].0));
    assert!(rows.iter().all(|(index, bytes)| *index < (1 << 20) && bytes.len() == ROW_BYTES));
    assert!(rows.iter().any(|(index, _)| *index == 420_831));
    assert!(rows.iter().any(|(index, _)| *index == 420_863));
    let header_rows = rows.iter().filter(|(index, _)| *index < HEADER_DOMAIN_ROWS).count();
    let padding_rows = ROWS - header_rows;
    assert_eq!((header_rows, padding_rows), (56, 8));
    let set_bits: usize = rows.iter().map(|(_, bytes)|
        bytes.iter().map(|byte| byte.count_ones() as usize).sum::<usize>()).sum();
    let nonzero_windows: usize = rows.iter().map(|(_, bytes)| bytes.iter().map(|byte|
        usize::from(byte & 0x0f != 0) + usize::from(byte >> 4 != 0)).sum::<usize>()).sum();
    assert!(set_bits > 0 && nonzero_windows > 0);

    phase("g1-prefix-start");
    let setup_started = Instant::now();
    let (g1, _) = pcs::g1_primary_prefix_for_width_test(41, WIDTH).unwrap();
    let g1_seconds = setup_started.elapsed().as_secs_f64();
    assert_eq!(g1.len(), WIDTH);
    phase("subset-table-start");
    let table_started = Instant::now();
    let (windows, table, stats) =
        commit_subset_table_chunked_from_g1(&g1, WIDTH, SUBSET_CHUNK_ENTRIES).unwrap();
    let table_seconds = table_started.elapsed().as_secs_f64();
    assert_eq!((windows.len(), table.len(), stats.normalization_calls),
               (WIDTH / COMMIT_WINDOW, 4 * WIDTH, 256));

    let file = SampleFile::write(&rows, false, "base");
    assert_eq!(std::fs::metadata(&file.0).unwrap().len(), FILE_BYTES as u64);
    let sample_sha256 = sample_file_receipt(&file, &rows);
    let source = PackedFile::open_with_limit(&file.0, LOG_N, LOG_N).unwrap();
    phase("commit-start");
    source.reset_io_metrics();
    let commit_started = Instant::now();
    let committed = commit_rows_batched_with_limit(
        &source, &windows, &table, WIDTH, ROWS, MAX_COMMIT_READ_BATCH_BYTES,
    ).unwrap();
    let commit_seconds = commit_started.elapsed().as_secs_f64();
    let commit_io = source.io_metrics_snapshot();
    assert_eq!(committed.len(), ROWS);
    assert_eq!(commit_io.read_bytes, FILE_BYTES as u64);
    phase("direct-g1-start");
    let direct_started = Instant::now();
    for (slot, (_, bytes)) in rows.iter().enumerate() {
        assert_eq!(committed[slot], direct_g1(bytes, &g1), "real row G1 parity slot={slot}");
    }
    let direct_g1_seconds = direct_started.elapsed().as_secs_f64();

    // In the real log41 matrix, the low 21 point coordinates select columns
    // and the high 20 coordinates weight *global* row indices. The 64 local
    // PackedFile slots are only a projection of those original rows.
    let row_point: Vec<Fr> = (0..GLOBAL_NU).map(|i| Fr::from(i as u64 + 2)).collect();
    let col_point: Vec<Fr> = (0..21).map(|i| Fr::from(i as u64 + 2)).collect();
    let left: Vec<ArkFr> = rows.iter().map(|(index, _)| ArkFr(eq_at(&row_point, *index))).collect();
    assert!(left.iter().all(|weight| weight.0 != Fr::zero()));
    let full_point: Vec<ArkFr> = col_point.iter().chain(row_point.iter()).copied().map(ArkFr).collect();
    let (reference_left, reference_right) =
        compute_left_right_vectors(&full_point, GLOBAL_NU, SIGMA);
    assert_eq!((reference_left.len(), reference_right.len()), (1 << GLOBAL_NU, WIDTH));
    for (slot, (global_row, _)) in rows.iter().enumerate() {
        assert_eq!(left[slot], reference_left[*global_row],
                   "vendor Dory global-row weight parity slot={slot} row={global_row}");
    }
    phase("vector-product-start");
    source.reset_io_metrics();
    let product_started = Instant::now();
    let product = source.vector_product_with_limit(&left, NU, SIGMA, MAX_COMMIT_READ_BATCH_BYTES)
        .unwrap();
    let product_seconds = product_started.elapsed().as_secs_f64();
    let product_io = source.io_metrics_snapshot();
    assert_eq!(product.len(), WIDTH);
    assert_eq!(product_io.read_bytes, FILE_BYTES as u64);
    phase("direct-column-oracle-start");
    let oracle_started = Instant::now();
    let mut projected_actual = Fr::zero();
    let mut projected_direct = Fr::zero();
    let mut nonzero_columns = 0usize;
    for column in 0..WIDTH {
        let mut expected = Fr::zero();
        for (global_row, bytes) in &rows {
            if bit_at(bytes, column) != 0 { expected += reference_left[*global_row].0; }
        }
        assert_eq!(product[column].0, expected, "independent global-row contribution at column={column}");
        if expected != Fr::zero() { nonzero_columns += 1; }
        let right = reference_right[column].0;
        assert_eq!(right, eq_at(&col_point, column),
                   "vendor Dory column weight parity at column={column}");
        projected_actual += product[column].0 * right;
        projected_direct += expected * right;
    }
    assert_eq!(projected_actual, projected_direct);
    let oracle_seconds = oracle_started.elapsed().as_secs_f64();
    assert!(nonzero_columns > 0);

    phase("isolated-negatives-start");
    let mut negatives = 0usize;
    let d_slot = rows.iter().position(|(index, _)| *index == 420_863).unwrap();
    let b_slot = rows.iter().position(|(index, _)| *index == 420_831).unwrap();
    let mut wrong_global_row = left.clone();
    wrong_global_row[d_slot] = reference_left[rows[d_slot].0 + 1];
    let wrong_global_delta = wrong_global_row[d_slot].0 - reference_left[rows[d_slot].0].0;
    assert_ne!(wrong_global_delta, Fr::zero(), "wrong-global-row mutant weight");
    let wrong_global_product = source.vector_product_with_limit(
        &wrong_global_row, NU, SIGMA, MAX_COMMIT_READ_BATCH_BYTES,
    ).expect("wrong-global-row mutant product");
    let wrong_global_column = (0..WIDTH)
        .find(|column| bit_at(&rows[d_slot].1, *column) != 0)
        .expect("real D row must have set bits");
    let direct_global_expected = rows.iter().fold(Fr::zero(), |sum, (global_row, bytes)| {
        sum + reference_left[*global_row].0 * Fr::from(bit_at(bytes, wrong_global_column))
    });
    assert_eq!(wrong_global_product[wrong_global_column].0,
               product[wrong_global_column].0 + wrong_global_delta);
    assert_ne!(wrong_global_product[wrong_global_column].0, direct_global_expected,
               "independent global-row oracle must reject wrong-row weight");
    negatives += 1;
    drop(wrong_global_product);
    let mut half_swapped = rows.clone();
    let (first, second) = half_swapped[d_slot].1.split_at_mut(ROW_BYTES / 2);
    first.swap_with_slice(second);
    let half_column = (0..WIDTH).find(|column|
        bit_at(&rows[d_slot].1, *column) != bit_at(&half_swapped[d_slot].1, *column))
        .expect("real row halves must differ");
    let half_delta = left[d_slot].0 *
        (Fr::from(bit_at(&half_swapped[d_slot].1, half_column))
         - Fr::from(bit_at(&rows[d_slot].1, half_column)));
    assert_mutant_probe(&half_swapped, &left, &product, half_column, half_delta, "half-swap");
    negatives += 1;
    drop(half_swapped);

    assert_ne!(rows[b_slot].1, rows[d_slot].1);
    assert_ne!(left[b_slot], left[d_slot]);
    let mut permuted = rows.clone();
    permuted.swap(b_slot, d_slot);
    let permuted_column = (0..WIDTH).find(|column|
        bit_at(&rows[b_slot].1, *column) != bit_at(&rows[d_slot].1, *column))
        .expect("selected real rows must differ");
    let permuted_delta = (left[b_slot].0 - left[d_slot].0) *
        (Fr::from(bit_at(&rows[d_slot].1, permuted_column))
         - Fr::from(bit_at(&rows[b_slot].1, permuted_column)));
    assert_mutant_probe(&permuted, &left, &product, permuted_column, permuted_delta, "row-permutation");
    negatives += 1;
    drop(permuted);

    let final_slot = ROWS - 1;
    let mut final_flipped = rows.clone();
    final_flipped[final_slot].1[ROW_BYTES - 1] ^= 0x80;
    let last_column = WIDTH - 1;
    let final_delta = left[final_slot].0 *
        (Fr::from(bit_at(&final_flipped[final_slot].1, last_column))
         - Fr::from(bit_at(&rows[final_slot].1, last_column)));
    assert_mutant_probe(&final_flipped, &left, &product, last_column, final_delta, "final-bit");
    negatives += 1;
    drop(final_flipped);
    assert!(source.vector_product_with_limit(&left, NU, SIGMA, ROW_BYTES - 1).is_err());
    negatives += 1;
    let short = SampleFile::write(&rows, true, "short");
    assert!(PackedFile::open_with_limit(&short.0, LOG_N, LOG_N)
        .err().expect("short packed file must be rejected")
        .contains("packed length mismatch"));
    negatives += 1;
    short.finish();
    assert_eq!(sample_file_receipt(&file, &rows), sample_sha256,
               "baseline packed sample changed during commit/product/negative reads");
    assert_eq!(negatives, 6);
    drop(source);
    file.finish();

    let sample_sha256_hex: String = sample_sha256.iter().map(|byte| format!("{byte:02x}")).collect();
    println!("CANDIDATE94_REAL_PACKED_VMV_PASS sample_rows={ROWS} header_rows={header_rows} padding_rows={padding_rows} sample_file_bytes={FILE_BYTES} sample_sha256={sample_sha256_hex} sigma={SIGMA} original_row_domain=1048576 set_bits={set_bits} nonzero_windows={nonzero_windows} nonzero_columns={nonzero_columns} g1_prefix_s={g1_seconds:.6} table_s={table_seconds:.6} commit_s={commit_seconds:.6} direct_g1_s={direct_g1_seconds:.6} product_s={product_seconds:.6} direct_oracle_s={oracle_seconds:.6} commit_read_bytes={} product_read_bytes={} negatives={negatives} elapsed_s={:.6} g2_setup=false full_v=false full_h21_witness=false proof=false",
             commit_io.read_bytes, product_io.read_bytes, started.elapsed().as_secs_f64());
    std::io::stdout().flush().expect("candidate94 terminal marker flush");
}

pub(crate) struct Candidate95PcsReceipt {
    pub sample_sha256: String,
    pub commit_read_bytes: u64,
    pub partial_v_read_bytes: u64,
    pub pcs_negative_read_bytes: u64,
    pub g1_commit_rows: usize,
    pub nonzero_v_columns: usize,
    pub pcs_negatives: usize,
    pub commit_s: f64,
    pub partial_v_s: f64,
}

/// Consume the same locked log-25 PackedFile that supplied the Map readback.
/// The 16 local slots retain their explicit global log-41 row coordinates.
pub(crate) fn run_candidate95_same_source(
    source: &PackedFile,
    global_rows: &[usize],
    rows: &[Vec<u8>],
) -> Candidate95PcsReceipt {
    const LOG_N: usize = 25;
    const NU: usize = 4;
    const SIGMA: usize = 21;
    const ROW_COUNT: usize = 1 << NU;
    const WIDTH: usize = 1 << SIGMA;
    const ROW_BYTES: usize = WIDTH / 8;
    const FILE_BYTES: usize = ROW_COUNT * ROW_BYTES;
    const GLOBAL_NU: usize = 20;
    const D_GLOBAL_ROW: usize = 420_863;

    let started = Instant::now();
    assert_eq!(source.input_len(), 1 << LOG_N);
    assert_eq!(global_rows.len(), ROW_COUNT);
    assert_eq!(rows.len(), ROW_COUNT);
    assert!(global_rows.windows(2).all(|pair| pair[0] < pair[1]));
    assert_eq!((global_rows[0], global_rows[ROW_COUNT - 1]), (0, (1 << GLOBAL_NU) - 1));
    assert!(rows.iter().all(|row| row.len() == ROW_BYTES));
    assert!(global_rows.binary_search(&D_GLOBAL_ROW).is_ok());

    let mut sample_bytes = Vec::with_capacity(FILE_BYTES);
    for row in rows {
        sample_bytes.extend_from_slice(row);
    }
    assert_eq!(sample_bytes.len(), FILE_BYTES);
    let sample_sha256 = role0_sha256(&sample_bytes)
        .expect("candidate95 exact packed sample SHA256")
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect::<String>();
    drop(sample_bytes);

    let (g1, _) = pcs::g1_primary_prefix_for_width_test(41, WIDTH)
        .expect("log41 G1 prefix for selected sigma rows");
    assert_eq!(g1.len(), WIDTH);
    let (windows, table, stats) = commit_subset_table_chunked_from_g1(
        &g1,
        WIDTH,
        SUBSET_CHUNK_ENTRIES,
    )
    .expect("bounded G1 row subset table");
    assert_eq!((windows.len(), table.len()), (WIDTH / COMMIT_WINDOW, 4 * WIDTH));
    assert_eq!(stats.normalization_calls, 256);

    source.reset_io_metrics();
    let commit_started = Instant::now();
    let committed = commit_rows_batched_with_limit(
        source,
        &windows,
        &table,
        WIDTH,
        ROW_COUNT,
        MAX_COMMIT_READ_BATCH_BYTES,
    )
    .expect("existing PackedFile selected-row G1 commitment");
    let commit_s = commit_started.elapsed().as_secs_f64();
    let commit_io = source.io_metrics_snapshot();
    assert_eq!(committed.len(), ROW_COUNT);
    assert_eq!(commit_io.read_bytes, FILE_BYTES as u64);
    for (slot, row) in rows.iter().enumerate() {
        assert_eq!(committed[slot], direct_g1(row, &g1), "direct typed G1 row={slot}");
    }

    let row_point: Vec<Fr> = (0..GLOBAL_NU).map(|bit| Fr::from(bit as u64 + 2)).collect();
    let column_point: Vec<Fr> = (0..SIGMA).map(|bit| Fr::from(bit as u64 + 2)).collect();
    let full_point: Vec<ArkFr> = column_point
        .iter()
        .chain(row_point.iter())
        .copied()
        .map(ArkFr)
        .collect();
    let (reference_left, reference_right) =
        compute_left_right_vectors(&full_point, GLOBAL_NU, SIGMA);
    assert_eq!((reference_left.len(), reference_right.len()), (1 << GLOBAL_NU, WIDTH));
    let left: Vec<ArkFr> = global_rows
        .iter()
        .map(|global_row| reference_left[*global_row])
        .collect();
    assert!(left.iter().all(|weight| weight.0 != Fr::zero()));
    for (slot, global_row) in global_rows.iter().enumerate() {
        assert_eq!(left[slot], reference_left[*global_row]);
        assert_eq!(
            reference_left[*global_row].0,
            eq_at(&row_point, *global_row),
            "independent global log41 row weight row={global_row}",
        );
    }

    source.reset_io_metrics();
    let partial_v_started = Instant::now();
    let partial_v = source
        .vector_product_with_limit(&left, NU, SIGMA, MAX_COMMIT_READ_BATCH_BYTES)
        .expect("existing PackedFile partial-V product");
    let partial_v_s = partial_v_started.elapsed().as_secs_f64();
    let partial_v_io = source.io_metrics_snapshot();
    assert_eq!(partial_v.len(), WIDTH);
    assert_eq!(partial_v_io.read_bytes, FILE_BYTES as u64);

    let mut nonzero_v_columns = 0usize;
    let mut projected_actual = Fr::zero();
    let mut projected_direct = Fr::zero();
    for column in 0..WIDTH {
        let mut expected = Fr::zero();
        for (slot, row) in rows.iter().enumerate() {
            if bit_at(row, column) != 0 {
                expected += left[slot].0;
            }
        }
        assert_eq!(
            partial_v[column].0,
            expected,
            "direct selected-row partial V oracle column={column}",
        );
        if expected != Fr::zero() {
            nonzero_v_columns += 1;
        }
        assert_eq!(
            reference_right[column].0,
            eq_at(&column_point, column),
            "independent log41 sigma-coordinate oracle column={column}",
        );
        projected_actual += partial_v[column].0 * reference_right[column].0;
        projected_direct += expected * reference_right[column].0;
    }
    assert_eq!(projected_actual, projected_direct);
    assert!(nonzero_v_columns > 0);

    // Isolate a global-row weight alias at the selected D destination.
    let d_slot = global_rows.binary_search(&D_GLOBAL_ROW).unwrap();
    let mut wrong_global_weight = left.clone();
    wrong_global_weight[d_slot] = reference_left[D_GLOBAL_ROW + 1];
    let delta = wrong_global_weight[d_slot].0 - reference_left[D_GLOBAL_ROW].0;
    assert_ne!(delta, Fr::zero());
    let changed_column = (0..WIDTH)
        .find(|column| bit_at(&rows[d_slot], *column) != 0)
        .expect("selected D destination row has a nonzero packed bit");
    source.reset_io_metrics();
    let wrong_product = source
        .vector_product_with_limit(
            &wrong_global_weight,
            NU,
            SIGMA,
            MAX_COMMIT_READ_BATCH_BYTES,
        )
        .expect("wrong-global-row weighted PackedFile negative");
    let negative_io = source.io_metrics_snapshot();
    assert_eq!(negative_io.read_bytes, FILE_BYTES as u64);
    let direct = rows.iter().enumerate().fold(Fr::zero(), |sum, (slot, row)| {
        if bit_at(row, changed_column) == 0 {
            sum
        } else {
            sum + reference_left[global_rows[slot]].0
        }
    });
    assert_eq!(
        wrong_product[changed_column].0,
        partial_v[changed_column].0 + delta,
        "wrong global-row weight changes the selected D contribution",
    );
    assert_ne!(
        wrong_product[changed_column].0,
        direct,
        "direct global-row oracle rejects aliased D coordinate",
    );
    drop(wrong_product);
    assert_eq!(negative_io.read_bytes, FILE_BYTES as u64);

    let elapsed_s = started.elapsed().as_secs_f64();
    let pcs_negatives = 1;
    assert_eq!(pcs_negatives, 1);
    println!(
        "CANDIDATE95_PHASE phase=global_row_commitment_and_partial_v elapsed_s={elapsed_s:.6} commit_s={commit_s:.6} partial_v_s={partial_v_s:.6} commit_read_bytes={} partial_v_read_bytes={} pcs_negative_read_bytes={} g1_commit_rows={} nonzero_v_columns={} pcs_negatives={pcs_negatives}",
        commit_io.read_bytes,
        partial_v_io.read_bytes,
        negative_io.read_bytes,
        committed.len(),
        nonzero_v_columns,
    );
    std::io::stdout().flush().expect("candidate95 PCS phase flush");
    Candidate95PcsReceipt {
        sample_sha256,
        commit_read_bytes: commit_io.read_bytes,
        partial_v_read_bytes: partial_v_io.read_bytes,
        pcs_negative_read_bytes: negative_io.read_bytes,
        g1_commit_rows: committed.len(),
        nonzero_v_columns,
        pcs_negatives,
        commit_s,
        partial_v_s,
    }
}

//! C312 projection-only seven-claim differential over a fixed selected subset
//! of the already reviewed candidate94 real H21 frame rows.
use ark_bn254::Fr;
use ark_ff::{BigInteger, One, PrimeField, Zero};
use crate::native_prefix_auth_plan::role0_sha256;
use std::{fs::{File, OpenOptions}, io::{Read, Write}, time::Instant};

const ROWS64_SHA256: &str = "155ccfb907c9afe9ff576c2eb131e262a9f94a928643e2afd05a2be6cdaf58f2";
const ROW420863_SHA256: &str = "629f65d24d6a770830dee8cf7069e0aea02d7d67bf47ff1b2821576f6e49a9da";
const POINTS_SHA256: &str = "bc0b7dcd576ee3bfa704d211e3284b8b51fe29dd95d7b1df1c0ce7832d8847f1";
const CLAIMS: usize = 7;
const ROW_DOMAIN: usize = 1 << 20;
const COLUMN_DOMAIN: usize = 1 << 21;
const ROW_BYTES: usize = COLUMN_DOMAIN / 8;
const SELECTED_ROWS: usize = 32;

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn digest(bytes: &[u8]) -> String {
    hex(&role0_sha256(bytes).expect("C312 SHA-256"))
}

fn eq_at(point: &[Fr], index: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |weight, (bit, value)| {
        weight * if index >> bit & 1 == 1 { *value } else { Fr::one() - *value }
    })
}

fn mle_weights(point: &[Fr]) -> Vec<Fr> {
    let mut weights = vec![Fr::one()];
    for coordinate in point {
        let old_len = weights.len();
        weights.resize(old_len * 2, Fr::zero());
        for index in 0..old_len {
            let old = weights[index];
            weights[index] = old * (Fr::one() - *coordinate);
            weights[index + old_len] = old * *coordinate;
        }
    }
    weights
}

fn fused_add_byte(
    projected: &mut [Vec<Fr>; CLAIMS], high_weights: &[Vec<Fr>; CLAIMS],
    global_row: usize, byte_index: usize, byte: u8, skip_first_add: bool,
) -> u64 {
    let mut skipped = false;
    let mut set_bits = 0;
    for bit in 0..8 {
        if byte & (1 << bit) == 0 { continue; }
        set_bits += 1;
        let column = byte_index * 8 + bit;
        for claim in 0..CLAIMS {
            if skip_first_add && !skipped { skipped = true; continue; }
            projected[claim][column] += high_weights[claim][global_row];
        }
    }
    set_bits
}

fn expected_rows() -> Vec<usize> {
    vec![
        0, 34379, 68759, 103138, 137518, 171897, 206277, 240656,
        275036, 309415, 343795, 378174, 412554, 420863, 446933, 481313,
        515692, 550072, 584451, 618831, 653210, 687590, 721969, 756349,
        790728, 825108, 859487, 893867, 928246, 962626, 997005, 1031385,
    ]
}

fn temp_sample(bytes: &[u8]) -> std::path::PathBuf {
    let path = std::env::temp_dir().join(format!("c312-projection-{}.bits", std::process::id()));
    let mut file = OpenOptions::new().write(true).create_new(true).open(&path)
        .expect("create C312 selected sample once");
    file.write_all(bytes).expect("write C312 selected sample");
    file.sync_all().expect("sync C312 selected sample");
    path
}

pub(crate) fn run(rows64: Vec<(usize, Vec<u8>)>) {
    let all_started = Instant::now();
    let fixture_only = std::env::var_os("C312_SELECTED_FIXTURE").is_some();
    assert_eq!(rows64.len(), if fixture_only { SELECTED_ROWS } else { 64 });
    assert!(rows64.windows(2).all(|pair| pair[0].0 < pair[1].0));
    assert!(rows64.iter().all(|(index, row)| *index < ROW_DOMAIN && row.len() == ROW_BYTES));

    let full_sample: Vec<u8> = if fixture_only { Vec::new() } else { rows64.iter().flat_map(|(_, row)| row.iter().copied()).collect() };
    let full_sha = if fixture_only { ROWS64_SHA256.to_owned() } else { digest(&full_sample) };
    if !fixture_only {
        assert_eq!(full_sample.len(), 16_777_216);
        assert_eq!(full_sha, ROWS64_SHA256, "candidate94 full 64-row sample pin");
    }
    let row_hashes = rows64.iter().map(|(index, row)| format!("{index}:{}", digest(row)))
        .collect::<Vec<_>>();
    if !fixture_only {
        let observed = rows64.iter().find(|(index, _)| *index == 420_863).unwrap();
        assert_eq!(digest(&observed.1), ROW420863_SHA256, "individually retained c94 row hash");
    }

    let all_indices: Vec<usize> = rows64.iter().map(|(index, _)| *index).collect();
    let selected_indices: Vec<usize> = if fixture_only { all_indices.clone() } else { (0..32).map(|position| all_indices[position * 2]).collect() };
    assert_eq!(selected_indices, expected_rows(), "fixed every-other sorted row rule");
    assert_eq!(selected_indices.iter().filter(|index| **index < 913_920).count(), 28);
    assert_eq!(selected_indices.iter().filter(|index| **index >= 913_920).count(), 4);
    let selected: Vec<(usize, Vec<u8>)> = if fixture_only { rows64 } else { rows64.iter().enumerate()
        .filter(|(position, _)| *position % 2 == 0).map(|(_, row)| row.clone()).collect() };
    assert_eq!(selected.len(), SELECTED_ROWS);
    let selected_bytes: Vec<u8> = selected.iter().flat_map(|(_, row)| row.iter().copied()).collect();
    assert_eq!(selected_bytes.len(), SELECTED_ROWS * ROW_BYTES);
    let selected_sha = digest(&selected_bytes);
    if std::env::var_os("C312_EXTRACT_ONLY").is_some() {
        assert!(!fixture_only);
        let output = std::env::var_os("C312_EXTRACT_DIR").expect("extraction output directory");
        let output = std::path::PathBuf::from(output);
        assert!(output.is_absolute(), "extraction directory must be absolute");
        let full_path = output.join("c312-rows64.bin");
        let selected_path = output.join("c312-selected32.bin");
        for (path, bytes) in [(&full_path, &full_sample), (&selected_path, &selected_bytes)] {
            let mut file = OpenOptions::new().write(true).create_new(true).open(path)
                .expect("create extraction artifact once");
            file.write_all(bytes).expect("write bounded extraction artifact");
            file.sync_all().expect("sync extraction artifact");
        }
        let row_stats = selected.iter().map(|(index, row)| {
            let popcount: u64 = row.iter().map(|byte| byte.count_ones() as u64).sum();
            let nonzero_nibble_windows: u64 = row.iter().map(|byte|
                if byte & 0x0f != 0 { 1 } else { 0 }
                    + if byte >> 4 != 0 { 1 } else { 0 }).sum();
            format!("{index}:{}:{popcount}:{nonzero_nibble_windows}", digest(row))
        }).collect::<Vec<_>>().join(",");
        println!("C312_EXTRACTION_PASS full64_sha256={full_sha} selected32_sha256={selected_sha} points_sha256={POINTS_SHA256} full_sample_bytes={} selected_sample_bytes={} selected_rows={} selected_row_stats={} full64_row_hashes={}",
            full_sample.len(), selected_bytes.len(), selected_indices.iter().map(usize::to_string).collect::<Vec<_>>().join(","),
            row_stats, row_hashes.join(","));
        std::io::stdout().flush().expect("C312 extraction marker flush");
        return;
    }
    if fixture_only {
        assert!(digest(&selected_bytes).eq_ignore_ascii_case(&std::env::var("C312_SELECTED_SHA256").expect("fixture SHA pin")));
    }
    let path = temp_sample(&selected_bytes);

    let read_started = Instant::now();
    let mut sample_file = File::open(&path).expect("open C312 selected sample");
    let mut sample = vec![0u8; selected_bytes.len()];
    sample_file.read_exact(&mut sample).expect("read C312 selected sample");
    assert_eq!(sample_file.read(&mut [0u8; 1]).unwrap(), 0, "selected sample exact EOF");
    drop(sample_file);
    let sample_temp_reread_s = read_started.elapsed().as_secs_f64();
    assert_eq!(sample, selected_bytes);
    assert_eq!(digest(&sample), selected_sha);
    assert!(selected.iter().all(|(_, row)| row.len() == ROW_BYTES));

    let points: [Vec<Fr>; CLAIMS] = std::array::from_fn(|claim| {
        (0..41).map(|bit| Fr::from((101 + 41 * claim + bit) as u64)).collect()
    });
    let mut encoded_points = Vec::with_capacity(CLAIMS * 41 * 32);
    for point in &points {
        for coordinate in point {
            let mut encoded = coordinate.into_bigint().to_bytes_le();
            encoded.resize(32, 0);
            assert_eq!(encoded.len(), 32);
            encoded_points.extend_from_slice(&encoded);
        }
    }
    assert_eq!(digest(&encoded_points), POINTS_SHA256, "frozen seven-point encoding");
    assert!(points.iter().flatten().all(|coordinate| *coordinate != Fr::zero() && *coordinate != Fr::one()));

    let alloc_started = Instant::now();
    let mut projected: [Vec<Fr>; CLAIMS] = std::array::from_fn(|_| vec![Fr::zero(); COLUMN_DOMAIN]);
    let mut high_weights: [Vec<Fr>; CLAIMS] = std::array::from_fn(|_| vec![Fr::zero(); ROW_DOMAIN]);
    let allocation_init_s = alloc_started.elapsed().as_secs_f64();
    let mut high_weight_s = 0.0;
    let mut reference_high_weight_s = 0.0;
    for claim in 0..CLAIMS {
        let row_point = &points[claim][21..];
        let reference_started = Instant::now();
        let reference = mle_weights(row_point);
        reference_high_weight_s += reference_started.elapsed().as_secs_f64();
        let high_claim_started = Instant::now();
        for (global_row, _) in &selected {
            high_weights[claim][*global_row] = eq_at(row_point, *global_row);
            assert_eq!(high_weights[claim][*global_row], reference[*global_row], "independent high-coordinate MLE claim={claim} row={global_row}");
        }
        high_weight_s += high_claim_started.elapsed().as_secs_f64();
    }

    let (control_slot, control_byte_index, control_byte) = selected.iter().enumerate().find_map(|(slot, (_, row))|
        row.iter().copied().enumerate().find(|(_, byte)| *byte != 0).map(|(byte_index, byte)| (slot, byte_index, byte))
    ).expect("real selected sample contains a set bit");
    let control_row = selected[control_slot].0;
    let mut one_byte = std::array::from_fn(|_| vec![Fr::zero(); 8]);
    fused_add_byte(&mut one_byte, &high_weights, control_row, 0, control_byte, false);
    let mut independent_byte = std::array::from_fn(|_| vec![Fr::zero(); 8]);
    for claim in 0..CLAIMS {
        let reference = mle_weights(&points[claim][21..]);
        for bit in 0..8 {
            if control_byte & (1 << bit) != 0 {
                independent_byte[claim][bit] += reference[control_row];
            }
        }
    }
    assert_eq!(one_byte, independent_byte, "real-byte fused-kernel control oracle");
    let mut skipped_add_mutant = std::array::from_fn(|_| vec![Fr::zero(); 8]);
    fused_add_byte(&mut skipped_add_mutant, &high_weights, control_row, 0, control_byte, true);
    assert_ne!(skipped_add_mutant, independent_byte, "one-addition-omitted control must be rejected");
    let column_weight_started = Instant::now();
    let column_weights: [Vec<Fr>; CLAIMS] = std::array::from_fn(|claim| mle_weights(&points[claim][..21]));
    let column_weight_s = column_weight_started.elapsed().as_secs_f64();

    let scan_started = Instant::now();
    let mut bit_tests = 0u64;
    let mut set_bit_count = 0u64;
    let add_started = Instant::now();
    for (slot, (_, row)) in selected.iter().enumerate() {
        for (byte_index, byte) in row.iter().copied().enumerate() {
            bit_tests += 8;
            set_bit_count += fused_add_byte(&mut projected, &high_weights, selected[slot].0, byte_index, byte, false);
        }
    }
    let bit_scan_s = scan_started.elapsed().as_secs_f64();
    assert_eq!(bit_tests, (SELECTED_ROWS * COLUMN_DOMAIN) as u64);
    let fr_add_s = add_started.elapsed().as_secs_f64();
    let additions = (set_bit_count as usize * CLAIMS) as u64;

    let mut oracle_bits = 0u64;
    let mut dot_products = Vec::with_capacity(CLAIMS);
    let mut direct_mles = Vec::with_capacity(CLAIMS);
    let mut oracle_s = 0.0;
    for claim in 0..CLAIMS {
        assert_eq!(column_weights[claim].len(), COLUMN_DOMAIN);
        let reference_high_weights = mle_weights(&points[claim][21..]);
        let oracle_started = Instant::now();
        for column in 0..COLUMN_DOMAIN {
            let mut expected = Fr::zero();
            for (global_row, row) in &selected {
                oracle_bits += 1;
                if row[column / 8] & (1 << (column % 8)) != 0 {
                    expected += reference_high_weights[*global_row];
                }
            }
            assert_eq!(projected[claim][column], expected,
                       "dense selected-row oracle claim={claim} column={column}");
        }
        let mut dot = Fr::zero();
        for column in 0..COLUMN_DOMAIN {
            dot += projected[claim][column] * column_weights[claim][column];
        }
        let mut direct = Fr::zero();
        for (global_row, row) in &selected {
            let mut row_mle = Fr::zero();
            for (byte_index, byte) in row.iter().copied().enumerate() {
                let mut remaining = byte;
                while remaining != 0 {
                    let bit = remaining.trailing_zeros() as usize;
                    row_mle += column_weights[claim][byte_index * 8 + bit];
                    remaining &= remaining - 1;
                }
            }
            // Independent global-row equality oracle, computed from the full
            // 20-bit row index instead of reusing the projection weight table.
            direct += reference_high_weights[*global_row] * row_mle;
        }
        assert_eq!(dot, direct, "independent selected-row MLE claim={claim}");
        oracle_s += oracle_started.elapsed().as_secs_f64();
        dot_products.push(hex(&dot.into_bigint().to_bytes_le()));
        direct_mles.push(hex(&direct.into_bigint().to_bytes_le()));
    }
    assert_eq!(oracle_bits, (CLAIMS * SELECTED_ROWS * COLUMN_DOMAIN) as u64);

    std::fs::remove_file(&path).expect("remove C312 selected sample");
    let row_hash_output = row_hashes.join(",");
    println!("C312_PROJECTION_PASS full64_sha256={full_sha} selected32_sha256={selected_sha} points_sha256={POINTS_SHA256} selected_rows={} header_rows=28 padding_rows=4 sample_bytes={} selected_set_bits={} bit_tests={} field_additions={} oracle_bit_tests={} alloc_init_s={allocation_init_s:.6} sample_temp_reread_s={sample_temp_reread_s:.6} high_weight_s={high_weight_s:.6} reference_high_weight_oracle_s={reference_high_weight_s:.6} column_weight_s={column_weight_s:.6} fused_kernel_s={bit_scan_s:.6} oracle_s={oracle_s:.6} dot_products={} direct_mles={} controls=skipped_add_rejected control_row={} control_byte_index={} control_byte={} row_hashes={row_hash_output} elapsed_s={:.6}",
        selected_indices.iter().map(usize::to_string).collect::<Vec<_>>().join(","),
        sample.len(), set_bit_count, bit_tests, additions, oracle_bits,
        dot_products.join(","), direct_mles.join(","), control_row, control_byte_index, control_byte, all_started.elapsed().as_secs_f64());
    std::io::stdout().flush().expect("C312 receipt marker flush");
}

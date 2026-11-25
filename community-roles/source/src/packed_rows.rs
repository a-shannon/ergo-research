//! Bounded contiguous-row reads from the canonical LSB-first packed witness.
use ark_bn254::Fr;

use crate::packed::PackedFile;

const DIRECT_READ_FIELDS: usize = 1 << 16;
const MAX_EXPANDED_ROW_BYTES: usize = 64 * 1024 * 1024;

pub(crate) fn read_row(source: &PackedFile, width: usize, row: usize) -> Result<Vec<Fr>, String> {
    if width == 0 || !width.is_power_of_two() {
        return Err("packed row width must be a nonzero power of two".into());
    }

    let input_len = source.input_len();
    if input_len % width != 0 {
        return Err("packed row width does not divide the source".into());
    }
    let row_count = input_len / width;
    if row >= row_count {
        return Err("packed row index is out of bounds".into());
    }

    let expanded_bytes = width
        .checked_mul(std::mem::size_of::<Fr>())
        .ok_or_else(|| "packed expanded row byte size overflow".to_string())?;
    if expanded_bytes > MAX_EXPANDED_ROW_BYTES {
        return Err("packed expanded row exceeds memory budget".into());
    }

    if width <= DIRECT_READ_FIELDS {
        return source.read_copy(width, row);
    }

    let chunks_per_row = width / DIRECT_READ_FIELDS;
    let first_chunk = row
        .checked_mul(chunks_per_row)
        .ok_or_else(|| "packed row first chunk index overflow".to_string())?;
    let last_chunk = first_chunk
        .checked_add(chunks_per_row - 1)
        .ok_or_else(|| "packed row last chunk index overflow".to_string())?;
    if last_chunk >= input_len / DIRECT_READ_FIELDS {
        return Err("packed row chunk range is out of bounds".into());
    }

    let mut values = Vec::new();
    values
        .try_reserve_exact(width)
        .map_err(|error| format!("packed row allocation failed: {error}"))?;

    for chunk in 0..chunks_per_row {
        let chunk_index = first_chunk
            .checked_add(chunk)
            .ok_or_else(|| "packed row chunk index overflow".to_string())?;
        let chunk_values = source.read_copy(DIRECT_READ_FIELDS, chunk_index)?;
        if chunk_values.len() != DIRECT_READ_FIELDS {
            return Err("packed row chunk length mismatch".into());
        }
        values.extend(chunk_values);
    }

    if values.len() != width {
        return Err("packed row length mismatch".into());
    }
    Ok(values)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::packed::PackedFileWriter;
    use std::{
        path::PathBuf,
        sync::atomic::{AtomicU64, Ordering},
        time::{SystemTime, UNIX_EPOCH},
    };

    const LARGE_LOG_N: usize = 22;
    const LARGE_INPUT_BITS: usize = 1 << LARGE_LOG_N;
    const SOURCE_BYTES: usize = LARGE_INPUT_BITS / 8;
    static NEXT: AtomicU64 = AtomicU64::new(0);

    fn artifact_path(label: &str) -> PathBuf {
        let root = std::env::var_os("NIPOPOW_PCS_ROW_DIR")
            .map(PathBuf::from)
            .unwrap_or_else(std::env::temp_dir);
        assert!(root.is_dir(), "row artifact directory must already exist");
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock before Unix epoch")
            .as_nanos();
        root.join(format!(
            "packed-row-{label}-{}-{nanos}-{}.bin",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ))
    }

    fn expected_bit(bit: usize) -> bool {
        let mixed = bit.wrapping_mul(37)
            ^ (bit >> 16).wrapping_mul(0x9E37)
            ^ (bit >> 11);
        mixed % 29 < 14
    }

    fn large_source() -> PackedFile {
        let path = artifact_path("log22");
        let mut writer = PackedFileWriter::create_new(&path, LARGE_LOG_N).unwrap();
        let mut bytes = vec![0u8; SOURCE_BYTES];
        for bit in 0..LARGE_INPUT_BITS {
            if expected_bit(bit) {
                bytes[bit / 8] |= 1 << (bit % 8);
            }
        }
        writer.write_bytes(&bytes).unwrap();
        writer.finish().unwrap()
    }

    fn small_source() -> PackedFile {
        let path = artifact_path("log3");
        let mut writer = PackedFileWriter::create_new(&path, 3).unwrap();
        writer.write_bytes(&[0b1011_0101]).unwrap();
        writer.finish().unwrap()
    }

    fn assert_row_matches(source: &PackedFile, width: usize, row: usize) {
        let values = read_row(source, width, row).unwrap();
        assert_eq!(values.len(), width);
        let first_bit = row.checked_mul(width).unwrap();
        for (column, value) in values.iter().enumerate() {
            assert_eq!(
                *value,
                Fr::from(u64::from(expected_bit(first_bit + column))),
                "row {row}, width {width}, column {column}"
            );
        }
    }

    #[test]
    fn small_rows_preserve_lsb_order_and_subbyte_reads() {
        let source = small_source();
        let input = [true, false, true, false, true, true, false, true];

        for width in [1usize, 2, 4] {
            source.reset_io_metrics();
            let rows = source.input_len() / width;
            for row in 0..rows {
                let values = read_row(&source, width, row).unwrap();
                let first = row * width;
                let expected = input[first..first + width]
                    .iter()
                    .map(|bit| Fr::from(u64::from(*bit)))
                    .collect::<Vec<_>>();
                assert_eq!(values, expected, "width {width}, row {row}");
            }
            let io = source.io_metrics_snapshot();
            assert_eq!(io.read_calls, rows as u64);
            assert_eq!(io.read_bytes, rows as u64);
        }
    }

    #[test]
    fn direct_and_chunked_rows_match_distinct_lsb_source_rows() {
        let source = large_source();

        for width in [1usize << 16, 1 << 17] {
            let last_row = source.input_len() / width - 1;
            for row in [0, last_row] {
                source.reset_io_metrics();
                assert_row_matches(&source, width, row);
                let io = source.io_metrics_snapshot();
                let expected_calls = (width / DIRECT_READ_FIELDS) as u64;
                assert_eq!(io.read_calls, expected_calls, "width {width}, row {row}");
                assert_eq!(io.read_bytes, (width / 8) as u64, "width {width}, row {row}");
            }
        }
    }

    #[test]
    fn maximum_row_uses_exactly_thirty_two_bounded_chunks() {
        let source = large_source();
        let width = 1usize << 21;
        let last_row = source.input_len() / width - 1;

        source.reset_io_metrics();
        assert_row_matches(&source, width, last_row);
        let io = source.io_metrics_snapshot();
        assert_eq!(io.read_calls, 32);
        assert_eq!(io.read_bytes, (width / 8) as u64);
    }

    #[test]
    fn invalid_rows_fail_before_any_packed_io() {
        let source = large_source();
        let invalid = [
            (0usize, 0usize),
            (3, 0),
            (1, usize::MAX),
            (1 << 17, source.input_len() / (1 << 17)),
            (1 << 22, 0),
        ];
        for (width, row) in invalid {
            source.reset_io_metrics();
            assert!(read_row(&source, width, row).is_err(), "width {width}, row {row}");
            let io = source.io_metrics_snapshot();
            assert_eq!(io.read_calls, 0, "width {width}, row {row}");
            assert_eq!(io.read_bytes, 0, "width {width}, row {row}");
        }

        let small = small_source();
        small.reset_io_metrics();
        assert!(read_row(&small, 16, 0).is_err(), "source-width mismatch");
        let io = small.io_metrics_snapshot();
        assert_eq!(io.read_calls, 0);
        assert_eq!(io.read_bytes, 0);
    }
}

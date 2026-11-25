//! One bounded H21 Map-to-packed-row join followed by the existing log41
//! row commitment and partial-V kernels. This is not a full witness or proof.

use super::*;
use crate::packed::PackedFile;
use std::{
    fs::OpenOptions,
    io::Write,
    path::PathBuf,
    sync::atomic::{AtomicU64, Ordering},
    time::{SystemTime, UNIX_EPOCH},
};

const LOG_N: usize = 25;
const SIGMA_ROWS: usize = 1 << 21;
const SIGMA_ROW_BYTES: usize = SIGMA_ROWS / 8;
const OWNER_ROW_BYTES: usize = 1 << 17;
const OWNER_ROW_BITS: usize = 1 << 20;
const SAMPLE_ROWS: usize = 16;
const SAMPLE_FILE_BYTES: usize = SAMPLE_ROWS * SIGMA_ROW_BYTES;
const GLOBAL_ROWS: usize = 1 << 20;
const ACTIVE_GLOBAL_ROWS: usize = N / 2;
const REQUIRED_GLOBAL_ROWS: [usize; 10] = [
    416_767, 417_279, 417_791, 418_303, 418_815, 419_327, 419_839, 420_351, 420_831, 420_863,
];
const SELECTED_GLOBAL_ROWS: [usize; SAMPLE_ROWS] = [
    0,
    1,
    262_144,
    416_767,
    417_279,
    417_791,
    418_303,
    418_815,
    419_327,
    419_839,
    420_351,
    420_831,
    420_863,
    524_288,
    786_432,
    GLOBAL_ROWS - 1,
];
const D_OWNER: usize = (D_MAX_HEIGHT - 2) as usize;
const B_OWNER: usize = (B_MAX_Q * 1024 + 959) as usize;

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

struct TempPackedFile(PathBuf);

impl TempPackedFile {
    fn write(rows: &[Vec<u8>], label: &str) -> Self {
        assert_eq!(rows.len(), SAMPLE_ROWS);
        assert!(rows.iter().all(|row| row.len() == SIGMA_ROW_BYTES));
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("system clock after epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "nipopow-candidate95-{}-{nonce}-{}-{label}.bits",
            std::process::id(),
            NEXT_TEMP.fetch_add(1, Ordering::Relaxed),
        ));
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .expect("create candidate95 packed sample once");
        for row in rows {
            file.write_all(row).expect("write candidate95 packed row");
        }
        file.sync_all().expect("sync candidate95 packed sample");
        assert_eq!(file.metadata().unwrap().len(), SAMPLE_FILE_BYTES as u64);
        drop(file);
        Self(path)
    }
}

impl Drop for TempPackedFile {
    fn drop(&mut self) {
        if !self.0.as_os_str().is_empty() {
            let _ = std::fs::remove_file(&self.0);
        }
    }
}

// Field order closes the locked handle before its temporary file is removed.
struct OpenedSample {
    source: PackedFile,
    _file: TempPackedFile,
    rows: Vec<Vec<u8>>,
}

fn open_sample(rows: &[Vec<u8>], label: &str) -> OpenedSample {
    let file = TempPackedFile::write(rows, label);
    let source = PackedFile::open_with_limit(&file.0, LOG_N, LOG_N)
        .expect("open immutable candidate95 packed sample");
    let readback = source
        .read_rows_bytes_with_limit_for_test(SIGMA_ROWS, SAMPLE_FILE_BYTES)
        .expect("same-handle bounded candidate95 row readback");
    assert_eq!(readback.len(), SAMPLE_ROWS);
    assert!(readback.iter().all(|row| row.len() == SIGMA_ROW_BYTES));
    OpenedSample {
        source,
        _file: file,
        rows: readback,
    }
}

struct PreparedJoin {
    opened: OpenedSample,
    global_rows: Vec<usize>,
    sample_sha256: String,
    required_rows_sha256: String,
    map_read_bytes: u64,
    frame_s: f64,
    plan_s: f64,
    rows_s: f64,
    map_s: f64,
    map_consumers: usize,
    map_negatives: usize,
}

fn hex95(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn sha256(bytes: &[u8]) -> String {
    hex95(&role0_sha256(bytes).expect("candidate95 SHA-256"))
}

fn rows_digest(rows: &[usize]) -> String {
    let canonical = rows
        .iter()
        .map(usize::to_string)
        .collect::<Vec<_>>()
        .join(",");
    sha256(canonical.as_bytes())
}

fn global_slot(global_rows: &[usize], row: usize) -> Result<usize, String> {
    let slot = global_rows
        .binary_search(&row)
        .map_err(|_| format!("missing global sigma row {row}"))?;
    if global_rows.get(slot).copied() != Some(row) {
        return Err("global sigma row coordinate alias".into());
    }
    Ok(slot)
}

fn owner_slot(global_rows: &[usize], owner: usize) -> Result<(usize, usize), String> {
    if owner >= N {
        return Err("native owner outside H21 domain".into());
    }
    let row = owner >> 1;
    let slot = global_slot(global_rows, row)
        .map_err(|_| format!("owner/global row coordinate mismatch owner={owner} row={row}"))?;
    let half = owner & 1;
    if ((global_rows[slot] << 1) | half) != owner {
        return Err("owner/global row coordinate alias".into());
    }
    Ok((slot, half))
}

fn validate_selected_sample(
    global_rows: &[usize],
    rows: &[Vec<u8>],
    map_owners: &BTreeSet<usize>,
) -> Result<(), String> {
    if global_rows.len() != SAMPLE_ROWS || rows.len() != SAMPLE_ROWS {
        return Err("selected sample row count mismatch".into());
    }
    if !global_rows.windows(2).all(|pair| pair[0] < pair[1]) {
        return Err("selected global rows are not sorted unique coordinates".into());
    }
    if global_rows.last().copied() != Some(GLOBAL_ROWS - 1)
        || global_rows.first().copied() != Some(0)
    {
        return Err("selected global row endpoint mismatch".into());
    }
    for required in REQUIRED_GLOBAL_ROWS {
        global_slot(global_rows, required)
            .map_err(|_| format!("required Map sigma row missing: {required}"))?;
    }
    let owner_rows: BTreeSet<usize> = map_owners.iter().map(|owner| owner >> 1).collect();
    let required_owner_rows: BTreeSet<usize> = REQUIRED_GLOBAL_ROWS.iter().copied().collect();
    if owner_rows != required_owner_rows {
        return Err(format!(
            "Map owner sigma-row set differs: actual={owner_rows:?} required={required_owner_rows:?}"
        ));
    }
    if rows.iter().any(|row| row.len() != SIGMA_ROW_BYTES) {
        return Err("selected packed row byte width mismatch".into());
    }
    for owner in map_owners {
        owner_slot(global_rows, *owner)?;
    }
    for (global_row, row) in global_rows.iter().zip(rows) {
        if *global_row >= ACTIVE_GLOBAL_ROWS && row.iter().any(|byte| *byte != 0) {
            return Err(format!("nonzero global-row padding at row {global_row}"));
        }
    }
    Ok(())
}

fn hydrate_owner(
    global_rows: &[usize],
    packed_rows: &[Vec<u8>],
    templates: &BTreeMap<usize, NativePackedRow>,
    owner: usize,
) -> Result<NativePackedRow, String> {
    let (slot, half) = owner_slot(global_rows, owner)?;
    let packed = packed_rows
        .get(slot)
        .ok_or("selected packed coordinate slot missing")?;
    if packed.len() != SIGMA_ROW_BYTES {
        return Err("selected packed coordinate row width mismatch".into());
    }
    let start = half * OWNER_ROW_BYTES;
    let end = start + OWNER_ROW_BYTES;
    let source = packed
        .get(start..end)
        .ok_or("selected packed native owner half missing")?;
    let template = templates
        .get(&owner)
        .ok_or_else(|| format!("source metadata template missing owner={owner}"))?;
    if template.owner() != owner || template.packed_bytes().len() != OWNER_ROW_BYTES {
        return Err(format!(
            "source metadata owner/width mismatch owner={owner}"
        ));
    }
    template.with_packed_bytes_for_test(source)
}

fn flatten_rows(rows: &[Vec<u8>]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(SAMPLE_FILE_BYTES);
    for row in rows {
        bytes.extend_from_slice(row);
    }
    assert_eq!(bytes.len(), SAMPLE_FILE_BYTES);
    bytes
}

fn flip_owner_bit(global_rows: &[usize], rows: &mut [Vec<u8>], owner: usize, bit: usize) {
    assert!(bit < OWNER_ROW_BITS);
    let (slot, half) = owner_slot(global_rows, owner).expect("mutant owner coordinate");
    let index = half * OWNER_ROW_BYTES + bit / 8;
    rows[slot][index] ^= 1 << (bit % 8);
}

fn consumer_from_rows(
    global_rows: &[usize],
    packed_rows: &[Vec<u8>],
    templates: &BTreeMap<usize, NativePackedRow>,
    foreign_owners: &BTreeSet<usize>,
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
    map: &Map,
) -> Result<(), String> {
    let b_row = hydrate_owner(global_rows, packed_rows, templates, B_OWNER)?;
    let mut foreign = BTreeMap::new();
    for owner in foreign_owners {
        foreign.insert(
            *owner,
            hydrate_owner(global_rows, packed_rows, templates, *owner)?,
        );
    }
    validate_native_bank53_map_consumer(plan, prefix, map, B_OWNER, 0, &b_row, &foreign)
}

fn expect_packed_consumer_rejection(
    mutated_rows: &[Vec<u8>],
    label: &str,
    expected: &[&str],
    global_rows: &[usize],
    templates: &BTreeMap<usize, NativePackedRow>,
    foreign_owners: &BTreeSet<usize>,
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
    map: &Map,
) {
    let opened = open_sample(mutated_rows, label);
    assert!(
        opened.rows.as_slice() == mutated_rows,
        "{label} packed mutation differs after same-handle readback"
    );
    let error = consumer_from_rows(
        global_rows,
        &opened.rows,
        templates,
        foreign_owners,
        plan,
        prefix,
        map,
    )
    .expect_err("isolated packed Map mutant must reach and fail the real consumer");
    assert!(
        expected.iter().any(|needle| error.contains(needle)),
        "{label} unexpected consumer error: {error}"
    );
    drop(opened);
}

fn expect_d_packed_consumer_rejection(
    mutated_rows: &[Vec<u8>],
    label: &str,
    expected: &[&str],
    global_rows: &[usize],
    templates: &BTreeMap<usize, NativePackedRow>,
    plan: &WorkTreeHistoryPlan,
    prefix: &NativePrefix,
    map: &Map,
) {
    let opened = open_sample(mutated_rows, label);
    assert!(
        opened.rows.as_slice() == mutated_rows,
        "{label} packed mutation differs after same-handle readback"
    );
    let d_row = hydrate_owner(global_rows, &opened.rows, templates, D_OWNER)
        .expect("hydrate D destination from mutant packed input");
    let error = validate_native_bank53_map_consumer(
        plan,
        prefix,
        map,
        D_OWNER,
        0,
        &d_row,
        &BTreeMap::new(),
    )
    .expect_err("isolated packed D helper mutant must reach and fail the real consumer");
    assert!(
        expected.iter().any(|needle| error.contains(needle)),
        "{label} unexpected D consumer error: {error}"
    );
    drop(d_row);
    drop(opened);
}

fn source_rows_from_pinned_frame() -> PreparedJoin {
    assert!(SELECTED_GLOBAL_ROWS
        .windows(2)
        .all(|pair| pair[0] < pair[1]));
    let frame_started = Instant::now();
    let path =
        std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned H21 frame environment variable");
    let path = PathBuf::from(path);
    assert!(path.is_absolute(), "frame path must be absolute");
    let before = std::fs::symlink_metadata(&path).expect("pinned frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES, "pinned frame length");
    let file = std::fs::File::open(&path).expect("open pinned H21 frame");
    assert_eq!(file.metadata().unwrap().len(), FRAME_BYTES);
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)
        .expect("streaming pinned frame SHA256 setup");
    preamble(&mut frame, 1_827_839, N as u32).expect("pinned ERFV preamble");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)
            .expect("canonical linked native H21 prefix");
        assert_eq!(headers.remaining, 0, "all H21 frame records consumed");
        (prefix, headers.extensions)
    };
    assert_eq!(prefix.header_count(), N);
    assert_eq!(frame.offset, PREFIX_BYTES, "exact H21 frame prefix bytes");
    assert_eq!(extensions, EXTENSIONS, "exact H21 frame extension count");
    frame
        .finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256)
        .expect("whole pinned H21 frame identity");
    let after = std::fs::symlink_metadata(&path).expect("pinned frame restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), FRAME_BYTES);
    let frame_s = frame_started.elapsed().as_secs_f64();

    let plan_started = Instant::now();
    let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())
        .expect("same-root/total H21 parent plan");
    validate_native_plan_input(&plan, &prefix).expect("native H21 parent exact root/total");
    let exports = NativeExports::new_for_history(&plan, &prefix)
        .expect("H21 native exports bound to admitted parent");
    let map = Map::from_parent_modern_global_u(
        &plan,
        E,
        LowerSelector {
            source: LowerSource::HeaderDifficulty {
                height: D_MAX_HEIGHT,
            },
            branch: LowerBranch::Pivot(LOWER_PIVOT),
        },
    )
    .expect("same-parent selected H21 Bank53 Map");
    assert_eq!(map.binding().parent_root, Some(prefix.root()));
    let (_d_inputs, d_imports) = typed_inputs(&map, D_OWNER as u64, &exports);
    assert_eq!(d_imports.len(), 1, "selected D import count");
    assert_eq!(d_imports[0].owner, D_OWNER as u64);
    assert_eq!(d_imports[0].kind, Kind::Difficulty);
    let (_b_inputs, b_imports) = typed_inputs(&map, B_OWNER as u64, &exports);
    assert_eq!(
        map_import_signature(&map, D_OWNER),
        BTreeSet::from([(D_OWNER as u64, Kind::Difficulty),])
    );
    assert_eq!(
        map_import_signature(&map, B_OWNER),
        expected_q821_imports(B_OWNER),
        "exact q821 B typed import roster",
    );
    let foreign_owners: BTreeSet<usize> = b_imports
        .iter()
        .filter(|import| import.owner != B_OWNER as u64)
        .map(|import| import.owner as usize)
        .collect();
    assert_eq!(foreign_owners.len(), 16, "q821 B foreign native owners");
    let mut q821_owners = foreign_owners.clone();
    q821_owners.insert(B_OWNER);
    assert_eq!(q821_owners.len(), 17, "all q821 B native owners");
    let mut map_owners = foreign_owners.clone();
    map_owners.extend([B_OWNER, D_OWNER]);
    assert_eq!(
        map_owners.len(),
        18,
        "all Map destination and foreign owners"
    );
    assert!(!foreign_owners.contains(&D_OWNER));
    let plan_s = plan_started.elapsed().as_secs_f64();

    let rows_started = Instant::now();
    let producer = NativeOwnerProducer::new_for_history(&plan, &prefix)
        .expect("source-owned producer bound to exact H21 parent");
    let d_template = producer
        .produce_bank53_map_h21_for_test(D_OWNER, &map, 0)
        .expect("source-owned D841727 context-0 Map row");
    let b_template = producer
        .produce_bank53_map_h21_for_test(B_OWNER, &map, 0)
        .expect("source-owned q821 B841663 context-0 Map row");
    assert_eq!(d_template.owner(), D_OWNER);
    assert_eq!(b_template.owner(), B_OWNER);
    assert_eq!(d_template.packed_bytes().len(), OWNER_ROW_BYTES);
    assert_eq!(b_template.packed_bytes().len(), OWNER_ROW_BYTES);
    let mut templates = BTreeMap::from([(D_OWNER, d_template), (B_OWNER, b_template)]);
    let mut canonical_rows = Vec::with_capacity(SAMPLE_ROWS);
    for global_row in SELECTED_GLOBAL_ROWS {
        if global_row >= ACTIVE_GLOBAL_ROWS {
            canonical_rows.push(vec![0u8; SIGMA_ROW_BYTES]);
            continue;
        }
        let mut row = Vec::with_capacity(SIGMA_ROW_BYTES);
        for owner in [global_row * 2, global_row * 2 + 1] {
            let source_row = if let Some(template) = templates.get(&owner) {
                template.clone()
            } else {
                producer
                    .produce(owner)
                    .expect("source-owned native sigma owner row")
            };
            assert_eq!(source_row.owner(), owner);
            assert_eq!(source_row.packed_bytes().len(), OWNER_ROW_BYTES);
            if foreign_owners.contains(&owner) {
                templates.insert(owner, source_row.clone());
            }
            row.extend_from_slice(source_row.packed_bytes());
        }
        assert_eq!(row.len(), SIGMA_ROW_BYTES);
        canonical_rows.push(row);
    }
    drop(producer);
    assert_eq!(templates.len(), 18, "exact source metadata template set");
    let rows_s = rows_started.elapsed().as_secs_f64();
    let global_rows = SELECTED_GLOBAL_ROWS.to_vec();

    // The one baseline PackedFile remains open from Map readback through the
    // later PCS commit and partial-V product. Map consumers only see bytes
    // reconstructed from its own immutable, same-handle row readback.
    let map_started = Instant::now();
    let opened = open_sample(&canonical_rows, "base");
    assert_eq!(
        opened.rows, canonical_rows,
        "packed readback equals source rows"
    );
    drop(canonical_rows);
    validate_selected_sample(&global_rows, &opened.rows, &map_owners)
        .expect("sorted global row map, source owners and zero padding");
    let sample_bytes = flatten_rows(&opened.rows);
    let sample_sha256 = sha256(&sample_bytes);
    drop(sample_bytes);
    let readback_io = opened.source.io_metrics_snapshot();
    assert_eq!(readback_io.read_bytes, SAMPLE_FILE_BYTES as u64);
    assert_eq!(readback_io.read_calls, SAMPLE_ROWS as u64);

    for owner in &map_owners {
        let hydrated = hydrate_owner(&global_rows, &opened.rows, &templates, *owner)
            .expect("hydrate every Map owner from same PackedFile input");
        assert_eq!(
            hydrated.packed_bytes(),
            templates[owner].packed_bytes(),
            "same packed coordinate bytes owner={owner}",
        );
    }
    let d_row = hydrate_owner(&global_rows, &opened.rows, &templates, D_OWNER)
        .expect("hydrate D destination from packed input");
    let d_foreign = BTreeMap::new();
    validate_native_bank53_map_consumer(&plan, &prefix, &map, D_OWNER, 0, &d_row, &d_foreign)
        .expect("D Map consumer uses the exact packed destination bytes");

    let mut map_negatives = 0usize;
    let mut wrong_d_helper = opened.rows.clone();
    flip_owner_bit(
        &global_rows,
        &mut wrong_d_helper,
        D_OWNER,
        BANK53_BASE + 672,
    );
    expect_d_packed_consumer_rejection(
        &wrong_d_helper,
        "d-destination-helper",
        &["physical residual"],
        &global_rows,
        &templates,
        &plan,
        &prefix,
        &map,
    );
    map_negatives += 1;
    drop(wrong_d_helper);

    consumer_from_rows(
        &global_rows,
        &opened.rows,
        &templates,
        &foreign_owners,
        &plan,
        &prefix,
        &map,
    )
    .expect("q821 B Map consumer uses destination and foreign bytes from same PackedFile");

    for kind in [Kind::Difficulty, Kind::Timestamp] {
        let import = *b_imports
            .iter()
            .find(|import| import.kind == kind && import.owner != B_OWNER as u64)
            .expect("q821 B foreign typed D/T import");
        let mut changed = opened.rows.clone();
        flip_owner_bit(
            &global_rows,
            &mut changed,
            import.owner as usize,
            import.local,
        );
        let label = match kind {
            Kind::Difficulty => "foreign-difficulty",
            Kind::Timestamp => "foreign-timestamp",
        };
        expect_packed_consumer_rejection(
            &changed,
            label,
            &["typed import differs"],
            &global_rows,
            &templates,
            &foreign_owners,
            &plan,
            &prefix,
            &map,
        );
        map_negatives += 1;
        drop(changed);
    }

    let mut wrong_helper = opened.rows.clone();
    flip_owner_bit(&global_rows, &mut wrong_helper, B_OWNER, BANK53_BASE + 672);
    expect_packed_consumer_rejection(
        &wrong_helper,
        "destination-helper",
        &["physical residual"],
        &global_rows,
        &templates,
        &foreign_owners,
        &plan,
        &prefix,
        &map,
    );
    map_negatives += 1;
    drop(wrong_helper);

    let mut swapped_halves = opened.rows.clone();
    let b_slot = global_slot(&global_rows, B_OWNER >> 1).unwrap();
    let source_slot = global_slot(&global_rows, (B_OWNER - 1) >> 1).unwrap();
    assert_eq!(
        b_slot, source_slot,
        "B destination and adjacent owner share one sigma row"
    );
    let (even_half, odd_half) = swapped_halves[b_slot].split_at_mut(OWNER_ROW_BYTES);
    even_half.swap_with_slice(odd_half);
    expect_packed_consumer_rejection(
        &swapped_halves,
        "adjacent-owner-swap",
        &["typed import differs", "physical residual"],
        &global_rows,
        &templates,
        &foreign_owners,
        &plan,
        &prefix,
        &map,
    );
    map_negatives += 1;
    drop(swapped_halves);

    let mut map_tail = opened.rows.clone();
    flip_owner_bit(
        &global_rows,
        &mut map_tail,
        B_OWNER,
        BANK53_BASE + BANK53_MAP_LIVE_BITS,
    );
    expect_packed_consumer_rejection(
        &map_tail,
        "map-tail",
        &["Map tail/Score slack"],
        &global_rows,
        &templates,
        &foreign_owners,
        &plan,
        &prefix,
        &map,
    );
    map_negatives += 1;
    drop(map_tail);

    let base_b = hydrate_owner(&global_rows, &opened.rows, &templates, B_OWNER).unwrap();
    let mut base_foreign = BTreeMap::new();
    for owner in &foreign_owners {
        base_foreign.insert(
            *owner,
            hydrate_owner(&global_rows, &opened.rows, &templates, *owner).unwrap(),
        );
    }
    let mut missing_owner = base_foreign.clone();
    missing_owner.pop_first();
    assert!(validate_native_bank53_map_consumer(
        &plan,
        &prefix,
        &map,
        B_OWNER,
        0,
        &base_b,
        &missing_owner,
    )
    .unwrap_err()
    .contains("foreign owner census"));
    map_negatives += 1;
    drop(missing_owner);
    drop(base_foreign);
    drop(base_b);

    let mut coordinate_alias = global_rows.clone();
    coordinate_alias[b_slot] += 1;
    assert!(owner_slot(&coordinate_alias, B_OWNER)
        .unwrap_err()
        .contains("owner/global row coordinate mismatch"));
    map_negatives += 1;
    drop(coordinate_alias);

    let mut duplicate_global_row = global_rows.clone();
    duplicate_global_row[2] = duplicate_global_row[1];
    assert!(
        validate_selected_sample(&duplicate_global_row, &opened.rows, &map_owners)
            .unwrap_err()
            .contains("sorted unique")
    );
    map_negatives += 1;
    drop(duplicate_global_row);

    let mut nonzero_padding = opened.rows.clone();
    let padding_slot = global_slot(&global_rows, GLOBAL_ROWS - 1).unwrap();
    nonzero_padding[padding_slot][0] |= 1;
    let opened_padding = open_sample(&nonzero_padding, "padding-bit");
    assert!(
        opened_padding.rows.as_slice() == nonzero_padding.as_slice(),
        "padding mutant differs after same-handle readback"
    );
    assert!(
        validate_selected_sample(&global_rows, &opened_padding.rows, &map_owners)
            .unwrap_err()
            .contains("nonzero global-row padding")
    );
    drop(opened_padding);
    drop(nonzero_padding);
    map_negatives += 1;
    assert_eq!(map_negatives, 10);

    let map_s = map_started.elapsed().as_secs_f64();
    let required_rows_sha256 = rows_digest(&REQUIRED_GLOBAL_ROWS);
    println!(
        "CANDIDATE95_ROWS_RECONSTRUCTED rows={SAMPLE_ROWS} first_global_row={} last_global_row={} required_rows={} required_rows_sha256={required_rows_sha256} readback_source_sha256={sample_sha256} sample_file_bytes={SAMPLE_FILE_BYTES} map_owners={} q821_owners={} context=0 frame_s={frame_s:.6} plan_s={plan_s:.6} rows_s={rows_s:.6} map_s={map_s:.6} frame_sha256={FRAME_SHA256} full_h21_witness=false",
        global_rows[0],
        global_rows[SAMPLE_ROWS - 1],
        REQUIRED_GLOBAL_ROWS.len(),
        map_owners.len(),
        q821_owners.len(),
    );
    std::io::stdout()
        .flush()
        .expect("candidate95 rows marker flush");

    // Drop all source-owned plan/export/Map/template state before G1 setup.
    drop(d_row);
    drop(templates);
    drop(_b_inputs);
    drop(_d_inputs);
    drop(b_imports);
    drop(d_imports);
    drop(exports);
    drop(map);
    drop(plan);
    drop(prefix);

    PreparedJoin {
        opened,
        global_rows,
        sample_sha256,
        required_rows_sha256,
        map_read_bytes: readback_io.read_bytes,
        frame_s,
        plan_s,
        rows_s,
        map_s,
        map_consumers: 2,
        map_negatives,
    }
}

#[test]
#[ignore = "pinned H21 frame, bounded same-file Map/PCS join and reviewed Job runner required"]
fn h21_q821_map_same_packed_log41_partial_v_join() {
    let started = Instant::now();
    let prepared = source_rows_from_pinned_frame();
    assert_eq!(prepared.global_rows.len(), SAMPLE_ROWS);
    assert_eq!(prepared.map_read_bytes, SAMPLE_FILE_BYTES as u64);
    println!(
        "CANDIDATE95_PHASE phase=map_consumer_from_same_packed_rows elapsed_s={:.6}",
        prepared.map_s
    );
    std::io::stdout()
        .flush()
        .expect("candidate95 Map phase flush");

    let pcs = crate::packed::candidate94_real_rows_packed_tests::run_candidate95_same_source(
        &prepared.opened.source,
        &prepared.global_rows,
        &prepared.opened.rows,
    );
    assert_eq!(pcs.sample_sha256, prepared.sample_sha256);
    assert_eq!(pcs.g1_commit_rows, SAMPLE_ROWS);
    assert!(pcs.nonzero_v_columns > 0);
    assert_eq!(pcs.pcs_negatives, 1);
    let same_handle_read_bytes = prepared
        .map_read_bytes
        .checked_add(pcs.commit_read_bytes)
        .and_then(|bytes| bytes.checked_add(pcs.partial_v_read_bytes))
        .and_then(|bytes| bytes.checked_add(pcs.pcs_negative_read_bytes))
        .expect("candidate95 packed read byte total");
    assert_eq!(same_handle_read_bytes, 4 * SAMPLE_FILE_BYTES as u64);
    assert_eq!(prepared.map_consumers, 2);
    assert_eq!(prepared.map_negatives, 10);

    let elapsed_s = started.elapsed().as_secs_f64();
    println!(
        "CANDIDATE95_H21_MAP_PACKED_JOIN_PASS scope=bank53-map-component-plus-partial-v sample_rows={SAMPLE_ROWS} first_global_row={} last_global_row={} required_rows={} required_rows_sha256={} map_owners=18 q821_owners=17 context=0 sigma=21 global_row_bits=20 file_log_n={LOG_N} sample_file_bytes={SAMPLE_FILE_BYTES} sample_sha256={} readback_source_sha256={} map_read_bytes={} commit_read_bytes={} partial_v_read_bytes={} pcs_negative_read_bytes={} same_handle_read_bytes={} g1_commit_rows={} nonzero_v_columns={} map_consumer_count={} map_negatives={} pcs_negatives={} negatives={} frame_s={:.6} plan_s={:.6} rows_s={:.6} map_s={:.6} commit_s={:.6} partial_v_s={:.6} elapsed_s={elapsed_s:.6} frame_sha256={FRAME_SHA256} full_log41_commitment=false partial_v=true full_v=false full_h21_witness=false same_x=false gkr_dory=false proof=false",
        prepared.global_rows[0],
        prepared.global_rows[SAMPLE_ROWS - 1],
        REQUIRED_GLOBAL_ROWS.len(),
        prepared.required_rows_sha256,
        pcs.sample_sha256,
        pcs.sample_sha256,
        prepared.map_read_bytes,
        pcs.commit_read_bytes,
        pcs.partial_v_read_bytes,
        pcs.pcs_negative_read_bytes,
        same_handle_read_bytes,
        pcs.g1_commit_rows,
        pcs.nonzero_v_columns,
        prepared.map_consumers,
        prepared.map_negatives,
        pcs.pcs_negatives,
        prepared.map_negatives + pcs.pcs_negatives,
        prepared.frame_s,
        prepared.plan_s,
        prepared.rows_s,
        prepared.map_s,
        pcs.commit_s,
        pcs.partial_v_s,
    );
    std::io::stdout()
        .flush()
        .expect("candidate95 terminal marker flush");
    drop(prepared);
}

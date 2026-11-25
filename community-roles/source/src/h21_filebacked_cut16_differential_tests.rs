//! File-backed H21 role-1 differential through local round 15 and the cut-16
//! boundary. Candidate I/O is deliberately limited to ten whole 8-KiB blocks
//! per round and one complete row per owner after round 15. The dense oracle
//! opens and reads the immutable fixture independently.

use crate::{
    daa_history_roster::{DaaHistoryRoster, OwnerClass},
    gkr,
    native_prefix_auth_plan::role0_sha256,
    sparse::Term,
    work_tree_history_plan::WorkTreeHistoryPlan,
};
use ark_bn254::Fr;
use ark_ff::{Field, One, Zero};
use std::{
    collections::{BTreeSet, HashMap},
    fs::{self, File, OpenOptions},
    io::{Read, Seek, SeekFrom, Write},
    path::{Path, PathBuf},
};

const HEADERS: u64 = 1_827_840;
const SLOT_LOG: usize = 21;
const OWNERS: [usize; 2] = [9_214, 9_215];
const INPUT_BITS: usize = 20;
const INPUTS: usize = 1 << INPUT_BITS;
const ROWS: usize = 1 << 19;
const CUT: usize = 16;
const CUT_WIDTH: usize = INPUTS >> CUT;
const TERMS: usize = 396_561;
const ROW_BYTES: usize = INPUTS / 8;
const BLOCK_BYTES: usize = 8 * 1024;
const BLOCK_BITS: usize = BLOCK_BYTES * 8;
const ACTIVE_BLOCKS: [usize; 10] = [0, 1, 2, 3, 4, 8, 9, 10, 12, 15];

struct State {
    a: Vec<Fr>,
    b: Vec<Fr>,
    x: Vec<Fr>,
}

impl State {
    fn zeros(width: usize) -> Self {
        Self { a: vec![Fr::zero(); width], b: vec![Fr::zero(); width],
            x: vec![Fr::zero(); width] }
    }
    fn width(&self) -> usize {
        assert_eq!(self.a.len(), self.b.len());
        assert_eq!(self.a.len(), self.x.len());
        self.a.len()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ReadEvent {
    round: usize,
    owner: usize,
    offset: u64,
    requested: usize,
    succeeded: bool,
}

#[derive(Default)]
struct ReadTrace {
    events: Vec<ReadEvent>,
    logical_bytes: usize,
    unique_offsets: BTreeSet<(usize, u64)>,
}

struct CandidateReader {
    files: [File; 2],
    trace: ReadTrace,
}

impl CandidateReader {
    fn open(paths: &[PathBuf; 2]) -> Result<Self, String> {
        let mut opened = Vec::with_capacity(2);
        for path in paths {
            let file = File::open(path).map_err(|e| format!("open {}: {e}", path.display()))?;
            let len = file.metadata().map_err(|e| format!("stat {}: {e}", path.display()))?.len();
            if len != ROW_BYTES as u64 {
                return Err(format!("packed row length {} expected {ROW_BYTES}", len));
            }
            opened.push(file);
        }
        let files: [File; 2] = opened.try_into().map_err(|_| "two owner files".to_string())?;
        Ok(Self { files, trace: ReadTrace::default() })
    }

    fn read_at(&mut self, round: usize, owner: usize, offset: u64, buf: &mut [u8]) -> Result<(), String> {
        let event = ReadEvent { round, owner: OWNERS[owner], offset, requested: buf.len(), succeeded: false };
        self.trace.events.push(event);
        let index = self.trace.events.len() - 1;
        let result = self.files[owner].seek(SeekFrom::Start(offset))
            .and_then(|_| self.files[owner].read_exact(buf));
        if let Err(error) = result {
            return Err(format!("read owner={owner} offset={offset} len={}: {error}", buf.len()));
        }
        self.trace.events[index].succeeded = true;
        self.trace.logical_bytes = self.trace.logical_bytes.checked_add(buf.len())
            .ok_or("logical byte count overflow")?;
        for byte in 0..buf.len() {
            self.trace.unique_offsets.insert((owner, offset + byte as u64));
        }
        Ok(())
    }

    fn read_active_blocks(&mut self, round: usize, owner_index: usize) -> Result<HashMap<usize, Vec<u8>>, String> {
        let mut blocks = HashMap::with_capacity(ACTIVE_BLOCKS.len());
        for block in ACTIVE_BLOCKS {
            let mut bytes = vec![0u8; BLOCK_BYTES];
            self.read_at(round, owner_index, (block * BLOCK_BYTES) as u64, &mut bytes)?;
            blocks.insert(block, bytes);
        }
        Ok(blocks)
    }

    fn read_complete_row(&mut self, owner_index: usize) -> Result<Vec<u8>, String> {
        let mut bytes = vec![0u8; ROW_BYTES];
        self.read_at(CUT, owner_index, 0, &mut bytes)?;
        Ok(bytes)
    }
}

fn synthetic_bit(owner: usize, local: usize) -> bool {
    let mixed = (local as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15)
        .rotate_left(17) ^ (owner as u64).wrapping_mul(0xd1b5_4a32_d192_ed03);
    (mixed & 7) == 0 || ((local ^ owner) & 127) == 0
}

fn packed_bytes(owner: usize) -> Vec<u8> {
    let mut bytes = vec![0u8; ROW_BYTES];
    for local in 0..INPUTS {
        if synthetic_bit(owner, local) { bytes[local >> 3] |= 1 << (local & 7); }
    }
    bytes
}

fn packed_bit(bytes: &[u8], local: usize) -> Fr {
    Fr::from(((bytes[local >> 3] >> (local & 7)) & 1) as u64)
}

fn active_bit(blocks: &HashMap<usize, Vec<u8>>, local: usize) -> Fr {
    let block = local / BLOCK_BITS;
    let offset = local % BLOCK_BITS;
    let bytes = blocks.get(&block).expect("c264 left/right active block support");
    Fr::from(((bytes[offset >> 3] >> (offset & 7)) & 1) as u64)
}

fn write_fixture(output: &Path) -> [PathBuf; 2] {
    assert!(output.is_absolute(), "C266_OUTPUT_DIR must be absolute");
    assert!(crate::preview_test_paths::absolute_outside_source(output),
        "fixture directory must be outside source");
    fs::create_dir_all(output).expect("runner output directory");
    let paths = [output.join("owner-9214-x.bin"), output.join("owner-9215-x.bin")];
    for (index, owner) in OWNERS.into_iter().enumerate() {
        let bytes = packed_bytes(owner);
        assert_eq!(bytes.len(), ROW_BYTES);
        let mut file = OpenOptions::new().write(true).create_new(true).open(&paths[index])
            .unwrap_or_else(|e| panic!("create unique fixture {}: {e}", paths[index].display()));
        file.write_all(&bytes).expect("write deterministic packed row");
        file.sync_all().expect("close fixture bytes to storage");
        drop(file);
        assert_eq!(fs::metadata(&paths[index]).unwrap().len(), ROW_BYTES as u64);
        let digest = role0_sha256(&bytes).expect("fixture SHA-256");
        println!("C266_FIXTURE owner={owner} bytes={} sha256={}", bytes.len(), hex(&digest));
    }
    paths
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b:02x}")).collect()
}

fn visit_owner(roster: &DaaHistoryRoster<'_>, owner: usize,
    mut sink: impl FnMut(&Term, usize, usize, usize) -> Result<(), String>) {
    assert_eq!(roster.owner_class(owner as u64).expect("owner class"), OwnerClass::Carry);
    let row_base = owner.checked_mul(ROWS).expect("row base");
    let input_base = owner.checked_mul(INPUTS).expect("input base");
    let mut observed = 0usize;
    let counts = roster.visit_header_terms(owner as u64, |term| {
        let row = term.row.checked_sub(row_base).ok_or("row before owner")?;
        let left = term.gate.left.checked_sub(input_base).ok_or("left before owner")?;
        let right = term.gate.right.checked_sub(input_base).ok_or("right before owner")?;
        if row >= ROWS || left >= INPUTS || right >= INPUTS {
            return Err("role-1 callback term escapes physical owner".into());
        }
        observed = observed.checked_add(1).ok_or("callback count overflow")?;
        sink(&term, row, left, right)
    }).expect("bounded H21 role-1 callback");
    assert_eq!(observed, counts.emitted);
    assert_eq!(observed, TERMS);
    assert_eq!(counts.omitted_worktree, 78_194);
    assert_eq!(counts.omitted_mature_a4, 0);
    assert_eq!(counts.omitted_short_a4, 0);
}

fn dense_oracle(roster: &DaaHistoryRoster<'_>, rows: &[Vec<u8>; 2], row_weights: &[Fr])
    -> ([State; 2], Fr) {
    let mut states = [State::zeros(INPUTS), State::zeros(INPUTS)];
    let mut direct = Fr::zero();
    for j in 0..2 {
        for local in 0..INPUTS {
            states[j].x[local] = packed_bit(&rows[j], local);
        }
        visit_owner(roster, OWNERS[j], |term, row, left, right| {
            let weight = row_weights[row];
            let xl = packed_bit(&rows[j], left);
            let xr = packed_bit(&rows[j], right);
            direct += weight * (term.gate.c0 + term.gate.c1 * xl + term.gate.c2 * xr
                + term.gate.c3 * xl * xr);
            states[j].a[left] += weight * (term.gate.c1 + term.gate.c3 * xr);
            states[j].b[left] += weight * (term.gate.c0 + term.gate.c2 * xr);
            Ok(())
        });
    }
    (states, direct)
}

fn candidate_a_b(roster: &DaaHistoryRoster<'_>, owner_index: usize,
    row_weights: &[Fr], blocks: &HashMap<usize, Vec<u8>>) -> (Vec<Fr>, Vec<Fr>) {
    let mut a = vec![Fr::zero(); INPUTS];
    let mut b = vec![Fr::zero(); INPUTS];
    visit_owner(roster, OWNERS[owner_index], |term, row, left, right| {
        let weight = row_weights[row];
        let xr = active_bit(blocks, right);
        a[left] += weight * (term.gate.c1 + term.gate.c3 * xr);
        b[left] += weight * (term.gate.c0 + term.gate.c2 * xr);
        Ok(())
    });
    (a, b)
}

fn folded_x_from_blocks(blocks: &HashMap<usize, Vec<u8>>, challenges: &[Fr]) -> Vec<Fr> {
    let width = INPUTS >> challenges.len();
    let mut x = vec![Fr::zero(); width];
    let low_weights = gkr::eq_weights(challenges);
    let low_mask = low_weights.len() - 1;
    for (&block, bytes) in blocks {
        assert_eq!(bytes.len(), BLOCK_BYTES);
        for offset in 0..BLOCK_BITS {
            let value = Fr::from(((bytes[offset >> 3] >> (offset & 7)) & 1) as u64);
            if value.is_zero() { continue; }
            let original = block * BLOCK_BITS + offset;
            x[original >> challenges.len()] += low_weights[offset & low_mask];
        }
    }
    x
}

fn folded_x_from_full(bytes: &[u8], challenges: &[Fr]) -> Vec<Fr> {
    let mut values: Vec<Fr> = (0..INPUTS).map(|i| packed_bit(bytes, i)).collect();
    for challenge in challenges { gkr::fold(&mut values, *challenge); }
    values
}

fn byte_runs(bytes: &BTreeSet<usize>) -> usize {
    let mut runs = 0;
    let mut previous = None;
    for &byte in bytes {
        if previous.map_or(true, |last: usize| byte != last + 1) { runs += 1; }
        previous = Some(byte);
    }
    runs
}

fn candidate_x_closure_bytes(a_after_challenge: &[Fr], round: usize) -> BTreeSet<usize> {
    let group_bits = 1usize << (round + 1);
    let mut bytes = BTreeSet::new();
    for (q, pair) in a_after_challenge.chunks_exact(2).enumerate() {
        if pair[0].is_zero() && pair[1].is_zero() { continue; }
        let start = q * group_bits;
        let first_byte = start >> 3;
        let last_byte = (start + group_bits - 1) >> 3;
        for byte in first_byte..=last_byte {
            bytes.insert(byte);
        }
    }
    bytes
}

fn direct_round(states: [&State; 2]) -> [Fr; 3] {
    let mut q = [Fr::zero(); 3];
    for state in states {
        let width = state.width();
        assert!(width >= 2 && width.is_power_of_two());
        for pair in 0..width / 2 {
            let i = 2 * pair;
            let da = state.a[i + 1] - state.a[i];
            let db = state.b[i + 1] - state.b[i];
            let dx = state.x[i + 1] - state.x[i];
            q[0] += state.a[i] * state.x[i] + state.b[i];
            q[1] += state.a[i] * dx + da * state.x[i] + db;
            q[2] += da * dx;
        }
    }
    q
}

fn initial_claim(states: [&State; 2]) -> Fr {
    states.into_iter().fold(Fr::zero(), |acc, state| {
        acc + (0..state.width()).fold(Fr::zero(), |sum, i| {
            sum + state.a[i] * state.x[i] + state.b[i]
        })
    })
}

fn fold_ab(state: &mut State, challenge: Fr) {
    gkr::fold(&mut state.a, challenge);
    gkr::fold(&mut state.b, challenge);
}

fn fold_oracle(state: &mut State, challenge: Fr) {
    gkr::fold(&mut state.a, challenge);
    gkr::fold(&mut state.b, challenge);
    gkr::fold(&mut state.x, challenge);
}

fn assert_exact_row(path: &Path) -> Result<(), String> {
    let file = File::open(path).map_err(|e| format!("open {}: {e}", path.display()))?;
    let len = file.metadata().map_err(|e| format!("stat fixture: {e}"))?.len();
    if len != ROW_BYTES as u64 { return Err(format!("packed row length {len} expected {ROW_BYTES}")); }
    Ok(())
}

fn assert_reader_rejects_bad_shapes(paths: &[PathBuf; 2], output: &Path) {
    let missing = output.join("missing-active-block-owner.bin");
    assert!(CandidateReader::open(&[missing, paths[1].clone()]).is_err(), "missing active owner row");

    let short = output.join("short-row-owner.bin");
    let bytes = fs::read(&paths[0]).expect("read fixture for isolated truncation");
    let mut file = OpenOptions::new().write(true).create_new(true).open(&short).unwrap();
    file.write_all(&bytes[..BLOCK_BYTES * 3 + BLOCK_BYTES / 2]).unwrap();
    drop(file);
    assert!(CandidateReader::open(&[short.clone(), paths[1].clone()]).is_err(), "truncated active block row");

    let trailing = output.join("trailing-row-owner.bin");
    let mut file = OpenOptions::new().write(true).create_new(true).open(&trailing).unwrap();
    file.write_all(&bytes).unwrap();
    file.write_all(&[0xA5]).unwrap();
    drop(file);
    assert!(assert_exact_row(&trailing).is_err(), "trailing byte rejected");
}

#[test]
fn adjacent_h21_role1_filebacked_cut16_matches_independent_dense_oracle() {
    assert_eq!(OWNERS[0] ^ 1, OWNERS[1]);
    let output = PathBuf::from(std::env::var_os("C266_OUTPUT_DIR")
        .expect("runner must supply unique absolute C266_OUTPUT_DIR outside source"));
    let paths = write_fixture(&output);
    assert_reader_rejects_bad_shapes(&paths, &output);

    // Oracle owns its handles and full-row buffers. CandidateReader below
    // separately opens the same now-closed immutable fixture.
    let mut oracle_rows = Vec::with_capacity(2);
    for path in &paths {
        assert_exact_row(path).expect("oracle exact fixture size");
        let mut file = File::open(path).expect("oracle independent open");
        let mut bytes = Vec::with_capacity(ROW_BYTES);
        file.read_to_end(&mut bytes).expect("oracle complete independent read");
        assert_eq!(bytes.len(), ROW_BYTES, "oracle rejects short/trailing rows");
        oracle_rows.push(bytes);
    }
    let oracle_rows: [Vec<u8>; 2] = oracle_rows.try_into().expect("two oracle rows");

    let plan = WorkTreeHistoryPlan::compile(HEADERS, SLOT_LOG, [0x35; 32], [0x35; 28])
        .expect("pinned H21 fixture plan");
    let roster = DaaHistoryRoster::compile(&plan).expect("H21 DAA roster");
    let row_point: Vec<_> = (0..19).map(|bit| Fr::from((3 * bit + 2) as u64)).collect();
    let row_weights = gkr::eq_weights(&row_point);
    let challenges: Vec<_> = (0..INPUT_BITS).map(|round| Fr::from((5 * round + 3) as u64)).collect();

    let (mut oracle, oracle_direct_claim) = dense_oracle(&roster, &oracle_rows, &row_weights);
    let oracle_initial_claim = initial_claim([&oracle[0], &oracle[1]]);
    assert_eq!(oracle_initial_claim, oracle_direct_claim,
        "independent source-gate claim equals dense oracle A/B reduction");
    assert!(!oracle_direct_claim.is_zero());

    let mut reader = CandidateReader::open(&paths).expect("candidate own file handles");
    let mut candidate_ab: [State; 2] = [State::zeros(INPUTS), State::zeros(INPUTS)];
    let mut claim = oracle_direct_claim;
    // Candidate State::zeros allocates A/B/X for each owner. The first X
    // replacement drops the unused initial X buffers after the first read.
    let mut tracked_candidate_vector_bytes_lower_bound = 2 * 3 * INPUTS * std::mem::size_of::<Fr>()
        + row_weights.capacity() * std::mem::size_of::<Fr>();

    for round in 0..CUT {
        let mut current_x: [Vec<Fr>; 2] = [Vec::new(), Vec::new()];
        for j in 0..2 {
            let blocks = reader.read_active_blocks(round, j).expect("candidate active support blocks");
            if round == 0 {
                // candidate_a_b allocates a second A/B pair before replacing
                // the zero pair held by candidate_ab.
                tracked_candidate_vector_bytes_lower_bound = tracked_candidate_vector_bytes_lower_bound.max(
                    2 * 4 * INPUTS * std::mem::size_of::<Fr>()
                        + row_weights.capacity() * std::mem::size_of::<Fr>()
                        + ACTIVE_BLOCKS.len() * BLOCK_BYTES);
                let (a, b) = candidate_a_b(&roster, j, &row_weights, &blocks);
                candidate_ab[j].a = a;
                candidate_ab[j].b = b;
            }
            current_x[j] = folded_x_from_blocks(&blocks, &challenges[..round]);
            let persistent = candidate_ab.iter().map(|state|
                (state.a.capacity() + state.b.capacity() + state.x.capacity())
                    * std::mem::size_of::<Fr>()).sum::<usize>();
            let live = persistent + current_x[j].capacity() * std::mem::size_of::<Fr>()
                + ACTIVE_BLOCKS.len() * BLOCK_BYTES;
            tracked_candidate_vector_bytes_lower_bound = tracked_candidate_vector_bytes_lower_bound.max(live);
            candidate_ab[j].x = std::mem::take(&mut current_x[j]);
        }
        for j in 0..2 {
            assert_eq!(candidate_ab[j].a, oracle[j].a, "candidate A before round {round}, owner {j}");
            assert_eq!(candidate_ab[j].b, oracle[j].b, "candidate B before round {round}, owner {j}");
            let support_len = candidate_ab[j].x.len();
            for i in 0..support_len {
                if !candidate_ab[j].a[i].is_zero() || !candidate_ab[j].b[i].is_zero() {
                    assert_eq!(candidate_ab[j].x[i], oracle[j].x[i],
                        "candidate active X before round {round}, owner {j}, index {i}");
                }
            }
        }
        if round == 0 {
            assert_eq!(initial_claim([&candidate_ab[0], &candidate_ab[1]]), claim,
                "candidate file-backed A/B reduction equals independent direct-gate claim");
        }
        let candidate_q = direct_round([&candidate_ab[0], &candidate_ab[1]]);
        let oracle_q = direct_round([&oracle[0], &oracle[1]]);
        assert_eq!(candidate_q, oracle_q, "candidate q0/q1/q2 round {round}");
        assert_eq!(candidate_q[0] + gkr::eval_polynomial(&candidate_q, Fr::one()), claim,
            "candidate sumcheck identity round {round}");
        assert_eq!(oracle_q[0] + gkr::eval_polynomial(&oracle_q, Fr::one()), claim,
            "dense oracle sumcheck identity round {round}");
        let challenge = challenges[round];
        let candidate_claim = gkr::eval_polynomial(&candidate_q, challenge);
        let oracle_claim = gkr::eval_polynomial(&oracle_q, challenge);
        assert_eq!(candidate_claim, oracle_claim, "postchallenge claim round {round}");
        claim = candidate_claim;
        for j in 0..2 {
            fold_ab(&mut candidate_ab[j], challenge);
            fold_oracle(&mut oracle[j], challenge);
            assert_eq!(candidate_ab[j].a, oracle[j].a, "A after round {round}, owner {j}");
            assert_eq!(candidate_ab[j].b, oracle[j].b, "B after round {round}, owner {j}");
        }
    }

    // The only full-row candidate reads occur after k15 has been challenged.
    for j in 0..2 {
        let full = reader.read_complete_row(j).expect("one complete row after cut round 15");
        let x16 = folded_x_from_full(&full, &challenges[..CUT]);
        tracked_candidate_vector_bytes_lower_bound = tracked_candidate_vector_bytes_lower_bound.max(
            2 * INPUTS * std::mem::size_of::<Fr>()
                + full.capacity() + x16.capacity() * std::mem::size_of::<Fr>());
        candidate_ab[j].x = x16;
        assert_eq!(candidate_ab[j].a.len(), CUT_WIDTH);
        assert_eq!(candidate_ab[j].a, oracle[j].a, "all A16, owner {j}");
        assert_eq!(candidate_ab[j].b, oracle[j].b, "all B16, owner {j}");
        assert_eq!(candidate_ab[j].x, oracle[j].x, "all X16 including inactive blocks, owner {j}");
        assert!(candidate_ab[j].x[CUT_WIDTH / 2..].iter().any(|v| !v.is_zero()),
            "exterior X16 entries participate, owner {j}");
    }
    assert_eq!(initial_claim([&candidate_ab[0], &candidate_ab[1]]), claim,
        "candidate cut-16 postchallenge claim");
    assert_eq!(initial_claim([&oracle[0], &oracle[1]]), claim,
        "oracle cut-16 postchallenge claim");

    // Mutating a bit outside the ten-block support is invisible to local rounds
    // but must alter candidate X16 after a separate full-row read.
    let mutation_path = output.join("owner-9214-exterior-mutant.bin");
    let mut mutated = oracle_rows[0].clone();
    let exterior_bit = 5 * BLOCK_BITS + 37;
    mutated[exterior_bit >> 3] ^= 1 << (exterior_bit & 7);
    let mut file = OpenOptions::new().write(true).create_new(true).open(&mutation_path).unwrap();
    file.write_all(&mutated).unwrap();
    drop(file);
    let mut mutant_reader = CandidateReader::open(&[mutation_path, paths[1].clone()])
        .expect("separate candidate reader for exterior mutant");
    let mutated_file_row = mutant_reader.read_complete_row(0).expect("mutant full-row read");
    let mutated_x16 = folded_x_from_full(&mutated_file_row, &challenges[..CUT]);
    assert_ne!(candidate_ab[0].x, mutated_x16,
        "candidate read of exterior mutation changes owner-9214 X16");
    assert_eq!(mutant_reader.trace.events.as_slice(), &[ReadEvent {
        round: CUT, owner: OWNERS[0], offset: 0, requested: ROW_BYTES, succeeded: true,
    }], "mutant reader has isolated one-row trace");

    let expected_calls = 2 * CUT * ACTIVE_BLOCKS.len() + 2;
    assert_eq!(reader.trace.events.len(), expected_calls, "candidate read call census");
    assert!(reader.trace.events.iter().all(|e| e.succeeded), "all main candidate reads succeed");
    assert_eq!(reader.trace.logical_bytes,
        2 * CUT * ACTIVE_BLOCKS.len() * BLOCK_BYTES + 2 * ROW_BYTES);
    assert_eq!(reader.trace.unique_offsets.len(), 2 * ROW_BYTES,
        "support reads plus one complete row cover each byte once");
    let mut expected_events = Vec::with_capacity(expected_calls);
    for round in 0..CUT {
        for owner_index in 0..2 {
            for block in ACTIVE_BLOCKS {
                expected_events.push(ReadEvent {
                    round,
                    owner: OWNERS[owner_index],
                    offset: (block * BLOCK_BYTES) as u64,
                    requested: BLOCK_BYTES,
                    succeeded: true,
                });
            }
        }
    }
    for owner in OWNERS {
        expected_events.push(ReadEvent {
            round: CUT, owner, offset: 0, requested: ROW_BYTES, succeeded: true,
        });
    }
    assert_eq!(reader.trace.events, expected_events,
        "exact candidate event order by round, owner, offset, length and outcome");
    let offsets: Vec<_> = reader.trace.events.iter()
        .map(|e| format!("{}:{}:{}:{}:{}", e.round, e.owner, e.offset, e.requested, e.succeeded as u8)).collect();
    let attempted = reader.trace.events.iter().filter(|e| !e.succeeded).count();
    println!("C268_FILEBACKED_CUT16_PASS owners=9214,9215 rounds=0..15 cut=16 terms_each={TERMS} omitted_worktree_each=78194 active_blocks={ACTIVE_BLOCKS:?} candidate_calls={} attempted_failures={attempted} logical_bytes={} unique_bytes={} tracked_candidate_vector_bytes_lower_bound={} tracked_excludes=trace,map,oracle,allocator_overhead offsets={:?} missing_short_trailing_rejected=true exterior_mutation_candidate_read=true full_proof=false all_h21_cost=false",
        reader.trace.events.len(), reader.trace.logical_bytes, reader.trace.unique_offsets.len(),
        tracked_candidate_vector_bytes_lower_bound, offsets);
}

#[test]
fn adjacent_h21_role1_candidate_x_byte_closure_census() {
    let mut first_byte = vec![Fr::zero(); 32];
    first_byte[0] = Fr::one();
    assert_eq!(candidate_x_closure_bytes(&first_byte, 0), BTreeSet::from([0]));
    let mut cross_byte = vec![Fr::zero(); 32];
    cross_byte[4] = Fr::one();
    assert_eq!(candidate_x_closure_bytes(&cross_byte, 1), BTreeSet::from([1]));
    let mut last_pair = vec![Fr::zero(); 32];
    last_pair[30] = Fr::one();
    let last_group = candidate_x_closure_bytes(&last_pair, 15);
    assert_eq!(last_group.len(), ROW_BYTES / 16);
    assert_eq!(last_group.first(), Some(&(ROW_BYTES - ROW_BYTES / 16)));
    assert_eq!(last_group.last(), Some(&(ROW_BYTES - 1)));

    let plan = WorkTreeHistoryPlan::compile(HEADERS, SLOT_LOG, [0x35; 32], [0x35; 28])
        .expect("pinned H21 fixture plan");
    let roster = DaaHistoryRoster::compile(&plan).expect("H21 DAA roster");
    let row_point: Vec<_> = (0..19).map(|bit| Fr::from((3 * bit + 2) as u64)).collect();
    let row_weights = gkr::eq_weights(&row_point);
    let challenges: Vec<_> = (0..INPUT_BITS).map(|round| Fr::from((5 * round + 3) as u64)).collect();
    let rows = [packed_bytes(OWNERS[0]), packed_bytes(OWNERS[1])];
    let mut initial_right_bytes = 0usize;
    let mut total_closure_bytes = 0usize;
    let mut total_closure_runs = 0usize;

    for owner_index in 0..2 {
        let mut a = vec![Fr::zero(); INPUTS];
        let mut right_support = BTreeSet::new();
        visit_owner(&roster, OWNERS[owner_index], |term, row, left, right| {
            let weight = row_weights[row];
            let xr = packed_bit(&rows[owner_index], right);
            a[left] += weight * (term.gate.c1 + term.gate.c3 * xr);
            right_support.insert(right >> 3);
            Ok(())
        });
        initial_right_bytes += right_support.len();
        println!("C273_INITIAL_RIGHT_X owner={} bytes={} runs={} ten_block_bytes={}",
            OWNERS[owner_index], right_support.len(), byte_runs(&right_support),
            ACTIVE_BLOCKS.len() * BLOCK_BYTES);

        for (round, challenge) in challenges.iter().take(CUT).enumerate() {
            let support = candidate_x_closure_bytes(&a, round);
            let runs = byte_runs(&support);
            total_closure_bytes += support.len();
            total_closure_runs += runs;
            println!("C273_X_CLOSURE owner={} round={} bytes={} runs={} ten_block_bytes={}",
                OWNERS[owner_index], round, support.len(), runs,
                ACTIVE_BLOCKS.len() * BLOCK_BYTES);
            gkr::fold(&mut a, *challenge);
        }
    }

    println!("C274_BYTE_CLOSURE_CENSUS_PASS owners=9214,9215 rounds=0..15 initial_right_x_bytes={initial_right_bytes} closure_bytes={total_closure_bytes} closure_runs={total_closure_runs} ten_block_bytes_per_owner_round={} witness_specific=true os_io=false all_owner_lower_bound=false",
        ACTIVE_BLOCKS.len() * BLOCK_BYTES);
}

#[test]
fn h21_role1_carry_candidate_source_term_cost_diagnostic() {
    use std::time::Instant;

    const REPS: usize = 3;
    const OWNER: usize = 9_214;

    // Compile and census are deliberately outside the timed candidate spans.
    let plan = WorkTreeHistoryPlan::compile(HEADERS, SLOT_LOG, [0x35; 32], [0x35; 28])
        .expect("pinned H21 fixture plan");
    let roster = DaaHistoryRoster::compile(&plan).expect("H21 DAA roster");
    assert_eq!(plan.headers(), HEADERS);
    assert_eq!(plan.slot_log(), SLOT_LOG);
    assert_eq!(roster.owner_class(OWNER as u64).expect("sample class"), OwnerClass::Carry);

    // Count every exact owner class once, outside timing, so the projection
    // does not infer Carry prevalence from a sample or a rounded ratio.
    let slots = 1usize.checked_shl(SLOT_LOG as u32).expect("H21 slots");
    let mut class_counts = [0usize; 15];
    for owner in 0..slots {
        let class = roster.owner_class(owner as u64).expect("H21 owner class");
        let index = match class {
            OwnerClass::Genesis => 0,
            OwnerClass::Initial => 1,
            OwnerClass::Carry => 2,
            OwnerClass::FixedV2 => 3,
            OwnerClass::Singleton => 4,
            OwnerClass::M1 => 5,
            OwnerClass::Short(profile) => 4 + profile.count(),
            OwnerClass::Mature(crate::daa_integer::Epoch::Legacy) => 12,
            OwnerClass::Mature(crate::daa_integer::Epoch::Eip) => 13,
            OwnerClass::Padding => 14,
        };
        class_counts[index] = class_counts[index].checked_add(1).expect("class census overflow");
    }
    assert_eq!(class_counts.iter().sum::<usize>(), slots);
    let carry_owners = class_counts[2];
    assert!(carry_owners > 0);

    // Deterministic callback inputs are materialized before timing. The X row
    // is packed Boolean data; row equality weights are also prepared up front.
    let row_point: Vec<_> = (0..19).map(|bit| Fr::from((3 * bit + 2) as u64)).collect();
    let row_weights = gkr::eq_weights(&row_point);
    assert_eq!(row_weights.len(), ROWS);
    let packed_x = packed_bytes(OWNER);
    assert_eq!(packed_x.len(), ROW_BYTES);

    let mut elapsed_ns = Vec::with_capacity(REPS);
    let mut emitted_terms = Vec::with_capacity(REPS);
    let mut vector_capacity_bytes_lower_bound = 0usize;
    let mut checksum = Fr::zero();
    for _rep in 0..REPS {
        let start = Instant::now();
        let mut a = vec![Fr::zero(); INPUTS];
        let mut b = vec![Fr::zero(); INPUTS];
        let mut callbacks = 0usize;
        let owner_row_base = OWNER.checked_mul(ROWS).expect("owner row base");
        let owner_input_base = OWNER.checked_mul(INPUTS).expect("owner input base");
        let counts = roster.visit_header_terms(OWNER as u64, |term| {
            let row = term.row.checked_sub(owner_row_base).ok_or("row before owner")?;
            let left = term.gate.left.checked_sub(owner_input_base).ok_or("left before owner")?;
            let right = term.gate.right.checked_sub(owner_input_base).ok_or("right before owner")?;
            if row >= ROWS || left >= INPUTS || right >= INPUTS {
                return Err("role-1 Carry callback escaped physical owner".into());
            }
            let weight = row_weights[row];
            let xr = packed_bit(&packed_x, right);
            a[left] += weight * (term.gate.c1 + term.gate.c3 * xr);
            b[left] += weight * (term.gate.c0 + term.gate.c2 * xr);
            callbacks = callbacks.checked_add(1).ok_or("callback count overflow")?;
            Ok(())
        }).expect("candidate Carry header callbacks");
        let wall = start.elapsed();

        assert_eq!(counts.emitted, callbacks);
        assert_eq!(callbacks, TERMS);
        assert_eq!(counts.omitted_worktree, 78_194);
        assert_eq!(counts.omitted_mature_a4, 0);
        assert_eq!(counts.omitted_short_a4, 0);
        elapsed_ns.push(wall.as_nanos());
        emitted_terms.push(callbacks);

        vector_capacity_bytes_lower_bound = a.capacity()
            .checked_add(b.capacity()).expect("A/B capacity sum")
            .checked_mul(std::mem::size_of::<Fr>()).expect("A/B capacity bytes")
            .checked_add(packed_x.capacity()).expect("candidate vectors including packed X");
        checksum = std::hint::black_box(
            a[0] + a[INPUTS / 2] + a[INPUTS - 1]
                + b[0] + b[INPUTS / 2] + b[INPUTS - 1],
        );
        std::hint::black_box((&a, &b));
    }

    let total_ns: u128 = elapsed_ns.iter().copied().sum();
    let mean_owner_ns = total_ns / REPS as u128;
    let projected_carry_terms = (carry_owners as u128)
        .checked_mul(TERMS as u128).expect("Carry projected term count");
    let projected_carry_ns_mean = (carry_owners as u128)
        .checked_mul(mean_owner_ns).expect("Carry projected duration");
    let class_counts_text = format!(
        "genesis:{},initial:{},carry:{},fixed_v2:{},singleton:{},m1:{},short_m2:{},short_m3:{},short_m4:{},short_m5:{},short_m6:{},short_m7:{},mature_legacy:{},mature_eip:{},padding:{}",
        class_counts[0], class_counts[1], class_counts[2], class_counts[3],
        class_counts[4], class_counts[5], class_counts[6], class_counts[7],
        class_counts[8], class_counts[9], class_counts[10], class_counts[11],
        class_counts[12], class_counts[13], class_counts[14],
    );
    println!(
        "C278_H21_CARRY_COST full_proof=false carry_only=true headers={HEADERS} slot_log={SLOT_LOG} slots={slots} owner={OWNER} class_counts={class_counts_text} carry_owners={carry_owners} reps={REPS} emitted_terms_each={emitted_terms:?} wall_ns_each={elapsed_ns:?} mean_owner_ns={mean_owner_ns} projected_carry_terms={projected_carry_terms} projected_carry_ns_mean={projected_carry_ns_mean} candidate_vector_capacity_bytes_lower_bound={} capacity_includes=A,B,packed_X excludes=row_weights,roster,plan,allocator_overhead checksum_nonzero={} projected_from=one_Carry_owner_repeated_measurement nonclaims=all_owner_proof,full_producer_cost,proof_cost",
        vector_capacity_bytes_lower_bound, !checksum.is_zero(),
    );
}

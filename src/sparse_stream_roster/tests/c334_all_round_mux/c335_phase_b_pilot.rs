//! One paired cost pilot over the C334-qualified MUX slice. This is deliberately
//! not a timing admission or a substitute for the later repeated-pair lot.
use super::*;
use rayon::prelude::*;
use std::time::{Duration, Instant};

#[derive(Clone, Copy, Debug, Default)]
struct Counts {
    packed_bytes_read: usize,
    byte_shifts: usize,
    byte_masks: usize,
    u64_loads: usize,
    u64_shifts: usize,
    u64_permute_stages: usize,
    u64_masks: usize,
    packed_word_ops: usize,
    original_right_reads: usize,
    field_fold_reads: usize,
    field_fold_writes: usize,
    fr_adds: usize,
    fr_muls: usize,
    fr_negs: usize,
    table_entries_built: usize,
    // Coefficient, row, prefix, owner, mask and right-cache tables. Folded-X
    // vector reads are reported separately as field_fold_reads.
    table_lookups: usize,
    shared_source_visits: usize,
    owner_source_visits: usize,
    grouped_key_visits: usize,
}

impl Counts {
    fn absorb(&mut self, rhs: &Self) {
        self.packed_bytes_read += rhs.packed_bytes_read;
        self.byte_shifts += rhs.byte_shifts;
        self.byte_masks += rhs.byte_masks;
        self.u64_loads += rhs.u64_loads;
        self.u64_shifts += rhs.u64_shifts;
        self.u64_permute_stages += rhs.u64_permute_stages;
        self.u64_masks += rhs.u64_masks;
        self.packed_word_ops += rhs.packed_word_ops;
        self.original_right_reads += rhs.original_right_reads;
        self.field_fold_reads += rhs.field_fold_reads;
        self.field_fold_writes += rhs.field_fold_writes;
        self.fr_adds += rhs.fr_adds;
        self.fr_muls += rhs.fr_muls;
        self.fr_negs += rhs.fr_negs;
        self.table_entries_built += rhs.table_entries_built;
        self.table_lookups += rhs.table_lookups;
        self.shared_source_visits += rhs.shared_source_visits;
        self.owner_source_visits += rhs.owner_source_visits;
        self.grouped_key_visits += rhs.grouped_key_visits;
    }
}

#[derive(Debug, Default)]
struct Stage {
    block_prep: Duration,
    x_read_fold: Duration,
    block_message: Duration,
    transcript_sumcheck: Duration,
    terminal: Duration,
    counts: Counts,
    peak_known_live_bytes: usize,
    groups: usize,
}

impl Stage {
    fn absorb(&mut self, rhs: &Self) {
        self.block_prep += rhs.block_prep;
        self.x_read_fold += rhs.x_read_fold;
        self.block_message += rhs.block_message;
        self.transcript_sumcheck += rhs.transcript_sumcheck;
        self.terminal += rhs.terminal;
        self.counts.absorb(&rhs.counts);
        self.peak_known_live_bytes = self.peak_known_live_bytes.max(rhs.peak_known_live_bytes);
    }
    fn inclusive(&self) -> Duration {
        self.block_prep + self.x_read_fold + self.block_message
            + self.transcript_sumcheck + self.terminal
    }
    fn marginal_block(&self) -> Duration {
        self.block_prep + self.block_message + self.terminal
    }
}

/// The same byte-table plus in-place field fold is charged independently to
/// each arm. Its table has at most 256 entries, even at prefix length 20.
struct PilotFoldPlan {
    prefix: Vec<Fr>,
    pattern: Vec<Fr>,
    bits_per_pattern: usize,
}

impl PilotFoldPlan {
    fn new(prefix: &[Fr], counts: &mut Counts) -> Self {
        assert!(prefix.len() <= 20);
        let low = prefix.len().min(3);
        if low == 0 {
            return Self { prefix: Vec::new(), pattern: Vec::new(), bits_per_pattern: 0 };
        }
        let weights = boolean_u_eq_weights(&prefix[..low]).unwrap();
        counts.fr_adds += (1usize << low) - 1;
        counts.fr_muls += 2 * ((1usize << low) - 1);
        counts.table_entries_built += weights.len();
        counts.table_lookups += (1usize << low) - 1;
        let bits_per_pattern = 1usize << low;
        let size = 1usize << bits_per_pattern;
        let mut pattern = vec![Fr::zero(); size];
        for mask in 1..size {
            let low_bit = mask.trailing_zeros() as usize;
            pattern[mask] = pattern[mask & (mask - 1)] + weights[low_bit];
        }
        counts.fr_adds += size - 1;
        counts.table_entries_built += size;
        counts.table_lookups += 2 * (size - 1);
        Self { prefix: prefix.to_vec(), pattern, bits_per_pattern }
    }

    fn project(&self, packet: &[u8], counts: &mut Counts) -> Vec<Fr> {
        assert_eq!(packet.len(), WIDTH / 8);
        counts.packed_bytes_read += packet.len();
        if self.prefix.is_empty() {
            let mut out = Vec::with_capacity(WIDTH);
            for &byte in packet {
                for lane in 0..8 {
                    out.push(Fr::from(((byte >> lane) & 1) as u64));
                }
            }
            counts.byte_shifts += WIDTH;
            counts.byte_masks += WIDTH;
            counts.field_fold_writes += WIDTH;
            return out;
        }
        let lanes_per_byte = 8 / self.bits_per_pattern;
        let lane_mask = (1usize << self.bits_per_pattern) - 1;
        let mut out = Vec::with_capacity(packet.len() * lanes_per_byte);
        for &byte in packet {
            for lane in 0..lanes_per_byte {
                let pattern = ((byte as usize >> (lane * self.bits_per_pattern)) & lane_mask) as usize;
                out.push(self.pattern[pattern]);
            }
        }
        counts.byte_shifts += out.len();
        counts.byte_masks += out.len();
        counts.table_lookups += out.len();
        counts.field_fold_writes += out.len();
        for &challenge in self.prefix.iter().skip(3) {
            let next = out.len() / 2;
            for index in 0..next {
                let low = out[2 * index];
                let high = out[2 * index + 1];
                out[index] = low + challenge * (high - low);
            }
            out.truncate(next);
            counts.field_fold_reads += 2 * next;
            counts.field_fold_writes += next;
            counts.fr_adds += 2 * next;
            counts.fr_muls += next;
        }
        assert_eq!(out.len(), WIDTH >> self.prefix.len());
        out
    }

    fn live_bytes(&self) -> usize {
        (self.prefix.capacity() + self.pattern.capacity()) * std::mem::size_of::<Fr>()
    }
}

/// C316-style generic grouping, restricted to the exact C334 canonical slice.
/// Source tuples are visited once per prefix, never inside an owner loop.
fn canonical_groups(terms: &[Term], prefix: &[Fr], local: &[Fr], counts: &mut Counts) -> Vec<Group> {
    assert_eq!(terms.len(), 192);
    let p = prefix.len();
    let weights = boolean_u_eq_weights(prefix).unwrap();
    let mask = weights.len() - 1;
    let mut map = BTreeMap::<Key, (Fr, Fr)>::new();
    for term in terms {
        let gate = &term.gate;
        assert!(gate.c0.is_zero() && gate.c2.is_zero());
        let key = Key { right: gate.right, s: (gate.left >> p) & 1,
            h: gate.left >> (p + 1) };
        let weight = local[term.row] * weights[gate.left & mask];
        let entry = map.entry(key).or_insert((Fr::zero(), Fr::zero()));
        entry.0 += weight * gate.c1;
        entry.1 += weight * gate.c3;
    }
    charge_group_prep(p, counts);
    map.into_iter().map(|(key, (c1, c3))| Group { key, c1, c3 }).collect()
}

fn charge_group_prep(p: usize, counts: &mut Counts) {
    // boolean_u_eq_weights plus the two coefficient sums in either grouped
    // constructor. Each tuple reads its row and prefix weights and performs
    // one BTreeMap lookup. Weight construction reads its previous table.
    counts.fr_adds += ((1usize << p) - 1) + 2 * 192;
    counts.fr_muls += 2 * ((1usize << p) - 1) + 3 * 192;
    counts.u64_shifts += 2 * 192;
    counts.u64_masks += 2 * 192;
    counts.table_entries_built += 1usize << p;
    counts.table_lookups += 3 * 192 + ((1usize << p) - 1);
    counts.shared_source_visits += 192;
}

fn grouped_alpha(group: &Group, packet: &[u8], right_cache: &mut BTreeMap<usize, Fr>,
    counts: &mut Counts) -> Fr {
    if group.c3.is_zero() { return group.c1; }
    counts.table_lookups += 1;
    let z = match right_cache.get(&group.key.right) {
        Some(value) => *value,
        None => {
            let value = Fr::from(u64::from(bit(packet, group.key.right)));
            right_cache.insert(group.key.right, value);
            counts.table_entries_built += 1;
            counts.packed_bytes_read += 1;
            counts.byte_shifts += 1;
            counts.byte_masks += 1;
            counts.original_right_reads += 1;
            value
        }
    };
    counts.fr_adds += 1;
    counts.fr_muls += 1;
    group.c1 + group.c3 * z
}

fn grouped_message(groups: &[Group], packet: &[u8], folded_x: &[Fr], rho: Fr,
    counts: &mut Counts) -> [Fr; 3] {
    let mut out = [Fr::zero(); 3];
    let mut right_cache = BTreeMap::<usize, Fr>::new();
    for group in groups {
        let key = group.key;
        let alpha = grouped_alpha(group, packet, &mut right_cache, counts);
        let x0 = folded_x[2 * key.h];
        let x1 = folded_x[2 * key.h + 1];
        add_one(&mut out, alpha, key.s, x0, x1);
        counts.field_fold_reads += 2;
        counts.fr_adds += if key.s == 0 { 5 } else { 3 };
        counts.fr_muls += if key.s == 0 { 3 } else { 2 };
        counts.grouped_key_visits += 1;
    }
    counts.fr_muls += 3;
    out.map(|value| rho * value)
}

fn packed_message(packet: &[u8], prefix: &[Fr], rho: Fr, lut: &MaskLut,
    counts: &mut Counts) -> [Fr; 3] {
    let mut work = KernelWork::default();
    let message = packed_owner_message(packet, prefix, rho, lut, Fault::None, &mut work);
    assert_eq!(work.aligned_loads, 7);
    assert_eq!(work.word_ops, 543);
    assert_eq!(work.masks, 96);
    counts.packed_bytes_read += 8 * work.aligned_loads;
    counts.u64_loads += work.aligned_loads;
    // Counts from the fixed C226 transpose source: 3 banks x 4 lanes x 3
    // butterfly stages, plus its window, mask and extraction shifts.
    counts.u64_shifts += 229;
    counts.u64_permute_stages += 36;
    counts.u64_masks += 163;
    counts.packed_word_ops += work.word_ops;
    counts.original_right_reads += 1; // original selector at 535974
    counts.fr_negs += 1; // the move bank uses -z
    counts.table_entries_built += 96; // PackedMasks::mask[3][4][8]
    counts.table_lookups += 2 * work.lut_reads; // packed mask and MaskLut reads
    assert_eq!(work.bank_bit_steps, 24);
    if prefix.is_empty() {
        assert_eq!(work.lut_reads, 48);
        counts.fr_adds += 97;
        counts.fr_muls += 111;
    } else {
        assert_eq!(prefix.len(), 1);
        assert_eq!(work.lut_reads, 96);
        counts.fr_adds += 205;
        counts.fr_muls += 159;
    }
    message
}

#[derive(Clone, Copy)]
enum Arm { Generic, Candidate }
impl Arm { fn name(self) -> &'static str { match self { Self::Generic => "generic", Self::Candidate => "candidate" } } }

#[derive(Clone, Debug, PartialEq, Eq)]
struct Round {
    owners: [[Fr; 3]; 4],
    aggregate: [Fr; 3],
    challenge: Fr,
    claim: Fr,
    continuation: Fr,
}

struct Run {
    rounds: Vec<Round>,
    prefixes: Vec<Fr>,
    terminal: [[Fr; 3]; 4],
    final_claim: Fr,
    final_continuation: Fr,
    stages: Vec<Stage>,
    wall: Duration,
}

fn factor_live_bytes(factor: &OneFamilyRowFactor<'_>) -> usize {
    factor.local_weights.len() * std::mem::size_of::<Fr>()
        + factor.copy_weights.capacity_bytes().unwrap()
}

fn known_live_bytes(terms: &[Term], packets: &[Vec<u8>; 4], factor: &OneFamilyRowFactor<'_>,
    group_capacity: usize, plan: &PilotFoldPlan, folded_capacity: usize,
    has_lut: bool) -> usize {
    packets.iter().map(Vec::capacity).sum::<usize>()
        + terms.len() * std::mem::size_of::<Term>()
        + factor_live_bytes(factor)
        + group_capacity * std::mem::size_of::<Group>()
        + plan.live_bytes() + folded_capacity * std::mem::size_of::<Fr>()
        + if has_lut { std::mem::size_of::<MaskLut>() } else { 0 }
}

fn known_group_prep_bytes(terms: &[Term], packets: &[Vec<u8>; 4], factor: &OneFamilyRowFactor<'_>,
    p: usize, group_count: usize, has_lut: bool) -> usize {
    // At the end of grouping, prefix weights and all actual map payloads are
    // live together. The collected group Vec is counted separately after
    // grouping; map node links and allocator overhead are omitted here.
    packets.iter().map(Vec::capacity).sum::<usize>()
        + terms.len() * std::mem::size_of::<Term>()
        + factor_live_bytes(factor)
        + ((1usize << p) * std::mem::size_of::<Fr>())
        + group_count * (std::mem::size_of::<Key>() + 2 * std::mem::size_of::<Fr>())
        + if has_lut { std::mem::size_of::<MaskLut>() } else { 0 }
}

fn terminal_owner(groups: &[Group], packet: &[u8], folded_x: &[Fr], rho: Fr,
    counts: &mut Counts) -> [Fr; 3] {
    assert_eq!(folded_x.len(), 1);
    let mut a = Fr::zero();
    let b = Fr::zero(); // C334 qualification checked c0=c2=0 for all 192 terms.
    let mut right_cache = BTreeMap::<usize, Fr>::new();
    for group in groups {
        assert_eq!((group.key.s, group.key.h), (0, 0));
        a += grouped_alpha(group, packet, &mut right_cache, counts);
        counts.grouped_key_visits += 1;
        counts.fr_adds += 1;
    }
    counts.field_fold_reads += 1;
    counts.fr_muls += 1;
    [rho * a, b, folded_x[0]]
}

fn run_arm(arm: Arm, terms: &[Term], packets: &[Vec<u8>; 4],
    factor: &OneFamilyRowFactor<'_>, seed: Transcript, initial: Fr) -> Run {
    let arm_started = Instant::now();
    let mut transcript = seed;
    let mut claim = initial;
    let mut proof_rounds = Vec::with_capacity(20);
    let mut prefix = Vec::with_capacity(20);
    let mut rounds = Vec::with_capacity(20);
    let mut stages = Vec::with_capacity(21);
    let mut lut = None;
    for p in 0..20 {
        let mut stage = Stage::default();
        if p == 0 && matches!(arm, Arm::Candidate) {
            let start = Instant::now();
            lut = Some(MaskLut::new(&factor.local_weights));
            stage.block_prep += start.elapsed();
            stage.counts.table_entries_built += 256;
            stage.counts.fr_adds += 255;
            stage.counts.table_lookups += 511; // 255 subset reads x2 and row0
        }
        let start = Instant::now();
        let grouped = match arm {
            Arm::Generic => canonical_groups(terms, &prefix, &factor.local_weights, &mut stage.counts),
            Arm::Candidate if p <= 1 => Vec::new(),
            Arm::Candidate => {
                let result = groups(&prefix, &factor.local_weights);
                charge_group_prep(p, &mut stage.counts);
                stage.counts.fr_negs += 128; // two negative roles x 64 bits
                stage.counts.u64_shifts += 192; // expected() coefficient shifts
                result
            }
        };
        stage.block_prep += start.elapsed();
        stage.groups = grouped.len();
        if matches!(arm, Arm::Generic) || p >= 2 {
            stage.counts.table_entries_built += grouped.len();
            stage.peak_known_live_bytes = known_group_prep_bytes(terms, packets,
                factor, p, grouped.len(), lut.is_some());
        }
        let start = Instant::now();
        let plan = PilotFoldPlan::new(&prefix, &mut stage.counts);
        stage.x_read_fold += start.elapsed();
        let mut owner_messages = [[Fr::zero(); 3]; 4];
        let mut aggregate = [Fr::zero(); 3];
        for (owner_index, (&owner, packet)) in OWNERS.iter().zip(packets).enumerate() {
            let start = Instant::now();
            let folded_x = plan.project(packet, &mut stage.counts);
            stage.x_read_fold += start.elapsed();
            stage.peak_known_live_bytes = stage.peak_known_live_bytes.max(known_live_bytes(
                terms, packets, factor, grouped.capacity(), &plan,
                folded_x.capacity(), lut.is_some()));
            let start = Instant::now();
            let rho = factor.copy(owner);
            stage.counts.table_lookups += 3;
            stage.counts.fr_muls += 3;
            stage.counts.u64_shifts += 3;
            stage.counts.u64_masks += 3;
            let part = match arm {
                Arm::Candidate if p <= 1 => packed_message(packet, &prefix,
                    rho, lut.as_ref().unwrap(), &mut stage.counts),
                _ => grouped_message(&grouped, packet, &folded_x,
                    rho, &mut stage.counts),
            };
            owner_messages[owner_index] = part;
            add(&mut aggregate, part);
            stage.counts.fr_adds += 3;
            stage.block_message += start.elapsed();
        }
        let start = Instant::now();
        let challenge = send_round(aggregate.to_vec(), &mut claim,
            &mut proof_rounds, &mut transcript).unwrap();
        // send_round checks P(0)+P(1), then evaluates P(challenge): two
        // three-coefficient Horner passes and the identity addition.
        stage.counts.fr_adds += 7;
        stage.counts.fr_muls += 6;
        let mut continuation = transcript.clone();
        let continuation = continuation.challenge_scalar(b"c335-pilot-continuation");
        stage.transcript_sumcheck += start.elapsed();
        rounds.push(Round { owners: owner_messages, aggregate, challenge, claim, continuation });
        prefix.push(challenge);
        stages.push(stage);
    }
    let mut stage = Stage::default();
    let start = Instant::now();
    let terminal_groups = match arm {
        Arm::Generic => canonical_groups(terms, &prefix, &factor.local_weights, &mut stage.counts),
        Arm::Candidate => {
            let result = groups(&prefix, &factor.local_weights);
            charge_group_prep(20, &mut stage.counts);
            stage.counts.fr_negs += 128;
            stage.counts.u64_shifts += 192;
            result
        }
    };
    stage.block_prep += start.elapsed();
    stage.groups = terminal_groups.len();
    stage.counts.table_entries_built += terminal_groups.len();
    stage.peak_known_live_bytes = known_group_prep_bytes(terms, packets,
        factor, 20, terminal_groups.len(), lut.is_some());
    assert_eq!(terminal_groups.len(), 2);
    let start = Instant::now();
    let plan = PilotFoldPlan::new(&prefix, &mut stage.counts);
    stage.x_read_fold += start.elapsed();
    let mut terminal = [[Fr::zero(); 3]; 4];
    let mut handoff_claim = Fr::zero();
    for (index, (&owner, packet)) in OWNERS.iter().zip(packets).enumerate() {
        let start = Instant::now();
        let folded_x = plan.project(packet, &mut stage.counts);
        stage.x_read_fold += start.elapsed();
        stage.peak_known_live_bytes = stage.peak_known_live_bytes.max(known_live_bytes(
            terms, packets, factor, terminal_groups.capacity(), &plan,
            folded_x.capacity(), lut.is_some()));
        let start = Instant::now();
        let rho = factor.copy(owner);
        stage.counts.table_lookups += 3;
        stage.counts.fr_muls += 3;
        stage.counts.u64_shifts += 3;
        stage.counts.u64_masks += 3;
        let triple = terminal_owner(&terminal_groups, packet, &folded_x,
            rho, &mut stage.counts);
        terminal[index] = triple;
        handoff_claim += triple[0] * triple[2] + triple[1];
        stage.counts.fr_muls += 1;
        stage.counts.fr_adds += 2;
        stage.terminal += start.elapsed();
    }
    assert_eq!(handoff_claim, claim, "p20 sumcheck handoff identity");
    let mut continuation = transcript.clone();
    let final_continuation = continuation.challenge_scalar(b"c335-pilot-final-continuation");
    stages.push(stage);
    Run { rounds, prefixes: prefix, terminal, final_claim: claim, final_continuation,
        stages, wall: arm_started.elapsed() }
}

fn print_run(arm: Arm, run: &Run) -> Duration {
    let mut total = Stage::default();
    for (p, stage) in run.stages.iter().enumerate() {
        total.absorb(stage);
        println!("C335_PILOT_PREFIX arm={} p={} groups={} block_prep_ns={} x_read_fold_ns={} block_message_ns={} transcript_sumcheck_ns={} terminal_ns={} marginal_block_ns={} inclusive_ns={} peak_known_live_bytes={} counts={:?}",
            arm.name(), p, stage.groups, stage.block_prep.as_nanos(),
            stage.x_read_fold.as_nanos(), stage.block_message.as_nanos(),
            stage.transcript_sumcheck.as_nanos(), stage.terminal.as_nanos(),
            stage.marginal_block().as_nanos(), stage.inclusive().as_nanos(),
            stage.peak_known_live_bytes, stage.counts);
    }
    println!("C335_PILOT_TOTAL arm={} prefixes=20 owners=4 block_prep_ns={} x_read_fold_ns={} block_message_ns={} transcript_sumcheck_ns={} p20_terminal_ns={} marginal_block_ns={} stage_sum_ns={} whole_arm_wall_ns={} unattributed_ns={} peak_known_live_lower_bound_bytes={} counts={:?}",
        arm.name(), total.block_prep.as_nanos(), total.x_read_fold.as_nanos(),
        total.block_message.as_nanos(), total.transcript_sumcheck.as_nanos(),
        total.terminal.as_nanos(), total.marginal_block().as_nanos(),
        total.inclusive().as_nanos(), run.wall.as_nanos(),
        run.wall.saturating_sub(total.inclusive()).as_nanos(),
        total.peak_known_live_bytes, total.counts);
    run.wall
}

#[test]
#[ignore = "C335 one-pair cost pilot; run only inside separately bounded Phase B Test Job"]
fn c335_phase_b_pilot_pair() {
    let qualification_start = Instant::now();
    let slice = qualify();
    let parent = WorkTreeHistoryPlan::compile(1_827_840, 21, [0; 32], [0; 28]).unwrap();
    let roster = DaaHistoryRoster::compile(&parent).unwrap();
    let scheduled = Scheduled::eligible08();
    for owner in OWNERS { check_retirement(&roster, &scheduled, owner); }
    let placement = RowPlan::new(&roster, &scheduled).unwrap();
    let owner_terms: [Vec<Term>; 4] = OWNERS.map(|owner| owner_slice(&placement, owner, &slice));
    let packets = OWNERS.map(packet);
    let digest = packet_digest(&packets);
    let row_point: Vec<Fr> = (0..40).map(|i| Fr::from((7 + 3 * i) as u64)).collect();
    let factor = OneFamilyRowFactor::try_new(&row_point, 21, 19, 0, &[19], None).unwrap();
    assert!(OWNERS.iter().all(|&owner| !factor.copy(owner).is_zero()));
    let initial = initial_claim(&owner_terms, &packets, &factor);
    let seed = transcript(&row_point, &digest, initial);
    drop(owner_terms);
    drop(placement);
    drop(scheduled);
    drop(roster);
    drop(parent);

    let qualification = qualification_start.elapsed();
    let baseline = run_arm(Arm::Generic, &slice.attached, &packets,
        &factor, seed.clone(), initial);
    let candidate = run_arm(Arm::Candidate, &slice.attached, &packets,
        &factor, seed, initial);
    assert_eq!(baseline.rounds, candidate.rounds,
        "all owner/aggregate messages, online challenges, claims and continuations");
    assert_eq!(baseline.prefixes, candidate.prefixes);
    assert_eq!(baseline.terminal, candidate.terminal, "p20 terminal owner triples");
    assert_eq!(baseline.final_claim, candidate.final_claim);
    assert_eq!(baseline.final_continuation, candidate.final_continuation);
    for (p, round) in baseline.rounds.iter().enumerate() {
        assert!(!round.challenge.is_zero() && !round.challenge.is_one(),
            "non-Boolean online challenge at prefix {p}");
    }
    // The two timed arms derive challenges online and independently. Check
    // their common byte fold against the established EdgePrefixPlan only after
    // both arms finish; a shared fold error must fail before the PASS marker.
    let fold_check_start = Instant::now();
    for p in 0..=20 {
        let prefix = &baseline.prefixes[..p];
        let plan = PilotFoldPlan::new(prefix, &mut Counts::default());
        for (&owner, packet) in OWNERS.iter().zip(&packets) {
            let actual = plan.project(packet, &mut Counts::default());
            let expected = if p == 0 { expand(packet) }
                else { EdgePrefixPlan::new(WIDTH, prefix).unwrap().project_bits(packet).unwrap() };
            assert_eq!(actual, expected, "fold plan vs EdgePrefixPlan owner={owner} prefix={p}");
        }
    }
    let fold_check = fold_check_start.elapsed();
    println!("C335_PILOT_QUALIFICATION source_ns={} fold_differential_ns={} source_tuples=192 packets=4 packet_bytes_each={} fold_differentials=84 x_digest={}",
        qualification.as_nanos(), fold_check.as_nanos(), WIDTH / 8,
        digest.iter().map(|byte| format!("{byte:02x}")).collect::<String>());
    let generic_sample = print_run(Arm::Generic, &baseline);
    let candidate_sample = print_run(Arm::Candidate, &candidate);
    assert!(generic_sample > Duration::from_millis(100)
        && candidate_sample > Duration::from_millis(100),
        "both paired whole-arm timing samples must exceed 100 ms");
    println!("C335_PHASE_B_PILOT_PASS cost_estimate_only=true pairs=1 confidence_interval=not_computed admission=not_evaluated cold_io=not_established path_memory=known_live_lower_bound_only");
}

/// Time only the already-qualified packed-X projection. Each prefix is fixed
/// by the original four-owner online transcript, and every output is dropped
/// before the next prefix so the pilot cannot hide an H21-wide owner cache.
fn c337_timed_fold_batch(packets: &[Vec<u8>], prefixes: &[Fr],
    pool: Option<&rayon::ThreadPool>) -> (Duration, Vec<Duration>) {
    assert_eq!(packets.len(), 16);
    assert_eq!(prefixes.len(), 20);
    let started = Instant::now();
    let mut by_prefix = Vec::with_capacity(21);
    for p in 0..=20 {
        let round_started = Instant::now();
        let plan = PilotFoldPlan::new(&prefixes[..p], &mut Counts::default());
        if let Some(pool) = pool {
            let output: Vec<Vec<Fr>> = pool.install(|| packets.par_iter().map(|packet| {
                plan.project(packet, &mut Counts::default())
            }).collect());
            assert_eq!(output.len(), 16);
            std::hint::black_box(&output);
            drop(output);
        } else {
            for packet in packets {
                let output = plan.project(packet, &mut Counts::default());
                std::hint::black_box(&output);
            }
        }
        by_prefix.push(round_started.elapsed());
    }
    (started.elapsed(), by_prefix)
}

#[test]
#[ignore = "C337 1-vs-16 packed-X throughput; run only in a bounded diagnostic Job"]
fn c337_parallel_fold_pilot() {
    let qualification_started = Instant::now();
    let slice = qualify();
    let parent = WorkTreeHistoryPlan::compile(1_827_840, 21, [0; 32], [0; 28]).unwrap();
    let roster = DaaHistoryRoster::compile(&parent).unwrap();
    let scheduled = Scheduled::eligible08();
    for owner in OWNERS { check_retirement(&roster, &scheduled, owner); }
    let placement = RowPlan::new(&roster, &scheduled).unwrap();
    let owner_terms: [Vec<Term>; 4] = OWNERS.map(|owner| owner_slice(&placement, owner, &slice));
    let original_packets = OWNERS.map(packet);
    let digest = packet_digest(&original_packets);
    let row_point: Vec<Fr> = (0..40).map(|i| Fr::from((7 + 3 * i) as u64)).collect();
    let factor = OneFamilyRowFactor::try_new(&row_point, 21, 19, 0, &[19], None).unwrap();
    assert!(OWNERS.iter().all(|&owner| !factor.copy(owner).is_zero()));
    let initial = initial_claim(&owner_terms, &original_packets, &factor);
    let seed = transcript(&row_point, &digest, initial);
    drop(owner_terms);
    drop(placement);
    drop(scheduled);
    drop(roster);
    drop(parent);
    let generic = run_arm(Arm::Generic, &slice.attached, &original_packets,
        &factor, seed.clone(), initial);
    assert_eq!(generic.rounds.len(), 20);
    assert_eq!(generic.prefixes.len(), 20);
    for (p, round) in generic.rounds.iter().enumerate() {
        assert!(!round.challenge.is_zero() && !round.challenge.is_one(),
            "non-Boolean online challenge at prefix {p}");
    }
    let qualification = qualification_started.elapsed();

    // The first four indices are actual C335 physical owners. The other twelve
    // are disjoint packet tags beyond H21, used only for throughput.
    let mut packets = original_packets.to_vec();
    for tag in 0..12 { packets.push(packet((1usize << 30) + tag)); }
    assert_eq!(packets.len(), 16);
    let mut digests = std::collections::BTreeSet::<Vec<u8>>::new();
    for data in &packets {
        assert_eq!(data.len(), WIDTH / 8);
        let mut hash = Blake2b::<U32>::new();
        hash.update(data);
        assert!(digests.insert(hash.finalize().to_vec()), "duplicate Boolean packet digest");
    }
    assert_eq!(digests.len(), 16);
    let pool = rayon::ThreadPoolBuilder::new().num_threads(16).build().unwrap();
    assert_eq!(pool.current_num_threads(), 16);

    // Three-way exact differential is outside both timed arms. The Subset4
    // path expands Boolean bits and checks Booleanity before its conversion.
    let differential_started = Instant::now();
    let mut fold_differentials = 0usize;
    let mut transcript_join_checked = false;
    for p in 0..=20 {
        let prefix = &generic.prefixes[..p];
        let plan = PilotFoldPlan::new(prefix, &mut Counts::default());
        let parallel: Vec<Vec<Fr>> = pool.install(|| packets.par_iter().map(|data| {
            plan.project(data, &mut Counts::default())
        }).collect());
        assert_eq!(parallel.len(), 16);
        let weights = boolean_u_eq_weights(prefix).unwrap();
        let mut subset_stats = BooleanSubset4Stats {
            extra_reserved_bytes: 256 * 1024 * 1024,
            ..Default::default()
        };
        let subset = BooleanSubset4Table::build(prefix, &weights, WIDTH,
            &mut subset_stats).unwrap();
        for (index, data) in packets.iter().enumerate() {
            let serial = plan.project(data, &mut Counts::default());
            let mut oracle = expand(data);
            assert_eq!(oracle.len(), WIDTH);
            assert_eq!(oracle.capacity(), WIDTH, "Subset4 oracle capacity");
            subset.apply(&mut oracle, &mut subset_stats).unwrap();
            assert_eq!(parallel[index], serial,
                "parallel vs serial packed fold, prefix={p}, packet={index}");
            assert_eq!(parallel[index], oracle,
                "packed fold vs checked Subset4, prefix={p}, packet={index}");
            fold_differentials += 1;
        }
        if p == 0 {
            let groups0 = canonical_groups(&slice.attached, prefix,
                &factor.local_weights, &mut Counts::default());
            let mut owner_messages = [[Fr::zero(); 3]; 4];
            let mut aggregate = [Fr::zero(); 3];
            for index in 0..4 {
                let rho = factor.copy(OWNERS[index]);
                let part = grouped_message(&groups0, &packets[index],
                    &parallel[index], rho, &mut Counts::default());
                owner_messages[index] = part;
                add(&mut aggregate, part);
            }
            let mut join_claim = initial;
            let mut join_transcript = seed.clone();
            let mut join_rounds = Vec::with_capacity(1);
            let challenge = send_round(aggregate.to_vec(), &mut join_claim,
                &mut join_rounds, &mut join_transcript).unwrap();
            let mut continuation = join_transcript.clone();
            let continuation = continuation.challenge_scalar(b"c335-pilot-continuation");
            let expected = &generic.rounds[0];
            assert_eq!(owner_messages, expected.owners, "canonical owner messages");
            assert_eq!(aggregate, expected.aggregate, "canonical aggregate");
            assert_eq!(challenge, expected.challenge, "online challenge");
            assert_eq!(join_claim, expected.claim, "updated claim");
            assert_eq!(continuation, expected.continuation,
                "transcript continuation");
            transcript_join_checked = true;
        }
    }
    assert_eq!(fold_differentials, 21 * 16);
    assert!(transcript_join_checked);
    let differential = differential_started.elapsed();

    // One diagnostic on identical packets/prefixes, with alternating order to
    // expose gross warm-order effects. Thread-pool construction is excluded.
    for pair in 0..3 {
        let (serial, parallel) = if pair % 2 == 0 {
            (c337_timed_fold_batch(&packets, &generic.prefixes, None),
             c337_timed_fold_batch(&packets, &generic.prefixes, Some(&pool)))
        } else {
            let parallel = c337_timed_fold_batch(&packets, &generic.prefixes, Some(&pool));
            let serial = c337_timed_fold_batch(&packets, &generic.prefixes, None);
            (serial, parallel)
        };
        assert!(serial.0 > Duration::from_millis(100)
            && parallel.0 > Duration::from_millis(100),
            "timed batches must exceed 100 ms");
        let ratio = parallel.0.as_secs_f64() / serial.0.as_secs_f64();
        println!("C337_FOLD_PAIR pair={} order={} serial_ns={} parallel16_ns={} ratio={:.6}",
            pair, if pair % 2 == 0 { "serial_parallel" } else { "parallel_serial" },
            serial.0.as_nanos(), parallel.0.as_nanos(), ratio);
        if pair == 0 {
            for p in 0..=20 {
                println!("C337_FOLD_PREFIX p={} serial_ns={} parallel16_ns={}",
                    p, serial.1[p].as_nanos(), parallel.1[p].as_nanos());
            }
        }
    }
    println!("C337_FOLD_QUALIFICATION source_and_online_ns={} exact_differential_ns={} fold_differentials={} packet_count=16 physical_transcript_owners=4 throughput_only_tags=12 bytes_per_packet={} max_parallel_fold_payload_bytes={} x_digest={}",
        qualification.as_nanos(), differential.as_nanos(), fold_differentials,
        WIDTH / 8, 16 * WIDTH * std::mem::size_of::<Fr>(),
        digest.iter().map(|byte| format!("{byte:02x}")).collect::<String>());
    println!("C337_PARALLEL_FOLD_PILOT_PASS throughput_diagnostic_only=true pairs=3 confidence_interval=not_computed full_proof=false public_admission=false");
}

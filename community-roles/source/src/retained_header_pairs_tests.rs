use std::{fs, path::PathBuf, time::Instant};

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use blake2::{digest::consts::U32, Blake2b, Digest};
use ergo_header_core::Header;

use crate::{
    daa_history_roster::OwnerClass,
    gkr,
    native_prefix_auth_plan::role0_sha256,
    native_work_relation::NativeWorkRelation,
    packed_owner_assembly::{
        validate_native_plan_input, AssemblyFault, NativeOwnerProducer, NativePackedRow,
        NativePrefix,
    },
    sparse::Term,
    work_tree_history_plan::WorkTreeHistoryPlan,
    work_tree_layout::WIDTH,
};

use super::{
    validate_pair_coverage, RetainedHeaderPair, RetainedHeaderPairs, OWNER_RETAINED_TERMS,
    OWNER_RETIRED_TERMS, PAIR_RETAINED_TERMS, PAIR_ROW_COUNT, SLOT_INPUT_WIDTH,
    SLOT_ROW_WIDTH,
};

const FIXTURE_ENV: &str = "NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR";
const FIXTURE_NAME: &str = "mainnet-prefix-first-3073-u32le-v1.bin";
const FIXTURE_BYTES: usize = 869_449;
const FIXTURE_SHA256: &str =
    "ABB3D74AE75256CED63110B72C2E0D5EBA1B90B09889E45EA327BDA1C9A640D2";
const FIXTURE_BLAKE2B256: &str =
    "8CDB90DA475E646280113D97C9469BE7EB86A1D04F20404C64239187284FC009";
const RAW_RECORDS: usize = 4;
const RAW_END: usize = 1_128;
const ROW_BYTES: usize = WIDTH / 8;
const X_LEN: usize = 1 << 22;
const WORK_TERM_COUNT: usize = 25_522;
const WORK_TERMS_BY_FAMILY: [usize; 6] = [1_121, 10_947, 224, 448, 224, 12_558];
const WORK_LOCAL_ROW_LOG: usize = 15;
const WORK_LOCAL_ROW_COUNT: usize = 1 << WORK_LOCAL_ROW_LOG;

const BAD_ALIAS_OWNER: usize = 1;
const BAD_ALIAS_LOCAL_WIRE: usize = 795_904;
const BAD_ALIAS_GLOBAL_WIRE: usize = (1 << 20) + BAD_ALIAS_LOCAL_WIRE;
const BAD_ALIAS_RIGHT_GLOBAL_WIRE: usize = (1 << 20) + 655_372;
const BAD_ALIAS_PAIR_ROW: usize = SLOT_ROW_WIDTH + 406_150;

fn emit(stage: &str, detail: &str) {
    println!("C556_GATE1_STAGE|{stage}|{detail}");
}

fn hex_upper(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02X}")).collect()
}

fn read_first_four(bundle: &[u8]) -> (Vec<Vec<u8>>, Vec<usize>, usize) {
    let mut raws = Vec::with_capacity(RAW_RECORDS);
    let mut lengths = Vec::with_capacity(RAW_RECORDS);
    let mut offset = 0usize;
    for _ in 0..RAW_RECORDS {
        let length_end = offset.checked_add(4).expect("RAW length offset");
        let length_bytes: [u8; 4] = bundle
            .get(offset..length_end)
            .expect("four-byte RAW length")
            .try_into()
            .expect("four-byte RAW length shape");
        let length = u32::from_le_bytes(length_bytes) as usize;
        assert_eq!(length, 278, "first four pinned RAW lengths");
        offset = length_end;
        let raw_end = offset.checked_add(length).expect("RAW end offset");
        raws.push(
            bundle
                .get(offset..raw_end)
                .expect("complete pinned RAW")
                .to_vec(),
        );
        lengths.push(length);
        offset = raw_end;
    }
    assert_eq!(offset, RAW_END, "first four RAWs end at byte 1128");
    (raws, lengths, offset)
}

fn real_prefix_fixture() -> (PathBuf, Vec<Vec<u8>>, NativePrefix) {
    let directory = PathBuf::from(
        std::env::var_os(FIXTURE_ENV)
            .expect("NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR must be set explicitly"),
    );
    let path = directory.join(FIXTURE_NAME);
    let bundle = fs::read(&path).expect("read the pinned offline prefix bundle");
    assert_eq!(bundle.len(), FIXTURE_BYTES, "whole-file size");

    let sha256 = hex_upper(&role0_sha256(&bundle).expect("native SHA-256 of whole bundle"));
    assert_eq!(sha256, FIXTURE_SHA256, "whole-file SHA-256");
    let blake2b256 = hex_upper(&Blake2b::<U32>::digest(&bundle));
    assert_eq!(blake2b256, FIXTURE_BLAKE2B256, "whole-file BLAKE2b-256");

    let (raws, lengths, offset) = read_first_four(&bundle);
    emit(
        "source_fixture",
        &format!(
            "file={} bytes={} sha256={} blake2b256={} lengths={:?} end={}",
            path.display(),
            bundle.len(),
            sha256,
            blake2b256,
            lengths,
            offset
        ),
    );

    let input = NativePrefix::from_raw_iter(
        RAW_RECORDS,
        raws.iter().cloned().map(Ok::<Vec<u8>, String>),
    )
    .expect("parse exactly the first four pinned RAWs");
    assert_eq!(input.header_count(), 4);
    assert_eq!(input.genuine_count(), 3);
    assert_eq!(input.slot_count(), 4);
    assert_eq!(input.leaf_count(), 4);
    assert_eq!(input.node_count(), 4);
    emit(
        "native_prefix",
        &format!(
            "headers=4 genuine=3 slots=4 leaves=4 profile={} root={} total={}",
            hex_upper(&input.profile()),
            hex_upper(&input.root()),
            hex_upper(&input.total_be28())
        ),
    );
    (directory, raws, input)
}

fn malformed_raw_reaches_native_parser(raws: &[Vec<u8>]) {
    let mut malformed = raws.to_vec();
    malformed[1] = vec![0xFF];
    assert!(
        Header::decode(&malformed[1], None).is_err(),
        "the malformed control must fail at header decode"
    );
    let error = match NativePrefix::from_raw_iter(
        RAW_RECORDS,
        malformed.into_iter().map(Ok::<Vec<u8>, String>),
    ) {
        Err(error) => error,
        Ok(_) => panic!("malformed RAW unexpectedly parsed"),
    };
    assert!(error.contains("native prefix decode"), "{error}");
}

fn expected_owner_classes() -> [OwnerClass; 4] {
    [
        OwnerClass::Genesis,
        OwnerClass::Initial,
        OwnerClass::Carry,
        OwnerClass::Carry,
    ]
}

fn expand_rows(rows: &[NativePackedRow]) -> Result<Vec<Fr>, String> {
    if rows.len() != RAW_RECORDS {
        return Err("shared X requires exactly four complete owner rows".into());
    }
    let expected_classes = expected_owner_classes();
    for (owner, row) in rows.iter().enumerate() {
        if row.owner() != owner {
            return Err(format!(
                "shared X owner order mismatch: expected {owner}, got {}",
                row.owner()
            ));
        }
        if row.class() != expected_classes[owner] {
            return Err(format!(
                "shared X owner class mismatch at owner {owner}: {:?}",
                row.class()
            ));
        }
        if row.packed_bytes().len() != ROW_BYTES {
            return Err(format!("shared X packed row width mismatch at owner {owner}"));
        }
    }

    let mut input = Vec::new();
    input
        .try_reserve_exact(X_LEN)
        .map_err(|_| "shared X allocation failed")?;
    for row in rows {
        for wire in 0..WIDTH {
            let bit = (row.packed_bytes()[wire / 8] >> (wire % 8)) & 1;
            input.push(Fr::from(bit as u64));
        }
    }
    if input.len() != X_LEN {
        return Err("shared X width differs from 2^22".into());
    }
    Ok(input)
}

fn gate_residual(term: &Term, input: &[Fr], input_base: usize) -> Fr {
    let left = input[input_base + term.gate.left];
    let right = input[input_base + term.gate.right];
    term.gate.c0 + term.gate.c1 * left + term.gate.c2 * right
        + term.gate.c3 * left * right
}

fn work_family_census_and_zero(terms: &[Term], input: &[Fr]) -> [usize; 6] {
    let mut counts = [0usize; 6];
    let mut residuals: [Vec<Fr>; 6] =
        std::array::from_fn(|_| vec![Fr::zero(); WORK_LOCAL_ROW_COUNT]);
    for term in terms {
        assert!(term.row < (1 << 18), "native work row outside log-18 domain");
        let family = term.row >> WORK_LOCAL_ROW_LOG;
        assert!(family < counts.len(), "native work family tag outside six-family set");
        let row = term.row & (WORK_LOCAL_ROW_COUNT - 1);
        counts[family] += 1;
        residuals[family][row] += gate_residual(term, input, 0);
    }
    assert_eq!(terms.len(), WORK_TERM_COUNT);
    assert_eq!(counts, WORK_TERMS_BY_FAMILY);
    for (family, rows) in residuals.iter().enumerate() {
        assert!(
            rows.iter().all(|value| value.is_zero()),
            "native work family {family} has a nonzero row residual"
        );
    }
    counts
}

fn residuals_by_row(
    terms: &[Term],
    input: &[Fr],
    input_base: usize,
    row_count: usize,
) -> Vec<Fr> {
    let mut residuals = vec![Fr::zero(); row_count];
    for term in terms {
        assert!(term.row < row_count, "relation row outside residual array");
        assert!(
            input_base + term.gate.left < input.len()
                && input_base + term.gate.right < input.len(),
            "relation input outside shared X"
        );
        residuals[term.row] += gate_residual(term, input, input_base);
    }
    residuals
}

fn active_term_reads(term: &Term, wire: usize) -> bool {
    (term.gate.left == wire && (!term.gate.c1.is_zero() || !term.gate.c3.is_zero()))
        || (term.gate.right == wire && (!term.gate.c2.is_zero() || !term.gate.c3.is_zero()))
}

fn point(bits: usize, seed: u64) -> Vec<Fr> {
    (0..bits)
        .map(|index| {
            let coordinate = index as u64 + 1;
            Fr::from(seed + coordinate * 17 + coordinate * coordinate * 3)
        })
        .collect()
}

fn assert_non_boolean(point: &[Fr]) {
    assert!(
        point
            .iter()
            .all(|coordinate| !coordinate.is_zero() && !coordinate.is_one()),
        "differential points must be asymmetric and non-Boolean"
    );
}

fn direct_single_term(term: &Term, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let row_weights = gkr::eq_weights(r);
    let left_weights = gkr::eq_weights(u);
    let right_weights = gkr::eq_weights(v);
    let weight = row_weights[term.row]
        * left_weights[term.gate.left]
        * right_weights[term.gate.right];
    [
        weight * term.gate.c0,
        weight * term.gate.c1,
        weight * term.gate.c2,
        weight * term.gate.c3,
    ]
}

fn retained_embedding_differentials(
    plan: &WorkTreeHistoryPlan,
    pairs: &RetainedHeaderPairs,
) {
    for seed in [17u64, 43u64] {
        let r = point(20, seed);
        let u = point(21, seed + 1_001);
        let v = point(21, seed + 2_003);
        assert_non_boolean(&r);
        assert_non_boolean(&u);
        assert_non_boolean(&v);

        for start in [0u64, 2u64] {
            let pair = pairs.pair(start).unwrap();
            let direct = pair.coefficients(&r, &u, &v).unwrap();
            let global_r = pairs.embed_row_point(start, &r).unwrap();
            let global_u = pairs.embed_input_point(start, &u).unwrap();
            let global_v = pairs.embed_input_point(start, &v).unwrap();
            assert_eq!(global_r.len(), 21);
            assert_eq!(global_u.len(), 22);
            assert_eq!(global_v.len(), 22);
            assert_eq!(global_r[20], Fr::from((start >> 1) as u64));
            assert_eq!(global_u[21], Fr::from((start >> 1) as u64));
            assert_eq!(global_v[21], Fr::from((start >> 1) as u64));
            assert_eq!(
                plan.coefficients(&global_r, &global_u, &global_v).unwrap(),
                direct,
                "retained pair {start} direct-term / parent coefficient differential"
            );

            let mut wrong_prefix_v = global_v.clone();
            wrong_prefix_v[21] = Fr::one() - wrong_prefix_v[21];
            assert_ne!(
                plan.coefficients(&global_r, &global_u, &wrong_prefix_v)
                    .unwrap(),
                direct,
                "mismatched right-input pair bit must break same-owner wiring"
            );

            let mut wrong_order_v = global_v.clone();
            wrong_order_v.swap(20, 21);
            assert_ne!(
                plan.coefficients(&global_r, &global_u, &wrong_order_v)
                    .unwrap(),
                direct,
                "right-input free-bit/fixed-bit order mutant"
            );
        }
    }
}

fn retained_alias_bad_x_control(
    pairs: &RetainedHeaderPairs,
    work_terms: &[Term],
    input: &[Fr],
) {
    let pair0 = pairs.pair(0).unwrap();
    let pair2 = pairs.pair(2).unwrap();
    assert_eq!(pair0.terms().len(), PAIR_RETAINED_TERMS);
    assert_eq!(pair2.terms().len(), PAIR_RETAINED_TERMS);
    assert!(input[BAD_ALIAS_GLOBAL_WIRE].is_zero() || input[BAD_ALIAS_GLOBAL_WIRE].is_one());
    assert_eq!(
        input[BAD_ALIAS_GLOBAL_WIRE],
        input[BAD_ALIAS_RIGHT_GLOBAL_WIRE],
        "real owner-1 digest-copy bit agrees with its source"
    );

    let matching: Vec<_> = pair0
        .terms()
        .iter()
        .enumerate()
        .filter(|(_, term)| {
            term.row == BAD_ALIAS_PAIR_ROW
                && term.gate.left == BAD_ALIAS_GLOBAL_WIRE
                && term.gate.right == BAD_ALIAS_RIGHT_GLOBAL_WIRE
                && term.gate.c0.is_zero()
                && term.gate.c1 == Fr::one()
                && term.gate.c2 == -Fr::one()
                && term.gate.c3.is_zero()
        })
        .collect();
    assert_eq!(matching.len(), 1, "one complete retained digest-copy equation");
    let selected_index = matching[0].0;
    let selected_term = matching[0].1;
    assert_eq!(
        pair0
            .terms()
            .iter()
            .filter(|term| active_term_reads(term, BAD_ALIAS_GLOBAL_WIRE))
            .count(),
        1,
        "changed cell has one active retained consumer"
    );
    assert!(
        !pair2
            .terms()
            .iter()
            .any(|term| {
                let base = pair2.start() as usize * SLOT_INPUT_WIDTH;
                BAD_ALIAS_GLOBAL_WIRE.checked_sub(base)
                    .map(|local| active_term_reads(term, local))
                    .unwrap_or(false)
            }),
        "pair2 does not read owner1 digest-copy cell"
    );
    assert!(
        !work_terms
            .iter()
            .any(|term| active_term_reads(term, BAD_ALIAS_GLOBAL_WIRE)),
        "native work does not read owner1 digest-copy cell"
    );
    assert_eq!(selected_term.row, 930_438);
    assert_eq!(selected_term.gate.left, 1_844_480);
    assert_eq!(selected_term.gate.right, 1_703_948);

    let old_bit = input[BAD_ALIAS_GLOBAL_WIRE];
    let mut bad_input = input.to_vec();
    bad_input[BAD_ALIAS_GLOBAL_WIRE] = Fr::one() - old_bit;
    let work_counts = work_family_census_and_zero(work_terms, &bad_input);
    let pair2_residuals = residuals_by_row(
        pair2.terms(),
        &bad_input,
        pair2.start() as usize * SLOT_INPUT_WIDTH,
        PAIR_ROW_COUNT,
    );
    assert!(pair2_residuals.iter().all(|value| value.is_zero()));

    let pair0_residuals = residuals_by_row(
        pair0.terms(),
        &bad_input,
        pair0.start() as usize * SLOT_INPUT_WIDTH,
        PAIR_ROW_COUNT,
    );
    let support: Vec<_> = pair0_residuals
        .iter()
        .enumerate()
        .filter_map(|(row, value)| (!value.is_zero()).then_some(row))
        .collect();
    assert_eq!(support, vec![BAD_ALIAS_PAIR_ROW]);
    assert_eq!(
        pair0_residuals[BAD_ALIAS_PAIR_ROW],
        Fr::one() - Fr::from(2u64) * old_bit
    );

    let omitted: Vec<_> = pair0
        .terms()
        .iter()
        .enumerate()
        .filter_map(|(index, term)| (index != selected_index).then_some(term.clone()))
        .collect();
    assert_eq!(omitted.len(), PAIR_RETAINED_TERMS - 1);
    let omitted_residuals = residuals_by_row(
        &omitted,
        &bad_input,
        pair0.start() as usize * SLOT_INPUT_WIDTH,
        PAIR_ROW_COUNT,
    );
    assert!(
        omitted_residuals.iter().all(|value| value.is_zero()),
        "exact complete-equation removal clears only the isolated Gate1 fault"
    );

    emit(
        "retained_alias_bad_x",
        &format!(
            "owner={} local_wire={} global_wire={} pair0_row={} work_zero=true work_families={:?} pair2_zero=true pair0_support={}:{} exact_term_removed=1 omission_clears=true proof=false",
            BAD_ALIAS_OWNER,
            BAD_ALIAS_LOCAL_WIRE,
            BAD_ALIAS_GLOBAL_WIRE,
            BAD_ALIAS_PAIR_ROW,
            work_counts,
            BAD_ALIAS_PAIR_ROW,
            pair0_residuals[BAD_ALIAS_PAIR_ROW]
        ),
    );
}

fn cheap_negative_controls(
    rows: &[NativePackedRow],
    pairs: &RetainedHeaderPairs,
    pair0: &RetainedHeaderPair,
    producer: &NativeOwnerProducer<'_>,
) {
    let mut swapped = rows.to_vec();
    swapped.swap(1, 2);
    assert!(expand_rows(&swapped).unwrap_err().contains("owner order"));
    assert!(expand_rows(&rows[..3]).unwrap_err().contains("exactly four"));

    let mut missing_term = pair0.clone();
    missing_term.terms.pop();
    assert!(validate_pair_coverage(&missing_term).is_err());
    assert!(pairs.pair(1).is_err());
    assert!(pairs.pair(3).is_err());
    let r = point(20, 83);
    let u = point(21, 197);
    let v = point(21, 311);
    assert!(pair0.coefficients(&r[..19], &u, &v).is_err());
    assert!(pairs.embed_row_point(0, &r[..19]).is_err());
    assert!(pairs.embed_input_point(0, &u[..20]).is_err());

    emit(
        "claim_conflict_start",
        &format!("owner={BAD_ALIAS_OWNER} wire={BAD_ALIAS_LOCAL_WIRE}"),
    );
    let started = Instant::now();
    let conflict_result = producer.produce_fault_for_test(
            BAD_ALIAS_OWNER,
            AssemblyFault::ConflictingClaim {
                owner: BAD_ALIAS_OWNER as u64,
                wire: BAD_ALIAS_LOCAL_WIRE,
            },
        );
    let error = match conflict_result {
        Err(error) => error,
        Ok(_) => panic!("conflicting producer claim unexpectedly succeeded"),
    };
    assert!(error.contains("claim conflict"), "{error}");
    emit(
        "claim_conflict_done",
        &format!("boundary=OwnedRows::claim rejected=true elapsed_ms={}", started.elapsed().as_millis()),
    );
}

#[test]
#[ignore = "bounded C556 real-prefix native-work/retained-pairs Gate1"]
fn real_prefix_work_and_retained_pairs_gate1() {
    emit("start", "headers=4 slots=4 pairs=0,2 input_log=22 profile=strict");

    let (_directory, raws, input) = real_prefix_fixture();
    malformed_raw_reaches_native_parser(&raws);
    emit("malformed_raw", "native_prefix_parser=true digest_bypass=true");

    let plan =
        WorkTreeHistoryPlan::compile(4, 2, input.root(), input.total_be28()).unwrap();
    validate_native_plan_input(&plan, &input).unwrap();
    assert_eq!(plan.descriptor().root, input.root());
    assert_eq!(plan.work_profile().total_be28, input.total_be28());
    assert_eq!(plan.descriptor().headers, 4);
    assert_eq!(plan.descriptor().genuine, 3);
    assert_eq!(plan.descriptor().slots, 4);
    assert_eq!(plan.descriptor().leaves, 4);

    let producer = NativeOwnerProducer::new_for_history(&plan, &input).unwrap();
    let expected_classes = expected_owner_classes();
    let mut rows = Vec::with_capacity(RAW_RECORDS);
    for owner in 0..RAW_RECORDS {
        let row = producer.produce(owner).unwrap();
        assert_eq!(row.owner(), owner);
        assert_eq!(row.class(), expected_classes[owner]);
        assert_eq!(row.packed_bytes().len(), ROW_BYTES);
        emit(
            &format!("owner_{owner}"),
            &format!(
                "owner={} class={:?} packed_bytes={} complete=true",
                row.owner(),
                row.class(),
                row.packed_bytes().len()
            ),
        );
        rows.push(row);
    }
    assert_eq!(rows[3].class(), OwnerClass::Carry, "owner 3 is a real header owner");

    let input_x = expand_rows(&rows).unwrap();
    assert_eq!(input_x.len(), X_LEN);
    emit(
        "shared_x",
        &format!("owner_major=true field_elements={} packed_bytes_per_owner={ROW_BYTES}", input_x.len()),
    );

    let pairs = RetainedHeaderPairs::new_for_history(&plan).unwrap();
    assert_eq!(pairs.starts(), [0, 2]);
    let work = NativeWorkRelation::new(&plan).unwrap();
    assert_eq!(work.input_log(), 22);
    assert_eq!(work.row_log(), 18);
    let mut work_terms = Vec::with_capacity(WORK_TERM_COUNT);
    let work_count = work
        .visit_terms(|term| {
            work_terms.push(term);
            Ok(())
        })
        .unwrap();
    assert_eq!(work_count, WORK_TERM_COUNT);
    let work_counts = work_family_census_and_zero(&work_terms, &input_x);
    emit(
        "work",
        &format!(
            "terms={} family_terms={:?} residual_nonzero_rows=0 aliases_equal=true",
            work_count, work_counts
        ),
    );

    for start in [0u64, 2u64] {
        let pair = pairs.pair(start).unwrap();
        assert_eq!(pair.terms().len(), PAIR_RETAINED_TERMS);
        assert_eq!(pair.owner_term_counts(), [OWNER_RETAINED_TERMS; 2]);
        assert_eq!(pair.omitted_worktree_counts(), [OWNER_RETIRED_TERMS; 2]);
        assert_eq!(pair.omitted_a4_counts(), [0; 2]);
        let residuals = residuals_by_row(
            pair.terms(),
            &input_x,
            start as usize * SLOT_INPUT_WIDTH,
            PAIR_ROW_COUNT,
        );
        assert!(residuals.iter().all(|value| value.is_zero()));
        emit(
            &format!("pair_{start}"),
            &format!(
                "terms={} owner_terms={:?} retired_per_owner={:?} a4={:?} residual_nonzero_rows=0 cap_margin={}",
                pair.terms().len(),
                pair.owner_term_counts(),
                pair.omitted_worktree_counts(),
                pair.omitted_a4_counts(),
                1_048_576 - pair.terms().len()
            ),
        );
    }

    retained_embedding_differentials(&plan, &pairs);
    let pair0 = pairs.pair(0).unwrap();
    let second_slot_right_zero = pair0.terms().iter().find(|term| {
        term.row >= SLOT_ROW_WIDTH
            && term.gate.right == SLOT_INPUT_WIDTH
            && [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3]
                .iter().any(|coefficient| !coefficient.is_zero())
    });
    let second_slot_right_zero =
        second_slot_right_zero.expect("second-slot local right zero maps to pair input 2^20");
    let r = point(20, 97);
    let u = point(21, 227);
    let v = point(21, 359);
    let correct_right = direct_single_term(second_slot_right_zero, &r, &u, &v);
    let mut wrong_right_zero = second_slot_right_zero.clone();
    wrong_right_zero.gate.right = 0;
    let wrong_right = direct_single_term(&wrong_right_zero, &r, &u, &v);
    assert_ne!(correct_right, wrong_right, "deliberate second-slot right-zero mutant");
    emit(
        "differential",
        "asymmetric_nonboolean_seeds=2 parent_coefficients=match prefix_flip=rejected bit_order_mutant=rejected second_slot_right_zero=rejected",
    );

    retained_alias_bad_x_control(&pairs, &work_terms, &input_x);
    cheap_negative_controls(&rows, &pairs, pair0, &producer);
    emit(
        "negatives",
        "malformed_raw_parser=reject owner_swap=reject missing_row=reject coverage=reject dimensions=reject claim_conflict=reject alias_bad_x=isolated pair_prefix=reject pair_right_zero=reject",
    );
    emit(
        "PASS",
        "gate1_source_fixture=true native_prefix=true owners=4 work_zero=true pairs_0_2_zero=true differential=true proof=false full_history=false",
    );
}

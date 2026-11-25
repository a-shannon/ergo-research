//! The first Mainnet Legacy retarget: one positive sample and its compact roundtrip.
use super::{Context, NumericRule};
use crate::{
    daa_integer::{self, CompiledCarry},
    gkr::{self, GkrError},
    header_hash,
    packed::{self, PackedFile, PackedFileWriter},
    pcs, serializer,
    sparse::{self, Circuit},
    sparse_stream_roster::{self, EdgeTerm},
    transcript::Transcript,
    verifier_key,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
use num_bigint::{BigInt, BigUint, Sign};
use std::{fs::OpenOptions, io::Write, time::Instant};

const WIDTH: usize = 1 << 20;
const MEMBER_ROWS: [usize; 2] = [19, 18];

// Byte/MPI model of DifficultySerializer.scala. It deliberately does not call
// the circuit's compact decoder or the host header decoder.
fn mpi(raw: u32) -> (bool, BigUint) {
    let size = ((raw >> 24) & 0xff) as usize;
    let mut mpi = vec![0u8; 4 + size];
    mpi[3] = size as u8;
    for (i, shift) in [16, 8, 0].into_iter().enumerate().take(size.min(3)) {
        mpi[4 + i] = (raw >> shift) as u8;
    }
    let payload = &mut mpi[4..];
    let negative = payload.first().is_some_and(|b| b & 0x80 != 0);
    if let Some(first) = payload.first_mut() {
        *first &= 0x7f;
    }
    (negative, BigUint::from_bytes_be(payload))
}

fn encode_mpi(value: &BigUint) -> u32 {
    let signed = BigInt::from_biguint(Sign::Plus, value.clone()).to_signed_bytes_be();
    let mut size = signed.len();
    let mut mantissa = [0u8; 3];
    let take = signed.len().min(3);
    mantissa[..take].copy_from_slice(&signed[..take]);
    let mut word = u32::from_be_bytes([0, mantissa[0], mantissa[1], mantissa[2]]);
    if word & 0x0080_0000 != 0 {
        word >>= 8;
        size += 1;
    }
    ((size as u32) << 24) | word
}

fn roundtrip(value: &BigUint) -> (u32, BigUint) {
    let compact = encode_mpi(value);
    (compact, mpi(compact).1)
}

fn singleton_raw_pair() -> (u32, u32) {
    let (_, headers) = crate::header_history_boundary::tests::fixture();
    let parent = ergo_header_core::Header::decode(&headers[&1024], None).unwrap();
    let child = ergo_header_core::Header::decode(&headers[&1025], None).unwrap();
    (
        serializer::Fields::from_header(&parent).unwrap().n_bits,
        serializer::Fields::from_header(&child).unwrap().n_bits,
    )
}

fn singleton_assignment(child_height: u32) -> Vec<Fr> {
    let (_, headers) = crate::header_history_boundary::tests::fixture();
    let child = ergo_header_core::Header::decode(&headers[&child_height], None).unwrap();
    let fields = serializer::Fields::from_header(&child).unwrap();
    let previous_time = if child_height == 1024 {
        // The frozen fixture has RAW 1024/1025 but no 1023. This local seed
        // satisfies only the order witness; it is not an authenticated parent.
        fields.timestamp.checked_sub(1).unwrap()
    } else {
        ergo_header_core::Header::decode(&headers[&(child_height - 1)], None)
            .unwrap()
            .timestamp
    };
    let mut boundary = crate::daa_history_layout::full_header_boundary(Some(&fields)).unwrap();
    crate::header_compact_links::assign_order(
        &mut boundary,
        &fields,
        child_height - 1,
        previous_time,
        false,
    )
    .unwrap();
    boundary.base.base.base.input.take().unwrap()
}

fn pack_bits(values: &[Fr]) -> Vec<u8> {
    let mut bytes = vec![0u8; values.len().div_ceil(8)];
    for (i, value) in values.iter().enumerate() {
        assert!(*value == Fr::zero() || *value == Fr::one());
        if *value == Fr::one() {
            bytes[i / 8] |= 1 << (i % 8);
        }
    }
    bytes
}

fn write_create_new(path: &std::path::Path, bytes: &[u8]) {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .unwrap();
    file.write_all(bytes).unwrap();
    file.sync_all().unwrap();
}

fn residuals(circuit: &Circuit, input: &[Fr]) -> Vec<Fr> {
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms {
        rows[term.row] += term.gate.evaluate(input);
    }
    rows
}

fn compiled_word(c: &CompiledCarry) -> BigUint {
    c.decoded
        .iter()
        .enumerate()
        .fold(BigUint::zero(), |n, (i, &wire)| {
            n + if c.witness[wire] == Fr::one() {
                BigUint::one() << i
            } else {
                BigUint::zero()
            }
        })
}

#[test]
fn legacy_singleton_native_roundtrip_topology_and_full_header_owners() {
    let c = Context::for_rule(NumericRule::LegacySingleton).unwrap();
    let plan = crate::daa_header_window::for_child_height(1025).unwrap();
    assert_eq!(
        plan.action(),
        crate::daa_header_window::Action::Retarget(daa_integer::Epoch::Legacy)
    );
    assert_eq!(plan.sample_heights(), [1024]);
    let unfiltered = (0..=8u32)
        .rev()
        .filter_map(|back| 1024u32.checked_sub(back * 1024))
        .collect::<Vec<_>>();
    assert_eq!(unfiltered, [0, 1024]);
    assert_eq!(
        unfiltered
            .into_iter()
            .filter(|height| *height > 0)
            .collect::<Vec<_>>(),
        plan.sample_heights()
    );

    let q = crate::daa_count::q();
    let (parent_raw, child_raw) = singleton_raw_pair();
    let (parent_negative, parent_value) = mpi(parent_raw);
    let (child_negative, child_value) = mpi(child_raw);
    assert!(!parent_negative && !child_negative);
    assert!(!parent_value.is_zero() && parent_value <= q);
    assert_eq!(parent_value, child_value);
    let actual_roundtrip = roundtrip(&parent_value);
    assert_eq!(actual_roundtrip.1, child_value);
    assert_eq!(
        crate::daa_finish::native_positive_compact_roundtrip(&parent_value),
        actual_roundtrip
    );
    assert_eq!(
        crate::work_tree_work::native_decode(parent_raw).unwrap(),
        parent_value
    );
    assert_eq!(
        crate::work_tree_work::native_decode(child_raw).unwrap(),
        child_value
    );

    // Exercise short exponents, aliases, leading-sign-byte boundaries, and
    // admitted high exponents with the separate byte/MPI implementation.
    let mut tested_high_exponent = false;
    for raw in [
        0x0101_0000,
        0x0101_ffff,
        0x0200_0100,
        0x0200_ffff,
        0x0300_0001,
        0x0300_7fff,
        0x0300_8000,
        0x0300_ffff,
        0x2000_0001,
        0x2100_0001,
        0x2200_0080,
    ] {
        let (negative, value) = mpi(raw);
        if !negative && !value.is_zero() && value <= q {
            let (canonical, decoded) = roundtrip(&value);
            assert_eq!(decoded, value, "raw compact {raw:08x}");
            assert_eq!(mpi(canonical).1, value, "canonical {canonical:08x}");
            assert_eq!(
                crate::daa_finish::native_positive_compact_roundtrip(&value).1,
                value,
                "native compact roundtrip {raw:08x}"
            );
            assert_eq!(
                crate::daa_finish::native_positive_compact_roundtrip(&value),
                (canonical, decoded.clone()),
                "canonical word {raw:08x}"
            );
            tested_high_exponent |= raw >> 24 >= 32;
        }
    }
    assert!(
        tested_high_exponent,
        "a high exponent admitted by Q is covered"
    );
    for value in [
        BigUint::one(),
        (BigUint::one() << 15usize) - BigUint::one(),
        BigUint::one() << 15usize,
        (BigUint::one() << 23usize) - BigUint::one(),
        BigUint::one() << 23usize,
        (BigUint::one() << 255usize) + (BigUint::one() << 248usize),
    ] {
        assert!(value <= q);
        let (compact, decoded) = roundtrip(&value);
        assert_eq!(decoded, value, "compact={compact:08x}");
        assert_eq!(
            crate::daa_finish::native_positive_compact_roundtrip(&value),
            (compact, decoded.clone())
        );
    }
    let outside_compact_image = (BigUint::one() << 23usize) + BigUint::one();
    let (outside_word, outside_value) = roundtrip(&outside_compact_image);
    assert_ne!(outside_value, outside_compact_image);
    assert_eq!(
        crate::daa_finish::native_positive_compact_roundtrip(&outside_compact_image),
        (outside_word, outside_value)
    );
    for alias in [0x0101_0000, 0x0200_0100, 0x0300_0001] {
        assert_eq!(mpi(alias), (false, BigUint::one()));
    }

    let actual = daa_integer::compile_carry(&q, parent_raw, child_raw, true).unwrap();
    assert!(residuals(actual.circuit.as_ref().unwrap(), &actual.witness)
        .iter()
        .all(Zero::is_zero));
    assert_eq!(actual.circuit, c.expected.circuit);
    assert_eq!(actual.parent_nbits, c.expected.parent_nbits);
    assert_eq!(actual.child_nbits, c.expected.child_nbits);
    assert_eq!(compiled_word(&actual), parent_value);
    assert!(actual
        .witness
        .iter()
        .all(|x| *x == Fr::zero() || *x == Fr::one()));
    for bit in 0..32 {
        assert_eq!(
            actual.witness[actual.parent_nbits[bit]],
            Fr::from(((parent_raw >> bit) & 1) as u64)
        );
        assert_eq!(
            actual.witness[actual.child_nbits[bit]],
            Fr::from(((child_raw >> bit) & 1) as u64)
        );
    }
    assert_eq!(actual.count.terms, 11804);
    assert_eq!(actual.count.padded_input_bits, 4096);
    assert_eq!(actual.count.padded_rows, 8192);
    assert_eq!(c.natural.terms, actual.circuit.as_ref().unwrap().terms);
    assert!(residuals(&c.natural, &actual.witness)
        .iter()
        .all(Zero::is_zero));

    // A one-bit decoded-value difference is isolated to the child decoder.
    let canonical = encode_mpi(&child_value);
    let changed = canonical ^ 0x0001_0000;
    assert_ne!(mpi(changed).1, child_value);
    let mismatch = daa_integer::compile_carry(&q, parent_raw, changed, true).unwrap();
    let failed = residuals(mismatch.circuit.as_ref().unwrap(), &mismatch.witness)
        .iter()
        .enumerate()
        .filter(|(_, x)| !x.is_zero())
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    assert_eq!(failed.len(), 1);
    assert!(mismatch.decoder_rows[1].contains(&failed[0]));

    // Different raw compacts with the same numeric value remain admissible.
    for (a, b) in [(0x0300_0001, 0x0101_0000), (0x0200_0100, 0x0300_0001)] {
        let alias = daa_integer::compile_carry(&q, a, b, true).unwrap();
        assert!(residuals(alias.circuit.as_ref().unwrap(), &alias.witness)
            .iter()
            .all(Zero::is_zero));
        assert_eq!(alias.circuit, c.expected.circuit);
        assert_eq!(compiled_word(&alias), BigUint::one());
    }

    let (_, headers) = crate::header_history_boundary::tests::fixture();
    for (i, height) in [1024, 1025].into_iter().enumerate() {
        let input = singleton_assignment(height);
        assert_eq!(input.len(), WIDTH);
        let copy = 12 + i;
        let mut row = None;
        let mut residual = Fr::zero();
        let mut count = 0;
        c.header_terms(copy, |edge| {
            if row != Some(edge.family_row) {
                assert!(residual.is_zero(), "header copy={copy} row={row:?}");
                row = Some(edge.family_row);
                residual = Fr::zero();
            }
            let mut gate = edge.term.gate;
            gate.left -= copy * WIDTH;
            gate.right -= copy * WIDTH;
            residual += gate.evaluate(&input);
            count += 1;
            Ok(())
        })
        .unwrap();
        assert!(residual.is_zero());
        assert_eq!(count, 474755);
        let mut height_count = 0;
        c.height_terms(copy, |edge| {
            let mut gate = edge.term.gate;
            gate.left -= copy * WIDTH;
            gate.right -= copy * WIDTH;
            assert!(gate.evaluate(&input).is_zero());
            height_count += 1;
            Ok(())
        })
        .unwrap();
        assert_eq!(height_count, 32);
        let header = ergo_header_core::Header::decode(&headers[&height], None).unwrap();
        assert_eq!(
            serializer::Fields::from_header(&header).unwrap().n_bits,
            if height == 1024 {
                parent_raw
            } else {
                child_raw
            }
        );
    }
    println!("Mainnet Legacy child1025 uses positive singleton [1024]; independent MPI compact roundtrips, actual numeric join, 11804-term decoder, and both 474755+32 full-header owners passed");
}

#[test]
fn legacy_singleton_four_families_match_full24_finite_oracle() {
    let c = Context::for_rule(NumericRule::LegacySingleton).unwrap();
    let r = (0..24)
        .map(|i| Fr::from((17 + i * 7) as u64))
        .collect::<Vec<_>>();
    let u = (0..24)
        .map(|i| Fr::from((37 + i * 13) as u64))
        .collect::<Vec<_>>();
    let v = (0..24)
        .map(|i| Fr::from((53 + i * 19) as u64))
        .collect::<Vec<_>>();
    let (header, header_count) = super::finite(
        |sink| {
            for copy in [12, 13] {
                c.header_terms(copy, &mut *sink)?;
            }
            Ok(())
        },
        &r,
        &u,
        &v,
    );
    let (height, height_count) = super::finite(
        |sink| {
            for copy in [12, 13] {
                c.height_terms(copy, &mut *sink)?;
            }
            Ok(())
        },
        &r,
        &u,
        &v,
    );
    let (arithmetic, arithmetic_count) = super::finite(|sink| c.arithmetic(sink), &r, &u, &v);
    let (aliases, alias_count) = super::finite(|sink| c.aliases(sink), &r, &u, &v);
    assert_eq!(
        [header_count, height_count, arithmetic_count, alias_count],
        [949510, 64, 11804, 64]
    );
    let parts = c.parts(&r, &u, &v).unwrap();
    assert_eq!(parts, [header, height, arithmetic, aliases]);
    for (name, part) in [
        ("header", header),
        ("height", height),
        ("arithmetic", arithmetic),
        ("aliases", aliases),
    ] {
        assert_ne!(part, [Fr::zero(); 4], "{name} family omitted");
    }
    assert_eq!(c.total(), 2_347_918);

    // The natural circuit has 13 row bits and 12 input bits; its common
    // embedding has 17 and 20. Every added factor must remain present.
    let natural_shape = sparse::validate(&c.natural, 0).unwrap();
    assert_eq!((natural_shape.row_bits, natural_shape.input_bits), (13, 12));
    let truncated =
        sparse::wiring(&c.natural, &natural_shape, &r[..13], &u[..12], &v[..12]).unwrap();
    let high = (13..17).fold(Fr::one(), |a, i| a * (Fr::one() - r[i]))
        * (12..20).fold(Fr::one(), |a, i| {
            a * (Fr::one() - u[i]) * (Fr::one() - v[i])
        });
    let padded = sparse::wiring(&c.padded, &c.shape, &r[..17], &u[..20], &v[..20]).unwrap();
    assert_eq!(padded, truncated.map(|x| x * high));
    assert_ne!(padded, truncated);

    // Every declared compact bit has its own physical alias row and owner.
    for i in 0..64 {
        let (left, right) = c.port(i);
        let mut actual = None;
        c.aliases(|edge| {
            if edge.family_row == super::ALIAS + i {
                actual = Some(edge);
            }
            Ok(())
        })
        .unwrap();
        let edge = actual.unwrap();
        assert_eq!((edge.term.gate.left, edge.term.gate.right), (left, right));
        assert_eq!(edge.source_slot, 14);
        assert_eq!(edge.family_row >> 19, 1);
        assert_eq!((edge.family_row >> 17) & 1, 1);
        assert_eq!(edge.family_row & 0x1ffff, 1152 + i);
        let row = sparse_stream_roster::global_edge_row(
            edge.source_slot,
            edge.family_row,
            4,
            19,
            1,
            &MEMBER_ROWS,
        )
        .unwrap();
        let rb = super::boolean(row, 24);
        let ub = super::boolean(left, 24);
        let vb = super::boolean(right, 24);
        assert_eq!(
            c.alias_coefficients(&rb, &ub, &vb).unwrap(),
            [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
        );
        assert_eq!(
            edge.term.gate.c0 + edge.term.gate.c1 - edge.term.gate.c2,
            Fr::from(2u64)
        );
    }

    // Full header boundaries use two physical copies; arithmetic occupies the
    // same family one with bit17=0, and both endpoint paths must visit aliases.
    for copy in [12, 13] {
        let expected_height = c.rule.heights()[copy - 12];
        let mut rb = super::boolean(
            sparse_stream_roster::global_edge_row(copy, super::HEIGHT, 4, 19, 1, &MEMBER_ROWS)
                .unwrap(),
            24,
        );
        rb[23] = Fr::one();
        let ub = super::boolean(copy * WIDTH + c.height().height_wire(0).unwrap(), 24);
        let vb = super::boolean(copy * WIDTH, 24);
        assert_eq!(
            c.parts(&rb, &ub, &vb).unwrap()[1],
            [
                -Fr::from(u64::from(expected_height) & 1),
                Fr::one(),
                Fr::zero(),
                Fr::zero()
            ]
        );
    }
    let first = c.natural.terms.first().unwrap();
    let arithmetic_row =
        sparse_stream_roster::global_edge_row(14, (1 << 19) | first.row, 4, 19, 1, &MEMBER_ROWS)
            .unwrap();
    let ar = super::boolean(arithmetic_row, 24);
    let au = super::boolean(14 * WIDTH + first.gate.left, 24);
    let av = super::boolean(14 * WIDTH + first.gate.right, 24);
    assert_ne!(
        c.arithmetic_coefficients(&ar, &au, &av).unwrap(),
        [Fr::zero(); 4]
    );
    let mut first_arithmetic = None;
    c.arithmetic(|edge| {
        first_arithmetic.get_or_insert(edge.family_row);
        Ok(())
    })
    .unwrap();
    let arithmetic_local_row = first_arithmetic.unwrap();
    assert_eq!(arithmetic_local_row >> 19, 1);
    assert_eq!((arithmetic_local_row >> 17) & 1, 0);
    for left in [true, false] {
        for copy in [12, 13, 14] {
            let mut visits = 0;
            c.visit(left, copy, |edge| {
                if edge.source_slot == 14
                    && edge.family_row >= super::ALIAS
                    && edge.family_row < super::ALIAS + 64
                {
                    visits += 1;
                }
                Ok(())
            })
            .unwrap();
            let expected = match (left, copy) {
                (true, 12 | 13) => 32,
                (false, 14) => 64,
                _ => 0,
            };
            assert_eq!(visits, expected, "left={left} copy={copy}");
        }
    }
    assert_eq!(
        c.aliases(|_| Err("sink-stop".into())).unwrap_err(),
        "sink-stop"
    );
    assert_eq!(
        c.arithmetic(|_| Err("sink-stop".into())).unwrap_err(),
        "sink-stop"
    );
    println!("Legacy singleton full24 finite references949510+64+11804+64; 64 exact aliases, both header owners, arithmetic family, endpoint enumeration and natural13/12 padding factors passed");
}

fn singleton_packed(c: &Context) -> (PackedFile, Vec<Fr>) {
    let (fixture, headers) = crate::header_history_boundary::tests::fixture();
    let serializer = serializer::build(None).unwrap();
    let (a, b) = super::super::native_pair();
    let carry = daa_integer::compile_carry(&crate::daa_count::q(), a, b, true).unwrap();
    super::super::assert_zero(&carry);
    let (parent_raw, child_raw) = singleton_raw_pair();
    let helper =
        daa_integer::compile_carry(&crate::daa_count::q(), parent_raw, child_raw, true).unwrap();
    assert!(residuals(helper.circuit.as_ref().unwrap(), &helper.witness)
        .iter()
        .all(Zero::is_zero));
    assert_eq!(helper.circuit, c.expected.circuit);
    assert_eq!(helper.parent_nbits, c.expected.parent_nbits);
    assert_eq!(helper.child_nbits, c.expected.child_nbits);
    assert_eq!(c.natural.terms, helper.circuit.as_ref().unwrap().terms);
    let path = super::super::super::super::artifact("singleton-packed", "bin");
    let mut writer = PackedFileWriter::create_new(&path, 24).unwrap();
    for copy in 0..16 {
        let mut input = if copy == 9 || copy == 10 {
            crate::header_history_boundary::tests::assignment_for_child(
                c.base.base.base.heights[copy],
                &fixture,
                &headers,
            )
        } else if copy == 12 || copy == 13 {
            singleton_assignment(c.rule.heights()[copy - 12])
        } else {
            vec![Fr::zero(); WIDTH]
        };
        if copy < 9 {
            let height = c.base.base.base.heights[copy];
            let header = ergo_header_core::Header::decode(&headers[&height], None).unwrap();
            let fields = serializer::Fields::from_header(&header).unwrap();
            let bits = serializer.assign(&fields);
            input[header_hash::SERIALIZER_OFFSET..header_hash::SERIALIZER_OFFSET + bits.len()]
                .copy_from_slice(&bits);
        } else if copy == 11 {
            input[..carry.witness.len()].copy_from_slice(&carry.witness);
        } else if copy == 14 {
            input[..helper.witness.len()].copy_from_slice(&helper.witness);
        }
        assert_eq!(input.len(), WIDTH);
        writer.write_bytes(&pack_bits(&input)).unwrap();
    }
    writer.finish().unwrap();
    let source = PackedFile::open(path, 24).unwrap();
    let fixed = super::pack_native(&Context::new().unwrap());
    for copy in (0..12).chain(std::iter::once(15)) {
        for chunk in 0..16 {
            assert_eq!(
                source.read_copy(1 << 16, copy * 16 + chunk).unwrap(),
                fixed.read_copy(1 << 16, copy * 16 + chunk).unwrap(),
                "shared carry baseline copy={copy} chunk={chunk}"
            );
        }
    }
    (source, helper.witness)
}

#[test]
fn legacy_singleton_one_fresh_common_gkr_pcs_and_single_faults() {
    let whole = Instant::now();
    let mark = Instant::now();
    let c = Context::for_rule(NumericRule::LegacySingleton).unwrap();
    let context_ms = mark.elapsed().as_millis();
    let mark = Instant::now();
    let (source, helper_witness) = singleton_packed(&c);
    let packing_ms = mark.elapsed().as_millis();
    let mut endpoint_visits = [0usize; 2];
    let mut alias = None;
    c.aliases(|edge| {
        if edge.family_row == super::ALIAS {
            alias = Some(edge);
        }
        Ok(())
    })
    .unwrap();
    let edge = alias.unwrap();
    let left_chunk = source
        .read_copy(1 << 16, edge.term.gate.left / (1 << 16))
        .unwrap();
    let right_chunk = source
        .read_copy(1 << 16, edge.term.gate.right / (1 << 16))
        .unwrap();
    let left = left_chunk[edge.term.gate.left % (1 << 16)];
    let right = right_chunk[edge.term.gate.right % (1 << 16)];
    assert_eq!(
        edge.term.gate.c0
            + edge.term.gate.c1 * left
            + edge.term.gate.c2 * right
            + edge.term.gate.c3 * left * right,
        Fr::zero(),
        "honest alias row is zero"
    );
    assert!(helper_witness
        .iter()
        .all(|x| *x == Fr::zero() || *x == Fr::one()));

    let mark = Instant::now();
    let setup = pcs::generate_setup(24).unwrap();
    let setup_ms = mark.elapsed().as_millis();
    let key = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
    let admitted = verifier_key::admit_generated_test_key(24, &key, setup.id).unwrap();
    let mark = Instant::now();
    let committed = packed::commit(&source, &setup).unwrap();
    let commitment = pcs::encode_commitment(&committed.commitment).unwrap();
    let commit_ms = mark.elapsed().as_millis();

    let mut transcript = Transcript::new(c.rule.domain());
    let mut loads = 0usize;
    let mut visits = 0usize;
    let mut passes = 0usize;
    source.reset_io_metrics();
    let mark = Instant::now();
    let (proof, claim, inc_u, inc_v) = sparse_stream_roster::prove_edge_terms(
        20,
        4,
        19,
        1,
        &MEMBER_ROWS,
        |left, copy, sink| {
            passes += 1;
            c.visit(left, copy, |edge| {
                visits += 1;
                sink(edge)
            })
        },
        |copy| {
            loads += 1;
            super::super::super::load(&source, copy)
        },
        &mut transcript,
        |t| c.bind(t, &setup.id, &commitment, &c.bound_target()),
        |r, u, v| c.coefficients(r, u, v),
    )
    .unwrap();
    let gkr_ms = mark.elapsed().as_millis();
    let io = source.io_metrics_snapshot();
    if inc_u && inc_v {
        assert_eq!(loads, 48);
        assert_eq!(passes, 64);
        assert_eq!(visits, 4 * c.total());
        assert_eq!(io.read_calls, 768);
        assert_eq!(io.read_bytes, 6_291_456);
    }

    let mark = Instant::now();
    let (verified, mut consumer) =
        super::verify_for_rule(NumericRule::LegacySingleton, &proof, &setup.id, &commitment)
            .unwrap();
    let consumer_ms = mark.elapsed().as_millis();
    assert_eq!(claim, verified);
    assert_eq!(
        transcript.clone().challenge_scalar(b"post-gkr"),
        consumer.clone().challenge_scalar(b"post-gkr")
    );
    assert_eq!(source.evaluate(&claim.point).unwrap(), claim.value);
    let pre_pcs = consumer.clone();
    let mut open_transcript = transcript.clone();
    let mark = Instant::now();
    let opening = packed::open(
        &committed,
        &source,
        &claim.point,
        &setup,
        &mut open_transcript,
    )
    .unwrap();
    let opening_ms = mark.elapsed().as_millis();
    let mark = Instant::now();
    pcs::verify_admitted(
        committed.commitment.clone(),
        claim.value,
        &claim.point,
        &opening,
        &admitted,
        &mut consumer,
    )
    .unwrap();
    let pcs_verify_ms = mark.elapsed().as_millis();
    assert_eq!(
        open_transcript.challenge_scalar(b"post-pcs"),
        consumer.challenge_scalar(b"post-pcs")
    );
    let mut wrong_value_transcript = pre_pcs;
    assert!(pcs::verify_admitted(
        committed.commitment.clone(),
        claim.value + Fr::one(),
        &claim.point,
        &opening,
        &admitted,
        &mut wrong_value_transcript,
    )
    .is_err());

    // Only the rule identity changes. The fresh consumer must reject it.
    let mut wrong_rule_transcript = Transcript::new(c.rule.domain());
    assert_eq!(
        gkr::verify_with_wiring(
            &[24],
            1 << 24,
            &proof,
            &mut wrong_rule_transcript,
            |t| {
                c.bind_with_rule_identity(
                    t,
                    &setup.id,
                    &commitment,
                    &c.bound_target(),
                    b"wrong-rule-identity",
                );
            },
            |_, r, u, v| {
                c.coefficients(r, u, v)
                    .map_err(|_| GkrError::PointDimension)
            },
        )
        .unwrap_err(),
        GkrError::SumcheckIdentity
    );

    for missing in ["one-alias", "arithmetic"] {
        let mut omitted_transcript = Transcript::new(c.rule.domain());
        let error = gkr::verify_with_wiring(
            &[24],
            1 << 24,
            &proof,
            &mut omitted_transcript,
            |t| {
                c.bind(t, &setup.id, &commitment, &c.bound_target());
            },
            |_, r, u, v| {
                let mut out = c.coefficients(r, u, v).unwrap();
                if missing == "one-alias" {
                    let (left, right) = c.port(0);
                    let row = sparse_stream_roster::global_edge_row(
                        14,
                        super::ALIAS,
                        4,
                        19,
                        1,
                        &MEMBER_ROWS,
                    )
                    .unwrap();
                    let weight = super::eq(r, row) * super::eq(u, left) * super::eq(v, right);
                    out[1] -= weight;
                    out[2] += weight;
                } else {
                    let full = c.arithmetic_coefficients(r, u, v).unwrap();
                    for i in 0..4 {
                        out[i] -= full[i];
                    }
                }
                Ok(out)
            },
        )
        .unwrap_err();
        assert_eq!(error, GkrError::TerminalExpression, "{missing}");
    }

    // Keep the alias's -1 fault identical in the left and right enumerations.
    let mut false_transcript = Transcript::new(c.rule.domain());
    let fault = sparse_stream_roster::prove_edge_terms(
        20,
        4,
        19,
        1,
        &MEMBER_ROWS,
        |left, copy, sink| {
            c.visit(left, copy, |mut edge| {
                if edge.source_slot == 14 && edge.family_row == super::ALIAS {
                    endpoint_visits[usize::from(!left)] += 1;
                    edge.term.gate.c0 = -Fr::one();
                }
                sink(edge)
            })
        },
        |copy| super::super::super::load(&source, copy),
        &mut false_transcript,
        |t| c.bind(t, &setup.id, &commitment, &c.bound_target()),
        |r, u, v| c.coefficients(r, u, v),
    );
    // The producer may replay either endpoint while forming its messages.
    // Every replay above applies the same fault to the same physical alias.
    assert!(
        endpoint_visits.iter().all(|&visits| visits >= 1),
        "fault must reach both endpoint enumerations: {endpoint_visits:?}"
    );
    assert_eq!(fault.unwrap_err(), GkrError::SumcheckIdentity.to_string());

    let proof_bytes = gkr::encode_proof(&proof).unwrap();
    let pcs_bytes = pcs::encode_proof(&opening).unwrap();
    for (kind, bytes) in [
        ("singleton-gkr", proof_bytes.as_slice()),
        ("singleton-pcs", pcs_bytes.as_slice()),
        ("singleton-test-key", key.as_slice()),
    ] {
        write_create_new(&super::super::super::super::artifact(kind, "bin"), bytes);
    }
    let receipt = serde_json::json!({
        "profile": "bounded Mainnet Legacy positive singleton at child 1025",
        "sample_heights": [1024],
        "header_1024_order_seed": "synthetic previous timestamp child_timestamp_minus_1; unauthenticated",
        "header_1025_order_seed": "previous timestamp derived from RAW header1024; adjacency not proved",
        "N": 844674,
        "slot_log": 20,
        "header_copies": [12, 13],
        "auxiliary_copy": 14,
        "unused_copy": 15,
        "terms": c.total(),
        "arithmetic_terms": c.natural.terms.len(),
        "header_terms": 949510,
        "height_terms": 64,
        "alias_terms": 64,
        "natural_input_bits": 12,
        "natural_row_bits": 13,
        "padded_input_bits": 20,
        "padded_row_bits": 17,
        "context_ms": context_ms,
        "packing_ms": packing_ms,
        "setup_ms": setup_ms,
        "commit_ms": commit_ms,
        "gkr_ms": gkr_ms,
        "consumer_ms": consumer_ms,
        "opening_ms": opening_ms,
        "pcs_verify_ms": pcs_verify_ms,
        "whole_ms": whole.elapsed().as_millis(),
        "loader_calls": loads,
        "endpoint_passes": passes,
        "term_visits": visits,
        "packed_reads": io.read_calls,
        "packed_read_bytes": io.read_bytes,
        "incremental_u": inc_u,
        "incremental_v": inc_v,
        "gkr_bytes": proof_bytes.len(),
        "pcs_bytes": pcs_bytes.len(),
        "setup_id": setup.id.iter().map(|b| format!("{b:02x}")).collect::<String>(),
        "authority_ceiling": "selected Legacy singleton numeric join only; no chain ancestry, history/hash authentication, global DAA, full historical runtime, or production claim"
    });
    println!("{receipt}");
    write_create_new(
        &super::super::super::super::artifact("singleton-receipt", "json"),
        receipt.to_string().as_bytes(),
    );
}

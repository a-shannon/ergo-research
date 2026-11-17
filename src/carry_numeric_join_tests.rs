//! A bounded native carry pair in the common GKR/PCS commitment.
use super::{Context as Base, CHUNK, MEMBER_ROWS, N, WIDTH};
use crate::{
    daa_integer::{self, CompiledCarry},
    gkr::{self, GkrProof, InputClaim},
    header_hash,
    packed::{self, PackedFile, PackedFileWriter},
    pcs, serializer,
    sparse::{self, Circuit, Term},
    sparse_stream_roster::{self, EdgeTerm},
    transcript::Transcript,
    verifier_key,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
use num_bigint::BigUint;
use std::time::Instant;
const AUX: usize = 11;
const ARITH: usize = 1 << 19;
const ALIAS: usize = (1 << 19) | (1 << 17) | 1088;
const DOMAIN: &[u8] = b"native-common-numeric-carry-v1";
fn eq(p: &[Fr], i: usize) -> Fr {
    super::eq(p, i)
}
fn boolean(i: usize, bits: usize) -> Vec<Fr> {
    super::boolean(i, bits)
}
fn global_row(edge: &EdgeTerm) -> Result<usize, String> {
    sparse_stream_roster::global_edge_row(edge.source_slot, edge.family_row, 4, 19, 1, &MEMBER_ROWS)
}
struct Context {
    base: Base,
    expected: CompiledCarry,
    padded: Circuit,
    shape: sparse::Shape,
    header_raw: [usize; 32],
}
impl Context {
    fn new() -> Result<Self, String> {
        let base = Base::new()?;
        if base.base.heights[9] != 844_673
            || base.base.heights[10] != 844_674
            || crate::daa_header_window::for_child_height(844_674)?.action()
                != crate::daa_header_window::Action::Carry
        {
            return Err("numeric carry logical pair changed".into());
        }
        let expected =
            daa_integer::compile_carry(&crate::daa_count::q(), 0x03000001, 0x03000001, true)?;
        let actual = expected
            .circuit
            .as_ref()
            .ok_or("missing expected carry circuit")?;
        let padded = Circuit {
            input_len: WIDTH,
            row_count: 1 << 17,
            terms: actual.terms.clone(),
        };
        let shape = sparse::validate(&padded, 0).map_err(|e| e.to_string())?;
        if shape.input_bits != 20 || shape.row_bits != 17 {
            return Err("carry padded shape changed".into());
        }
        let serializer = serializer::build(None)?;
        let header_raw = serializer
            .layout
            .fields
            .n_bits
            .map(|w| header_hash::SERIALIZER_OFFSET + w);
        if header_raw.iter().any(|w| *w >= WIDTH) {
            return Err("carry header raw escaped copy".into());
        }
        Ok(Self {
            base,
            expected,
            padded,
            shape,
            header_raw,
        })
    }
    fn total(&self) -> usize {
        super::TOTAL + self.expected.count.terms + 64
    }
    fn bind(&self, t: &mut Transcript, key: &[u8; 32], commitment: &[u8], alias_count: u64) {
        self.base.bind(t, key, commitment, 11);
        t.append_bytes(b"carry-profile", DOMAIN);
        t.append_bytes(b"carry-action", b"native-decoded-equality");
        t.append_bytes(b"carry-Q", &crate::daa_count::q().to_bytes_be());
        t.append_bytes(b"carry-topology", &self.expected.count.topology_blake2b256);
        for (label, v) in [
            (b"carry-parent-height".as_slice(), 844_673),
            (b"carry-child-height", 844_674),
            (b"carry-auxiliary-copy", AUX as u64),
            (b"carry-alias-count", alias_count),
            (b"carry-alias-start", ALIAS as u64),
            (b"carry-arithmetic-start", ARITH as u64),
            (
                b"carry-natural-input",
                self.expected.count.padded_input_bits as u64,
            ),
            (
                b"carry-natural-rows",
                self.expected.count.padded_rows as u64,
            ),
            (
                b"carry-residual-rows",
                self.expected.count.residual_rows as u64,
            ),
            (b"carry-padded-input", WIDTH as u64),
            (b"carry-padded-rows", 1 << 17),
            (b"carry-terms", self.expected.count.terms as u64),
            (b"carry-total", self.total() as u64),
        ] {
            t.append_u64(label, v);
        }
        for (&header, (&parent, &child)) in self.header_raw.iter().zip(
            self.expected
                .parent_nbits
                .iter()
                .zip(&self.expected.child_nbits),
        ) {
            t.append_u64(b"carry-header-port", header as u64);
            t.append_u64(b"carry-parent-port", parent as u64);
            t.append_u64(b"carry-child-port", child as u64);
        }
    }
    fn port(&self, i: usize) -> (usize, usize) {
        assert!(i < 64);
        let source_copy = if i < 32 { 9 } else { 10 };
        let bit = i % 32;
        let raw = if i < 32 {
            self.expected.parent_nbits[bit]
        } else {
            self.expected.child_nbits[bit]
        };
        (
            source_copy * WIDTH + self.header_raw[bit],
            AUX * WIDTH + raw,
        )
    }
    fn aliases(&self, mut sink: impl FnMut(EdgeTerm) -> Result<(), String>) -> Result<(), String> {
        for i in 0..64 {
            let (left, right) = self.port(i);
            let row = ALIAS + i;
            sink(EdgeTerm {
                source_slot: AUX,
                family_row: row,
                term: Term {
                    row,
                    gate: gkr::Gate {
                        left,
                        right,
                        c0: Fr::zero(),
                        c1: Fr::one(),
                        c2: -Fr::one(),
                        c3: Fr::zero(),
                    },
                },
            })?;
        }
        Ok(())
    }
    fn arithmetic(
        &self,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        for source in &self.padded.terms {
            let row = ARITH + source.row;
            let mut term = source.clone();
            term.row = row;
            term.gate.left += AUX * WIDTH;
            term.gate.right += AUX * WIDTH;
            sink(EdgeTerm {
                source_slot: AUX,
                family_row: row,
                term,
            })?;
        }
        Ok(())
    }
    fn visit(
        &self,
        left: bool,
        copy: usize,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        self.base.visit(left, copy, &mut sink)?;
        if copy == AUX {
            self.arithmetic(&mut sink)?;
        }
        self.aliases(|edge| {
            let wire = if left {
                edge.term.gate.left
            } else {
                edge.term.gate.right
            };
            if wire / WIDTH == copy {
                sink(edge)?;
            }
            Ok(())
        })
    }
    fn arithmetic_coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != 24 || u.len() != 24 || v.len() != 24 {
            return Err("carry common dimensions".into());
        }
        let mask = r[23]
            * (Fr::one() - r[22])
            * (Fr::one() - r[17])
            * eq(&r[18..22], AUX)
            * eq(&u[20..], AUX)
            * eq(&v[20..], AUX);
        let local = sparse::wiring(&self.padded, &self.shape, &r[..17], &u[..20], &v[..20])
            .map_err(|e| e.to_string())?;
        Ok(local.map(|c| c * mask))
    }
    fn alias_coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != 24 || u.len() != 24 || v.len() != 24 {
            return Err("carry alias dimensions".into());
        }
        let mask = r[23]
            * (Fr::one() - r[22])
            * r[17]
            * r[10]
            * r[6]
            * (7..10)
                .chain(11..17)
                .fold(Fr::one(), |a, i| a * (Fr::one() - r[i]))
            * eq(&r[18..22], AUX);
        let mut weight = Fr::zero();
        for i in 0..64 {
            let (left, right) = self.port(i);
            weight += eq(&r[..6], i) * eq(u, left) * eq(v, right);
        }
        Ok([Fr::zero(), mask * weight, -mask * weight, Fr::zero()])
    }
    fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let old = self.base.coefficients(r, u, v)?;
        let a = self.arithmetic_coefficients(r, u, v)?;
        let b = self.alias_coefficients(r, u, v)?;
        Ok(std::array::from_fn(|i| old[i] + a[i] + b[i]))
    }
}
fn residuals(c: &CompiledCarry) -> Vec<Fr> {
    let circuit = c.circuit.as_ref().unwrap();
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms {
        rows[term.row] += term.gate.evaluate(&c.witness);
    }
    rows
}
fn assert_zero(c: &CompiledCarry) {
    assert!(residuals(c).iter().all(Zero::is_zero));
}
// Byte-oriented MPI model of the pinned Scala decoder, independent of shifts.
fn mpi(raw: u32) -> (bool, BigUint) {
    let size = (raw >> 24) as usize;
    let mut bytes = vec![0u8; size];
    for (i, shift) in [16, 8, 0].into_iter().enumerate().take(size) {
        bytes[i] = (raw >> shift) as u8;
    }
    let negative = !bytes.is_empty() && bytes[0] & 0x80 != 0;
    if !bytes.is_empty() {
        bytes[0] &= 0x7f;
    }
    (negative, BigUint::from_bytes_be(&bytes))
}
fn read_word(c: &CompiledCarry) -> BigUint {
    c.decoded
        .iter()
        .enumerate()
        .fold(BigUint::zero(), |n, (i, &w)| {
            n + if c.witness[w] == Fr::one() {
                BigUint::one() << i
            } else {
                BigUint::zero()
            }
        })
}
fn native_pair() -> (u32, u32) {
    let (_, headers) = crate::header_history_boundary::tests::fixture();
    let a = ergo_header_core::Header::decode(&headers[&844_673], None).unwrap();
    let b = ergo_header_core::Header::decode(&headers[&844_674], None).unwrap();
    (
        serializer::Fields::from_header(&a).unwrap().n_bits,
        serializer::Fields::from_header(&b).unwrap().n_bits,
    )
}

#[test]
fn carry_decoders_match_native_numeric_aliases_and_isolated_constraints() {
    let q = crate::daa_count::q();
    let fixed = daa_integer::compile_carry(&q, 0x03000001, 0x03000001, true).unwrap();
    for parent in [0x03000001, 0x01010000, 0x0101ffff] {
        for child in [0x03000001, 0x01010000, 0x0101ffff] {
            let c = daa_integer::compile_carry(&q, parent, child, true).unwrap();
            assert_zero(&c);
            assert_eq!(mpi(parent), (false, BigUint::one()));
            assert_eq!(
                crate::work_tree_work::native_decode(child).unwrap(),
                BigUint::one()
            );
            assert_eq!(read_word(&c), BigUint::one());
            assert_eq!(c.circuit, fixed.circuit);
            assert_eq!(c.count.topology_blake2b256, fixed.count.topology_blake2b256);
            assert_eq!(c.parent_nbits, fixed.parent_nbits);
            assert_eq!(c.child_nbits, fixed.child_nbits);
        }
    }
    let (parent, child) = native_pair();
    let native = daa_integer::compile_carry(&q, parent, child, true).unwrap();
    assert_zero(&native);
    assert_eq!(mpi(parent), mpi(child));
    assert_eq!(read_word(&native), mpi(parent).1);
    assert_eq!(native.circuit, fixed.circuit);
    assert_eq!(native.count.source_nbits_bits, 64);
    assert_eq!(native.count.decoded_bits, 256);
    assert_eq!(native.count.source_timestamp_bits, 0);
    assert_eq!(native.count.maximum_column_signed_abs_bits, 6);
    for wire in native
        .parent_nbits
        .into_iter()
        .chain(native.child_nbits)
        .chain(native.decoded.iter().copied())
    {
        let mut c = daa_integer::compile_carry(&q, parent, child, true).unwrap();
        c.witness[wire] = Fr::one() - c.witness[wire];
        assert!(
            residuals(&c).iter().any(|r| !r.is_zero()),
            "single actual bit {wire}"
        );
    }
    let mut c = daa_integer::compile_carry(&q, parent, child, true).unwrap();
    c.witness[c.child_nbits[0]] = Fr::from(2u64);
    let boolean_row = c
        .circuit
        .as_ref()
        .unwrap()
        .terms
        .iter()
        .find(|t| {
            t.gate.left == c.child_nbits[0]
                && t.gate.right == c.child_nbits[0]
                && t.gate.c3 == Fr::one()
        })
        .unwrap()
        .row;
    assert_eq!(residuals(&c)[boolean_row], Fr::from(2u64));
    // Numeric mismatch: one low mantissa bit differs; only child's decoder fails.
    let mismatch = daa_integer::compile_carry(&q, 0x03000001, 0x03000003, true).unwrap();
    let failed = residuals(&mismatch)
        .iter()
        .enumerate()
        .filter(|(_, x)| !x.is_zero())
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    assert_eq!(failed.len(), 1);
    assert!(mismatch.decoder_rows[1].contains(&failed[0]));
    let max = (BigUint::one() << 256usize) - BigUint::one();
    for raw in [
        0x01010000, 0x02000100, 0x03000001, 0x207fffff, 0x2100ffff, 0x22000080,
    ] {
        let good = daa_integer::compile_carry(&max, raw, raw, true).unwrap();
        assert_zero(&good);
        assert_eq!(read_word(&good), mpi(raw).1);
    }
    // Each fixture below has precisely one named failed row in each decoder.
    for (raw, bound, cause) in [
        (0x03800001, max.clone(), "sign"),
        (0x03000000, max.clone(), "nonzero"),
        (
            0x22000101,
            max.clone(),
            "overflow at bit256 with positive low bit248",
        ),
        (0x03000002, BigUint::one(), "final Q borrow"),
    ] {
        let bad = daa_integer::compile_carry(&bound, raw, raw, true).unwrap();
        let failed = residuals(&bad)
            .iter()
            .enumerate()
            .filter(|(_, x)| !x.is_zero())
            .map(|(i, _)| i)
            .collect::<Vec<_>>();
        assert_eq!(failed.len(), 2, "{cause}");
        assert!(bad.decoder_rows[0].contains(&failed[0]));
        assert!(bad.decoder_rows[1].contains(&failed[1]));
    }
    // An out-of-domain exponent also forces zero; do not mislabel that rejection
    // as single-cause. Isolate the domain gate separately on a valid witness.
    let invalid = daa_integer::compile_carry(&max, 0x23000001, 0x23000001, true).unwrap();
    assert!(residuals(&invalid).iter().any(|r| !r.is_zero()));
    let mut domain = daa_integer::compile_carry(&max, 0x03000001, 0x03000001, true).unwrap();
    let circuit = domain.circuit.as_mut().unwrap();
    let onehot = circuit
        .terms
        .iter()
        .filter(|t| domain.decoder_rows[0].contains(&t.row) && t.gate.c0 == -Fr::one())
        .find(|t| {
            circuit
                .terms
                .iter()
                .filter(|other| other.row == t.row)
                .count()
                == 35
        })
        .unwrap()
        .row;
    circuit
        .terms
        .iter_mut()
        .find(|t| t.row == onehot && t.gate.c0 == -Fr::one())
        .unwrap()
        .gate
        .c0 = -Fr::from(2u64);
    let failed = residuals(&domain)
        .iter()
        .enumerate()
        .filter(|(_, x)| !x.is_zero())
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    assert_eq!(failed, vec![onehot]);
    assert!(daa_integer::compile_carry(&BigUint::zero(), 1, 1, true).is_err());
    assert!(daa_integer::compile_carry(&(BigUint::one() << 256usize), 1, 1, true).is_err());
    println!("carry native parent={parent:08x} child={child:08x} input={} rows={} residual_rows={} terms={} raw64/shared256 aliases9 single-bit320; sign/nonzero/overflow/Q rows isolated; exponent domain gate isolated",native.count.padded_input_bits,native.count.padded_rows,native.count.residual_rows,native.count.terms);
}

fn finite(
    mut visit: impl FnMut(&mut dyn FnMut(EdgeTerm) -> Result<(), String>) -> Result<(), String>,
    r: &[Fr],
    u: &[Fr],
    v: &[Fr],
) -> ([Fr; 4], usize) {
    let mut out = [Fr::zero(); 4];
    let mut count = 0;
    visit(&mut |edge| {
        let weight =
            eq(r, global_row(&edge)?) * eq(u, edge.term.gate.left) * eq(v, edge.term.gate.right);
        for (a, c) in out.iter_mut().zip([
            edge.term.gate.c0,
            edge.term.gate.c1,
            edge.term.gate.c2,
            edge.term.gate.c3,
        ]) {
            *a += weight * c;
        }
        count += 1;
        Ok(())
    })
    .unwrap();
    (out, count)
}

#[test]
fn carry_padded_arithmetic_and_64_aliases_match_independent_full_domain() {
    let c = Context::new().unwrap();
    let r = (0..24)
        .map(|i| Fr::from((11 + i * 7) as u64))
        .collect::<Vec<_>>();
    let u = (0..24)
        .map(|i| Fr::from((23 + i * 13) as u64))
        .collect::<Vec<_>>();
    let v = (0..24)
        .map(|i| Fr::from((31 + i * 17) as u64))
        .collect::<Vec<_>>();
    let (arithmetic, terms) = finite(|sink| c.arithmetic(sink), &r, &u, &v);
    let (aliases, n) = finite(|sink| c.aliases(sink), &r, &u, &v);
    assert_eq!(terms, c.expected.count.terms);
    assert_eq!(n, 64);
    assert_eq!(c.arithmetic_coefficients(&r, &u, &v).unwrap(), arithmetic);
    assert_eq!(c.alias_coefficients(&r, &u, &v).unwrap(), aliases);
    assert_ne!(arithmetic, [Fr::zero(); 4]);
    assert_ne!(aliases, [Fr::zero(); 4]);
    let natural = c.expected.circuit.as_ref().unwrap();
    let shape = sparse::validate(natural, 0).unwrap();
    assert!(shape.input_bits < 20 && shape.row_bits < 17);
    let truncated = sparse::wiring(
        natural,
        &shape,
        &r[..shape.row_bits],
        &u[..shape.input_bits],
        &v[..shape.input_bits],
    )
    .unwrap();
    let padded = sparse::wiring(&c.padded, &c.shape, &r[..17], &u[..20], &v[..20]).unwrap();
    let high = (shape.row_bits..17).fold(Fr::one(), |a, i| a * (Fr::one() - r[i]))
        * (shape.input_bits..20).fold(Fr::one(), |a, i| {
            a * (Fr::one() - u[i]) * (Fr::one() - v[i])
        });
    assert_eq!(padded, truncated.map(|x| x * high));
    assert_ne!(padded, truncated, "omitted high-zero factors");
    for i in 0..64 {
        let (left, right) = c.port(i);
        let mut actual = None;
        c.aliases(|e| {
            if e.family_row == ALIAS + i {
                actual = Some(e);
            }
            Ok(())
        })
        .unwrap();
        let edge = actual.unwrap();
        assert_eq!((edge.term.gate.left, edge.term.gate.right), (left, right));
        let row = global_row(&edge).unwrap();
        let rb = boolean(row, 24);
        let ub = boolean(left, 24);
        let vb = boolean(right, 24);
        let expected = [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()];
        assert_eq!(c.alias_coefficients(&rb, &ub, &vb).unwrap(), expected);
        for bit in [6, 10, 17, 18, 22, 23] {
            let mut wrong = rb.clone();
            wrong[bit] = Fr::one() - wrong[bit];
            assert_eq!(
                c.alias_coefficients(&wrong, &ub, &vb).unwrap(),
                [Fr::zero(); 4],
                "row bit{bit}"
            );
        }
        for wrong in [left ^ 1, left ^ WIDTH] {
            assert_eq!(
                c.alias_coefficients(&rb, &boolean(wrong, 24), &vb).unwrap(),
                [Fr::zero(); 4]
            );
        }
        for wrong in [right ^ 1, right ^ WIDTH] {
            assert_eq!(
                c.alias_coefficients(&rb, &ub, &boolean(wrong, 24)).unwrap(),
                [Fr::zero(); 4]
            );
        }
        let weight = eq(&r, row) * eq(&u, left) * eq(&v, right);
        assert_ne!(
            [
                aliases[0],
                aliases[1] - weight,
                aliases[2] + weight,
                aliases[3]
            ],
            aliases,
            "one alias omitted"
        );
        assert!(edge.family_row >= ALIAS && edge.family_row < ALIAS + 64);
        assert!(edge.family_row > super::HEIGHT_START + 31);
    }
    let first = &c.padded.terms[0];
    let edge = EdgeTerm {
        source_slot: AUX,
        family_row: ARITH + first.row,
        term: first.clone(),
    };
    let row = global_row(&edge).unwrap();
    let rb = boolean(row, 24);
    let ub = boolean(AUX * WIDTH + first.gate.left, 24);
    let vb = boolean(AUX * WIDTH + first.gate.right, 24);
    assert_ne!(
        c.arithmetic_coefficients(&rb, &ub, &vb).unwrap(),
        [Fr::zero(); 4]
    );
    for bit in [17, 18, 22, 23] {
        let mut wrong = rb.clone();
        wrong[bit] = Fr::one() - wrong[bit];
        assert_eq!(
            c.arithmetic_coefficients(&wrong, &ub, &vb).unwrap(),
            [Fr::zero(); 4]
        );
    }
    assert!(c.arithmetic_coefficients(&r[..23], &u, &v).is_err());
    assert!(c.alias_coefficients(&r, &u[..23], &v).is_err());
    assert_eq!(
        c.aliases(|_| Err("sink-stop".into())).unwrap_err(),
        "sink-stop"
    );
    assert_eq!(
        c.arithmetic(|_| Err("sink-stop".into())).unwrap_err(),
        "sink-stop"
    );
    println!("carry padded input20/row17: {terms} arithmetic +64 aliases; all4 coefficients, full-domain high factors,64 actual ports, owners/regions/padding/endpoints/sink passed");
}

fn pack_native(c: &Context) -> PackedFile {
    let (fixture, headers) = crate::header_history_boundary::tests::fixture();
    let serializer = serializer::build(None).unwrap();
    let (parent, child) = native_pair();
    let helper = daa_integer::compile_carry(&crate::daa_count::q(), parent, child, true).unwrap();
    assert_zero(&helper);
    assert_eq!(helper.circuit, c.expected.circuit);
    assert_eq!(
        helper.count.topology_blake2b256,
        c.expected.count.topology_blake2b256
    );
    assert_eq!(helper.parent_nbits, c.expected.parent_nbits);
    assert_eq!(helper.child_nbits, c.expected.child_nbits);
    let path = super::super::artifact("carry-packed", "bin");
    let mut writer = PackedFileWriter::create_new(&path, 24).unwrap();
    for copy in 0..16 {
        let mut input = if copy == 9 || copy == 10 {
            crate::header_history_boundary::tests::assignment_for_child(
                c.base.base.heights[copy],
                &fixture,
                &headers,
            )
        } else {
            vec![Fr::zero(); WIDTH]
        };
        if copy < 9 {
            let header =
                ergo_header_core::Header::decode(&headers[&c.base.base.heights[copy]], None)
                    .unwrap();
            let assignment = serializer.assign(&serializer::Fields::from_header(&header).unwrap());
            input
                [header_hash::SERIALIZER_OFFSET..header_hash::SERIALIZER_OFFSET + assignment.len()]
                .copy_from_slice(&assignment);
        } else if copy == AUX {
            assert!(helper.witness.len() <= WIDTH);
            input[..helper.witness.len()].copy_from_slice(&helper.witness);
        }
        assert_eq!(input.len(), WIDTH);
        writer
            .write_bytes(&super::super::super::pack_bits(&input))
            .unwrap();
    }
    writer.finish().unwrap()
}
fn verify(
    proof: &GkrProof,
    key: &[u8; 32],
    commitment: &[u8],
) -> Result<(InputClaim, Transcript), String> {
    let expected = Context::new()?;
    let mut t = Transcript::new(DOMAIN);
    let claim = gkr::verify_with_wiring(
        &[24],
        1 << 24,
        proof,
        &mut t,
        |t| expected.bind(t, key, commitment, 64),
        |_, r, u, v| {
            expected
                .coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        },
    )
    .map_err(|e| e.to_string())?;
    Ok((claim, t))
}

#[test]
fn native_common_carry_one_gkr_pcs_and_single_alias_fault() {
    let whole = Instant::now();
    let mark = Instant::now();
    let c = Context::new().unwrap();
    let context_ms = mark.elapsed().as_millis();
    let mark = Instant::now();
    let source = pack_native(&c);
    let packing_ms = mark.elapsed().as_millis();
    let mark = Instant::now();
    let setup = pcs::generate_setup(24).unwrap();
    let setup_ms = mark.elapsed().as_millis();
    let key = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone())).unwrap();
    let admitted = verifier_key::admit_generated_test_key(24, &key, setup.id).unwrap();
    let mark = Instant::now();
    let committed = packed::commit(&source, &setup).unwrap();
    let commit_ms = mark.elapsed().as_millis();
    let commitment = pcs::encode_commitment(&committed.commitment).unwrap();
    let mut t = Transcript::new(DOMAIN);
    let mut loads = 0;
    let mut visits = 0;
    let mut passes = 0;
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
            super::load(&source, copy)
        },
        &mut t,
        |t| c.bind(t, &setup.id, &commitment, 64),
        |r, u, v| c.coefficients(r, u, v),
    )
    .unwrap();
    let gkr_ms = mark.elapsed().as_millis();
    let io = source.io_metrics_snapshot();
    assert_eq!(loads, 48);
    assert_eq!(passes, 64);
    assert_eq!(visits, 4 * c.total());
    assert_eq!(io.read_calls, 768);
    assert_eq!(io.read_bytes, 6291456);
    assert!(inc_u && inc_v);
    let mark = Instant::now();
    let (verified, mut consumer) = verify(&proof, &setup.id, &commitment).unwrap();
    let consumer_ms = mark.elapsed().as_millis();
    assert_eq!(claim, verified);
    assert_eq!(
        t.clone().challenge_scalar(b"post-gkr"),
        consumer.clone().challenge_scalar(b"post-gkr")
    );
    let mark = Instant::now();
    assert_eq!(source.evaluate(&claim.point).unwrap(), claim.value);
    let mle_ms = mark.elapsed().as_millis();
    let pre_pcs = consumer.clone();
    let mut opening_t = t.clone();
    let mark = Instant::now();
    let opening = packed::open(&committed, &source, &claim.point, &setup, &mut opening_t).unwrap();
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
        opening_t.challenge_scalar(b"post-pcs"),
        consumer.challenge_scalar(b"post-pcs")
    );
    let mut wrong = pre_pcs;
    assert!(pcs::verify_admitted(
        committed.commitment.clone(),
        claim.value + Fr::one(),
        &claim.point,
        &opening,
        &admitted,
        &mut wrong
    )
    .is_err());
    for missing in ["arithmetic", "one-alias"] {
        let mut omitted = Transcript::new(DOMAIN);
        let err = gkr::verify_with_wiring(
            &[24],
            1 << 24,
            &proof,
            &mut omitted,
            |t| c.bind(t, &setup.id, &commitment, 64),
            |_, r, u, v| {
                let mut value = c.coefficients(r, u, v).unwrap();
                if missing == "arithmetic" {
                    let local = c.arithmetic_coefficients(r, u, v).unwrap();
                    for i in 0..4 {
                        value[i] -= local[i];
                    }
                } else {
                    let (left, right) = c.port(0);
                    let edge = EdgeTerm {
                        source_slot: AUX,
                        family_row: ALIAS,
                        term: Term {
                            row: ALIAS,
                            gate: gkr::Gate {
                                left,
                                right,
                                c0: Fr::zero(),
                                c1: Fr::one(),
                                c2: -Fr::one(),
                                c3: Fr::zero(),
                            },
                        },
                    };
                    let w = eq(r, global_row(&edge).unwrap()) * eq(u, left) * eq(v, right);
                    value[1] -= w;
                    value[2] += w;
                }
                Ok(value)
            },
        )
        .unwrap_err();
        assert_eq!(err, gkr::GkrError::TerminalExpression, "{missing}");
    }
    let mut wrong_context = Transcript::new(DOMAIN);
    assert_eq!(
        gkr::verify_with_wiring(
            &[24],
            1 << 24,
            &proof,
            &mut wrong_context,
            |t| c.bind(t, &setup.id, &commitment, 63),
            |_, r, u, v| c
                .coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        )
        .unwrap_err(),
        gkr::GkrError::SumcheckIdentity
    );
    let mut causal = None;
    c.aliases(|e| {
        if e.family_row == ALIAS {
            causal = Some(e);
        }
        Ok(())
    })
    .unwrap();
    let causal = causal.unwrap();
    let x = source
        .read_copy(CHUNK, causal.term.gate.left / CHUNK)
        .unwrap()[causal.term.gate.left % CHUNK];
    let y = source
        .read_copy(CHUNK, causal.term.gate.right / CHUNK)
        .unwrap()[causal.term.gate.right % CHUNK];
    assert!(causal.term.gate.c0.is_zero());
    assert_eq!(causal.term.gate.c1, Fr::one());
    assert_eq!(causal.term.gate.c2, -Fr::one());
    assert!(causal.term.gate.c3.is_zero());
    assert_eq!(x, y);
    assert!((x - y).is_zero());
    assert_eq!(-Fr::one() + x - y, -Fr::one());
    let mut false_t = Transcript::new(DOMAIN);
    let false_edge = sparse_stream_roster::prove_edge_terms(
        20,
        4,
        19,
        1,
        &MEMBER_ROWS,
        |left, copy, sink| {
            c.visit(left, copy, |mut e| {
                if e.source_slot == AUX && e.family_row == ALIAS {
                    e.term.gate.c0 = -Fr::one();
                }
                sink(e)
            })
        },
        |copy| super::load(&source, copy),
        &mut false_t,
        |t| c.bind(t, &setup.id, &commitment, 64),
        |r, u, v| c.coefficients(r, u, v),
    );
    assert_eq!(
        false_edge.unwrap_err(),
        gkr::GkrError::SumcheckIdentity.to_string()
    );
    let proof_bytes = gkr::encode_proof(&proof).unwrap();
    let pcs_bytes = pcs::encode_proof(&opening).unwrap();
    for (kind, bytes) in [
        ("carry-gkr", proof_bytes.as_slice()),
        ("carry-pcs", pcs_bytes.as_slice()),
        ("carry-test-key", key.as_slice()),
    ] {
        super::super::super::write_create_new(&super::super::artifact(kind, "bin"), bytes);
    }
    let receipt = serde_json::json!({"profile":"bounded common native numeric carry","N":N,"terms":c.total(),"carry_terms":c.expected.count.terms,"carry_natural_input":c.expected.count.padded_input_bits,"carry_natural_rows":c.expected.count.padded_rows,"carry_residual_rows":c.expected.count.residual_rows,"carry_fingerprint":c.expected.count.topology_blake2b256.iter().map(|b|format!("{b:02x}")).collect::<String>(),"source_bits":64,"shared_decoded_bits":256,"aliases":64,"auxiliary_copy":11,"historical_header_copies":11,"input_bits":24,"row_bits":24,"context_ms":context_ms,"packing_ms":packing_ms,"setup_ms":setup_ms,"commit_ms":commit_ms,"gkr_ms":gkr_ms,"full_consumer_ms":consumer_ms,"mle_ms":mle_ms,"opening_ms":opening_ms,"pcs_verify_ms":pcs_verify_ms,"whole_ms":whole.elapsed().as_millis(),"loader_calls":loads,"endpoint_passes":passes,"term_visits":visits,"packed_reads":io.read_calls,"packed_read_bytes":io.read_bytes,"incremental_u":inc_u,"incremental_v":inc_v,"gkr_bytes":proof_bytes.len(),"pcs_bytes":pcs_bytes.len(),"setup_id":setup.id.iter().map(|b|format!("{b:02x}")).collect::<String>(),"authority_ceiling":"selected numeric carry pair only; global carry/history authentication/hash/time adjacency/fullchain/final parameters not proven"});
    println!("{receipt}");
    super::super::super::write_create_new(
        &super::super::artifact("carry-receipt", "json"),
        receipt.to_string().as_bytes(),
    );
}

#[path = "fixed_v2_join_tests.rs"]
mod fixed_v2_join_tests;

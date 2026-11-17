//! Bounded, test-only differential for one retained serializer MUX block.
//! The four packets are a sparse diagnostic domain, not a historical witness.
use super::*;
use crate::{
    daa_history_layout,
    daa_history_roster::{DaaHistoryRoster, OwnerClass},
    daa_integer::Epoch,
    gkr::Gate,
    h21_scheduled_max_cap::{Plan as Scheduled, Writer},
    header_daa_row_placement::{Relation, RowPlan},
    header_scheduled_retirement::Merge,
    serializer,
    sparse::Term,
    work_tree_history_plan::WorkTreeHistoryPlan,
};
use blake2::{digest::consts::U32, Blake2b, Digest};
use std::collections::BTreeMap;

mod c335_phase_b_pilot;

const WIDTH: usize = 1 << 20;
const ROWS: usize = 1 << 19;
const SOURCE_BASE_7238: usize = 49_548;
const SOURCE_END_7348: usize = 52_188;
const SOURCE_FIRST_7340: usize = 51_996;
const PACKED_WORDS_P01: [usize; 7] = [8374, 8509, 8510, 8511, 8512, 8552, 8553];
const BANKS: [(usize, usize); 3] = [(547_360, 0), (544_716, 3), (544_588, 3)];
const OWNERS: [usize; 4] = [843_776, 845_759, 1_048_576, 1_827_840];
const LOCAL_ROW: usize = 20_176;

#[derive(Clone)]
struct Slice {
    /// Already attached to the HEADER slot, but not yet copied to an owner.
    attached: Vec<Term>,
}

fn expected(k: usize, bit: usize, role: usize) -> Term {
    assert!(k < 8 && bit < 8 && role < 3);
    let coefficient = Fr::from(1u64 << bit);
    let (left, right, c1, c3) = match role {
        0 => (547_360 + 8 * k + bit, 524_288, coefficient, Fr::zero()),
        1 => (544_719 + 8 * k + bit, 535_974, -coefficient, coefficient),
        _ => (544_591 + 8 * k + bit, 535_974, Fr::zero(), -coefficient),
    };
    Term {
        row: LOCAL_ROW + k,
        gate: Gate { left, right, c0: Fr::zero(), c1, c2: Fr::zero(), c3 },
    }
}

fn trace_gate(source: &serializer::Compiled) {
    let trace = &source.c334_mux_trace;
    assert_eq!(trace.base_7238, SOURCE_BASE_7238, "independent source-prefix ordinal pin");
    assert_eq!(trace.end_7348, SOURCE_END_7348, "independent source-prefix end pin");
    assert!(trace.arities_7238_to_7347.iter().all(|&count| count == 24),
        "all 110 intervening source rows must emit 24 ordered terms");
    assert_eq!(trace.base_7238 + 102 * 24, SOURCE_FIRST_7340);
    assert_eq!(trace.base_7238 + 110 * 24, trace.end_7348);
}

#[test]
fn c334_source_counter_calibration() {
    // This test deliberately never reads Circuit.terms. It confirms the
    // independently derived ordinal pin using Builder's emission side counter.
    let source = serializer::build(None).expect("source serializer");
    trace_gate(&source);
    println!("C334_SOURCE_COUNTER base_7238={} arities_7238_to_7347=110x24 end_7348={}",
        source.c334_mux_trace.base_7238, source.c334_mux_trace.end_7348);
}

fn qualify() -> Slice {
    let source = serializer::build(None).expect("source serializer");
    // The independent numeric/arity gate MUST precede the canonical vector.
    trace_gate(&source);
    for k in 0..8 {
        for bit in 0..8 {
            for role in 0..3 {
                let ordinal = SOURCE_BASE_7238 + 24 * (102 + k) + 3 * bit + role;
                let mut wanted = expected(k, bit, role);
                wanted.row = 7340 + k;
                wanted.gate.left -= 524_288;
                wanted.gate.right -= 524_288;
                assert_eq!(source.circuit.terms.get(ordinal), Some(&wanted),
                    "ordered serializer source tuple k={k} bit={bit} role={role} ordinal={ordinal}");
            }
        }
    }
    let joined = daa_history_layout::full_header_boundary(None).expect("canonical attached HEADER");
    let terms = &joined.base.base.base.boundary.terms;
    let mut attached = Vec::with_capacity(192);
    for k in 0..8 {
        let q = LOCAL_ROW + k;
        let start = terms.partition_point(|term| term.row < q);
        let end = terms.partition_point(|term| term.row <= q);
        assert_eq!(end - start, 24, "attached byte row {q} term count");
        for bit in 0..8 {
            for role in 0..3 {
                let wanted = expected(k, bit, role);
                assert_eq!(terms.get(start + 3 * bit + role), Some(&wanted),
                    "ordered attached HEADER tuple k={k} bit={bit} role={role}");
                attached.push(wanted);
            }
        }
    }
    assert_eq!(attached.len(), 192);
    Slice { attached }
}

fn packet(owner: usize) -> Vec<u8> {
    let mut data = vec![0u8; WIDTH / 8];
    for (j, byte) in data.iter_mut().enumerate() {
        let v = (j as u64).wrapping_mul(0x9e37_79b9_7f4a_7c15)
            ^ (owner as u64).wrapping_mul(0xd1b5_4a32_d192_ed03);
        *byte = (v ^ (v >> 13) ^ (v >> 37)) as u8;
    }
    // Deliberately different adjacent output bits and original-right bits.
    for (wire, bit) in [(524_288, false), (535_974, true),
        (544_592, true), (547_360, false), (547_361, true)] {
        set_bit(&mut data, wire, bit);
    }
    set_bit(&mut data, 0, owner & 1 != 0);
    data
}

fn bit(bytes: &[u8], wire: usize) -> bool {
    (bytes[wire / 8] >> (wire % 8)) & 1 != 0
}

fn set_bit(bytes: &mut [u8], wire: usize, value: bool) {
    let mask = 1u8 << (wire % 8);
    if value { bytes[wire / 8] |= mask; } else { bytes[wire / 8] &= !mask; }
}

fn expand(bytes: &[u8]) -> Vec<Fr> {
    (0..WIDTH).map(|wire| Fr::from(u64::from(bit(bytes, wire)))).collect()
}

fn packet_digest(packets: &[Vec<u8>; 4]) -> [u8; 32] {
    let mut hash = Blake2b::<U32>::new();
    hash.update(b"c334-four-sparse-packets-v1\0");
    for (&owner, bytes) in OWNERS.iter().zip(packets) {
        hash.update((owner as u64).to_le_bytes());
        hash.update(bytes);
    }
    hash.finalize().into()
}

fn localize(term: &Term, owner: usize) -> Term {
    let mut out = term.clone();
    out.row -= owner * ROWS;
    out.gate.left -= owner * WIDTH;
    out.gate.right -= owner * WIDTH;
    out
}

fn owner_slice(plan: &RowPlan<'_, '_>, owner: usize, slice: &Slice) -> Vec<Term> {
    let staged = plan.stage_owner(owner).expect("complete owner ROW stage");
    let selected: Vec<_> = staged.terms()
        .filter(|(relation, term)| *relation == Relation::Header
            && (owner * ROWS + LOCAL_ROW..owner * ROWS + LOCAL_ROW + 8).contains(&term.row))
        .map(|(_, term)| localize(term, owner)).collect();
    assert_eq!(selected.len(), 192, "all MUX tuples retained at owner {owner}");
    assert_eq!(selected, slice.attached, "ordered retained/placed MUX tuples at owner {owner}");
    selected
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Key { right: usize, s: usize, h: usize }

#[derive(Clone, Copy)]
struct Group { key: Key, c1: Fr, c3: Fr }

fn groups(prefix: &[Fr], local_row_weights: &[Fr]) -> Vec<Group> {
    let p = prefix.len();
    assert!(p <= 20 && local_row_weights.len() == ROWS);
    let weights = boolean_u_eq_weights(prefix).expect("prefix weights");
    let mask = weights.len() - 1;
    let mut map = BTreeMap::<Key, (Fr, Fr)>::new();
    // Finite source grammar. This routine never receives a Term or oracle
    // tuple stream, and it runs once per prefix, outside the owner loop.
    for k in 0..8 {
        let row = LOCAL_ROW + k;
        for i in 0..8 {
            for role in 0..3 {
                let d = expected(k, i, role);
                let left = d.gate.left;
                let key = Key { right: d.gate.right, s: (left >> p) & 1, h: left >> (p + 1) };
                let weight = local_row_weights[row] * weights[left & mask];
                let entry = map.entry(key).or_insert((Fr::zero(), Fr::zero()));
                entry.0 += weight * d.gate.c1;
                entry.1 += weight * d.gate.c3;
            }
        }
    }
    map.into_iter().map(|(key, (c1, c3))| Group { key, c1, c3 }).collect()
}

#[derive(Default)]
struct KernelWork {
    aligned_loads: usize,
    word_ops: usize,
    masks: usize,
    lut_reads: usize,
    bank_bit_steps: usize,
    grouped_key_visits: usize,
}

/// Source-fixed C226 transpose. `mask[bank][neighbor][bit]` has lane k equal
/// to X at the bank's kth selected byte and the requested quartet neighbor.
/// No owner-dependent array is indexed by an occurrence or a group key.
struct PackedMasks { mask: [[[u8; 8]; 4]; 3], selector: bool }
impl PackedMasks {
    fn load64(packet: &[u8], word: usize) -> u64 {
        let start = word * 8;
        u64::from_le_bytes(packet[start..start + 8].try_into().unwrap())
    }
    fn new(packet: &[u8], work: &mut KernelWork) -> Self {
        assert_eq!(packet.len(), WIDTH / 8);
        assert_eq!([535_974 / 64, 544_588 / 64, 544_588 / 64 + 1,
            544_716 / 64, 544_716 / 64 + 1, 547_360 / 64,
            547_360 / 64 + 1], PACKED_WORDS_P01);
        let mut mask = [[[0u8; 8]; 4]; 3];
        // Exactly six bank words and one original-selector word. The linear
        // output's right address has c2=c3=0 and needs no witness load.
        for (bank, (start, residue)) in BANKS.into_iter().enumerate() {
            let d = start % 64;
            let aligned = start / 64;
            let u = Self::load64(packet, aligned);
            let v = Self::load64(packet, aligned + 1);
            let window = (u >> d) | (v << (64 - d));
            let tail4 = if residue == 3 { (v >> d) & 0xf } else { 0 };
            for neighbor in 0..4 {
                let x = (window >> neighbor) & 0x1111_1111_1111_1111;
                let mut y = x | (x << 1);
                y |= y << 2;
                if residue == 3 {
                    let x16 = (tail4 >> neighbor) & 1;
                    y = (y >> 3) | (0u64.wrapping_sub(x16) & 0xe000_0000_0000_0000);
                }
                for (shift, filter) in [(7, 0x00aa_00aa_00aa_00aa),
                    (14, 0x0000_cccc_0000_cccc), (28, 0x0000_0000_f0f0_f0f0)] {
                    let t = (y ^ (y >> shift)) & filter;
                    y ^= t ^ (t << shift);
                }
                for bit in 0..8 {
                    mask[bank][neighbor][bit] = ((y >> (8 * bit)) & 0xff) as u8;
                }
            }
        }
        let z = Self::load64(packet, 535_974 / 64);
        work.aligned_loads += 7;
        work.word_ops += 543; // C226 fixed transpose + 96 mask extractions + selector.
        work.masks += 96;
        Self { mask, selector: (z >> (535_974 % 64)) & 1 != 0 }
    }
}

fn qualify_mask_network() {
    // Independent bit-address oracle for all 200 possible bank input bits.
    // This qualification is outside the candidate owner's measured path.
    let mut basis_packet = vec![0u8; WIDTH / 8];
    for (bank, (start, residue)) in BANKS.into_iter().enumerate() {
        let input_bits = if residue == 0 { 64 } else { 68 };
        for source_bit in 0..input_bits {
            set_bit(&mut basis_packet, start + source_bit, true);
            let masks = PackedMasks::new(&basis_packet, &mut KernelWork::default());
            for neighbor in 0..4 {
                for i in 0..8 {
                    for k in 0..8 {
                        let wire = start + 4 * ((residue + 8 * k + i) / 4) + neighbor;
                        let actual = (masks.mask[bank][neighbor][i] >> k) & 1 != 0;
                        assert_eq!(actual, bit(&basis_packet, wire),
                            "packed mask basis bank={bank} source_bit={source_bit} neighbor={neighbor} i={i} k={k}");
                    }
                }
            }
            set_bit(&mut basis_packet, start + source_bit, false);
        }
    }
    // A mixed packet also catches interference between set bits that a basis
    // check alone would miss if the implementation were nonlinear.
    let mixed = packet(OWNERS[0]);
    let masks = PackedMasks::new(&mixed, &mut KernelWork::default());
    for (bank, (start, residue)) in BANKS.into_iter().enumerate() {
        for neighbor in 0..4 {
            for i in 0..8 {
                for k in 0..8 {
                    let wire = start + 4 * ((residue + 8 * k + i) / 4) + neighbor;
                    let actual = (masks.mask[bank][neighbor][i] >> k) & 1 != 0;
                    assert_eq!(actual, bit(&mixed, wire),
                        "packed mask mixed bank={bank} neighbor={neighbor} i={i} k={k}");
                }
            }
        }
    }
}

/// The eight q rows share one high-row factor. The 256 subset sums are made
/// once from the actual ROW19 weights; each owner uses only byte-mask lookups.
struct MaskLut { value: [Fr; 256], row0: Fr }
impl MaskLut {
    fn new(local: &[Fr]) -> Self {
        assert_eq!(local.len(), ROWS);
        let mut value = [Fr::zero(); 256];
        for mask in 1usize..256 {
            let bit = mask.trailing_zeros() as usize;
            value[mask] = value[mask & (mask - 1)] + local[LOCAL_ROW + bit];
        }
        Self { value, row0: local[LOCAL_ROW] }
    }
    fn get(&self, mask: u8, work: &mut KernelWork) -> Fr {
        work.lut_reads += 1;
        self.value[mask as usize]
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Fault { None, Row, Right, Side, SelectOutput01 }

fn packed_owner_message(packet: &[u8], prefix: &[Fr], rho: Fr, lut: &MaskLut,
    fault: Fault, work: &mut KernelWork) -> [Fr; 3] {
    assert!(prefix.len() <= 1);
    let p = prefix.len();
    let masks = PackedMasks::new(packet, work);
    let z = Fr::from(u64::from(masks.selector));
    let mut out = [Fr::zero(); 3];
    for (bank, residue) in [(0usize, 0usize), (1, 3), (2, 3)] {
        let selector = match bank { 0 => Fr::one(), 1 => z - Fr::one(), _ => -z };
        for i in 0..8 {
            work.bank_bit_steps += 1;
            let lane = (residue + i) & 3;
            let s = (lane >> p) & 1;
            let chi = if p == 0 { Fr::one() }
                else if lane & 1 == 0 { Fr::one() - prefix[0] } else { prefix[0] };
            let mut x0;
            let x1;
            if p == 0 {
                x0 = lut.get(masks.mask[bank][lane & !1][i], work);
                x1 = lut.get(masks.mask[bank][(lane & !1) + 1][i], work);
            } else {
                let b0 = lut.get(masks.mask[bank][0][i], work);
                let mut high_mask = masks.mask[bank][1][i];
                if fault == Fault::SelectOutput01 && bank == 0 && i == 0 {
                    assert_eq!(masks.mask[0][0][0] & 1, 0);
                    assert_eq!(high_mask & 1, 1);
                    // Inject the fault into the actual packed mask input of
                    // the Fr fold, leaving X and all other lanes unchanged.
                    high_mask &= !1;
                }
                let b1 = lut.get(high_mask, work);
                let b2 = lut.get(masks.mask[bank][2][i], work);
                let b3 = lut.get(masks.mask[bank][3][i], work);
                x0 = b0 + prefix[0] * (b1 - b0);
                x1 = b2 + prefix[0] * (b3 - b2);
            }
            let alpha = selector * Fr::from(1u64 << i) * chi;
            add_one(&mut out, alpha, s, x0, x1);
        }
    }
    let mut weighted = out.map(|value| rho * value);
    if matches!(fault, Fault::Row | Fault::Right | Fault::Side) {
        // Test-only count-preserving replacement of one finite grammar tuple.
        // The admitted Fault::None path above has no occurrence reads.
        let old = expected(0, 1, 2);
        let mut new = old.clone();
        match fault {
            Fault::Row => new.row += 1,
            Fault::Right => new.gate.right = 524_288,
            Fault::Side => std::mem::swap(&mut new.gate.left, &mut new.gate.right),
            _ => unreachable!(),
        }
        let old_message = candidate_one_fault_tuple(&old, packet, prefix, rho, lut);
        let new_message = candidate_one_fault_tuple(&new, packet, prefix, rho, lut);
        for j in 0..3 { weighted[j] += new_message[j] - old_message[j]; }
    }
    weighted
}

fn candidate_one_fault_tuple(term: &Term, packet: &[u8], prefix: &[Fr], rho: Fr,
    lut: &MaskLut) -> [Fr; 3] {
    assert_eq!(prefix.len(), 1); // This accessor exists only for isolated faults.
    let left = term.gate.left;
    let z = Fr::from(u64::from(bit(packet, term.gate.right)));
    let low = (left >> 1) & !1;
    let folded = |index: usize| {
        let a = Fr::from(u64::from(bit(packet, 2 * index)));
        let b = Fr::from(u64::from(bit(packet, 2 * index + 1)));
        a + prefix[0] * (b - a)
    };
    let x0 = folded(low);
    let x1 = folded(low + 1);
    let chi = if left & 1 == 0 { Fr::one() - prefix[0] } else { prefix[0] };
    let weight = match term.row {
        LOCAL_ROW => lut.row0,
        row if row == LOCAL_ROW + 1 => lut.value[2], // bit1 selects q20177.
        _ => panic!("fault tuple ROW outside selected pair"),
    };
    let alpha = rho * weight * chi * (term.gate.c1 + term.gate.c3 * z);
    let mut result = [Fr::zero(); 3];
    add_one(&mut result, alpha, (left >> 1) & 1, x0, x1);
    result
}

fn add_one(message: &mut [Fr; 3], alpha: Fr, s: usize, x0: Fr, x1: Fr) {
    let dx = x1 - x0;
    if s == 0 {
        message[0] += alpha * x0;
        message[1] += alpha * (dx - x0);
        message[2] -= alpha * dx;
    } else {
        message[1] += alpha * x0;
        message[2] += alpha * dx;
    }
}

fn candidate_owner_message(groups: &[Group], packet: &[u8], prefix: &[Fr], rho: Fr,
    lut: &MaskLut, fault: Fault, work: &mut KernelWork) -> [Fr; 3] {
    let p = prefix.len();
    if p <= 1 { return packed_owner_message(packet, prefix, rho, lut, fault, work); }
    assert_eq!(fault, Fault::None);
    let projected = if p >= 2 {
        Some(EdgePrefixPlan::new(WIDTH, prefix).unwrap().project_bits(packet).unwrap())
    } else { None };
    let mut out = [Fr::zero(); 3];
    for group in groups {
        work.grouped_key_visits += 1;
        let z = Fr::from(u64::from(bit(packet, group.key.right)));
        let alpha = group.c1 + group.c3 * z;
        let x0 = projected.as_ref().unwrap()[2 * group.key.h];
        let x1 = projected.as_ref().unwrap()[2 * group.key.h + 1];
        add_one(&mut out, alpha, group.key.s, x0, x1);
    }
    out.map(|value| rho * value)
}

fn oracle_owner_message(terms: &[Term], packet: &[u8], prefix: &[Fr],
    factor: &OneFamilyRowFactor<'_>, owner: usize) -> [Fr; 3] {
    let original = expand(packet);
    let weights = boolean_u_eq_weights(prefix).unwrap();
    let (a, b) = direct_u_prefix_coefficients(WIDTH, prefix, &weights, owner, &original,
        |_, row| factor.local(row),
        |sink| { for term in terms { sink(term.clone())?; } Ok(()) }).unwrap();
    let x = if prefix.is_empty() { original }
        else { EdgePrefixPlan::new(WIDTH, prefix).unwrap().project_bits(packet).unwrap() };
    let values = gkr::quadratic_message(&a, &b, &x);
    [values[0] * factor.copy(owner), values[1] * factor.copy(owner),
        values[2] * factor.copy(owner)]
}

fn initial_claim(owners: &[Vec<Term>; 4], packets: &[Vec<u8>; 4],
    factor: &OneFamilyRowFactor<'_>) -> Fr {
    let mut claim = Fr::zero();
    for ((&owner, terms), packet) in OWNERS.iter().zip(owners).zip(packets) {
        let rho = factor.copy(owner);
        for term in terms {
            let gate = &term.gate;
            let x = Fr::from(u64::from(bit(packet, gate.left)));
            let z = Fr::from(u64::from(bit(packet, gate.right)));
            claim += rho * factor.local(term.row)
                * (gate.c0 + gate.c1 * x + gate.c2 * z + gate.c3 * x * z);
        }
    }
    claim
}

fn transcript(r: &[Fr], digest: &[u8; 32], claim: Fr) -> Transcript {
    let mut t = Transcript::new(b"c334-h21-four-owner-mux-slice-v1");
    t.append_bytes(b"source-sha256", b"52C6D954F0E11EAE2749DCE34692941C457BEB50F598FFEED16848383071323A");
    t.append_bytes(b"sparse-domain", b"all nonselected H21 owners have zero X; selected HEADER MUX slice only");
    t.append_u64(b"headers", 1_827_840);
    t.append_u64(b"slot-log", 21);
    t.append_bytes(b"cut", b"eligible08");
    t.append_bytes(b"row-layout", &crate::header_daa_row_placement::Layout::fixed().digest());
    for owner in OWNERS { t.append_u64(b"owner", owner as u64); }
    t.append_bytes(b"X-digest", digest);
    for coordinate in r { t.append_scalar(b"row-coordinate", coordinate); }
    t.append_scalar(b"initial-slice-claim", &claim);
    t
}

fn add(sum: &mut [Fr; 3], part: [Fr; 3]) {
    for (target, value) in sum.iter_mut().zip(part) { *target += value; }
}

fn check_retirement(roster: &DaaHistoryRoster<'_>, scheduled: &Scheduled, owner: usize) {
    let (class, wanted_active) = match owner {
        843_776 => (OwnerClass::Mature(Epoch::Legacy), [false; 4]),
        845_759 => (OwnerClass::Carry, [false, false, true, true]),
        1_048_576 => (OwnerClass::Mature(Epoch::Eip), [false; 4]),
        1_827_840 => (OwnerClass::Padding, [false; 4]),
        _ => panic!("owner not in frozen H21 diagnostic list"),
    };
    assert_eq!(roster.owner_class(owner as u64).unwrap(), class,
        "independent frozen physical-owner class");
    let mut active = [false; 4];
    scheduled.visit_owner(owner, |writer, _| {
        match writer {
            Writer::Max { context, .. } => active[context] = true,
            Writer::Cap { context, .. } => active[2 + context] = true,
        }
        Ok(())
    }).unwrap();
    assert_eq!(active, wanted_active, "eligible08 frozen role mask owner {owner}");
    let boolean_owner_point: Vec<_> = (0..21)
        .map(|bit| Fr::from(((owner >> bit) & 1) as u64)).collect();
    let analytic = scheduled.anchor_owner_weights(&boolean_owner_point,
        &boolean_owner_point, &boolean_owner_point).unwrap();
    let expected_analytic = wanted_active.map(|enabled| Fr::from(u64::from(enabled)));
    assert_eq!(analytic, expected_analytic, "analytic role mask independent of literal writer visit");
    let header = Merge::new(roster, scheduled).unwrap().header_terms(owner).unwrap();
    let wanted = std::array::from_fn(|j| if active[j] { [673, 673, 2048, 2048][j] } else { 0 });
    assert_eq!(header.retired, wanted, "eligible08 exact HEADER retirement mask owner {owner}");
    assert!(header.terms.iter().filter(|term|
        (owner * ROWS + LOCAL_ROW..owner * ROWS + LOCAL_ROW + 8).contains(&term.row)).count() == 192,
        "all selected MUX occurrences survive the exact retirement");
}

fn owner_terminal(terms: &[Term], packet: &[u8], prefix: &[Fr],
    factor: &OneFamilyRowFactor<'_>, owner: usize) -> [Fr; 3] {
    assert_eq!(prefix.len(), 20);
    let original = expand(packet);
    let weights = boolean_u_eq_weights(prefix).unwrap();
    let (a, b) = direct_u_prefix_coefficients(WIDTH, prefix, &weights, owner, &original,
        |_, row| factor.local(row),
        |sink| { for term in terms { sink(term.clone())?; } Ok(()) }).unwrap();
    let x = EdgePrefixPlan::new(WIDTH, prefix).unwrap().project_bits(packet).unwrap();
    [factor.copy(owner) * a[0], factor.copy(owner) * b[0], x[0]]
}

fn candidate_terminal(packet: &[u8], prefix: &[Fr], terminal_groups: &[Group], rho: Fr) -> [Fr; 3] {
    let mut a = Fr::zero();
    let mut b = Fr::zero();
    for group in terminal_groups {
        assert_eq!((group.key.s, group.key.h), (0, 0));
        let z = Fr::from(u64::from(bit(packet, group.key.right)));
        a += group.c1 + group.c3 * z;
        // Every reviewed MUX tuple has c0=c2=0. Keep B explicit in the
        // terminal triple so a later source change cannot imply a hidden B.
        b += Fr::zero();
    }
    let x = EdgePrefixPlan::new(WIDTH, prefix).unwrap().project_bits(packet).unwrap();
    [rho * a, rho * b, x[0]]
}

fn check_mutants(terms: &[Term], packet: &[u8], prefix: &[Fr],
    factor: &OneFamilyRowFactor<'_>, owner: usize, lut: &MaskLut) {
    assert_eq!(prefix.len(), 1);
    assert!(!prefix[0].is_zero() && !prefix[0].is_one());
    let baseline = oracle_owner_message(terms, packet, prefix, factor, owner);
    let target = terms.iter().position(|t| t.row == LOCAL_ROW && t.gate.left == 544_592
        && t.gate.right == 535_974 && t.gate.c3 == -Fr::from(2u64)).unwrap();
    let target_baseline = oracle_owner_message(std::slice::from_ref(&terms[target]),
        packet, prefix, factor, owner);
    let mut predicted = [[Fr::zero(); 3]; 3];
    for (index, fault) in [Fault::Row, Fault::Right, Fault::Side].into_iter().enumerate() {
        let mut bad = terms.to_vec();
        match fault {
            Fault::Row => bad[target].row += 1,
            Fault::Right => bad[target].gate.right = 524_288,
            Fault::Side => { let gate = &mut bad[target].gate;
                std::mem::swap(&mut gate.left, &mut gate.right); }
            _ => unreachable!(),
        }
        let target_bad = oracle_owner_message(std::slice::from_ref(&bad[target]),
            packet, prefix, factor, owner);
        predicted[index] = std::array::from_fn(|j| target_bad[j] - target_baseline[j]);
        assert_ne!(predicted[index], [Fr::zero(); 3],
            "isolated mutant {index} predicted nonzero delta");
    }
    let output = terms.iter().find(|t| t.row == LOCAL_ROW && t.gate.left == 547_360).unwrap();
    let one = oracle_owner_message(std::slice::from_ref(output), packet, prefix, factor, owner);
    let alpha = factor.copy(owner) * factor.local(LOCAL_ROW)
        * (Fr::one() - prefix[0]) * output.gate.c1;
    let folded_x0 = prefix[0]; // X[547360..=547361] is sealed to 01.
    let delta = [-(alpha * folded_x0), alpha * Fr::from(2u64) * folded_x0,
        -(alpha * folded_x0)];
    assert_ne!(delta, [Fr::zero(); 3], "Boolean-select mutant predicted delta");
    assert_ne!(one, [Fr::zero(); 3], "the targeted output occurrence is active");
    // Only after all four oracle-side nonzero predictions are fixed does the
    // candidate consume the sealed packet and challenge.
    let shared = groups(prefix, &factor.local_weights);
    let mut work = KernelWork::default();
    let candidate = candidate_owner_message(&shared, packet, prefix,
        factor.copy(owner), lut, Fault::None, &mut work);
    assert_eq!(candidate, baseline, "preflight candidate matches unchanged literal oracle");
    for (index, fault) in [Fault::Row, Fault::Right, Fault::Side].into_iter().enumerate() {
        let actual = candidate_owner_message(&shared, packet, prefix,
            factor.copy(owner), lut, fault, &mut KernelWork::default());
        let observed = std::array::from_fn::<_, 3, _>(|j| actual[j] - baseline[j]);
        assert_eq!(observed, predicted[index], "candidate mutant {index} delta attribution");
        assert_ne!(actual, baseline, "candidate MUX mutant {index} rejected by unchanged oracle");
    }
    let wrong = candidate_owner_message(&shared, packet, prefix, factor.copy(owner),
        lut, Fault::SelectOutput01, &mut KernelWork::default());
    let observed = std::array::from_fn::<_, 3, _>(|j| wrong[j] - baseline[j]);
    assert_eq!(observed, delta, "packed-mask Boolean-select mutant delta attribution");
    assert_ne!(wrong, baseline, "Boolean-select candidate rejected by unchanged literal oracle");
}

#[test]
fn c334_phase_a_all_round() {
    qualify_mask_network();
    let slice = qualify();
    let parent = WorkTreeHistoryPlan::compile(1_827_840, 21, [0; 32], [0; 28]).unwrap();
    let roster = DaaHistoryRoster::compile(&parent).unwrap();
    let scheduled = Scheduled::eligible08();
    for owner in OWNERS { check_retirement(&roster, &scheduled, owner); }
    let placement = RowPlan::new(&roster, &scheduled).unwrap();
    let owner_terms: [Vec<Term>; 4] = OWNERS.map(|owner| owner_slice(&placement, owner, &slice));
    let packets = OWNERS.map(packet);
    let digest = packet_digest(&packets);
    let r: Vec<Fr> = (0..40).map(|i| Fr::from((7 + 3 * i) as u64)).collect();
    let factor = OneFamilyRowFactor::try_new(&r, 21, 19, 0, &[19], None).unwrap();
    let lut = MaskLut::new(&factor.local_weights);
    assert!(OWNERS.iter().all(|&owner| !factor.copy(owner).is_zero()));
    // Preflight from literal terms only: a sealed non-Boolean first challenge
    // and a fault-sensitive owner exist before the candidate receives X.
    let initial = initial_claim(&owner_terms, &packets, &factor);
    let seed = transcript(&r, &digest, initial);
    let mut preflight = seed.clone();
    let mut pre_claim = initial;
    let mut pre_rounds = Vec::new();
    let mut first = [Fr::zero(); 3];
    for ((&owner, terms), packet) in OWNERS.iter().zip(&owner_terms).zip(&packets) {
        let part = oracle_owner_message(terms, packet, &[], &factor, owner);
        if owner == 1_048_576 || owner == 1_827_840 {
            assert_ne!(part, [Fr::zero(); 3], "high-owner/padding block must be nonvacuous");
        }
        add(&mut first, part);
    }
    let u0 = send_round(first.to_vec(), &mut pre_claim, &mut pre_rounds, &mut preflight).unwrap();
    check_mutants(&owner_terms[2], &packets[2], &[u0], &factor, OWNERS[2], &lut);
    // From this point, both paths receive the same immutable packets and
    // transcript seed. Every challenge below is drawn online by each path.
    let mut literal_t = seed.clone();
    let mut candidate_t = seed;
    let mut literal_claim = initial;
    let mut candidate_claim = initial;
    let mut literal_rounds = Vec::new();
    let mut candidate_rounds = Vec::new();
    let mut literal_prefix = Vec::new();
    let mut candidate_prefix = Vec::new();
    let mut work = KernelWork::default();
    const SUPPORT: [usize; 20] = [192, 98, 50, 26, 14, 8, 6, 4, 3, 3,
        3, 3, 3, 2, 2, 2, 2, 2, 2, 2];
    for p in 0..20 {
        let shared = groups(&candidate_prefix, &factor.local_weights);
        assert_eq!(shared.len(), SUPPORT[p], "source-shared group census prefix {p}");
        let mut expected_aggregate = [Fr::zero(); 3];
        let mut actual_aggregate = [Fr::zero(); 3];
        for ((&owner, terms), packet) in OWNERS.iter().zip(&owner_terms).zip(&packets) {
            let expected = oracle_owner_message(terms, packet, &literal_prefix, &factor, owner);
            let actual = candidate_owner_message(&shared, packet, &candidate_prefix,
                factor.copy(owner), &lut, Fault::None, &mut work);
            assert_eq!(actual, expected, "MUX owner {owner} prefix {p} message");
            add(&mut expected_aggregate, expected);
            add(&mut actual_aggregate, actual);
        }
        assert_eq!(actual_aggregate, expected_aggregate, "MUX aggregate prefix {p}");
        let lu = send_round(expected_aggregate.to_vec(), &mut literal_claim,
            &mut literal_rounds, &mut literal_t).unwrap();
        let cu = send_round(actual_aggregate.to_vec(), &mut candidate_claim,
            &mut candidate_rounds, &mut candidate_t).unwrap();
        assert_eq!(cu, lu, "online challenge prefix {p}");
        assert!(!cu.is_zero() && !cu.is_one(), "every frozen online challenge is non-Boolean");
        assert_eq!(candidate_claim, literal_claim, "updated claim prefix {p}");
        let mut l_probe = literal_t.clone();
        let mut c_probe = candidate_t.clone();
        assert_eq!(c_probe.challenge_scalar(b"c334-continuation"),
            l_probe.challenge_scalar(b"c334-continuation"), "transcript continuation prefix {p}");
        literal_prefix.push(lu);
        candidate_prefix.push(cu);
    }
    let mut terminal_claim = Fr::zero();
    let terminal_groups = groups(&candidate_prefix, &factor.local_weights);
    assert_eq!(terminal_groups.len(), 2, "p20 right-key terminal grammar");
    for ((&owner, terms), packet) in OWNERS.iter().zip(&owner_terms).zip(&packets) {
        let expected = owner_terminal(terms, packet, &literal_prefix, &factor, owner);
        let actual = candidate_terminal(packet, &candidate_prefix, &terminal_groups,
            factor.copy(owner));
        assert_eq!(actual, expected, "p20 high A/B/X owner {owner}");
        terminal_claim += actual[0] * actual[2] + actual[1];
    }
    assert_eq!(literal_claim, terminal_claim, "p20 local high handoff claim");
    assert_eq!(candidate_claim, terminal_claim, "candidate p20 terminal claim");
    assert_eq!((work.aligned_loads, work.word_ops, work.masks, work.lut_reads,
        work.bank_bit_steps), (56, 4344, 768, 576, 192), "fixed p0/p1 packed work census");
    assert_eq!(work.grouped_key_visits, 4 * (427 - 192 - 98),
        "p2..19 owner work visits only shared group keys");
    println!("C334_PHASE_A_PASS source_tuples=192 prefixes=20 owners=4 grouped_support_sum=427 x_digest={}",
        digest.iter().map(|byte| format!("{byte:02x}")).collect::<String>());
}

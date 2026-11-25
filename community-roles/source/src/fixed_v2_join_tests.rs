//! Selected Mainnet reset difficulties joined to the existing common witness.
use super::{Context as Base, AUX as CARRY_AUX};
use crate::daa_alias_stream_tests as helpers;
use crate::{
    daa_integer::{self, CompiledCarry},
    gkr::{self, GkrProof, InputClaim},
    header_hash,
    header_height_layout::HeaderHeightLayout,
    header_history_boundary::HeaderHistoryBoundary,
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
const WIDTH: usize = 1 << 20;
const MEMBER_ROWS: [usize; 2] = [19, 18];
const H: u32 = 417_792;
const HEADERS: [u32; 2] = [H, H + 1];
const AUX: usize = 14;
const ANCHOR: usize = 8192;
const ALIAS: usize = (1 << 19) | (1 << 17) | 1152;
const HEIGHT: usize = (1 << 19) | (1 << 17) | 1024;
const COMPACT: u32 = 0x066f98d5;
const DOMAIN: &[u8] = b"native-common-mainnet-fixed-v2-v1";
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum NumericRule {
    FixedReset,
    LegacySingleton,
}
impl NumericRule {
    fn heights(self) -> [u32; 2] {
        match self {
            Self::FixedReset => HEADERS,
            Self::LegacySingleton => [1024, 1025],
        }
    }
    fn anchor_count(self) -> usize {
        match self {
            Self::FixedReset => 256,
            Self::LegacySingleton => 0,
        }
    }
    fn domain(self) -> &'static [u8] {
        match self {
            Self::FixedReset => DOMAIN,
            Self::LegacySingleton => b"native-common-mainnet-legacy-singleton-v1",
        }
    }
    fn identity(self) -> &'static [u8] {
        match self {
            Self::FixedReset => b"Mainnet-fixed-reset",
            Self::LegacySingleton => b"Mainnet-Legacy-positive-singleton",
        }
    }
}
fn target() -> BigUint {
    BigUint::parse_bytes(b"6f98d5000000", 16).unwrap()
}
fn eq(p: &[Fr], i: usize) -> Fr {
    helpers::eq_at(p, i)
}
fn boolean(i: usize, bits: usize) -> Vec<Fr> {
    super::boolean(i, bits)
}
fn row(e: &EdgeTerm) -> Result<usize, String> {
    sparse_stream_roster::global_edge_row(e.source_slot, e.family_row, 4, 19, 1, &MEMBER_ROWS)
}
fn augment(helper: &CompiledCarry) -> Circuit {
    let mut circuit = helper.circuit.as_ref().unwrap().clone();
    assert_eq!(circuit.input_len, 4096);
    assert_eq!(circuit.row_count, ANCHOR);
    circuit.row_count = 16384;
    for (b, &wire) in helper.decoded.iter().enumerate() {
        circuit.terms.push(Term {
            row: ANCHOR + b,
            gate: gkr::Gate {
                left: wire,
                right: 0,
                c0: -Fr::from(target().bit(b as u64) as u64),
                c1: Fr::one(),
                c2: Fr::zero(),
                c3: Fr::zero(),
            },
        });
    }
    circuit
}
struct Context {
    rule: NumericRule,
    base: Base,
    expected: CompiledCarry,
    natural: Circuit,
    padded: Circuit,
    shape: sparse::Shape,
    header_raw: [usize; 32],
    fingerprint: String,
}
impl Context {
    fn new() -> Result<Self, String> {
        Self::for_rule(NumericRule::FixedReset)
    }
    fn for_rule(rule: NumericRule) -> Result<Self, String> {
        let base = Base::new()?;
        match rule {
            NumericRule::FixedReset => {
                for child in HEADERS {
                    if crate::daa_header_window::for_child_height(child)?.action()
                        != crate::daa_header_window::Action::FixedV2
                    {
                        return Err("Mainnet reset schedule changed".into());
                    }
                }
            }
            NumericRule::LegacySingleton => {
                let plan = crate::daa_header_window::for_child_height(1025)?;
                if plan.action()
                    != crate::daa_header_window::Action::Retarget(daa_integer::Epoch::Legacy)
                    || plan.sample_heights() != [1024]
                {
                    return Err("Mainnet singleton schedule changed".into());
                }
            }
        }
        let value = target();
        if value.is_zero() || value.bits() > 256 || value > crate::daa_count::q() {
            return Err("Mainnet reset target bounds".into());
        }
        let raw = match rule {
            NumericRule::FixedReset => COMPACT,
            NumericRule::LegacySingleton => 0x03000001,
        };
        let expected = daa_integer::compile_carry(&crate::daa_count::q(), raw, raw, true)?;
        let natural = match rule {
            NumericRule::FixedReset => augment(&expected),
            NumericRule::LegacySingleton => expected.circuit.as_ref().unwrap().clone(),
        };
        let padded = Circuit {
            input_len: WIDTH,
            row_count: 1 << 17,
            terms: natural.terms.clone(),
        };
        let shape = sparse::validate(&padded, 0).map_err(|e| e.to_string())?;
        if shape.input_bits != 20
            || shape.row_bits != 17
            || natural.terms.len() != 11804 + rule.anchor_count()
        {
            return Err("fixed target shape/count changed".into());
        }
        let fingerprint = crate::work_tree_layout::hash_terms(&natural.terms);
        let raw = serializer::build(None)?.layout.fields.n_bits;
        let header_raw = raw.map(|w| header_hash::SERIALIZER_OFFSET + w);
        if header_raw.iter().any(|w| *w >= WIDTH) {
            return Err("reset raw port escaped copy".into());
        }
        let c = Self {
            rule,
            base,
            expected,
            natural,
            padded,
            shape,
            header_raw,
            fingerprint,
        };
        for child in c.rule.heights() {
            if c.header().eip_is_mature_at(u64::from(child - 1)) {
                return Err("reset must not release mature EIP anchors".into());
            }
        }
        Ok(c)
    }
    fn header(&self) -> &HeaderHistoryBoundary {
        &self.base.base.base.header
    }
    fn height(&self) -> &HeaderHeightLayout {
        &self.base.base.height
    }
    fn total(&self) -> usize {
        self.base.total() + 949510 + 64 + self.natural.terms.len() + 64
    }
    fn bound_target(&self) -> BigUint {
        match self.rule {
            NumericRule::FixedReset => target(),
            NumericRule::LegacySingleton => BigUint::zero(),
        }
    }
    fn bind(&self, t: &mut Transcript, key: &[u8; 32], commitment: &[u8], bound_target: &BigUint) {
        self.bind_with_rule_identity(t, key, commitment, bound_target, self.rule.identity());
    }
    fn bind_with_rule_identity(
        &self,
        t: &mut Transcript,
        key: &[u8; 32],
        commitment: &[u8],
        bound_target: &BigUint,
        rule_identity: &[u8],
    ) {
        self.base.bind(t, key, commitment, 64);
        t.append_bytes(b"fixed-profile", self.rule.domain());
        t.append_bytes(b"fixed-rule", rule_identity);
        t.append_bytes(b"fixed-network", b"Mainnet");
        t.append_bytes(b"fixed-target", &bound_target.to_bytes_be());
        t.append_bytes(b"fixed-Q", &crate::daa_count::q().to_bytes_be());
        t.append_bytes(
            b"fixed-config-sha256",
            b"8714A73D3012A123D39EA5242410B993A627AEEFA180E6501EDAF679CFC8682E",
        );
        t.append_bytes(
            b"fixed-processor-sha256",
            b"35CBB6EF3F9BCB885E6C76BE6F3C9AA489815D18D291D3E06DE1DF38F655C715",
        );
        t.append_bytes(
            b"fixed-chain-settings-sha256",
            b"792FF3A3F5DF6336968B36C064A3CE0602A642F1FAB79B7E0389273BC9548BE1",
        );
        t.append_bytes(
            b"fixed-difficulty-adjustment-sha256",
            b"A38AE5FA599E2E61971823C335A0261369A2C4AAA030B11F82454CEFDC73B170",
        );
        t.append_bytes(b"fixed-augmented-fingerprint", self.fingerprint.as_bytes());
        t.append_bytes(
            b"fixed-helper-fingerprint",
            &self.expected.count.topology_blake2b256,
        );
        for (label, value) in [
            (b"fixed-H".as_slice(), u64::from(H)),
            (
                b"fixed-positive-sample-count",
                u64::from(self.rule == NumericRule::LegacySingleton),
            ),
            (b"fixed-native-legacy-epoch", 1024),
            (b"fixed-native-last-epochs", 8),
            (
                b"fixed-constant-target-present",
                u64::from(self.rule == NumericRule::FixedReset),
            ),
            (b"fixed-auxiliary-copy", AUX as u64),
            (b"fixed-original-input", 4096),
            (b"fixed-original-rows", 8192),
            (b"fixed-original-terms", 11804),
            (b"fixed-natural-input", 4096),
            (b"fixed-natural-rows", self.natural.row_count as u64),
            (b"fixed-padded-input", WIDTH as u64),
            (b"fixed-padded-rows", 1 << 17),
            (b"fixed-header-family-start", 0),
            (b"fixed-header-rows-per-copy", 1 << 19),
            (b"fixed-header-terms-per-copy", 474755),
            (b"fixed-header-term-count", 949510),
            (b"fixed-header-omitted-a4-count", 0),
            (b"fixed-height-family-start", HEIGHT as u64),
            (b"fixed-height-rows-per-copy", 32),
            (b"fixed-height-term-count", 64),
            (b"fixed-arithmetic-family-start", 1 << 19),
            (
                b"fixed-arithmetic-term-count",
                self.natural.terms.len() as u64,
            ),
            (b"fixed-anchor-start", ANCHOR as u64),
            (b"fixed-anchor-family-start", (1 << 19) | ANCHOR as u64),
            (b"fixed-anchor-count", self.rule.anchor_count() as u64),
            (b"fixed-alias-start", ALIAS as u64),
            (b"fixed-alias-count", 64),
            (b"fixed-local-terms", self.natural.terms.len() as u64),
            (b"fixed-total", self.total() as u64),
        ] {
            t.append_u64(label, value);
        }
        if self.rule == NumericRule::LegacySingleton {
            for height in [0, 1024] {
                t.append_u64(b"fixed-native-unfiltered-sample", height);
            }
            t.append_u64(b"fixed-native-positive-sample", 1024);
        }
        for (i, height) in self.rule.heights().into_iter().enumerate() {
            t.append_u64(b"fixed-header-height", u64::from(height));
            t.append_u64(b"fixed-header-copy", (12 + i) as u64);
        }
        for (i, &header) in self.header_raw.iter().enumerate() {
            t.append_u64(b"fixed-header-port", header as u64);
            t.append_u64(b"fixed-first-port", self.expected.parent_nbits[i] as u64);
            t.append_u64(b"fixed-second-port", self.expected.child_nbits[i] as u64);
        }
    }
    fn header_terms(
        &self,
        copy: usize,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        if !(12..14).contains(&copy) {
            return Ok(());
        }
        let slot = u64::from(self.rule.heights()[copy - 12] - 1);
        let counts = self.header().visit_slot_terms(slot, |mut term| {
            let local_row = term
                .row
                .checked_sub(slot as usize * (1 << 19))
                .ok_or("reset header row underflow")?;
            for wire in [&mut term.gate.left, &mut term.gate.right] {
                let local = wire
                    .checked_sub(slot as usize * WIDTH)
                    .ok_or("reset header endpoint underflow")?;
                if local >= WIDTH {
                    return Err("reset header endpoint escaped".into());
                }
                *wire = copy * WIDTH + local;
            }
            if local_row >= 1 << 19 {
                return Err("reset header row escaped".into());
            }
            term.row = local_row;
            sink(EdgeTerm {
                source_slot: copy,
                family_row: local_row,
                term,
            })
        })?;
        if counts.emitted != 474755 || counts.omitted_a4 != 0 {
            return Err("reset header release/count changed".into());
        }
        Ok(())
    }
    fn height_terms(
        &self,
        copy: usize,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        if !(12..14).contains(&copy) {
            return Ok(());
        }
        let slot = u64::from(self.rule.heights()[copy - 12] - 1);
        let n = self.height().visit_slot_terms(slot, |mut term| {
            let bit = term
                .row
                .checked_sub(slot as usize * 32)
                .ok_or("reset height row underflow")?;
            if bit >= 32 {
                return Err("reset height row escaped".into());
            }
            for wire in [&mut term.gate.left, &mut term.gate.right] {
                let local = wire
                    .checked_sub(slot as usize * WIDTH)
                    .ok_or("reset height endpoint underflow")?;
                if local >= WIDTH {
                    return Err("reset height endpoint escaped".into());
                }
                *wire = copy * WIDTH + local;
            }
            let row = HEIGHT + bit;
            term.row = row;
            sink(EdgeTerm {
                source_slot: copy,
                family_row: row,
                term,
            })
        })?;
        if n != 32 {
            return Err("reset height count".into());
        }
        Ok(())
    }
    fn arithmetic(
        &self,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        for source in &self.natural.terms {
            let mut term = source.clone();
            let row = (1 << 19) | source.row;
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
    fn port(&self, i: usize) -> (usize, usize) {
        assert!(i < 64);
        (
            (12 + i / 32) * WIDTH + self.header_raw[i % 32],
            AUX * WIDTH
                + if i < 32 {
                    self.expected.parent_nbits[i]
                } else {
                    self.expected.child_nbits[i - 32]
                },
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
    fn visit(
        &self,
        left: bool,
        copy: usize,
        mut sink: impl FnMut(EdgeTerm) -> Result<(), String>,
    ) -> Result<(), String> {
        self.base.visit(left, copy, &mut sink)?;
        self.header_terms(copy, &mut sink)?;
        self.height_terms(copy, &mut sink)?;
        if copy == AUX {
            self.arithmetic(&mut sink)?;
        }
        self.aliases(|e| {
            let wire = if left {
                e.term.gate.left
            } else {
                e.term.gate.right
            };
            if wire / WIDTH == copy {
                sink(e)?;
            }
            Ok(())
        })
    }
    fn parts(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[[Fr; 4]; 4], String> {
        if r.len() != 24 || u.len() != 24 || v.len() != 24 {
            return Err("reset common dimensions".into());
        }
        let mut header = [Fr::zero(); 4];
        let mut height = [Fr::zero(); 4];
        for (i, h) in self.rule.heights().into_iter().enumerate() {
            let copy = 12 + i;
            let fixed = boolean(h as usize - 1, 20);
            let mut rr = r[..19].to_vec();
            rr.extend_from_slice(&fixed);
            let mut uu = u[..20].to_vec();
            uu.extend_from_slice(&fixed);
            let mut vv = v[..20].to_vec();
            vv.extend_from_slice(&fixed);
            let hs = self.header().coefficients(&rr, &uu, &vv)?;
            let mask = (Fr::one() - r[23])
                * eq(&r[19..23], copy)
                * eq(&u[20..], copy)
                * eq(&v[20..], copy);
            for j in 0..4 {
                header[j] += mask * hs[j];
            }
            let mut hr = r[..5].to_vec();
            hr.extend_from_slice(&fixed);
            let ht = self.height().coefficients(&hr, &uu, &vv)?;
            let mask = r[23]
                * (Fr::one() - r[22])
                * r[17]
                * r[10]
                * (5..10)
                    .chain(11..17)
                    .fold(Fr::one(), |a, j| a * (Fr::one() - r[j]))
                * eq(&r[18..22], copy)
                * eq(&u[20..], copy)
                * eq(&v[20..], copy);
            for j in 0..4 {
                height[j] += mask * ht[j];
            }
        }
        Ok([
            header,
            height,
            self.arithmetic_coefficients(r, u, v)?,
            self.alias_coefficients(r, u, v)?,
        ])
    }
    fn arithmetic_coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != 24 || u.len() != 24 || v.len() != 24 {
            return Err("reset arithmetic dimensions".into());
        }
        let mask = r[23]
            * (Fr::one() - r[22])
            * (Fr::one() - r[17])
            * eq(&r[18..22], AUX)
            * eq(&u[20..], AUX)
            * eq(&v[20..], AUX);
        Ok(
            sparse::wiring(&self.padded, &self.shape, &r[..17], &u[..20], &v[..20])
                .map_err(|e| e.to_string())?
                .map(|x| x * mask),
        )
    }
    fn alias_coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        if r.len() != 24 || u.len() != 24 || v.len() != 24 {
            return Err("reset alias dimensions".into());
        }
        let mask = r[23]
            * (Fr::one() - r[22])
            * r[17]
            * r[10]
            * r[7]
            * (Fr::one() - r[6])
            * (8..10)
                .chain(11..17)
                .fold(Fr::one(), |a, j| a * (Fr::one() - r[j]))
            * eq(&r[18..22], AUX);
        let mut sum = Fr::zero();
        for i in 0..64 {
            let (l, h) = self.port(i);
            sum += eq(&r[..6], i) * eq(u, l) * eq(v, h);
        }
        let alias = [Fr::zero(), mask * sum, -mask * sum, Fr::zero()];
        Ok(alias)
    }
    fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let old = self.base.coefficients(r, u, v)?;
        let parts = self.parts(r, u, v)?;
        Ok(std::array::from_fn(|j| {
            old[j] + parts.iter().map(|p| p[j]).sum::<Fr>()
        }))
    }
}
fn reset_assignment(child: u32) -> Vec<Fr> {
    let (_, headers) = crate::header_history_boundary::tests::fixture();
    let h = ergo_header_core::Header::decode(&headers[&child], None).unwrap();
    let parent = ergo_header_core::Header::decode(&headers[&(child - 1)], None).unwrap();
    let fields = serializer::Fields::from_header(&h).unwrap();
    let mut boundary = crate::daa_history_layout::full_header_boundary(Some(&fields)).unwrap();
    crate::header_compact_links::assign_order(
        &mut boundary,
        &fields,
        child - 1,
        parent.timestamp,
        false,
    )
    .unwrap();
    boundary.base.base.base.input.take().unwrap()
}
fn native_helper() -> CompiledCarry {
    let (_, headers) = crate::header_history_boundary::tests::fixture();
    let raw = HEADERS.map(|h| {
        let decoded = ergo_header_core::Header::decode(&headers[&h], None).unwrap();
        serializer::Fields::from_header(&decoded).unwrap().n_bits
    });
    for x in raw {
        assert_eq!(super::mpi(x), (false, target()));
        assert_eq!(crate::work_tree_work::native_decode(x).unwrap(), target());
    }
    daa_integer::compile_carry(&crate::daa_count::q(), raw[0], raw[1], true).unwrap()
}

fn residues(circuit: &Circuit, input: &[Fr]) -> Vec<Fr> {
    let mut rows = vec![Fr::zero(); circuit.row_count];
    for term in &circuit.terms {
        rows[term.row] += term.gate.evaluate(input);
    }
    rows
}
#[test]
fn fixed_target_counterexample_anchors_and_native_header_owners() {
    let c = Context::new().unwrap();
    let helper = native_helper();
    super::assert_zero(&helper);
    assert_eq!(helper.circuit, c.expected.circuit);
    assert_eq!(super::read_word(&helper), target());
    assert!(residues(&c.natural, &helper.witness)
        .iter()
        .all(Zero::is_zero));
    let wrong =
        daa_integer::compile_carry(&crate::daa_count::q(), 0x066f98d4, 0x066f98d4, true).unwrap();
    super::assert_zero(&wrong);
    let failures = residues(&c.natural, &wrong.witness)
        .iter()
        .enumerate()
        .filter(|(_, x)| !x.is_zero())
        .map(|(i, _)| i)
        .collect::<Vec<_>>();
    assert_eq!(
        failures,
        vec![ANCHOR + 24],
        "shared wrong decoded target must fail only its changed target bit"
    );
    for b in 0..256 {
        let wire = helper.decoded[b];
        let mut bad = helper.witness.clone();
        bad[wire] = Fr::one() - bad[wire];
        let anchor = c
            .natural
            .terms
            .iter()
            .find(|t| t.row == ANCHOR + b)
            .unwrap();
        assert_eq!(anchor.gate.left, wire);
        assert_eq!(anchor.gate.right, 0);
        assert_eq!(anchor.gate.c0, -Fr::from(target().bit(b as u64) as u64));
        assert_eq!(anchor.gate.c1, Fr::one());
        assert!(!anchor.gate.evaluate(&bad).is_zero(), "target bit{b}");
        if b == 0 {
            bad[wire] = Fr::from(2u64);
            assert_eq!(
                residues(c.expected.circuit.as_ref().unwrap(), &bad)[0],
                Fr::from(2u64)
            );
        }
    }
    for child in [H, H + 1] {
        assert_eq!(
            crate::daa_header_window::for_child_height(child)
                .unwrap()
                .action(),
            crate::daa_header_window::Action::FixedV2
        );
    }
    for child in [H - 1, H + 2, 844673] {
        assert_ne!(
            crate::daa_header_window::for_child_height(child)
                .unwrap()
                .action(),
            crate::daa_header_window::Action::FixedV2
        );
    }
    for (i, child) in HEADERS.into_iter().enumerate() {
        let input = reset_assignment(child);
        assert_eq!(input.len(), WIDTH);
        let copy = 12 + i;
        let mut last = None;
        let mut residual = Fr::zero();
        let mut count = 0;
        c.header_terms(copy, |e| {
            if last.is_some_and(|r| r != e.family_row) {
                assert!(residual.is_zero(), "reset header row{last:?}");
                residual = Fr::zero();
            }
            last = Some(e.family_row);
            let mut gate = e.term.gate.clone();
            gate.left -= copy * WIDTH;
            gate.right -= copy * WIDTH;
            residual += gate.evaluate(&input);
            count += 1;
            Ok(())
        })
        .unwrap();
        assert!(residual.is_zero());
        assert_eq!(count, 474755);
        let mut hcount = 0;
        c.height_terms(copy, |e| {
            let mut gate = e.term.gate.clone();
            gate.left -= copy * WIDTH;
            gate.right -= copy * WIDTH;
            assert!(gate.evaluate(&input).is_zero());
            hcount += 1;
            Ok(())
        })
        .unwrap();
        assert_eq!(hcount, 32);
    }
    assert_eq!(c.total(), 2348174);
    println!("native MainnetH/H+1 numeric target {} compact066f98d5; shared wrong raw066f98d4 accepted bydecoders but onlyanchorbit24 fails; all256actualanchors/Boolean/two474755header+32height owners passed",target());
}

fn finite(
    mut visit: impl FnMut(&mut dyn FnMut(EdgeTerm) -> Result<(), String>) -> Result<(), String>,
    r: &[Fr],
    u: &[Fr],
    v: &[Fr],
) -> ([Fr; 4], usize) {
    // Independent per-term equality avoids three full 24-bit tables.
    let mut out = [Fr::zero(); 4];
    let mut count = 0;
    visit(&mut |e| {
        let w = eq(r, row(&e)?) * eq(u, e.term.gate.left) * eq(v, e.term.gate.right);
        for (a, b) in out.iter_mut().zip([
            e.term.gate.c0,
            e.term.gate.c1,
            e.term.gate.c2,
            e.term.gate.c3,
        ]) {
            *a += w * b;
        }
        count += 1;
        Ok(())
    })
    .unwrap();
    (out, count)
}
#[test]
fn fixed_families_match_full_domain_and_isolated_ports() {
    let c = Context::new().unwrap();
    let r = (0..24)
        .map(|i| Fr::from((17 + i * 7) as u64))
        .collect::<Vec<_>>();
    let u = (0..24)
        .map(|i| Fr::from((37 + i * 13) as u64))
        .collect::<Vec<_>>();
    let v = (0..24)
        .map(|i| Fr::from((53 + i * 19) as u64))
        .collect::<Vec<_>>();
    let parts = c.parts(&r, &u, &v).unwrap();
    let (header, hcount) = finite(
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
    let (height, n) = finite(
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
    let (arith, acount) = finite(|sink| c.arithmetic(sink), &r, &u, &v);
    let (alias, aliases) = finite(|sink| c.aliases(sink), &r, &u, &v);
    assert_eq!([hcount, n, acount, aliases], [949510, 64, 12060, 64]);
    assert_eq!(parts, [header, height, arith, alias]);
    for p in parts {
        assert_ne!(p, [Fr::zero(); 4]);
    }
    let natural_shape = sparse::validate(&c.natural, 0).unwrap();
    let truncated =
        sparse::wiring(&c.natural, &natural_shape, &r[..14], &u[..12], &v[..12]).unwrap();
    let high = (14..17).fold(Fr::one(), |a, i| a * (Fr::one() - r[i]))
        * (12..20).fold(Fr::one(), |a, i| {
            a * (Fr::one() - u[i]) * (Fr::one() - v[i])
        });
    let padded = sparse::wiring(&c.padded, &c.shape, &r[..17], &u[..20], &v[..20]).unwrap();
    assert_eq!(padded, truncated.map(|x| x * high));
    assert_ne!(padded, truncated);
    for i in 0..64 {
        let (l, h) = c.port(i);
        let mut actual = None;
        c.aliases(|e| {
            if e.family_row == ALIAS + i {
                actual = Some(e);
            }
            Ok(())
        })
        .unwrap();
        let e = actual.unwrap();
        assert_eq!((e.term.gate.left, e.term.gate.right), (l, h));
        let rb = boolean(row(&e).unwrap(), 24);
        let ub = boolean(l, 24);
        let vb = boolean(h, 24);
        let expected = [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()];
        assert_eq!(c.alias_coefficients(&rb, &ub, &vb).unwrap(), expected);
        for bit in [6, 7, 10, 17, 18, 22, 23] {
            let mut wrong = rb.clone();
            wrong[bit] = Fr::one() - wrong[bit];
            assert_eq!(
                c.alias_coefficients(&wrong, &ub, &vb).unwrap(),
                [Fr::zero(); 4]
            );
        }
        for wrong in [l ^ 1, l ^ WIDTH] {
            assert_eq!(
                c.alias_coefficients(&rb, &boolean(wrong, 24), &vb).unwrap(),
                [Fr::zero(); 4]
            );
        }
        for wrong in [h ^ 1, h ^ WIDTH] {
            assert_eq!(
                c.alias_coefficients(&rb, &ub, &boolean(wrong, 24)).unwrap(),
                [Fr::zero(); 4]
            );
        }
        let w = eq(&r, row(&e).unwrap()) * eq(&u, l) * eq(&v, h);
        assert_ne!([alias[0], alias[1] - w, alias[2] + w, alias[3]], alias);
        assert!(e.family_row >= ALIAS && e.family_row < ALIAS + 64);
        assert!(e.family_row >= super::ALIAS + 64);
    }
    for copy in [12, 13] {
        let mut rr = r.clone();
        rr[19..23].copy_from_slice(&boolean(copy, 4));
        rr[23] = Fr::zero();
        let (reference, _) = finite(|sink| c.header_terms(copy, sink), &rr, &u, &v);
        assert_ne!(reference, [Fr::zero(); 4]);
        assert_eq!(c.parts(&rr, &u, &v).unwrap()[0], reference);
        let bit = 0;
        let rb = boolean(
            sparse_stream_roster::global_edge_row(copy, HEIGHT + bit, 4, 19, 1, &MEMBER_ROWS)
                .unwrap(),
            24,
        );
        let ub = boolean(copy * WIDTH + c.height().height_wire(bit).unwrap(), 24);
        let vb = boolean(copy * WIDTH, 24);
        assert_eq!(
            c.parts(&rb, &ub, &vb).unwrap()[1],
            [
                -Fr::from((HEADERS[copy - 12] as u64) & 1),
                Fr::one(),
                Fr::zero(),
                Fr::zero()
            ]
        );
    }
    let first = &c.natural.terms[0];
    let rb = boolean(
        sparse_stream_roster::global_edge_row(AUX, 1 << 19, 4, 19, 1, &MEMBER_ROWS).unwrap(),
        24,
    );
    let ub = boolean(AUX * WIDTH + first.gate.left, 24);
    let vb = boolean(AUX * WIDTH + first.gate.right, 24);
    assert_ne!(
        c.arithmetic_coefficients(&rb, &ub, &vb).unwrap(),
        [Fr::zero(); 4]
    );
    for bit in 20..24 {
        let mut wrong = ub.clone();
        wrong[bit] = Fr::one() - wrong[bit];
        assert_eq!(
            c.arithmetic_coefficients(&rb, &wrong, &vb).unwrap(),
            [Fr::zero(); 4]
        );
        let mut wrong = vb.clone();
        wrong[bit] = Fr::one() - wrong[bit];
        assert_eq!(
            c.arithmetic_coefficients(&rb, &ub, &wrong).unwrap(),
            [Fr::zero(); 4]
        );
    }
    for bit in [17, 18, 22, 23] {
        let mut wrong = rb.clone();
        wrong[bit] = Fr::one() - wrong[bit];
        assert_eq!(
            c.arithmetic_coefficients(&wrong, &ub, &vb).unwrap(),
            [Fr::zero(); 4]
        );
    }
    assert!(c.parts(&r[..23], &u, &v).is_err());
    assert_eq!(
        c.aliases(|_| Err("sink-stop".into())).unwrap_err(),
        "sink-stop"
    );
    assert_eq!(
        c.arithmetic(|_| Err("sink-stop".into())).unwrap_err(),
        "sink-stop"
    );
    println!("reset four-family finite full24 references949510+64+12060+64; mixedowners,64ports,high-zero factors,offsets,padding,arithmeticcopybothsides passed");
}

fn pack_native(c: &Context) -> PackedFile {
    let (fixture, headers) = crate::header_history_boundary::tests::fixture();
    let serializer = serializer::build(None).unwrap();
    let (a, b) = super::native_pair();
    let carry = daa_integer::compile_carry(&crate::daa_count::q(), a, b, true).unwrap();
    super::assert_zero(&carry);
    let fixed = native_helper();
    assert_eq!(fixed.circuit, c.expected.circuit);
    assert!(residues(&c.natural, &fixed.witness)
        .iter()
        .all(Zero::is_zero));
    let path = super::super::super::artifact("fixed-packed", "bin");
    let mut writer = PackedFileWriter::create_new(&path, 24).unwrap();
    for copy in 0..16 {
        let mut input = if copy == 9 || copy == 10 {
            crate::header_history_boundary::tests::assignment_for_child(
                c.base.base.base.heights[copy],
                &fixture,
                &headers,
            )
        } else if copy == 12 || copy == 13 {
            reset_assignment(HEADERS[copy - 12])
        } else {
            vec![Fr::zero(); WIDTH]
        };
        if copy < 9 {
            let h =
                ergo_header_core::Header::decode(&headers[&c.base.base.base.heights[copy]], None)
                    .unwrap();
            let fields = serializer::Fields::from_header(&h).unwrap();
            let bits = serializer.assign(&fields);
            input[header_hash::SERIALIZER_OFFSET..header_hash::SERIALIZER_OFFSET + bits.len()]
                .copy_from_slice(&bits);
        } else if copy == CARRY_AUX {
            input[..carry.witness.len()].copy_from_slice(&carry.witness);
        } else if copy == AUX {
            input[..fixed.witness.len()].copy_from_slice(&fixed.witness);
        }
        assert_eq!(input.len(), WIDTH);
        writer.write_bytes(&helpers::pack_bits(&input)).unwrap();
    }
    writer.finish().unwrap()
}
fn verify(
    proof: &GkrProof,
    key: &[u8; 32],
    commitment: &[u8],
) -> Result<(InputClaim, Transcript), String> {
    verify_for_rule(NumericRule::FixedReset, proof, key, commitment)
}
fn verify_for_rule(
    rule: NumericRule,
    proof: &GkrProof,
    key: &[u8; 32],
    commitment: &[u8],
) -> Result<(InputClaim, Transcript), String> {
    let c = Context::for_rule(rule)?;
    let mut t = Transcript::new(rule.domain());
    let claim = gkr::verify_with_wiring(
        &[24],
        1 << 24,
        proof,
        &mut t,
        |t| c.bind(t, key, commitment, &c.bound_target()),
        |_, r, u, v| {
            c.coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        },
    )
    .map_err(|e| e.to_string())?;
    Ok((claim, t))
}
fn anchors_coefficients(c: &Context, r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    let mut out = [Fr::zero(); 4];
    for b in 0..256 {
        let term = &c.natural.terms[c.expected.count.terms + b];
        let global = sparse_stream_roster::global_edge_row(
            AUX,
            (1 << 19) | term.row,
            4,
            19,
            1,
            &MEMBER_ROWS,
        )
        .unwrap();
        let w = eq(r, global)
            * eq(u, AUX * WIDTH + term.gate.left)
            * eq(v, AUX * WIDTH + term.gate.right);
        out[0] += w * term.gate.c0;
        out[1] += w * term.gate.c1;
    }
    out
}

#[test]
fn native_common_fixed_v2_one_gkr_pcs_and_single_anchor_fault() {
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
    let commitment = pcs::encode_commitment(&committed.commitment).unwrap();
    let commit_ms = mark.elapsed().as_millis();
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
            c.visit(left, copy, |e| {
                visits += 1;
                sink(e)
            })
        },
        |copy| {
            loads += 1;
            super::super::load(&source, copy)
        },
        &mut t,
        |t| c.bind(t, &setup.id, &commitment, &target()),
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
        assert_eq!(io.read_bytes, 6291456);
    }
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
    let mut open_t = t.clone();
    let mark = Instant::now();
    let opening = packed::open(&committed, &source, &claim.point, &setup, &mut open_t).unwrap();
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
        open_t.challenge_scalar(b"post-pcs"),
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
    for missing in ["anchors", "one-alias"] {
        let mut omitted = Transcript::new(DOMAIN);
        let err = gkr::verify_with_wiring(
            &[24],
            1 << 24,
            &proof,
            &mut omitted,
            |t| c.bind(t, &setup.id, &commitment, &target()),
            |_, r, u, v| {
                let mut out = c.coefficients(r, u, v).unwrap();
                if missing == "anchors" {
                    let a = anchors_coefficients(&c, r, u, v);
                    for i in 0..4 {
                        out[i] -= a[i];
                    }
                } else {
                    let (l, h) = c.port(0);
                    let rr =
                        sparse_stream_roster::global_edge_row(AUX, ALIAS, 4, 19, 1, &MEMBER_ROWS)
                            .unwrap();
                    let w = eq(r, rr) * eq(u, l) * eq(v, h);
                    out[1] -= w;
                    out[2] += w;
                }
                Ok(out)
            },
        )
        .unwrap_err();
        assert_eq!(err, gkr::GkrError::TerminalExpression, "{missing}");
    }
    let mut wrong_context = Transcript::new(DOMAIN);
    let wrong_target = target() + BigUint::one();
    assert_eq!(
        gkr::verify_with_wiring(
            &[24],
            1 << 24,
            &proof,
            &mut wrong_context,
            |t| c.bind(t, &setup.id, &commitment, &wrong_target),
            |_, r, u, v| c
                .coefficients(r, u, v)
                .map_err(|_| gkr::GkrError::PointDimension)
        )
        .unwrap_err(),
        gkr::GkrError::SumcheckIdentity
    );
    let anchor = &c.natural.terms[c.expected.count.terms];
    assert_eq!(anchor.row, ANCHOR);
    assert!(anchor.gate.c0.is_zero());
    assert_eq!(anchor.gate.c1, Fr::one());
    assert!(anchor.gate.c2.is_zero() && anchor.gate.c3.is_zero());
    let wire = AUX * WIDTH + anchor.gate.left;
    let x = source.read_copy(1 << 16, wire / (1 << 16)).unwrap()[wire % (1 << 16)];
    assert!(x.is_zero());
    assert_eq!(anchor.gate.c0 + anchor.gate.c1 * x, Fr::zero());
    assert_eq!(-Fr::one() + anchor.gate.c1 * x, -Fr::one());
    let mut false_t = Transcript::new(DOMAIN);
    let invalid = sparse_stream_roster::prove_edge_terms(
        20,
        4,
        19,
        1,
        &MEMBER_ROWS,
        |left, copy, sink| {
            c.visit(left, copy, |mut e| {
                if e.source_slot == AUX && e.family_row == ((1 << 19) | ANCHOR) {
                    e.term.gate.c0 = -Fr::one();
                }
                sink(e)
            })
        },
        |copy| super::super::load(&source, copy),
        &mut false_t,
        |t| c.bind(t, &setup.id, &commitment, &target()),
        |r, u, v| c.coefficients(r, u, v),
    );
    assert_eq!(
        invalid.unwrap_err(),
        gkr::GkrError::SumcheckIdentity.to_string()
    );
    let gkr_bytes = gkr::encode_proof(&proof).unwrap();
    let pcs_bytes = pcs::encode_proof(&opening).unwrap();
    for (kind, bytes) in [
        ("fixed-gkr", gkr_bytes.as_slice()),
        ("fixed-pcs", pcs_bytes.as_slice()),
        ("fixed-test-key", key.as_slice()),
    ] {
        helpers::write_create_new(&super::super::super::artifact(kind, "bin"), bytes);
    }
    let receipt = serde_json::json!({"profile":"bounded Mainnet twoFixedV2 header owners plus carry","target_numeric_hex":"6f98d5000000","compact":"066f98d5","activation_height":H,"header_copies":13,"auxiliary_copies":2,"unused_copy":15,"fixed_auxiliary_copy":AUX,"terms":c.total(),"added_terms":961698,"fixed_arithmetic_terms":12060,"target_anchors":256,"aliases":64,"fixed_fingerprint":c.fingerprint,"natural_input":4096,"natural_rows":16384,"padded_input_bits":20,"padded_row_bits":17,"input_bits":24,"row_bits":24,"context_ms":context_ms,"packing_ms":packing_ms,"setup_ms":setup_ms,"commit_ms":commit_ms,"gkr_ms":gkr_ms,"full_consumer_ms":consumer_ms,"mle_ms":mle_ms,"opening_ms":opening_ms,"pcs_verify_ms":pcs_verify_ms,"whole_ms":whole.elapsed().as_millis(),"loader_calls":loads,"endpoint_passes":passes,"term_visits":visits,"packed_reads":io.read_calls,"packed_read_bytes":io.read_bytes,"incremental_u":inc_u,"incremental_v":inc_v,"gkr_bytes":gkr_bytes.len(),"pcs_bytes":pcs_bytes.len(),"setup_id":setup.id.iter().map(|b|format!("{b:02x}")).collect::<String>(),"authority_ceiling":"selected Mainnet reset pairs only; history/hash/global DAA/adjacency/fullchain/final parameters/integration not proven"});
    println!("{receipt}");
    helpers::write_create_new(
        &super::super::super::artifact("fixed-receipt", "json"),
        receipt.to_string().as_bytes(),
    );
}

#[path = "early_singleton_join_tests.rs"]
mod early_singleton_join_tests;

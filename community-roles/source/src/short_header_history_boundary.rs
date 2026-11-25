//! Canonical header boundary with one explicitly selected short DAA owner.
//! This structural adapter does not authenticate a chain or include its
//! arithmetic/import lanes in a common GKR/PCS proof.
use crate::{
    header_history_boundary::HeaderHistoryBoundary,
    short_daa_layout::{Profile, ShortDaaLayout},
    sparse::Term,
    transcript::Transcript,
    wiring::{self, RightIndex},
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};

const ROW_BITS: usize = 19;
const INPUT_BITS: usize = 20;
const ROWS: usize = 1 << ROW_BITS;
const CANONICAL_TERMS: usize = 474_755;
const A4_ROWS: std::ops::Range<usize> = 348_440..356_632;
const A4_WIRES: std::ops::Range<usize> = 991_232..999_424;
const A4_COUNT: usize = 8192;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct Counts {
    pub(crate) emitted: usize,
    pub(crate) omitted_mature_a4: usize,
    pub(crate) omitted_short_a4: usize,
}

pub(crate) struct ShortHeaderHistoryBoundary {
    base: HeaderHistoryBoundary,
    short: ShortDaaLayout,
    target: u64,
}
impl ShortHeaderHistoryBoundary {
    pub(crate) fn compile(profile: Profile, headers: u64, slot_log: usize) -> Result<Self, String> {
        // Short admission rejects invalid dimensions before either large build.
        let short = ShortDaaLayout::compile(profile, headers, slot_log)?;
        let base = HeaderHistoryBoundary::compile(headers, slot_log)?;
        validate_anchors(&base.canonical_circuit().terms)?;
        Ok(Self {
            base,
            short,
            target: (profile.child_height() - 1) as u64,
        })
    }
    pub(crate) fn short_layout(&self) -> &ShortDaaLayout {
        &self.short
    }
    pub(crate) fn base(&self) -> &HeaderHistoryBoundary {
        &self.base
    }
    pub(crate) fn bind(&self, t: &mut Transcript) {
        t.append_bytes(b"short-header-overlay", b"one-short-owner-additive-a4-v1");
        t.append_bytes(b"header-template", self.base.fingerprint().as_bytes());
        t.append_bytes(
            b"header-base-release-rule",
            b"code-owned-mature-legacy-eip-a4-only-v1",
        );
        for value in [
            self.base.history_slots(),
            self.base.slot_log() as u64,
            self.target,
            ROW_BITS as u64,
            INPUT_BITS as u64,
            A4_ROWS.start as u64,
            A4_ROWS.end as u64,
            A4_WIRES.start as u64,
            A4_WIRES.end as u64,
        ] {
            t.append_bytes(b"short-header-coordinate", &value.to_le_bytes());
        }
        self.short.bind(t);
    }
    pub(crate) fn visit_slot_terms(
        &self,
        slot: u64,
        mut sink: impl FnMut(Term) -> Result<(), String>,
    ) -> Result<Counts, String> {
        let row_base = usize::try_from(slot)
            .ok()
            .and_then(|s| s.checked_mul(ROWS))
            .ok_or("short header row offset overflow")?;
        let mut omitted = 0usize;
        let base = self.base.visit_slot_terms(slot, |term| {
            let local = term
                .row
                .checked_sub(row_base)
                .ok_or("short header row precedes its slot")?;
            if slot == self.target && A4_ROWS.contains(&local) {
                omitted = omitted
                    .checked_add(1)
                    .ok_or("short omission count overflow")?;
                return Ok(());
            }
            sink(term)
        })?;
        let expected = if slot == self.target { A4_COUNT } else { 0 };
        if omitted != expected || (slot == self.target && base.omitted_a4 != 0) {
            return Err("short header A4 omission inventory changed".into());
        }
        let emitted = base
            .emitted
            .checked_sub(omitted)
            .ok_or("short header emission underflow")?;
        let total = emitted
            .checked_add(base.omitted_a4)
            .and_then(|v| v.checked_add(omitted))
            .ok_or("short header inventory overflow")?;
        if total != CANONICAL_TERMS {
            return Err("short header canonical inventory changed".into());
        }
        Ok(Counts {
            emitted,
            omitted_mature_a4: base.omitted_a4,
            omitted_short_a4: omitted,
        })
    }
    pub(crate) fn release_coefficient(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<Fr, String> {
        let slots = self.base.slot_log();
        if r.len() != ROW_BITS + slots
            || u.len() != INPUT_BITS + slots
            || v.len() != INPUT_BITS + slots
        {
            return Err("short header release point dimensions rejected".into());
        }
        let mut padded_r = r[..ROW_BITS].to_vec();
        padded_r.push(Fr::zero());
        let zeros = vec![Fr::zero(); INPUT_BITS];
        let local = wiring::evaluate_shift(
            &u[..INPUT_BITS],
            &padded_r,
            &zeros,
            (A4_WIRES.start - A4_ROWS.start) as u64,
            A4_WIRES.start as u64,
            A4_WIRES.end as u64,
            0,
            RightIndex::GlobalZero,
        )? * eq(&v[..INPUT_BITS], 0);
        Ok(local
            * eq(&r[ROW_BITS..], self.target)
            * eq(&u[INPUT_BITS..], self.target)
            * eq(&v[INPUT_BITS..], self.target))
    }
    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String> {
        let release = self.release_coefficient(r, u, v)?;
        let mut out = self.base.coefficients(r, u, v)?;
        out[1] -= release;
        Ok(out)
    }
}

fn validate_anchors(terms: &[Term]) -> Result<(), String> {
    let mut count = 0usize;
    for t in terms.iter().filter(|t| A4_ROWS.contains(&t.row)) {
        if t.row != A4_ROWS.start + count
            || t.gate.left != A4_WIRES.start + count
            || t.gate.right != 0
            || [t.gate.c0, t.gate.c1, t.gate.c2, t.gate.c3]
                != [Fr::zero(), Fr::one(), Fr::zero(), Fr::zero()]
        {
            return Err("short header canonical A4 anchors changed".into());
        }
        count += 1;
    }
    if count != A4_COUNT {
        return Err("short header canonical A4 anchor count changed".into());
    }
    Ok(())
}
fn eq(p: &[Fr], i: u64) -> Fr {
    p.iter().enumerate().fold(Fr::one(), |acc, (bit, x)| {
        acc * if i >> bit & 1 == 1 { *x } else { Fr::one() - x }
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        daa_count, daa_finish, daa_history_layout, daa_integer::TwoRatioInputs,
        header_compact_links, header_hash, serializer,
    };
    const WIDTH: usize = 1 << INPUT_BITS;
    fn boolean(n: usize, i: u64) -> Vec<Fr> {
        (0..n).map(|b| Fr::from(i >> b & 1)).collect()
    }

    #[test]
    fn streams_preserve_neighbors_padding_and_both_mature_families() {
        let family = ShortHeaderHistoryBoundary::compile(Profile::M2, 1_234_568, 21).unwrap();
        for slot in [3072, 3071, 3073, 9216, 844672, 844800, (1 << 21) - 1] {
            let mut expected = Vec::new();
            let base = family
                .base
                .visit_slot_terms(slot, |t| {
                    expected.push(t);
                    Ok(())
                })
                .unwrap();
            if slot == family.target {
                expected.retain(|t| !A4_ROWS.contains(&(t.row - slot as usize * ROWS)));
            }
            let mut index = 0;
            let got = family
                .visit_slot_terms(slot, |t| {
                    assert_eq!(Some(&t), expected.get(index));
                    index += 1;
                    Ok(())
                })
                .unwrap();
            assert_eq!(got.emitted, expected.len());
            assert_eq!(index, expected.len());
            assert_eq!(got.omitted_mature_a4, base.omitted_a4);
            assert_eq!(got.omitted_short_a4, if slot == 3072 { 8192 } else { 0 });
            if [9216, 844672, 844800].contains(&slot) {
                assert_eq!(got.omitted_mature_a4, 8192);
            }
            assert_eq!(
                got.emitted + got.omitted_mature_a4 + got.omitted_short_a4,
                CANONICAL_TERMS
            );
        }
        let mut calls = 0;
        assert_eq!(
            family
                .visit_slot_terms(1 << 21, |_| {
                    calls += 1;
                    Ok(())
                })
                .err()
                .as_deref(),
            Some("header slot is outside the declared power-of-two domain")
        );
        assert_eq!(calls, 0);
        assert_eq!(
            family
                .visit_slot_terms(u64::MAX, |_| {
                    calls += 1;
                    Ok(())
                })
                .err()
                .as_deref(),
            Some("short header row offset overflow")
        );
        assert_eq!(calls, 0);
        assert_eq!(
            family
                .visit_slot_terms(3072, |_| {
                    calls += 1;
                    Err("fixture sink stop".into())
                })
                .err()
                .as_deref(),
            Some("fixture sink stop")
        );
        assert_eq!(calls, 1);
    }

    #[test]
    fn release_coefficients_match_exact_anchor_enumeration_and_boundaries() {
        let f = ShortHeaderHistoryBoundary::compile(Profile::M2, 3074, 12).unwrap();
        let mixed = |n, seed| {
            (0..n)
                .map(|i| Fr::from(seed + 7 * i as u64))
                .collect::<Vec<_>>()
        };
        let r = mixed(31, 3);
        let u = mixed(32, 31);
        let v = mixed(32, 97);
        let rw = crate::gkr::eq_weights(&r[..19]);
        let uw = crate::gkr::eq_weights(&u[..20]);
        let vw = crate::gkr::eq_weights(&v[..20]);
        let mut sum = Fr::zero();
        let mut count = 0;
        for t in f
            .base
            .canonical_circuit()
            .terms
            .iter()
            .filter(|t| A4_ROWS.contains(&t.row))
        {
            sum += rw[t.row] * uw[t.gate.left] * vw[t.gate.right];
            count += 1;
        }
        assert_eq!(count, 8192);
        let expected = sum * eq(&r[19..], 3072) * eq(&u[20..], 3072) * eq(&v[20..], 3072);
        assert_eq!(f.release_coefficient(&r, &u, &v).unwrap(), expected);
        let base = f.base.coefficients(&r, &u, &v).unwrap();
        let got = f.coefficients(&r, &u, &v).unwrap();
        assert_eq!(got, [base[0], base[1] - expected, base[2], base[3]]);
        for fault in 0..4 {
            let mut a = r.clone();
            let mut b = u.clone();
            let mut c = v.clone();
            match fault {
                0 => a[19..].copy_from_slice(&boolean(12, 3073)),
                1 => b[20..].copy_from_slice(&boolean(12, 3073)),
                2 => c[20..].copy_from_slice(&boolean(12, 3073)),
                _ => c[..20].copy_from_slice(&boolean(20, 1)),
            }
            assert!(f.release_coefficient(&a, &b, &c).unwrap().is_zero());
        }
        for row in [
            A4_ROWS.start - 1,
            A4_ROWS.start,
            A4_ROWS.end - 1,
            A4_ROWS.end,
        ] {
            let mut a = boolean(19, row as u64);
            a.extend(boolean(12, 3072));
            let wire = row + A4_WIRES.start - A4_ROWS.start;
            let mut b = boolean(20, wire as u64);
            b.extend(boolean(12, 3072));
            let mut c = boolean(20, 0);
            c.extend(boolean(12, 3072));
            assert_eq!(
                f.release_coefficient(&a, &b, &c).unwrap(),
                Fr::from(A4_ROWS.contains(&row) as u64)
            );
        }
        for fault in 0..3 {
            let mut a = r.clone();
            let mut b = u.clone();
            let mut c = v.clone();
            match fault {
                0 => {
                    a.pop();
                }
                1 => {
                    b.pop();
                }
                _ => {
                    c.pop();
                }
            }
            assert_eq!(
                f.coefficients(&a, &b, &c).err().as_deref(),
                Some("short header release point dimensions rejected")
            );
        }
        let mut anchors = f
            .base
            .canonical_circuit()
            .terms
            .iter()
            .filter(|t| A4_ROWS.contains(&t.row))
            .cloned()
            .collect::<Vec<_>>();
        validate_anchors(&anchors).unwrap();
        let saved = anchors[0].clone();
        for fault in 0..7 {
            let t = &mut anchors[0];
            match fault {
                0 => t.row += 1,
                1 => t.gate.left += 1,
                2 => t.gate.right += 1,
                3 => t.gate.c0 += Fr::one(),
                4 => t.gate.c1 += Fr::one(),
                5 => t.gate.c2 += Fr::one(),
                _ => t.gate.c3 += Fr::one(),
            }
            assert_eq!(
                validate_anchors(&anchors).err().as_deref(),
                Some("short header canonical A4 anchors changed")
            );
            anchors[0] = saved.clone();
        }
        let last = anchors.pop().unwrap();
        assert_eq!(
            validate_anchors(&anchors).err().as_deref(),
            Some("short header canonical A4 anchor count changed")
        );
        anchors.push(last);
        anchors.swap(0, 1);
        assert_eq!(
            validate_anchors(&anchors).err().as_deref(),
            Some("short header canonical A4 anchors changed")
        );
        anchors.swap(0, 1);
        validate_anchors(&anchors).unwrap();
    }

    #[test]
    fn real_child3073_replaces_nonzero_a4_and_isolates_source_field_faults() {
        let f = ShortHeaderHistoryBoundary::compile(Profile::M2, 3074, 12).unwrap();
        let raws = crate::daa_two_ratio_join::fixture_raws();
        let hs = raws
            .iter()
            .map(|r| ergo_header_core::Header::decode(r, None).unwrap())
            .collect::<Vec<_>>();
        let compiled = daa_finish::compile_two_finish_with_child(
            &daa_count::q(),
            TwoRatioInputs {
                nbits: [hs[1].n_bits, hs[2].n_bits],
                timestamps: [hs[0].timestamp, hs[1].timestamp, hs[2].timestamp],
            },
            hs[3].n_bits,
            true,
        )
        .unwrap();
        let mapped = f.short_layout().admit(&compiled).unwrap();
        let fields = serializer::Fields::from_header(&hs[3]).unwrap();
        let mut child = daa_history_layout::full_header_boundary(Some(&fields)).unwrap();
        header_compact_links::assign_order(&mut child, &fields, 3072, hs[2].timestamp, false)
            .unwrap();
        let mut input = child.base.base.base.input.take().unwrap();
        for (start, end) in mapped.phase_bank_ranges() {
            input[start..end].copy_from_slice(&mapped.witness()[start..end]);
        }
        let mut arithmetic = vec![Fr::zero(); mapped.circuit().row_count];
        for t in &mapped.circuit().terms {
            arithmetic[t.row] += t.gate.evaluate(&input);
        }
        assert!(arithmetic.iter().all(Zero::is_zero));
        let anchored = f
            .base
            .canonical_circuit()
            .terms
            .iter()
            .find(|t| A4_ROWS.contains(&t.row) && !input[t.gate.left].is_zero())
            .expect("real short A4 has a nonzero anchored cell");
        assert_eq!(anchored.gate.evaluate(&input), Fr::one());
        let mut residual = vec![Fr::zero(); ROWS];
        let mut reinserted = false;
        let counts = f
            .visit_slot_terms(3072, |mut t| {
                t.row -= 3072 * ROWS;
                t.gate.left -= 3072 * WIDTH;
                t.gate.right -= 3072 * WIDTH;
                reinserted |= t.row == anchored.row;
                residual[t.row] += t.gate.evaluate(&input);
                Ok(())
            })
            .unwrap();
        let bad = residual
            .iter()
            .enumerate()
            .filter_map(|(row, r)| (!r.is_zero()).then_some(row))
            .collect::<Vec<_>>();
        assert!(
            bad.is_empty(),
            "retained header residuals: {:?}",
            &bad[..bad.len().min(16)]
        );
        assert_eq!(counts.omitted_short_a4, 8192);
        assert!(!reinserted);
        residual[anchored.row] += anchored.gate.evaluate(&input);
        assert_eq!(
            residual
                .iter()
                .enumerate()
                .filter_map(|(row, r)| (!r.is_zero()).then_some(row))
                .collect::<Vec<_>>(),
            vec![anchored.row]
        );
        let mut serializers = hs[..3]
            .iter()
            .map(|h| {
                serializer::build(Some(&serializer::Fields::from_header(h).unwrap()))
                    .unwrap()
                    .input
                    .unwrap()
            })
            .collect::<Vec<_>>();
        let owners = [1023, 2047, 3071];
        let mut aliases = Vec::new();
        f.short_layout()
            .visit_alias_terms(|t| {
                aliases.push(t);
                Ok(())
            })
            .unwrap();
        let alias_failures = |sources: &Vec<Vec<Fr>>| {
            aliases
                .iter()
                .enumerate()
                .filter_map(|(index, t)| {
                    let owner = t.gate.left / WIDTH;
                    let wire = t.gate.left % WIDTH;
                    let left = if owner == 3072 {
                        input[wire]
                    } else {
                        let source = owners
                            .iter()
                            .position(|o| *o == owner)
                            .expect("known physical M2 sample");
                        sources[source][wire - header_hash::SERIALIZER_OFFSET]
                    };
                    let right = input[t.gate.right % WIDTH];
                    (!(left - right).is_zero()).then_some(index)
                })
                .collect::<Vec<_>>()
        };
        assert!(alias_failures(&serializers).is_empty());
        for index in [0, 192] {
            let t = &aliases[index];
            let source = owners
                .iter()
                .position(|o| *o == t.gate.left / WIDTH)
                .unwrap();
            let wire = t.gate.left % WIDTH - header_hash::SERIALIZER_OFFSET;
            let old = serializers[source][wire];
            serializers[source][wire] = Fr::one() - old;
            assert_eq!(alias_failures(&serializers), vec![index]);
            serializers[source][wire] = old;
        }
        assert!(alias_failures(&serializers).is_empty());
    }

    fn selected_profiles(profiles: &[Profile]) {
        let mut challenges = std::collections::BTreeSet::new();
        for &p in profiles {
            let n = p.child_height() as u64;
            let s = n.next_power_of_two().trailing_zeros() as usize;
            let f = ShortHeaderHistoryBoundary::compile(p, n, s).unwrap();
            let counts = f.visit_slot_terms(n - 1, |_| Ok(())).unwrap();
            assert_eq!(
                (counts.omitted_short_a4, counts.omitted_mature_a4),
                (8192, 0)
            );
            let mut t = Transcript::new(b"short-header-tests-v1");
            f.bind(&mut t);
            let challenge = format!("{:?}", t.challenge_scalar(b"joined-consumer"));
            assert!(challenges.insert(challenge.clone()));
            println!(
                "{}",
                serde_json::json!({"kind":"short-owner-context","profile":format!("{p:?}"),"headers":n,"slotLog":s,"challenge":challenge})
            );
        }
    }
    #[test]
    fn selected_profiles_m2_m3_m4_bind_distinct_owners() {
        selected_profiles(&[Profile::M2, Profile::M3, Profile::M4]);
    }
    #[test]
    fn selected_profiles_m5_m6_m7_bind_distinct_owners() {
        selected_profiles(&[Profile::M5, Profile::M6, Profile::M7]);
    }
    #[test]
    fn domains_change_the_bound_transcript_and_reject_invalid_counts() {
        for (n, s) in [(3072, 12), (3073, 13), (4097, 12), (1 << 22, 22)] {
            assert_eq!(
                ShortHeaderHistoryBoundary::compile(Profile::M2, n, s)
                    .err()
                    .as_deref(),
                Some("short DAA history count or slot domain rejected")
            );
        }
        let mut challenges = std::collections::BTreeSet::new();
        for n in [3073, 3074, 4097] {
            let s = (n as u64).next_power_of_two().trailing_zeros() as usize;
            let f = ShortHeaderHistoryBoundary::compile(Profile::M2, n, s).unwrap();
            let mut t = Transcript::new(b"short-header-tests-v1");
            f.bind(&mut t);
            assert!(challenges.insert(format!("{:?}", t.challenge_scalar(b"joined-consumer"))));
        }
    }
}

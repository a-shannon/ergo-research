use crate::{
    daa_count,
    daa_finish::{self, CompiledFinish},
    daa_integer::{ShortLegacyProfile, TwoRatioInputs},
    header_hash,
    mapped_daa_plan::MappedDaaPlan,
    serializer,
    short_daa_layout::{Profile, ShortDaaLayout},
    sparse::Term,
    transcript::Transcript,
};
use ark_bn254::Fr;
use ark_ff::{One, Zero};

fn actual(profile: Profile) -> CompiledFinish {
    if profile == Profile::M2 {
        let hs: Vec<_> = crate::daa_two_ratio_join::fixture_raws()
            .iter()
            .map(|r| ergo_header_core::Header::decode(r, None).unwrap())
            .collect();
        daa_finish::compile_two_finish_with_child(
            &daa_count::q(),
            TwoRatioInputs {
                nbits: [hs[1].n_bits, hs[2].n_bits],
                timestamps: [hs[0].timestamp, hs[1].timestamp, hs[2].timestamp],
            },
            hs[3].n_bits,
            true,
        )
        .unwrap()
    } else {
        let (native, compact) = match profile {
            Profile::M3 => (ShortLegacyProfile::M3, 0x0700_be31),
            Profile::M4 => (ShortLegacyProfile::M4, 0x0700_bd4a),
            Profile::M5 => (ShortLegacyProfile::M5, 0x0700_b138),
            Profile::M6 => (ShortLegacyProfile::M6, 0x0700_ab6f),
            Profile::M7 => (ShortLegacyProfile::M7, 0x0700_a288),
            Profile::M2 => unreachable!(),
        };
        daa_finish::compile_short_legacy_with_child(
            &daa_count::q(),
            crate::daa_integer::mainnet_short_legacy_test_inputs(native),
            compact,
            true,
        )
        .unwrap()
    }
}
fn log(n: u64) -> usize {
    n.next_power_of_two().trailing_zeros() as usize
}
fn ports(layout: &ShortDaaLayout) -> Vec<Term> {
    let mut out = Vec::new();
    assert_eq!(
        layout
            .visit_alias_terms(|t| {
                out.push(t);
                Ok(())
            })
            .unwrap(),
        out.len()
    );
    out
}
fn expected_ports(
    profile: Profile,
    c: &CompiledFinish,
    map: &MappedDaaPlan,
) -> Vec<(usize, usize)> {
    let fields = serializer::build(None).unwrap().layout.fields;
    let w = &c.joined.joined.joined;
    let target = profile.child_height() - 1;
    let width = 1usize << 20;
    let mut out = Vec::new();
    for i in 0..=profile.count() {
        let bits = if i == profile.count() {
            &w.external[i - 1].end_timestamp
        } else {
            &w.external[i].start_timestamp
        };
        for bit in 0..64 {
            out.push((
                ((i + 1) * 1024 - 1) * width
                    + header_hash::SERIALIZER_OFFSET
                    + fields.timestamp[bit],
                target * width + map.mapped_wire(bits[bit]).unwrap(),
            ));
        }
    }
    for i in 0..profile.count() {
        for bit in 0..32 {
            out.push((
                ((i + 2) * 1024 - 1) * width + header_hash::SERIALIZER_OFFSET + fields.n_bits[bit],
                target * width + map.mapped_wire(w.external[i].nbits[bit]).unwrap(),
            ));
        }
    }
    for bit in 0..32 {
        out.push((
            target * width + header_hash::SERIALIZER_OFFSET + fields.n_bits[bit],
            target * width + map.mapped_wire(c.child_nbits.unwrap()[bit]).unwrap(),
        ));
    }
    out
}
fn eq(p: &[Fr], i: usize) -> Fr {
    p.iter().enumerate().fold(Fr::one(), |v, (b, x)| {
        v * if i >> b & 1 == 1 { *x } else { Fr::one() - x }
    })
}
fn boolean(n: usize, i: usize) -> Vec<Fr> {
    (0..n).map(|b| Fr::from((i >> b & 1) as u64)).collect()
}

#[test]
fn all_six_actual_profiles_admit_with_exact_physical_ports() {
    for p in [
        Profile::M2,
        Profile::M3,
        Profile::M4,
        Profile::M5,
        Profile::M6,
        Profile::M7,
    ] {
        let n = p.child_height() as u64;
        let l = ShortDaaLayout::compile(p, n, log(n)).unwrap();
        let c = actual(p);
        let m = l.admit(&c).unwrap();
        assert_eq!(m.circuit(), l.mapped_relation());
        let expected = expected_ports(p, &c, &m);
        let ts = ports(&l);
        assert_eq!(ts.len(), 96 * (p.count() + 1));
        for (i, (t, (left, right))) in ts.iter().zip(expected).enumerate() {
            assert_eq!(
                (t.row, t.gate.left, t.gate.right),
                ((p.child_height() - 1) * 1024 + i, left, right)
            );
            assert_eq!(
                [t.gate.c0, t.gate.c1, t.gate.c2, t.gate.c3],
                [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
            );
        }
        let other = if p == Profile::M2 {
            Profile::M3
        } else {
            Profile::M2
        };
        let foreign = ShortDaaLayout::compile(other, 8193, 14).unwrap();
        assert_eq!(
            foreign.admit(&c).err().as_deref(),
            Some("short DAA profile source count mismatch")
        );
    }
}

#[test]
fn source_relation_handles_and_padding_fail_separately() {
    let l = ShortDaaLayout::compile(Profile::M2, 3073, 12).unwrap();
    let mut c = actual(Profile::M2);
    let reject = |c: &CompiledFinish, msg: &str| assert_eq!(l.admit(c).err().as_deref(), Some(msg));
    for i in 0..7 {
        let window = &mut c.joined.joined.joined;
        let saved = window.count.clone();
        match i {
            0 => window.count.live_bits += 1,
            1 => window.count.input_bits += 1,
            2 => window.count.padded_input_bits += 1,
            3 => window.count.residual_rows += 1,
            4 => window.count.padded_rows += 1,
            5 => window.count.terms += 1,
            _ => window.count.padding_bits += 1,
        }
        reject(&c, "short DAA native geometry or checkpoint mismatch");
        c.joined.joined.joined.count = saved;
    }
    for checkpoint in 0..3 {
        let inc = match checkpoint {
            0 => &mut c.increment,
            1 => &mut c.joined.increment,
            _ => &mut c.joined.joined.increment,
        };
        inc.before.live_bits += 1;
        reject(&c, "short DAA native geometry or checkpoint mismatch");
        let inc = match checkpoint {
            0 => &mut c.increment,
            1 => &mut c.joined.increment,
            _ => &mut c.joined.joined.increment,
        };
        inc.before.live_bits -= 1;
    }
    let saved = c.joined.joined.joined.circuit.as_ref().unwrap().terms[0].clone();
    for i in 0..7 {
        let t = &mut c.joined.joined.joined.circuit.as_mut().unwrap().terms[0];
        match i {
            0 => t.row += 1,
            1 => t.gate.left += 1,
            2 => t.gate.right += 1,
            3 => t.gate.c0 += Fr::one(),
            4 => t.gate.c1 += Fr::one(),
            5 => t.gate.c2 += Fr::one(),
            _ => t.gate.c3 += Fr::one(),
        }
        reject(&c, "short DAA native relation mismatch");
        c.joined.joined.joined.circuit.as_mut().unwrap().terms[0] = saved.clone();
    }
    let last = c
        .joined
        .joined
        .joined
        .circuit
        .as_mut()
        .unwrap()
        .terms
        .pop()
        .unwrap();
    reject(&c, "short DAA native relation mismatch");
    c.joined
        .joined
        .joined
        .circuit
        .as_mut()
        .unwrap()
        .terms
        .push(last.clone());
    c.joined
        .joined
        .joined
        .circuit
        .as_mut()
        .unwrap()
        .terms
        .push(last);
    reject(&c, "short DAA native relation mismatch");
    c.joined.joined.joined.circuit.as_mut().unwrap().terms.pop();
    c.joined
        .joined
        .joined
        .circuit
        .as_mut()
        .unwrap()
        .terms
        .swap(0, 1);
    reject(&c, "short DAA native relation mismatch");
    c.joined
        .joined
        .joined
        .circuit
        .as_mut()
        .unwrap()
        .terms
        .swap(0, 1);
    let second = c.joined.joined.joined.circuit.as_ref().unwrap().terms[1].clone();
    c.joined.joined.joined.circuit.as_mut().unwrap().terms[0] = second;
    reject(&c, "short DAA native relation mismatch");
    c.joined.joined.joined.circuit.as_mut().unwrap().terms[0] = saved;
    for i in 0..5 {
        let old = match i {
            0 => c.child_nbits.as_ref().unwrap()[0],
            1 => c.output.numeric_result[0],
            2 => c.joined.joined.joined.external[0].nbits[0],
            3 => c.joined.joined.joined.external[0].start_timestamp[0],
            _ => c.joined.joined.joined.external[0].end_timestamp[0],
        };
        let set = |c: &mut CompiledFinish, value| match i {
            0 => c.child_nbits.as_mut().unwrap()[0] = value,
            1 => c.output.numeric_result[0] = value,
            2 => c.joined.joined.joined.external[0].nbits[0] = value,
            3 => c.joined.joined.joined.external[0].start_timestamp[0] = value,
            _ => c.joined.joined.joined.external[0].end_timestamp[0] = value,
        };
        set(&mut c, old + 1);
        reject(&c, "short DAA native field handle mismatch");
        set(&mut c, old);
    }
    let live = c.joined.joined.joined.count.live_bits;
    c.joined.joined.joined.witness[live] = Fr::one();
    reject(&c, "short DAA native padding witness is nonzero");
    c.joined.joined.joined.witness[live] = Fr::zero();
    l.admit(&c).unwrap();
}

#[test]
fn canonical_domains_and_descriptors_separate_transcripts() {
    for (p, n, s) in [
        (Profile::M2, 3072, 12),
        (Profile::M2, 4097, 12),
        (Profile::M2, 3073, 13),
        (Profile::M7, 8193, 15),
        (Profile::M2, 1u64 << 22, 22),
        (Profile::M2, u64::MAX, 21),
    ] {
        assert_eq!(
            ShortDaaLayout::compile(p, n, s).err().as_deref(),
            Some("short DAA history count or slot domain rejected")
        );
    }
    let mut challenges = std::collections::BTreeSet::new();
    let mut descriptors = std::collections::BTreeSet::new();
    for (p, n) in [
        (Profile::M2, 3073),
        (Profile::M2, 3074),
        (Profile::M2, 4096),
        (Profile::M2, 4097),
        (Profile::M3, 4097),
    ] {
        let l = ShortDaaLayout::compile(p, n, log(n)).unwrap();
        assert!(descriptors.insert(l.descriptor()));
        let mut t = Transcript::new(b"short-admission-tests-v1");
        l.bind(&mut t);
        assert!(challenges.insert(format!("{:?}", t.challenge_scalar(b"consumer"))));
    }
}

#[test]
fn alias_mixed_points_boolean_coordinates_and_dimensions_match() {
    let l = ShortDaaLayout::compile(Profile::M2, 3073, 12).unwrap();
    let ts = ports(&l);
    let mixed = |n, seed| {
        (0..n)
            .map(|i| Fr::from(seed + i as u64 * 7))
            .collect::<Vec<_>>()
    };
    let r = mixed(22, 3);
    let u = mixed(32, 19);
    let v = mixed(32, 103);
    let mut expected = [Fr::zero(); 4];
    for t in &ts {
        let w = eq(&r, t.row) * eq(&u, t.gate.left) * eq(&v, t.gate.right);
        for (a, c) in expected
            .iter_mut()
            .zip([t.gate.c0, t.gate.c1, t.gate.c2, t.gate.c3])
        {
            *a += w * c;
        }
    }
    assert_eq!(l.alias_coefficients(&r, &u, &v).unwrap(), expected);
    for index in [0, 191, 192, 255, 256, 287] {
        let t = &ts[index];
        let r = boolean(22, t.row);
        let u = boolean(32, t.gate.left);
        let v = boolean(32, t.gate.right);
        assert_eq!(
            l.alias_coefficients(&r, &u, &v).unwrap(),
            [Fr::zero(), Fr::one(), -Fr::one(), Fr::zero()]
        );
        for fault in 0..6 {
            let mut a = r.clone();
            let mut b = u.clone();
            let mut c = v.clone();
            match fault {
                0 => a[10] = Fr::one() - a[10],
                1 => b[20] = Fr::one() - b[20],
                2 => c[20] = Fr::one() - c[20],
                3 => a[0] = Fr::one() - a[0],
                4 => b[0] = Fr::one() - b[0],
                _ => c[0] = Fr::one() - c[0],
            }
            assert_eq!(l.alias_coefficients(&a, &b, &c).unwrap(), [Fr::zero(); 4]);
        }
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
            l.alias_coefficients(&a, &b, &c).err().as_deref(),
            Some("short DAA alias point dimensions rejected")
        );
    }
    assert_eq!(
        l.arithmetic_coefficients(&r, &u, &v).err().as_deref(),
        Some("short DAA arithmetic point dimensions rejected")
    );
}

#[test]
fn arithmetic_embedded_term_differential_and_all_dimensions() {
    let l = ShortDaaLayout::compile(Profile::M2, 3073, 12).unwrap();
    let point = |n, seed| {
        (0..n)
            .map(|i| Fr::from(seed + 11 * i as u64))
            .collect::<Vec<_>>()
    };
    let r = point(29, 5);
    let u = point(32, 29);
    let v = point(32, 107);
    let rw = crate::gkr::eq_weights(&r[..17]);
    let uw = crate::gkr::eq_weights(&u[..20]);
    let vw = crate::gkr::eq_weights(&v[..20]);
    // Embed each actual term independently in the full physical slot domain.
    // Equality tables cover only local coordinates, never the history domain.
    let target = 3072;
    let factor = eq(&r[17..], target) * eq(&u[20..], target) * eq(&v[20..], target);
    let mut expected = [Fr::zero(); 4];
    for t in &l.mapped_relation().terms {
        let weight = rw[t.row] * uw[t.gate.left] * vw[t.gate.right] * factor;
        for (out, c) in expected
            .iter_mut()
            .zip([t.gate.c0, t.gate.c1, t.gate.c2, t.gate.c3])
        {
            *out += weight * c;
        }
    }
    assert_eq!(l.arithmetic_coefficients(&r, &u, &v).unwrap(), expected);
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
            l.arithmetic_coefficients(&a, &b, &c).err().as_deref(),
            Some("short DAA arithmetic point dimensions rejected")
        );
    }
    // Fix one wrong physical owner separately in each coordinate domain.
    for fault in 0..3 {
        let mut a = r.clone();
        let mut b = u.clone();
        let mut c = v.clone();
        match fault {
            0 => a[17..].copy_from_slice(&boolean(12, target + 1)),
            1 => b[20..].copy_from_slice(&boolean(12, target + 1)),
            _ => c[20..].copy_from_slice(&boolean(12, target + 1)),
        }
        assert_eq!(
            l.arithmetic_coefficients(&a, &b, &c).unwrap(),
            [Fr::zero(); 4]
        );
    }
}

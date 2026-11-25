//! Producer for the repeated canonical POINT circuit. A class is an exact
//! 1,024-byte slice of the held witness, including padding. Copy coordinates
//! are kept for every owner and expanded before each high-coordinate fold.
use super::{copy_line_selector, finish_high, multiply_polynomials, quadratic_scaled_d,
            send_round, FirstPhase};
use crate::{gkr::{self, GkrProof, InputClaim, LayerProof}, sparse, transcript::Transcript};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use rayon::prelude::*;
use std::{collections::HashMap, sync::Arc};

const INPUT_BITS: usize = 13;
const ROW_BITS: usize = 14;
const BANK_BYTES: usize = 1 << (INPUT_BITS - 3);
type Bank = [u8; BANK_BYTES];

fn bit(bank: &Bank, wire: usize) -> bool {
    bank[wire / 8] & (1 << (wire % 8)) != 0
}

fn fields(bank: &Bank) -> Vec<Fr> {
    (0..1 << INPUT_BITS).map(|i| if bit(bank, i) { Fr::one() } else { Fr::zero() }).collect()
}

struct Copies {
    banks: Vec<Arc<Bank>>,
    owners: Vec<u32>,
}

impl Copies {
    fn read(count: usize, mut load: impl FnMut(usize) -> Result<Vec<u8>, String>) -> Result<Self, String> {
        let mut index = HashMap::<Arc<Bank>, u32>::new();
        let mut banks = Vec::new();
        let mut owners = Vec::with_capacity(count);
        for owner in 0..count {
            let bytes: Bank = load(owner)?.try_into().map_err(|_| "wrong packed POINT bank length")?;
            let class = if let Some(&class) = index.get(&bytes) {
                class
            } else {
                let class = u32::try_from(banks.len()).map_err(|_| "too many POINT classes")?;
                let data = Arc::new(bytes);
                index.insert(Arc::clone(&data), class);
                banks.push(data);
                class
            };
            owners.push(class);
        }
        Ok(Self { banks, owners })
    }

    fn class_weights(&self, weights: &[Fr]) -> Vec<Fr> {
        debug_assert_eq!(weights.len(), self.owners.len());
        let mut result = vec![Fr::zero(); self.banks.len()];
        for (&class, weight) in self.owners.iter().zip(weights) {
            result[class as usize] += weight;
        }
        result
    }

    fn check_residuals(&self, circuit: &sparse::Circuit) -> Result<(), String> {
        self.banks.par_iter().try_for_each_init(
            || vec![Fr::zero(); circuit.row_count],
            |rows, bank| {
                rows.fill(Fr::zero());
                for term in &circuit.terms {
                    let g = &term.gate;
                    let left = bit(bank, g.left);
                    let right = bit(bank, g.right);
                    let mut value = g.c0;
                    if left { value += g.c1; }
                    if right { value += g.c2; }
                    if left && right { value += g.c3; }
                    rows[term.row] += value;
                }
                if rows.iter().any(|x| !x.is_zero()) { return Err("nonzero POINT residual".to_owned()); }
                Ok(())
            })
    }
}

fn reduced_vectors(tables: &FirstPhase, bank: &Bank, low: &[Fr]) -> (Vec<Fr>, Vec<Fr>, Vec<Fr>) {
    let mut x = fields(bank);
    let (a, b) = tables.vectors(&x);
    for &coordinate in low { gkr::fold(&mut x, coordinate); }
    (a, b, x)
}

fn add_message(mut a: [Fr; 3], b: [Fr; 3]) -> [Fr; 3] {
    for (out, value) in a.iter_mut().zip(b) { *out += value; }
    a
}

fn first(circuit: &sparse::Circuit, copies: &Copies, rows: &[Fr], omega: &[Fr],
         claim: &mut Fr, rounds: &mut Vec<Vec<Fr>>, t: &mut Transcript) -> Result<(Vec<Fr>, Fr), String> {
    let weights = copies.class_weights(omega);
    let mut tables = FirstPhase::new_point(circuit, rows);
    let mut u = Vec::new();
    for _ in 0..INPUT_BITS {
        let message = copies.banks.par_iter().zip(&weights).map(|(bank, weight)| {
            let (a, b, x) = reduced_vectors(&tables, bank, &u);
            let m = gkr::quadratic_message(&a, &b, &x);
            [m[0] * weight, m[1] * weight, m[2] * weight]
        }).reduce(|| [Fr::zero(); 3], add_message);
        let next = send_round(message.to_vec(), claim, rounds, t).map_err(|e| e.to_string())?;
        tables.bind_low(next);
        u.push(next);
    }
    let local: Vec<_> = copies.banks.par_iter().map(|bank| {
        let (a, b, x) = reduced_vectors(&tables, bank, &u);
        (a[0], b[0], x[0])
    }).collect();
    drop(tables);
    let mut a = Vec::with_capacity(omega.len());
    let mut b = Vec::with_capacity(omega.len());
    let mut x = Vec::with_capacity(omega.len());
    for (&class, weight) in copies.owners.iter().zip(omega) {
        let (aa, bb, xx) = local[class as usize];
        a.push(aa * weight); b.push(bb * weight); x.push(xx);
    }
    let value = finish_high(a, b, x, &mut u, claim, rounds, t).map_err(|e| e.to_string())?;
    Ok((u, value))
}

fn add_vectors(mut a: Vec<Fr>, b: Vec<Fr>) -> Vec<Fr> {
    for (out, value) in a.iter_mut().zip(b) { *out += value; }
    a
}

fn set_wires(bank: &Bank, mut visit: impl FnMut(usize)) {
    for (byte_index, &byte) in bank.iter().enumerate() {
        let mut bits = byte;
        while bits != 0 {
            visit(byte_index * 8 + bits.trailing_zeros() as usize);
            bits &= bits - 1;
        }
    }
}

fn second(copies: &Copies, mut c: Vec<Fr>, mut d: Vec<Fr>, tau: &[Fr],
          claim: &mut Fr, rounds: &mut Vec<Vec<Fr>>, t: &mut Transcript) -> Result<(Vec<Fr>, Fr), String> {
    let weights = copies.class_weights(tau);
    let width = 1 << INPUT_BITS;
    let mut x_bar = copies.banks.par_iter().zip(&weights)
        .fold(|| vec![Fr::zero(); width], |mut sum, (bank, weight)| {
            set_wires(bank, |wire| sum[wire] += weight);
            sum
        }).reduce(|| vec![Fr::zero(); width], add_vectors);
    let sigma = tau.iter().copied().sum();
    let mut v = Vec::new();
    for _ in 0..INPUT_BITS {
        let m = quadratic_scaled_d(&c, &d, &x_bar, sigma);
        let next = send_round(m, claim, rounds, t).map_err(|e| e.to_string())?;
        gkr::fold(&mut c, next); gkr::fold(&mut d, next); gkr::fold(&mut x_bar, next);
        v.push(next);
    }
    let low = gkr::eq_weights(&v);
    let local: Vec<Fr> = copies.banks.par_iter().map(|bank| {
        let mut value = Fr::zero();
        set_wires(bank, |wire| value += low[wire]);
        value
    }).collect();
    let a = tau.iter().map(|weight| *weight * c[0]).collect();
    let b = tau.iter().map(|weight| *weight * d[0]).collect();
    let x = copies.owners.iter().map(|&class| local[class as usize]).collect();
    let value = finish_high(a, b, x, &mut v, claim, rounds, t).map_err(|e| e.to_string())?;
    Ok((v, value))
}

fn line(copies: &Copies, u: &[Fr], v: &[Fr]) -> Vec<Fr> {
    let (ul, uh) = u.split_at(INPUT_BITS);
    let (vl, vh) = v.split_at(INPUT_BITS);
    let local: Vec<_> = copies.banks.par_iter()
        .map(|bank| gkr::line_polynomial(&fields(bank), ul, vl)).collect();
    copies.owners.par_iter().enumerate()
        .fold(|| vec![Fr::zero(); u.len() + 1], |mut sum, (owner, &class)| {
            let selector = copy_line_selector(owner, uh, vh);
            let term = multiply_polynomials(&local[class as usize], &selector);
            for (out, value) in sum.iter_mut().zip(term) { *out += value; }
            sum
        }).reduce(|| vec![Fr::zero(); u.len() + 1], add_vectors)
}

pub(crate) fn check_resources(log_copies:usize,scratch_bytes:usize)->Result<(),String>{
    if !matches!(log_copies, 4 | 21) || rayon::current_num_threads() > 16 {
        return Err("unsupported canonical POINT producer geometry or worker count".into());
    }
    let count = 1usize << log_copies;
    // Even if all banks differ: allow 4 KiB per owner for the exact keys,
    // dictionary and dense/high/line tables, plus 512 MiB for circuit and workers.
    if scratch_bytes < count * 4096 + (512 << 20) { return Err("POINT scratch reservation".into()); }
    Ok(())
}

pub(crate) fn prove(circuit: &sparse::Circuit, log_copies: usize, scratch_bytes: usize,
                    load: impl FnMut(usize) -> Result<Vec<u8>, String>, t: &mut Transcript)
    -> Result<(GkrProof, InputClaim), String> {
    check_resources(log_copies,scratch_bytes)?;
    let count=1usize<<log_copies;
    sparse::validate_h21_point_window(circuit).map_err(|e| e.to_string())?;
    let shape = sparse::Shape { input_bits: INPUT_BITS, row_bits: ROW_BITS, copies: count,
        input_len: circuit.input_len * count, row_count: circuit.row_count * count };
    let began=std::time::Instant::now();
    let copies = Copies::read(count, load)?;
    if log_copies==21 {
        println!("H21_POINT_BANKS {}",serde_json::json!({"owners":count,"distinct_banks":copies.banks.len(),
            "bank_bytes":BANK_BYTES,"payload_bytes":count*BANK_BYTES,"grouping_ms":began.elapsed().as_millis()as u64}));
    }
    let residual_start=std::time::Instant::now();
    copies.check_residuals(circuit)?;
    let residual_ms=residual_start.elapsed().as_millis()as u64;
    sparse::bind(circuit, log_copies, t);
    let r = gkr::output_point(shape.row_count, t);
    gkr::append_usize(t, b"gkr-layer-index", 0);
    let rows = gkr::eq_weights(&r[..ROW_BITS]);
    let omega = gkr::eq_weights(&r[ROW_BITS..]);
    let mut claim = Fr::zero();
    let mut rounds = Vec::new();
    let u_start=std::time::Instant::now();
    let (u, left_value) = first(circuit, &copies, &rows, &omega, &mut claim, &mut rounds, t)?;
    let u_ms=u_start.elapsed().as_millis()as u64;
    let v_start=std::time::Instant::now();
    let low = gkr::eq_weights(&u[..INPUT_BITS]);
    let mut c = vec![Fr::zero(); circuit.input_len];
    let mut d = vec![Fr::zero(); circuit.input_len];
    for term in &circuit.terms {
        let gate = &term.gate;
        let weight = rows[term.row] * low[gate.left];
        c[gate.right] += weight * (gate.c2 + gate.c3 * left_value);
        d[gate.right] += weight * (gate.c0 + gate.c1 * left_value);
    }
    let mut tau = gkr::eq_weights(&u[INPUT_BITS..]);
    for (value, weight) in tau.iter_mut().zip(omega) { *value *= weight; }
    let (v, right_value) = second(&copies, c, d, &tau, &mut claim, &mut rounds, t)?;
    let v_ms=v_start.elapsed().as_millis()as u64;
    let w = sparse::wiring(circuit, &shape, &r, &u, &v).map_err(|e| e.to_string())?;
    if w[0] + w[1] * left_value + w[2] * right_value + w[3] * left_value * right_value != claim {
        return Err("POINT terminal expression".into());
    }
    let line_start=std::time::Instant::now();
    let coefficients = line(&copies, &u, &v);
    let line_ms=line_start.elapsed().as_millis()as u64;
    if coefficients[0] != left_value || gkr::eval_polynomial(&coefficients, Fr::one()) != right_value {
        return Err("POINT line endpoints".into());
    }
    t.append_scalar(b"gkr-left-value", &left_value);
    t.append_scalar(b"gkr-right-value", &right_value);
    gkr::append_polynomial(t, b"gkr-line-polynomial", &coefficients);
    let challenge = t.challenge_scalar(b"gkr-line-challenge");
    let point = gkr::line_point(&u, &v, challenge);
    let value = gkr::eval_polynomial(&coefficients, challenge);
    if log_copies==21 {
        println!("H21_POINT_PHASES {}",serde_json::json!({"owners":count,"distinct_banks":copies.banks.len(),
            "workers":rayon::current_num_threads(),"residual_ms":residual_ms,"u_ms":u_ms,"v_ms":v_ms,"line_ms":line_ms}));
    }
    Ok((GkrProof { layers: vec![LayerProof { rounds, left_value, right_value,
        line_coefficients: coefficients }] }, InputClaim { point, value }))
}

use super::*;
use crate::gkr::Gate;
use blake2::{Blake2b512, Digest};
use std::{io::Write, path::PathBuf};

const LOCAL_BITS: usize = 11;
const OWNERS: usize = 4;
const WIDTH: usize = 1 << LOCAL_BITS;

fn public_circuit() -> (crate::sparse::Circuit, Vec<EdgeTerm>) {
    let mut edges = Vec::new();
    for owner in 0..OWNERS {
        for local in [0, 31, 97, 511, 1024, 2046] {
            let wire = owner * WIDTH + local;
            edges.push(EdgeTerm { source_slot: owner, family_row: 0, term: Term { row: owner,
                gate: Gate { left: wire, right: wire, c0: Fr::zero(), c1: -Fr::one(),
                             c2: Fr::zero(), c3: Fr::one() } } });
        }
        edges.push(EdgeTerm { source_slot: owner, family_row: 0, term: Term { row: owner,
            gate: Gate { left: owner * WIDTH + 1571 + 13*owner,
                right: ((owner + 1) % OWNERS) * WIDTH + 37 + 17*owner,
                c0: -Fr::from([0u64, 0, 10, 0][owner]), c1: Fr::from(2u64),
                c2: Fr::from(3u64), c3: Fr::from(5u64) } } });
    }
    (crate::sparse::Circuit { input_len: WIDTH * OWNERS, row_count: OWNERS,
        terms: edges.iter().map(|e| e.term.clone()).collect() }, edges)
}

fn bind_public(t: &mut Transcript) { t.append_bytes(b"relation", b"fixed-native-window-bilinear-v1"); }
fn transcript() -> Transcript { Transcript::new(b"packed-history-prefix-native-differential-v1") }
fn external(name: &str) -> Result<PathBuf,String> {
    let p = PathBuf::from(std::env::var_os(name).ok_or_else(|| format!("missing {name}"))?);
    if !crate::preview_test_paths::absolute_outside_source(&p) { return Err("external fixture path required".into()); }
    Ok(p)
}

#[test]
#[ignore = "original N0 owner bytes and fresh external output"]
fn export_packed_prefix_proof_from_native_rows() -> Result<(),String> {
    let path = external("NIPOPOW_PACKED_FOLD_INPUT")?;
    if std::fs::metadata(&path).map_err(|e|e.to_string())?.len() != 64*131072 { return Err("owner fixture length".into()); }
    let bytes = std::fs::read(path).map_err(|e|e.to_string())?;
    if format!("{:x}",Blake2b512::digest(&bytes)) != "2b0eeabc82f705741f6f7aa9a965039afdf1c0cbb9a652b1ba11204fd0c5ce001a12328a6cb31f57a0a9e37f01791ae56012e76ddbb5309d16a5f2d248ce7a3b" {
        return Err("native bytes drift".into());
    }
    let owners: Vec<_> = [0,1,32,33].iter().map(|&i| {
        let base = i * 131072 + 98304; &bytes[base..base+WIDTH/8]
    }).collect();
    let fields: Vec<_> = owners.iter().flat_map(|row| (0..WIDTH)
        .map(move |i| Fr::from(((row[i/8] >> (i%8)) & 1) as u64))).collect();
    let (circuit,edges) = public_circuit();
    let shape = crate::sparse::validate(&circuit,0).map_err(|e|e.to_string())?;
    let mut oracle_t = transcript();
    let (oracle,oracle_claim) = crate::sparse::prove_with_binding(&circuit,&fields,0,&mut oracle_t,bind_public)
        .map_err(|e|e.to_string())?;
    let mut t = transcript();
    let inner = PackedEdgeInput::new(WIDTH,OWNERS,|i| Ok(owners[i].to_vec()))?;
    let mut input = H21Role1PackedInput { inner };
    let (proof,claim,u,v,stats) = prove_edge_terms_strategy_for_test(LOCAL_BITS,2,0,0,&[0],
        false,true,true,0,&mut input,
        |left,owner,sink| {
            for edge in &edges {
                let g=&edge.term.gate;
                if (if left {g.left} else {g.right}) / WIDTH == owner { sink(edge.clone())?; }
            }
            Ok(())
        }, &mut t,bind_public,|r,u,v| crate::sparse::wiring(&circuit,&shape,r,u,v).map_err(|e|e.to_string()),
        &mut |_| Ok(()))?;
    assert!(!u && !v);
    assert!(stats.prefix_patterns > 1<<20, "tiled replay must actually execute");
    let wire = gkr::encode_proof(&proof)?;
    assert_eq!(wire,gkr::encode_proof(&oracle)?);
    assert_eq!(claim,oracle_claim);
    assert_eq!(gkr::mle(&fields,&claim.point).map_err(|e|e.to_string())?,claim.value);
    assert_eq!(t.challenge_scalar(b"after"),oracle_t.challenge_scalar(b"after"));
    let mut out = std::fs::OpenOptions::new().write(true).create_new(true)
        .open(external("NIPOPOW_PACKED_FOLD_PACKET")?).map_err(|e|e.to_string())?;
    out.write_all(&wire).and_then(|_|out.sync_all()).map_err(|e|e.to_string())?;
    println!("PACKED_FOLD_EXPORTED bytes={} input_bits=13 dense_reference=true",wire.len());
    Ok(())
}

#[test]
#[ignore = "fresh process with only the exported packet"]
fn verify_packed_prefix_proof_from_packet() -> Result<(),String> {
    if std::env::var_os("NIPOPOW_PACKED_FOLD_INPUT").is_some(){return Err("unexpected producer input".into());}
    let p = external("NIPOPOW_PACKED_FOLD_PACKET")?;
    if std::fs::metadata(&p).map_err(|e|e.to_string())?.len() != 3008 {return Err("packet extent".into());}
    let wire = std::fs::read(p).map_err(|e|e.to_string())?;
    let mut proof = gkr::decode_dimensions(&[13],&wire)?;
    assert_eq!(gkr::encode_proof(&proof)?,wire);
    let (circuit,_) = public_circuit();
    let shape = crate::sparse::validate(&circuit,0).map_err(|e|e.to_string())?;
    let verify = |proof: &GkrProof| gkr::verify_with_wiring(&[13],OWNERS,proof,&mut transcript(),
        bind_public,|_,r,u,v| crate::sparse::wiring(&circuit,&shape,r,u,v));
    let claim = verify(&proof).map_err(|e|e.to_string())?;
    assert_eq!(claim.point.len(),13);
    proof.layers[0].rounds[0][0] += Fr::one();
    assert!(verify(&proof).is_err());
    println!("PACKED_FOLD_VERIFIED bytes={} altered_round_rejected=true",wire.len());
    Ok(())
}

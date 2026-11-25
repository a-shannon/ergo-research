use crate::{gkr, point_role::PointMath, sparse, sparse_stream_boolean, transcript::Transcript};
use ark_bn254::Fr;
use blake2::{Blake2b512, Digest};
use std::{collections::HashSet, path::PathBuf, time::Instant};

#[test]
#[ignore = "two pinned POINT windows from sealed N0 witness chunks"]
fn native_banks_match_reference_proof_claim_and_transcript() -> Result<(), String> {
    let dir = PathBuf::from(std::env::var_os("NIPOPOW_POINT_WINDOWS").ok_or("missing POINT windows")?);
    if !crate::preview_test_paths::absolute_outside_source(&dir) { return Err("POINT fixture directory".into()); }
    let base = crate::point_membership::build()?.circuit;
    let independent = PointMath::dimensions(&base, 4, 17, 18, 24)?;
    for (name, classes, digest) in [
        ("early", 16, "e026c22874226815e1ceb9123f7c9b306f84217d231d37599c3e37d2b0532236881bf43a5a52181d2c7d15f621478ba1fad89158b33d26845b47d881a22dedcb"),
        ("repeated", 6, "c76b9c280e5f54c23844cc0da0dae26a06aa484c28cf7816545edde580cc5fd413cb61c1ec4b33dda8a8edabed6dbaf9a9c7d157dd1b0b4381bb29c339af01a2"),
    ] {
        let path = dir.join(format!("{name}.point"));
        if std::fs::metadata(&path).map_err(|e|e.to_string())?.len() != 16384 { return Err("POINT fixture extent".into()); }
        let bytes = std::fs::read(path).map_err(|e| e.to_string())?;
        if bytes.len() != 16384 || format!("{:x}", Blake2b512::digest(&bytes)) != digest {
            return Err("POINT fixture bytes".into());
        }
        let banks: Vec<_> = bytes.chunks_exact(1024).collect();
        assert_eq!(banks.iter().copied().collect::<HashSet<_>>().len(), classes);
        let prefix = || {
            let mut t = Transcript::new(b"canonical-POINT-native-parity-v1");
            t.append_bytes(b"physical-window", name.as_bytes());
            t
        };
        let started = Instant::now();
        let mut reference_t = prefix();
        let (reference, reference_claim) = sparse_stream_boolean::prove_h21_point_window(&base, |i| {
            Ok((0..8192).map(|wire| Fr::from(((banks[i][wire/8] >> (wire%8)) & 1) as u64)).collect())
        }, &mut reference_t).map_err(|e|e.to_string())?;
        let reference_elapsed = started.elapsed();
        let started = Instant::now();
        let mut t = prefix();
        let (proof, claim) = sparse_stream_boolean::point_grouped_producer::prove(&base, 4, 1 << 30,
            |i| Ok(banks[i].to_vec()), &mut t)?;
        let grouped_elapsed = started.elapsed();
        let wire = gkr::encode_proof(&proof)?;
        assert_eq!(wire, gkr::encode_proof(&reference)?);
        assert_eq!(claim, reference_claim);
        let decoded = gkr::decode_dimensions(&[17], &wire)?;
        let mut check = prefix();
        let verified = gkr::verify_with_wiring(&[17], 1 << 18, &decoded, &mut check,
            |tr| sparse::bind(&base, 4, tr), |_,r,u,v| independent.coefficients(r,u,v)).map_err(|e|e.to_string())?;
        assert_eq!(claim, verified);
        let tail = t.challenge_scalar(b"parity-after-proof");
        assert_eq!(tail, reference_t.challenge_scalar(b"parity-after-proof"));
        assert_eq!(tail, check.challenge_scalar(b"parity-after-proof"));
        println!("POINT_WINDOW name={name} classes={classes} proof_bytes={} reference_us={} grouped_us={}",
            wire.len(), reference_elapsed.as_micros(), grouped_elapsed.as_micros());
        if classes < 16 {
            let mut bad = banks[0].to_vec();
            // Last coordinate is a canonical zero-padding constraint.
            bad[1023] ^= 0x80;
            let mut t = prefix();
            let fault = sparse_stream_boolean::point_grouped_producer::prove(&base, 4, 1 << 30,
                |i| Ok(if i == 0 { bad.clone() } else { banks[i].to_vec() }), &mut t);
            assert_eq!(fault.unwrap_err(), "nonzero POINT residual");
            assert_eq!(t.challenges(), 0);
        }
    }
    let mut t = Transcript::new(b"budget");
    let failure = sparse_stream_boolean::point_grouped_producer::prove(&base, 21, 8 << 30,
        |_| panic!("read before full-domain scratch admission"), &mut t);
    assert_eq!(failure.unwrap_err(), "POINT scratch reservation");
    Ok(())
}

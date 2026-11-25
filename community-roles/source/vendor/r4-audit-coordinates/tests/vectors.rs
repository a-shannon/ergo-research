use nipopow_r4_audit_coordinates::{coordinates, Work};
use sha2::{Digest, Sha256};

fn small(value: u8) -> Work {
    let mut bytes = [0; 28];
    bytes[27] = value;
    bytes
}

#[test]
fn independent_dotnet_work_vector() {
    // .NET SHA512.HashData + unsigned big-endian BigInteger over literal preimages,
    // SHA256 over all three 466-draw runs (concatenated U224BE coordinates).
    let draws = coordinates(b"xy", b"z", small(10), small(3)).unwrap();
    let mut hash = Sha256::new();
    for draw in &draws { hash.update(draw); }
    assert_eq!(format!("{:x}", hash.finalize()),
        "e7ef8584f80b5a3456e30a3215d35ce8a41f3021ed652e7d74dd6e7c682d07d5");
    assert_eq!([draws[0], draws[466], draws[932]], [small(8), small(6), small(6)]);
}

#[test]
fn full_width_scale_and_frame_extent() {
    let work = [255u8; 28];
    let mut following = [0u8; 28];
    following[0] = 128;
    let a = coordinates(b"x", b"first\0last", work, following).unwrap();
    let b = coordinates(b"x", b"first\0lasT", work, following).unwrap();
    let c = coordinates(b"x\0", b"first\0last", work, following).unwrap();
    assert_eq!(a.len(), 932);
    assert!(a.iter().all(|coord| *coord < work));
    let mut lower = [255; 28];
    lower[0] = 127;
    assert!(a[..466].iter().all(|coord| *coord >= lower));
    assert_ne!(a, b);
    assert_ne!(a, c);
}

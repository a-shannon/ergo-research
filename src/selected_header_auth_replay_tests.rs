//! Separate-process replay of the fixed selected-authentication file set.
use crate::{
    pcs,
    selected_header_auth::{Artifact, Plan, Reject},
    selected_header_auth_tests::expected_ids,
    verifier_key,
};
use std::{
    env,
    fs::{self, File, OpenOptions},
    io::{self, Cursor, Read, Write},
    path::{Path, PathBuf},
    time::Instant,
};

const FILE_SPECS: [(&str, usize); 10] = [
    ("verifier-key.bin", 23_664),
    ("commitment.bin", 384),
    ("role-0.gkr", 5_024),
    ("role-1.gkr", 5_024),
    ("role-2.gkr", 3_456),
    ("role-3.gkr", 5_024),
    ("role-0.pcs", 29_421),
    ("role-1.pcs", 29_421),
    ("role-2.pcs", 29_421),
    ("role-3.pcs", 29_421),
];

#[derive(Debug)]
enum ReadFailure {
    Io(io::Error),
    NotRegular,
    BoundaryLength { expected: usize, actual: u64 },
    ShortRead,
    TrailingByte,
}

struct ReplayFiles {
    key: Vec<u8>,
    commitment: Vec<u8>,
    roles: [Vec<u8>; 4],
    openings: [Vec<u8>; 4],
}

impl ReplayFiles {
    fn artifact(&self) -> Artifact {
        Artifact {
            commitment: self.commitment.clone(),
            roles: self.roles.clone(),
            openings: self.openings.clone(),
        }
    }

    fn payloads(&self) -> [&[u8]; 10] {
        [
            &self.key,
            &self.commitment,
            &self.roles[0],
            &self.roles[1],
            &self.roles[2],
            &self.roles[3],
            &self.openings[0],
            &self.openings[1],
            &self.openings[2],
            &self.openings[3],
        ]
    }
}

fn configured_directory(name: &str) -> PathBuf {
    let value = env::var_os(name).unwrap_or_else(|| panic!("{name} must name a directory"));
    let path = PathBuf::from(value);
    assert!(path.is_absolute(), "{name} must be an absolute path");
    assert!(path.is_dir(), "{name} must be an existing directory");
    path
}

fn read_bounded_stream(mut reader: impl Read, expected: usize) -> Result<Vec<u8>, ReadFailure> {
    let mut bytes = vec![0u8; expected];
    reader.read_exact(&mut bytes).map_err(|error| {
        if error.kind() == io::ErrorKind::UnexpectedEof {
            ReadFailure::ShortRead
        } else {
            ReadFailure::Io(error)
        }
    })?;
    let mut trailing = [0u8; 1];
    match reader.read(&mut trailing) {
        Ok(0) => Ok(bytes),
        Ok(_) => Err(ReadFailure::TrailingByte),
        Err(error) => Err(ReadFailure::Io(error)),
    }
}

fn read_regular_exact(path: &Path, expected: usize) -> Result<Vec<u8>, ReadFailure> {
    let file = File::open(path).map_err(ReadFailure::Io)?;
    let metadata = file.metadata().map_err(ReadFailure::Io)?;
    if !metadata.file_type().is_file() {
        return Err(ReadFailure::NotRegular);
    }
    if metadata.len() != expected as u64 {
        return Err(ReadFailure::BoundaryLength {
            expected,
            actual: metadata.len(),
        });
    }
    read_bounded_stream(file, expected)
}

fn read_files(directory: &Path) -> Result<ReplayFiles, ReadFailure> {
    let mut read = || {
        FILE_SPECS
            .iter()
            .map(|(name, size)| read_regular_exact(&directory.join(name), *size))
            .collect::<Result<Vec<_>, _>>()
    };
    let mut bytes = read()?.into_iter();
    Ok(ReplayFiles {
        key: bytes.next().unwrap(),
        commitment: bytes.next().unwrap(),
        roles: [
            bytes.next().unwrap(),
            bytes.next().unwrap(),
            bytes.next().unwrap(),
            bytes.next().unwrap(),
        ],
        openings: [
            bytes.next().unwrap(),
            bytes.next().unwrap(),
            bytes.next().unwrap(),
            bytes.next().unwrap(),
        ],
    })
}

fn negative_root() -> PathBuf {
    let root = configured_directory("NIPOPOW_SELECTED_REPLAY_OUTPUT")
        .join("selected-auth-replay-negatives");
    fs::create_dir(&root).expect("negative replay output directory must be fresh");
    root
}

fn write_new(path: &Path, bytes: &[u8]) {
    let mut file = OpenOptions::new()
        .write(true)
        .create_new(true)
        .open(path)
        .unwrap();
    file.write_all(bytes).unwrap();
    file.sync_all().unwrap();
}

fn write_case(root: &Path, label: &str, files: &ReplayFiles) -> PathBuf {
    let directory = root.join(label);
    fs::create_dir(&directory).unwrap();
    for ((name, _), bytes) in FILE_SPECS.iter().zip(files.payloads()) {
        write_new(&directory.join(name), bytes);
    }
    directory
}

#[test]
fn fresh_process_replays_the_ten_frozen_files_with_pinned_authority() {
    let started = Instant::now();
    let input = configured_directory("NIPOPOW_SELECTED_REPLAY_INPUT");
    let files = read_files(&input).expect("all ten diagnostic files must be exact regular files");
    let key = verifier_key::admit(22, &files.key).expect("source-pinned verifier key admission");
    assert_eq!(key.log_n(), 22);
    let plan = Plan::new(expected_ids()).unwrap();
    let verify_started = Instant::now();
    let claims = plan.verify(&files.artifact(), &key).unwrap();
    let verify_seconds = verify_started.elapsed().as_secs_f64();
    assert_eq!(claims.len(), 4);
    println!(
        "selected-auth file replay: files=10 claims={} verify_seconds={verify_seconds:.3} total_seconds={:.3}",
        claims.len(),
        started.elapsed().as_secs_f64()
    );
}

#[test]
fn exact_file_boundaries_authority_and_disk_role_order_fail_closed() {
    let input = configured_directory("NIPOPOW_SELECTED_REPLAY_INPUT");
    let frozen = read_files(&input).expect("baseline diagnostic files");
    let key = verifier_key::admit(22, &frozen.key).expect("source-pinned verifier key admission");
    let plan = Plan::new(expected_ids()).unwrap();
    let output = negative_root();

    // Disk boundaries are checked from each opened file handle before allocation.
    let boundaries = output.join("file-boundaries");
    fs::create_dir(&boundaries).unwrap();
    for (index, ((name, expected), payload)) in FILE_SPECS.iter().zip(frozen.payloads()).enumerate()
    {
        let short_path = boundaries.join(format!("short-{index}-{name}"));
        write_new(&short_path, &payload[..expected - 1]);
        assert!(matches!(
            read_regular_exact(&short_path, *expected),
            Err(ReadFailure::BoundaryLength { expected: e, actual })
                if e == *expected && actual == (*expected - 1) as u64
        ));

        let long_path = boundaries.join(format!("long-{index}-{name}"));
        let mut grown = payload.to_vec();
        grown.push(0);
        write_new(&long_path, &grown);
        assert!(matches!(
            read_regular_exact(&long_path, *expected),
            Err(ReadFailure::BoundaryLength { expected: e, actual })
                if e == *expected && actual == (*expected + 1) as u64
        ));
    }

    // Exercise the exact-read and EOF branches independently of metadata.
    let expected = FILE_SPECS[0].1;
    assert!(matches!(
        read_bounded_stream(Cursor::new(vec![0u8; expected - 1]), expected),
        Err(ReadFailure::ShortRead)
    ));
    assert!(matches!(
        read_bounded_stream(Cursor::new(vec![0u8; expected + 1]), expected),
        Err(ReadFailure::TrailingByte)
    ));

    // Change a digest-covered group byte while preserving the key frame.
    let mut wrong_key = frozen.clone_for_test();
    wrong_key.key[8] ^= 1;
    let wrong_key_dir = write_case(&output, "wrong-key", &wrong_key);
    let wrong_key_files = read_files(&wrong_key_dir).unwrap();
    assert_eq!(wrong_key_files.key.len(), FILE_SPECS[0].1);
    assert!(matches!(
        verifier_key::admit(22, &wrong_key_files.key),
        Err(message) if message == "verifier-key digest mismatch"
    ));

    let mut malformed_commitment = frozen.clone_for_test();
    malformed_commitment.commitment.fill(0xff);
    let malformed_dir = write_case(&output, "malformed-commitment", &malformed_commitment);
    let malformed_files = read_files(&malformed_dir).unwrap();
    assert_eq!(
        plan.verify(&malformed_files.artifact(), &key).unwrap_err(),
        Reject::Commitment
    );
    assert!(pcs::decode_commitment(&malformed_files.commitment).is_err());

    let mut swapped_gkr = frozen.clone_for_test();
    swapped_gkr.roles.swap(0, 1);
    let swapped_gkr_dir = write_case(&output, "swapped-gkr", &swapped_gkr);
    let swapped_gkr_files = read_files(&swapped_gkr_dir).unwrap();
    assert_eq!(
        plan.verify(&swapped_gkr_files.artifact(), &key)
            .unwrap_err(),
        Reject::Role(0)
    );

    let mut swapped_pcs = frozen.clone_for_test();
    swapped_pcs.openings.swap(0, 1);
    let swapped_pcs_dir = write_case(&output, "swapped-pcs", &swapped_pcs);
    let swapped_pcs_files = read_files(&swapped_pcs_dir).unwrap();
    assert_eq!(
        plan.verify(&swapped_pcs_files.artifact(), &key)
            .unwrap_err(),
        Reject::Opening(0)
    );
}

impl ReplayFiles {
    fn clone_for_test(&self) -> Self {
        Self {
            key: self.key.clone(),
            commitment: self.commitment.clone(),
            roles: self.roles.clone(),
            openings: self.openings.clone(),
        }
    }
}

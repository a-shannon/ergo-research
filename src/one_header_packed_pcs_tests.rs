use crate::{gkr, one_header_gkr_pcs::*, packed::{self, PackedFile, PackedFileWriter, PackedIoSnapshot},
    pcs, projection_aux_retirement::Authority, serializer, sparse, transcript::Transcript, verifier_key};
use ark_bn254::{Fr, G1Affine, G1Projective, Fq};
use ark_ff::{Field, One, Zero};
use dory_pcs::{MultilinearLagrange, Polynomial};
use dory_pcs::backends::arkworks::{ArkFr, ArkG1, ArkG2, ArkGT};
use serde::{Deserialize, Serialize};
use std::{fs::{self, OpenOptions}, io::{self, Write}, mem::size_of, path::{Path, PathBuf}, time::Instant};

const BYTES: usize = N / 8;
const ENV: &str = "NIPOPOW_ONE_HEADER_PACKED_PCS_ARTIFACT_DIR";
const LIMIT_US: u64 = 120_000_000;
const LIMIT_NS: u64 = 120_000_000_000;

fn micros(t: Instant) -> u64 {
    let n = u64::try_from(t.elapsed().as_micros()).expect("checked microseconds");
    assert!(n <= LIMIT_US); n
}
fn nanos(n: u128) -> u64 {
    let n = u64::try_from(n).expect("checked I/O nanoseconds");
    assert!(n <= LIMIT_NS); n
}
fn add_time(total: &mut u64, t: Instant) {
    *total = total.checked_add(micros(t)).expect("checked disjoint reference duration");
    assert!(*total <= LIMIT_US);
}
fn fields() -> serializer::Fields {
    serializer::Fields { version:4,parent_id:[0x11;32],ad_proofs_root:[0x22;32],
        transactions_root:[0x33;32],state_root:[0x44;33],timestamp:0,extension_root:[0x55;32],
        n_bits:0x043B9ACA,height:844672,votes:[0x66,0x77,0x88],pk:[0;33],w:[0;33],
        nonce:[1,2,3,4,5,6,7,8],payload_len:0,payload:[0;255] }
}
#[derive(Debug, Eq, PartialEq)]
enum PackingError { Length, NonBoolean(usize) }
fn pack(x: &[Fr]) -> Result<[u8; BYTES], PackingError> {
    if x.len() != N { return Err(PackingError::Length); }
    let mut bytes = [0u8; BYTES];
    for (i, v) in x.iter().enumerate() {
        if v.is_one() { bytes[i/8] |= 1 << (i%8); }
        else if !v.is_zero() { return Err(PackingError::NonBoolean(i)); }
    }
    Ok(bytes)
}
fn bit(bytes: &[u8; BYTES], i: usize) -> Fr {
    assert!(i < N); Fr::from(((bytes[i/8] >> (i%8)) & 1) as u64)
}
fn selector(i: usize) -> [Fr;18] { std::array::from_fn(|b| Fr::from(((i>>b)&1) as u64)) }
fn eq(point: &[Fr], i: usize) -> Fr {
    point.iter().enumerate().fold(Fr::one(), |w,(b,t)| w *
        if (i>>b)&1 == 1 { *t } else { Fr::one()-t })
}
fn directory() -> PathBuf {
    let value = std::env::var_os(ENV).expect("controller-bound artifact environment required");
    let path = PathBuf::from(value); assert!(path.is_absolute());
    let expected = path.canonicalize().expect("controller-created directory");
    assert!(crate::preview_test_paths::absolute_outside_source(&expected), "artifact directory must be outside source");
    assert!(fs::metadata(&expected).unwrap().is_dir());
    assert_eq!(fs::read_dir(&expected).unwrap().count(),0,"exclusive fresh output lane");
    expected
}
fn lock_controls(source: &PackedFile, path: &Path) {
    assert!(OpenOptions::new().write(true).open(path).is_err(),"live source must deny writer");
    assert!(fs::remove_file(path).is_err(),"live source must deny delete");
    assert_eq!(source.input_len(), N);
}
fn checked_snapshot(source: &PackedFile, expected: &[u8;BYTES]) {
    for copy in 0..4 {
        let chunk = source.read_copy(65536,copy).unwrap();
        assert_eq!((chunk.len(),chunk.capacity()),(65536,65536));
        let mut bytes = [0u8;8192];
        for (i, v) in chunk.iter().enumerate() {
            assert!(v.is_zero() || v.is_one());
            if v.is_one() { bytes[i/8] |= 1<<(i%8); }
        }
        assert_eq!(&bytes[..],&expected[copy*8192..(copy+1)*8192],"full locked snapshot {copy}");
        drop(chunk);
    }
    assert!(source.read_copy(65536,4).is_err());
}
fn wrote_once(s: PackedIoSnapshot) {
    assert_eq!((s.write_calls,s.write_bytes,s.sync_calls),(1,BYTES as u64,1));
    assert_eq!((s.read_calls,s.read_bytes),(0,0),"log18 has no partial-byte opening read");
    let _ = (nanos(s.write_ns), nanos(s.sync_ns));
}
fn read_count(s: PackedIoSnapshot, calls: u64, bytes: u64) {
    assert_eq!((s.read_calls,s.read_bytes),(calls,bytes));
    assert_eq!((s.write_calls,s.write_bytes,s.sync_calls),(0,0,0));
    let _ = nanos(s.read_ns);
}
fn framing_controls(path: &Path, main: &Path) {
    assert!(!path.exists());
    assert!(PackedFileWriter::create_new(path,25).is_err());
    assert!(!path.exists());
    let mut writer = PackedFileWriter::create_new(path,18).unwrap();
    writer.write_bytes(&[0]).unwrap();
    assert!(writer.finish().err().unwrap().contains("writer length mismatch"));
    assert!(!path.exists());
    let mut writer = PackedFileWriter::create_new(path,18).unwrap();
    assert!(writer.write_bytes(&[0u8;BYTES+1]).err().unwrap().contains("exceeds declared dimension"));
    drop(writer); assert!(!path.exists());
    for length in [BYTES-1,BYTES+1] {
        let mut file = OpenOptions::new().write(true).create_new(true).open(path).unwrap();
        file.write_all(&[0u8;BYTES+1][..length]).unwrap(); drop(file);
        assert!(PackedFile::open(path,18).err().unwrap().contains("packed length mismatch"));
        fs::remove_file(path).unwrap();
    }
    assert!(PackedFile::open(main,25).err().unwrap().contains("dimension exceeds admitted bound"));
    assert!(PackedFile::open(main,17).err().unwrap().contains("packed length mismatch"));
    assert!(!path.exists());
}
fn non_boolean_points() -> [[Fr;18];2] {
    [[Fr::from(2);18], std::array::from_fn(|j| Fr::from((2*j+3) as u64)/Fr::from((2*j+5) as u64))]
}
fn reference_checks(source: &PackedFile, expected: &[u8;BYTES], x: &[Fr]) -> [Fr;2] {
    assert_eq!(x[1],Fr::one(),"genuine first-active bit makes the omission decisive");
    for i in [0,1,131071,131072,131455,131456,131487,131488,131489,131490,131491,N-1] {
        assert_eq!(source.evaluate(&selector(i)).unwrap(), x[i]);
    }
    let reversed = (0..N).find(|i| bit(expected,*i)!=bit(expected,*i^7)).unwrap();
    let baseline = source.evaluate(&selector(reversed)).unwrap();
    assert_eq!(baseline,bit(expected,reversed)); assert_ne!(baseline,bit(expected,reversed^7));
    let transpose = |i:usize| (i%512)*512+i/512;
    let changed = (0..N).find(|i| bit(expected,*i)!=bit(expected,transpose(*i))).unwrap();
    let baseline = source.evaluate(&selector(changed)).unwrap();
    assert_eq!(baseline,bit(expected,changed)); assert_ne!(baseline,bit(expected,transpose(changed)));
    assert_ne!(source.evaluate(&selector(1)).unwrap(),Fr::zero(),"first-active omission mutant");
    let mut scalars = [Fr::zero();2];
    for (j,point) in non_boolean_points().into_iter().enumerate() {
        // Callable golden, independent of the packing helper and optimized packed implementation.
        let dense = dory_pcs::backends::arkworks::ArkworksPolynomial::new(x.iter().copied().map(ArkFr).collect());
        let p: [ArkFr;18] = point.map(ArkFr);
        scalars[j] = Polynomial::evaluate(&dense,&p).0;
        assert_eq!(source.evaluate(&point).unwrap(),scalars[j]);
        let (left,right) = MultilinearLagrange::compute_evaluation_vectors(&dense,&p,9,9);
        assert_eq!((left.len(),left.capacity(),right.len(),right.capacity()),(512,512,512,512));
        let actual = MultilinearLagrange::vector_matrix_product(source,&left,9,9);
        let reference = MultilinearLagrange::vector_matrix_product(&dense,&left,9,9);
        assert_eq!(actual,reference); assert_eq!((actual.len(),actual.capacity()),(512,512));
        let wrong_left:Vec<_> = right.clone();
        let wrong = MultilinearLagrange::vector_matrix_product(source,&wrong_left,9,9);
        // The asymmetric point makes the wrong split a real mutation; [2;18] is symmetric.
        if point[0]!=point[9] { assert_ne!(actual,wrong,"wrong source point split"); }
        drop(wrong);drop(wrong_left);drop(actual);drop(reference);drop(left);drop(right);drop(dense);
    }
    scalars
}
fn resource_model(c: &Compact, x: &[Fr]) {
    assert_eq!((size_of::<Fr>(),size_of::<ArkG1>(),size_of::<ArkG2>(),size_of::<ArkGT>()),(32,96,192,384));
    assert_eq!((size_of::<G1Projective>(),size_of::<G1Affine>(),size_of::<Fq>()),(96,72,32));
    let entries = (512/4)*(1usize<<4); assert_eq!(entries,2048);
    let table_bound = entries*(size_of::<G1Projective>()+size_of::<G1Affine>()+size_of::<Fq>())+128*3*size_of::<usize>();
    assert_eq!(table_bound,412672,"source modeled table normalization peak, not RSS");
    assert_eq!(512*(512/8),BYTES);
    assert_eq!((c.circuit().terms.len(),c.circuit().terms.capacity()),(TERMS,TERMS));
    assert_eq!(x.len(),N);
    assert!(94221696usize+48334632+68*1024*1024+3*8*1024*1024+32*1024*1024+
        5*1024*1024+table_bound+2*49152+2*BYTES+2*1024*1024+8192 <512*1024*1024);
}

#[derive(Debug, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Diagnostic {
    schema:u64, log_n:u64, input_extent:u64, packed_file_bytes:u64, subset_entries:u64,
    commit_read_calls:u64, commit_read_bytes:u64, eval_read_calls:u64, eval_read_bytes:u64,
    open_read_calls:u64, open_read_bytes:u64, write_calls:u64, write_bytes:u64, sync_calls:u64,
    main_file_bytes:u64, tail_file_bytes:u64, gkr_bytes:u64, dory_bytes:u64,
    commit_equal:bool, proof_equal:bool, continuation_equal:bool, controls_pass:bool,
    commit_read_ns:u64, eval_read_ns:u64, open_read_ns:u64, write_ns:u64, sync_ns:u64,
    packing_us:u64, finish_us:u64, reference_us:u64, setup_us:u64, dense_commit_us:u64,
    gkr_prove_us:u64, gkr_codec_verify_us:u64, dense_open_us:u64, packed_commit_us:u64,
    packed_open_us:u64, key_admit_us:u64, pcs_verify_us:u64,
}

#[test]
fn gkr_claim_opens_existing_packed_snapshot() {
    let dir = directory(); let main_path = dir.join("witness-main.bin"); let tail_path = dir.join("witness-tail.bin");
    let a = Authority::build().unwrap();
    let c = Compact::build(&a,&Descriptor::canonical(&a),&placements(),&rows(),&SETUP_ID).unwrap();
    let f = fields(); assert_eq!(u64::from(f.height),OWNER+1,"fixture only, not an encoded ownership constraint");
    let mut x = assign(&a,&f).unwrap(); assert_eq!((x.len(),x.capacity()),(N,N));
    c.check(&x).unwrap(); resource_model(&c,&x);
    // Source Builder constants0/1 precede version; nBits source rails begin1362.
    assert_eq!((a.serializer().layout.zero,a.serializer().layout.one),(0,1));
    assert_eq!(a.serializer().layout.fields.version,std::array::from_fn(|b|2+b));
    assert_eq!(a.serializer().layout.fields.n_bits,std::array::from_fn(|b|1362+b));
    assert_eq!(x[1],Fr::one());x[1]=Fr::from(2);
    assert_eq!(pack(&x).err(),Some(PackingError::NonBoolean(1))); x[1]=Fr::one();
    assert_eq!(pack(&x[..N-1]).err(),Some(PackingError::Length));
    drop(a); // no compiler/recipe/Authority arrays in crypto phases
    let started = Instant::now();
    let expected = pack(&x).unwrap();
    // Independent literal bytes from constants0/1, version4 and LE0x043B9ACA decoder.
    assert_eq!(expected[0],0x12);
    assert_eq!(&expected[DECODER/8..DECODER/8+4],&[0xCA,0x9A,0x3B,0x04]);
    assert_eq!(expected[NEIGHBOR_INPUT/8],0);assert_eq!(expected[BYTES-1],0);
    let mut writer = PackedFileWriter::create_new(&main_path,18).unwrap();
    writer.write_bytes(&expected).unwrap(); let packing_us = micros(started);
    let started = Instant::now(); let main = writer.finish().unwrap(); let finish_us = micros(started);
    let write_stats = main.io_metrics_snapshot(); wrote_once(write_stats);
    lock_controls(&main,&main_path);
    let mut reference_us = 0;
    let started = Instant::now(); checked_snapshot(&main,&expected); add_time(&mut reference_us,started);
    framing_controls(&tail_path,&main_path);
    let started = Instant::now(); let scalar_oracles = reference_checks(&main,&expected,&x); add_time(&mut reference_us,started);
    assert!(bit(&expected,INPUT_USED).is_zero() && bit(&expected,N-1).is_zero());
    let started = Instant::now(); let mut setup = pcs::generate_setup(18).unwrap(); let setup_us = micros(started);
    assert_eq!((setup.log_n,setup.id),(18,SETUP_ID));
    assert_eq!((setup.prover.g1_vec.len(),setup.prover.g2_vec.len()),(512,512));
    assert_eq!(pcs::encode(&dory_pcs::backends::arkworks::ArkworksVerifierSetup(setup.verifier.clone())).unwrap(),KEY);
    main.reset_io_metrics(); setup.log_n=17;
    assert!(packed::commit(&main,&setup).err().unwrap().contains("packed/setup dimension mismatch"));
    setup.log_n=18; read_count(main.io_metrics_snapshot(),0,0);
    let started = Instant::now(); let dense = pcs::commit(&x,&setup).unwrap(); let dense_commit_us = micros(started);
    assert_eq!((dense.rows.len(),dense.rows.capacity()),(512,512));
    let commitment_bytes = pcs::encode_commitment(&dense.commitment).unwrap(); assert_eq!(commitment_bytes.len(),384);assert!(commitment_bytes.capacity()<=1024*1024);
    let statement = c.statement(setup.id,&commitment_bytes,&commitment_bytes).unwrap();
    let mut producer = statement.transcript();
    let started = Instant::now(); let (proof,claim) = sparse::prove(c.circuit(),&x,0,&mut producer).unwrap(); let gkr_prove_us = micros(started);
    assert_eq!(producer.challenges(),56);assert_eq!(claim.point.len(),18);
    assert_eq!(gkr::mle(&x,&claim.point).unwrap(),claim.value);
    let started = Instant::now(); let gkr_bytes = gkr::encode_proof(&proof).unwrap();
    let decoded = sparse::decode_proof(c.circuit(),0,&gkr_bytes).unwrap(); assert_eq!(decoded,proof);
    let mut continuation = statement.transcript();
    let verified = sparse::verify(c.circuit(),0,&decoded,&mut continuation).unwrap();
    let gkr_codec_verify_us = micros(started);
    assert_eq!(verified,claim);assert_eq!(continuation.challenges(),56);
    assert_eq!(gkr_bytes.len(),4128);assert_eq!(gkr_bytes.len()/32,129);assert!(gkr_bytes.capacity()<=1024*1024);
    let mut p1 = producer.clone();let mut p2 = continuation.clone();
    assert_eq!(p1.challenge_scalar(b"same-post-gkr"),p2.challenge_scalar(b"same-post-gkr"));
    drop(proof);drop(decoded);drop(x); // dense PCS owns the only remaining N-Fr polynomial
    let started = Instant::now(); let dense_opening = pcs::open(&dense,&claim.point,&setup,&mut producer).unwrap(); let dense_open_us = micros(started);
    let dense_bytes = pcs::encode_proof(&dense_opening).unwrap();assert_eq!(dense_bytes.len(),24237);assert!(dense_bytes.capacity()<=1024*1024);
    assert_eq!(dense_bytes.len()+gkr_bytes.len(),28365);
    let golden_rows = dense.rows.clone(); assert_eq!((golden_rows.len(),golden_rows.capacity()),(512,512));
    drop(dense_opening);drop(dense);
    main.reset_io_metrics();let started = Instant::now();let committed = packed::commit(&main,&setup).unwrap(); let packed_commit_us = micros(started);
    let commit_stats = main.io_metrics_snapshot();read_count(commit_stats,1,BYTES as u64);
    assert_eq!(committed.rows,golden_rows);assert_eq!((committed.rows.len(),committed.rows.capacity()),(512,512));
    assert_eq!(pcs::encode_commitment(&committed.commitment).unwrap(),commitment_bytes);drop(golden_rows);
    let mut wrong = commitment_bytes.clone();wrong[0]^=1;
    assert_eq!(c.statement(SETUP_ID,&wrong,&commitment_bytes).err(),Some(Error::Commitment));drop(wrong);
    main.reset_io_metrics();assert_eq!(main.evaluate(&claim.point).unwrap(),claim.value);
    let eval_stats = main.io_metrics_snapshot();read_count(eval_stats,1,BYTES as u64);
    main.reset_io_metrics();
    assert!(packed::open(&committed,&main,&claim.point[..17],&setup,&mut continuation.clone()).err().unwrap().contains("dimensions mismatch"));
    read_count(main.io_metrics_snapshot(),0,0);
    let mut packed_transcript = continuation.clone();
    main.reset_io_metrics();let started = Instant::now();
    let opening = packed::open(&committed,&main,&claim.point,&setup,&mut packed_transcript).unwrap();let packed_open_us = micros(started);
    let open_stats = main.io_metrics_snapshot();read_count(open_stats,2,(2*BYTES) as u64);
    assert_eq!((opening.nu,opening.sigma,opening.first_messages.len(),opening.second_messages.len()),(9,9,9,9));
    let pcs_bytes = pcs::encode_proof(&opening).unwrap();assert!(pcs_bytes.capacity()<=1024*1024);assert_eq!(pcs_bytes,dense_bytes);
    assert_eq!((producer.challenges(),producer.raw_queries(),producer.bytes_absorbed()),
        (packed_transcript.challenges(),packed_transcript.raw_queries(),packed_transcript.bytes_absorbed()));
    assert_eq!(producer.challenge_scalar(b"same-post-opening"),packed_transcript.challenge_scalar(b"same-post-opening"));
    drop(opening);drop(dense_bytes);drop(main); // release immutable MAIN handle; keep declared file
    let mut tail_bytes = expected;
    tail_bytes[INPUT_USED/8] |= 1<<(INPUT_USED%8);tail_bytes[(N-1)/8] |= 1<<((N-1)%8);
    for i in 0..BYTES { let delta = (u8::from(i==INPUT_USED/8)<<(INPUT_USED%8)) |
        (u8::from(i==(N-1)/8)<<((N-1)%8));assert_eq!(tail_bytes[i],expected[i]|delta); }
    assert_eq!(tail_bytes[NEIGHBOR_INPUT/8],0x08);assert_eq!(tail_bytes[BYTES-1],0x80);
    let mut writer = PackedFileWriter::create_new(&tail_path,18).unwrap(); writer.write_bytes(&tail_bytes).unwrap();
    let tail = writer.finish().unwrap();wrote_once(tail.io_metrics_snapshot());
    lock_controls(&tail,&tail_path);checked_snapshot(&tail,&tail_bytes);
    // Retained actual dense oracle values were captured before dropping the only X.
    for (point,main_value) in non_boolean_points().into_iter().zip(scalar_oracles) {
        assert_eq!(tail.evaluate(&point).unwrap(),main_value+eq(&point,INPUT_USED)+eq(&point,N-1));
    }
    assert_eq!(tail.evaluate(&selector(INPUT_USED)).unwrap(),Fr::one());
    assert_eq!(tail.evaluate(&selector(N-1)).unwrap(),Fr::one());
    assert_ne!(tail.evaluate(&selector(INPUT_USED)).unwrap(),bit(&expected,INPUT_USED),"isolated first-tail omission");
    assert_ne!(tail.evaluate(&selector(N-1)).unwrap(),bit(&expected,N-1),"isolated last-tail omission");
    let tail_value = tail.evaluate(&claim.point).unwrap();
    let tail_delta = eq(&claim.point,INPUT_USED)+eq(&claim.point,N-1);
    assert!(!tail_delta.is_zero(),"decisive scalar-tail fixture");assert_eq!(tail_value,claim.value+tail_delta);
    drop(tail);drop(committed);drop(setup);drop(c); // no witness, reader, rows or prover generators in final consumer
    let started = Instant::now();let key = verifier_key::admit(18,KEY).unwrap();let key_admit_us = micros(started);
    assert_eq!(key.id(),&SETUP_ID);assert_eq!(key.log_n(),18);assert_eq!(KEY.len(),19824);
    let final_proof = pcs::decode_proof(&pcs_bytes,18).unwrap();assert_eq!(pcs::encode_proof(&final_proof).unwrap(),pcs_bytes);
    let started = Instant::now();pcs::verify_admitted(statement.commitment(),verified.value,&verified.point,&final_proof,&key,&mut continuation.clone()).unwrap();let pcs_verify_us = micros(started);
    assert!(pcs::verify_admitted(statement.commitment(),verified.value+Fr::one(),&verified.point,&final_proof,&key,&mut continuation.clone()).is_err());
    assert!(pcs::verify_admitted(statement.commitment(),tail_value,&verified.point,&final_proof,&key,&mut continuation.clone()).is_err(),"ONLY scalar value differs, no tail proof generated");
    let entries:Vec<_> = fs::read_dir(&dir).unwrap().map(|e|e.unwrap().file_name()).collect();assert_eq!(entries.len(),2);
    assert!(entries.contains(&main_path.file_name().unwrap().to_os_string()));assert!(entries.contains(&tail_path.file_name().unwrap().to_os_string()));
    for path in [&main_path,&tail_path] {let m=fs::symlink_metadata(path).unwrap();assert!(m.file_type().is_file());assert!(!m.file_type().is_symlink());assert_eq!(m.len(),BYTES as u64);}
    let diagnostic = Diagnostic {schema:1,log_n:18,input_extent:N as u64,packed_file_bytes:BYTES as u64,subset_entries:2048,
        commit_read_calls:commit_stats.read_calls,commit_read_bytes:commit_stats.read_bytes,
        eval_read_calls:eval_stats.read_calls,eval_read_bytes:eval_stats.read_bytes,
        open_read_calls:open_stats.read_calls,open_read_bytes:open_stats.read_bytes,
        write_calls:write_stats.write_calls,write_bytes:write_stats.write_bytes,sync_calls:write_stats.sync_calls,
        main_file_bytes:BYTES as u64,tail_file_bytes:BYTES as u64,gkr_bytes:gkr_bytes.len() as u64,dory_bytes:pcs_bytes.len() as u64,
        commit_equal:true,proof_equal:true,continuation_equal:true,controls_pass:true,
        commit_read_ns:nanos(commit_stats.read_ns),eval_read_ns:nanos(eval_stats.read_ns),open_read_ns:nanos(open_stats.read_ns),
        write_ns:nanos(write_stats.write_ns),sync_ns:nanos(write_stats.sync_ns),packing_us,finish_us,reference_us,setup_us,
        dense_commit_us,gkr_prove_us,gkr_codec_verify_us,dense_open_us,packed_commit_us,packed_open_us,key_admit_us,pcs_verify_us};
    let json = serde_json::to_string(&diagnostic).unwrap();assert!(json.len()<=8192);
    let value:serde_json::Value=serde_json::from_str(&json).unwrap();assert_eq!(value.as_object().unwrap().len(),39);
    let decoded:Diagnostic=serde_json::from_str(&json).unwrap();assert_eq!(serde_json::to_string(&decoded).unwrap(),json);
    let mut extra=value;extra["unexpected"]=true.into();assert!(serde_json::from_value::<Diagnostic>(extra).is_err());
    assert!(serde_json::from_str::<Diagnostic>(&json.replacen("\"schema\":1","\"schema\":1,\"schema\":1",1)).is_err());
    let line=format!("\nONE_HEADER_PACKED_PCS_DIAGNOSTIC_V1 {json}\n");
    let mut stdout=io::stdout().lock();stdout.write_all(line.as_bytes()).unwrap();stdout.flush().unwrap();
}

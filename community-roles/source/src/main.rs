use blake2::digest::{Update, VariableOutput};
use blake2::Blake2bVar;
use nipopow_gkr_dory_prototype::{circuit, gkr, packed, pcs, sparse, sparse_stream, sparse_stream_boolean, verifier_key, transcript::Transcript};
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::fs::{self, OpenOptions};
use std::io::{Read, Write};
use std::path::Path;
use std::time::Instant;

const MAGIC: &[u8; 16] = b"NIPOGKRDORY00001";
const PROFILE: &str = "blake2b256-single-block-localops-v1";
const REPEAT_PROFILE: &str = "blake2b256-repeated-localops-v1";
const SPARSE_PROFILE: &str = "blake2b256-sparse-localops-v1";
const MAX_FILE: u64 = 8 * 1024 * 1024;

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Statement {
    profile: String,
    message_len: u16,
    digest: [u8; 32],
    anchor: [u8; 32],
    #[serde(default)]
    log_copies: u8,
}

impl Statement {
    fn validate(&self) -> Result<(), String> {
        if self.message_len > 128 || !(
            (self.profile == PROFILE && self.log_copies == 0)
            || ((self.profile == REPEAT_PROFILE || self.profile == SPARSE_PROFILE) && self.log_copies <= 3)) {
            return Err("unsupported public profile or message length".into());
        }
        Ok(())
    }

    fn bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&(self.profile.len() as u32).to_le_bytes());
        out.extend_from_slice(self.profile.as_bytes());
        out.extend_from_slice(&self.message_len.to_le_bytes());
        out.extend_from_slice(&self.digest);
        out.extend_from_slice(&self.anchor);
        if self.profile != PROFILE { out.push(self.log_copies); }
        out
    }

    fn repeated(&self) -> bool { self.profile == REPEAT_PROFILE }
    fn copies(&self) -> usize { 1usize << self.log_copies }
}

enum Graph { Layered(Vec<gkr::Layer>), Sparse(sparse::Circuit) }

struct Prepared {
    input: Option<Vec<ark_bn254::Fr>>,
    input_len: usize,
    graph: Graph,
    stats: circuit::Stats,
}

impl Prepared {
    fn build(statement: &Statement, message: Option<&[u8]>) -> Result<Self, String> {
        if statement.profile == SPARSE_PROFILE {
            let compiled = circuit::build_sparse(message, statement.message_len as usize, statement.digest)?;
            Ok(Self { input: compiled.input, input_len: compiled.circuit.input_len,
                graph: Graph::Sparse(compiled.circuit), stats: compiled.stats })
        } else {
            let compiled = circuit::build(message, statement.message_len as usize, statement.digest, circuit::Mode::LocalOps)?;
            Ok(Self { input: compiled.input, input_len: compiled.input_len,
                graph: Graph::Layered(compiled.layers), stats: compiled.stats })
        }
    }

    fn layers(&self) -> usize {
        match &self.graph { Graph::Layered(layers) => layers.len(), Graph::Sparse(_) => 1 }
    }
    fn terms(&self) -> usize {
        match &self.graph { Graph::Layered(layers) => layers.iter().map(Vec::len).sum(), Graph::Sparse(c) => c.terms.len() }
    }
    fn max_width(&self) -> usize {
        match &self.graph { Graph::Layered(layers) => layers.iter().map(Vec::len).max().unwrap_or(0), Graph::Sparse(c) => c.row_count.max(c.input_len) }
    }
}

fn read_limited(path: &Path, limit: u64) -> Result<Vec<u8>, String> {
    if fs::metadata(path).map_err(|e| e.to_string())?.len() > limit {
        return Err("file exceeds admitted size".into());
    }
    let file = fs::File::open(path).map_err(|e| e.to_string())?;
    let mut bytes = Vec::new();
    file.take(limit + 1).read_to_end(&mut bytes).map_err(|e| e.to_string())?;
    if bytes.len() as u64 > limit { return Err("file grew beyond size bound".into()); }
    Ok(bytes)
}

fn read_statement(path: &Path) -> Result<Statement, String> {
    let statement: Statement = serde_json::from_slice(&read_limited(path, 4096)?)
        .map_err(|e| e.to_string())?;
    statement.validate()?;
    Ok(statement)
}

fn write_new(path: &Path, bytes: &[u8]) -> Result<(), String> {
    let mut file = OpenOptions::new().write(true).create_new(true).open(path)
        .map_err(|e| e.to_string())?;
    file.write_all(bytes).map_err(|e| e.to_string())?;
    file.sync_all().map_err(|e| e.to_string())
}

fn digest(message: &[u8]) -> [u8; 32] {
    let mut hash = Blake2bVar::new(32).expect("fixed digest length");
    hash.update(message);
    let mut out = [0; 32];
    hash.finalize_variable(&mut out).expect("fixed output length");
    out
}

fn fixture(dir: &Path, len: usize, profile: &str, log_copies: u8) -> Result<(), String> {
    if len > 128 || log_copies > 3 { return Err("fixture exceeds length/copy bound".into()); }
    fs::create_dir(dir).map_err(|e| e.to_string())?;
    let message: Vec<u8> = (0..len).map(|i| ((i * 37 + 11) & 255) as u8).collect();
    let statement = Statement { profile: profile.into(), message_len: len as u16,
        digest: digest(&message), anchor: digest(b"bounded-gkr-dory-fixture-anchor-v1"), log_copies };
    write_new(&dir.join("statement.json"), &serde_json::to_vec_pretty(&statement).unwrap())?;
    write_new(&dir.join("message.bin"), &message)?;
    println!("{}", json!({"status":"fixture_created","message_bytes":len,"copies":statement.copies(),
        "scope":"synthetic hash fixture; no Ergo history claim"}));
    Ok(())
}

struct Envelope {
    statement: Vec<u8>,
    setup_id: [u8; 32],
    commitment: Vec<u8>,
    gkr: Vec<u8>,
    dory: Vec<u8>,
}

fn put_blob(out: &mut Vec<u8>, bytes: &[u8]) -> Result<(), String> {
    let len = u32::try_from(bytes.len()).map_err(|_| "oversized blob")?;
    out.extend_from_slice(&len.to_le_bytes());
    out.extend_from_slice(bytes);
    Ok(())
}

impl Envelope {
    fn encode(&self) -> Result<Vec<u8>, String> {
        let mut out = MAGIC.to_vec();
        put_blob(&mut out, &self.statement)?;
        out.extend_from_slice(&self.setup_id);
        put_blob(&mut out, &self.commitment)?;
        put_blob(&mut out, &self.gkr)?;
        put_blob(&mut out, &self.dory)?;
        if out.len() as u64 > MAX_FILE { return Err("proof exceeds file bound".into()); }
        Ok(out)
    }

    fn decode(bytes: &[u8]) -> Result<Self, String> {
        fn take<'a>(bytes: &mut &'a [u8], len: usize) -> Result<&'a [u8], String> {
            if bytes.len() < len { return Err("truncated envelope".into()); }
            let (head, tail) = bytes.split_at(len); *bytes = tail; Ok(head)
        }
        fn blob(bytes: &mut &[u8], max: usize) -> Result<Vec<u8>, String> {
            let n = u32::from_le_bytes(take(bytes, 4)?.try_into().unwrap()) as usize;
            if n > max { return Err("envelope component exceeds bound".into()); }
            Ok(take(bytes, n)?.to_vec())
        }
        if bytes.len() as u64 > MAX_FILE { return Err("proof exceeds file bound".into()); }
        let mut cursor = bytes;
        if take(&mut cursor, 16)? != MAGIC { return Err("wrong proof version".into()); }
        let statement = blob(&mut cursor, 1024)?;
        let setup_id = take(&mut cursor, 32)?.try_into().unwrap();
        let commitment = blob(&mut cursor, 4096)?;
        let gkr = blob(&mut cursor, 4 * 1024 * 1024)?;
        let dory = blob(&mut cursor, 1024 * 1024)?;
        if !cursor.is_empty() { return Err("trailing proof bytes".into()); }
        Ok(Self { statement, setup_id, commitment, gkr, dory })
    }
}

fn start_transcript(statement: &Statement, setup_id: &[u8; 32], log_n: usize, commitment: &[u8]) -> Transcript {
    let mut transcript = Transcript::new(b"nipopow-gkr-dory-bounded-hash-v1");
    transcript.append_bytes(b"vendor-pin", pcs::VENDOR_PIN);
    transcript.append_bytes(b"mode", b"Transparent-nonzero-fs-v1");
    transcript.append_bytes(b"public-statement", &statement.bytes());
    transcript.append_bytes(b"setup-identity", setup_id);
    transcript.append_u64(b"input-log-size", log_n as u64);
    transcript.append_bytes(b"input-commitment", commitment);
    transcript
}

fn prove(statement_path: &Path, message_path: &Path, proof_path: &Path) -> Result<(), String> {
    let all = Instant::now();
    let statement = read_statement(statement_path)?;
    let message = read_limited(message_path, 128)?;
    if message.len() != statement.message_len as usize || digest(&message) != statement.digest {
        return Err("private message does not match public length/digest".into());
    }
    let timer = Instant::now();
    let compiled = Prepared::build(&statement, Some(&message))?;
    let circuit_seconds = timer.elapsed().as_secs_f64();
    let base_input = compiled.input.as_ref().ok_or("missing private input")?;
    let input = base_input.repeat(statement.copies());
    if !compiled.input_len.is_power_of_two() { return Err("invalid circuit input width".into()); }
    let log_n = input.len().trailing_zeros() as usize;
    let timer = Instant::now();
    let setup = pcs::generate_setup(log_n)?;
    let setup_seconds = timer.elapsed().as_secs_f64();
    let timer = Instant::now();
    let committed = pcs::commit(&input, &setup)?;
    let commitment_seconds = timer.elapsed().as_secs_f64();
    let commitment_bytes = pcs::encode_commitment(&committed.commitment)?;
    let mut transcript = start_transcript(&statement, &setup.id, setup.log_n, &commitment_bytes);
    let timer = Instant::now();
    let (gkr_proof, claim) = match &compiled.graph {
        Graph::Sparse(c) => sparse::prove(c, &input, statement.log_copies as usize, &mut transcript),
        Graph::Layered(layers) if statement.repeated() => gkr::prove_repeated(&input, compiled.input_len, layers, statement.log_copies as usize, &mut transcript),
        Graph::Layered(layers) => gkr::prove(&input, layers, &mut transcript),
    }.map_err(|e| e.to_string())?;
    let gkr_seconds = timer.elapsed().as_secs_f64();
    if gkr::mle(&input, &claim.point).map_err(|e| e.to_string())? != claim.value {
        return Err("GKR returned an inconsistent input claim".into());
    }
    let timer = Instant::now();
    let dory_proof = pcs::open(&committed, &claim.point, &setup, &mut transcript)?;
    let dory_seconds = timer.elapsed().as_secs_f64();
    let envelope = Envelope { statement: statement.bytes(), setup_id: setup.id,
        commitment: commitment_bytes, gkr: gkr::encode_proof(&gkr_proof)?, dory: pcs::encode_proof(&dory_proof)? };
    let encoded = envelope.encode()?;
    write_new(proof_path, &encoded)?;
    println!("{}", json!({"status":"proof_exported","profile":statement.profile,
        "message_bytes":message.len(),"input_fields":input.len(),"copies":statement.copies(),
        "layers":compiled.layers(),"gates":compiled.terms()*statement.copies(),
        "base_circuit_gates":compiled.terms(),
        "max_layer_width":compiled.max_width()*statement.copies(),
        "circuit_stats":format!("{:?}",compiled.stats),"circuit_seconds":circuit_seconds,
        "setup_seconds":setup_seconds,"commitment_seconds":commitment_seconds,
        "gkr_seconds":gkr_seconds,"dory_seconds":dory_seconds,"total_seconds":all.elapsed().as_secs_f64(),
        "gkr_bytes":envelope.gkr.len(),"dory_bytes":envelope.dory.len(),"proof_bytes":encoded.len(),
        "scalar_challenges":transcript.challenges(),"raw_hash_queries":transcript.raw_queries(),
        "transcript_input_bytes":transcript.bytes_absorbed(),"threads":1,
        "scope":"copies of the same public single-block hash; no full Ergo relation/security qualification"}));
    Ok(())
}

enum VerificationParameters {
    Generated(pcs::Setup),
    Pinned(verifier_key::AdmittedVerifierKey),
}

impl VerificationParameters {
    fn id(&self) -> &[u8; 32] {
        match self {
            Self::Generated(setup) => &setup.id,
            Self::Pinned(key) => key.id(),
        }
    }
}

fn verify(statement_path: &Path, proof_path: &Path, key_path: Option<&Path>) -> Result<(), String> {
    let all = Instant::now();
    let statement = read_statement(statement_path)?;
    let encoded = read_limited(proof_path, MAX_FILE)?;
    let envelope = Envelope::decode(&encoded)?;
    if envelope.statement != statement.bytes() { return Err("public statement mismatch".into()); }
    let timer = Instant::now();
    let compiled = Prepared::build(&statement, None)?;
    if compiled.input.is_some() { return Err("verifier unexpectedly has a witness".into()); }
    let circuit_seconds = timer.elapsed().as_secs_f64();
    if !compiled.input_len.is_power_of_two() { return Err("invalid circuit input width".into()); }
    let input_len = compiled.input_len.checked_mul(statement.copies()).ok_or("expanded input overflow")?;
    let log_n = input_len.trailing_zeros() as usize;
    let timer = Instant::now();
    let parameters = match key_path {
        Some(path) => {
            // This file is untrusted input. Its expected digest and original
            // setup ID come exclusively from the verifier's compiled pins.
            let bytes = read_limited(path, verifier_key::MAX_PINNED_KEY_BYTES as u64)?;
            VerificationParameters::Pinned(verifier_key::admit(log_n, &bytes)?)
        }
        None => VerificationParameters::Generated(pcs::generate_setup(log_n)?),
    };
    let parameter_seconds = timer.elapsed().as_secs_f64();
    let (parameter_mode, setup_seconds, vk_load_validate_seconds) = match &parameters {
        VerificationParameters::Generated(_) => ("generated_setup", parameter_seconds, 0.0),
        VerificationParameters::Pinned(_) => ("pinned_verifier_key", 0.0, parameter_seconds),
    };
    if &envelope.setup_id != parameters.id() { return Err("setup identity mismatch".into()); }
    let commitment = pcs::decode_commitment(&envelope.commitment)?;
    let gkr_proof = match &compiled.graph {
        Graph::Sparse(c) => sparse::decode_proof(c, statement.log_copies as usize, &envelope.gkr)?,
        Graph::Layered(layers) if statement.repeated() => gkr::decode_repeated_proof(compiled.input_len, layers, statement.log_copies as usize, &envelope.gkr)?,
        Graph::Layered(layers) => gkr::decode_proof(compiled.input_len, layers, &envelope.gkr)?,
    };
    let dory_proof = pcs::decode_proof(&envelope.dory, log_n)?;
    let mut transcript = start_transcript(&statement, parameters.id(), log_n, &envelope.commitment);
    let timer = Instant::now();
    let claim = match &compiled.graph {
        Graph::Sparse(c) => sparse::verify(c, statement.log_copies as usize, &gkr_proof, &mut transcript),
        Graph::Layered(layers) if statement.repeated() => gkr::verify_repeated(compiled.input_len, layers, statement.log_copies as usize, &gkr_proof, &mut transcript),
        Graph::Layered(layers) => gkr::verify(compiled.input_len, layers, &gkr_proof, &mut transcript),
    }.map_err(|e| e.to_string())?;
    let gkr_seconds = timer.elapsed().as_secs_f64();
    let timer = Instant::now();
    match &parameters {
        VerificationParameters::Generated(setup) =>
            pcs::verify(commitment, claim.value, &claim.point, &dory_proof, setup, &mut transcript)?,
        VerificationParameters::Pinned(key) =>
            pcs::verify_admitted(commitment, claim.value, &claim.point, &dory_proof, key, &mut transcript)?,
    }
    let dory_seconds = timer.elapsed().as_secs_f64();
    println!("{}", json!({"status":"verified","private_witness_loaded":false,
        "profile":statement.profile,"message_bytes":statement.message_len,"proof_bytes":encoded.len(),
        "input_fields":input_len,"copies":statement.copies(),"layers":compiled.layers(),
        "gates":compiled.terms()*statement.copies(),
        "base_circuit_gates":compiled.terms(),
        "circuit_seconds":circuit_seconds,"setup_seconds":setup_seconds,
        "parameter_mode":parameter_mode,"vk_load_validate_seconds":vk_load_validate_seconds,
        "gkr_seconds":gkr_seconds,"dory_seconds":dory_seconds,"total_seconds":all.elapsed().as_secs_f64(),
        "scalar_challenges":transcript.challenges(),"raw_hash_queries":transcript.raw_queries(),
        "transcript_input_bytes":transcript.bytes_absorbed(),"threads":1,
        "scope":"fixed base-circuit scan with repeated-copy factorization; no heterogeneous Ergo history or streaming producer claim"}));
    Ok(())
}

fn prove_stream(statement_path: &Path, message_path: &Path, proof_path: &Path, boolean: bool) -> Result<(), String> {
    let all = Instant::now();
    let statement = read_statement(statement_path)?;
    if statement.profile != SPARSE_PROFILE { return Err("streaming requires sparse profile".into()); }
    let message = read_limited(message_path, 128)?;
    if message.len() != statement.message_len as usize || digest(&message) != statement.digest {
        return Err("private message does not match public length/digest".into());
    }
    let timer = Instant::now();
    let mut compiled = Prepared::build(&statement, Some(&message))?;
    let circuit_seconds = timer.elapsed().as_secs_f64();
    let Graph::Sparse(circuit) = &compiled.graph else { return Err("expected sparse circuit".into()); };
    let input_len = compiled.input_len.checked_mul(statement.copies()).ok_or("expanded input overflow")?;
    let log_n = input_len.trailing_zeros() as usize;
    let timer = Instant::now();
    let base = compiled.input.take().ok_or("missing private input")?;
    let mut packed_base = vec![0u8; base.len().div_ceil(8)];
    for (index, value) in base.iter().enumerate() {
        if *value == ark_bn254::Fr::from(1u64) { packed_base[index / 8] |= 1 << (index % 8); }
        else if *value != ark_bn254::Fr::from(0u64) { return Err("nonbinary private witness".into()); }
    }
    drop(base);
    let witness_path = proof_path.with_extension("witness.bits");
    let mut file = OpenOptions::new().write(true).create_new(true).open(&witness_path).map_err(|e| e.to_string())?;
    for _ in 0..statement.copies() { file.write_all(&packed_base).map_err(|e| e.to_string())?; }
    file.sync_all().map_err(|e| e.to_string())?;
    drop(file);
    drop(packed_base);
    let source = packed::PackedFile::open(&witness_path, log_n)?;
    let witness_seconds = timer.elapsed().as_secs_f64();
    let timer = Instant::now();
    let setup = pcs::generate_setup(log_n)?;
    let setup_seconds = timer.elapsed().as_secs_f64();
    let timer = Instant::now();
    let committed = packed::commit(&source, &setup)?;
    let commitment_seconds = timer.elapsed().as_secs_f64();
    let commitment_bytes = pcs::encode_commitment(&committed.commitment)?;
    let mut transcript = start_transcript(&statement, &setup.id, setup.log_n, &commitment_bytes);
    let mut copy_reads = 0u64;
    let timer = Instant::now();
    let mut read_copy = |copy| {
        copy_reads += 1;
        source.read_copy(compiled.input_len, copy).map_err(|_| gkr::GkrError::InvalidInputWidth)
    };
    let (gkr_proof, claim) = if boolean {
        sparse_stream_boolean::prove(circuit, statement.log_copies as usize, &mut read_copy, &mut transcript)
            .map_err(|e| e.to_string())?
    } else {
        sparse_stream::prove(circuit, statement.log_copies as usize, &mut read_copy, &mut transcript)
            .map_err(|e| e.to_string())?
    };
    let gkr_seconds = timer.elapsed().as_secs_f64();
    if source.evaluate(&claim.point)? != claim.value { return Err("streamed GKR input claim mismatch".into()); }
    let timer = Instant::now();
    let dory_proof = packed::open(&committed, &source, &claim.point, &setup, &mut transcript)?;
    let dory_seconds = timer.elapsed().as_secs_f64();
    let envelope = Envelope { statement: statement.bytes(), setup_id: setup.id, commitment: commitment_bytes,
        gkr: gkr::encode_proof(&gkr_proof)?, dory: pcs::encode_proof(&dory_proof)? };
    let encoded = envelope.encode()?;
    write_new(proof_path, &encoded)?;
    println!("{}", json!({"status":"proof_exported","producer_mode":if boolean {"packed_streamed_boolean"} else {"packed_streamed"},
        "profile":statement.profile,"copies":statement.copies(),"input_fields":input_len,
        "base_terms":circuit.terms.len(),"base_rows":circuit.row_count,"witness_bytes":input_len.div_ceil(8),
        "circuit_seconds":circuit_seconds,"witness_seconds":witness_seconds,"setup_seconds":setup_seconds,
        "commitment_seconds":commitment_seconds,"gkr_seconds":gkr_seconds,"dory_seconds":dory_seconds,
        "total_seconds":all.elapsed().as_secs_f64(),"gkr_copy_reads":copy_reads,
        "gkr_bytes_read":copy_reads*(compiled.input_len as u64).div_ceil(8),
        "gkr_bytes":envelope.gkr.len(),"dory_bytes":envelope.dory.len(),"proof_bytes":encoded.len(),
        "scalar_challenges":transcript.challenges(),"raw_hash_queries":transcript.raw_queries(),
        "transcript_input_bytes":transcript.bytes_absorbed(),"threads":1,
        "scope":"bounded immutable-file producer; no full Ergo relation or production-time qualification"}));
    Ok(())
}

fn run() -> Result<(), String> {
    let args: Vec<String> = std::env::args().collect();
    match args.get(1).map(String::as_str) {
        Some("fixture") if args.len() == 4 => fixture(Path::new(&args[2]), args[3].parse().map_err(|_| "bad length")?, PROFILE, 0),
        Some("fixture-repeat") if args.len() == 5 => fixture(Path::new(&args[2]), args[3].parse().map_err(|_| "bad length")?, REPEAT_PROFILE, args[4].parse().map_err(|_| "bad copy dimension")?),
        Some("fixture-sparse") if args.len() == 5 => fixture(Path::new(&args[2]), args[3].parse().map_err(|_| "bad length")?, SPARSE_PROFILE, args[4].parse().map_err(|_| "bad copy dimension")?),
        Some("prove") if args.len() == 5 => prove(Path::new(&args[2]), Path::new(&args[3]), Path::new(&args[4])),
        Some("prove-stream") if args.len() == 5 => prove_stream(Path::new(&args[2]), Path::new(&args[3]), Path::new(&args[4]), false),
        Some("prove-stream-boolean") if args.len() == 5 => prove_stream(Path::new(&args[2]), Path::new(&args[3]), Path::new(&args[4]), true),
        Some("verify") if args.len() == 4 => verify(Path::new(&args[2]), Path::new(&args[3]), None),
        Some("verify-vk") if args.len() == 5 => verify(Path::new(&args[2]), Path::new(&args[3]), Some(Path::new(&args[4]))),
        _ => Err("usage: fixture <new-dir> <len<=128> | prove/prove-stream/prove-stream-boolean <statement.json> <message.bin> <new-proof> | verify <statement.json> <proof> | verify-vk <statement.json> <proof> <pinned-key>".into()),
    }
}

fn main() {
    match std::panic::catch_unwind(run) {
        Ok(Ok(())) => {},
        Ok(Err(error)) => { eprintln!("{}", json!({"status":"rejected","error":error})); std::process::exit(1); },
        Err(_) => { eprintln!("{}", json!({"status":"rejected","error":"bounded verifier/prover aborted"})); std::process::exit(2); },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn verifier_key_reader_admits_largest_pinned_fixture_at_exact_bound() {
        let path=Path::new(env!("CARGO_MANIFEST_DIR")).join("fixtures/verifier-keys-v1/log41.vk");
        let bytes=read_limited(&path,verifier_key::MAX_PINNED_KEY_BYTES as u64).unwrap();
        assert_eq!(bytes.len(),verifier_key::MAX_PINNED_KEY_BYTES);
        assert!(verifier_key::admit(41,&bytes).is_ok());
        assert!(read_limited(&path,(verifier_key::MAX_PINNED_KEY_BYTES-1) as u64).is_err());
    }
    #[test]
    fn envelope_bounds_and_exact_eof() {
        let e = Envelope { statement: vec![1;9], setup_id:[3;32],commitment:vec![4;12],gkr:vec![5;32],dory:vec![6;20] };
        let bytes=e.encode().unwrap();
        assert_eq!(Envelope::decode(&bytes).unwrap().encode().unwrap(),bytes);
        let mut trailing=bytes.clone();trailing.push(0);assert!(Envelope::decode(&trailing).is_err());
        assert!(Envelope::decode(&bytes[..bytes.len()-1]).is_err());
        let mut large=bytes.clone();large[16..20].copy_from_slice(&u32::MAX.to_le_bytes());assert!(Envelope::decode(&large).is_err());
        let mut version=bytes;version[0]^=1;assert!(Envelope::decode(&version).is_err());
    }
}

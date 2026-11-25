//! Private diagnostic orchestration; no saved prefix or caller-supplied challenges.
use super::*;
use crate::{gkr, packed::PackedFile, sparse_stream_roster as edge, transcript::Transcript};
use std::{fs::File, time::Instant};

// Constructed only by live_u after the commitment-bound transcript is created
// by this module's producer. It has no public constructor or serialized form.
struct LivePrefix {
    r: Vec<Fr>,
    u: Vec<Fr>,
    left: Fr,
    claim: Fr,
    rounds: Vec<Vec<Fr>>,
    sender: Transcript,
    reference: Transcript,
}

fn phase(start: Instant, name: &str, completed: usize) -> Result<(), String> {
    use std::io::Write;
    println!("native_role4_live_phase {}", serde_json::json!({
        "stage": name, "completed": completed, "seconds": start.elapsed().as_secs_f64()
    }));
    std::io::stdout().flush().map_err(|e| e.to_string())
}

fn same_sender(a: &Transcript, b: &Transcript) -> Result<(), String> {
    whole_require(u0_counters(a) == u0_counters(b)
        && a.clone().challenge_scalar(JH_CONTINUATION) == b.clone().challenge_scalar(JH_CONTINUATION),
        "live candidate/reference transcript mismatch")
}

fn live_u(parent: &WorkTreeHistoryPlan, height: &HeightWork<'_>, daa: &DaaHistoryRoster<'_>,
    adapter: &Role4EndpointAdapter<'_, '_>, source: &PackedFile, held: &File,
    mut sender: Transcript, start: Instant) -> Result<LivePrefix, String> {
    let binding = adapter.binding();
    let r = gkr::output_point(1usize << 32, &mut sender);
    gkr::append_usize(&mut sender, b"gkr-layer-index", 0);
    let mut reference = sender.clone();
    phase(start, "u-census", 0)?;
    let counts = edge::edge_u0_census_for_test(20, 12, 19, &[19, 19],
        |left, owner, sink| adapter.visit_endpoint(&binding, left, owner, |term| sink(term)).map(|_| ()),
        |_, _| Ok(()))?;
    whole_require(counts.len() == 4096 && counts.iter().sum::<usize>() as u64 == U0_TERMS,
        "live U owner census")?;
    phase(start, "u-local", 0)?;
    let candidate = edge::edge_u_sequence_for_test(20, 12, 19, 1, &[19, 19], &counts,
        &r, 20, &mut sender,
        |left, owner, sink| adapter.visit_endpoint(&binding, left, owner, |term| sink(term)).map(|_| ()),
        |owner| crate::packed_rows::read_row(source, 1 << 20, owner),
        |event| {
            match event {
                edge::EdgeUSequenceEvent::Progress(round, owner, _) if owner % 1024 == 0 =>
                    phase(start, "u-local-owners", round * 4096 + owner)?,
                edge::EdgeUSequenceEvent::Closed(round) => phase(start, "u-local-round", round.round + 1)?,
                _ => (),
            }
            Ok(())
        })?;
    whole_require(candidate.rounds.len() == 20 && candidate.terminals.len() == 4096,
        "live U result shape")?;
    let weights = U0OracleWeights::new(&r)?;
    let aliases = whole_aliases(daa)?;
    let numeric = crate::daa_work_actions::DaaWorkActions::new(parent)?;
    let identity = u0_file_info(held)?;
    let mut bytes = U0ByteCache { file: held.try_clone().map_err(|e| e.to_string())?,
        rows: std::collections::VecDeque::new(), loads: 0, bytes: 0, capacity_peak: 0 };
    let mut polynomials = vec![[Fr::zero(); 3]; 20];
    let mut oracle_terminals = Vec::with_capacity(4096);
    let mut terms = 0u64;
    phase(start, "u-canonical", 0)?;
    for owner in 0..4096 {
        let mut a = vec![Fr::zero(); 1 << 20];
        let mut b = vec![Fr::zero(); 1 << 20];
        let mut x = useq_legacy_row(source, owner)?;
        whole_oracle_partition(height, daa, &numeric, &aliases, true, owner, |term| {
            whole_require(term.left / (1 << 20) == owner, "live canonical LEFT owner")?;
            let y = bytes.bit(term.right)?;
            let weight = weights.at(term.row)?;
            let wire = term.left % (1 << 20);
            a[wire] += weight * (term.c[1] + term.c[3] * y);
            b[wire] += weight * (term.c[0] + term.c[2] * y);
            terms = terms.checked_add(1).ok_or("live U oracle count overflow")?;
            Ok(())
        })?;
        for (index, round) in candidate.rounds.iter().enumerate() {
            let polynomial = useq_message(&a, &b, &x);
            for i in 0..3 { polynomials[index][i] += polynomial[i]; }
            useq_fold(&mut a, round.challenge);
            useq_fold(&mut b, round.challenge);
            useq_fold(&mut x, round.challenge);
        }
        let terminal = [a[0], b[0], x[0]];
        useq_terminal_compare(candidate.terminals[owner], terminal)?;
        oracle_terminals.push(terminal);
        if (owner + 1) % 1024 == 0 { phase(start, "u-canonical", owner + 1)?; }
    }
    whole_require(terms == U0_TERMS && u0_file_info(&bytes.file)? == identity,
        "live U oracle coverage and held identity")?;
    let mut claim = Fr::zero();
    let mut u = Vec::with_capacity(32);
    for (index, round) in candidate.rounds.iter().enumerate() {
        whole_require(polynomials[index] == round.polynomial && round.previous_claim == claim,
            "live U independent polynomial/previous claim")?;
        let (challenge, next) = useq_reference_send(polynomials[index], claim, &mut reference)?;
        whole_require(challenge == round.challenge && next == round.claim
            && u0_counters(&reference) == round.counters
            && reference.clone().challenge_scalar(b"native-u-sequence-continuation") == round.continuation,
            "live U reference sender round")?;
        u.push(challenge);
        claim = next;
    }
    same_sender(&sender, &reference)?;
    let mut rounds = candidate.rounds.iter().map(|round| round.polynomial.to_vec()).collect::<Vec<_>>();
    let mut candidate_claim = claim;
    let (high, left) = gkr::prove_phase(candidate.terminals.iter().map(|t| t[0]).collect(),
        candidate.terminals.iter().map(|t| t[1]).collect(),
        &candidate.terminals.iter().map(|t| t[2]).collect::<Vec<_>>(),
        &mut candidate_claim, &mut rounds, &mut sender).map_err(|e| e.to_string())?;
    whole_require(high.len() == 12 && rounds.len() == 32, "live high U shape")?;
    let mut a = oracle_terminals.iter().map(|t| t[0]).collect::<Vec<_>>();
    let mut b = oracle_terminals.iter().map(|t| t[1]).collect::<Vec<_>>();
    let mut x = oracle_terminals.iter().map(|t| t[2]).collect::<Vec<_>>();
    for index in 0..12 {
        let polynomial = useq_message(&a, &b, &x);
        whole_require(rounds[20 + index] == polynomial, "live high U polynomial")?;
        let (challenge, next) = useq_reference_send(polynomial, claim, &mut reference)?;
        whole_require(challenge == high[index], "live high U challenge")?;
        useq_fold(&mut a, challenge); useq_fold(&mut b, challenge); useq_fold(&mut x, challenge);
        u.push(challenge); claim = next;
    }
    whole_require(candidate_claim == claim && left == x[0] && u.len() == 32,
        "live U terminal claim/value")?;
    same_sender(&sender, &reference)?;
    phase(start, "u-complete", 32)?;
    Ok(LivePrefix { r, u, left, claim, rounds, sender, reference })
}

fn live_v(parent: &WorkTreeHistoryPlan, height: &HeightWork<'_>, daa: &DaaHistoryRoster<'_>,
    adapter: &Role4EndpointAdapter<'_, '_>, source: &PackedFile,
    prefix: LivePrefix, start: Instant) -> Result<(gkr::GkrProof, gkr::InputClaim, Transcript), String> {
    let LivePrefix { r, u, left, mut claim, mut rounds, mut sender, mut reference } = prefix;
    let prefix_claim = claim;
    let binding = adapter.binding();
    let counts = edge::edge_v_census_for_test(20, 12, 19, 1, &[19, 19],
        |side, owner, sink| adapter.visit_endpoint(&binding, side, owner, |term| sink(term)).map(|_| ()),
        |_, _| Ok(()))?;
    whole_require(counts.len() == 4096 && v_sum_usize_counts(&counts)? == U0_TERMS, "live V census")?;
    let context = edge::EdgeGroupedVContextForTest::new(adapter, &r, &u, left)?;
    whole_require(context.template_visits() == 155648, "live V family census")?;
    let mut candidate = edge::EdgeGroupedVCandidateForTest::new(
        |owner| crate::packed_rows::read_row(source, 1 << 20, owner), 1 << 20, 4096)?;
    let mut ledgers = Vec::with_capacity(20);
    let mut qs = Vec::with_capacity(20);
    let mut polynomials = Vec::with_capacity(20);
    for round in 0..20 {
        let mut ledger = Vec::with_capacity(4096);
        let mut sum = [Fr::zero(); 3];
        let mut metrics = edge::EdgeGroupedVMetricsForTest::default();
        for owner in 0..4096 {
            let result = candidate.local_owner_deferred(&context, owner, counts[owner], &qs)?;
            vc_metric_add(&mut metrics, &result.metrics)?;
            ledger.push(VOwnerRecord { count: counts[owner], polynomial: result.message });
            for i in 0..3 { sum[i] += result.message[i]; }
        }
        vc_census_guard(&metrics)?;
        let (challenge, next) = edge::edge_u_sequence_send_for_test(sum, claim, &mut sender)?;
        claim = next; qs.push(challenge); polynomials.push(sum); ledgers.push(ledger);
        phase(start, "v-local-round", round + 1)?;
    }
    let mut terminals = Vec::with_capacity(4096);
    for owner in 0..4096 {
        let result = candidate.terminal_owner(&context, owner, counts[owner], &qs)?;
        whole_require(result.message.is_empty(), "live V terminal cannot emit a round")?;
        terminals.push([result.terminal.0, result.terminal.1, result.folded_x]);
        if (owner + 1) % 1024 == 0 { phase(start, "v-terminal", owner + 1)?; }
    }
    drop(candidate);

    // Reference channels are accumulated during the existing canonical pass;
    // the receiver later computes the analytic coefficients independently.
    let rows = U0OracleWeights::new(&r)?;
    let uweights = U0OracleWeights::new(&u)?;
    let mut padded_v = qs.clone(); padded_v.resize(32, Fr::zero());
    let vweights = U0OracleWeights::new(&padded_v)?;
    let aliases = whole_aliases(daa)?;
    let numeric = crate::daa_work_actions::DaaWorkActions::new(parent)?;
    let mut reference_polynomials = vec![[Fr::zero(); 3]; 20];
    let mut reference_terminals = Vec::with_capacity(4096);
    let mut channels = Vec::with_capacity(4096);
    let mut terms = 0u64;
    for owner in 0..4096 {
        let mut a = vec![Fr::zero(); 1 << 20];
        let mut b = vec![Fr::zero(); 1 << 20];
        let mut x = useq_legacy_row(source, owner)?;
        let mut count = 0usize;
        let mut local_channels = [Fr::zero(); 4];
        whole_oracle_partition(height, daa, &numeric, &aliases, false, owner, |term| {
            whole_require(term.right / (1 << 20) == owner, "live canonical RIGHT owner")?;
            let weight = rows.at(term.row)? * uweights.at(term.left)?;
            let wire = term.right % (1 << 20);
            a[wire] += weight * (term.c[2] + term.c[3] * left);
            b[wire] += weight * (term.c[0] + term.c[1] * left);
            let projected = weight * vweights.at(wire)?;
            for i in 0..4 { local_channels[i] += projected * term.c[i]; }
            count = count.checked_add(1).ok_or("live canonical count overflow")?;
            Ok(())
        })?;
        whole_require(count == counts[owner], "live V canonical owner count")?;
        terms = terms.checked_add(count as u64).ok_or("live canonical total overflow")?;
        for round in 0..20 {
            let polynomial = useq_message(&a, &b, &x);
            v_owner_compare(count, polynomial, ledgers[round][owner].count, ledgers[round][owner].polynomial)?;
            for i in 0..3 { reference_polynomials[round][i] += polynomial[i]; }
            useq_fold(&mut a, qs[round]); useq_fold(&mut b, qs[round]); useq_fold(&mut x, qs[round]);
        }
        let terminal = [a[0], b[0], x[0]];
        vc_terminal_guard(terminals[owner], terminal)?;
        whole_require(local_channels[2] + local_channels[3] * left == a[0]
            && local_channels[0] + local_channels[1] * left == b[0], "live canonical channel combination")?;
        channels.push(local_channels); reference_terminals.push(terminal);
        if (owner + 1) % 1024 == 0 { phase(start, "v-canonical", owner + 1)?; }
    }
    whole_require(terms == U0_TERMS, "live canonical V coverage")?;
    let mut reference_claim = prefix_claim;
    for round in 0..20 {
        whole_require(polynomials[round] == reference_polynomials[round], "live V canonical polynomial")?;
        let (challenge, next) = useq_reference_send(reference_polynomials[round], reference_claim, &mut reference)?;
        whole_require(challenge == qs[round], "live V independent challenge")?;
        reference_claim = next;
        rounds.push(polynomials[round].to_vec());
    }
    whole_require(reference_claim == claim, "live V local terminal claim")?;
    same_sender(&sender, &reference)?;
    let (high, right) = gkr::prove_phase(terminals.iter().map(|t| t[0]).collect(),
        terminals.iter().map(|t| t[1]).collect(), &terminals.iter().map(|t| t[2]).collect::<Vec<_>>(),
        &mut claim, &mut rounds, &mut sender).map_err(|e| e.to_string())?;
    whole_require(high.len() == 12 && rounds.len() == 64, "live high V shape")?;
    let mut a = reference_terminals.iter().map(|t| t[0]).collect::<Vec<_>>();
    let mut b = reference_terminals.iter().map(|t| t[1]).collect::<Vec<_>>();
    let mut x = reference_terminals.iter().map(|t| t[2]).collect::<Vec<_>>();
    for round in 0..12 {
        let polynomial = useq_message(&a, &b, &x);
        whole_require(rounds[52 + round] == polynomial, "live high V polynomial")?;
        let (challenge, next) = useq_reference_send(polynomial, reference_claim, &mut reference)?;
        whole_require(challenge == high[round], "live high V challenge")?;
        reference_claim = next;
        useq_fold(&mut a, challenge); useq_fold(&mut b, challenge); useq_fold(&mut x, challenge);
    }
    whole_require(right == x[0] && reference_claim == claim, "live high V terminal")?;
    same_sender(&sender, &reference)?;
    let mut v = qs; v.extend_from_slice(&high);
    let mut coefficients = [Fr::zero(); 4];
    for owner in 0..4096 {
        let selector = u0_direct_weight(&v[20..], owner);
        for i in 0..4 { coefficients[i] += channels[owner][i] * selector; }
    }
    whole_require(coefficients == adapter.coefficients(&r, &u, &v)?,
        "live analytic/canonical wiring mismatch")?;
    whole_require(coefficients[0] + coefficients[1] * left + coefficients[2] * right
        + coefficients[3] * left * right == claim, "live wiring terminal relation")?;

    let mut line = vec![Fr::zero(); 33];
    let mut reference_line = line.clone();
    for owner in 0..4096 {
        let candidate_x = crate::packed_rows::read_row(source, 1 << 20, owner)?;
        let canonical_x = useq_legacy_row(source, owner)?;
        vc_line_inputs(owner, owner, owner, &candidate_x, &canonical_x, &u[..20], &v[..20], &u[..20], &v[..20])?;
        drop(canonical_x);
        let local = gkr::line_polynomial(&candidate_x, &u[..20], &v[..20]);
        whole_require(local.len() == 21, "live local line shape")?;
        let contribution = edge::edge_line_owner_contribution_for_test(owner, &local, &u[20..], &v[20..])?;
        let canonical = vc_reference_contribution(owner, &local, &u[20..], &v[20..])?;
        vc_line_guard(&contribution, &canonical)?;
        for i in 0..33 { line[i] += contribution[i]; reference_line[i] += canonical[i]; }
        if (owner + 1) % 1024 == 0 { phase(start, "line", owner + 1)?; }
    }
    vc_line_guard(&line, &reference_line)?;
    whole_require([line[0], vc_eval(&line, Fr::one())] == [left, right], "live line endpoints")?;
    sender.append_scalar(b"gkr-left-value", &left); sender.append_scalar(b"gkr-right-value", &right);
    gkr::append_polynomial(&mut sender, b"gkr-line-polynomial", &line);
    reference.append_scalar(b"gkr-left-value", &left); reference.append_scalar(b"gkr-right-value", &right);
    reference.append_bytes(b"gkr-line-polynomial", &33u64.to_le_bytes());
    for coefficient in &reference_line { reference.append_scalar(b"gkr-polynomial-coefficient", coefficient); }
    let challenge = sender.challenge_scalar(b"gkr-line-challenge");
    whole_require(challenge == reference.challenge_scalar(b"gkr-line-challenge"), "live line challenge")?;
    same_sender(&sender, &reference)?;
    let input_claim = gkr::InputClaim { point: gkr::line_point(&u, &v, challenge), value: vc_eval(&line, challenge) };
    let proof = gkr::GkrProof { layers: vec![gkr::LayerProof { rounds, left_value: left,
        right_value: right, line_coefficients: line }] };
    Ok((proof, input_claim, sender))
}

fn open_key_bytes(path: &std::path::Path) -> Result<File, String> {
    use std::os::windows::fs::{MetadataExt, OpenOptionsExt};
    let metadata = std::fs::symlink_metadata(path).map_err(|e| e.to_string())?;
    whole_require(metadata.is_file() && metadata.file_attributes() & 0x400 == 0
        && metadata.len() == 33264, "live verifier-key extent/type")?;
    let file = OpenOptions::new().read(true).share_mode(1).open(path).map_err(|e| e.to_string())?;
    let identity = u0_file_info(&file)?;
    whole_require(identity.size_high == 0 && identity.size_low == 33264, "live verifier-key handle extent")?;
    Ok(file)
}

#[test]
fn live_key_opener_accepts_exact_extent_and_rejects_truncation() {
    use std::io::Write;
    let path = std::env::temp_dir().join(format!("nipopow-live-key-control-{}-{}.bin",
        std::process::id(), std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
    let mut file = OpenOptions::new().write(true).create_new(true).open(&path).unwrap();
    file.write_all(&vec![0u8; 33264]).unwrap(); file.sync_all().unwrap(); drop(file);
    let held = open_key_bytes(&path).unwrap();
    assert_eq!(u0_file_info(&held).unwrap().size_low, 33264); drop(held);
    let file = OpenOptions::new().write(true).open(&path).unwrap();
    file.set_len(33263).unwrap(); file.sync_all().unwrap(); drop(file);
    assert!(open_key_bytes(&path).unwrap_err().contains("extent/type"));
    std::fs::remove_file(path).unwrap();
}

fn execute_live(start: Instant) -> Result<(), String> {
    use crate::{native_role4_join as receiver, packed, pcs};
    use dory_pcs::backends::arkworks::ArkworksVerifierSetup;
    use std::{collections::BTreeMap, io::{Read, Write}, path::PathBuf};
    let output = PathBuf::from(std::env::var_os("NIPOPOW_ROLE4_LIVE_OUTPUT").ok_or("live output directory absent")?);
    whole_require(output.is_absolute(), "absolute live output directory required")?;
    for ancestor in output.ancestors() {
        let metadata = std::fs::symlink_metadata(ancestor).map_err(|e| e.to_string())?;
        whole_require(metadata.is_dir() && !metadata.file_type().is_symlink(), "live output directory type")?;
        #[cfg(windows)] {
            use std::os::windows::fs::MetadataExt;
            whole_require(metadata.file_attributes() & 0x400 == 0, "live output reparse directory")?;
        }
    }
    whole_require(std::fs::read_dir(&output).map_err(|e| e.to_string())?.next().is_none(), "fresh empty live output")?;
    let key_path = PathBuf::from(std::env::var_os("NIPOPOW_ROLE4_KEY_PATH").ok_or("live pinned key path absent")?);
    whole_require(key_path.is_absolute(), "absolute pinned key path required")?;
    let key_file = open_key_bytes(&key_path)?;
    let key_identity = u0_file_info(&key_file)?;
    let mut key = Vec::with_capacity(33264);
    key_file.try_clone().map_err(|e| e.to_string())?.take(33265).read_to_end(&mut key).map_err(|e| e.to_string())?;
    whole_require(key.len() == 33264, "live key exact extent")?;
    let native = input();
    let root = native.root(); let total = native.total_be28();
    whole_require(screen_hex(&root) == U0_ROOT && screen_hex(&total) == U0_TOTAL, "live parent identity")?;
    let parent = WorkTreeHistoryPlan::compile(3073, 12, root, total)?;
    drop(native);
    let height = HeightWork::compile_history(&parent)?;
    let daa = DaaHistoryRoster::compile(&parent)?;
    let adapter = Role4EndpointAdapter::new(&height, &daa, Role4EndpointScope::WholeS12)?;
    let (source, held, identity) = useq_admit()?;
    phase(start, "setup", 0)?;
    let setup = pcs::generate_setup_for_scale_diagnostic(32)?;
    let generated_key = pcs::encode(&ArkworksVerifierSetup(setup.verifier.clone()))?;
    whole_require(generated_key == key, "producer setup must match independently pinned verifier key")?;
    phase(start, "commitment", 0)?;
    let committed = packed::commit(&source, &setup)?;
    let commitment = pcs::encode_commitment(&committed.commitment)?;
    let statement = receiver::expected_statement_bytes(&commitment)?;
    let context = receiver::start_transcript(&statement, &key, &commitment)?;
    let prefix = live_u(&parent, &height, &daa, &adapter, &source, &held, context.producer_transcript(), start)?;
    let (proof, claimed, mut sender) = live_v(&parent, &height, &daa, &adapter, &source, prefix, start)?;
    let gkr_bytes = gkr::encode_proof(&proof)?;
    let verified = context.verify_gkr(&gkr_bytes)?;
    whole_require(verified.claim() == &claimed && source.evaluate(&claimed.point)? == claimed.value,
        "live GKR derived claim must equal source evaluation")?;
    same_sender(&sender, verified.transcript())?;
    phase(start, "dory-opening", 0)?;
    let opening = packed::open(&committed, &source, &claimed.point, &setup, &mut sender)?;
    let dory_bytes = pcs::encode_proof(&opening)?;
    context.verify_dory(verified, &dory_bytes)?;
    whole_require(u0_file_info(&held)? == identity && u0_file_info(&key_file)? == key_identity,
        "live final held witness/key identity")?;
    let mut members = BTreeMap::<String, Vec<u8>>::from([
        ("public-key.bin".into(), key), ("commitment.bin".into(), commitment),
        ("gkr-proof.bin".into(), gkr_bytes), ("dory-proof.bin".into(), dory_bytes),
        ("statement.json".into(), statement),
    ]);
    let files = members.iter().map(|(name, bytes)| Ok(serde_json::json!({
        "name": name, "bytes": bytes.len(), "sha256": vc_sha(bytes)?
    }))).collect::<Result<Vec<_>, String>>()?;
    let manifest = serde_json::to_vec(&serde_json::json!({
        "schema": "native-role4-gkr-pcs32-manifest-v1", "files": files
    })).map_err(|e| e.to_string())?;
    members.insert("manifest.json".into(), manifest);
    let verify_start = Instant::now();
    let package = receiver::validate_package(&members)?;
    let standalone = package.context.verify_gkr(&package.gkr_proof)?;
    whole_require(standalone.claim() == &claimed, "fresh package receiver GKR claim")?;
    package.context.verify_dory(standalone, &package.dory_proof)?;
    let verify_ns = screen_ns(verify_start);
    for (name, bytes) in &members {
        let mut file = OpenOptions::new().write(true).create_new(true).open(output.join(name)).map_err(|e| e.to_string())?;
        file.write_all(bytes).map_err(|e| e.to_string())?;
        file.sync_all().map_err(|e| e.to_string())?;
        whole_require(file.metadata().map_err(|e| e.to_string())?.len() == bytes.len() as u64, "live output write extent")?;
    }
    phase(start, "complete", 1)?;
    println!("native_role4_live_result {}", serde_json::json!({
        "schema": "native-role4-gkr-pcs32-result-v1", "status": "PASS",
        "proof_files": members.len(), "proof_package_bytes": members.values().map(Vec::len).sum::<usize>(),
        "manifest_sha256": package.manifest_sha256, "standalone_verify_ns": verify_ns,
        "elapsed_ns": screen_ns(start), "full_history": false, "all_seven_roles": false,
        "production_adopted": false
    }));
    std::io::stdout().flush().map_err(|e| e.to_string())?;
    Ok(())
}

#[test]
#[ignore = "manual bounded commitment-first native U/V/PCS32 join; reviewed controller required"]
fn native_role4_live_gkr_pcs_bounded() {
    execute_live(Instant::now()).expect("complete live role4 GKR/PCS diagnostic");
}

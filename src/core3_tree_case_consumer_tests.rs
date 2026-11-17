use super::*;
use std::io::Write;

fn emit(stage: &str, detail: &str) { println!("C560_COLD_STAGE|{stage}|{detail}"); }
fn context(files: &[Vec<u8>; 12]) -> Context { parse(&files[10], CONTEXT_BOUND).unwrap() }
fn manifest(files: &mut [Vec<u8>; 12]) {
    let records: [FileMeta; 11] = std::array::from_fn(|i| FileMeta {
        file: NAMES[i].into(), bytes: files[i].len() as u64, blake2b256: hash(&files[i]),
    });
    files[11] = serde_json::to_vec(&records).unwrap();
}
fn set_context(files: &mut [Vec<u8>; 12], context: &Context) {
    files[10] = serde_json::to_vec(context).unwrap();
    manifest(files);
}
fn repair_body(files: &mut [Vec<u8>; 12], index: usize) {
    let mut c = context(files);
    let meta = if index % 2 == 0 { &mut c.bodies[index/2].gkr } else { &mut c.bodies[index/2].pcs };
    meta.bytes = files[index].len() as u64;
    meta.blake2b256 = hash(&files[index]);
    set_context(files, &c);
}
fn write_case(root: &Path, name: &str, files: &[Vec<u8>; 12], omit: Option<usize>) -> PathBuf {
    let path = root.join(name);
    fs::create_dir(&path).expect("create fresh isolated negative case");
    for (i, (name, bytes)) in NAMES.iter().zip(files).enumerate() {
        if omit == Some(i) { continue; }
        let file_path = path.join(name);
        let mut file = fs::OpenOptions::new().write(true).create_new(true).open(&file_path).unwrap();
        file.write_all(bytes).unwrap();
        file.flush().unwrap();
        file.sync_all().unwrap();
        let mut permissions = file.metadata().unwrap().permissions();
        permissions.set_readonly(true);
        file.set_permissions(permissions).unwrap();
    }
    path
}
fn rejection(path: &Path, phase: &str, text: &str, real_crypto: bool) {
    let e = verify_internal_four_claim_case(path).unwrap_err();
    assert_eq!(e.phase, phase, "{e}");
    assert!(e.cause.contains(text), "{e}");
    if real_crypto {
        for incidental in ["header", "extent", "encoding", "canonical", "metadata", "hash differs"] {
            assert!(!e.cause.contains(incidental), "incidental rejection: {e}");
        }
    }
}
fn object_negatives<T: serde::de::DeserializeOwned + Serialize>(value: &T, first: &str, replacement: &str) {
    let bytes = serde_json::to_vec(value).unwrap();
    let object = std::str::from_utf8(&bytes).unwrap();
    for prefix in [format!("{{\"unexpected\":0,{}", &object[1..]),
        format!("{{\"{first}\":{replacement},{}", &object[1..])]
    {
        let e = parse::<T>(prefix.as_bytes(), CONTEXT_BOUND).err().expect("unknown/duplicate field");
        assert_eq!(e.phase, "json");
    }
    // Each exercised object's first field is a scalar, so this removes exactly
    // that required member while retaining all remaining valid fields.
    let first_end=object.find(',').unwrap();
    let missing=format!("{{{}",&object[first_end+1..]);
    let e=parse::<T>(missing.as_bytes(),CONTEXT_BOUND).err().expect("required object member");
    assert_eq!(e.phase,"json");
    assert!(e.cause.contains("missing field"),"{e}");
}
fn parser_negatives(files: &[Vec<u8>; 12]) {
    let c = context(files);
    object_negatives(&c, "schema", "\"different\"");
    object_negatives(&c.bodies[0], "role", "\"different\"");
    object_negatives(&c.bodies[0].gkr, "file", "\"different\"");
    object_negatives(&c.measurements_ms, "witness", "1");
    let records: [FileMeta; 11] = parse(&files[11], MANIFEST_BOUND).unwrap();
    object_negatives(&records[0], "file", "\"different\"");

    macro_rules! sequence {
        ($($field:expr),* $(,)?) => {{
            let fields = [$(serde_json::to_string(&$field).unwrap()),*];
            format!("[{}]", fields.join(","))
        }};
    }
    let g = &c.bodies[0].gkr;
    let b = &c.bodies[0];
    let m = &c.measurements_ms;
    let file_sequence = sequence!(g.file,g.bytes,g.blake2b256);
    let body_sequence = sequence!(b.role,b.tag,b.gkr_input_log,b.row_log,b.pcs_input_log,b.gkr,b.pcs);
    let measurements_sequence = sequence!(m.witness,m.setup_and_key,m.commit,m.verifier_plan_admission,m.proof_production,m.verification_only);
    let context_sequence = sequence!(c.schema,c.version,c.profile,c.coverage,c.root,c.total_be28,c.headers,c.slot_log,c.pair_starts,
        c.key_log_n,c.key_id,c.key_file,c.key_blake2b256,c.pcs_mode,c.vendor,c.commitment_file,c.commitment_hex,
        c.commitment_blake2b256,c.tree_source_blake2b256,c.tree_input_log,c.tree_row_log,c.tree_terms,c.tree_families,
        c.tree_domain,c.bodies,c.measurements_ms);
    assert!(parse::<Context>(context_sequence.as_bytes(),CONTEXT_BOUND).is_err());
    assert!(parse::<BodyMeta>(body_sequence.as_bytes(),CONTEXT_BOUND).is_err());
    assert!(parse::<FileMeta>(file_sequence.as_bytes(),CONTEXT_BOUND).is_err());
    assert!(parse::<Measurements>(measurements_sequence.as_bytes(),CONTEXT_BOUND).is_err());
    let object_context = serde_json::to_string(&c).unwrap();
    for (object, sequence) in [(serde_json::to_string(g).unwrap(),file_sequence),
        (serde_json::to_string(b).unwrap(),body_sequence),
        (serde_json::to_string(m).unwrap(),measurements_sequence)]
    {
        let nested = object_context.replace(&object,&sequence);
        assert_ne!(nested,object_context);
        assert!(parse::<Context>(nested.as_bytes(),CONTEXT_BOUND).is_err());
    }
    let record_sequence=sequence!(records[0].file,records[0].bytes,records[0].blake2b256);
    let bad_manifest=serde_json::to_string(&records).unwrap().replacen(&serde_json::to_string(&records[0]).unwrap(),&record_sequence,1);
    assert!(parse::<[FileMeta;11]>(bad_manifest.as_bytes(),MANIFEST_BOUND).is_err());

    let compact = serde_json::to_string(&c).unwrap();
    for token in ["-1", "-0", "4.0", "4e0", "4E+0", "9007199254740992", "18446744073709551616",
        "true", "\"4\"", "null", "[]", "{}", "04"]
    {
        let bad = compact.replace("\"headers\":4", &format!("\"headers\":{token}"));
        assert_ne!(bad, compact);
        assert!(parse::<Context>(bad.as_bytes(), CONTEXT_BOUND).is_err(), "numeric alias {token}");
    }
    // Malformed array shape and nested object types cannot become a partial role set.
    for (from, to) in [("\"coverage\":[0,1,2,3]", "\"coverage\":[0,1,2]"),
        ("\"coverage\":[0,1,2,3]", "\"coverage\":[0,1,2,3,4]"),
        ("\"pair_starts\":[0,2]", "\"pair_starts\":null")]
    {
        let bad = compact.replace(from, to);
        assert_ne!(bad, compact);
        assert!(parse::<Context>(bad.as_bytes(), CONTEXT_BOUND).is_err());
    }
    let measure = serde_json::to_string(&c.measurements_ms).unwrap();
    let needle = format!("\"witness\":{}", c.measurements_ms.witness);
    let bad = measure.replace(&needle, "\"witness\":null");
    assert_ne!(bad, measure);
    assert!(parse::<Measurements>(bad.as_bytes(), CONTEXT_BOUND).is_err());
    let mut bom = vec![0xef,0xbb,0xbf]; bom.extend_from_slice(&files[10]);
    let mut utf8 = files[10].clone(); utf8.push(0xff);
    let mut trailing = files[10].clone(); trailing.extend_from_slice(b" {}");
    let nesting = format!("{{\"schema\":{}0{} }}", "[".repeat(140), "]".repeat(140)).into_bytes();
    for bytes in [&bom, &utf8, &trailing, &nesting] {
        assert!(parse::<Context>(bytes, CONTEXT_BOUND).is_err());
    }
    let mut unknown_nested = c.clone();
    unknown_nested.measurements_ms.witness = MAX_INTEGER;
    assert!(parse::<Context>(&serde_json::to_vec(&unknown_nested).unwrap(), CONTEXT_BOUND).is_ok());
    let too_large = vec![b' '; CONTEXT_BOUND+1];
    assert_eq!(parse::<Context>(&too_large, CONTEXT_BOUND).err().unwrap().phase, "bounds");
    assert!(parse::<[FileMeta; 11]>(&serde_json::to_vec(&records[..10]).unwrap(), MANIFEST_BOUND).is_err());
    let mut twelve = records.to_vec(); twelve.push(records[0].clone());
    assert!(parse::<[FileMeta; 11]>(&serde_json::to_vec(&twelve).unwrap(), MANIFEST_BOUND).is_err());
    let mut total = CASE_BOUND;
    assert!(debit(&mut total, 1).is_err());
    assert_eq!(total, CASE_BOUND);
    total = usize::MAX;
    assert!(debit(&mut total, 1).is_err());
    total = 0;
    debit(&mut total, CASE_BOUND).unwrap();
    for i in 0..12 {
        let max = if i < 10 { EXACT[i] } else if i == 10 { CONTEXT_BOUND } else { MANIFEST_BOUND };
        assert!(check_length(i, max as u64).is_ok());
        assert!(check_length(i, max as u64+1).is_err());
        assert!(check_length(i, 0).is_err());
    }
}

#[test]
#[ignore = "bounded C560 cold internal-case replay; requires separately admitted Windows run"]
fn cold_four_claim_case_replays_without_producer() {
    let path = PathBuf::from(std::env::var_os("NIPOPOW_C560_CASE_DIR")
        .expect("NIPOPOW_C560_CASE_DIR must name the qualified readonly case"));
    assert!(std::env::var_os("NIPOPOW_OWNER_ASSEMBLY_FIXTURE_DIR").is_none(), "no RAW/producer fixture input");
    let parent = path.parent().unwrap();
    let scratch = parent.join("c560-negative-fixtures");
    assert!(!scratch.exists(), "no reuse of consumed negative-fixture directory");
    emit("start", "input=qualified_internal_case roles=4 producer_access=false");
    // Fail cheap filesystem prerequisites before the nine full crypto calls.
    // These public junction cases are real; the observed-attribute bit test is
    // explicitly synthetic and needs no Cloud fixture, compatibility mode or FFI.
    let root_link=parent.join("c560-case-link");
    let ancestor_case=parent.join("c560-ancestor-link").join(path.file_name().unwrap());
    for fixture in [&root_link,&ancestor_case] {
        assert!(fs::symlink_metadata(fixture).is_ok(), "controlled link fixture missing");
        rejection(fixture,"filesystem","link",false);
    }
    #[cfg(windows)] {
        use std::os::windows::fs::MetadataExt;
        let regular=fs::symlink_metadata(path.join(NAMES[0])).unwrap();
        assert!(regular.is_file());
        require_regular_nonreparse(&regular).expect("real regular D snapshot metadata control");
        let is_symlink=regular.file_type().is_symlink();
        let attributes=regular.file_attributes();
        assert!(!is_symlink);
        assert_eq!(attributes&0x400,0);
        assert!(observed_nonreparse(is_symlink,attributes));
        let synthetic_attributes=attributes|0x400;
        assert_eq!(synthetic_attributes^attributes,0x400);
        assert!(!observed_nonreparse(is_symlink,synthetic_attributes));
        let omitted_attribute_control=!is_symlink;
        assert!(omitted_attribute_control,"omitting only 0x400 accepts the synthetic observed metadata");
        assert!(!observed_nonreparse(true,attributes),"isolated observed symlink flag");
        assert!(check_ancestors(Path::new("\\\\untrusted-server\\share\\case")).unwrap_err().cause.contains("local Windows drive"));
    }
    #[cfg(not(windows))]
    panic!("controlled Windows metadata/junction prerequisites are mandatory, not skipped");
    emit("links", "root_ancestor_junctions=reject real_regular_D_metadata=accept synthetic_observed_0x400=reject omitted_0x400_control=accept symlink_flag=reject public_file_symlink_case=not_executed skipped=0");
    let verified = verify_internal_four_claim_case(&path).expect("cold public runtime facade verifies four real proofs");
    emit("positive", &format!("bytes={} io_hash_parse_ms={} key_admission_ms={} plan_construction_ms={} four_proof_replay_ms={} accepted=true",
        verified.case_bytes, verified.io_hash_parse_ms, verified.key_admission_ms,
        verified.plan_construction_ms, verified.four_proof_replay_ms));
    let loaded = load_case(&path).unwrap();
    let base = loaded.files.clone();
    drop(loaded);
    fs::create_dir(&scratch).unwrap();

    // First semantic falsifier: valid Dory bytes, same dimensions/key/C and all
    // GKR unchanged. Repair every enclosing integrity hash before real replay.
    assert_ne!(base[7], base[1], "positive Tree and Work PCS bodies differ");
    let mut bad = base.clone(); bad[7] = base[1].clone(); repair_body(&mut bad, 7);
    let fixture = write_case(&scratch, "tree-pcs-from-work", &bad, None);
    rejection(&fixture, "replay", "core3 tree PCS rejected", true);
    emit("tree_pcs_falsifier", "hashes_repaired=true exact_extent=true GKR_unchanged=true rejection=real_Tree_PCS");

    for (target, source) in [(0usize,6usize), (6,0)] {
        let mut bad = base.clone(); bad[target] = base[source].clone(); repair_body(&mut bad, target);
        let fixture = write_case(&scratch, &format!("gkr-transplant-{target}"), &bad, None);
        rejection(&fixture, "replay", "GKR rejected", true);
    }
    for target in [1usize,3,5] {
        let mut bad = base.clone();
        assert_ne!(bad[target], base[7]);
        bad[target] = base[7].clone(); repair_body(&mut bad, target);
        let fixture = write_case(&scratch, &format!("pcs-transplant-{target}"), &bad, None);
        rejection(&fixture, "replay", "joined history PCS rejected", true);
    }
    emit("other_crypto", "GKR_transplants=2 other_role_PCS=3 same_header_and_repaired_hashes=true rejected=true");

    for field in ["root", "total"] {
        let mut bad = base.clone(); let mut c = context(&bad);
        if field == "root" { let mut bytes = hex::<32>(&c.root, false, "root").unwrap(); bytes[0]^=1; c.root=upper_hex(&bytes); }
        else { let mut bytes = hex::<28>(&c.total_be28, false, "total").unwrap(); bytes[27]^=1; c.total_be28=upper_hex(&bytes); }
        set_context(&mut bad, &c);
        let fixture = write_case(&scratch, &format!("coherent-{field}"), &bad, None);
        rejection(&fixture, "replay", "joined history GKR rejected", true);
    }
    emit("context_crypto", "coherent_root_and_total_faults=2 old_bodies_preserved=true real_GKR_reject=true");

    // These fields share exact equality preflight, but each is mutated alone.
    for fault in 0..23 {
        let mut bad = base.clone(); let mut c = context(&bad);
        match fault {
            0 => c.schema.push('x'), 1 => c.version=2, 2 => c.profile.push('x'),
            3 => c.coverage.swap(2,3), 4 => c.headers=3, 5 => c.slot_log=3,
            6 => c.pair_starts.swap(0,1), 7 => c.key_log_n=21, 8 => c.tree_input_log=21,
            9 => c.tree_row_log=20, 10 => c.tree_terms-=1, 11 => c.tree_families-=1,
            12 => c.tree_domain.push('x'), 13 => c.pcs_mode.push('x'), 14 => c.vendor.push('0'),
            15 => c.tree_source_blake2b256=c.tree_source_blake2b256.to_ascii_uppercase(),
            16 => c.key_id="00".repeat(32), 17 => c.commitment_hex="00".repeat(384),
            18 => c.commitment_file="../commitment.bin".into(), 19 => c.key_file="C:log22.vk".into(),
            20 => c.commitment_blake2b256="00".repeat(32), 21 => c.key_blake2b256="00".repeat(32),
            22 => {
                let original=c.tree_source_blake2b256.clone();
                let mut fingerprint=hex::<32>(&original,true,"Tree source identity").unwrap();
                fingerprint[0]^=1; // one nibble, retaining the canonical lowercase64 form
                c.tree_source_blake2b256=fingerprint.iter().map(|b|format!("{b:02x}")).collect();
                assert_ne!(c.tree_source_blake2b256,original);
                assert_eq!(hex::<32>(&c.tree_source_blake2b256,true,"Tree source identity").unwrap(),fingerprint);
            }
            _ => unreachable!(),
        }
        set_context(&mut bad, &c);
        let fixture = write_case(&scratch, &format!("metadata-{fault}"), &bad, None);
        let e = load_case(&fixture).err();
        if fault == 16 {
            assert!(e.is_none(), "key-ID mismatch belongs to actual key admission");
            rejection(&fixture, "key_admission", "key ID differs", false);
        } else {
            let e = e.expect("isolated metadata fault rejected before plan");
            assert!(e.phase=="context" || e.phase=="integrity", "{e}");
            if fault==15 { assert!(e.cause.contains("Tree source identity")); }
            if fault==22 {
                assert_eq!(e.phase,"context");
                assert_eq!(e.cause,"Tree source identity differs");
            }
        }
    }
    for index in 0..4 {
        for fault in 0..11 {
            let mut bad = base.clone(); let mut c = context(&bad); let body = &mut c.bodies[index];
            match fault {
                0 => body.role.push('x'), 1 => body.tag=99,
                2 => body.gkr_input_log-=1, 3 => body.row_log-=1, 4 => body.pcs_input_log-=1,
                5 => body.gkr.file="../work.gkr.bin".into(), 6 => body.pcs.file="tree.pcs.bin:alias".into(),
                7 => body.gkr.bytes-=1, 8 => body.pcs.bytes-=1,
                9 => body.gkr.blake2b256="00".repeat(32), 10 => body.pcs.blake2b256="00".repeat(32),
                _ => unreachable!(),
            }
            set_context(&mut bad, &c);
            let fixture=write_case(&scratch,&format!("role-{index}-field-{fault}"),&bad,None);
            let e=load_case(&fixture).err().expect("each role field must reject before plan");
            assert!(e.phase=="context" || e.phase=="integrity", "{e}");
        }
    }
    emit("metadata", "context_faults=23 role_field_faults=44 Tree_source_uppercase_rejected=true Tree_source_lowercase_mismatch_rejected=true no_plan_for_preflight_faults=true");
    parser_negatives(&base);
    emit("json_bounds", "closed_objects_duplicate_unknown_types_lexical_integers_UTF8_BOM_nesting_trailing_fixed_arrays_and_aggregate=reject");

    for index in 0..10 {
        for trailing in [false,true] {
            let mut bad=base.clone();
            if trailing { bad[index].push(0); } else { bad[index].pop(); }
            manifest(&mut bad);
            let fixture=write_case(&scratch,&format!("extent-{index}-{trailing}"),&bad,None);
            rejection(&fixture,"bounds","file extent",false);
        }
    }
    let missing=write_case(&scratch,"missing",&base,Some(6));
    rejection(&missing,"filesystem","missing",false);
    let extra=write_case(&scratch,"extra",&base,None);
    fs::OpenOptions::new().write(true).create_new(true).open(extra.join("extra.bin")).unwrap();
    rejection(&extra,"filesystem","case",false);
    let mut duplicate=base.clone();
    let mut records:[FileMeta;11]=parse(&duplicate[11],MANIFEST_BOUND).unwrap();
    records[1]=records[0].clone(); duplicate[11]=serde_json::to_vec(&records).unwrap();
    let duplicate=write_case(&scratch,"duplicate-manifest",&duplicate,None);
    rejection(&duplicate,"integrity","metadata/hash differs",false);
    let mut hash_only=base.clone(); hash_only[6][0]^=1;
    let fixture=write_case(&scratch,"unrepaired-payload",&hash_only,None);
    rejection(&fixture,"integrity","metadata/hash differs",false);
    for (index, alias) in ["Work.gkr.bin","../work.gkr.bin","C:work.gkr.bin","work\\gkr.bin"].into_iter().enumerate() {
        let mut bad=base.clone(); let mut records:[FileMeta;11]=parse(&bad[11],MANIFEST_BOUND).unwrap();
        records[0].file=alias.into(); bad[11]=serde_json::to_vec(&records).unwrap();
        let fixture=write_case(&scratch,&format!("name-alias-{index}"),&bad,None);
        rejection(&fixture,"integrity","metadata/hash differs",false);
    }
    // Isolate the physical case-sensitive roster without changing any bytes,
    // metadata record or cardinality. Write the alias directly on Windows.
    let physical_alias=write_case(&scratch,"physical-case-alias",&base,Some(0));
    let mut alias_file=fs::OpenOptions::new().write(true).create_new(true)
        .open(physical_alias.join("Work.gkr.bin")).unwrap();
    alias_file.write_all(&base[0]).unwrap();
    alias_file.flush().unwrap();
    alias_file.sync_all().unwrap();
    let mut permissions=alias_file.metadata().unwrap().permissions();
    permissions.set_readonly(true);
    alias_file.set_permissions(permissions).unwrap();
    drop(alias_file);
    let physical_names:Vec<_>=fs::read_dir(&physical_alias).unwrap()
        .map(|entry|entry.unwrap().file_name().into_string().unwrap()).collect();
    assert_eq!(physical_names.len(),12);
    assert_eq!(physical_names.iter().filter(|name|name.as_str()=="Work.gkr.bin").count(),1);
    assert!(!physical_names.iter().any(|name|name=="work.gkr.bin"));
    for (index,name) in NAMES.iter().enumerate().skip(1) {
        assert_eq!(physical_names.iter().filter(|actual|actual.as_str()==*name).count(),1);
        assert!(fs::read(physical_alias.join(name)).unwrap()==base[index],"canonical sibling bytes changed");
    }
    assert!(fs::read(physical_alias.join("Work.gkr.bin")).unwrap()==base[0],"physical alias bytes changed");
    // This establishes the Windows resolution premise of the case-insensitive
    // roster mutant: its subsequent canonical open would see the valid bytes.
    assert!(fs::read(physical_alias.join("work.gkr.bin")).unwrap()==base[0],"Windows canonical lookup must resolve the alias bytes");
    rejection(&physical_alias,"filesystem","unexpected literal case name",false);
    for index in [10usize,11] {
        let mut bad=base.clone();
        bad[index]=vec![b' '; if index==10 {CONTEXT_BOUND+1} else {MANIFEST_BOUND+1}];
        let fixture=write_case(&scratch,&format!("oversized-json-{index}"),&bad,None);
        rejection(&fixture,"bounds","file extent",false);
    }
    emit("filesystem", "ten_binary_extents_truncated_trailing_missing_extra_duplicate_manifest_alias_and_integrity=reject physical_single_case_alias=reject");

    emit("PASS", "cold_runtime_public4=true rehashed_Tree_PCS_negative=true no_X_RAW_prover_setup_generation=true full_history=false production=false");
}

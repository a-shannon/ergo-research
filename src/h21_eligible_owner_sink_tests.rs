use super::*;
use crate::sparse::Term;

/// Real three-header packed source -> opaque publication -> synthetic sink
/// consumer geometry. Only the private owner parameter and synthetic read
/// coordinates are scaled down; production pins the source to owner845758.
fn upper_fixture()->(Eligible08OwnerSink,crate::packed_owner_assembly::WorkUpperPublication) {
    let (mut sink,_)=cap_fixture();
    let local=structural_work_source();let parent=local.parent.clone();let binding=sink.binding.clone();
    sink.admit_work_local(&binding,&parent,local).unwrap();
    let (token,parent)=crate::packed_owner_assembly::small_work_upper_fixture(None).unwrap();
    sink.binding.root=parent.root;sink.binding.total=parent.total;sink.binding.profile=parent.profile;
    sink.binding.cut=parent.cut;
    let upper=token.checked_upper(sink.binding.root,sink.binding.total,sink.binding.profile,&sink.binding.cut,0).unwrap();
    for read in &mut sink.state.reads {
        if matches!(read.author,RequiredAuthor::WorkUpper{..}) {
            let bit=read.wire-((OWNER-1)*WIDTH+987450);
            read.wire=upper[bit].0;read.value=upper[bit].1.is_one();
            read.author=RequiredAuthor::WorkUpper{owner:0,height:2};
        }
    }
    (sink,token)
}
fn reject_upper(sink:&mut Eligible08OwnerSink,token:crate::packed_owner_assembly::WorkUpperPublication,
    owner:usize,expected:&str) {
    let binding=sink.binding.clone();
    reject_upper_binding(sink,&binding,token,owner,expected);
}
fn reject_upper_binding(sink:&mut Eligible08OwnerSink,binding:&Binding,
    token:crate::packed_owner_assembly::WorkUpperPublication,owner:usize,expected:&str) {
    let before=sink.state.clone();let row_source=sink.source.clone();let local=sink.work_source.clone();
    let cap=sink.cap_source.as_ref().map(|s|s as *const _);let upper=sink.upper_source.clone();
    let sink_binding=sink.binding.clone();let before_token=token.clone();
    assert_eq!(sink.admit_work_upper(binding,owner,token.clone()).err().unwrap(),expected);
    assert!(sink.binding==sink_binding);assert!(token==before_token);
    assert!(sink.state==before);assert!(sink.source==row_source);assert!(sink.work_source==local);
    assert!(sink.upper_source==upper);assert_eq!(sink.cap_source.as_ref().map(|s|s as *const _),cap);
}

#[test]
fn c203_packed_upper_token_resolves_exactly_448_edges_atomically_and_preserves_row_lease() {
    let (mut sink,token)=upper_fixture();let before=sink.state.clone();let row_source=sink.source.clone();
    let local=sink.work_source.clone();let expected=token.clone();let binding=sink.binding.clone();
    let admitted=sink.admit_work_upper(&binding,0,token).unwrap();
    assert_eq!((admitted.cell_count(),admitted.pending_read_count()),(16832,580));
    assert_eq!(admitted.term_count(),before.terms.len());
    assert_eq!(sink.retained_work_upper_counts(),(3265,1184));
    assert!(sink.upper_source.as_ref()==Some(&expected));
    assert!(sink.source==row_source);assert!(sink.work_source==local);
    assert!(sink.state.rows==before.rows);assert_eq!(sink.state.terms,before.terms);
    for (wire,cell) in before.cells {assert_eq!(sink.state.cells.get(&wire),Some(&cell));}
    assert_eq!(sink.state.reads,before.reads.into_iter().filter(|r|
        !matches!(r.author,RequiredAuthor::WorkUpper{..})).collect::<Vec<_>>());
    assert_eq!(sink.pending_sources().iter().filter(|r|matches!(r.author,RequiredAuthor::Cap{..})).count(),130);
    assert_eq!(sink.pending_sources().iter().filter(|r|matches!(r.author,RequiredAuthor::PreviousR{..})).count(),450);
    reject_upper(&mut sink,expected,0,"Eligible08 sink Upper order/duplicate");
}

#[test]
fn c203_upper_typed_reads_bits_owners_heights_domains_and_census_fail_atomically() {
    let (mut sink,token)=upper_fixture();
    for context in 0..2 {
        for kind in 0..12 {
            let reads=sink.state.reads.clone();
            let i=sink.state.reads.iter().position(|r|matches!(r.author,RequiredAuthor::WorkUpper{..})
                && matches!(r.consumer,Writer::Score(a) if a.context==context)).unwrap();
            let expected=match kind {
                0=>{sink.state.reads[i].value^=true;"Eligible08 sink Upper source bit/duplicate read"},
                1=>{sink.state.reads[i].author=RequiredAuthor::WorkUpper{owner:1,height:2};"Eligible08 sink Upper exact typed source"},
                2=>{sink.state.reads[i].author=RequiredAuthor::WorkUpper{owner:0,height:3};"Eligible08 sink Upper exact typed source"},
                3=>{sink.state.reads[i].wire-=1;"Eligible08 sink Upper exact read domain"},
                4=>{sink.state.reads.remove(i);"Eligible08 sink Upper exact 448-read census"},
                5=>{sink.state.reads.push(sink.state.reads[i].clone());"Eligible08 sink Upper source bit/duplicate read"},
                6=>{sink.state.reads[i].consumer=Writer::Map(context);"Eligible08 sink Upper exact Score consumer"},
                7=>{if let Writer::Score(ref mut a)=sink.state.reads[i].consumer {a.context=2;}
                    "Eligible08 sink Upper exact Score consumer"},
                8=>{if let Writer::Score(ref mut a)=sink.state.reads[i].consumer {a.origin+=1;}
                    "Eligible08 sink Upper exact Score consumer"},
                9=>{if let Writer::Score(ref mut a)=sink.state.reads[i].consumer {a.previous_owner+=1;}
                    "Eligible08 sink Upper exact Score consumer"},
                10=>{if let Writer::Score(ref mut a)=sink.state.reads[i].consumer {a.max_owner+=1;}
                    "Eligible08 sink Upper exact Score consumer"},
                11=>{if let Writer::Score(ref mut a)=sink.state.reads[i].consumer {a.cap_owner+=1;}
                    "Eligible08 sink Upper exact Score consumer"},
                _=>unreachable!(),
            };
            reject_upper(&mut sink,token.clone(),0,expected);sink.state.reads=reads;
        }
    }
    reject_upper(&mut sink,token.clone(),1,"Work Upper exact parent/cut/owner/height");
    let wire=987450;sink.state.cells.insert(wire,(Writer::Header,false));
    reject_upper(&mut sink,token.clone(),0,"Eligible08 sink Upper duplicate X");sink.state.cells.remove(&wire);
    let binding=sink.binding.clone();assert!(sink.admit_work_upper(&binding,0,token).is_ok());
}

#[test]
fn c203_upper_token_parent_fields_and_destination_binding_order_reject_without_mutation() {
    let (mut sink,token)=upper_fixture();let original=sink.binding.clone();
    // A caller binding mismatch stops at the destination guard, independently
    // for every field (including the two existing Map bindings).
    for kind in 0..6 {
        let mut binding=original.clone();
        match kind {
            0=>binding.root[0]^=1,1=>binding.total[0]^=1,2=>binding.profile[0]^=1,
            3=>binding.cut.push(0),4=>binding.maps[0].e+=1,5=>binding.maps[1].e+=1,
            _=>unreachable!(),
        }
        reject_upper_binding(&mut sink,&binding,token.clone(),0,"Eligible08 sink Upper full context binding");
    }
    // Pass the destination guard with equal caller/sink metadata, changing
    // only one expected parent field. The real packed-source token stays
    // unchanged, so each fault must reach checked_upper's parent predicate.
    for kind in 0..4 {
        match kind {
            0=>sink.binding.root[0]^=1,1=>sink.binding.total[0]^=1,
            2=>sink.binding.profile[0]^=1,3=>sink.binding.cut.push(0),
            _=>unreachable!(),
        }
        reject_upper(&mut sink,token.clone(),0,"Work Upper exact parent/cut/owner/height");
        sink.binding=original.clone();
    }
    // Isolate each order prerequisite while all sibling preconditions hold.
    assert!(sink.state.published&&sink.source.is_some()&&sink.work_source.is_some()&&sink.upper_source.is_none());
    sink.state.published=false;
    reject_upper(&mut sink,token.clone(),0,"Eligible08 sink Upper order/duplicate");
    sink.state.published=true;
    let row_source=sink.source.take().unwrap();
    reject_upper(&mut sink,token.clone(),0,"Eligible08 sink Upper order/duplicate");
    sink.source=Some(row_source);
    let local_source=sink.work_source.take().unwrap();
    reject_upper(&mut sink,token.clone(),0,"Eligible08 sink Upper order/duplicate");
    sink.work_source=Some(local_source);
    assert_eq!(sink.admit_work_upper(&original,0,token).unwrap().pending_read_count(),580);
}

#[test]
fn c203_upper_packed_source_mutants_reject_before_token_and_leave_sink_unchanged() {
    let (mut sink,good)=upper_fixture();
    for (kind,needle) in [(0,"exact packed/native active operand"),(1,"parent/cut/owner/height"),
        (2,"parent/cut/owner/height"),(3,"canonical tagged term occurrences")] {
        let before=sink.state.clone();let source=sink.source.clone();let local=sink.work_source.clone();
        let error=crate::packed_owner_assembly::small_work_upper_fixture(Some(kind)).err().unwrap();
        assert!(error.contains(needle),"{error}");assert!(sink.state==before);assert!(sink.source==source);
        assert!(sink.work_source==local);assert!(sink.upper_source.is_none());
    }
    let binding=sink.binding.clone();assert!(sink.admit_work_upper(&binding,0,good).is_ok());
}

fn fixture() -> (Eligible08OwnerSink, Eligible08OwnerLease) {
    let source = H21EligibleSlackStage::synthetic_owner_sink_source();
    let map = &source.map_stage;
    let binding = Binding {root: map.parent_root, total: map.parent_total,
        profile: map.parent_profile, cut: map.cut_identity.clone(), maps: map.map_bindings.clone()};
    let map_reads = Vec::new();
    let (cells, rows, reads) = material(&binding, &source, &map_reads).unwrap();
    let sink = Eligible08OwnerSink {binding: binding.clone(), state: State::default(),
        custody: std::sync::Arc::new(()), source: None,
        cap_source: None, cap_max_resolution: None, work_source: None, upper_source: None,
        previous_r_source: None};
    (sink, Eligible08OwnerLease {binding, source, map_reads, cells, rows, reads})
}

#[test]
fn c455_local_row_source_view_keeps_exact_sink_custody_without_foreign_claims() {
    let sink = Eligible08OwnerSink::synthetic_map_source_for_test();
    let detached = Eligible08OwnerSink::synthetic_map_source_for_test();
    let view = sink.local_source_view_for_test().unwrap();
    let own = view.map_view().typed_source_for_test().unwrap();
    let detached_view = detached.local_source_view_for_test().unwrap();
    let detached_lease = detached_view.map_view().typed_source_for_test().unwrap();

    assert_eq!(own.binding(), detached_lease.binding());
    assert_eq!(own.entries(), detached_lease.entries());
    view.require_typed_source(&own).unwrap();
    assert!(view.require_typed_source(&detached_lease).unwrap_err().contains("custody"));
    assert_eq!(view.score_cells().len(), 4_096);
    assert_eq!(view.slack_cells().len(), 774);
    assert!(view.score_terms(0).is_ok());
    assert_eq!(view.slack_terms(0).unwrap(),
        crate::bank53_slack::slack_zero_terms(OWNER, 0).unwrap().as_slice());
    assert!(view.score_imports().err().unwrap()
        .contains("publication qualification"));
}

/// The fixture supplies synthetic import records and already-projected source
/// slices to the production qualifier. It tests only source-to-record mechanics.
fn c455_import_qualification_fixture() -> (
    Vec<(usize, ScoreRelationReadAuthor, Fr)>,
    Vec<PendingRead>,
    Vec<(usize, usize, bool)>,
    [Vec<(usize, bool)>; 2],
    Vec<(usize, Fr)>,
    BTreeMap<usize, (Writer, bool)>,
) {
    let (mut sink, lease) = fixture();
    sink.admit(lease).unwrap();
    let imports = sink.source.as_ref().unwrap().score_imports().to_vec();
    let obligations = sink.state.read_obligations.clone();
    let mut previous_r = Vec::with_capacity(450);
    let mut cap_q = [Vec::with_capacity(65), Vec::with_capacity(65)];
    let mut upper = Vec::with_capacity(224);
    let mut sink_cells = BTreeMap::new();
    for (index, &(wire, author, value)) in imports.iter().enumerate() {
        let context = index / 514;
        let bit = value.is_one();
        match author {
            ScoreRelationReadAuthor::PreviousR { context: found, .. } => {
                assert_eq!(found, context);
                previous_r.push((wire, context, bit));
                assert!(sink_cells.insert(wire, (Writer::PreviousR(context), bit)).is_none());
            }
            ScoreRelationReadAuthor::Cap { context: found, .. } => {
                assert_eq!(found, context);
                cap_q[context].push((wire, bit));
                assert!(sink_cells.insert(wire, (Writer::Cap(context), bit)).is_none());
            }
            ScoreRelationReadAuthor::WorkUpper { .. } => {
                if context == 0 { upper.push((wire, value)); }
                assert!(sink_cells.insert(wire, (Writer::WorkUpper, bit))
                    .is_none_or(|prior| prior == (Writer::WorkUpper, bit)));
            }
        }
    }
    (imports, obligations, previous_r, cap_q, upper, sink_cells)
}

#[test]
fn c455_source_qualification_rejects_relabels_output_faults_and_import_census_mutants() {
    let (imports, obligations, previous_r, cap_q, upper, sink_cells) =
        c455_import_qualification_fixture();
    assert!(qualify_score_import_records(
        &imports, &obligations, &previous_r, &cap_q, &upper, &sink_cells).is_ok());

    let mut relabeled = imports.clone();
    relabeled[0].1 = ScoreRelationReadAuthor::WorkUpper {
        owner: OWNER - 1, height: OWNER + 1,
    };
    assert!(qualify_score_import_records(
        &relabeled, &obligations, &previous_r, &cap_q, &upper, &sink_cells)
        .unwrap_err().contains("order/author/value"));

    let mut relabeled_projection = previous_r.clone();
    relabeled_projection[0].0 = upper[0].0;
    assert!(qualify_score_import_records(
        &imports, &obligations, &relabeled_projection, &cap_q, &upper, &sink_cells)
        .unwrap_err().contains("PreviousR projection/import source qualification"));

    let mut upper_fault = upper.clone();
    upper_fault[0].0 += 1;
    assert!(qualify_score_import_records(
        &imports, &obligations, &previous_r, &cap_q, &upper_fault, &sink_cells)
        .unwrap_err().contains("WorkUpper projection/import source qualification"));

    let mut missing = imports.clone();
    missing.remove(0);
    assert!(qualify_score_import_records(
        &missing, &obligations, &previous_r, &cap_q, &upper, &sink_cells)
        .unwrap_err().contains("exact source import/projection census"));

    let mut duplicate = imports.clone();
    duplicate[0] = duplicate[1];
    assert!(qualify_score_import_records(
        &duplicate, &obligations, &previous_r, &cap_q, &upper, &sink_cells)
        .unwrap_err().contains("order/author/value"));

    let mut wrong_context = imports.clone();
    wrong_context[0].1 = ScoreRelationReadAuthor::PreviousR {
        context: 1, owner: OWNER - 1,
    };
    assert!(qualify_score_import_records(
        &wrong_context, &obligations, &previous_r, &cap_q, &upper, &sink_cells)
        .unwrap_err().contains("order/author/value"));
}

/// This fixture checks only domain accounting and bit comparison. It does not
/// manufacture a native H21 source, packed-row provenance, or proof authority.
fn c372_semantic_cell_fixture() -> (BTreeMap<usize, (Writer, bool)>, Vec<u8>) {
    let mut cells = BTreeMap::new();
    for context in 0..2 {
        let score = ScoreReplayAuthor {context, origin: OWNER + 1,
            previous_owner: OWNER - 1, max_owner: CAP_MAX_OWNER, cap_owner: OWNER};
        for (range, writer) in [
            (H21EligibleMapStage::map_live(context).unwrap(), Writer::Map(context)),
            (H21EligibleMapStage::score_live(context).unwrap(), Writer::Score(score)),
            (H21EligibleMapStage::slack_live(context).unwrap(), Writer::Slack(context)),
            (H21EligibleMapStage::cap_live(context).unwrap(), Writer::Cap(context)),
        ] {
            for local in range {
                assert!(cells.insert(OWNER * WIDTH + local, (writer, false)).is_none());
            }
        }
    }
    for bit in 0..224 {
        assert!(cells.insert(OWNER * WIDTH + crate::legacy_envelope_map::D_LOCAL + bit,
            (Writer::WorkLocal, false)).is_none());
        assert!(cells.insert((OWNER - 1) * WIDTH + 987_450 + bit,
            (Writer::WorkUpper, true)).is_none());
    }
    for context in 0..2 {
        for bit in 0..225 {
            assert!(cells.insert((OWNER - 1) * WIDTH + [677_501, 685_693][context]
                + 1_318 + bit, (Writer::PreviousR(context), true)).is_none());
        }
    }
    assert_eq!(cells.len(), 21_378);
    (cells, vec![0; WIDTH / 8])
}

#[test]
fn c372_semantic_local_and_foreign_domains_have_exact_census_without_native_authority() {
    let (cells, packed) = c372_semantic_cell_fixture();
    assert_eq!(reconcile_local_cells_with_bytes_845759(&cells, &packed).unwrap(),
        (20_704, 674));
    let mut short = packed.clone(); short.pop();
    assert_eq!(reconcile_local_cells_with_bytes_845759(&cells, &short).unwrap_err(),
        "C372 packed owner byte width");
    let mut extra = cells.clone();
    extra.insert(OWNER * WIDTH + 10, (Writer::Header, false));
    assert_eq!(reconcile_local_cells_with_bytes_845759(&extra, &packed).unwrap_err(),
        "C372 exact local/foreign cell partition");
    for (wire, expected) in [
        (OWNER * WIDTH + H21EligibleMapStage::map_live(0).unwrap().start,
            "C372 missing local cell"),
        ((OWNER - 1) * WIDTH + 987_450, "C372 foreign WorkUpper"),
        ((OWNER - 1) * WIDTH + 677_501 + 1_318, "C372 foreign PreviousR"),
    ] {
        let mut missing = cells.clone(); missing.remove(&wire);
        assert!(reconcile_local_cells_with_bytes_845759(&missing, &packed)
            .unwrap_err().starts_with(expected));
    }
}

#[test]
fn c372_semantic_local_bits_and_typed_writers_reject_independent_faults() {
    let (cells, packed) = c372_semantic_cell_fixture();
    let locals = [
        H21EligibleMapStage::map_live(0).unwrap().start,
        H21EligibleMapStage::map_live(1).unwrap().start,
        H21EligibleMapStage::score_live(0).unwrap().start,
        H21EligibleMapStage::score_live(1).unwrap().start,
        H21EligibleMapStage::slack_live(0).unwrap().start,
        H21EligibleMapStage::slack_live(1).unwrap().start,
        H21EligibleMapStage::cap_live(0).unwrap().start,
        H21EligibleMapStage::cap_live(1).unwrap().start,
        crate::legacy_envelope_map::D_LOCAL,
    ];
    for (domain, &local) in locals.iter().enumerate() {
        let mut wrong_bit = packed.clone();
        wrong_bit[local / 8] ^= 1 << (local % 8);
        let error = reconcile_local_cells_with_bytes_845759(&cells, &wrong_bit).unwrap_err();
        assert!(error.contains(&format!("first=Some(({domain}, {local}))")), "{error}");
        let mut wrong_writer = cells.clone();
        wrong_writer.insert(OWNER * WIDTH + local, (Writer::Header, false));
        assert!(reconcile_local_cells_with_bytes_845759(&wrong_writer, &packed)
            .unwrap_err().starts_with("C372 wrong local writer"));
    }
    let mut wrong_semantic_bit = cells.clone();
    wrong_semantic_bit.insert(OWNER * WIDTH + locals[0], (Writer::Map(0), true));
    assert!(reconcile_local_cells_with_bytes_845759(&wrong_semantic_bit, &packed)
        .unwrap_err().contains("first=Some((0,"));
    let mut nonzero_slack = cells.clone();
    nonzero_slack.insert(OWNER * WIDTH + locals[4], (Writer::Slack(0), true));
    assert!(reconcile_local_cells_with_bytes_845759(&nonzero_slack, &packed)
        .unwrap_err().starts_with("C372 nonzero Slack"));
    let mut wrong_foreign = cells;
    wrong_foreign.insert((OWNER - 1) * WIDTH + 987_450,
        (Writer::PreviousR(0), true));
    assert!(reconcile_local_cells_with_bytes_845759(&wrong_foreign, &packed)
        .unwrap_err().starts_with("C372 foreign WorkUpper"));
}

/// Structural extension of the synthetic zero fixture. Map ROW terms and
/// import coordinates come from the canonical symbolic Maps; the zero-valued
/// read bits remain synthetic and carry no native-source claim.
fn map_import_fixture() -> (Eligible08OwnerSink, Eligible08OwnerLease) {
    let (sink, mut lease) = fixture();
    let maps = H21EligibleMapStage::source_maps().unwrap();
    let descriptor = H21EligibleMapStage::descriptor();
    let mut map_reads = Vec::new();
    for (context, map) in maps.iter().enumerate() {
        lease.source.map_stage.map_terms[context] =
            crate::bank53_map::map_owner_terms_for_descriptor(
                map, OWNER as u64, context, descriptor).unwrap();
        for import in map.imports(OWNER as u64).unwrap() {
            let author = match import.kind {
                Kind::Difficulty => RequiredAuthor::WorkDifficulty {
                    owner: import.owner as usize, height: import.owner as usize + 2,
                },
                Kind::Timestamp => RequiredAuthor::HeaderTimestamp {
                    owner: import.owner as usize, height: import.owner as usize + 1,
                },
            };
            for bit in 0..import.width {
                map_reads.push(PendingRead {consumer: Writer::Map(context),
                    wire: map.input_index(import, bit).unwrap(), author,
                    value: false});
            }
        }
    }
    require_canonical_map_rows(&lease.source, &maps, descriptor).unwrap();
    let (cells, rows, reads) = material(&lease.binding, &lease.source, &map_reads).unwrap();
    lease.map_reads = map_reads;
    lease.cells = cells;
    lease.rows = rows;
    lease.reads = reads;
    (sink, lease)
}

fn rebuild_reads(lease: &mut Eligible08OwnerLease) {
    lease.reads = material(&lease.binding, &lease.source, &lease.map_reads).unwrap().2;
}

fn reject(mut sink: Eligible08OwnerSink, lease: Eligible08OwnerLease, expected: &str) {
    let before_cells = sink.state.cells.clone();
    let before_rows = sink.state.rows.clone();
    let before_terms = sink.state.terms.clone();
    let before_reads = sink.state.reads.clone();
    let before_published = sink.state.published;
    let before_source = sink.source.clone();
    let error = sink.admit(lease).err().expect("mutant admitted");
    assert_eq!(error, expected);
    assert_eq!(sink.state.cells, before_cells);
    assert_eq!(sink.state.rows, before_rows);
    assert_eq!(sink.state.terms, before_terms);
    assert_eq!(sink.state.reads, before_reads);
    assert_eq!(sink.state.published, before_published);
    assert!(sink.source == before_source);
}

#[test]
fn c191_one_owner_atomic_join_retains_all_authored_zeros_and_pending_sources() {
    let (mut sink, lease) = fixture();
    let duplicate = lease.clone();
    let admitted = sink.admit(lease).unwrap();
    assert_eq!(admitted.cell_count(), 16_384);
    assert_eq!(admitted.term_count(), 778);
    assert_eq!(admitted.pending_read_count(), 1_028);
    assert_eq!(sink.state.cells.len(), 16_384);
    assert!(sink.state.cells.values().all(|(_, bit)| !bit));
    assert_eq!(sink.pending_sources().len(), 1_028);
    assert!(sink.pending_sources().iter().any(|r|
        matches!(r.required_author(), RequiredAuthor::Cap {cap_owner: OWNER, ..})
            && r.wire() / WIDTH == OWNER && !r.expected_bit()));
    reject(sink, duplicate, "Eligible08 sink destination binding/duplicate");
}

impl Eligible08OwnerSink {
    /// Native-only continuation of c208. No synthetic source constructor.
    pub(crate) fn c210_native_cap_upper_probe_for_test(&mut self, context: &H21EligibleContext<'_>,
        cap: crate::h21_scheduled_family_ledger::FirstModernCapPublication) {
        let snap = |sink: &Eligible08OwnerSink| (sink.binding.clone(), sink.state.clone(),
            sink.source.clone(), sink.work_source.clone(), sink.upper_source.clone(),
            sink.cap_source.as_ref().map(|s| s as *const _),
            sink.previous_r_source.as_ref().map(|s| s as *const _));
        assert_eq!(self.state.cells.len(), 17_058);
        assert_eq!(self.state.reads.len(), 578);
        assert!(self.cap_source.is_none() && self.upper_source.is_none());
        assert!(self.previous_r_source.is_some());
        assert_eq!(cap.pending_max_read_count(), 448);
        assert_eq!(cap.pending_max_source_owners(), vec![844_670]);
        let material = cap.checked_material().expect("genuine Cap source replay");
        assert_eq!(material.cells.len(), 4096);
        for c in 0..2 {
            assert_eq!(material.q[c].len(), 65);
            assert_eq!(material.rows.iter().filter(|(writer, _)| *writer == Some(c)).count(), 6419);
        }
        let original = self.state.clone();
        let index = self.state.reads.iter().position(|read|
            matches!(read.author, RequiredAuthor::Cap {context: 0, ..})).unwrap();
        self.state.reads[index].value ^= true;
        let mutated = snap(self);
        assert_eq!(self.admit_first_modern_cap(cap.clone()).err().unwrap(),
            "Eligible08 sink Cap source bit/duplicate read");
        assert!(snap(self) == mutated);
        self.state = original;
        println!("C210_NATIVE_CAP_REJECT context=0 rollback=true");
        let before = snap(self);
        let non_cap: Vec<_> = self.state.reads.iter().filter(|r|
            !matches!(r.author, RequiredAuthor::Cap {..})).cloned().collect();
        assert_eq!(self.state.reads.len() - non_cap.len(), 130);
        let duplicate = cap.clone();
        let admitted = self.admit_first_modern_cap(cap).expect("native Cap ROW coexistence and q join");
        assert_eq!(admitted.cell_count(), 21_154);
        assert_eq!(admitted.pending_read_count(), 448);
        assert_eq!(admitted.term_count(), before.1.terms.len() + material.rows.len());
        let mut expected_terms = before.1.terms.clone();
        expected_terms.extend(material.rows.iter().map(|(c, term)| Row {
            writer: c.map_or(Writer::Header, Writer::Cap), term: term.clone() }));
        assert_eq!(self.state.terms, expected_terms);
        for (row, author) in &before.1.rows { assert_eq!(self.state.rows.get(row), Some(author)); }
        for (wire, value) in &before.1.cells { assert_eq!(self.state.cells.get(wire), Some(value)); }
        for &(wire, c, value) in &material.cells {
            assert_eq!(self.state.cells.get(&wire), Some(&(Writer::Cap(c), value)));
        }
        assert_eq!(self.state.reads, non_cap);
        assert!(self.binding == before.0 && self.source == before.2 && self.work_source == before.3
            && self.upper_source == before.4 && self.previous_r_source.as_ref().map(|s| s as *const _) == before.6);
        assert_eq!(self.pending_cap_max_read_count(), 448);
        assert_eq!(self.cap_source.as_ref().unwrap().pending_max_source_owners(), vec![844_670]);
        let after_cap = snap(self);
        assert_eq!(self.admit_first_modern_cap(duplicate).err().unwrap(), "Eligible08 sink Cap order/duplicate");
        assert!(snap(self) == after_cap);
        println!("C210_NATIVE_CAP_JOIN cells=21154 pending=448 resolved_cap=130 cap_max_pending=448 cap_max_owner=844670 row_occurrences_preserved=true duplicate_rejected=true");
        let index = self.state.reads.iter().position(|read| match read.consumer {
            Writer::Score(author) => author.context == 0 && matches!(read.author, RequiredAuthor::WorkUpper {..}),
            _ => false }).unwrap();
        let original = self.state.clone();
        self.state.reads[index].value ^= true;
        let mutated = snap(self);
        assert_eq!(context.join_owner_work_upper_845759(self).err().unwrap(),
            "Eligible08 sink Upper source bit/duplicate read");
        assert!(snap(self) == mutated);
        self.state = original;
        println!("C210_NATIVE_UPPER_REJECT context=0 post_cap=true rollback=true");
        std::io::Write::flush(&mut std::io::stdout()).unwrap();
        let before_upper = snap(self);
        let admitted = context.join_owner_work_upper_845759(self).expect("native Upper448 to Score join");
        assert_eq!(admitted.cell_count(), 21_378);
        assert_eq!(admitted.pending_read_count(), 0);
        assert_eq!(admitted.term_count(), before_upper.1.terms.len());
        assert!(self.state.rows == before_upper.1.rows && self.state.terms == before_upper.1.terms);
        assert_eq!(self.state.published, before_upper.1.published);
        for (wire, value) in &before_upper.1.cells { assert_eq!(self.state.cells.get(wire), Some(value)); }
        let upper = self.upper_source.as_ref().unwrap().checked_upper(self.binding.root,
            self.binding.total, self.binding.profile, &self.binding.cut, OWNER - 1).unwrap();
        assert_eq!(upper.len(), 224);
        for &(wire, value) in upper {
            assert!(!before_upper.1.cells.contains_key(&wire));
            assert_eq!(self.state.cells.get(&wire), Some(&(Writer::WorkUpper, !value.is_zero())));
        }
        assert!(self.binding == before_upper.0 && self.source == before_upper.2
            && self.work_source == before_upper.3);
        assert_eq!(self.cap_source.as_ref().map(|s| s as *const _), before_upper.5);
        assert_eq!(self.previous_r_source.as_ref().map(|s| s as *const _), before_upper.6);
        assert!(self.pending_sources().is_empty());
        assert_eq!(self.pending_cap_max_read_count(), 448);
        assert_eq!(self.cap_source.as_ref().unwrap().pending_max_source_owners(), vec![844_670]);
        assert_eq!(self.retained_work_local_counts(), (3265, 1184));
        let after = snap(self);
        assert_eq!(context.join_owner_work_upper_845759(self).err().unwrap(), "Eligible08 sink Upper order/duplicate");
        assert!(snap(self) == after);
        println!("C210_NATIVE_CAP_UPPER_PASS owner=845759 cells=21378 selected_pending=0 cap_max_pending=448 cap_max_owner=844670 resolved_cap=130 resolved_upper=448 upper_source_owner=845758 upper_cells=224 source_retained=true custodians_preserved=true duplicate_rejected=true rollback=true global_x_row=false pcs_proof_client=false");
        std::io::Write::flush(&mut std::io::stdout()).unwrap();
    }

    /// Called only with the genuine c187 closed-stream sink and native context.
    /// No fixture, relation constructor or detached R token enters this probe.
    pub(crate) fn c208_native_r450_probe_for_test(&mut self, context: &H21EligibleContext<'_>) {
        let snap = |sink: &Eligible08OwnerSink| (sink.binding.clone(), sink.state.clone(),
            sink.source.clone(), sink.work_source.clone(), sink.upper_source.clone(),
            sink.cap_source.as_ref().map(|s| s as *const _),
            sink.previous_r_source.as_ref().map(|s| s as *const _));
        assert_eq!(self.state.cells.len(), 16_608);
        assert_eq!(self.state.reads.len(), 1_028);
        assert!(self.source.is_some() && self.work_source.is_some());
        assert!(self.previous_r_source.is_none());
        assert_eq!(self.retained_work_local_counts(), (3265, 1184));
        // Binding and prerequisite faults fail before any expensive native mint.
        for kind in 0..5 {
            let original = self.binding.clone();
            match kind { 0 => self.binding.root[0] ^= 1, 1 => self.binding.total[0] ^= 1,
                2 => self.binding.profile[0] ^= 1, 3 => self.binding.cut.push(0),
                _ => self.binding.maps.swap(0, 1) }
            let before = snap(self);
            assert_eq!(context.join_owner_previous_r_845759(self).err().unwrap(),
                "R450 sink exact destination binding");
            assert!(snap(self) == before);
            self.binding = original;
            println!("C208_R450_PREMINT_REJECT kind=binding{kind} rollback=true");
        }
        for kind in 0..3 {
            let published = self.state.published;
            let source = if kind == 1 { self.source.take() } else { None };
            let work = if kind == 2 { self.work_source.take() } else { None };
            if kind == 0 { self.state.published = false; }
            let before = snap(self);
            assert_eq!(context.join_owner_previous_r_845759(self).err().unwrap(),
                "R450 sink order/duplicate");
            assert!(snap(self) == before);
            self.state.published = published;
            if kind == 1 { self.source = source; }
            if kind == 2 { self.work_source = work; }
            println!("C208_R450_PREMINT_REJECT kind=order{kind} rollback=true");
        }
        // Four calls mint genuine physical source tokens. Only the sink input
        // changes; W/U, ordered source terms and native relation stay fixed.
        for kind in 0..4 {
            let original = self.state.clone();
            let context_index = kind % 2;
            let index = self.state.reads.iter().position(|read|
                matches!(read.author, RequiredAuthor::PreviousR {context, ..}
                    if context == context_index)).unwrap();
            let expected = match kind {
                0 | 1 => { self.state.reads[index].value ^= true;
                    "R450 sink source bit/duplicate read" },
                2 => { self.state.reads.remove(index); "R450 sink exact 450-read census" },
                _ => { self.state.reads.push(self.state.reads[index].clone());
                    "R450 sink source bit/duplicate read" },
            };
            let before = snap(self);
            assert_eq!(context.join_owner_previous_r_845759(self).err().unwrap(), expected);
            assert!(snap(self) == before);
            self.state = original;
            println!("C208_R450_NATIVE_REJECT kind={kind} context={context_index} rollback=true");
            std::io::Write::flush(&mut std::io::stdout()).unwrap();
        }
        let before = snap(self);
        let non_r: Vec<_> = self.state.reads.iter().filter(|read|
            !matches!(read.author, RequiredAuthor::PreviousR {..})).cloned().collect();
        assert_eq!(self.state.reads.len() - non_r.len(), 450);
        let admitted = context.join_owner_previous_r_845759(self)
            .expect("genuine native R450 mint-to-sink positive");
        assert_eq!(admitted.cell_count(), 17_058);
        assert_eq!(admitted.pending_read_count(), 578);
        assert_eq!(admitted.term_count(), before.1.terms.len());
        assert!(self.state.rows == before.1.rows && self.state.terms == before.1.terms);
        assert_eq!(self.state.published, before.1.published);
        assert_eq!(self.state.reads, non_r);
        assert!(self.binding == before.0 && self.source == before.2
            && self.work_source == before.3 && self.upper_source == before.4);
        assert_eq!(self.cap_source.as_ref().map(|s| s as *const _), before.5);
        assert!(self.previous_r_source.is_some());
        let projection = self.previous_r_source.as_ref().unwrap().checked_projection(
            self.binding.root, self.binding.total, self.binding.profile,
            &self.binding.cut, &self.binding.maps).unwrap();
        for &(wire, c, bit) in &projection.cells[1] {
            assert!(!before.1.cells.contains_key(&wire));
            assert_eq!(self.state.cells.get(&wire), Some(&(Writer::PreviousR(c), bit)));
        }
        for (wire, value) in &before.1.cells { assert_eq!(self.state.cells.get(wire), Some(value)); }
        assert_eq!(self.state.reads.iter().filter(|r|
            matches!(r.author, RequiredAuthor::Cap {..})).count(), 130);
        assert_eq!(self.state.reads.iter().filter(|r|
            matches!(r.author, RequiredAuthor::WorkUpper {..})).count(), 448);
        let after = snap(self);
        assert_eq!(context.join_owner_previous_r_845759(self).err().unwrap(),
            "R450 sink order/duplicate");
        assert!(snap(self) == after);
        println!("C208_NATIVE_R450_SINK_PASS owner=845759 cells=17058 pending=578 resolved_previous_r=450 cap=130 work_upper=448 native_mints=5 row19_preserved=true custodians_preserved=true source_retained=true duplicate_rejected=true rollback=true global_x_row=false pcs_proof_client=false");
        std::io::Write::flush(&mut std::io::stdout()).unwrap();
    }
}

/// Conditional pending-read join only: the Score sink and Work prerequisite
/// are structural fixtures. No PremodernRPublication/native token is minted.
fn r450_conditional_sink() -> (Eligible08OwnerSink, R450Projection) {
    let (mut sink, lease) = fixture();
    sink.admit(lease).unwrap();
    sink.work_source = Some(structural_work_source());
    let (projection, identity) = conditional_r450_projection_for_test();
    sink.binding = Binding {root: identity.parent_root, total: identity.parent_total,
        profile: identity.parent_profile, cut: identity.cut_identity, maps: identity.map_bindings};
    for read in &mut sink.state.reads {
        if let RequiredAuthor::PreviousR {context, ..} = read.author {
            let bit = read.wire - ((OWNER - 1) * WIDTH + [677_501, 685_693][context] + 1318);
            read.value = projection.cells[1][context * 225 + bit].2;
        }
    }
    (sink, projection)
}

fn reject_r450_sink(sink: &Eligible08OwnerSink, binding: &Binding,
    projection: &R450Projection, expected: &str) {
    let before = sink.state.clone(); let source = sink.source.clone();
    let local = sink.work_source.clone(); let upper = sink.upper_source.clone();
    let cap = sink.cap_source.as_ref().map(|source| source as *const _);
    let r = sink.previous_r_source.as_ref().map(|source| source as *const _);
    assert_eq!(sink.prepare_previous_r(binding, projection).err().unwrap(), expected);
    assert!(sink.state == before); assert!(sink.source == source); assert!(sink.work_source == local);
    assert!(sink.upper_source == upper); assert_eq!(sink.cap_source.as_ref().map(|s| s as *const _), cap);
    assert_eq!(sink.previous_r_source.as_ref().map(|s| s as *const _), r);
    assert!(sink.binding == *binding || expected == "R450 sink exact destination binding");
}

#[test]
fn c205_r450_conditional_pending_join_resolves_exact450_and_preserves_all_other_state() {
    let (sink, projection) = r450_conditional_sink(); let before = sink.state.clone();
    let next = sink.prepare_previous_r(&sink.binding, &projection).unwrap();
    assert_eq!(next.cells.len(), before.cells.len() + 450);
    assert_eq!(next.reads.len(), before.reads.len() - 450);
    assert!(next.rows == before.rows); assert_eq!(next.terms, before.terms);
    assert_eq!(next.published, before.published);
    assert_eq!(next.reads, before.reads.into_iter().filter(|read|
        !matches!(read.author, RequiredAuthor::PreviousR {..})).collect::<Vec<_>>());
    assert!(sink.previous_r_source.is_none(), "conditional preparation cannot mint native authority");
    let mut destination = sink; destination.state = next;
    reject_r450_sink(&destination, &destination.binding, &projection, "R450 sink duplicate X including equal");
}

#[test]
fn c205_r450_conditional_source_domains_consumers_bits_omission_and_duplicate_fail_without_mutation() {
    let (mut sink, projection) = r450_conditional_sink();
    for context in 0..2 { for kind in 0..11 {
        let before = sink.state.clone();
        let index = sink.state.reads.iter().position(|read|
            matches!(read.author, RequiredAuthor::PreviousR {context: c, ..} if c == context)).unwrap();
        let expected = match kind {
            0 => { sink.state.reads[index].value ^= true; "R450 sink source bit/duplicate read" },
            1 => { sink.state.reads[index].author = RequiredAuthor::PreviousR {context, owner: 417_790}; "R450 sink exact typed source/consumer" },
            2 => { sink.state.reads[index].author = RequiredAuthor::PreviousR {context: context ^ 1, owner: OWNER - 1}; "R450 sink exact typed source/consumer" },
            3 => { sink.state.reads[index].consumer = Writer::Map(context); "R450 sink exact Score consumer" },
            4 => { if let Writer::Score(ref mut author) = sink.state.reads[index].consumer { author.previous_owner -= 1; } "R450 sink exact typed source/consumer" },
            5 => { if let Writer::Score(ref mut author) = sink.state.reads[index].consumer { author.origin -= 1; } "R450 sink exact typed source/consumer" },
            6 => { if let Writer::Score(ref mut author) = sink.state.reads[index].consumer { author.max_owner += 1; } "R450 sink exact typed source/consumer" },
            7 => { if let Writer::Score(ref mut author) = sink.state.reads[index].consumer { author.cap_owner += 1; } "R450 sink exact typed source/consumer" },
            8 => { sink.state.reads[index].wire -= 1; "R450 sink exact read domain" },
            9 => { sink.state.reads.remove(index); "R450 sink exact 450-read census" },
            _ => { sink.state.reads.push(sink.state.reads[index].clone()); "R450 sink source bit/duplicate read" },
        };
        reject_r450_sink(&sink, &sink.binding, &projection, expected);
        sink.state = before;
    }}
    for kind in 0..5 {
        let mut bad = projection.clone();
        let expected = match kind {
            0 => { bad.cells[1].pop(); "R450 sink source census" },
            1 => { let duplicate = bad.cells[1][0]; bad.cells[1].push(duplicate); "R450 sink source census" },
            2 => { bad.cells[1].swap(0, 1); "R450 sink exact physical source/order" },
            3 => { bad.cells[1][0].0 += WIDTH; "R450 sink exact physical source/order" },
            _ => { bad.cells[1][0].1 ^= 1; "R450 sink exact physical source/order" },
        };
        reject_r450_sink(&sink, &sink.binding, &bad, expected);
    }
}

#[test]
fn c205_r450_conditional_binding_and_order_fail_before_projection() {
    let (mut sink, projection) = r450_conditional_sink();
    for field in 0..5 {
        let mut binding = sink.binding.clone();
        match field { 0 => binding.root[0] ^= 1, 1 => binding.total[0] ^= 1,
            2 => binding.profile[0] ^= 1, 3 => binding.cut.push(0), _ => binding.maps.swap(0, 1) }
        reject_r450_sink(&sink, &binding, &projection, "R450 sink exact destination binding");
    }
    sink.state.published = false;
    reject_r450_sink(&sink, &sink.binding, &projection, "R450 sink order/duplicate");
    sink.state.published = true;
    let source = sink.source.take();
    reject_r450_sink(&sink, &sink.binding, &projection, "R450 sink order/duplicate");
    sink.source = source;
    sink.work_source = None;
    reject_r450_sink(&sink, &sink.binding, &projection, "R450 sink order/duplicate");
}

#[test]
fn c192_canonical_map_terms_and_typed_imports_join_score_pending_reads() {
    let (mut sink, lease) = map_import_fixture();
    assert_eq!(lease.map_reads.len(), 448);
    assert_eq!(lease.map_reads.iter().filter(|r| r.consumer == Writer::Map(0)).count(), 224);
    assert_eq!(lease.map_reads.iter().filter(|r| r.consumer == Writer::Map(1)).count(), 224);
    assert!(lease.map_reads.iter().all(|read|
        matches!(read.consumer, Writer::Map(_))
            && matches!(read.author, RequiredAuthor::WorkDifficulty {
                owner: 845_759, height: 845_761,
            })
            && read.wire / WIDTH == 845_759));
    let expected_terms = lease.rows.len();
    assert!(expected_terms > 774, "canonical Map rows plus Score/Slack rows");
    let admitted = sink.admit(lease).unwrap();
    assert_eq!(admitted.cell_count(), 16_384);
    assert_eq!(admitted.term_count(), expected_terms);
    assert_eq!(admitted.pending_read_count(), 1_476);
    let pending = sink.pending_sources();
    assert_eq!(pending.len(), 1_476);
    assert_eq!(pending.iter().filter(|r|
        matches!(r.required_author(), RequiredAuthor::WorkDifficulty {
            owner: 845_759, height: 845_761,
        })).count(), 448);
    assert_eq!(pending.iter().filter(|r|
        matches!(r.required_author(), RequiredAuthor::PreviousR {
            context: 0, owner: 845_758,
        } | RequiredAuthor::PreviousR {context: 1, owner: 845_758})).count(), 450);
    assert_eq!(pending.iter().filter(|r|
        matches!(r.required_author(), RequiredAuthor::Cap {
            origin: 845_760, max_owner: 844_670, cap_owner: 845_759, ..
        })).count(), 130);
    assert_eq!(pending.iter().filter(|r|
        matches!(r.required_author(), RequiredAuthor::WorkUpper {
            owner: 845_758, height: 845_760,
        })).count(), 448);
    assert!(pending.iter().all(|r| r.wire() / WIDTH <= 845_759));
}

#[test]
fn c192_map_read_edge_mutants_reject_atomically() {
    let (sink, mut duplicate) = map_import_fixture();
    let edge = duplicate.map_reads.iter().find(|r| r.consumer == Writer::Map(0)).unwrap().clone();
    duplicate.map_reads.push(edge);
    rebuild_reads(&mut duplicate);
    reject(sink, duplicate, "Eligible08 sink duplicate read edge");

    let (sink, mut disagreement) = map_import_fixture();
    let shared_wire = disagreement.map_reads.iter()
        .find(|r| r.consumer == Writer::Map(0)
            && disagreement.map_reads.iter().any(|other|
                other.consumer == Writer::Map(1) && other.wire == r.wire))
        .map(|r| r.wire).expect("canonical maps share an imported Work-D wire");
    disagreement.map_reads.iter_mut().find(|r|
        r.consumer == Writer::Map(0) && r.wire == shared_wire).unwrap().value = true;
    rebuild_reads(&mut disagreement);
    reject(sink, disagreement, "Eligible08 sink typed read disagreement/extent");
}

#[test]
fn c192_missing_active_map_read_rejects_atomically() {
    let (sink, mut missing) = map_import_fixture();
    let active_edge = missing.map_reads.iter().position(|read| {
        let Writer::Map(context) = read.consumer else { return false; };
        missing.source.map_stage.map_terms[context].iter().any(|term| {
            let gate = &term.gate;
            (gate.left == read.wire && (!gate.c1.is_zero() || !gate.c3.is_zero()))
                || (gate.right == read.wire && (!gate.c2.is_zero() || !gate.c3.is_zero()))
        })
    }).expect("canonical Map import used by an active operand");
    missing.map_reads.remove(active_edge);
    rebuild_reads(&mut missing);
    reject(sink, missing, "Eligible08 sink unclassified active read");
}

#[test]
fn c191_binding_fields_and_source_binding_fail_atomically() {
    for field in 0..6 {
        let (sink, mut lease) = fixture();
        match field {
            0 => lease.binding.root[0] ^= 1,
            1 => lease.binding.total[0] ^= 1,
            2 => lease.binding.profile[0] ^= 1,
            3 => lease.binding.cut = crate::bank53_map::CutDescriptor::diagnostic08().canonical_identity(),
            4 => lease.binding.maps.swap(0, 1),
            5 => lease.source.map_stage.owner -= 1,
            _ => unreachable!(),
        }
        reject(sink, lease, if field == 5 {"Eligible08 sink source parent/cut/owner/binding"}
            else {"Eligible08 sink destination binding/duplicate"});
    }
}

#[test]
fn c191_missing_and_same_zero_duplicate_x_are_distinct_atomic_rejects() {
    let (sink, mut missing) = fixture();
    let index = missing.cells.iter().position(|c| matches!(c.writer, Writer::Slack(0))).unwrap();
    missing.cells.remove(index);
    reject(sink, missing, "Eligible08 sink exact source projection");
    let (sink, mut duplicate) = fixture();
    let zero = duplicate.cells.iter().find(|c| matches!(c.writer, Writer::Slack(0))).unwrap().clone();
    duplicate.cells.push(zero);
    reject(sink, duplicate, "Eligible08 sink duplicate/outside X author");
}

#[test]
fn c191_cross_writer_row_and_typed_import_mutants_fail_atomically() {
    let (sink, mut lease) = fixture();
    let score_row = lease.rows.iter().find(|r| matches!(r.writer, Writer::Score(_))).unwrap().term.row;
    lease.rows.iter_mut().find(|r| r.writer == Writer::Map(0)).unwrap().term.row = score_row;
    reject(sink, lease, "Eligible08 sink cross-writer ROW collision");
    let (sink, mut lease) = fixture();
    let read = lease.reads.iter_mut().find(|r| matches!(r.author, RequiredAuthor::PreviousR {..})).unwrap();
    read.author = RequiredAuthor::WorkUpper {owner: OWNER - 1, height: OWNER + 1};
    reject(sink, lease, "Eligible08 sink exact source projection");
    let (sink, mut lease) = fixture();
    lease.reads[0].value ^= true;
    reject(sink, lease, "Eligible08 sink exact source projection");
}

#[test]
fn c191_same_writer_row_multiplicity_survives_and_unclassified_read_stops_publication() {
    let (mut sink, mut lease) = fixture();
    let term = lease.source.map_stage.map_terms[0][0].clone();
    lease.source.map_stage.map_terms[0].push(term.clone());
    lease.rows.insert(1, Row {writer: Writer::Map(0), term});
    assert_eq!(sink.admit(lease).unwrap().term_count(), 779);
    let (sink, mut lease) = fixture();
    // Mutate the fixture's source too, so exact projection alone cannot catch
    // this control: active external reads require a classified source edge.
    let wire = 17 * WIDTH + crate::legacy_envelope_map::D_LOCAL;
    lease.source.map_stage.map_terms[0][0].gate.left = wire;
    lease.rows[0].term.gate.left = wire;
    reject(sink, lease, "Eligible08 sink unclassified active read");
}

#[test]
fn c191_active_wire_zero_cannot_bypass_source_author_coverage() {
    let (sink, mut lease) = fixture();
    lease.source.map_stage.map_terms[0][0].gate.left = 0;
    lease.rows[0].term.gate.left = 0;
    reject(sink, lease, "Eligible08 sink unclassified active read");
}

#[test]
fn c191_mint_rederives_map_rows_instead_of_trusting_coordinated_copies() {
    let maps = H21EligibleMapStage::source_maps().unwrap();
    let descriptor = H21EligibleMapStage::descriptor();
    let (_, lease) = fixture();
    let mut source = lease.source;
    for context in 0..2 {
        source.map_stage.map_terms[context] = crate::bank53_map::map_owner_terms_for_descriptor(
            &maps[context], OWNER as u64, context, descriptor).unwrap();
    }
    require_canonical_map_rows(&source, &maps, descriptor).unwrap();
    source.map_stage.map_terms[0][0].gate.c0 += Fr::one();
    assert_eq!(require_canonical_map_rows(&source, &maps, descriptor).err().unwrap(),
        "Eligible08 sink canonical Map source rows");
}

fn cap_publication()->crate::h21_scheduled_family_ledger::FirstModernCapPublication {
    use std::sync::OnceLock;
    use crate::{h21_scheduled_family_ledger::FirstModernCapPublication,
        h21_scheduled_max_cap::Eligible08NativeSnapshot,
        work_tree_history_plan::WorkTreeHistoryPlan};
    static SOURCE:OnceLock<FirstModernCapPublication>=OnceLock::new();
    SOURCE.get_or_init(|| {
        use blake2::{digest::consts::U32,Blake2b,Digest};
        let mut bytes=crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
        bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let profile=Blake2b::<U32>::digest(bytes).into();
        let plan=WorkTreeHistoryPlan::compile(1_827_840,21,[17;32],[0;28]).unwrap();
        let snapshot=Eligible08NativeSnapshot::constant_d_for_test([17;32],[0;28],profile,16).unwrap();
        let first=Eligible08NativeSnapshot::first_modern_constant_d_for_test(
            [17;32],[0;28],profile,16).unwrap();
        FirstModernCapPublication::synthetic_for_test(&plan,&snapshot,&first).unwrap()
    }).clone()
}

/// Full real HEADER/Cap circuits and their production publication, over a
/// synthetic constant-D snapshot; Map/Score input values remain synthetic.
fn cap_fixture()->(Eligible08OwnerSink,crate::h21_scheduled_family_ledger::FirstModernCapPublication) {
    let (sink,source,_)=cap_fixture_with_material();
    (sink,source)
}

fn cap_fixture_with_material()->(Eligible08OwnerSink,
    crate::h21_scheduled_family_ledger::FirstModernCapPublication,
    crate::h21_scheduled_family_ledger::CapJoinMaterial) {
    cap_fixture_with_material_including_score_reads(false)
}

fn cap_occurrence_fixture_with_material()->(Eligible08OwnerSink,
    crate::h21_scheduled_family_ledger::FirstModernCapPublication,
    crate::h21_scheduled_family_ledger::CapJoinMaterial) {
    cap_fixture_with_material_including_score_reads(true)
}

fn cap_fixture_with_material_including_score_reads(include_score_reads:bool)
    ->(Eligible08OwnerSink,
    crate::h21_scheduled_family_ledger::FirstModernCapPublication,
    crate::h21_scheduled_family_ledger::CapJoinMaterial) {
    let source=cap_publication();
    let material=source.checked_material().unwrap();
    let (mut sink,mut lease)=map_import_fixture();
    use blake2::{digest::consts::U32,Blake2b,Digest};
    let mut bytes=crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
    bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
    lease.binding.root=[17;32];lease.binding.total=[0;28];lease.binding.profile=Blake2b::<U32>::digest(bytes).into();
    lease.source.map_stage.parent_root=lease.binding.root;
    lease.source.map_stage.parent_total=lease.binding.total;
    lease.source.map_stage.parent_profile=lease.binding.profile;
    lease.source=lease.source.with_cap_q_for_sink_test(material.q.clone());
    if include_score_reads {
        lease.source=lease.source.with_score_read_alias_rows_for_sink_test();
    }
    let (cells,rows,reads)=material_for_cap_fixture(&lease);
    lease.cells=cells;lease.rows=rows;lease.reads=reads;
    sink.binding=lease.binding.clone();sink.admit(lease).unwrap();
    (sink,source,material)
}

fn c355_check_rows(header:&[Term],cap:&[(usize,Term)],
    observed:&[(Option<usize>,Term)])->Result<(),&'static str> {
    let observed_header=observed.iter().filter_map(|(writer,term)|
        writer.is_none().then(||term.clone())).collect::<Vec<_>>();
    if observed_header!=header {return Err("C355 raw HEADER occurrence mismatch");}
    let observed_cap=observed.iter().filter_map(|(writer,term)|
        writer.map(|context|(context,term.clone()))).collect::<Vec<_>>();
    if observed_cap!=cap {return Err("C355 Cap relation/ROW/gate occurrence mismatch");}
    Ok(())
}

fn c355_check_cells(expected:&[(usize,usize,bool)],observed:&[(usize,usize,bool)])
    ->Result<(),&'static str> {
    if expected!=observed {return Err("C355 Cap writer/wire/value occurrence mismatch");}
    Ok(())
}

fn c355_admit_candidate(sink:&mut Eligible08OwnerSink,
    source:crate::h21_scheduled_family_ledger::FirstModernCapPublication,
    material:crate::h21_scheduled_family_ledger::CapJoinMaterial,
    header:&[Term],cap:&[(usize,Term)],cells:&[(usize,usize,bool)])
    ->Result<Eligible08OwnerAdmission,String> {
    c355_check_rows(header,cap,&material.rows).map_err(str::to_owned)?;
    c355_check_cells(cells,&material.cells).map_err(str::to_owned)?;
    sink.admit_first_modern_cap_material(source,material)
}

fn c355_partition_key(relation:crate::header_daa_row_placement::Relation,
    term:&Term)->Vec<u8> {
    use ark_ff::{BigInteger,PrimeField};
    let mut key=Vec::with_capacity(1+8*3+32*4+9);
    match relation {
        crate::header_daa_row_placement::Relation::Header=>key.push(0),
        crate::header_daa_row_placement::Relation::Scheduled(
            crate::h21_scheduled_max_cap::Writer::Cap{context,origin})=>{
                key.push(1);key.extend_from_slice(&(context as u64).to_le_bytes());
                key.extend_from_slice(&(origin as u64).to_le_bytes());
            },
        _=>unreachable!("C355 partition contains only Header and Cap"),
    }
    key.extend_from_slice(&(term.row as u64).to_le_bytes());
    key.extend_from_slice(&(term.gate.left as u64).to_le_bytes());
    key.extend_from_slice(&(term.gate.right as u64).to_le_bytes());
    for coefficient in [term.gate.c0,term.gate.c1,term.gate.c2,term.gate.c3] {
        let mut bytes=coefficient.into_bigint().to_bytes_le();
        bytes.resize(32,0);key.extend_from_slice(&bytes);
    }
    key
}

fn c355_partition_multiset(rows:&[(crate::header_daa_row_placement::Relation,Term)])
    ->Vec<Vec<u8>> {
    let mut keys=rows.iter().map(|(relation,term)|c355_partition_key(*relation,term))
        .collect::<Vec<_>>();
    keys.sort();keys
}

#[test]
fn c355_owner845759_header_cap_row_partition_matches_and_tracks_open_edges() {
    let owner=OWNER;
    let parent=crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(
        1_827_840,21,[17;32],[0;28]).unwrap();
    let roster=crate::daa_history_roster::DaaHistoryRoster::compile(&parent).unwrap();
    let scheduled=crate::h21_scheduled_max_cap::Plan::eligible08();
    let row_plan=crate::header_daa_row_placement::RowPlan::new(&roster,&scheduled).unwrap();
    let batch=row_plan.stage_owner(owner).unwrap();
    assert_eq!(roster.owner_class(owner as u64).unwrap(),
        crate::daa_history_roster::OwnerClass::Carry);

    // One checked-material replay is shared by the source comparison and the
    // sink commit below. Its fixture values remain synthetic.
    let (mut sink,source,material)=cap_fixture_with_material();
    let raw_header=material.rows.iter().filter_map(|(writer,term)|
        writer.is_none().then(||term.clone())).collect::<Vec<_>>();
    let placed_header=row_plan.check_raw_header_placement(owner,&raw_header,&batch).unwrap();
    assert_ne!(raw_header,placed_header,"raw and ROW19-placed Header views stay distinct");

    let row_plan_cap=batch.terms().filter_map(|(relation,term)| match relation {
        crate::header_daa_row_placement::Relation::Scheduled(
            crate::h21_scheduled_max_cap::Writer::Cap{context,origin})=>{
                assert_eq!(origin,owner+1);Some((context,term.clone()))
            },
        _=>None,
    }).collect::<Vec<_>>();
    for lane in [0,1] {
        assert!(!batch.terms().any(|(relation,_)|relation
            ==crate::header_daa_row_placement::Relation::DaaLane(lane)),
            "Carry excludes arithmetic/alias DAA lanes");
    }
    for lane in [2,3] {
        assert!(batch.terms().any(|(relation,_)|relation
            ==crate::header_daa_row_placement::Relation::DaaLane(lane)),
            "Carry retains numeric and inactive-zero DAA lanes");
    }

    let cap_rows=material.rows.iter().filter_map(|(writer,term)|
        writer.map(|context|(context,term.clone()))).collect::<Vec<_>>();
    assert_eq!(row_plan_cap,cap_rows,"scheduled Cap placement is identity and ordered");
    let cap_cells=material.cells.iter().map(|(wire,context,value)|(*wire,*context,*value))
        .collect::<Vec<_>>();
    let expected_header=raw_header.clone();
    let expected_cap=cap_rows.clone();
    let expected_cells=cap_cells.clone();
    let before=sink.state.clone();

    // Mutants pass through the same source-comparison gate that precedes
    // admission. A rejection must leave the sink state and custody untouched.
    let mut wrong_rows=material.rows.clone();
    let first=wrong_rows.iter().position(|(writer,_)|writer.is_none()).unwrap();
    let other=(0..wrong_rows.len()).find(|index|*index!=first
        && wrong_rows[*index].0==wrong_rows[first].0
        && wrong_rows[*index].1!=wrong_rows[first].1).unwrap();
    let duplicate=wrong_rows[other].clone();
    wrong_rows[first]=duplicate;
    assert_eq!(wrong_rows.len(),material.rows.len());
    let omitted_and_duplicated=crate::h21_scheduled_family_ledger::CapJoinMaterial {
        rows:wrong_rows,cells:material.cells.clone(),q:material.q.clone()};
    assert!(c355_admit_candidate(&mut sink,source.clone(),omitted_and_duplicated,
        &expected_header,&expected_cap,&expected_cells).is_err());
    assert!(sink.state==before&&sink.cap_source.is_none());

    let mut wrong_author=material.rows.clone();
    let author_index=wrong_author.iter().position(|(writer,_)|*writer==Some(0)).unwrap();
    wrong_author[author_index].0=Some(1);
    let wrong_author_material=crate::h21_scheduled_family_ledger::CapJoinMaterial {
        rows:wrong_author,cells:material.cells.clone(),q:material.q.clone()};
    assert!(c355_admit_candidate(&mut sink,source.clone(),wrong_author_material,
        &expected_header,&expected_cap,&expected_cells).is_err());
    assert!(sink.state==before&&sink.cap_source.is_none());

    let mut wrong_cells=material.cells.iter().map(|(wire,context,value)|
        (*wire,*context,*value)).collect::<Vec<_>>();
    wrong_cells[0].2^=true;
    let wrong_value_material=crate::h21_scheduled_family_ledger::CapJoinMaterial {
        rows:material.rows.clone(),cells:wrong_cells,q:material.q.clone()};
    assert!(c355_admit_candidate(&mut sink,source.clone(),wrong_value_material,
        &expected_header,&expected_cap,&expected_cells).is_err());
    assert!(sink.state==before&&sink.cap_source.is_none());

    let before_reads=sink.pending_sources().to_vec();
    assert_eq!(source.pending_max_read_count(),448);
    assert_eq!(source.pending_max_source_owners(),vec![844_670]);
    let expected_appended=material.rows.iter().map(|(context,term)|Row{
        writer:context.map_or(Writer::Header,Writer::Cap),term:term.clone()}).collect::<Vec<_>>();
    let expected_material_cells=material.cells.clone();
    c355_admit_candidate(&mut sink,source,material,&expected_header,&expected_cap,
        &expected_cells).unwrap();

    let appended=&sink.state.terms[before.terms.len()..];
    assert_eq!(appended,expected_appended.as_slice());
    // The fixture is synthetic: this establishes only material-to-sink
    // readback, not authenticated author/value coverage for ROW operands.
    let mut cap_cells_by_wire=std::collections::BTreeMap::new();
    for &(wire,context,value) in &expected_material_cells {
        assert!(cap_cells_by_wire.insert(wire,(Writer::Cap(context),value)).is_none());
    }
    for (wire,cell) in &cap_cells_by_wire {
        assert_eq!(sink.state.cells.get(wire),Some(cell),"synthetic Cap material-to-sink readback");
    }
    let remaining_reads=before_reads.iter().filter(|read|
        !matches!(read.required_author(),RequiredAuthor::Cap{..})).cloned().collect::<Vec<_>>();
    assert_eq!(sink.pending_sources(),remaining_reads.as_slice());
    assert_eq!(sink.pending_cap_max_read_count(),448);
    assert_eq!(sink.pending_sources().iter().filter(|read|
        matches!(read.required_author(),RequiredAuthor::PreviousR{..})).count(),450);

    // Compare the complete Header+Cap ROW19 partition after converting only
    // the sink's raw Header occurrences through the RowPlan placement. Max
    // rows and sink Map/Score/Slack rows remain separate exclusive partitions.
    let row_plan_partition=batch.terms().filter_map(|(relation,term)|match relation {
        crate::header_daa_row_placement::Relation::Header=>Some((relation,term.clone())),
        crate::header_daa_row_placement::Relation::Scheduled(
            crate::h21_scheduled_max_cap::Writer::Cap{..})=>Some((relation,term.clone())),
        _=>None,
    }).collect::<Vec<_>>();
    let sink_header_raw=appended.iter().filter_map(|row|
        (row.writer==Writer::Header).then(||row.term.clone())).collect::<Vec<_>>();
    let sink_header_placed=row_plan.check_raw_header_placement(owner,&sink_header_raw,&batch).unwrap();
    let mut header_index=0usize;
    let sink_partition=appended.iter().map(|row|match row.writer {
        Writer::Header=>{
            let term=sink_header_placed[header_index].clone();header_index+=1;
            (crate::header_daa_row_placement::Relation::Header,term)
        },
        Writer::Cap(context)=>(crate::header_daa_row_placement::Relation::Scheduled(
            crate::h21_scheduled_max_cap::Writer::Cap{context,origin:owner+1}),row.term.clone()),
        _=>unreachable!("sink suffix is its Header/Cap publication"),
    }).collect::<Vec<_>>();
    assert_eq!(header_index,sink_header_placed.len());
    assert_eq!(sink_partition,row_plan_partition,"ordered Header+Cap relation/ROW/gate join");
    assert_eq!(c355_partition_multiset(&sink_partition),
        c355_partition_multiset(&row_plan_partition),"Header+Cap occurrence multiset");
    let base_rows=&sink.state.terms[..before.terms.len()];
    assert_eq!(base_rows,before.terms.as_slice());
    assert!(base_rows.iter().all(|row|matches!(row.writer,
        Writer::Map(_)|Writer::Score(_)|Writer::Slack(_))));

    // Index pending edges by wire without collapsing consumer occurrences.
    // Each Vec retains distinct consumer/expected-author/expected-bit tuples.
    // No RowPlan-relation-to-sink-writer identity is inferred from wire overlap.
    let active=batch.active_operands().collect::<Vec<_>>();
    let mut active_occurrences_by_wire=std::collections::BTreeMap::new();
    for operand in &active {
        *active_occurrences_by_wire.entry(operand.wire).or_insert(0usize)+=1;
    }
    let mut pending_by_wire=std::collections::BTreeMap::<usize,Vec<&PendingRead>>::new();
    for read in sink.pending_sources() {
        pending_by_wire.entry(read.wire()).or_default().push(read);
    }
    let mut cap_wire_overlap_occurrences=0usize;
    let mut sink_cell_overlap_occurrences=0usize;
    let mut pending_consumer_edges_on_active_wires=0usize;
    let mut named_open_occurrences=std::collections::BTreeMap::<&'static str,usize>::new();
    for (wire,occurrences) in &active_occurrences_by_wire {
        if cap_cells_by_wire.contains_key(wire) {
            cap_wire_overlap_occurrences+=occurrences;
        }
        let sink_cell=sink.state.cells.get(wire);
        let open=if sink_cell.is_some() {
            sink_cell_overlap_occurrences+=occurrences;
            "ROW consumer author compatibility is not joined"
        } else {
            "native HEADER/foreign/other producer value remains open"
        };
        *named_open_occurrences.entry(open).or_default()+=occurrences;
        pending_consumer_edges_on_active_wires+=pending_by_wire.get(wire).map_or(0,Vec::len);
    }
    assert!(!active.is_empty(),"ROW operand inventory is nonempty");
    assert!(cap_wire_overlap_occurrences>0,
        "no active-operand wire overlaps the synthetic Cap material partition");
    println!("synthetic wire report: active_operands={}, active_cap_overlap_occurrences={}, sink_cell_overlap_occurrences={}, pending_consumer_edges_on_active_wires={}, named_open_occurrences={:?}",
        active.len(),cap_wire_overlap_occurrences,sink_cell_overlap_occurrences,
        pending_consumer_edges_on_active_wires,named_open_occurrences);
    assert!(sink.work_source.is_none()&&sink.upper_source.is_none()
        &&sink.previous_r_source.is_none());
}

fn c358_raw_gate_occurrences(row19:&crate::header_daa_row_placement::Batch,
    sink:&Eligible08OwnerSink)->Vec<(ConsumerOccurrence,usize)> {
    use crate::header_daa_row_placement::{ActiveOperand,OperandSide};
    let mut expected=Vec::new();
    for (occurrence,(relation,term)) in row19.terms().enumerate() {
        let gate=&term.gate;
        let c1=gate.c1!=Fr::zero();let c2=gate.c2!=Fr::zero();let c3=gate.c3!=Fr::zero();
        if c1||c3 {
            let operand=ActiveOperand{occurrence,relation,row:term.row,side:OperandSide::Left,
                wire:gate.left,c1_active:c1,c2_active:false,c3_active:c3};
            expected.push((ConsumerOccurrence::Row19(operand),gate.left));
        }
        if c2||c3 {
            let operand=ActiveOperand{occurrence,relation,row:term.row,side:OperandSide::Right,
                wire:gate.right,c1_active:false,c2_active:c2,c3_active:c3};
            expected.push((ConsumerOccurrence::Row19(operand),gate.right));
        }
    }
    for (occurrence,row) in sink.state.terms.iter().enumerate() {
        let gate=&row.term.gate;
        if gate.c1!=Fr::zero()||gate.c3!=Fr::zero() {
            let operand=SinkOperand{occurrence,writer:row.writer,row:row.term.row,
                side:OperandSide::Left,wire:gate.left};
            expected.push((ConsumerOccurrence::Sink(operand),gate.left));
        }
        if gate.c2!=Fr::zero()||gate.c3!=Fr::zero() {
            let operand=SinkOperand{occurrence,writer:row.writer,row:row.term.row,
                side:OperandSide::Right,wire:gate.right};
            expected.push((ConsumerOccurrence::Sink(operand),gate.right));
        }
    }
    expected
}

fn c358_known_bit(source:OccurrenceSource)->Option<bool> {
    match source {
        OccurrenceSource::Resolved(claim)=>Some(claim.bit),
        OccurrenceSource::Pending{expected_bit,..}=>Some(expected_bit),
        OccurrenceSource::Open(_)=>None,
    }
}

#[test]
fn c358_owner845759_exact_occurrence_ledger_preserves_consumers_and_open_sources() {
    let plan=crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(
        1_827_840,21,[17;32],[0;28]).unwrap();
    let roster=crate::daa_history_roster::DaaHistoryRoster::compile(&plan).unwrap();
    let scheduled=crate::h21_scheduled_max_cap::Plan::eligible08();
    let row_plan=crate::header_daa_row_placement::RowPlan::new(&roster,&scheduled).unwrap();
    let row19=row_plan.stage_owner(OWNER).unwrap();
    let (mut sink,source,material)=cap_occurrence_fixture_with_material();
    let mut original_keys=std::collections::BTreeSet::new();
    for read in &sink.state.read_obligations {
        assert!(original_keys.insert((sink_read_slot(read.consumer).unwrap(),read.wire)),
            "the admitted sink has one obligation per consumer family and wire");
    }
    assert_eq!(sink.state.read_obligations.len(),1476);
    assert_eq!(sink.state.reads.len(),1476,"first Cap publication starts before its 130 reads resolve");
    sink.admit_first_modern_cap_material(source,material).unwrap();
    assert_eq!(sink.state.reads.len(),1346,"first Cap publication resolves its 130 exact reads");
    let ledger=sink.occurrence_ledger_845759(&row_plan,&row19,&plan,None).unwrap();
    for lane in [2,3] {
        let lane_reads=ledger.records.iter().filter(|read|matches!(read.consumer,
            ConsumerOccurrence::Row19(crate::header_daa_row_placement::ActiveOperand{
                relation:crate::header_daa_row_placement::Relation::DaaLane(found),..})
                if found==lane)).collect::<Vec<_>>();
        assert!(!lane_reads.is_empty(),"Carry DAA lane {lane} has active ROW occurrences");
    }
    let local_daa_reads=ledger.records.iter().filter(|read|
        matches!(read.consumer,ConsumerOccurrence::Row19(
            crate::header_daa_row_placement::ActiveOperand{
                relation:crate::header_daa_row_placement::Relation::DaaLane(3),..}))
        && is_local_daa_bank_wire(read.wire)).collect::<Vec<_>>();
    assert!(!local_daa_reads.is_empty(),"Carry lane 3 has active local DAA BANKS reads");
    assert!(local_daa_reads.iter().all(|read|matches!(read.source,
        OccurrenceSource::Open(OpenSource::UnqualifiedLocal))),
        "local Carry lane 3 DAA BANKS reads remain open without a native lease");
    let from_raw_gates=c358_raw_gate_occurrences(&row19,&sink);
    let from_ledger=ledger.records.iter().map(|read|(read.consumer,read.wire))
        .collect::<Vec<_>>();
    assert_eq!(from_ledger,from_raw_gates,"full ordered consumer/row/side/wire/activation census");
    assert_eq!(ledger.records.len(),ledger.resolved_count()+ledger.pending_count()+ledger.open_count());
    assert!(ledger.records.iter().any(|read|matches!(read.consumer,ConsumerOccurrence::Row19(_))
        && matches!(read.source,OccurrenceSource::Resolved(PhysicalClaim{
            author:PhysicalAuthor::PublishedCap{..},..}))));
    assert!(ledger.records.iter().any(|read|matches!(read.consumer,
        ConsumerOccurrence::Sink(SinkOperand{writer:Writer::Score(_),..}))
        && matches!(read.source,OccurrenceSource::Resolved(PhysicalClaim{
            author:PhysicalAuthor::PublishedCap{..},..}))));
    assert!(ledger.records.iter().any(|read|matches!(read.consumer,
        ConsumerOccurrence::Row19(crate::header_daa_row_placement::ActiveOperand{
            relation:crate::header_daa_row_placement::Relation::Header,..}))
        && matches!(read.source,OccurrenceSource::Open(_))));
    assert!(ledger.records.iter().any(|read|matches!(read.consumer,
        ConsumerOccurrence::Sink(SinkOperand{writer:Writer::Map(0),..}))
        && matches!(read.source,OccurrenceSource::Pending{
            author:RequiredAuthor::WorkDifficulty{owner:OWNER,..},..})));
    let shared=sink.state.read_obligations.iter().find(|read|read.consumer==Writer::Map(0)
        && sink.state.read_obligations.iter().any(|other|
            other.consumer==Writer::Map(1)&&other.wire==read.wire)).unwrap().wire;
    let consumers=ledger.records.iter().filter_map(|read|match read.consumer {
        ConsumerOccurrence::Sink(op) if op.wire==shared && matches!(op.writer,Writer::Map(_))=>
            Some(op.writer),_=>None}).collect::<Vec<_>>();
    assert!(consumers.contains(&Writer::Map(0))&&consumers.contains(&Writer::Map(1)));
    assert!(ledger.check_exact(&row19,&sink).is_ok());
}

#[test]
fn c358_occurrence_census_and_typed_sources_reject_isolated_faults() {
    let plan=crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(
        1_827_840,21,[17;32],[0;28]).unwrap();
    let roster=crate::daa_history_roster::DaaHistoryRoster::compile(&plan).unwrap();
    let scheduled=crate::h21_scheduled_max_cap::Plan::eligible08();
    let row_plan=crate::header_daa_row_placement::RowPlan::new(&roster,&scheduled).unwrap();
    let row19=row_plan.stage_owner(OWNER).unwrap();
    let (mut sink,source,material)=cap_occurrence_fixture_with_material();
    sink.admit_first_modern_cap_material(source,material).unwrap();
    let good=sink.occurrence_ledger_845759(&row_plan,&row19,&plan,None).unwrap();
    let before=sink.state.clone();

    let score_read=sink.state.read_obligations.iter().find(|read|
        matches!(read.consumer,Writer::Score(author) if author.context==0)
        && matches!(read.author,RequiredAuthor::PreviousR{..})).unwrap().wire;
    let score_row=sink.state.terms.iter().position(|row|
        matches!(row.writer,Writer::Score(author) if author.context==0)
        && row.term.gate.left==score_read && row.term.gate.c1==Fr::one()
        && row.term.gate.c2==-Fr::one()).unwrap();
    sink.state.terms.remove(score_row);
    assert_eq!(sink.occurrence_ledger_845759(&row_plan,&row19,&plan,None).unwrap_err(),
        "owner occurrence orphan original sink edge");
    sink.state=before.clone();

    let daa_wire=good.records.iter().find_map(|read|match read.consumer {
        ConsumerOccurrence::Row19(crate::header_daa_row_placement::ActiveOperand{
            relation:crate::header_daa_row_placement::Relation::DaaLane(3),..})
            if is_local_daa_bank_wire(read.wire)=>Some(read.wire),
        _=>None,
    }).filter(|wire|!sink.state.cells.contains_key(wire))
        .expect("active local Carry DAA BANKS wire without a sink claim");
    let equal_cap_bit=sink.state.cells.values().find_map(|(writer,bit)|
        matches!(writer,Writer::Cap(_)).then_some(*bit))
        .expect("published Cap source supplies the decoy Boolean");
    sink.state.cells.insert(daa_wire,(Writer::Slack(0),equal_cap_bit));
    let injected=sink.state.clone();
    assert_eq!(sink.occurrence_ledger_845759(&row_plan,&row19,&plan,None).unwrap_err(),
        "owner occurrence local DAA bank claim lacks native source");
    assert!(sink.state == injected,"wrong-author DAA claim rejection is non-mutating");
    sink.state=before.clone();

    let mut missing=good.clone();
    let omitted=missing.records.remove(0);
    missing.records.push(missing.records[0]);
    assert_eq!(missing.records.len(),good.records.len());
    assert_ne!(missing.records[0].consumer,omitted.consumer);
    assert_eq!(missing.check_exact(&row19,&sink).unwrap_err(),
        "owner occurrence exact ordered consumer census");
    let mut wrong_side=good.clone();
    if let ConsumerOccurrence::Row19(ref mut operand)=wrong_side.records[0].consumer {
        operand.side=match operand.side {OperandSide::Left=>OperandSide::Right,
            OperandSide::Right=>OperandSide::Left};
    }
    assert_eq!(wrong_side.check_exact(&row19,&sink).unwrap_err(),
        "owner occurrence exact ordered consumer census");
    let mut equal_bit_pair=None;
    for bit in [false,true] {
        let left=good.records.iter().enumerate().find(|(_,read)|matches!(read.consumer,
            ConsumerOccurrence::Sink(SinkOperand{side:OperandSide::Left,..}))
            && c358_known_bit(read.source)==Some(bit));
        if let Some((left_index,left_read))=left {
            let right=good.records.iter().enumerate().find(|(_,read)|matches!(read.consumer,
                ConsumerOccurrence::Sink(SinkOperand{side:OperandSide::Right,..}))
                && read.wire!=left_read.wire && c358_known_bit(read.source)==Some(bit));
            if let Some((right_index,_))=right {equal_bit_pair=Some((left_index,right_index,bit));break;}
        }
    }
    let (left_index,right_index,bit)=equal_bit_pair
        .expect("two distinct sink wires with opposite sides and an equal known bit");
    assert_eq!(c358_known_bit(good.records[left_index].source),Some(bit));
    assert_eq!(c358_known_bit(good.records[right_index].source),Some(bit));
    let mut swapped=good.clone();
    if let ConsumerOccurrence::Sink(ref mut op)=swapped.records[left_index].consumer {
        op.side=OperandSide::Right;
    } else {unreachable!();}
    if let ConsumerOccurrence::Sink(ref mut op)=swapped.records[right_index].consumer {
        op.side=OperandSide::Left;
    } else {unreachable!();}
    assert_eq!(swapped.check_exact(&row19,&sink).unwrap_err(),
        "owner occurrence exact ordered consumer census");
    assert!(sink.state == before,"side mutant cannot change admitted sink state");

    let duplicate=sink.state.read_obligations.iter().find(|read|
        read.consumer==Writer::Map(0)).unwrap().clone();
    sink.state.read_obligations.push(duplicate);
    assert_eq!(sink.occurrence_ledger_845759(&row_plan,&row19,&plan,None).unwrap_err(),
        "owner occurrence duplicate original sink edge");
    sink.state=before.clone();

    let removed=sink.state.reads.iter().position(|read|
        read.consumer==Writer::Map(0)
            && matches!(read.author,RequiredAuthor::WorkDifficulty{..})).unwrap();
    sink.state.reads.remove(removed);
    let after_removal=sink.state.clone();
    assert_eq!(sink.occurrence_ledger_845759(&row_plan,&row19,&plan,None).unwrap_err(),
        "owner occurrence resolved edge lacks source");
    assert!(sink.state == after_removal,"rejection cannot mutate the candidate sink");
    sink.state=before.clone();

    let i=sink.state.read_obligations.iter().position(|read|
        matches!(read.author,RequiredAuthor::Cap{context:0,..})).unwrap();
    sink.state.read_obligations[i].value^=true;
    assert_eq!(sink.occurrence_ledger_845759(&row_plan,&row19,&plan,None).unwrap_err(),
        "owner occurrence typed source author/value");
    sink.state=before.clone();
    sink.state.read_obligations[i].author=RequiredAuthor::WorkDifficulty{
        owner:OWNER,height:OWNER+2};
    assert_eq!(sink.occurrence_ledger_845759(&row_plan,&row19,&plan,None).unwrap_err(),
        "owner occurrence typed source author/value");
    sink.state=before.clone();

    let mut orphan=sink.state.read_obligations.iter().find(|read|
        read.consumer==Writer::Map(0)).unwrap().clone();
    orphan.wire=OWNER*WIDTH+1;
    sink.state.read_obligations.push(orphan);
    assert_eq!(sink.occurrence_ledger_845759(&row_plan,&row19,&plan,None).unwrap_err(),
        "owner occurrence orphan original sink edge");
    sink.state=before.clone();

    let cap_wire=sink.state.cells.iter().find(|(_,cell)|matches!(cell.0,Writer::Cap(0)))
        .unwrap().0.to_owned();
    sink.state.cells.get_mut(&cap_wire).unwrap().1^=true;
    assert_eq!(sink.occurrence_ledger_845759(&row_plan,&row19,&plan,None).unwrap_err(),
        "owner occurrence exact published Cap cell");
    sink.state=before.clone();

    sink.state.cells.insert(OWNER*WIDTH+987_674,(Writer::WorkLocal,false));
    assert_eq!(sink.occurrence_ledger_845759(&row_plan,&row19,&plan,None).unwrap_err(),
        "owner occurrence Work LOCAL source absent");
    sink.state=before.clone();

    let mut duplicate_physical=good.physical.clone();
    let claim=*duplicate_physical.values().next().unwrap();
    assert_eq!(insert_physical(&mut duplicate_physical,claim).unwrap_err(),
        "owner occurrence duplicate/outside physical source");
    sink.binding.root[0]^=1;
    assert_eq!(sink.occurrence_ledger_845759(&row_plan,&row19,&plan,None).unwrap_err(),
        "owner occurrence sink/ROW parent cut profile");
    sink.binding.root[0]^=1;
    assert!(sink.state == before);
}

fn material_for_cap_fixture(lease:&Eligible08OwnerLease)->(Vec<Cell>,Vec<Row>,Vec<PendingRead>) {
    material(&lease.binding,&lease.source,&lease.map_reads).unwrap()
}

fn reject_cap(sink:&mut Eligible08OwnerSink,
    source:crate::h21_scheduled_family_ledger::FirstModernCapPublication,expected:&str) {
    let before=sink.state.clone();let before_cap=sink.cap_source.is_some();
    let before_source=sink.source.clone();
    let before_work=sink.work_source.clone();
    assert_eq!(sink.admit_first_modern_cap(source).err().unwrap(),expected);
    assert!(sink.state==before);assert_eq!(sink.cap_source.is_some(),before_cap);
    assert!(sink.source==before_source);
    assert!(sink.work_source==before_work);
}

fn synthetic_cap_max_edges(binding:&Binding)->(Vec<CapMaxImport>,Vec<CapMaxReplayCell>) {
    let mut expected=Vec::with_capacity(448);
    let mut replay=Vec::with_capacity(448);
    for context in 0..2 {
        for bit in 0..CAP_MAX_BITS {
            let wire=CAP_MAX_OWNER*WIDTH+CAP_MAX_BASE[context]+bit;
            let writer=crate::h21_scheduled_max_cap::Writer::Max {context,end:CAP_MAX_OWNER+2};
            let value=Fr::from(((context+bit)%5!=0) as u64);
            expected.push((wire,writer,value));
            replay.push((wire,crate::h21_scheduled_max_cap::MaxReplayAuthor::Scheduled(writer),value));
        }
    }
    assert_eq!(binding.cut,crate::h21_scheduled_max_cap::CutDescriptor::eligible08().canonical_identity());
    (expected,replay)
}

#[test]
fn c345_synthetic_cap_max_resolution_is_exact_typed_owned_and_separate_from_source() {
    // This synthetic comparison fixture tests the sink join only. It does not
    // exercise MaxStream closure or establish native source execution.
    let (mut sink,cap)=cap_fixture();
    sink.admit_first_modern_cap(cap).unwrap();
    let (expected,replay)=synthetic_cap_max_edges(&sink.binding);
    let state=sink.state.clone();
    let cap_source=sink.cap_source.as_ref().map(|source|source as *const _);
    assert_eq!(sink.pending_cap_max_read_count(),448);
    let resolution=prepare_cap_max_resolution(&sink.binding,&expected,&replay).unwrap();
    assert_eq!(resolution.owner,CAP_MAX_OWNER);
    assert_eq!(resolution.cells.len(),448);
    assert!(resolution.cells.iter().any(|cell|cell.value.is_zero()));
    assert!(resolution.cells.iter().any(|cell|cell.value.is_one()));
    sink.state.published=false;
    assert_eq!(sink.commit_cap_max_resolution(resolution.clone()).unwrap_err(),
        "Eligible08 sink Cap MAX order/duplicate");
    assert_eq!(sink.pending_cap_max_read_count(),448);
    sink.state.published=true;
    let retained_source=sink.source.take();
    assert_eq!(sink.commit_cap_max_resolution(resolution.clone()).unwrap_err(),
        "Eligible08 sink Cap MAX order/duplicate");
    assert_eq!(sink.pending_cap_max_read_count(),448);
    sink.source=retained_source;
    let mut wrong_binding=resolution.clone();wrong_binding.binding.root[0]^=1;
    assert_eq!(sink.commit_cap_max_resolution(wrong_binding).unwrap_err(),
        "Eligible08 sink Cap MAX order/duplicate");
    assert_eq!(sink.pending_cap_max_read_count(),448);
    sink.commit_cap_max_resolution(resolution.clone()).unwrap();
    assert_eq!(sink.pending_cap_max_read_count(),0);
    assert_eq!(sink.cap_max_resolution.as_ref(),Some(&resolution));
    assert!(sink.state==state);
    assert_eq!(sink.cap_source.as_ref().map(|source|source as *const _),cap_source);
    assert_eq!(sink.commit_cap_max_resolution(resolution).unwrap_err(),
        "Eligible08 sink Cap MAX order/duplicate");
}

#[test]
fn c345_synthetic_cap_max_join_rejects_single_fault_cell_mutants() {
    // Synthetic replay tuples exercise exact comparison, not production
    // stream closure, native custody, or a global X/ROW/proof claim.
    let (sink,_)=cap_fixture();
    let (expected,replay)=synthetic_cap_max_edges(&sink.binding);
    for mutation in 0..8 {
        let mut wrong_expected=expected.clone();
        let mut wrong_replay=replay.clone();
        match mutation {
            0=>{wrong_replay.pop();},
            1=>{let duplicate=wrong_replay[0];wrong_replay.push(duplicate);},
            2=>wrong_replay[0].0+=WIDTH,
            3=>wrong_replay[0].1=crate::h21_scheduled_max_cap::MaxReplayAuthor::Scheduled(
                crate::h21_scheduled_max_cap::Writer::Max {context:1,end:CAP_MAX_OWNER+2}),
            4=>wrong_replay[0].0+=1,
            5=>wrong_replay[0].2=if wrong_replay[0].2.is_zero(){Fr::one()}else{Fr::zero()},
            6=>wrong_expected[0].1=crate::h21_scheduled_max_cap::Writer::Max {
                context:0,end:CAP_MAX_OWNER+3},
            _=>wrong_expected[0].0+=1,
        }
        assert_eq!(prepare_cap_max_resolution(&sink.binding,&wrong_expected,&wrong_replay)
            .unwrap_err(),"Eligible08 sink exact Cap MAX replay join","mutation {mutation}");
    }
}

#[test]
fn c194_full_cap_header_publication_resolves_130_score_reads_and_retains_source_dependencies() {
    let (mut sink,source)=cap_fixture();
    let duplicate=source.clone();
    assert_eq!(source.pending_max_read_count(),448);
    assert_eq!(source.pending_max_source_owners(),vec![844_670]);
    let source_material=source.checked_material().unwrap();
    assert_eq!(source_material.cells.len(),4096);
    for context in 0..2 {
        assert_eq!(source_material.rows.iter().filter(|(c,_)|*c==Some(context)).count(),6419);
        assert_eq!(source_material.q[context].iter().filter(|(_,bit)|*bit).count(),1,"D16 gives q32");
    }
    let original=sink.state.terms.clone();
    let admitted=sink.admit_first_modern_cap(source).unwrap();
    assert_eq!(admitted.cell_count(),16_384+4096);
    assert_eq!(admitted.pending_read_count(),1346);
    assert_eq!(&sink.state.terms[..original.len()],original.as_slice());
    assert_eq!(sink.pending_cap_max_read_count(),448);
    assert!(sink.pending_sources().iter().all(|read|!matches!(read.author,RequiredAuthor::Cap{..})));
    for (expected,kind) in [(448,0),(450,1),(448,2)] {
        assert_eq!(sink.pending_sources().iter().filter(|read|match kind {
            0=>matches!(read.author,RequiredAuthor::WorkDifficulty{..}),
            1=>matches!(read.author,RequiredAuthor::PreviousR{..}),
            _=>matches!(read.author,RequiredAuthor::WorkUpper{..}),
        }).count(),expected);
    }
    for context in 0..2 {
        for &(wire,value) in &source_material.q[context] {
            assert_eq!(sink.state.cells.get(&wire),Some(&(Writer::Cap(context),value)));
        }
    }
    reject_cap(&mut sink,duplicate,"Eligible08 sink Cap order/duplicate");
}

#[test]
fn c194_cap_source_mutants_are_atomic_and_context_q_bits_are_checked_separately() {
    let (mut sink,source)=cap_fixture();
    for mutation in 0..12 {
        let mut wrong=source.clone();wrong.mutate_for_test(mutation);
        let expected=match mutation {
            0..=3=>"first Cap publication parent/cut binding",
            4|6|7=>"first Cap publication exact owner/retirement/census",
            5=>"scheduled ledger exact X source",
            8..=10=>"scheduled ledger exact ROW source",
            _=>"first Cap publication exact published source",
        };
        reject_cap(&mut sink,wrong,expected);
    }
    for context in 0..2 {
        let index=sink.state.reads.iter().position(|read|
            matches!(read.author,RequiredAuthor::Cap{context:c,..} if c==context)).unwrap();
        sink.state.reads[index].value^=true;
        reject_cap(&mut sink,source.clone(),"Eligible08 sink Cap source bit/duplicate read");
        sink.state.reads[index].value^=true;
    }
    let removed=sink.state.reads.remove(sink.state.reads.iter().position(|read|
        matches!(read.author,RequiredAuthor::Cap{context:1,..})).unwrap());
    reject_cap(&mut sink,source.clone(),"Eligible08 sink Cap exact 130-read census");
    sink.state.reads.push(removed.clone());sink.state.reads.push(removed);
    reject_cap(&mut sink,source,"Eligible08 sink Cap source bit/duplicate read");
}

#[test]
fn c194_cap_header_cross_writer_collisions_and_x_overlap_reject_before_publication() {
    let (mut sink,source)=cap_fixture();
    let material=source.checked_material().unwrap();
    for writer in [Writer::Map(0),Writer::Score(ScoreReplayAuthor{context:1,origin:OWNER+1,
        previous_owner:OWNER-1,max_owner:844_670,cap_owner:OWNER}),Writer::Slack(1)] {
        for context in [None,Some(0),Some(1)] {
            let target=material.rows.iter().find(|(c,_)|*c==context).unwrap().1.row;
            sink.state.rows.insert(target,writer);
            reject_cap(&mut sink,source.clone(),"Eligible08 sink Cap/HEADER ROW overlap/owner");
            sink.state.rows.remove(&target);
        }
    }
    let wire=material.cells[0].0;sink.state.cells.insert(wire,(Writer::Header,false));
    reject_cap(&mut sink,source,"Eligible08 sink Cap duplicate X/owner");
}

/// Structural join material only. The native-shaped parent and canonical local
/// terms do not make these zero operands a native packed assignment. Production
/// source custody is checked by c195 and the separately gated native run.
fn structural_work_source() -> WorkLocalPublication {
    use std::sync::OnceLock;
    static SOURCE: OnceLock<WorkLocalPublication> = OnceLock::new();
    SOURCE.get_or_init(|| {
        use blake2::{digest::consts::U32, Blake2b, Digest};
        let mut bytes = crate::work_tree_fixed_hash::PROFILE_PREFIX.to_vec();
        bytes.extend_from_slice(&crate::header_order::MAINNET_GENESIS);
        let profile = Blake2b::<U32>::digest(bytes).into();
        let snapshot = crate::h21_scheduled_max_cap::Eligible08NativeSnapshot::constant_d_for_test(
            [17; 32], [0; 28], profile, 16).unwrap();
        let plan = crate::work_tree_history_plan::WorkTreeHistoryPlan::compile(
            1_827_840, 21, [17; 32], [0; 28]).unwrap();
        WorkLocalPublication {parent: snapshot.parent(), owner: OWNER, height: OWNER + 2,
            terms: crate::h21_work_local_source::canonical_terms(&plan, OWNER).unwrap(),
            operands: crate::h21_work_local_source::operand_domain(OWNER).unwrap()
                .into_iter().map(|wire| (wire, Fr::zero())).collect(),
            d: (0..224).map(|bit| (OWNER * WIDTH + crate::legacy_envelope_map::D_LOCAL + bit,
                Fr::zero())).collect()}
    }).clone()
}

fn reject_work(sink: &mut Eligible08OwnerSink, binding: &Binding,
    parent: &crate::h21_scheduled_max_cap::NativeParent, source: WorkLocalPublication,
    expected: &str) {
    let before = sink.state.clone(); let before_source = sink.source.clone();
    let before_work = sink.work_source.clone();
    let before_cap = sink.cap_source.as_ref().map(|source| source as *const _);
    assert_eq!(sink.admit_work_local(binding, parent, source).err().unwrap(), expected);
    assert!(sink.state == before); assert!(sink.source == before_source);
    assert!(sink.work_source == before_work);
    assert_eq!(sink.cap_source.as_ref().map(|source| source as *const _), before_cap);
}

#[test]
fn c198_structural_work_join_resolves_both_maps_retains_local_custody_and_row19() {
    let (mut sink, _) = cap_fixture(); let mut source = structural_work_source();
    // Both true and false bits, including all leading zero bits, are owned.
    for (bit, (wire, value)) in source.d.iter_mut().enumerate() {
        *value = Fr::from((bit % 3 == 1) as u64);
        source.operands.iter_mut().find(|(w, _)| w == wire).unwrap().1 = *value;
        for read in sink.state.reads.iter_mut().filter(|r|
            matches!(r.author, RequiredAuthor::WorkDifficulty {..}) && r.wire == *wire) {
            read.value = value.is_one();
        }
    }
    let before = sink.state.clone(); let original_source = sink.source.clone();
    let expected = source.clone(); let binding = sink.binding.clone(); let parent = source.parent.clone();
    let admitted = sink.admit_work_local(&binding, &parent, source).unwrap();
    assert_eq!((admitted.cell_count(), admitted.pending_read_count()), (16_608, 1_028));
    assert_eq!(admitted.term_count(), before.terms.len());
    assert_eq!(sink.retained_work_local_counts(), (3265, 1184));
    assert!(sink.work_source.as_ref() == Some(&expected));
    assert!(sink.source == original_source);
    assert!(sink.state.rows == before.rows); assert_eq!(sink.state.terms, before.terms);
    for (wire, cell) in before.cells {assert_eq!(sink.state.cells.get(&wire), Some(&cell));}
    let remaining: Vec<_> = before.reads.into_iter().filter(|read|
        !matches!(read.author, RequiredAuthor::WorkDifficulty {..})).collect();
    assert_eq!(sink.state.reads, remaining);
    for &(wire, value) in &expected.d {
        assert_eq!(sink.state.cells.get(&wire), Some(&(Writer::WorkLocal, value.is_one())));
    }
    reject_work(&mut sink, &binding, &parent, expected, "Eligible08 sink Work order/duplicate");
}

#[test]
fn c198_structural_work_destination_parent_and_material_mutants_are_atomic_then_retry() {
    let (mut sink, _) = cap_fixture(); let source = structural_work_source();
    let parent = source.parent.clone(); let binding = sink.binding.clone();
    for mutation in 0..6 {
        let mut wrong = binding.clone();
        match mutation {0 => wrong.root[0] ^= 1, 1 => wrong.total[0] ^= 1,
            2 => wrong.profile[0] ^= 1, 3 => wrong.cut.push(0),
            4 => wrong.maps[0].e += 1, 5 => wrong.maps[1].e += 1, _ => unreachable!()}
        reject_work(&mut sink, &wrong, &parent, source.clone(), "Eligible08 sink Work full context binding");
    }
    for mutation in 0..5 {
        let mut wrong = source.clone();
        match mutation {0 => wrong.parent = parent.different_cut_for_test(),
            1 => wrong.owner -= 1, 2 => wrong.height -= 1,
            3 => {wrong.terms.pop();}, 4 => {wrong.operands.pop();}, _ => unreachable!()}
        reject_work(&mut sink, &binding, &parent, wrong,
            "Eligible08 sink Work native parent/owner/height/material");
    }
    let mut empty = Eligible08OwnerSink {binding: binding.clone(), state: State::default(),
        custody: std::sync::Arc::new(()),
        source: None, cap_source: None, cap_max_resolution: None, work_source: None,
        upper_source: None, previous_r_source: None};
    reject_work(&mut empty, &binding, &parent, source.clone(), "Eligible08 sink Work order/duplicate");
    assert_eq!(sink.admit_work_local(&binding, &parent, source).unwrap().pending_read_count(), 1028);
}

#[test]
fn c198_structural_work_exact_read_context_wire_bit_census_rejects_and_retries() {
    let (mut sink, _) = cap_fixture(); let source = structural_work_source();
    let parent = source.parent.clone(); let binding = sink.binding.clone();
    for context in 0..2 {
        for mutation in 0..8 {
            let original = sink.state.reads.clone();
            let index = sink.state.reads.iter().position(|read|
                read.consumer == Writer::Map(context)
                    && matches!(read.author, RequiredAuthor::WorkDifficulty {..})).unwrap();
            let expected = match mutation {
                0 => {sink.state.reads[index].value ^= true; "Eligible08 sink Work source bit/duplicate read"},
                1 => {sink.state.reads[index].wire -= 1; "Eligible08 sink Work exact read domain"},
                2 => {sink.state.reads.remove(index); "Eligible08 sink Work exact 448-read census"},
                3 => {sink.state.reads.push(sink.state.reads[index].clone()); "Eligible08 sink Work source bit/duplicate read"},
                4 => {sink.state.reads[index].consumer = Writer::Map(1 - context); "Eligible08 sink Work source bit/duplicate read"},
                5 => {sink.state.reads[index].consumer = Writer::Map(2); "Eligible08 sink Work Map consumer context"},
                6 => {sink.state.reads[index].author = RequiredAuthor::WorkDifficulty {owner: OWNER - 1, height: OWNER + 2};
                    "Eligible08 sink Work exact typed source"},
                7 => {sink.state.reads[index].author = RequiredAuthor::WorkDifficulty {owner: OWNER, height: OWNER + 1};
                    "Eligible08 sink Work exact typed source"}, _ => unreachable!(),
            };
            reject_work(&mut sink, &binding, &parent, source.clone(), expected);
            sink.state.reads = original;
        }
    }
    assert_eq!(sink.admit_work_local(&binding, &parent, source).unwrap().pending_read_count(), 1028);
}

#[test]
fn c198_structural_work_d_material_and_owned_x_overlap_fail_before_publication() {
    let (mut sink, _) = cap_fixture(); let source = structural_work_source();
    let parent = source.parent.clone(); let binding = sink.binding.clone();
    for mutation in 0..6 {
        let mut wrong = source.clone();
        let expected = match mutation {
            0 => {wrong.d[0].1 = Fr::one(); "Eligible08 sink Work exact D wire/value/operand"},
            1 => {wrong.d[0].0 += 1; "Eligible08 sink Work exact D wire/value/operand"},
            2 => {wrong.d.pop(); "Eligible08 sink Work exact D census"},
            3 => {wrong.d.push(wrong.d[0]); "Eligible08 sink Work exact D census"},
            4 => {wrong.d[0].1 = Fr::from(2u64); "Eligible08 sink Work exact D wire/value/operand"},
            5 => {wrong.d[1] = wrong.d[0]; "Eligible08 sink Work exact D wire/value/operand"},
            _ => unreachable!(),
        };
        reject_work(&mut sink, &binding, &parent, wrong, expected);
    }
    let wire = source.d[0].0; sink.state.cells.insert(wire, (Writer::Header, false));
    reject_work(&mut sink, &binding, &parent, source.clone(), "Eligible08 sink Work duplicate X");
    sink.state.cells.remove(&wire);
    assert_eq!(sink.admit_work_local(&binding, &parent, source).unwrap().cell_count(), 16_608);
}

#[test]
fn c198_structural_cap_and_work_compose_in_both_orders_and_keep_sibling_custody() {
    let (mut left, cap) = cap_fixture(); let (mut right, _) = cap_fixture();
    let work = structural_work_source(); let parent = work.parent.clone(); let binding = left.binding.clone();
    left.admit_work_local(&binding, &parent, work.clone()).unwrap();
    let admitted = left.admit_first_modern_cap(cap.clone()).unwrap();
    assert_eq!((admitted.cell_count(), admitted.pending_read_count()), (20_704, 898));
    right.admit_first_modern_cap(cap.clone()).unwrap();
    let mut wrong = work.clone(); wrong.parent = parent.different_cut_for_test();
    reject_work(&mut right, &binding, &parent, wrong,
        "Eligible08 sink Work native parent/owner/height/material");
    assert_eq!(right.admit_work_local(&binding, &parent, work.clone()).unwrap().pending_read_count(), 898);
    assert!(left.state == right.state); assert!(left.work_source == right.work_source);
    assert_eq!(left.retained_work_local_counts(), (3265, 1184));
    assert_eq!(left.pending_cap_max_read_count(), 448);
    assert_eq!(right.pending_cap_max_read_count(), 448);
    reject_cap(&mut left, cap, "Eligible08 sink Cap order/duplicate");
    reject_work(&mut right, &binding, &parent, work, "Eligible08 sink Work order/duplicate");
}

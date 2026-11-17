//! Internal checkpoint-aware role4 source and opaque GKR handoff.
//! This module admits no public statement, PCS key or common-X authentication.

use ark_bn254::Fr;
use ark_ff::{One, Zero};
use crate::{daa_history_roster::DaaHistoryRoster,
    historical_prefix_height_work::HeightWork,
    gkr::InputClaim, sparse::Term, transcript::Transcript,
    work_tree_history_plan::WorkTreeHistoryPlan};

pub(crate) fn check_term(row_log:usize,input_log:usize,t:&Term)->Result<(),String> {
    let rows=1usize.checked_shl(row_log as u32).ok_or("row domain overflow")?;
    let inputs=1usize.checked_shl(input_log as u32).ok_or("input domain overflow")?;
    if t.row>=rows || t.gate.left>=inputs || t.gate.right>=inputs {return Err("emitted term outside role domain".into());}Ok(())
}
/// Same source-derived composition for the complete S2 reference and S12 plan.
pub(crate) fn composite_coefficients(height:&HeightWork<'_>,daa:&DaaHistoryRoster<'_>,
    r:&[Fr],u:&[Fr],v:&[Fr])->Result<[Fr;4],String> {
    let hr=height.row_log();let dr=daa.row_log();let input=height.input_log();
    if height.slots()!=1usize<<daa.slot_log() || dr!=19+daa.slot_log() || hr!=6+daa.slot_log()
        || daa.input_log()!=input || r.len()!=dr+1 || u.len()!=input || v.len()!=input {return Err("height/DAA composite dimension mismatch".into());}
    let h=height.coefficients(&r[..hr],u,v)?;let d=daa.coefficients(&r[..dr],u,v)?;
    let mask=composite_height_mask(daa.slot_log(),r)?;
    Ok(std::array::from_fn(|i|mask*h[i]+r[dr]*d[i]))
}
pub(crate) fn composite_height_mask(slot_log:usize,r:&[Fr])->Result<Fr,String> {
    if r.len()!=20usize.checked_add(slot_log).ok_or("height composite mask dimensions")? {
        return Err("height composite mask dimensions".into());
    }
    let hr=6+slot_log;let dr=19+slot_log;
    Ok((Fr::one()-r[dr])*r[hr..dr].iter().fold(Fr::one(),|a,x|a*(Fr::one()-x)))
}
pub(crate) fn visit_composite_owner(height:&HeightWork<'_>,daa:&DaaHistoryRoster<'_>,owner:u64,
    mut sink:impl FnMut(Term)->Result<(),String>)->Result<(),String> {
    let dr=daa.row_log();
    if height.slots()!=1usize<<daa.slot_log() || height.input_log()!=daa.input_log()
        || owner>=height.slots() as u64 {return Err("composite owner/parent geometry".into());}
    height.visit_owner_terms(owner,|t|{check_term(height.row_log(),height.input_log(),&t)?;sink(t)})?;
    let base=1usize.checked_shl(dr as u32).ok_or("DAA composite base overflow")?;
    daa.visit_owner_terms(owner,|mut t|{check_term(dr,daa.input_log(),&t)?;
        t.row=t.row.checked_add(base).ok_or("DAA composite row overflow")?;
        check_term(dr+1,daa.input_log(),&t)?;sink(t)})?;Ok(())
}

/// Closed internal identity. It cannot widen Selection::s12 or public S.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct CheckpointRole4Binding {
    pub(crate) tag: &'static str,
    pub(crate) parent_object: usize,
    pub(crate) checkpoint: crate::checkpoint_output_layout::CheckpointRole4Descriptor,
}

pub(crate) struct CheckpointRole4Adapter<'a> {
    height: HeightWork<'a>,
    daa: DaaHistoryRoster<'a>,
    lane: crate::checkpoint_output_layout::CheckpointRole4Lane<'a>,
    descriptor: CheckpointRole4Binding,
}

impl<'a> CheckpointRole4Adapter<'a> {
    /// h is an expected verifier input, never taken from a prover descriptor.
    pub(crate) fn new(parent: &'a WorkTreeHistoryPlan, h: u64,
        public: crate::checkpoint_output_layout::CheckpointPublic) -> Result<Self, String>
    {
        let lane = crate::checkpoint_output_layout::CheckpointRole4Lane::new(parent, h, public)?;
        let height = HeightWork::compile_history(parent)?;
        let daa = DaaHistoryRoster::compile(parent)?;
        HistoricalRole4Endpoints::new(&height, &daa)?;
        let descriptor = CheckpointRole4Binding {
            tag: "role4-height-daa-checkpoint-internal-k64-v1",
            parent_object: parent as *const _ as usize, checkpoint: lane.descriptor() };
        Ok(Self { height, daa, lane, descriptor })
    }

    fn descriptor(&self) -> CheckpointRole4Binding { self.descriptor.clone() }

    /// Bind the adapter to verifier-owned checkpoint coordinates before any
    /// transcript, source, or terminal operation can run.
    pub(crate) fn admit_query<'r>(&'r self, expected_hf: (u64, u64))
        -> Result<AdmittedCheckpointRole4<'r, 'a>, String>
    {
        let actual_hf = (self.descriptor.checkpoint.h, self.descriptor.checkpoint.f);
        if !checkpoint_query_matches(expected_hf, actual_hf) {
            return Err("checkpoint role4 verifier query tuple mismatch".into());
        }
        Ok(AdmittedCheckpointRole4 { adapter: self, expected_hf })
    }

    fn validate_descriptor(&self, requested: &CheckpointRole4Binding) -> Result<(), String> {
        if requested != &self.descriptor { return Err("diagnostic checkpoint role4 descriptor mismatch".into()); }
        self.lane.validate_descriptor(&requested.checkpoint)
    }

    fn bind(&self, requested: &CheckpointRole4Binding, t: &mut Transcript)
        -> Result<(), String>
    {
        self.validate_descriptor(requested)?;
        if t.challenges() != 0 { return Err("diagnostic checkpoint role4 binding after challenge".into()); }
        t.append_bytes(b"diagnostic-checkpoint-role4", self.descriptor.tag.as_bytes());
        t.append_bytes(b"diagnostic-checkpoint-role4-order", b"height+numeric;daa;checkpoint");
        self.height.bind(t); self.daa.bind(t); self.lane.bind(t)
    }

    fn coefficients(&self, requested: &CheckpointRole4Binding,
        r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String>
    {
        self.validate_descriptor(requested)?;
        let old = composite_coefficients(&self.height, &self.daa, r, u, v)?;
        let extra = self.lane.coefficients(r, u, v)?;
        Ok(std::array::from_fn(|i| old[i] + extra[i]))
    }

    fn visit_owner_terms(&self, requested: &CheckpointRole4Binding, owner: usize,
        mut sink: impl FnMut(Term) -> Result<(), String>) -> Result<usize, String>
    {
        self.validate_descriptor(requested)?;
        if owner >= self.height.slots() { return Err("diagnostic checkpoint role4 row owner".into()); }
        let d = &self.descriptor.checkpoint;
        let mut count = 0usize;
        let mut checked = |term: Term| {
            check_term(d.row_log, d.input_log, &term)?;
            sink(term)?; count = count.checked_add(1).ok_or("diagnostic checkpoint role4 count")?; Ok(())
        };
        visit_composite_owner(&self.height, &self.daa, owner as u64, &mut checked)?;
        self.lane.visit_owner_terms(d, owner, checked)?;
        Ok(count)
    }

    fn visit_endpoint(&self, requested: &CheckpointRole4Binding, left: bool, owner: usize,
        mut sink: impl FnMut(crate::sparse_stream_roster::EdgeTerm) -> Result<(), String>)
        -> Result<usize, String>
    {
        self.validate_descriptor(requested)?;
        if owner >= self.height.slots() { return Err("diagnostic checkpoint role4 endpoint owner".into()); }
        let old = HistoricalRole4Endpoints::new(&self.height, &self.daa)?.visit(left, owner, &mut sink)?.total()?;
        let extra = self.lane.visit_endpoint(&requested.checkpoint, left, owner, sink)?;
        old.checked_add(extra).ok_or_else(|| "diagnostic checkpoint role4 endpoint count".into())
    }

}

fn checkpoint_query_matches(expected_hf: (u64, u64), actual_hf: (u64, u64)) -> bool {
    expected_hf == actual_hf
}

/// A query tuple admitted by the verifier-owned caller. Effectful role-4
/// operations are exposed only through this wrapper, which keeps the external
/// expected tuple separate from the adapter's self-description.
pub(crate) struct AdmittedCheckpointRole4<'r, 'p> {
    adapter: &'r CheckpointRole4Adapter<'p>,
    expected_hf: (u64, u64),
}

impl<'r, 'p> AdmittedCheckpointRole4<'r, 'p> {
    pub(crate) fn descriptor(&self) -> CheckpointRole4Binding { self.adapter.descriptor() }

    fn ensure_query(&self) -> Result<(), String> {
        if !checkpoint_query_matches(self.expected_hf,
            (self.adapter.descriptor.checkpoint.h, self.adapter.descriptor.checkpoint.f)) {
            return Err("checkpoint role4 verifier query tuple mismatch".into());
        }
        Ok(())
    }

    pub(crate) fn bind(&self, requested: &CheckpointRole4Binding, t: &mut Transcript)
        -> Result<(), String>
    {
        self.ensure_query()?;
        self.adapter.bind(requested, t)
    }

    pub(crate) fn coefficients(&self, requested: &CheckpointRole4Binding,
        r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr; 4], String>
    {
        self.ensure_query()?;
        self.adapter.coefficients(requested, r, u, v)
    }

    pub(crate) fn visit_owner_terms(&self, requested: &CheckpointRole4Binding, owner: usize,
        sink: impl FnMut(Term) -> Result<(), String>) -> Result<usize, String>
    {
        self.ensure_query()?;
        self.adapter.visit_owner_terms(requested, owner, sink)
    }

    pub(crate) fn visit_endpoint(&self, requested: &CheckpointRole4Binding, left: bool, owner: usize,
        sink: impl FnMut(crate::sparse_stream_roster::EdgeTerm) -> Result<(), String>)
        -> Result<usize, String>
    {
        self.ensure_query()?;
        self.adapter.visit_endpoint(requested, left, owner, sink)
    }

    /// Freeze the complete caller prefix and relation before any challenge.
    /// The admitted verifier tuple has already been checked before binding.
    pub(crate) fn bind_consumer(&self, requested: &CheckpointRole4Binding, prefix: &Transcript)
        -> Result<BoundCheckpointRole4<'_, 'p>, String>
    {
        self.ensure_query()?;
        let mut transcript = prefix.clone();
        self.bind(requested, &mut transcript)?;
        Ok(BoundCheckpointRole4 { relation: self.adapter, expected_hf: self.expected_hf, transcript })
    }
}


#[cfg(test)]
mod checkpoint_role4_internal_tests {
    use super::*;
    use ark_ff::Field;
    use std::sync::OnceLock;

    fn parent() -> &'static WorkTreeHistoryPlan {
        static PARENT: OnceLock<WorkTreeHistoryPlan> = OnceLock::new();
        PARENT.get_or_init(|| {
            let mut total = [0; 28]; total[27] = 9;
            WorkTreeHistoryPlan::compile(66, 7, [7; 32], total).unwrap()
        })
    }
    fn public() -> crate::checkpoint_output_layout::CheckpointPublic {
        let mut header = crate::historical_prefix_witness::retained_headers().unwrap()[1].clone();
        header.height = 2;
        let mut floor_work = [0; 28]; floor_work[27] = 3;
        let mut audit_work = [0; 28]; audit_work[27] = 6;
        crate::checkpoint_output_layout::CheckpointPublic { raw: header.encode().unwrap(), floor_work, audit_work }
    }
    fn adapter() -> &'static CheckpointRole4Adapter<'static> {
        static RELATION: OnceLock<CheckpointRole4Adapter<'static>> = OnceLock::new();
        RELATION.get_or_init(|| CheckpointRole4Adapter::new(parent(), 2, public()).unwrap())
    }
    fn relation() -> &'static AdmittedCheckpointRole4<'static, 'static> {
        static RELATION: OnceLock<AdmittedCheckpointRole4<'static, 'static>> = OnceLock::new();
        RELATION.get_or_init(|| adapter().admit_query((2, 65)).unwrap())
    }
    fn point(log: usize, index: usize) -> Vec<Fr> {
        (0..log).map(|b| Fr::from(((index >> b) & 1) as u64)).collect()
    }

    #[test]
    fn checkpoint_role4_internal_closed_requests_precede_every_effect() {
        let raw_adapter = adapter();
        let relation = raw_adapter.admit_query((2, 65)).unwrap(); let d = relation.descriptor();
        for field in 0..15 {
            let mut wrong = d.clone();
            match field { 0 => wrong.tag = "other", 1 => wrong.parent_object ^= 1,
                2 => wrong.checkpoint.h += 1, 3 => wrong.checkpoint.f += 1,
                4 => wrong.checkpoint.depth = 1, 5 => wrong.checkpoint.base += 8192,
                6 => wrong.checkpoint.live_rows -= 1, 7 => wrong.checkpoint.map_fingerprint.push('x'),
                8 => wrong.checkpoint.headers += 1, 9 => wrong.checkpoint.input_log += 1,
                10 => wrong.checkpoint.row_log += 1, 11 => wrong.checkpoint.root[0] ^= 1,
                12 => wrong.checkpoint.total[27] ^= 1, 13 => wrong.checkpoint.public_fingerprint.push('x'),
                _ => wrong.checkpoint.slot_log += 1 }
            let mut prefix = Transcript::new(b"c201-internal-boundary");
            let before = (prefix.bytes_absorbed(), prefix.challenges(), prefix.raw_queries());
            assert!(relation.bind(&wrong, &mut prefix).unwrap_err().contains("descriptor mismatch"));
            assert!(relation.bind_consumer(&wrong, &prefix).is_err());
            let mut calls = 0;
            assert!(relation.visit_owner_terms(&wrong, 0, |_| { calls += 1; Ok(()) }).is_err());
            assert!(relation.visit_endpoint(&wrong, true, 1, |_| { calls += 1; Ok(()) }).is_err());
            assert!(relation.coefficients(&wrong, &point(27, 0), &point(27, 0), &point(27, 0)).is_err());
            assert_eq!(calls, 0);
            assert_eq!((prefix.bytes_absorbed(), prefix.challenges(), prefix.raw_queries()), before);
        }
        let mut late = Transcript::new(b"c201-internal-boundary"); late.challenge_scalar(b"prior");
        let before = (late.bytes_absorbed(), late.challenges(), late.raw_queries());
        assert!(relation.bind_consumer(&d, &late).is_err());
        assert_eq!((late.bytes_absorbed(), late.challenges(), late.raw_queries()), before);
        assert!(CheckpointRole4Adapter::new(parent(), 3, public()).err().unwrap().contains("immature"));
        let mut wrong_raw = public();
        let mut header = ergo_header_core::Header::decode(&wrong_raw.raw, None).unwrap(); header.height = 3;
        wrong_raw.raw = header.encode().unwrap();
        assert!(CheckpointRole4Adapter::new(parent(), 2, wrong_raw).err().unwrap().contains("height differs"));
        let mut wrong_audit = public(); wrong_audit.audit_work[27] ^= 1;
        assert!(CheckpointRole4Adapter::new(parent(), 2, wrong_audit).err().unwrap().contains("supplied audit work"));
        for left in [true, false] {
            let mut calls = 0;
            assert!(relation.visit_endpoint(&d, left, 128, |_| { calls += 1; Ok(()) }).is_err());
            assert_eq!(calls, 0);
        }
    }

    #[test]
    fn verifier_query_tuple_gates_adapter_before_effects_and_mutant_bypasses_gate() {
        let adapter = adapter();
        let a = (1_810_842, 1_810_905);
        let b = (1_810_841, 1_810_904);
        assert!(checkpoint_query_matches(a, a));
        assert!(!checkpoint_query_matches(b, a));

        let expected = (2, 65);
        let requested = (3, 66);
        assert!(adapter.admit_query(expected).is_ok());
        let before = Transcript::new(b"role4-query-boundary");
        let before_state = (before.bytes_absorbed(), before.challenges(), before.raw_queries());
        assert!(adapter.admit_query(requested).err().unwrap().contains("verifier query tuple mismatch"));
        assert!(adapter.admit_query(requested).is_err());

        // Isolated omitted-comparison mutant: the old self-descriptor check
        // passes and binds the transcript. This demonstrates only that the
        // missing external tuple check is observable at this boundary.
        let descriptor = adapter.descriptor();
        let mut mutant_transcript = before.clone();
        adapter.bind(&descriptor, &mut mutant_transcript).unwrap();
        assert_ne!((mutant_transcript.bytes_absorbed(), mutant_transcript.challenges(),
            mutant_transcript.raw_queries()), before_state);

        let admitted = adapter.admit_query(expected).unwrap();
        let mut prefix = Transcript::new(b"role4-query-boundary");
        let unchanged = (prefix.bytes_absorbed(), prefix.challenges(), prefix.raw_queries());
        let mismatched_wrapper = AdmittedCheckpointRole4 { adapter, expected_hf: requested };
        assert!(mismatched_wrapper.bind_consumer(&descriptor, &prefix).is_err());
        assert!(mismatched_wrapper.coefficients(&descriptor, &[], &[], &[])
            .err().unwrap().contains("verifier query tuple mismatch"));
        let mut source_calls = 0;
        assert!(mismatched_wrapper.visit_owner_terms(&descriptor, 0, |_| {
            source_calls += 1; Ok(())
        }).is_err());
        assert!(mismatched_wrapper.visit_endpoint(&descriptor, true, 0, |_| {
            source_calls += 1; Ok(())
        }).is_err());
        assert_eq!(source_calls, 0);
        assert_eq!((prefix.bytes_absorbed(), prefix.challenges(), prefix.raw_queries()), unchanged);
        let mismatched_bound = BoundCheckpointRole4 {
            relation: adapter, expected_hf: requested, transcript: prefix.clone(),
        };
        assert!(mismatched_bound.verify_gkr(&[]).err().unwrap()
            .contains("verifier query tuple mismatch"));
        let context = admitted.bind_consumer(&descriptor, &prefix).unwrap();
        let token = context.verify_gkr(&terminal_fixture(&context)).unwrap();
        let mut consumer_calls = 0;
        assert!(mismatched_bound.consume(token, |_, _| {
            consumer_calls += 1; Ok(())
        }).err().unwrap().contains("verifier query tuple mismatch"));
        assert_eq!(consumer_calls, 0);
        assert_eq!(context.relation.descriptor.checkpoint.h, expected.0);
        assert_eq!(context.relation.descriptor.checkpoint.f, expected.1);
    }

    /// A terminal-equation fixture, deliberately without a committed witness.
    /// This exercises the internal token handoff, not PCS authentication.
    fn terminal_fixture(context: &BoundCheckpointRole4<'_, '_>) -> Vec<u8> {
        let descriptor = context.relation.descriptor();
        let n = descriptor.checkpoint.input_log;
        let mut transcript = context.producer_transcript();
        let r = crate::gkr::output_point(1 << n, &mut transcript);
        crate::gkr::append_usize(&mut transcript, b"gkr-layer-index", 0);
        let rounds = vec![vec![Fr::zero(); 3]; 2 * n];
        let mut challenges = Vec::new();
        for round in &rounds {
            crate::gkr::append_polynomial(&mut transcript, b"gkr-sumcheck-polynomial", round);
            challenges.push(transcript.challenge_scalar(b"gkr-sumcheck-challenge"));
        }
        let (u, v) = challenges.split_at(n);
        let c = context.relation.coefficients(&descriptor, &r, u, v).unwrap();
        let a = -c[0] * c[1].inverse().expect("fixture c1 nonzero");
        let mut line = vec![Fr::zero(); n + 1]; line[0] = a; line[1] = -a;
        crate::gkr::encode_proof(&crate::gkr::GkrProof { layers: vec![crate::gkr::LayerProof {
            rounds, left_value: a, right_value: Fr::zero(), line_coefficients: line }] }).unwrap()
    }

    #[test]
    fn checkpoint_role4_internal_opaque_consumer_uses_bound_wiring_and_context() {
        let relation = relation(); let d = relation.descriptor();
        let prefix = Transcript::new(b"c201-internal-boundary");
        let context = relation.bind_consumer(&d, &prefix).unwrap();
        let other = relation.bind_consumer(&d, &prefix).unwrap();
        let proof = terminal_fixture(&context);
        let token = context.verify_gkr(&proof).unwrap();
        let expected = token.claim.clone(); let continuation = token.transcript.clone();
        let mut effects = 0;
        assert!(other.consume(token, |_, _| { effects += 1; Ok(()) }).unwrap_err().contains("claim context"));
        assert_eq!(effects, 0);
        let token = context.verify_gkr(&proof).unwrap();
        context.consume(token, |claim, mut transcript| {
            assert_eq!(claim, expected);
            let mut continuation = continuation.clone();
            assert_eq!(transcript.challenge_scalar(b"continued"), continuation.challenge_scalar(b"continued"));
            effects += 1; Ok(())
        }).unwrap();
        assert_eq!(effects, 1);
        let mut changed_prefix = prefix.clone(); changed_prefix.append_bytes(b"shared-X", b"different");
        let changed = relation.bind_consumer(&d, &changed_prefix).unwrap();
        assert!(changed.verify_gkr(&proof).is_err());
        let mut padded = proof.clone(); padded.push(0); assert!(context.verify_gkr(&padded).is_err());
        let mut bad = crate::gkr::decode_dimensions(&[27], &proof).unwrap();
        bad.layers[0].left_value += Fr::one();
        assert!(context.verify_gkr(&crate::gkr::encode_proof(&bad).unwrap()).is_err());
        for (left, owner) in [(true, 1), (true, 63), (false, 1)] {
            let mut actual = Vec::new();
            relation.visit_endpoint(&d, left, owner, |edge| { actual.push(edge.term); Ok(()) }).unwrap();
            let mut expected = Vec::new();
            HistoricalRole4Endpoints::new(&relation.adapter.height, &relation.adapter.daa).unwrap()
                .visit(left, owner, |edge| { expected.push(edge.term); Ok(()) }).unwrap();
            relation.adapter.lane.visit_endpoint(&d.checkpoint, left, owner, |edge| { expected.push(edge.term); Ok(()) }).unwrap();
            assert_eq!(actual, expected);
            assert!(actual.iter().all(|term| if left { term.gate.left >> 20 == owner } else { term.gate.right >> 20 == owner }));
        }
        // The lane's padding contributes no term or coefficient; old role4 is unchanged.
        let r = point(27, d.checkpoint.base + d.checkpoint.live_rows);
        let u = point(27, 0); let v = point(27, 0);
        assert_eq!(relation.coefficients(&d, &r, &u, &v).unwrap(),
            composite_coefficients(&relation.adapter.height, &relation.adapter.daa, &r, &u, &v).unwrap());
    }
}

/// An internal GKR boundary only. No PCS/key or public-statement admission.
pub(crate) struct BoundCheckpointRole4<'a, 'p> {
    relation: &'a CheckpointRole4Adapter<'p>,
    expected_hf: (u64, u64),
    transcript: Transcript,
}

/// Only fresh verification can construct this token. Its claim and continued
/// transcript remain private until the exact bound consumer consumes it.
pub(crate) struct CheckpointRole4Claim<'a, 'r, 'p> {
    context: &'a BoundCheckpointRole4<'r, 'p>,
    claim: InputClaim,
    transcript: Transcript,
}

impl<'r, 'p> BoundCheckpointRole4<'r, 'p> {
    pub(crate) fn producer_transcript(&self) -> Transcript { self.transcript.clone() }

    pub(crate) fn verify_gkr(&self, bytes: &[u8]) -> Result<CheckpointRole4Claim<'_, 'r, 'p>, String> {
        let d = &self.relation.descriptor.checkpoint;
        if !checkpoint_query_matches(self.expected_hf, (d.h, d.f)) {
            return Err("checkpoint role4 verifier query tuple mismatch".into());
        }
        let proof = crate::gkr::decode_dimensions(&[d.input_log], bytes)?;
        if crate::gkr::encode_proof(&proof)? != bytes {
            return Err("internal checkpoint role4 noncanonical proof".into());
        }
        let mut transcript = self.transcript.clone();
        let requests = std::cell::Cell::new(0usize);
        let claim = crate::gkr::verify_with_wiring(&[d.input_log], 1usize << d.row_log,
            &proof, &mut transcript, |_| {}, |layer, r, u, v| {
                if layer != 0 { return Err(crate::gkr::GkrError::PointDimension); }
                requests.set(requests.get() + 1);
                self.relation.coefficients(&self.relation.descriptor, r, u, v)
                    .map_err(|_| crate::gkr::GkrError::TerminalExpression)
            }).map_err(|e| e.to_string())?;
        if requests.get() != 1 || claim.point.len() != d.input_log {
            return Err("internal checkpoint role4 wiring closure".into());
        }
        Ok(CheckpointRole4Claim { context: self, claim, transcript })
    }

    /// The next internal stage receives the GKR-derived point, value and
    /// continuation together. It must authenticate them to the shared X.
    pub(crate) fn consume<R>(&self, token: CheckpointRole4Claim<'_, 'r, 'p>,
        next: impl FnOnce(InputClaim, Transcript) -> Result<R, String>) -> Result<R, String>
    {
        let d = &self.relation.descriptor.checkpoint;
        if !checkpoint_query_matches(self.expected_hf, (d.h, d.f)) {
            return Err("checkpoint role4 verifier query tuple mismatch".into());
        }
        if !std::ptr::eq(self, token.context) {
            return Err("internal checkpoint role4 claim context".into());
        }
        next(token.claim, token.transcript)
    }
}

/// Separate historical source capability; it does not widen any legacy scope.
pub(crate) struct HistoricalRole4Endpoints<'a,'p> {
    height: &'a HeightWork<'p>,
    daa: &'a DaaHistoryRoster<'p>,
}

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct HistoricalRole4Counts {
    pub(crate) height: usize,
    pub(crate) daa: crate::daa_history_roster::HistoryEndpointCounts,
}

impl HistoricalRole4Counts {
    pub(crate) fn total(&self) -> Result<usize, String> {
        self.daa.lanes.iter().try_fold(self.height, |a, b| a.checked_add(*b).ok_or_else(|| "history endpoint total".into()))
    }
}

impl<'a,'p> HistoricalRole4Endpoints<'a,'p> {
    pub(crate) fn new(height: &'a HeightWork<'p>, daa: &'a DaaHistoryRoster<'p>) -> Result<Self, String> {
        let adapter = Self { height, daa }; adapter.validate()?; Ok(adapter)
    }

    fn validate(&self) -> Result<(), String> {
        self.height.check_history_endpoint_scope()?;
        let parent = self.height.endpoint_parent();
        let h = parent.slot_log();
        if !std::ptr::eq(parent, self.daa.endpoint_parent()) {
            return Err("history endpoint parent identity".into());
        }
        if !(2..=21).contains(&h) || parent.headers() != self.daa.headers()
            || self.height.slots() != parent.slots() || parent.slots() != 1usize << h
            || self.daa.slot_log() != h || self.height.input_log() != 20 + h
            || self.daa.input_log() != 20 + h || self.height.row_log() != 6 + h
            || self.daa.row_log() != 19 + h {
            return Err("history endpoint relation geometry".into());
        }
        Ok(())
    }

    pub(crate) fn check_edge(&self, left: bool, slot: usize,
        edge: &crate::sparse_stream_roster::EdgeTerm) -> Result<(), String> {
        self.validate()?;
        let h = self.daa.slot_log();
        if slot >= self.height.slots() { return Err("history endpoint requested owner".into()); }
        check_term(20 + h, 20 + h, &edge.term)?;
        let row = crate::sparse_stream_roster::global_edge_row(edge.source_slot, edge.family_row, h, 19, 1, &[19,19])?;
        let endpoint = if left { edge.term.gate.left } else { edge.term.gate.right };
        if row != edge.term.row || endpoint / (1 << 20) != slot {
            return Err("history endpoint canonical row or side".into());
        }
        Ok(())
    }

    fn pack(&self, family: usize, term: Term, left: bool, slot: usize)
        -> Result<crate::sparse_stream_roster::EdgeTerm, String> {
        let base = 1usize.checked_shl((19 + self.daa.slot_log()) as u32).ok_or("history endpoint row base")?;
        let low = term.row.checked_sub(family.checked_mul(base).ok_or("history endpoint family overflow")?)
            .filter(|row| *row < base).ok_or("history endpoint family row")?;
        if family > 1 { return Err("history endpoint family".into()); }
        let edge = crate::sparse_stream_roster::EdgeTerm {
            source_slot: low >> 19, family_row: (family << 19) | (low & ((1 << 19) - 1)), term,
        };
        self.check_edge(left, slot, &edge)?; Ok(edge)
    }

    pub(crate) fn visit(&self, left: bool, slot: usize,
        mut sink: impl FnMut(crate::sparse_stream_roster::EdgeTerm) -> Result<(), String>)
        -> Result<HistoricalRole4Counts, String> {
        self.validate()?;
        if slot >= self.height.slots() { return Err("history endpoint requested owner".into()); }
        let height = self.height.visit_history_endpoint_terms(left, slot, |term| sink(self.pack(0, term, left, slot)?))?;
        let base = 1usize << self.daa.row_log();
        let daa = self.daa.visit_history_endpoint_terms(left, slot, |mut term| {
            term.row = term.row.checked_add(base).ok_or("history endpoint DAA outer row")?;
            sink(self.pack(1, term, left, slot)?)
        })?;
        Ok(HistoricalRole4Counts { height, daa })
    }

    pub(crate) fn coefficients(&self, r: &[Fr], u: &[Fr], v: &[Fr]) -> Result<[Fr;4], String> {
        self.validate()?; composite_coefficients(self.height, self.daa, r, u, v)
    }
}



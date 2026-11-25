use super::*;
use num_bigint::BigUint;
use std::{collections::BTreeMap, sync::OnceLock};
use crate::{daa_history_roster::DaaHistoryRoster, historical_prefix_height_work::HeightWork,
    historical_prefix_witness as prefix, serializer, sparse, work_tree_layout};

fn headers() -> &'static Vec<ergo_header_core::Header> {
    static HEADERS: OnceLock<Vec<ergo_header_core::Header>> = OnceLock::new();
    HEADERS.get_or_init(|| prefix::retained_headers().unwrap())
}

fn total() -> [u8; 28] { let mut w = [0; 28]; w[0] = 0xf0; w[27] = 3; w }
fn floor() -> [u8; 28] { let mut w = [0; 28]; w[0] = 0x80; w[5] = 0x35; w[27] = 9; w }
fn be28(value: &BigUint) -> [u8; 28] {
    let bytes = value.to_bytes_be(); assert!(bytes.len() <= 28);
    let mut out = [0; 28]; out[28 - bytes.len()..].copy_from_slice(&bytes); out
}
fn public(h: u64) -> CheckpointPublic {
    let mut header = headers()[1].clone(); header.height = u32::try_from(h).unwrap();
    CheckpointPublic { raw: header.encode().unwrap(), floor_work: floor(),
        audit_work: be28(&(BigUint::from_bytes_be(&total()) - BigUint::from_bytes_be(&floor()))) }
}
fn parent() -> &'static WorkTreeHistoryPlan {
    static PLAN: OnceLock<WorkTreeHistoryPlan> = OnceLock::new();
    PLAN.get_or_init(|| WorkTreeHistoryPlan::compile(66, 7, [7; 32], total()).unwrap())
}
fn large() -> &'static WorkTreeHistoryPlan {
    static PLAN: OnceLock<WorkTreeHistoryPlan> = OnceLock::new();
    PLAN.get_or_init(|| WorkTreeHistoryPlan::compile((1 << 21) - 1, 21, [7; 32], total()).unwrap())
}
fn terms(role: &CheckpointOutputLayout<'_>) -> Vec<Term> {
    let mut out = Vec::new(); assert_eq!(role.visit_terms(|t| { out.push(t); Ok(()) }).unwrap(), 4346); out
}
fn point(log: usize, index: usize) -> Vec<Fr> {
    (0..log).map(|b| Fr::from(((index >> b) & 1) as u64)).collect()
}
fn dense(log: usize, seed: u64) -> Vec<Fr> {
    (0..log).map(|b| Fr::from(seed + b as u64 * 13)).collect()
}
fn direct(ts: &[Term], r: &[Fr], u: &[Fr], v: &[Fr]) -> [Fr; 4] {
    // Independently expand index selectors without production's owner factoring.
    fn select(p: &[Fr], index: usize) -> Fr {
        let mut weight = Fr::one();
        for (b, x) in p.iter().enumerate() {
            if index & (1 << b) == 0 { weight *= Fr::one() - x; } else { weight *= x; }
        } weight
    }
    let mut out = [Fr::zero(); 4];
    for t in ts {
        let w = select(r, t.row) * select(u, t.gate.left) * select(v, t.gate.right);
        for (a, c) in out.iter_mut().zip([t.gate.c0, t.gate.c1, t.gate.c2, t.gate.c3]) { *a += w * c; }
    } out
}
fn assignment(h: u64, f: u64, raw: &[u8], wf: [u8; 28]) -> BTreeMap<usize, Fr> {
    let header = ergo_header_core::Header::decode(raw, None).unwrap();
    let producer = serializer::build(Some(&serializer::Fields::from_header(&header).unwrap())).unwrap();
    let input = producer.input.as_ref().unwrap();
    let mut values = BTreeMap::new();
    // Actual existing serializer output, independently mapped into header space.
    for wire in producer.layout.bytes.iter().flatten().chain(&producer.layout.length) {
        values.insert((h as usize - 1) * (1 << 20) + 524288 + *wire, input[*wire]);
    }
    let number = BigUint::from_bytes_be(&wf);
    for b in 0..224 {
        let bit = (&number >> b) & BigUint::from(1u8);
        values.insert((f as usize - 2) * (1 << 20) + 987450 + b,
            Fr::from(u64::from(bit == BigUint::from(1u8))));
    }
    values
}
fn failures(ts: &[Term], values: &BTreeMap<usize, Fr>) -> Vec<usize> {
    let mut rows = BTreeMap::<usize, Fr>::new();
    for t in ts {
        let a = values.get(&t.gate.left).copied().unwrap_or_default();
        let b = values.get(&t.gate.right).copied().unwrap_or_default();
        *rows.entry(t.row).or_default() += t.gate.c0 + t.gate.c1 * a + t.gate.c2 * b + t.gate.c3 * a * b;
    }
    rows.into_iter().filter_map(|(i, v)| (!v.is_zero()).then_some(i)).collect()
}

// Independent serializer-coordinate and public-bit oracle for the new lane.
fn role4_expected(public: &CheckpointPublic, h: usize, f: usize, base: usize) -> Vec<Term> {
    let header = ergo_header_core::Header::decode(&public.raw, None).unwrap();
    let serialized = serializer::build(Some(&serializer::Fields::from_header(&header).unwrap())).unwrap();
    let wires: Vec<_> = serialized.layout.bytes.iter().flatten().chain(&serialized.layout.length).copied().collect();
    assert_eq!(wires.len(), 4122);
    let baseline = work_tree_layout::shared_baseline().unwrap();
    (0..4346).map(|row| {
        let (source, bit) = if row < 4112 {
            ((h - 1) * work_tree_layout::WIDTH + 524288 + wires[row],
                (public.raw.get(row / 8).copied().unwrap_or(0) >> (row % 8)) & 1 == 1)
        } else if row < 4122 {
            ((h - 1) * work_tree_layout::WIDTH + 524288 + wires[row],
                (public.raw.len() >> (row - 4112)) & 1 == 1)
        } else {
            let b = row - 4122;
            ((f - 2) * work_tree_layout::WIDTH + baseline.endpoints.upper[b],
                (public.floor_work[27 - b / 8] >> (b % 8)) & 1 == 1)
        };
        Term { row: base + row, gate: Gate { left: source, right: 0,
            c0: -Fr::from(bit as u64), c1: Fr::one(), c2: Fr::zero(), c3: Fr::zero() } }
    }).collect()
}

fn role4_digest(visit: impl FnOnce(&mut dyn FnMut(Term) -> Result<(), String>) -> Result<(), String>)
    -> (usize, [u8; 32])
{
    use ark_serialize::CanonicalSerialize;
    use blake2::{Blake2b, Digest, digest::consts::U32};
    let mut hash = Blake2b::<U32>::new(); let mut count = 0;
    visit(&mut |term| {
        for value in [term.row, term.gate.left, term.gate.right] { hash.update((value as u64).to_le_bytes()); }
        for value in [term.gate.c0, term.gate.c1, term.gate.c2, term.gate.c3] {
            let mut bytes = [0; 32]; value.serialize_compressed(&mut bytes[..]).unwrap(); hash.update(bytes);
        }
        count += 1; Ok(())
    }).unwrap();
    (count, hash.finalize().into())
}

#[test]
fn checkpoint_role4_lane_selector_rows_and_original_global_x_match_independent_terms() {
    let public = public(2); let lane = CheckpointRole4Lane::new(parent(), 2, public.clone()).unwrap();
    let d = lane.descriptor();
    assert_eq!(d.base >> 19,(d.base + d.live_rows - 1) >> 19);
    assert_eq!((d.headers, d.slot_log, d.h, d.f, d.depth, d.input_log, d.row_log, d.base, d.live_rows),
        (66, 7, 2, 65, 64, 27, 27, 8192, 4346));
    let expected = role4_expected(&public, 2, 65, d.base);
    let mut actual = Vec::new();
    assert_eq!(lane.visit_owner_terms(&d, 0, |term| { actual.push(term); Ok(()) }).unwrap(), 4346);
    assert_eq!(actual, expected);
    for owner in [1, 63, 127] { assert_eq!(lane.visit_owner_terms(&d, owner, |_| panic!("unexpected ROW owner")).unwrap(), 0); }
    for seed in [3, 29] {
        let (r,u,v) = (dense(27, seed), dense(27, seed + 7), dense(27, seed + 19));
        assert_eq!(lane.coefficients(&r,&u,&v).unwrap(), direct(&expected,&r,&u,&v));
    }
    for row in [0, 4111, 4112, 4121, 4122, 4345] {
        let term = &expected[row]; let r = point(27, term.row); let u = point(27, term.gate.left);
        assert_eq!(lane.coefficients(&r,&u,&point(27,0)).unwrap(), [term.gate.c0,Fr::one(),Fr::zero(),Fr::zero()]);
        assert_eq!(lane.coefficients(&r,&u,&point(27,(term.gate.left >> 20) << 20)).unwrap(), [Fr::zero();4]);
    }
    for row in [d.base - 1, d.base + 4346, (1 << 26) - 1, 1 << 26] {
        assert_eq!(lane.coefficients(&point(27,row),&point(27,expected[0].gate.left),&point(27,0)).unwrap(), [Fr::zero();4]);
    }
    // Omitting, duplicating, or moving one term has a distinct first-row result.
    let (r,u,v) = (point(27,d.base),point(27,expected[0].gate.left),point(27,0));
    let canonical = lane.coefficients(&r,&u,&v).unwrap();
    assert_ne!(canonical,direct(&expected[1..],&r,&u,&v));
    let mut duplicate = expected.clone(); duplicate.push(expected[0].clone());
    assert_ne!(canonical,direct(&duplicate,&r,&u,&v));
    let mut shifted = expected.clone(); shifted[0].row += 1;
    assert_ne!(canonical,direct(&shifted,&r,&u,&v));
    for (rl,ul,vl) in [(26,27,27),(28,27,27),(27,26,27),(27,28,27),(27,27,26),(27,27,28)] {
        assert!(lane.coefficients(&vec![Fr::zero();rl],&vec![Fr::zero();ul],&vec![Fr::zero();vl]).is_err());
    }
}

#[test]
fn checkpoint_role4_diagnostic_composition_preserves_old_polynomial_and_exact_streams() {
    use crate::native_prefix_auth_plan::{DiagnosticCheckpointRole4Relation, HistoricalRole4Endpoints,
        composite_coefficients, visit_composite_owner};
    let relation = DiagnosticCheckpointRole4Relation::new(parent(),2,public(2)).unwrap();
    let d = relation.descriptor(); let expected = role4_expected(&public(2),2,65,d.checkpoint.base);
    let height = HeightWork::compile_history(parent()).unwrap(); let daa = DaaHistoryRoster::compile(parent()).unwrap();
    for seed in [7,31] {
        let (r,u,v) = (dense(27,seed),dense(27,seed+13),dense(27,seed+29));
        let old = composite_coefficients(&height,&daa,&r,&u,&v).unwrap();
        let added = direct(&expected,&r,&u,&v);
        assert_eq!(relation.coefficients(&d,&r,&u,&v).unwrap(),std::array::from_fn(|i|old[i]+added[i]));
    }
    // The old producers are unchanged. Check their join at all new sources
    // and the domain boundary; the lane-only test covers every other owner.
    let endpoints = HistoricalRole4Endpoints::new(&height,&daa).unwrap();
    for owner in [0,1,63,127] {
        let actual = role4_digest(|sink| relation.visit_owner_terms(&d,owner,sink).map(|_|()));
        let reference = role4_digest(|sink| {
            visit_composite_owner(&height,&daa,owner as u64,&mut *sink)?;
            for term in expected.iter().filter(|t|t.row >> 19 == owner) { sink(term.clone())?; } Ok(())
        });
        assert_eq!(actual,reference,"ROW owner {owner}");
        for left in [true,false] {
            let actual = role4_digest(|sink| relation.visit_endpoint(&d,left,owner,|edge| {
                assert_eq!(crate::sparse_stream_roster::global_edge_row(edge.source_slot,edge.family_row,7,19,1,&[19,19])?,edge.term.row);
                assert_eq!((if left {edge.term.gate.left} else {edge.term.gate.right}) >> 20,owner);
                sink(edge.term)
            }).map(|_|()));
            let reference = role4_digest(|sink| {
                endpoints.visit(left,owner,|edge|sink(edge.term))?;
                for term in expected.iter().filter(|t|(if left {t.gate.left} else {t.gate.right}) >> 20 == owner) {
                    sink(term.clone())?;
                } Ok(())
            });
            assert_eq!(actual,reference,"endpoint side {left} owner {owner}");
        }
    }
}

#[test]
fn checkpoint_role4_lane_inverse_endpoints_distinguish_x_and_row_owners() {
    let lane = CheckpointRole4Lane::new(parent(),2,public(2)).unwrap(); let d = lane.descriptor();
    let expected = role4_expected(&public(2),2,65,d.base);
    for owner in 0..128 {
        if owner != d.base >> 19 {
            assert_eq!(lane.visit_owner_terms(&d,owner,|_|panic!("unrelated ROW owner")).unwrap(),0);
        }
        for left in [true,false] {
            let mut actual = Vec::new();
            let count = lane.visit_endpoint(&d,left,owner,|edge| {
                assert_eq!(edge.source_slot,0); assert_eq!(edge.family_row,edge.term.row);
                assert_eq!(edge.term.gate.right,0); actual.push(edge.term); Ok(())
            }).unwrap();
            let reference: Vec<_> = expected.iter().filter(|t|(if left {t.gate.left} else {t.gate.right}) >> 20 == owner).cloned().collect();
            assert_eq!(actual,reference);
            assert_eq!(count,if left {match owner {1=>4122,63=>224,_=>0}} else if owner==0 {4346} else {0});
        }
    }
    let mut altered = d.clone(); altered.base += 8192;
    let mut calls = 0;
    assert!(lane.visit_endpoint(&altered,true,1,|_|{calls+=1;Ok(())}).is_err());
    assert!(lane.visit_owner_terms(&altered,0,|_|{calls+=1;Ok(())}).is_err());
    assert!(lane.visit_endpoint(&d,false,128,|_|{calls+=1;Ok(())}).is_err());
    assert!(lane.visit_owner_terms(&d,128,|_|{calls+=1;Ok(())}).is_err()); assert_eq!(calls,0);
    assert_eq!(lane.visit_endpoint(&d,true,1,|_|Err("lane sink sentinel".into())).err().as_deref(),Some("lane sink sentinel"));
}

#[test]
fn checkpoint_role4_descriptors_and_binding_are_closed_before_challenges() {
    use crate::native_prefix_auth_plan::{DiagnosticCheckpointRole4Relation,Selection};
    let relation = DiagnosticCheckpointRole4Relation::new(parent(),2,public(2)).unwrap(); let d = relation.descriptor();
    let mut t = Transcript::new(b"role4-c200-binding-tests"); relation.bind(&d,&mut t).unwrap();
    assert_eq!(t.challenges(),0); let golden = t.challenge_scalar(b"bound");
    assert!(relation.bind(&d,&mut t).is_err());
    for field in 0..15 {
        let mut wrong = d.clone();
        match field {0=>wrong.tag="other",1=>wrong.parent_object^=1,2=>wrong.checkpoint.h+=1,
            3=>wrong.checkpoint.f+=1,4=>wrong.checkpoint.depth=1,5=>wrong.checkpoint.base+=8192,
            6=>wrong.checkpoint.live_rows-=1,7=>wrong.checkpoint.map_fingerprint.push('x'),
            8=>wrong.checkpoint.headers+=1,9=>wrong.checkpoint.input_log+=1,10=>wrong.checkpoint.row_log+=1,
            11=>wrong.checkpoint.root[0]^=1,12=>wrong.checkpoint.total[27]^=1,
            13=>wrong.checkpoint.public_fingerprint.push('x'),_=>wrong.checkpoint.slot_log+=1}
        let mut t = Transcript::new(b"role4-c200-binding-tests"); let before = t.bytes_absorbed();
        assert!(relation.bind(&wrong,&mut t).is_err()); assert_eq!(t.bytes_absorbed(),before);
        let mut calls=0; assert!(relation.visit_owner_terms(&wrong,0,|_|{calls+=1;Ok(())}).is_err());
        assert!(relation.visit_endpoint(&wrong,false,0,|_|{calls+=1;Ok(())}).is_err()); assert_eq!(calls,0);
    }
    let same_values_parent = WorkTreeHistoryPlan::compile(66,7,[7;32],total()).unwrap();
    let foreign = DiagnosticCheckpointRole4Relation::new(&same_values_parent,2,public(2)).unwrap().descriptor();
    assert!(relation.bind(&foreign,&mut Transcript::new(b"role4-c200-binding-tests")).is_err());
    let mut changed = public(2); changed.floor_work[27]^=1;
    changed.audit_work=be28(&(BigUint::from_bytes_be(&total())-BigUint::from_bytes_be(&changed.floor_work)));
    let altered=DiagnosticCheckpointRole4Relation::new(parent(),2,changed).unwrap();
    assert_ne!(d.checkpoint.public_fingerprint,altered.descriptor().checkpoint.public_fingerprint);
    assert!(relation.bind(&altered.descriptor(),&mut Transcript::new(b"role4-c200-binding-tests")).is_err());
    let mut t=Transcript::new(b"role4-c200-binding-tests"); altered.bind(&altered.descriptor(),&mut t).unwrap();
    assert_ne!(golden,t.challenge_scalar(b"bound"));
    // Single-field binder probes bypass construction only here; they do not
    // claim canonical admission of the mutated object. Public fingerprint
    // construction itself is checked below against independently framed bytes.
    let lane=CheckpointRole4Lane::new(parent(),2,public(2)).unwrap();
    let mut framed=b"checkpoint-role4-expected-public-v1".to_vec();
    framed.extend_from_slice(&(public(2).raw.len() as u64).to_le_bytes());
    framed.extend_from_slice(&public(2).raw); framed.extend_from_slice(&floor());
    framed.extend_from_slice(&public(2).audit_work);
    assert_eq!(lane.descriptor().public_fingerprint,work_tree_layout::hash_bytes(&framed));
    let probe=|lane:&CheckpointRole4Lane<'_>| {
        let mut t=Transcript::new(b"role4-lane-isolated-binding");lane.bind(&mut t).unwrap();t.challenge_scalar(b"bound")
    };
    let original=probe(&lane);
    let mut late=Transcript::new(b"role4-lane-late-binding"); late.challenge_scalar(b"prior");
    let before=(late.bytes_absorbed(),late.challenges(),late.raw_queries());
    assert_eq!(lane.bind(&mut late).err().as_deref(),Some("checkpoint role4 binding after challenge"));
    assert_eq!((late.bytes_absorbed(),late.challenges(),late.raw_queries()),before);
    for field in 0..6 {
        let mut changed=CheckpointRole4Lane::new(parent(),2,public(2)).unwrap();
        match field {0=>changed.checkpoint.public.raw[0]^=1,1=>changed.checkpoint.public.raw.push(0),
            2=>changed.checkpoint.public.floor_work[27]^=1,3=>changed.checkpoint.public.audit_work[27]^=1,
            4=>changed.descriptor.root[0]^=1,_=>changed.descriptor.total[27]^=1}
        assert_ne!(original,probe(&changed),"isolated binding input {field}");
    }
    assert!(DiagnosticCheckpointRole4Relation::new(parent(),3,public(3)).is_err());
    assert!(DiagnosticCheckpointRole4Relation::new(parent(),1,public(2)).is_err());
    assert!(CheckpointRole4Lane::new(&WorkTreeHistoryPlan::compile(3,2,[7;32],total()).unwrap(),2,public(2)).is_err());
    let selection=Selection::s12(); assert_eq!((selection.query_h,selection.slot_log),(3073,12)); assert!(selection.validate().is_ok());
    let parent12=WorkTreeHistoryPlan::compile(3073,12,[7;32],total()).unwrap();
    assert!(CheckpointRole4Lane::new(&parent12,selection.query_h,public(selection.query_h)).err().unwrap().contains("immature"));
}

#[test]
fn checkpoint_role4_translated_false_raw_floor_and_admission_faults_remain_load_bearing() {
    let good = public(2); let values = assignment(2,65,&good.raw,good.floor_work);
    let collect = |p| {
        let lane=CheckpointRole4Lane::new(parent(),2,p).unwrap(); let mut out=Vec::new();
        lane.visit_owner_terms(&lane.descriptor(),0,|term|{out.push(term);Ok(())}).unwrap(); out
    };
    assert!(failures(&collect(good.clone()),&values).is_empty());
    let mut raw_header=ergo_header_core::Header::decode(&good.raw,None).unwrap();
    match &mut raw_header.pow {
        ergo_header_core::PowSolution::V1{nonce,..}|ergo_header_core::PowSolution::V2{nonce,..}=>nonce[0]^=1,
    }
    let mut changed=good.clone(); changed.raw=raw_header.encode().unwrap();
    assert_eq!(changed.raw.len(),good.raw.len());
    let byte=changed.raw.iter().zip(&good.raw).position(|(a,b)|a!=b).unwrap();
    assert_eq!(failures(&collect(changed),&values),vec![8192+byte*8]);
    let mut changed=good.clone(); changed.floor_work[27]^=1;
    changed.audit_work=be28(&(BigUint::from_bytes_be(&total())-BigUint::from_bytes_be(&changed.floor_work)));
    assert_eq!(failures(&collect(changed),&values),vec![8192+4122]);
    let mut wrong=good.clone(); wrong.audit_work[27]^=1;
    assert!(CheckpointRole4Lane::new(parent(),2,wrong).err().unwrap().contains("supplied audit work"));
    assert!(CheckpointRole4Lane::new(parent(),2,public(3)).err().unwrap().contains("height differs"));
}

#[test]
fn checkpoint_role4_large_geometry_keeps_high_row_and_endpoint_owner_bits() {
    let h=(1<<21)-66; let p=public(h); let lane=CheckpointRole4Lane::new(large(),h,p.clone()).unwrap();
    let d=lane.descriptor(); assert_eq!((d.input_log,d.row_log,d.base),(41,41,1<<27));
    assert_eq!(d.base >> 19,(d.base + d.live_rows - 1) >> 19);
    for owner in [0,255,257,(1<<21)-1] {
        assert_eq!(lane.visit_owner_terms(&d,owner,|_|panic!("unrelated high ROW owner")).unwrap(),0);
    }
    for owner in [0,1,(1<<21)-1] {
        assert_eq!(lane.visit_endpoint(&d,true,owner,|_|panic!("unrelated high left owner")).unwrap(),0);
    }
    for owner in [1,256,(1<<21)-1] {
        assert_eq!(lane.visit_endpoint(&d,false,owner,|_|panic!("unrelated high right owner")).unwrap(),0);
    }
    let expected=role4_expected(&p,h as usize,(h+63) as usize,d.base);
    let mut emitted=Vec::new();
    lane.visit_owner_terms(&d,d.base>>19,|term|{emitted.push(term);Ok(())}).unwrap(); assert_eq!(emitted,expected);
    for row in [0,4112,4122,4345] {
        let term=&expected[row]; let r=point(41,term.row); let u=point(41,term.gate.left); let v=point(41,0);
        assert_eq!(lane.coefficients(&r,&u,&v).unwrap(),[term.gate.c0,Fr::one(),Fr::zero(),Fr::zero()]);
        for bit in 0..21 {
            let mut wrong=u.clone(); wrong[20+bit]=Fr::one()-wrong[20+bit];
            assert_eq!(lane.coefficients(&r,&wrong,&v).unwrap(),[Fr::zero();4]);
        }
    }
    let mut count=0;
    lane.visit_endpoint(&d,false,0,|edge|{assert_eq!(edge.source_slot,256);assert_eq!(edge.term.gate.right,0);count+=1;Ok(())}).unwrap();
    assert_eq!(count,4346);
}

#[test]
fn checkpoint_admission_and_exact_integer_difference_are_verifier_owned() {
    let good = public(2);
    let role = CheckpointOutputLayout::new(parent(), 2, good.clone()).unwrap();
    assert_eq!((role.h, role.f, role.depth, role.input_log(), role.row_log()), (2, 65, 64, 27, 13));
    for (h, p, error) in [(1, good.clone(), "h >= 2"), (3, public(3), "immature"),
        (u64::MAX, good.clone(), "overflow")] {
        assert!(CheckpointOutputLayout::new(parent(), h, p).err().unwrap().contains(error));
    }
    let mut wrong = good.clone(); wrong.audit_work[27] ^= 1;
    assert!(CheckpointOutputLayout::new(parent(), 2, wrong).err().unwrap().contains("supplied audit work"));
    for wf in [total(), [0xff; 28]] {
        let mut bad = good.clone(); bad.floor_work = wf;
        assert!(CheckpointOutputLayout::new(parent(), 2, bad).err().unwrap().contains("floor < total"));
    }
    for raw in [Vec::new(), vec![0; 515], headers()[0].encode().unwrap()] {
        let mut bad = good.clone(); bad.raw = raw;
        assert!(CheckpointOutputLayout::new(parent(), 2, bad).is_err());
    }
    let mut bad = good.clone(); bad.raw.push(0);
    assert!(CheckpointOutputLayout::new(parent(), 2, bad).is_err());
    // The test-depth entry cannot be used for a production-shape parent.
    assert!(CheckpointOutputLayout::diagnostic(parent(), 2, good).is_err());
    let maximal = [0xff; 28]; let mut one = [0; 28]; one[27] = 1;
    assert_eq!(checked_difference(&maximal, &one).unwrap(),
        be28(&(BigUint::from_bytes_be(&maximal) - BigUint::from(1u8))));
}

#[test]
fn checkpoint_source_byte_length_and_floor_faults_are_isolated_and_load_bearing() {
    let p = public(2); let role = CheckpointOutputLayout::new(parent(), 2, p.clone()).unwrap();
    let all = terms(&role); let good = assignment(2, 65, &p.raw, p.floor_work);
    assert!(failures(&all, &good).is_empty());
    // Canonical nonce alteration keeps height, parser shape and length fixed.
    let mut header = headers()[1].clone();
    match &mut header.pow {
        ergo_header_core::PowSolution::V1 { nonce, .. } | ergo_header_core::PowSolution::V2 { nonce, .. } => nonce[0] ^= 1,
    }
    let changed_raw = header.encode().unwrap(); assert_eq!(changed_raw.len(), p.raw.len());
    let altered: Vec<_> = changed_raw.iter().zip(&p.raw).enumerate()
        .filter_map(|(i, (a, b))| (a != b).then_some(i)).collect(); assert_eq!(altered.len(), 1);
    let mut changed_public = p.clone(); changed_public.raw = changed_raw;
    let changed_role = CheckpointOutputLayout::new(parent(), 2, changed_public).unwrap();
    let changed_terms = terms(&changed_role);
    assert_eq!(failures(&changed_terms, &good), vec![altered[0] * 8]);
    let omitted_raw: Vec<_> = changed_terms.iter().filter(|t| t.row != altered[0] * 8).cloned().collect();
    assert!(failures(&omitted_raw, &good).is_empty());

    let mut bad_length = good.clone();
    let key = all[4112].gate.left; bad_length.insert(key, Fr::one() - good[&key]);
    assert_eq!(failures(&all, &bad_length), vec![4112]);
    let omitted_length: Vec<_> = all.iter().filter(|t| t.row != 4112).cloned().collect();
    assert!(failures(&omitted_length, &bad_length).is_empty());

    let mut changed = p.clone(); changed.floor_work[27] ^= 1;
    changed.audit_work = be28(&(BigUint::from_bytes_be(&total()) - BigUint::from_bytes_be(&changed.floor_work)));
    let changed = CheckpointOutputLayout::new(parent(), 2, changed).unwrap();
    let changed_terms = terms(&changed);
    assert_eq!(failures(&changed_terms, &good), vec![4122]);
    let omitted_work: Vec<_> = changed_terms.iter().filter(|t| t.row != 4122).cloned().collect();
    assert!(failures(&omitted_work, &good).is_empty());
    for b in [0, 63, 223] {
        let mut bad = good.clone(); let wire = 63 * (1 << 20) + 987450 + b;
        bad.insert(wire, Fr::one() - good[&wire]);
        assert_eq!(failures(&all, &bad), vec![4122 + b]);
    }
    let mut reversed = p.floor_work; reversed.reverse();
    let reversed_values = assignment(2, 65, &p.raw, reversed);
    let wrong_rows = failures(&all, &reversed_values); assert!(!wrong_rows.is_empty());
    assert!(wrong_rows.iter().all(|r| (4122..4346).contains(r)));
}

#[test]
fn checkpoint_analytic_channels_owners_global_zero_padding_and_lengths_are_exact() {
    let role = CheckpointOutputLayout::new(parent(), 2, public(2)).unwrap(); let all = terms(&role);
    for seed in [3, 37] {
        let (r, u, v) = (dense(13, seed), dense(27, seed + 3), dense(27, seed + 11));
        assert_eq!(role.coefficients(&r, &u, &v).unwrap(), direct(&all, &r, &u, &v));
    }
    for row in [0, 4111, 4112, 4121, 4122, 4345] {
        let t = &all[row]; let r = point(13, row); let u = point(27, t.gate.left); let v = point(27, 0);
        assert_eq!(role.coefficients(&r, &u, &v).unwrap(), [t.gate.c0, Fr::one(), Fr::zero(), Fr::zero()]);
        let wrong_owner = point(27, t.gate.left + (1 << 20));
        assert_eq!(role.coefficients(&r, &wrong_owner, &v).unwrap(), [Fr::zero(); 4]);
        let owner_zero = point(27, (t.gate.left >> 20) << 20);
        assert_eq!(role.coefficients(&r, &u, &owner_zero).unwrap(), [Fr::zero(); 4]);
    }
    let t = &all[0]; let r = point(13, 4346); let u = point(27, t.gate.left); let v = point(27, 0);
    assert_eq!(role.coefficients(&r, &u, &v).unwrap(), [Fr::zero(); 4]);
    let mut extra = all.clone(); let mut added = t.clone(); added.row = 4346; extra.push(added);
    assert_ne!(direct(&extra, &r, &u, &v), role.coefficients(&r, &u, &v).unwrap());
    for (rlen, ulen, vlen) in [(12,27,27),(14,27,27),(13,26,27),(13,28,27),(13,27,26),(13,27,28)] {
        assert!(role.coefficients(&vec![Fr::zero(); rlen], &vec![Fr::zero(); ulen], &vec![Fr::zero(); vlen]).is_err());
    }
}

#[test]
fn checkpoint_large_history_selectors_keep_all_owner_bits_without_materialization() {
    let h = (1 << 21) - 66; let role = CheckpointOutputLayout::new(large(), h, public(h)).unwrap();
    assert_eq!(role.input_log(), 41); let all = terms(&role); assert_eq!(all.len(), 4346);
    for row in [0, 4112, 4122, 4345] {
        let t = &all[row]; let r = point(13, row); let u = point(41, t.gate.left); let v = point(41, 0);
        assert_eq!(role.coefficients(&r, &u, &v).unwrap(), [t.gate.c0, Fr::one(), Fr::zero(), Fr::zero()]);
        for owner_bit in 0..21 {
            let mut wrong = u.clone(); wrong[20 + owner_bit] = Fr::one() - wrong[20 + owner_bit];
            assert_eq!(role.coefficients(&r, &wrong, &v).unwrap(), [Fr::zero(); 4]);
        }
    }
    let (r, u, v) = (dense(13, 7), dense(41, 11), dense(41, 31));
    assert_eq!(role.coefficients(&r, &u, &v).unwrap(), direct(&all, &r, &u, &v));
}

#[test]
fn checkpoint_transcript_binds_expected_values_geometry_and_maps_before_challenges() {
    fn challenge(role: &CheckpointOutputLayout<'_>) -> Fr {
        let mut t = Transcript::new(b"checkpoint-binding-tests"); role.bind(&mut t);
        assert_eq!(t.challenges(), 0); t.challenge_scalar(b"bound")
    }
    let baseline = challenge(&CheckpointOutputLayout::new(parent(), 2, public(2)).unwrap());
    for field in 0..8 {
        // Descriptor-only binding probes; these mutations do not claim admission.
        let mut changed = CheckpointOutputLayout::new(parent(), 2, public(2)).unwrap();
        match field {
            0 => changed.h += 1, 1 => changed.f += 1, 2 => changed.domain = b"different-profile",
            3 => changed.public.raw[0] ^= 1, 4 => changed.public.floor_work[27] ^= 1,
            5 => changed.map_fingerprint.push('x'), 6 => changed.public.audit_work[27] ^= 1,
            _ => changed.depth += 1,
        }
        assert_ne!(baseline, challenge(&changed));
    }
}

#[test]
fn checkpoint_native_n3_gkr_uses_analytic_consumer_and_known_witness_terminal() {
    let native = crate::historical_prefix_public::expected(3).unwrap();
    let witness = prefix::build(headers()).unwrap(); assert_eq!(witness.total, native.total);
    assert_eq!(witness.root, native.root);
    let parent = WorkTreeHistoryPlan::compile(3, 2, native.root, native.total).unwrap();
    let wf = be28(&crate::work_tree_work::native_decode(headers()[1].n_bits).unwrap());
    let p = CheckpointPublic { raw: headers()[1].encode().unwrap(), floor_work: wf,
        audit_work: be28(&(BigUint::from_bytes_be(&native.total) - BigUint::from_bytes_be(&wf))) };
    assert!(CheckpointOutputLayout::new(&parent, 2, p.clone()).is_err());
    let role = CheckpointOutputLayout::diagnostic(&parent, 2, p).unwrap();
    let circuit = sparse::Circuit { input_len: 1 << 22, row_count: 1 << 13, terms: terms(&role) };
    for t in &circuit.terms { assert_eq!(t.gate.evaluate(&witness.values), Fr::zero()); }
    let mut pt = Transcript::new(b"checkpoint-known-witness-gkr-v1");
    let (proof, prover_claim) = sparse::prove_with_binding(&circuit, &witness.values, 0, &mut pt, |t| role.bind(t)).unwrap();
    let mut vt = Transcript::new(b"checkpoint-known-witness-gkr-v1");
    let claim = role.verify(&proof, &mut vt).unwrap();
    assert_eq!(claim.point, prover_claim.point); assert_eq!(claim.value, prover_claim.value);
    assert_eq!(gkr::mle(&witness.values, &claim.point).unwrap(), claim.value);
    // Proof messages must remain load-bearing. No PCS or full-history claim.
    let mut bad = proof.clone(); bad.layers[0].rounds[0][0] += Fr::one();
    let mut bt = Transcript::new(b"checkpoint-known-witness-gkr-v1"); assert!(role.verify(&bad, &mut bt).is_err());
    assert_eq!(pt.challenge_scalar(b"post"), vt.challenge_scalar(b"post"));
}

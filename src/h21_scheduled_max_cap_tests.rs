use super::*;
use std::{collections::BTreeSet, sync::OnceLock};

// Separate height-space oracle: no Plan, schedule allocator or production constants.
fn epochs(c:usize)->Vec<(usize,usize)> {
    let end=if c==0 {1_827_840}else{1_827_775};
    let mut result=vec![(844672,844672)];
    for start in (844673..=end).step_by(128) {result.push((start,(start+127).min(end)));}
    result
}
fn guards(c:usize)->Vec<(usize,usize)> {
    let limit=if c==0 {1827838}else{1827775};
    let mut result=vec![(845759,844670)];
    for origin in (845888..=limit).step_by(128) {result.push((origin-1,origin-1090));}
    if result.last().unwrap().0!=limit-1 {
        let q=limit-1088;let b=844800+128*((q-844673)/128);
        result.push((limit-1,b-2));
    }result
}
fn difficulty(h:usize)->BigUint {
    let epoch=if h==844672 {0}else{1+(h-844673)/128};
    if epoch==1024 {BigUint::from(1u8)<<62usize}
    else {BigUint::from((epoch*17%997+1)as u64)}
}
fn prepared()->&'static Prepared {
    static P:OnceLock<Prepared>=OnceLock::new();
    P.get_or_init(||Prepared::from_d_iter((844672..=1827840).map(|h|(h,difficulty(h)))).unwrap())
}
fn number(v:&[Fr])->BigUint {
    let mut n=BigUint::zero();for (k,b) in v.iter().enumerate(){
        assert!(*b==Fr::zero()||*b==Fr::one());if *b==Fr::one(){n+=BigUint::from(1u8)<<k;}
    }n
}
fn terms(p:&Plan,o:usize)->Vec<(Writer,Term)> {
    let mut out=Vec::new();p.visit_owner(o,|w,t|{out.push((w,t));Ok(())}).unwrap();out
}
fn bits(n:usize,h:usize)->Vec<Fr> {(0..h).map(|k|Fr::from(((n>>k)&1)as u64)).collect()}
fn point(seed:u64,h:usize)->Vec<Fr> {(0..h).map(|k|Fr::from(seed+37*(k as u64+1))).collect()}
fn independently_eq(p:&[Fr],n:usize)->Fr {
    let mut a=Fr::one();let mut index=n;
    for z in p {a*=if index%2==1 {*z}else{Fr::one()-z};index/=2;}a
}

#[test]
fn full_schedule_and_component_row_partition_are_literal_and_complete() {
    let p=Plan::new();let mut max_terms=0u64;let mut cap_terms=0u64;let mut semantic=0usize;
    for c in 0..2 {
        let expected=epochs(c);assert_eq!(expected.len(),7682);
        assert_eq!(p.epochs[c].iter().map(|e|(e.start,e.end)).collect::<Vec<_>>(),expected);
        let g=guards(c);assert_eq!(g.len(),if c==0 {7674}else{7673});
        assert_eq!(p.caps[c].iter().map(|g|(g.owner,p.epochs[c][g.source].owner())).collect::<Vec<_>>(),g);
        let expected_x=if c==0 {999424..1000097}else{1000097..1000770};
        let expected_cap_x=if c==0 {1000770..1002818}else{1002818..1004866};
        for (j,&(_,b)) in expected.iter().enumerate() {
            assert_eq!(p.max_index(c,b-2),Some(j));
            max_terms+=if j+1==expected.len(){2466}else{2690};semantic+=1;
            let patch=prepared().owner_patch(b-2).unwrap();
            let s=patch.spans.iter().find(|s|s.writer==Writer::Max {context:c,end:b}).unwrap();
            assert_eq!(s.start..s.start+s.values.len(),expected_x);
        }
        for &(o,source_owner) in &g {
            assert!(expected.iter().any(|e|e.1-2==source_owner));
            let patch=prepared().owner_patch(o).unwrap();
            let s=patch.spans.iter().find(|s|s.writer==Writer::Cap {context:c,origin:o+1}).unwrap();
            assert_eq!(s.start..s.start+s.values.len(),expected_cap_x);cap_terms+=6419;semantic+=1;
        }
    }
    assert_eq!((max_terms,cap_terms,semantic),(41328712,98512393,30711));
    // Actual complete local supports, with independent literal ranges.
    let mut rows=BTreeMap::<usize,&str>::new();
    for c in 0..2 {
        for (o,kind) in [(844670,"MAX"),(845759,"Cap")] {
            let selected:Vec<_>=terms(&p,o).into_iter().filter(|(w,_)|match w {
                Writer::Max {context,..} if kind=="MAX"=>*context==c,
                Writer::Cap {context,..} if kind=="Cap"=>*context==c,_=>false}).collect();
            let occupied:BTreeSet<_>=selected.iter().map(|(_,t)|t.row-o*524288).collect();
            let expected:BTreeSet<_>=if kind=="MAX" {
                let (a,e)=if c==0 {(356632,475136)}else{(357305,475585)};
                (a..a+673).chain(e..e+449).collect()
            }else{
                let (a,e)=if c==0 {(357978,476034)}else{(360026,476554)};
                (a..a+1838).chain(a+1903..a+2048).chain(e..e+520).collect()
            };
            assert_eq!(occupied,expected);
            assert_eq!(selected.len(),if kind=="MAX" {2690}else{6419});
            for q in occupied {assert!(rows.insert(q,kind).is_none(),"component relation row collision {q}");}
        }
    }
    assert!((475136..477074).all(|q|!(393216..475136).contains(&q)));
    let mut called=0;assert!(p.visit_owner(2097152,|_,_|{called+=1;Ok(())}).is_err());assert_eq!(called,0);
}

#[test]
fn old_extras_collide_with_actual_coactive_daa_and_high_candidate_excludes_it() {
    use crate::{daa_history_roster::{DaaHistoryRoster,OwnerClass},work_tree_history_plan::WorkTreeHistoryPlan};
    let parent=WorkTreeHistoryPlan::compile(1827840,21,[0;32],[0;28]).unwrap();
    let daa=DaaHistoryRoster::compile(&parent).unwrap();let o=844670;
    assert_eq!(daa.owner_class(o as u64).unwrap(),OwnerClass::Carry);
    let mut occupied=BTreeSet::new();
    daa.visit_owner_terms(o as u64,|t|{occupied.insert(t.row-o*524288);Ok(())}).unwrap();
    for q in 406406..408344 {assert!(occupied.contains(&q),"coactive DAA collision {q}");}
    assert!(ComponentRows::checked([406406,406855],[407304,407824]).is_err());
    assert!(ComponentRows::checked([475136,475136],[476034,476554]).is_err());
    assert!(ComponentRows::checked([524000,475585],[476034,476554]).is_err());
    assert!(ComponentRows::checked([356632,475585],[476034,476554]).is_err());
    let candidate=ComponentRows::checked([475136,475585],[476034,476554]).unwrap();
    for (start,len) in [(candidate.max_extra[0],449),(candidate.max_extra[1],449),
        (candidate.cap_extra[0],520),(candidate.cap_extra[1],520)] {
        assert!((start..start+len).all(|q|!occupied.contains(&q)));
    }
    // Other relation families and final HEADER retirement are not admitted here.
}

#[test]
fn d_stream_is_exact_ordered_epoch_constant_and_cap_bounded_before_export() {
    let valid=|| (844672..=1827840).map(|h|(h,BigUint::from(5u8)));
    assert!(Prepared::from_d_iter(valid().take(983168)).is_err());
    assert!(Prepared::from_d_iter(valid().chain([(1827841,BigUint::from(5u8))])).is_err());
    for (at,which) in [(844672,0),(844673,1),(844674,2),(1827840,3)] {
        let result=Prepared::from_d_iter(valid().map(|(h,mut d)|{
            if h==at {match which {0=>d=BigUint::zero(),1=>d=BigUint::from(1u8)<<224usize,
                2=>d=BigUint::from(6u8),_=>return (h-1,d)}}(h,d)}));
        assert!(result.is_err(),"stream fault {which}");
    }
    // A height hole and a same-height duplicate are independently rejected.
    assert!(Prepared::from_d_iter(valid().filter(|(h,_)|*h!=900000)).is_err());
    assert!(Prepared::from_d_iter(valid().flat_map(|p|if p.0==900000 {vec![p.clone(),p]}else{vec![p]})).is_err());
    let high=BigUint::from(1u8)<<223usize;
    assert!(Prepared::from_d_iter((844672..=1827840).map(|h|(h,high.clone()))).is_err(),"MAX U224 does not imply Cap coverage");
    assert!(Prepared::from_d_iter(valid()).is_ok());
}

#[test]
fn complete_reverse_max_and_cap_producers_match_independent_integer_oracles() {
    let p=prepared();
    for c in 0..2 {
        let e=epochs(c);let mut expected=vec![BigUint::zero();e.len()];let mut next=BigUint::zero();
        for j in (0..e.len()).rev() {
            let d=difficulty(e[j].1);let wanted=if d>next {d.clone()}else{next.clone()};
            let m=&p.max[c][j];assert_eq!(m.d,d);assert_eq!(m.r,wanted);assert_eq!(m.t,next);
            assert_eq!(m.less,d<next);
            let delta=if d<next {(&BigUint::from(1u8)<<224usize)+&d-&next}else{&d-&next};
            assert_eq!(m.delta,delta);expected[j]=wanted.clone();next=wanted;
        }
        for (o,src) in guards(c) {
            let j=e.iter().position(|e|e.1-2==src).unwrap();let operand=&expected[j];
            let mut q=BigUint::from(1u8);let target=(operand*3u8)/2u8;
            while q<target {q*=2u8;}
            let patch=p.owner_patch(o).unwrap();let cap=patch.spans.iter().find(|s|matches!(s.writer,Writer::Cap {context,..} if context==c)).unwrap();
            assert_eq!(number(&cap.values[1..225]),*operand);assert_eq!(number(&cap.values[740..805]),q);
            assert!(cap.values[1383..].iter().all(Zero::is_zero));
            assert!(patch.spans.iter().all(|s|s.start>=1000770),"Cap must not write MAX.R");
        }
    }
}

fn neighborhood(p:&Prepared,o:usize)->BTreeMap<usize,Fr> {
    let ts=terms(p.plan(),o);let mut needed=BTreeSet::from([o]);
    for (_,t) in &ts {needed.insert(t.gate.left/1048576);needed.insert(t.gate.right/1048576);}
    let mut values=BTreeMap::new();
    for owner in needed {
        let patch=p.owner_patch(owner).unwrap();let mut cells=OwnerCells::new(owner).unwrap();patch.apply(&mut cells).unwrap();
        for (wire,(_,v)) in cells.cells {assert!(values.insert(owner*1048576+wire,v).is_none());}
        assert!(values.insert(owner*1048576,Fr::zero()).is_none());
        for c in 0..2 {if let Some(j)=p.plan.max_index(c,owner) {
            let native=difficulty(p.plan.epochs[c][j].end);
            for k in 0..224 {
                let key=owner*1048576+987674+k;let value=Fr::from(native.bit(k as u64)as u64);
                if let Some(old)=values.insert(key,value) {assert_eq!(old,value);}
            }
        }}
    }values
}
fn residual(ts:&[(Writer,Term)],values:&BTreeMap<usize,Fr>)->Result<BTreeMap<usize,Fr>,String> {
    let mut out=BTreeMap::new();
    for (_,t) in ts {
        let g=&t.gate;let l=*values.get(&g.left).ok_or("missing physical left source")?;
        let r=*values.get(&g.right).ok_or("missing physical right source")?;
        *out.entry(t.row).or_insert(Fr::zero())+=g.c0+g.c1*l+g.c2*r+g.c3*l*r;
    }Ok(out)
}
#[test]
fn physical_selected_rows_residuals_activation_clipping_and_high_owner_bit() {
    let p=prepared();
    for o in [844670,844798,845759,845887,1048446,1048574,1048511,1048639,
        1827582,1827710,1827773,1827838,1827837,1827774] {
        let ts=terms(p.plan(),o);assert!(!ts.is_empty());let v=neighborhood(p,o);
        assert!(residual(&ts,&v).unwrap().values().all(Zero::is_zero),"honest owner {o}");
        let mut missing=v.clone();missing.remove(&ts[0].1.gate.left);
        assert!(residual(&ts,&missing).is_err());
    }
    let inactive=844671;assert!(terms(p.plan(),inactive).is_empty());assert!(p.owner_patch(inactive).unwrap().spans.is_empty());
    // Every imported bit gets an isolated, directly exercised residual negative.
    let o=845759;let ts=terms(p.plan(),o);let original=neighborhood(p,o);
    for k in 0..224 {
        let wanted=o*524288+357978+1383+k;
        let local:Vec<_>=ts.iter().filter(|(w,t)|*w==Writer::Cap {context:0,origin:o+1}&&t.row==wanted).cloned().collect();
        assert_eq!(local.len(),2);let mut bad=original.clone();
        let key=844670*1048576+999424+k;bad.insert(key,Fr::one()-bad[&key]);
        assert!(!residual(&local,&bad).unwrap()[&wanted].is_zero(),"imported bit {k}");
    }
}

// Brute-force owner equality sums over the independent full height calendar.
// Test-side O(epoch count) work; production coefficients use only O(H) kernels.
fn owner_weight(r:&[Fr],u:&[Fr],v:&[Fr],owners:impl Iterator<Item=(usize,usize)>)->Fr {
    owners.map(|(o,l)|independently_eq(r,o)*independently_eq(u,l)*independently_eq(v,o)).sum()
}
fn literal_boolean(ts:&[(Writer,Term)],r:usize,u:usize,v:usize)->[Fr;4] {
    let mut result=[Fr::zero();4];
    for (_,t) in ts {
        if (t.row,t.gate.left,t.gate.right)==(r,u,v) {
            for (sum,c) in result.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]) {*sum+=c;}
        }
    }result
}
fn coefficient_oracle(p:&Plan,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4] {
    let mut out=[Fr::zero();4];
    for c in 0..2 {
        let e=epochs(c);let g=guards(c);
        let ms=owner_weight(&r[19..],&u[20..],&v[20..],e.iter().map(|(_,b)|(b-2,b-2)));
        let mn=owner_weight(&r[19..],&u[20..],&v[20..],e.windows(2).map(|w|(w[0].1-2,w[1].1-2)));
        let cs=owner_weight(&r[19..],&u[20..],&v[20..],g.iter().map(|(o,_)|(*o,*o)));
        let ci=owner_weight(&r[19..],&u[20..],&v[20..],g.iter().copied());
        for o in [844670,845759] {
            for (w,t) in terms(p,o) {
                let (context,weight)=match w {
                    Writer::Max {context,..}=>(context,if t.gate.left/1048576!=o {mn}else{ms}),
                    Writer::Cap {context,..}=>(context,if t.gate.left/1048576!=o {ci}else{cs}),
                };if context!=c {continue;}
                let local=independently_eq(&r[..19],t.row%524288)*independently_eq(&u[..20],t.gate.left%1048576)
                    *independently_eq(&v[..20],t.gate.right%1048576)*weight;
                for (sum,coef) in out.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]) {*sum+=local*coef;}
            }
        }
    }out
}
#[test]
fn global_coefficients_match_independent_full_calendar_owner_sums() {
    let p=Plan::new();
    for seed in [3,59] {
        let r=point(seed,40);let u=point(seed+101,41);let v=point(seed+251,41);
        assert_eq!(p.coefficients(&r,&u,&v).unwrap(),coefficient_oracle(&p,&r,&u,&v));
    }
    assert!(p.coefficients(&point(1,39),&point(2,41),&point(3,41)).is_err());
}

#[test]
fn exact_boolean_tuple_channels_and_isolated_coordinate_mutations() {
    let p=Plan::new();
    for o in [844670,1048574,1827710,1827773,1827838,845759,1048639,1827837,1827774] {
        let ts=terms(&p,o);
        for t in ts.iter().filter(|(_,t)|t.gate.c1==-Fr::one()).take(3).chain(ts.iter().rev().take(3)) {
            let q=t.1.row;let l=t.1.gate.left;let rt=t.1.gate.right;
            let expected=ts.iter().filter(|(_,a)|(a.row,a.gate.left,a.gate.right)==(q,l,rt))
                .fold([Fr::zero();4],|mut a,(_,t)|{for (sum,b) in a.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]){*sum+=b;}a});
            assert_eq!(p.coefficients(&bits(q,40),&bits(l,41),&bits(rt,41)).unwrap(),expected);
        }
    }
    for (o,c,source_owner) in [(1827837,0,1826814),(1827774,1,1826686)] {
        let ts=terms(&p,o);let base=if c==0 {999424}else{1000097};
        let index=ts.iter().position(|(w,t)|matches!(w,Writer::Cap {context,..} if *context==c)
            && t.gate.left==source_owner*1048576+base+223).unwrap();
        let target=&ts[index];
        for axis in 0..8 {
            let mut bad=target.clone();match axis {0=>bad.1.gate.left+=1048576,
                1=>bad.1.gate.left^=1usize<<40,2=>bad.1.row^=1usize<<39,
                3=>bad.1.row+=1,4=>bad.1.gate.c1=-bad.1.gate.c1,
                5=>bad.1.gate.left=o.saturating_sub(1089)*1048576+base+223,
                6=>bad.1.gate.right=o*1048576,
                _=>bad.1.gate.left=source_owner*1048576+if c==0 {1000097+223}else{999424+223}};
            assert_ne!(bad.1,target.1,"coordinate fault {axis}");
            let wanted=(target.1.row,target.1.gate.left,target.1.gate.right);
            let before=p.coefficients(&bits(wanted.0,40),&bits(wanted.1,41),&bits(wanted.2,41)).unwrap();
            assert_eq!(before,literal_boolean(&ts,wanted.0,wanted.1,wanted.2));
            let mut changed=ts.clone();changed[index]=bad;
            let observed=literal_boolean(&changed,wanted.0,wanted.1,wanted.2);
            assert_ne!(before,observed,"mutated physical tuple at axis {axis}");
        }
    }
}

#[test]
fn candidate_rows_fail_closed_outside_the_high_component_band() {
    for start in [0,356632,393216,406406,475135,524000,usize::MAX] {
        assert!(ComponentRows::checked([start,475585],[476034,476554]).is_err(),"candidate start {start}");
    }
    assert!(ComponentRows::checked([475136,475585],[476034,476554]).is_ok());
    assert!(ComponentRows::checked([475136,475136],[476034,476554]).is_err());
}

#[test]
fn patches_reject_same_value_second_writer_wrong_identity_and_missing_cells() {
    let p=prepared();let o=845759;let patch=p.owner_patch(o).unwrap();
    let mut cells=OwnerCells::new(o).unwrap();assert!(cells.read(1000770).is_err());
    patch.apply(&mut cells).unwrap();let before=cells.cells.clone();
    assert!(patch.apply(&mut cells).is_err());assert_eq!(cells.cells,before);
    let mut wrong=OwnerCells::new(o+1).unwrap();assert!(patch.apply(&mut wrong).is_err());assert!(wrong.cells.is_empty());
    for axis in 0..5 {
        let mut bad=p.owner_patch(o).unwrap();match axis {0=>bad.spans[0].start+=1,
            1=>{bad.spans[0].values.pop();},2=>bad.spans[0].values[0]=Fr::from(2u8),
            3=>bad.spans[0].writer=Writer::Cap {context:2,origin:o+1},
            _=>bad.spans[0].writer=Writer::Cap {context:0,origin:o+2}};
        let mut clean=OwnerCells::new(o).unwrap();assert!(bad.apply(&mut clean).is_err());assert!(clean.cells.is_empty());
    }
    assert!(p.owner_patch(2097152).is_err());assert!(OwnerCells::new(2097152).is_err());
}

#[test]
fn eligible08_high_varying_score_dense_oracle_matches_sparse_endpoints_and_rejects_diagnostic() {
    let descriptor=CutDescriptor::eligible08();
    let difficulty_at=|height:usize| {
        const REGIME_CUT:usize=1_200_001;
        let block=(height-1)/128;
        let base=if height<REGIME_CUT {7_000_000_000_000_000_000u64}
            else {5_000_000_000_000_000_000u64};
        base+(block as u64)*1_000_000_000_000u64
    };
    let mut difficulties=Vec::with_capacity(LAST-FIRST+1);
    for height in FIRST..=LAST {
        // All D values are high, vary by scheduled epoch, and stay within the
        // local dyadic Cap profile: floor(3*D/2) <= 2^64.
        let d=difficulty_at(height);
        assert!(d>1u64<<62);
        assert!((u128::from(d)*3)/2<=1u128<<64);
        difficulties.push(d);
    }
    let input=|| difficulties.iter().copied().enumerate()
        .map(|(i,d)|(FIRST+i,BigUint::from(d)));
    let eligible=Prepared::from_d_iter_eligible08(input()).unwrap();

    // Independent dense height arrays: W is a cumulative sum; V is the
    // suffix maximum. The same synthetic D rule extends before FIRST so both
    // premodern anchors can be derived without borrowing implementation state.
    let mut work=vec![0u128;LAST+1];
    for height in 1..=LAST {
        work[height]=work[height-1]+u128::from(difficulty_at(height));
    }
    let mut suffix=vec![0u64;LAST+2];
    let mut maximum=0u64;
    for height in (1..=LAST).rev() {
        maximum=maximum.max(difficulty_at(height));suffix[height]=maximum;
    }
    let cap_scalar=|d:u64| {
        let target=(u128::from(d)*3)/2;
        let mut q=1u128;
        while q<target {q*=2;}
        q
    };

    // Independently replay all synthetic per-origin maxima through the two
    // premodern anchors. The fixture extends D deterministically to height 1;
    // this is a source-model counterexample, not native-history evidence.
    let mut premodern_r=[0u128;2];
    for context in 0..2 {
        let mut running=0u128;
        let mut first_anchor_r=None;
        for origin in descriptor.offset()+1..=845_759 {
            let v=cap_scalar(suffix[origin-descriptor.offset()]);
            let candidate=work[origin]
                +u128::from(descriptor.maturity_value(context,origin).unwrap())*v;
            running=running.max(candidate);
            if origin==417_791 {first_anchor_r=Some(running);}
        }
        let first_anchor_r=first_anchor_r.unwrap();
        assert!(first_anchor_r>0);
        assert!(running>=first_anchor_r);
        premodern_r[context]=running;
    }

    for context in 0..2 {
        let guard=descriptor.guards()[context];
        let start=descriptor.modern_start();
        let offset=descriptor.offset();
        let mut expected=vec![(start,start)];
        let mut first=start+1;
        while first<=guard {
            let last=(first+127).min(guard);
            expected.push((first,last));first=last+1;
        }
        assert_eq!(expected[0],(845_760,845_760));
        assert_eq!(expected[1],(845_761,845_888));
        let tail=expected.last().unwrap();
        assert_eq!(tail.1-tail.0+1,if context==0 {25}else{90});

        let actual=eligible.score_spans(context).unwrap();
        assert_eq!(actual.len(),expected.len());
        assert_eq!(actual.iter().map(|span|(span.first,span.last)).collect::<Vec<_>>(),expected);
        let maturity=descriptor.maturity_value(context,start).unwrap();
        let mut observed_caps=BTreeSet::new();
        // Carry R from premodern owner 845758 into first modern owner 845759.
        let mut dense_running=premodern_r[context];
        let mut sparse_running=premodern_r[context];
        for ((first,last),span) in expected.iter().copied().zip(&actual) {
            let source_height=first-offset;
            let v=cap_scalar(suffix[source_height]);
            assert_eq!(span.value,BigUint::from(v));
            observed_caps.insert(span.value.clone());

            let mut dense_span_max=0u128;
            for origin in first..=last {
                let candidate=work[origin]+u128::from(maturity)*v;
                dense_span_max=dense_span_max.max(candidate);
                dense_running=dense_running.max(candidate);
            }
            // Since W grows with each positive D and the descriptor holds V
            // fixed over this span, its endpoint is the independent sparse
            // candidate for the dense per-origin maximum.
            let sparse_candidate=work[last]+u128::from(maturity)*v;
            assert_eq!(dense_span_max,sparse_candidate);
            sparse_running=sparse_running.max(sparse_candidate);
            assert_eq!(sparse_running,dense_running,
                "dense versus sparse Score maximum at context {context}, endpoint {last}");
        }
        assert!(observed_caps.len()>=2,"varying suffix Cap values in context {context}");
        assert!(observed_caps.contains(&BigUint::from(1u128<<63)));
        assert!(observed_caps.contains(&BigUint::from(1u128<<64)));
    }

    // Diagnostic08 can agree on an early physical patch while its complete
    // source identity and clipped Score calendar differ from Eligible08.
    let diagnostic=Prepared::from_d_iter_with_descriptor(
        CutDescriptor::diagnostic08(),input()).unwrap();
    assert_eq!(eligible.owner_patch(844_670).unwrap(),diagnostic.owner_patch(844_670).unwrap());
    assert!(!eligible.source_replay_matches(&diagnostic));
}

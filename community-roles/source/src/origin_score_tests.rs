use ark_bn254::Fr;
use ark_ff::{One,Zero};
use num_bigint::{BigInt,BigUint};
use std::ops::Range;
use crate::{origin_score as words,origin_score_map::{Plan,Profile,Mode,GuardPolicy},sparse::Term};

fn n(x:u64)->BigUint{BigUint::from(x)}
fn pow(k:usize)->BigUint{BigUint::from(1u8)<<k}
fn reference_m(mode:Mode,origin:u64)->u64{
    match (mode,origin){(Mode::Sampled,1..=417791)=>43410,(Mode::Sampled,417792..=845759)=>23155,
        (Mode::Sampled,_)=>4995,(Mode::Exact,1..=417791)=>17867,(Mode::Exact,417792..=845759)=>9548,(Mode::Exact,_)=>2090}
}
fn set(x:&mut[Fr],rail:Range<usize>,value:&BigUint){
    assert!(value.bits()<=rail.len() as u64);for (i,w) in rail.enumerate(){x[w]=if value.bit(i as u64){Fr::one()}else{Fr::zero()};}
}
fn number(x:&[Fr],rail:Range<usize>)->BigUint{
    let mut out=n(0);for (i,w) in rail.enumerate(){assert!(x[w].is_zero()||x[w].is_one());if x[w].is_one(){out+=pow(i);}}out
}
// Independent BigInt assignment: no producer, emitter, coefficient or shift helper calls.
fn reference(plan:&Plan,first:u64,modes:&[Mode],w:&[BigUint],v:&[BigUint])->Vec<Vec<Fr>>{
    assert!(plan.slots()<=8,"bounded independent functional view only");
    let l=words::Layout::new();assert_eq!((w.len(),v.len()),(plan.count(),plan.count()));
    let mut view=Vec::with_capacity(plan.profiles()*plan.slots());
    for (profile,mode) in modes.iter().enumerate(){let mut previous=BigInt::from(0);
        for slot in 0..plan.slots(){let spec=plan.spec(profile,slot).unwrap();let mut x=vec![Fr::zero();words::INPUT];
            if spec.active{let wi=BigInt::from(w[slot].clone());let vi=BigInt::from(v[slot].clone());
                let a=&wi+&vi*BigInt::from(reference_m(*mode,first+slot as u64));
                for rail in [l.sw.clone(),l.w.clone()]{set(&mut x,rail,&w[slot]);}
                for rail in [l.sv.clone(),l.v.clone()]{set(&mut x,rail,&v[slot]);}
                let mut any=false;for bit in 0usize..65{any=any||v[slot].bit(bit as u64);x[l.or.start+bit]=Fr::from(u64::from(any));}
                set(&mut x,l.a.clone(),&a.to_biguint().unwrap());
                if spec.reducing{let select=a>previous;
                    let delta=if select{&a-&previous-BigInt::from(1)}else{&previous-&a};
                    let maximum=if select{a.clone()}else{previous.clone()};
                    set(&mut x,l.current.clone(),&a.to_biguint().unwrap());set(&mut x,l.p.clone(),&previous.to_biguint().unwrap());
                    set(&mut x,l.r.clone(),&maximum.to_biguint().unwrap());set(&mut x,l.d.clone(),&delta.to_biguint().unwrap());
                    x[l.s]=Fr::from(u64::from(select));previous=maximum;
                }
                if let Some(total)=spec.guard_total{let difference=BigInt::from(total)-a;
                    // An unsigned zero gap isolates the impossible negative guard.
                    if let Some(gap)=difference.to_biguint(){set(&mut x,l.gap.clone(),&gap);}}
            }view.push(x);
        }}view
}
fn failures(plan:&Plan,terms:&[Term],view:&[Vec<Fr>])->Vec<words::Failure>{
    words::failures(terms,plan.row_count(),|i|view[i/words::INPUT][i%words::INPUT])
}
fn positive(plan:&Plan,view:&[Vec<Fr>])->Vec<Term>{
    let terms=plan.terms().unwrap();plan.authenticate(&terms).unwrap();let errors=failures(plan,&terms,view);assert!(errors.is_empty(),"first failure {:?}",errors.first());terms
}
fn only(plan:&Plan,terms:&[Term],view:&[Vec<Fr>],label:&str,slot:usize)->Vec<words::Failure>{
    let errors=failures(plan,terms,view);assert!(!errors.is_empty(),"missing {label}");
    assert!(errors.iter().all(|e|e.label==label&&e.row/words::ROWS==slot),"first failure {:?}; isolated {label}/{slot}",errors.first());
    assert!(errors.iter().all(|e|!e.residual.is_zero()));errors
}
fn one_plan(first:u64,count:usize,prefix:usize,expected:BigUint,mode:Mode,guard:GuardPolicy)->Plan{
    Plan::new(first,count,vec![Profile{mode,prefix,expected,guard}]).unwrap()
}
fn erase(terms:&[Term],slot:usize,label:&str)->Vec<Term>{
    terms.iter().filter(|t|!(t.row/words::ROWS==slot&&words::group(label).contains(&(t.row%words::ROWS)))).cloned().collect()
}
fn basic_producer_and_geometry(){
    words::bounds().unwrap();let l=words::Layout::new();assert_eq!((l.gap.end,words::LIVE,words::INPUT,words::ROWS),(1994,1994,2048,8192));
    assert_eq!(words::GROUPS.iter().map(|(_,n)|n).sum::<usize>(),4208);
    let mode=Mode::Exact;let w=vec![n(3),n(9),n(5)];let v=vec![n(1);3];
    let plan=one_plan(2,3,3,n(17876),mode,GuardPolicy::Disabled);
    let view=reference(&plan,2,&[mode],&w,&v);let terms=positive(&plan,&view);
    assert_eq!((plan.input_log(),plan.row_log(),plan.input_len(),plan.row_count()),(13,15,8192,32768));
    assert_eq!(terms.len(),26369);assert_eq!(std::mem::size_of::<Term>(),152);
    let mut previous=n(0);for slot in 0..plan.slots(){let spec=plan.spec(0,slot).unwrap();
        let input=if slot<3{Some(words::ConditionalInputs{w:w[slot].clone(),v:v[slot].clone()})}else{None};
        let produced=words::produce(&spec,input.as_ref(),&previous).unwrap();assert_eq!(produced,view[slot]);
        if slot<3{previous=std::cmp::max(previous,&w[slot]+17867u64);}}
    for (slot,expected) in [(0,17870u64),(1,17876),(2,17876)]{assert_eq!(number(&view[slot],l.r.clone()),n(expected));}
    let mut bad=view.clone();bad[0][l.w.start]=Fr::one()-bad[0][l.w.start];
    assert!(failures(&plan,&terms,&bad).iter().any(|e|e.label=="aliases"));
    bad=view.clone();bad[3][words::INPUT-1]=Fr::one();only(&plan,&terms,&bad,"padding",3);
    bad=view.clone();bad[0][l.s]=Fr::from(2u8);assert!(failures(&plan,&terms,&bad).iter().any(|e|e.label=="boolean"));
    let (segments,templates)=plan.analytic_cost().unwrap();assert!(segments<=8);assert!(templates>0);
    assert_eq!(8192usize*32+2*2048*32,393216);assert_eq!(view.len()*words::INPUT*32,262144);
}
fn positive_range_guard_and_ties(){
    let l=words::Layout::new();let top=pow(64);let a=&top*17867u64;
    let plan=one_plan(2,1,1,a.clone(),Mode::Exact,GuardPolicy::Require{prefix:1,total:a.clone()});
    let view=reference(&plan,2,&[Mode::Exact],&[n(0)],&[top.clone()]);let terms=positive(&plan,&view);
    assert_eq!(number(&view[0],l.v.clone()),top);assert_eq!(number(&view[0],l.gap.clone()),n(0));
    let above=&top+1u8;let above_a=&above*17867u64;
    let above_plan=one_plan(2,1,1,above_a.clone(),Mode::Exact,GuardPolicy::Disabled);
    let above_view=reference(&above_plan,2,&[Mode::Exact],&[n(0)],&[above]);
    let above_terms=above_plan.terms().unwrap();only(&above_plan,&above_terms,&above_view,"range",0);
    assert!(failures(&above_plan,&erase(&above_terms,0,"range"),&above_view).is_empty());
    let zero_plan=one_plan(2,1,1,n(7),Mode::Exact,GuardPolicy::Disabled);
    let zero_view=reference(&zero_plan,2,&[Mode::Exact],&[n(7)],&[n(0)]);let zero_terms=zero_plan.terms().unwrap();
    only(&zero_plan,&zero_terms,&zero_view,"positive",0);
    assert!(failures(&zero_plan,&erase(&zero_terms,0,"positive"),&zero_view).is_empty());
    let mut bad=view.clone();bad[0][l.or.start]=Fr::one();assert!(failures(&plan,&terms,&bad).iter().any(|e|e.label=="positive"));
    // This malformed operand also breaks its integer aliases/score; not isolated Boolean evidence.
    bad=view.clone();bad[0][l.v.start]=Fr::from(2u8);assert!(failures(&plan,&terms,&bad).iter().any(|e|e.label=="boolean"));
    let integer_v=pow(63)+1u8;let integer_a=&integer_v*17867u64;
    let boolean_plan=one_plan(2,1,1,integer_a,Mode::Exact,GuardPolicy::Disabled);
    let mut nonboolean=reference(&boolean_plan,2,&[Mode::Exact],&[n(0)],&[integer_v]);
    let boolean_terms=positive(&boolean_plan,&nonboolean);
    // 2*2^62 replaces2^63 in BOTH aliased V rails. The integer is unchanged;
    // OR already equals1 from bit0, so only the two Boolean rows fail.
    for rail in [l.sv.clone(),l.v.clone()]{nonboolean[0][rail.start+62]=Fr::from(2u8);nonboolean[0][rail.start+63]=Fr::zero();}
    let boolean_errors=only(&boolean_plan,&boolean_terms,&nonboolean,"boolean",0);
    assert_eq!(boolean_errors.len(),2);assert!(boolean_errors.iter().all(|e|e.residual==Fr::from(2u8)));
    assert!(failures(&boolean_plan,&erase(&boolean_terms,0,"boolean"),&nonboolean).is_empty());
    for delta in [-1i64,0,1]{let total=if delta<0{&a-1u8}else{&a+delta as u8};
        let guard=one_plan(2,1,1,a.clone(),Mode::Exact,GuardPolicy::Require{prefix:1,total});
        let x=reference(&guard,2,&[Mode::Exact],&[n(0)],&[top.clone()]);let ts=guard.terms().unwrap();
        if delta<0{only(&guard,&ts,&x,"guard",0);}else{assert!(failures(&guard,&ts,&x).is_empty());}}
    let max_w=pow(224)-1u8;let largest=&max_w+&top*43410u64;
    let maximum=one_plan(2,1,1,largest.clone(),Mode::Sampled,GuardPolicy::Disabled);
    positive(&maximum,&reference(&maximum,2,&[Mode::Sampled],&[max_w.clone()],&[top.clone()]));
    let under=one_plan(2,1,1,largest,Mode::Sampled,GuardPolicy::Require{prefix:1,total:max_w.clone()});
    only(&under,&under.terms().unwrap(),&reference(&under,2,&[Mode::Sampled],&[max_w],&[top]),"guard",0);
    let tie=one_plan(2,2,2,n(17870),Mode::Exact,GuardPolicy::Disabled);
    let tie_view=reference(&tie,2,&[Mode::Exact],&[n(3),n(3)],&[n(1),n(1)]);let tie_terms=positive(&tie,&tie_view);
    assert_eq!((tie_view[1][l.s],number(&tie_view[1],l.d.clone())),(Fr::zero(),n(0)));
    let mut wrong=tie_view.clone();wrong[1][l.s]=Fr::one();only(&tie,&tie_terms,&wrong,"maximum",1);
    wrong=tie_view.clone();wrong[1][l.d.start]=Fr::one();only(&tie,&tie_terms,&wrong,"maximum",1);
    let linked=one_plan(2,2,2,n(17871),Mode::Exact,GuardPolicy::Disabled);
    let mut wrong_link=reference(&linked,2,&[Mode::Exact],&[n(3),n(3)],&[n(1),n(1)]);
    set(&mut wrong_link[1],l.p.clone(),&n(17871));set(&mut wrong_link[1],l.r.clone(),&n(17871));
    set(&mut wrong_link[1],l.d.clone(),&n(1));wrong_link[1][l.s]=Fr::zero();
    let linked_terms=linked.terms().unwrap();only(&linked,&linked_terms,&wrong_link,"predecessor",1);
    assert!(failures(&linked,&erase(&linked_terms,1,"predecessor"),&wrong_link).is_empty());
}
fn isolated_reducer_and_omissions(){
    // Active score without guard/reducer consumers isolates the producer equation.
    let score_layout=words::Layout::new();
    let score_plan=one_plan(2,1,0,n(0),Mode::Exact,GuardPolicy::Disabled);
    let mut wrong_score=reference(&score_plan,2,&[Mode::Exact],&[n(7)],&[n(1)]);
    let score_terms=positive(&score_plan,&wrong_score);
    set(&mut wrong_score[0],score_layout.a.clone(),&n(17875));
    let score_errors=only(&score_plan,&score_terms,&wrong_score,"score",0);
    assert_eq!(score_errors.len(),1);assert_eq!(score_errors[0].row,words::group("score").start);
    assert_eq!(score_errors[0].residual,Fr::one());
    let missing_score=erase(&score_terms,0,"score");
    assert!(failures(&score_plan,&missing_score,&wrong_score).is_empty());
    assert!(score_plan.authenticate(&missing_score).is_err());
    let l=words::Layout::new();let plan=one_plan(2,3,3,n(17872),Mode::Exact,GuardPolicy::Disabled);
    let w=vec![n(3),n(9),n(5)];let v=vec![n(1);3];let mut view=reference(&plan,2,&[Mode::Exact],&w,&v);
    // Full positive-V score producer stays m+[3,9,5]. Forge only the consumer import.
    let currents=[17870u64,17870,17872];let mut previous=0u64;
    for (slot,a) in currents.into_iter().enumerate(){let select=a>previous;
        let maximum=previous.max(a);let gap=if select{a-previous-1}else{previous-a};
        set(&mut view[slot],l.current.clone(),&n(a));set(&mut view[slot],l.p.clone(),&n(previous));
        set(&mut view[slot],l.r.clone(),&n(maximum));set(&mut view[slot],l.d.clone(),&n(gap));view[slot][l.s]=Fr::from(u64::from(select));previous=maximum;
    }
    let terms=plan.terms().unwrap();let errors=only(&plan,&terms,&view,"current",1);
    assert_eq!(errors[0].row,words::ROWS+words::group("current").start+1);
    assert!(failures(&plan,&erase(&terms,1,"current"),&view).is_empty());
    // Isolated reducer component has literal scores[3,9,5], not a false full-score claim.
    let pure=one_plan(2,3,3,n(9),Mode::Exact,GuardPolicy::Disabled);
    let mut pure_view=reference(&pure,2,&[Mode::Exact],&w,&v);previous=0;
    for (slot,a) in [3u64,9,5].into_iter().enumerate(){let select=a>previous;let maximum=a.max(previous);
        set(&mut pure_view[slot],l.a.clone(),&n(a));set(&mut pure_view[slot],l.current.clone(),&n(a));
        set(&mut pure_view[slot],l.p.clone(),&n(previous));set(&mut pure_view[slot],l.r.clone(),&n(maximum));
        set(&mut pure_view[slot],l.d.clone(),&n(if select{a-previous-1}else{previous-a}));pure_view[slot][l.s]=Fr::from(u64::from(select));previous=maximum;
    }
    let subset=pure.terms().unwrap().into_iter().filter(|t|["boolean","current","predecessor","maximum","terminal","padding","max-mask"].contains(&words::row_label(t.row))).collect::<Vec<_>>();
    assert!(failures(&pure,&subset,&pure_view).is_empty());
    for (slot,r) in [(0,3u64),(1,9),(2,9)]{assert_eq!(number(&pure_view[slot],l.r.clone()),n(r));}
    let early=one_plan(2,2,2,n(43419),Mode::Sampled,GuardPolicy::Require{prefix:2,total:n(43413)});
    let early_view=reference(&early,2,&[Mode::Sampled],&[n(9),n(0)],&[n(1),n(1)]);let early_terms=early.terms().unwrap();
    only(&early,&early_terms,&early_view,"guard",0);
    assert!(failures(&early,&erase(&early_terms,0,"guard"),&early_view).is_empty());
    // One immutable profile total supplies constants at every active owner.
    let shared=one_plan(2,3,3,n(17876),Mode::Exact,GuardPolicy::Require{prefix:3,total:n(17877)});
    let mut shared_view=reference(&shared,2,&[Mode::Exact],&w,&v);let shared_terms=positive(&shared,&shared_view);
    let false_total_gap=number(&shared_view[1],l.gap.clone())+1u8;set(&mut shared_view[1],l.gap.clone(),&false_total_gap);
    only(&shared,&shared_terms,&shared_view,"guard",1);
    let mut wrong_total_program=shared_terms.clone();let guard_row=words::ROWS+words::group("guard").start;
    let constant=wrong_total_program.iter_mut().find(|t|t.row==guard_row&&!t.gate.c0.is_zero()).unwrap();constant.gate.c0+=Fr::one();
    assert!(failures(&shared,&wrong_total_program,&shared_view).is_empty());
    assert!(shared.authenticate(&wrong_total_program).is_err());
    // Last score is below the existing maximum, so output value alone cannot
    // expose omission of the final genuine origin's complete constraint block.
    let complete_view=reference(&shared,2,&[Mode::Exact],&w,&v);
    let missing_final=shared_terms.iter().filter(|t|t.row/words::ROWS!=2).cloned().collect::<Vec<_>>();
    assert!(failures(&shared,&missing_final,&complete_view).is_empty());
    let wire_reads=std::cell::Cell::new(0usize);
    let admitted=shared.authenticate(&missing_final).map(|_|words::failures(&missing_final,shared.row_count(),|i|{
        wire_reads.set(wire_reads.get()+1);complete_view[i/words::INPUT][i%words::INPUT]
    }));
    assert!(admitted.is_err());assert_eq!(wire_reads.get(),0);
}
fn cuts_profiles_and_symbolic_boundaries(){
    let w=vec![n(3),n(5),n(9)];let v=vec![n(1);3];let mode=Mode::Exact;
    let cut=one_plan(2,3,2,n(17872),mode,GuardPolicy::Disabled);let view=reference(&cut,2,&[mode],&w,&v);positive(&cut,&view);
    let guard_prefix=one_plan(2,3,3,n(17876),mode,GuardPolicy::Require{prefix:1,total:n(17870)});
    positive(&guard_prefix,&reference(&guard_prefix,2,&[mode],&w,&v));
    let wrong=one_plan(2,3,2,n(17876),mode,GuardPolicy::Disabled);only(&wrong,&wrong.terms().unwrap(),&view,"terminal",1);
    let empty=one_plan(2,0,0,n(0),mode,GuardPolicy::Disabled);positive(&empty,&reference(&empty,2,&[mode],&[],&[]));
    let wrong_empty=one_plan(2,0,0,n(1),mode,GuardPolicy::Disabled);
    only(&wrong_empty,&wrong_empty.terms().unwrap(),&reference(&wrong_empty,2,&[mode],&[],&[]),"terminal",0);
    let origin=one_plan(1,1,1,n(17867),mode,GuardPolicy::Disabled);
    positive(&origin,&reference(&origin,1,&[mode],&[n(0)],&[n(1)]));
    let bad_origin=one_plan(1,1,1,n(17868),mode,GuardPolicy::Disabled);
    only(&bad_origin,&bad_origin.terms().unwrap(),&reference(&bad_origin,1,&[mode],&[n(1)],&[n(1)]),"origin-zero",0);
    for first in [417791u64,845759]{let modes=[Mode::Sampled,Mode::Exact];let profiles=modes.iter().map(|mode|Profile{mode:*mode,prefix:2,
        expected:n(reference_m(*mode,first)),guard:GuardPolicy::Disabled}).collect();let both=Plan::new(first,2,profiles).unwrap();
        let both_view=reference(&both,first,&modes,&[n(0),n(0)],&[n(1),n(1)]);positive(&both,&both_view);
        assert_eq!(both.input_base(1,0).unwrap(),both.slots()*words::INPUT);
        assert_ne!(number(&both_view[0],words::Layout::new().a.clone()),number(&both_view[2],words::Layout::new().a.clone()));
        let sampled=one_plan(first,2,2,n(reference_m(Mode::Sampled,first)),Mode::Sampled,GuardPolicy::Disabled);
        let exact_values=reference(&sampled,first,&[Mode::Exact],&[n(0),n(0)],&[n(1),n(1)]);
        assert!(failures(&sampled,&sampled.terms().unwrap(),&exact_values).iter().any(|e|e.label=="score"));
    }
    for origin in [845760u64,845761,1827840]{let (work,_,shift)=crate::origin_score_map::model_source(origin,false).unwrap();
        let (header,w_shift,h_shift)=crate::origin_score_map::model_source(origin,true).unwrap();
        assert_eq!(work-shift,origin-1090);assert_eq!(header-h_shift,origin-1090);assert_eq!(header-w_shift,work);
        assert_ne!(work-1087,origin-1090);assert_ne!(work-1089,origin-1090);
        let low=origin-1088;let range=low..=origin+2;assert_eq!(range.clone().count(),1091);
        assert!(range.contains(&low)&&range.contains(&(origin+2)));assert!(!((low+1)..=origin+2).contains(&low));
    }
    let mut callbacks=0usize;assert!(cut.read(99,0,|_|{callbacks+=1;}).is_err());assert_eq!(callbacks,0);
    assert!(cut.read(0,cut.slots(),|_|{callbacks+=1;}).is_err());assert_eq!(callbacks,0);
    assert!(cut.read(0,3,|_|{callbacks+=1;}).unwrap().is_empty());assert_eq!(callbacks,0);
    assert!(Plan::new(0,1,vec![Profile{mode,prefix:1,expected:n(0),guard:GuardPolicy::Disabled}]).is_err());
    assert!(Plan::new(2,1,vec![Profile{mode,prefix:2,expected:n(0),guard:GuardPolicy::Disabled}]).is_err());
    assert!(Plan::new(2,1,vec![Profile{mode,prefix:1,expected:pow(225),guard:GuardPolicy::Disabled}]).is_err());
    assert!(Plan::new(2,1,vec![Profile{mode,prefix:1,expected:n(0),guard:GuardPolicy::Require{prefix:1,total:pow(224)}}]).is_err());
    assert!(Plan::new(2,1,vec![Profile{mode,prefix:1,expected:n(0),guard:GuardPolicy::Require{prefix:2,total:n(1)}}]).is_err());
    assert!(Plan::new(u64::MAX-2,3,vec![Profile{mode,prefix:3,expected:n(0),guard:GuardPolicy::Disabled}]).is_err());
    for axis in 0..5 {
        let mut invalid=cut.spec(0,0).unwrap();
        let expected=match axis {
            0=>{invalid.maturity=1<<16;"local constant range before sink"},
            1=>{invalid.expected=pow(225);"local constant range before sink"},
            2=>{invalid.guard_total=Some(pow(224));"local guard range before sink"},
            3=>{invalid.active=false;"inactive reduction before sink"},
            _=>{invalid.reducing=false;invalid.terminal=true;"terminal scope before sink"},
        };
        let mut sinks=0usize;
        let rejected=words::emit_local(&invalid,|_|{sinks+=1;});
        assert_eq!(rejected.unwrap_err(),expected);assert_eq!(sinks,0,"admission axis {axis}");
    }
}
fn independent_eq(point:&[Fr],index:usize)->Fr{let mut out=Fr::one();for (bit,z) in point.iter().enumerate(){out*=if index&(1usize<<bit)==0{Fr::one()-z}else{*z};}out}
fn direct(terms:&[Term],r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{
    let mut out=[Fr::zero();4];for t in terms{let g=&t.gate;
        let weight=independent_eq(r,t.row)*independent_eq(u,g.left)*independent_eq(v,g.right);
        for (sum,c) in out.iter_mut().zip([g.c0,g.c1,g.c2,g.c3]){*sum+=weight*c;}}out
}
fn point(k:usize,seed:u64)->Vec<Fr>{(0..k).map(|b|Fr::from(seed+3*b as u64)).collect()}
fn analytic_tuples_and_resources(){
    for first in [2u64,417791,845759]{let plan=one_plan(first,3,2,n(0),Mode::Exact,GuardPolicy::Require{prefix:3,total:n(100000)});
        let terms=plan.terms().unwrap();let r=point(plan.row_log(),2);let u=point(plan.input_log(),7);let v=point(plan.input_log(),11);
        let wanted=plan.coefficients(&r,&u,&v).unwrap();assert_eq!(wanted,direct(&terms,&r,&u,&v));
        for channel in 0..4{let mut changed=terms.clone();let t=changed.iter_mut().find(|t|![t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3][channel].is_zero()).unwrap();
            match channel{0=>t.gate.c0+=Fr::one(),1=>t.gate.c1+=Fr::one(),2=>t.gate.c2+=Fr::one(),_=>t.gate.c3+=Fr::one()}
            assert!(plan.authenticate(&changed).is_err());
            assert_ne!(direct(&changed,&r,&u,&v),wanted);}
        for axis in 0..3{let mut changed=terms.clone();match axis{0=>changed[0].row+=1,1=>changed[0].gate.left+=1,_=>changed[0].gate.right+=1}
            assert!(plan.authenticate(&changed).is_err());
            assert_ne!(direct(&changed,&r,&u,&v),wanted);}
        let mut ordered=terms.clone();ordered.swap(0,1);assert!(plan.authenticate(&ordered).is_err());assert_eq!(direct(&ordered,&r,&u,&v),wanted);
        let boolean=|k:usize,i:usize|(0..k).map(|b|Fr::from(((i>>b)&1)as u64)).collect::<Vec<_>>();
        let t=&terms[terms.len()/2];let rr=boolean(plan.row_log(),t.row);let uu=boolean(plan.input_log(),t.gate.left);let vv=boolean(plan.input_log(),t.gate.right);
        assert_eq!(plan.coefficients(&rr,&uu,&vv).unwrap(),direct(&terms,&rr,&uu,&vv));
        assert!(plan.coefficients(&r[..r.len()-1],&u,&v).is_err());
    }
    let both=Plan::new(417791,2,vec![Profile{mode:Mode::Sampled,prefix:2,expected:n(0),guard:GuardPolicy::Disabled},
        Profile{mode:Mode::Exact,prefix:1,expected:n(0),guard:GuardPolicy::Disabled}]).unwrap();
    let r=point(both.row_log(),3);let u=point(both.input_log(),5);let v=point(both.input_log(),13);
    assert_eq!(both.coefficients(&r,&u,&v).unwrap(),direct(&both.terms().unwrap(),&r,&u,&v));
    let symbolic=one_plan(1,1<<21,1810905,n(0),Mode::Exact,GuardPolicy::Disabled);
    assert!(symbolic.terms().is_err());let (segments,templates)=symbolic.analytic_cost().unwrap();
    assert!(segments<=8&&templates<8*10000);let r=point(symbolic.row_log(),2);let u=point(symbolic.input_log(),7);let v=point(symbolic.input_log(),11);
    assert!(symbolic.coefficients(&r,&u,&v).is_ok());
    let (_,_,header)=crate::origin_score_map::model_source(845760,true).unwrap();assert_eq!(header,1089);
}
#[test]
fn portable_score_and_prefix_constraints(){
    basic_producer_and_geometry();positive_range_guard_and_ties();isolated_reducer_and_omissions();
    cuts_profiles_and_symbolic_boundaries();analytic_tuples_and_resources();
}

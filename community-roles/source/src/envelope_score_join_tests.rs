//! Independent local integer assignment and bounded producer/consumer controls.
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use num_bigint::{BigInt,BigUint};
use num_traits::ToPrimitive;
use std::{collections::BTreeSet,ops::Range};
use crate::{certified_legacy_bound as legacy,certified_modern_cap as modern,
    envelope_cover::{self as cover,Cover,Descriptor},envelope_score_join::{self as join,Declaration,Plan},
    origin_score as words,origin_score_map::{Mode,GuardPolicy},sparse::Term};
fn n(s:&str)->BigUint{BigUint::parse_bytes(s.as_bytes(),10).unwrap()}
fn p(e:usize)->BigUint{BigUint::from(1u8)<<e}
fn bitword(x:&mut[Fr],rail:Range<usize>,value:&BigUint){assert!(value.bits()<=rail.len() as u64);for (b,w) in rail.enumerate(){x[w]=Fr::from(u64::from(value.bit(b as u64)));}}
fn global_word(x:&mut[Fr],base:usize,rail:Range<usize>,value:&BigUint){bitword(x,base+rail.start..base+rail.end,value);}
fn ceiling(value:&BigUint)->BigUint{(0usize..=64).map(p).find(|v|v>=value).unwrap()}
fn fixture(prefix:usize,mode:Mode)->Declaration{
    let m=match mode{Mode::Exact=>17867u64,Mode::Sampled=>43410};
    Declaration{legacy:legacy::Inputs{d:[n("1000000000"),n("100000000000")],t:[1,2,3]},
        bound:n("255212307692307695"),modern_d:BigUint::from(5u8),modern_q:BigUint::from(8u8),
        work:[BigUint::zero(),BigUint::from(7u8)],mode,prefix,
        expected:if prefix==0{BigUint::zero()}else{p(58)*m+if prefix==2{7u8}else{0}},guard:GuardPolicy::Disabled}
}
// Geometry is read from Layout only. No scalar, producer, emitter, coefficient or
// claimed-value helper participates in the reference assignment below.
fn limb(value:&BigUint,index:usize)->u64{((value>>(16*index))&BigUint::from(65535u64)).to_u64().unwrap()}
fn carry_word(x:&mut[Fr],rail:&Range<usize>,column:usize,width:usize,value:&BigUint){bitword(x,rail.start+(column-1)*width..rail.start+column*width,value);}
fn subtract_reference(x:&mut[Fr],a:&BigUint,b:&BigUint,s:&legacy::Sub){
    let width=s.diff.len();let modulus=p(width);let difference=(&modulus+a-b-1u8)%&modulus;
    x[s.initial]=Fr::one();bitword(x,s.diff.clone(),&difference);
    for bit in 0..width{let base=p(bit+1);x[s.borrow.start+bit]=Fr::from(u64::from(a%&base < b%&base+1u8));}
}
fn reference_legacy(input:&legacy::Inputs)->(Vec<Fr>,BigUint){
    let l=legacy::Layout::new();let mut x=vec![Fr::zero();8192];
    for k in 0..2{global_word(&mut x,l.source.start,224*k..224*(k+1),&input.d[k]);bitword(&mut x,l.d(k),&input.d[k]);}
    for k in 0..3{global_word(&mut x,l.source.start,448+64*k..448+64*(k+1),&BigUint::from(input.t[k]));bitword(&mut x,l.time(k),&BigUint::from(input.t[k]));}
    let deltas=[BigUint::from(input.t[1]-input.t[0]),BigUint::from(input.t[2]-input.t[1]),BigUint::from(input.t[2]-input.t[1]+64)];
    for k in 0..3{bitword(&mut x,l.delta[k].clone(),&deltas[k]);for j in 1..4{let base=p(16*j);
        let (a,b)=if k<2{(deltas[k].clone(),BigUint::from(input.t[k]))}else{(deltas[1].clone(),BigUint::from(64u8))};
        x[l.tc[k].start+j-1]=Fr::from((((&a%&base)+(&b%&base))/&base).to_u64().unwrap());}}
    for k in 0..2{subtract_reference(&mut x,&deltas[k],&BigUint::zero(),&l.positive[k]);}
    let mut quotients=Vec::new();
    for k in 0..2{
        let numerator=&input.d[k]*122880000u64;let denominator=&deltas[if k==0{0}else{2}];
        let quotient=&numerator/denominator;let remainder=&numerator%denominator;
        bitword(&mut x,l.numerator[k].clone(),&numerator);bitword(&mut x,l.q[k].clone(),&quotient);bitword(&mut x,l.rem[k].clone(),&remainder);
        for j in 1..16{let base=p(16*j);carry_word(&mut x,&l.nc[k],j,27,&((&input.d[k]%&base)*122880000u64/&base));}
        // Direct truncated integer convolution, independent of recursive producer carries.
        for j in 1..19{let base=p(16*j);let mut lower=&remainder%&base;
            for qi in 0..16{for di in 0..4{if qi+di<j{lower+=BigUint::from(limb(&quotient,qi))*limb(denominator,di)*p(16*(qi+di));}}}
            carry_word(&mut x,&l.pc[k],j,19,&(lower/base));}
        subtract_reference(&mut x,denominator,&remainder,&l.rem_sub[k]);quotients.push(quotient);
    }
    let a=(&quotients[1]<<1usize)+3u8;let c=&quotients[0]+1199990374400u64;
    let b=if a>c{&a-&quotients[0]}else{BigUint::from(1199990374400u64)};
    bitword(&mut x,l.a.clone(),&a);bitword(&mut x,l.c.clone(),&c);bitword(&mut x,l.b.clone(),&b);
    for j in 1..16{let base=p(16*j);let aa=((&quotients[1]<<1usize)%&base)+BigUint::from(3u8)%&base;
        let cc=(&quotients[0]%&base)+(BigUint::from(1199990374400u64)%&base);
        x[l.ac[0].start+j-1]=Fr::from((aa/&base).to_u64().unwrap());x[l.ac[1].start+j-1]=Fr::from((cc/&base).to_u64().unwrap());
        if a>c{x[l.selected.start+j-1]=Fr::from((((&b%&base)+(&quotients[0]%&base))/&base).to_u64().unwrap());}}
    subtract_reference(&mut x,&a,&c,&l.compare);x[l.selector]=Fr::from(u64::from(a>c));(x,b)
}
fn reference_modern(d:&BigUint)->(Vec<Fr>,BigUint){
    let l=modern::Layout::new();let mut x=vec![Fr::zero();2048];let floor=(d*3u8)/2u8;let q=ceiling(&floor);let h=&q>>1usize;
    bitword(&mut x,l.source.clone(),d);bitword(&mut x,l.operand.clone(),d);bitword(&mut x,l.p.clone(),&floor);
    x[l.r]=Fr::from(((d*3u8)%2u8).to_u64().unwrap());let exponent=q.bits() as usize-1;x[l.s.start+exponent]=Fr::one();
    bitword(&mut x,l.q.clone(),&q);bitword(&mut x,l.prev.clone(),&h);bitword(&mut x,l.hi.clone(),&(&q-&floor));
    bitword(&mut x,l.low.clone(),&(&floor-&h-1u8));bitword(&mut x,l.positive.clone(),&(d-1u8));(x,q)
}
fn reference_cover(c:&Cover,values:&[BigUint],u:&BigUint)->Vec<Fr>{
    let l=c.layout();let mut x=vec![Fr::zero();2048];let half=u>>1usize;
    for (rail,value) in l.candidates.iter().zip(values){bitword(&mut x,rail.clone(),value);}
    bitword(&mut x,l.u.clone(),u);bitword(&mut x,l.half.clone(),&half);x[l.hot.start+u.bits() as usize-1]=Fr::one();
    // For an intentionally inflated U, select the real maximal candidate and leave
    // a Boolean zero minimal gap: only strict minimality then fails.
    let j=values.iter().enumerate().max_by_key(|(_,v)|*v).unwrap().0;
    x[l.select.start+j]=Fr::one();bitword(&mut x,l.selected.clone(),&values[j]);
    for (value,rail) in values.iter().zip(&l.gaps){bitword(&mut x,rail.clone(),&(u-value));}
    let delta=if &values[j]>&half{&values[j]-&half-1u8}else{BigUint::zero()};bitword(&mut x,l.minimal.clone(),&delta);x
}
fn reference_scores(x:&mut[Fr],d:&Declaration,u:&BigUint){
    let l=words::Layout::new();let maturity=match d.mode{Mode::Exact=>17867u64,Mode::Sampled=>43410};let mut previous=BigUint::zero();
    for s in 0..2{let base=join::SCORE_BASE+s*2048;let a=&d.work[s]+u*maturity;let reducing=s<d.prefix;
        for rail in [l.sw.clone(),l.w.clone()]{global_word(x,base,rail,&d.work[s]);}
        for rail in [l.sv.clone(),l.v.clone()]{global_word(x,base,rail,u);}
        let mut seen=false;for b in 0..65{seen|=u.bit(b);x[base+l.or.start+b as usize]=Fr::from(u64::from(seen));}global_word(x,base,l.a.clone(),&a);
        if reducing{let select=a>previous;let delta=if select{&a-&previous-1u8}else{&previous-&a};let result=if select{a.clone()}else{previous.clone()};
            global_word(x,base,l.current.clone(),&a);global_word(x,base,l.p.clone(),&previous);global_word(x,base,l.r.clone(),&result);global_word(x,base,l.d.clone(),&delta);
            x[base+l.s]=Fr::from(u64::from(select));previous=result;}
        if let GuardPolicy::Require{prefix,total}=&d.guard{if s<*prefix{global_word(x,base,l.gap.clone(),&(total-&a));}}
    }
}
fn reference(d:&Declaration)->Vec<Fr>{
    let (old,b)=reference_legacy(&d.legacy);let (m,q)=reference_modern(&d.modern_d);
    let values=[n("1199990374400"),n("122702199259136"),b,d.legacy.d[0].clone(),d.legacy.d[1].clone(),d.modern_d.clone(),q];
    let u=ceiling(values.iter().max().unwrap());let c=Cover::new(Descriptor::Envelope).unwrap();let cv=reference_cover(&c,&values,&u);
    let mut x=vec![Fr::zero();join::INPUT];x[..8192].copy_from_slice(&old);x[8192..10240].copy_from_slice(&m);x[10240..12288].copy_from_slice(&cv);
    reference_scores(&mut x,d,&u);x
}
fn failures(terms:&[Term],x:&[Fr],range:Range<usize>)->Vec<usize>{
    let mut rows=vec![Fr::zero();range.len()];for t in terms{assert!(range.contains(&t.row));let g=&t.gate;rows[t.row-range.start]+=g.c0+g.c1*x[g.left]+g.c2*x[g.right]+g.c3*x[g.left]*x[g.right];}
    rows.iter().enumerate().filter_map(|(i,v)|if v.is_zero(){None}else{Some(range.start+i)}).collect()
}
fn only(terms:&[Term],x:&[Fr],range:Range<usize>,expected:Range<usize>,label:&str){
    let bad=failures(terms,x,range);assert!(!bad.is_empty(),"{label}: no failed row");assert!(bad.iter().all(|r|expected.contains(r)),"{label}: first={} all={bad:?}",bad[0]);
}
fn cover_terms(c:&Cover)->Vec<Term>{let mut count=0;c.emit(|_|count+=1);let mut out=Vec::with_capacity(count);c.emit(|t|out.push(t));out}
fn without_rows(terms:&[Term],range:Range<usize>)->Vec<Term>{
    let mut out=Vec::with_capacity(terms.len());out.extend(terms.iter().filter(|t|!range.contains(&t.row)).cloned());
    assert_eq!(out.capacity(),terms.len());out
}
fn cover_erasure(c:&Cover,terms:&[Term],x:&[Fr],group:&str){
    let r=c.group(group);only(terms,x,cover::ROW_BASE..cover::ROW_BASE+cover::ROWS,r.clone(),group);
    assert!(c.verify(terms,|i|x[i]).unwrap_err().starts_with(group));
    let mutant=without_rows(terms,r);
    assert!(failures(&mutant,x,cover::ROW_BASE..cover::ROW_BASE+cover::ROWS).is_empty());let mut reads=0;
    assert!(c.verify(&mutant,|i|{reads+=1;x[i]}).is_err());assert_eq!(reads,0,"cover erasure must reject before lookup");
}
fn joint_erasure(plan:&Plan,terms:&[Term],x:&[Fr],range:Range<usize>,label:&str){
    only(terms,x,0..join::ROWS,range.clone(),label);assert!(plan.verify(terms,|i|x[i]).unwrap_err().starts_with(label));
    let mutant=without_rows(terms,range);assert!(failures(&mutant,x,0..join::ROWS).is_empty());
    let mut reads=0;assert!(plan.verify(&mutant,|i|{reads+=1;x[i]}).is_err());assert_eq!(reads,0,"joint erasure before lookup");
}
fn literal_fixture_and_joint_producers(){
    let y1=BigInt::from(1000000000u64)*122880000u64;let future=BigInt::from(100000000000u64)*122880000u64;
    let ymax=&future/65u8;assert_eq!((&future%65u8).to_u64().unwrap(),10);
    assert_eq!(y1.to_string(),"122880000000000000");assert_eq!(ymax.to_string(),"189046153846153846");
    assert_eq!((ymax*2u8-y1+3u8).to_string(),"255212307692307695");
    assert_eq!(p(58).to_string(),"288230376151711744");assert_eq!((p(58)-n("255212307692307695")).to_string(),"33018068459404049");
    assert_eq!((n("255212307692307695")-p(57)-1u8).to_string(),"111097119616451822");
    assert_eq!(0x6f98d5000000u64,122702199259136);assert_eq!(0x011765000000u64,1199990374400);
    let d=fixture(2,Mode::Exact);let plan=Plan::new(d.clone()).unwrap();let terms=plan.terms().unwrap();let x=reference(&d);
    assert_eq!((x.len(),terms.len()),(16384,93441));assert_eq!(d.expected,n("5149812130702633730055"));
    assert_eq!(plan.produce().unwrap(),x);assert!(failures(&terms,&x,0..join::ROWS).is_empty());plan.verify(&terms,|i|x[i]).unwrap();
    assert_eq!(plan.cover().layout().live,1906);assert_eq!(plan.cover().group("padding").end-cover::ROW_BASE,3910);
    assert_eq!(plan.cover().group("high-zero").len(),665);
    drop(terms);drop(x);
    let sampled=fixture(2,Mode::Sampled);let plan=Plan::new(sampled.clone()).unwrap();let sampled_x=reference(&sampled);
    let terms=plan.terms().unwrap();plan.verify(&terms,|i|sampled_x[i]).unwrap();assert_eq!(plan.produce().unwrap(),sampled_x);
}
fn cover_field_profile_and_faults(){
    let d=fixture(2,Mode::Exact);let c=Cover::new(Descriptor::Envelope).unwrap();let terms=cover_terms(&c);let original=reference(&d);
    for (candidate,source,bit) in [(2usize,5668usize,65usize),(2,5668,252),(3,641,65),(4,865,223),(5,8192+225,65)]{
        let mut x=original.clone();x[cover::BASE+c.layout().candidates[candidate].start+bit]=Fr::one();x[source+bit]=Fr::one();cover_erasure(&c,&terms,&x,"high-zero");}
    // Preserve the entire weighted minimal gap while introducing one Fr2 digit.
    // All non-Boolean rows remain consistent; the actual Boolean factory alone fails.
    let k=(c.layout().minimal.start..c.layout().minimal.end-1).find(|w|original[cover::BASE+*w].is_zero()&&original[cover::BASE+*w+1]==Fr::one()).unwrap();
    let mut x=original.clone();x[cover::BASE+k]=Fr::from(2u8);x[cover::BASE+k+1]=Fr::zero();cover_erasure(&c,&terms,&x,"boolean");drop(x);
    for (wire,group) in [(c.layout().hot.start+58,"boolean"),(c.layout().select.start+2,"boolean"),(c.layout().minimal.start,"boolean")]{
        let mut x=original.clone();x[cover::BASE+wire]=Fr::from(2u8);
        // The factory Boolean row itself is isolated by its actual row subset.
        let boolean=terms.iter().filter(|t|c.group("boolean").contains(&t.row)).cloned().collect::<Vec<_>>();
        only(&boolean,&x,c.group("boolean"),cover::ROW_BASE+wire..cover::ROW_BASE+wire+1,group);
    }
    let mut x=original.clone();x[cover::BASE+c.layout().candidates[1].start+6]=Fr::one()-x[cover::BASE+c.layout().candidates[1].start+6];
    // Literal anchors are authoritative independently of the unchanged dyadic cap.
    let anchors=terms.iter().filter(|t|c.group("constant-anchors").contains(&t.row)).cloned().collect::<Vec<_>>();
    assert!(!failures(&anchors,&x,c.group("constant-anchors")).is_empty());
    drop(x);drop(anchors);
    let wrong=BigUint::from(122702194049536u64);let values=[n("1199990374400"),wrong,d.bound.clone(),d.legacy.d[0].clone(),d.legacy.d[1].clone(),d.modern_d.clone(),d.modern_q.clone()];
    let local=reference_cover(&c,&values,&p(58));let mut x=original.clone();x[10240..12288].copy_from_slice(&local);drop(local);cover_erasure(&c,&terms,&x,"constant-anchors");drop(x);
    assert_eq!(122702199259136u64-122702194049536u64,5209600);
    let values=[n("1199990374400"),n("122702199259136"),&d.bound+1u8,d.legacy.d[0].clone(),d.legacy.d[1].clone(),d.modern_d.clone(),d.modern_q.clone()];
    let local=reference_cover(&c,&values,&p(58));let mut x=original.clone();x[10240..12288].copy_from_slice(&local);drop(local);cover_erasure(&c,&terms,&x,"source-alias");drop(x);
    let mut x=original.clone();global_word(&mut x,cover::BASE,c.layout().selected.clone(),&(&d.bound+1u8));
    global_word(&mut x,cover::BASE,c.layout().minimal.clone(),&(&d.bound-p(57)));cover_erasure(&c,&terms,&x,"selected");drop(x);
    let mut x=original.clone();x[cover::BASE+c.layout().live]=Fr::one();cover_erasure(&c,&terms,&x,"padding");drop(x);
    for (name,wire) in [("source-alias",c.layout().candidates[2].start),("padding",c.layout().live)]{
        let mut x=original.clone();x[cover::BASE+wire]=Fr::one()-x[cover::BASE+wire];
        let subset=terms.iter().filter(|t|c.group(name).contains(&t.row)).cloned().collect::<Vec<_>>();assert!(!failures(&subset,&x,c.group(name)).is_empty());}
}
fn dyadic_boundaries_and_selectors(){
    for value in [BigUint::one(),p(64)]{
        let c=Cover::new(Descriptor::Unit{candidate:value.clone()}).unwrap();let terms=cover_terms(&c);let local=reference_cover(&c,&[value.clone()],&value);
        assert_eq!(terms.len(),3479);
        let mut x=vec![Fr::zero();join::INPUT];x[cover::BASE..cover::BASE+2048].copy_from_slice(&local);
        assert_eq!(local,c.produce(&[value.clone()]).unwrap());c.verify(&terms,|i|x[i]).unwrap();
        if value.is_one(){assert!(c.layout().half.clone().all(|i|local[i].is_zero()));}
    }
    let c=Cover::new(Descriptor::Unit{candidate:BigUint::from(5u8)}).unwrap();let terms=cover_terms(&c);
    for u in [BigUint::from(8u8),BigUint::from(16u8)]{let local=reference_cover(&c,&[BigUint::from(5u8)],&u);let mut x=vec![Fr::zero();join::INPUT];x[cover::BASE..cover::BASE+2048].copy_from_slice(&local);
        if u==BigUint::from(8u8){c.verify(&terms,|i|x[i]).unwrap();}else{cover_erasure(&c,&terms,&x,"minimal");}}
    // Multiple Boolean exponent selectors can create a non-dyadic U=6. Keep
    // every rail equation coherent so only the onehot sum rejects it.
    let mut local=reference_cover(&c,&[BigUint::from(5u8)],&BigUint::from(6u8));local[c.layout().hot.start+1]=Fr::one();
    let mut x=vec![Fr::zero();join::INPUT];x[10240..12288].copy_from_slice(&local);cover_erasure(&c,&terms,&x,"onehot");drop(x);drop(local);
    // U=2^64+1 is never represented by a permitted onehot. Keep U=2^64,
    // candidate=2^64+1, and all other rails Boolean/coherent; only cover fails.
    let value=p(64)+1u8;let c=Cover::new(Descriptor::Unit{candidate:value.clone()}).unwrap();let terms=cover_terms(&c);assert!(c.produce(&[value.clone()]).is_err());
    let l=c.layout();let mut x=vec![Fr::zero();join::INPUT];global_word(&mut x,cover::BASE,l.candidates[0].clone(),&value);
    global_word(&mut x,cover::BASE,l.u.clone(),&p(64));global_word(&mut x,cover::BASE,l.half.clone(),&p(63));global_word(&mut x,cover::BASE,l.selected.clone(),&value);
    global_word(&mut x,cover::BASE,l.minimal.clone(),&p(63));x[cover::BASE+l.hot.start+64]=Fr::one();x[cover::BASE+l.select.start]=Fr::one();cover_erasure(&c,&terms,&x,"cover");
    assert!(Cover::new(Descriptor::Unit{candidate:BigUint::zero()}).is_err());assert!(Cover::new(Descriptor::Unit{candidate:p(65)}).is_err());
}
fn bridge_isolation(){
    let d=fixture(0,Mode::Exact);let plan=Plan::new(d.clone()).unwrap();let terms=plan.terms().unwrap();let original=reference(&d);plan.verify(&terms,|i|original[i]).unwrap();
    let mut x=original.clone();reference_scores(&mut x,&d,&p(59));joint_erasure(&plan,&terms,&x,join::BRIDGE_ROWS..join::BRIDGE_ROWS+130,"V-bridge");drop(x);
    let mut changed=d.clone();changed.work[1]=BigUint::from(8u8);let mut x=original.clone();reference_scores(&mut x,&changed,&p(58));
    joint_erasure(&plan,&terms,&x,join::BRIDGE_ROWS+130..41538,"W-anchor");drop(x);
    let mut x=original.clone();let candidate=cover::BASE+plan.cover().layout().candidates[6].start;let old=8192+740;
    // q is changed only in the source alias consumer to isolate that boundary.
    x[candidate]=Fr::one()-x[candidate];let subset=terms.iter().filter(|t|plan.cover().group("source-alias").contains(&t.row)).cloned().collect::<Vec<_>>();
    assert!(!failures(&subset,&x,plan.cover().group("source-alias")).is_empty());assert_eq!(x[old],original[old]);
    drop(x);drop(subset);
    // Inflated U and a self-consistent downstream score in prefix0 isolate cover minimality.
    let values=[n("1199990374400"),n("122702199259136"),d.bound.clone(),d.legacy.d[0].clone(),d.legacy.d[1].clone(),d.modern_d.clone(),d.modern_q.clone()];
    let local=reference_cover(plan.cover(),&values,&p(59));let mut x=original.clone();x[10240..12288].copy_from_slice(&local);drop(local);reference_scores(&mut x,&d,&p(59));
    joint_erasure(&plan,&terms,&x,plan.cover().group("minimal"),"minimal");drop(x);
    // Omit precisely the dominant B coverage row. U=2^47 covers every other
    // candidate; RESET is a genuine strict-half witness. The relaxed program
    // accepts the same complete downstream assignment, while canonical binding
    // rejects the omission before reading even one wire.
    let l=plan.cover().layout();let u=p(47);let half=p(46);let mut x=original.clone();
    global_word(&mut x,cover::BASE,l.u.clone(),&u);global_word(&mut x,cover::BASE,l.half.clone(),&half);
    for w in l.hot.clone(){x[cover::BASE+w]=Fr::zero();}x[cover::BASE+l.hot.start+47]=Fr::one();
    for w in l.select.clone(){x[cover::BASE+w]=Fr::zero();}x[cover::BASE+l.select.start+1]=Fr::one();
    global_word(&mut x,cover::BASE,l.selected.clone(),&values[1]);global_word(&mut x,cover::BASE,l.minimal.clone(),&(&values[1]-&half-1u8));
    for (j,gap) in l.gaps.iter().enumerate(){global_word(&mut x,cover::BASE,gap.clone(),&if j==2{BigUint::zero()}else{&u-&values[j]});}
    reference_scores(&mut x,&d,&u);let row=plan.cover().group("cover").start+2;
    joint_erasure(&plan,&terms,&x,row..row+1,"cover");
}
fn program_and_callback_controls(){
    let d=fixture(2,Mode::Exact);let plan=Plan::new(d.clone()).unwrap();let terms=plan.terms().unwrap();let x=reference(&d);
    for kind in 0..7{let mut mutant=terms.clone();match kind{
        0=>mutant.retain(|t|!plan.cover().group("cover").contains(&t.row)),
        1=>mutant.retain(|t|!plan.cover().group("high-zero").contains(&t.row)),
        2=>mutant.retain(|t|!(join::SCORE_ROWS+8192..join::SCORE_ROWS+16384).contains(&t.row)),
        3=>mutant.swap(0,1),4=>mutant[0].gate.c0+=Fr::one(),5=>mutant[0].gate.left+=1,_=>{mutant.pop();}}
        let mut reads=0;assert!(plan.verify(&mutant,|i|{reads+=1;x[i]}).is_err());assert_eq!(reads,0,"program kind {kind}");}
    let mut mutated=d.clone();mutated.prefix=1;mutated.expected=p(58)*17867u64;let different=Plan::new(mutated).unwrap();let mut reads=0;
    assert!(different.verify(&terms,|i|{reads+=1;x[i]}).is_err());assert_eq!(reads,0);
    let mut mutated=d.clone();mutated.mode=Mode::Sampled;let different=Plan::new(mutated).unwrap();let mut reads=0;
    assert!(different.verify(&terms,|i|{reads+=1;x[i]}).is_err());assert_eq!(reads,0);
    // Complete candidate omission uses the actual B candidate's coverage row.
    let row=plan.cover().group("cover").start+2;let mutant=without_rows(&terms,row..row+1);let mut reads=0;
    assert!(plan.verify(&mutant,|i|{reads+=1;x[i]}).is_err());assert_eq!(reads,0);
    drop(mutant);drop(x);
    // A correct flat final maximum still cannot license removing its final owner.
    let mut flat=d;flat.work[1]=BigUint::zero();flat.expected=p(58)*17867u64;let flat_plan=Plan::new(flat.clone()).unwrap();let canonical=flat_plan.terms().unwrap();let flat_x=reference(&flat);
    flat_plan.verify(&canonical,|i|flat_x[i]).unwrap();drop(terms);
    let mutant=without_rows(&canonical,join::SCORE_ROWS+8192..join::BRIDGE_ROWS);
    assert!(failures(&mutant,&flat_x,0..join::ROWS).is_empty());let mut reads=0;assert!(flat_plan.verify(&mutant,|i|{reads+=1;flat_x[i]}).is_err());assert_eq!(reads,0);
}
fn admission_before_sink(){
    for axis in 0..10{let mut d=fixture(2,Mode::Exact);match axis{
        0=>d.legacy.d[0]=p(224),1=>d.legacy.t=[1,1,3],2=>d.bound=p(253),3=>d.modern_d=BigUint::zero(),
        4=>d.modern_d=p(64),5=>d.modern_q=p(64)+1u8,6=>d.work[1]=p(224),7=>d.work[0]=BigUint::one(),
        8=>d.prefix=3,_=>d.guard=GuardPolicy::Require{prefix:2,total:p(224)}}
        let mut count=0;assert!(Plan::emit(d,|_|count+=1).is_err(),"admission axis {axis}");assert_eq!(count,0);}
    let mut d=fixture(0,Mode::Exact);d.expected=p(225);let mut count=0;assert!(Plan::emit(d,|_|count+=1).is_err());assert_eq!(count,0);
    let mut d=fixture(0,Mode::Exact);d.guard=GuardPolicy::Require{prefix:3,total:BigUint::zero()};let mut count=0;assert!(Plan::emit(d,|_|count+=1).is_err());assert_eq!(count,0);
    assert!(Plan::new(fixture(0,Mode::Exact)).unwrap().coefficients(&[],&[],&[]).is_err());
}
fn guards_and_upstream_failures(){
    for prefix in [1usize,2]{let mut d=fixture(2,Mode::Exact);let total=p(58)*17867u64+if prefix==2{7u8}else{0};
        d.guard=GuardPolicy::Require{prefix,total};let plan=Plan::new(d.clone()).unwrap();let terms=plan.terms().unwrap();let x=reference(&d);
        assert_eq!(terms.len(),join::TERMS+226*prefix);
        plan.verify(&terms,|i|x[i]).unwrap();assert_eq!(plan.produce().unwrap(),x);}
    // One shared total: origin1 passes by3, origin2 fails by4. Keep all other
    // groups coherent, including the exact terminal and the original W anchors.
    let mut d=fixture(2,Mode::Exact);d.guard=GuardPolicy::Require{prefix:2,total:p(58)*17867u64+3u8};
    let plan=Plan::new(d.clone()).unwrap();let terms=plan.terms().unwrap();let mut no_guard=d.clone();no_guard.guard=GuardPolicy::Disabled;
    let mut x=reference(&no_guard);let l=words::Layout::new();global_word(&mut x,join::SCORE_BASE,l.gap.clone(),&BigUint::from(3u8));
    let guard_row=join::SCORE_ROWS+words::ROWS+words::group("guard").start;
    joint_erasure(&plan,&terms,&x,guard_row..guard_row+1,"guard");
    // Mutating only the later owner's literal total into its own advised total
    // repairs that residual, but exact program comparison refuses the substitution.
    let mut mutant=terms.clone();let constant=mutant.iter_mut().find(|t|t.row==guard_row&&!t.gate.c0.is_zero()).unwrap();constant.gate.c0+=Fr::from(4u8);
    assert!(failures(&mutant,&x,0..join::ROWS).is_empty());let mut reads=0;assert!(plan.verify(&mutant,|i|{reads+=1;x[i]}).is_err());assert_eq!(reads,0);drop(mutant);
    // Early-failure/later-pass is impossible for the fixed two-origin fixture:
    // A1=mU, A2=mU+7. General nonmonotone-window guard controls remain the prior
    // primitive's scope, not a claimed new native/global guard result.
    assert!(p(58)*17867u64 < p(58)*17867u64+7u8);drop(terms);drop(x);
    for output in ["B","q"]{let mut d=fixture(2,Mode::Exact);if output=="B"{d.bound+=1u8;}else{d.modern_q+=1u8;}
        let plan=Plan::new(d).unwrap();let terms=plan.terms().unwrap();let x=plan.produce().unwrap();let bad=failures(&terms,&x,0..join::ROWS);
        let labels=bad.iter().map(|r|plan.row_label(*r)).collect::<BTreeSet<_>>();
        if output=="B"{assert_eq!(labels,BTreeSet::from(["legacy"]));}else{assert_eq!(labels,BTreeSet::from(["modern","source-alias"]));}
        assert!(plan.verify(&terms,|i|x[i]).is_err()); // These are attributed upstream controls, not single-row claims.
    }
}
fn literal_weights(point:&[Fr])->Vec<Fr>{
    let mut table=vec![Fr::one()];for z in point{let mut next=Vec::with_capacity(table.len()*2);for old in &table{next.push(*old*(Fr::one()-z));}for old in &table{next.push(*old*z);}table=next;}table
}
fn tuple_oracle(terms:&[Term],r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{
    let row=literal_weights(r);let left=literal_weights(u);let right=literal_weights(v);let mut out=[Fr::zero();4];
    for t in terms{let g=&t.gate;let eq=row[t.row]*left[g.left]*right[g.right];out[0]+=eq*g.c0;out[1]+=eq*g.c1;out[2]+=eq*g.c2;out[3]+=eq*g.c3;}out
}
fn coeff_channels_and_placeholders(){
    let plan=Plan::new(fixture(2,Mode::Exact)).unwrap();let terms=plan.terms().unwrap();
    let point=|len:usize,offset:usize|->Vec<Fr>{(0..len).map(|i|Fr::from((i+offset+2) as u64)).collect()};
    let r=point(16,0);let u=point(14,1);let v=point(14,2);
    assert_eq!(plan.coefficients(&r,&u,&v).unwrap(),tuple_oracle(&terms,&r,&u,&v));
    drop(r);drop(u);drop(v);
    // Boolean points select actual tuple coordinates, including nonzero literal,
    // bilinear/second-linear channels and both ends of the cross-block V alias.
    // Numeric coordinates are an independent namespace oracle, not emitter picks.
    let positive=Fr::one();let negative=-positive;let zero=Fr::zero();
    let probes=[
        ("W literal",41314usize,10240usize,10240usize,0usize,[negative,zero,zero,zero]),
        ("OR nonlinear",26860,12866,12802,3,[zero,negative,negative,positive]),
        ("V destination",41018,12570,10240,1,[zero,positive,zero,zero]),
        ("V source",41018,11418,10240,1,[zero,negative,zero,zero]),
    ];
    let boolean_point=|len:usize,index:usize|->Vec<Fr>{assert!(index<1usize<<len);(0..len).map(|b|Fr::from(((index>>b)&1) as u64)).collect()};
    for (name,row,left,right,channel,expected) in probes{
        assert!(row<41538&&left<join::INPUT&&right<join::INPUT,"{name}: active extent");
        let r=boolean_point(16,row);let u=boolean_point(14,left);let v=boolean_point(14,right);
        let oracle=tuple_oracle(&terms,&r,&u,&v);
        assert_eq!(oracle,expected,"{name}: exact active tuple channels");
        assert!(!oracle[channel].is_zero(),"{name}: vacuous coefficient probe");
        for active in 0..4{if !expected[active].is_zero(){assert!(!oracle[active].is_zero(),"{name}: vacuous active channel {active}");}}
        assert_eq!(plan.coefficients(&r,&u,&v).unwrap(),oracle,"{name}: Boolean differential");
    }
    let literal=terms.iter().find(|t|t.row>=join::BRIDGE_ROWS+130&&!t.gate.c0.is_zero()).unwrap();
    assert_eq!((literal.gate.left,literal.gate.right),(cover::BASE,cover::BASE));
    let r=vec![Fr::from(2u8);16];let u=vec![Fr::from(3u8);14];let v=vec![Fr::from(5u8);14];
    let weight=|i:usize,p:&[Fr]|->Fr{let mut w=Fr::one();for (b,z) in p.iter().enumerate(){w*=if i>>b&1==1{*z}else{Fr::one()-z};}w};
    let actual=weight(literal.row,&r)*weight(literal.gate.left,&u)*weight(literal.gate.right,&v)*literal.gate.c0;
    let incorrect=weight(literal.row,&r)*literal.gate.c0;assert_ne!(actual,incorrect,"c0 is not a coordinate-free channel");
    let extent=terms.iter().map(|t|t.row).max().unwrap()+1;assert_eq!(extent,41538);
    assert_eq!((std::mem::size_of::<Fr>(),std::mem::size_of::<crate::gkr::Gate>(),std::mem::size_of::<Term>()),(32,144,152));
    assert_eq!(join::TERMS*std::mem::size_of::<Term>(),14203032);
    let names=terms.iter().map(|t|plan.row_label(t.row)).collect::<BTreeSet<_>>();assert!(names.contains("V-bridge")&&names.contains("W-anchor")&&names.contains("high-zero"));
}
#[test]
fn bounded_envelope_to_early_score(){
    literal_fixture_and_joint_producers();cover_field_profile_and_faults();dyadic_boundaries_and_selectors();
    bridge_isolation();program_and_callback_controls();admission_before_sink();guards_and_upstream_failures();coeff_channels_and_placeholders();
}

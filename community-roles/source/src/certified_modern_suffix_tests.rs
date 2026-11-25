//! One bounded semantic/source/coefficient join. Expected assertions are not RSS measurements.
use ark_bn254::Fr;
use ark_ff::{BigInteger, Field, One, PrimeField, Zero};
use num_bigint::BigUint;
use crate::{certified_modern_suffix as s, certified_modern_cap as old_cap,
    circuit::CompressionLayout, gkr::Gate, sparse::Term, suffix_max,
    transcript::Transcript, work_tree_layout::{Baseline,CoreCounts,Endpoints,Inventory},
    work_tree_work as work};
use s::{AdmittedSuffix,Descriptor,Error,LocalWeights,PackedSuffix,Port,Row,Scan,Tuple,Wire};

fn power(b:usize)->BigUint{BigUint::from(1u8)<<b}
fn put(x:&mut PackedSuffix,owner:u64,start:usize,width:usize,n:&BigUint){
    assert!(n.bits()<=width as u64);for b in 0..width{x.set(s::native(owner,start+b),n.bit(b as u64)).unwrap();}}
fn number(read:impl Fn(usize)->Fr,start:usize,width:usize)->BigUint{
    let mut n=BigUint::zero();for b in 0..width{let x=read(start+b);assert!(x.is_zero()||x.is_one());if x.is_one(){n+=power(b);}}n}
fn fixture(which:usize)->PackedSuffix{
    assert!(which<3);let mut x=PackedSuffix::zeroed();let mut next=BigUint::zero();
    for slot in (0..s::ACTIVE).rev(){let owner=s::FIRST+slot as u64;
        let high=match which{0=>slot==s::ACTIVE-1,1=>slot==0,_=>slot==0||slot==s::ACTIVE-1};
        let bits=if high{0x05174876}else{0x043B9ACA};let d=work::native_decode(bits).unwrap();
        assert_eq!(d,BigUint::from(if high{99999940608u64}else{1000000000u64}));
        put(&mut x,owner,987162,32,&BigUint::from(bits));put(&mut x,owner,987674,224,&d);
        x.set(s::native(owner,987898+(bits>>24) as usize),true).unwrap();put(&mut x,owner,988154,224,&(&d-1u8));
        let selected=d<next;let maximum=if selected{next.clone()}else{d.clone()};
        let delta=if selected{power(224)+&d-&next}else{&d-&next};
        put(&mut x,owner,999424,224,&maximum);put(&mut x,owner,999648,224,&next);put(&mut x,owner,999872,224,&delta);
        x.set(s::native(owner,1000096),selected).unwrap();next=maximum;
    }
    for origin in s::I0..s::I0+64{let m=number(|w|x.read(s::native(origin-1090,w)).unwrap(),999424,224);
        let temporary=old_cap::producer(&m).unwrap();assert_eq!((temporary.len(),temporary.capacity()),(2048,2048));
        for (w,b) in temporary.iter().enumerate(){assert!(b.is_zero()||b.is_one());x.set(s::cap(origin,w),b.is_one()).unwrap();}
        drop(temporary);
    }
    assert_eq!((x.frames.len()*8,x.caps.len()*8),(376832,16384));x.framing().unwrap();x
}
fn minimal_baseline()->Baseline{
    let core=CoreCounts{used_bits:0,padded_bits:0,residual_rows:0,padded_rows:0,terms:0,maximum_degree:0,
        internal_zero_bits:0,terms_blake2b256:String::new(),sparse_dimension24:false,sparse_base_terms_2pow20:false};
    let inventory=Inventory{schema:String::new(),baseline_id:String::new(),contract_sha256:String::new(),
        source_sha256_pins_for_archive:Vec::new(),core,banks:Vec::new(),endpoint_fields:Vec::new(),free_ranges:Vec::new(),
        remaining_bits:0,retired:Vec::new(),checked_retired_rows:0,checked_retired_terms:0,old_boundary_terms:0,
        unrelated_terms_retained:0,old_boundary_blake2b256:String::new(),descriptor_blake2b256:String::new(),
        partial_arithmetic_reservation_bits:0,pending:Vec::new(),retained_capacity_bytes:0,inspected_template_peak_capacity_bytes:0};
    let compression=CompressionLayout{state:[[0;64];8],message:[[0;64];16],counter:[0;64],final_flag:0,
        output:[[0;64];8],used_input_len:0};
    Baseline{inventory,compression,endpoints:Endpoints::new(),header_alias_wires:Vec::new()}
}
fn retained_work_row(row:usize)->bool{row<32||(480..1434).contains(&row)}
fn convert(t:&Term,family:u8,owner:u64)->Tuple{let g=&t.gate;Tuple{row:Row{family,owner,local:t.row as u32},
    left:if family==2{s::cap(owner,g.left)}else{s::native(owner,g.left)},
    right:if family==2{s::cap(owner,g.right)}else{s::native(owner,g.right)},c:[g.c0,g.c1,g.c2,g.c3]}}
fn authenticate_decoder(reference:&[Term])->Result<(),Error>{if reference.len()!=2145{return Err(Error::TupleCount);}
    let mut index=0;let mut equal=true;s::emit_decoder(s::FIRST,true,|t|{equal &=t==convert(&reference[index],0,s::FIRST);index+=1;});
    if equal{Ok(())}else{Err(Error::TupleFields)}}
fn field_counts(reference:&[Term])->[u64;4]{let mut c=[0;4];for t in reference{for (x,v) in c.iter_mut().zip([t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]){*x+=u64::from(!v.is_zero());}}c}
fn mutate_tuple(reference:&mut [Term],kind:usize){match kind{
    0=>reference.swap(0,1),1=>reference[0].row+=1,2=>reference[0].gate.left+=1,
    3=>reference[0].gate.right+=1,4=>reference[0].gate.c0+=Fr::one(),5=>reference[0].gate.c1+=Fr::one(),
    6=>reference[0].gate.c2+=Fr::one(),_=>reference[0].gate.c3+=Fr::one()}}

struct ReferencePoint {local:LocalWeights,native:[Vec<Fr>;3],cap:[Vec<Fr>;3],tags:[[Fr;2];2],families:[Fr;4]}
impl ReferencePoint {
    fn new(r:&[Fr],u:&[Fr],v:&[Fr])->Self{let local=LocalWeights::new(r,u,v).unwrap();assert_eq!(local.payload(),494736);
        let native=[(s::FIRST..s::FIRST+2048).map(|o|s::eq(&r[12..32],o)).collect(),
            (s::FIRST..s::FIRST+2048).map(|o|s::eq(&u[20..40],o)).collect(),
            (s::FIRST..s::FIRST+2048).map(|o|s::eq(&v[20..40],o)).collect()];
        let cap=[(s::I0..s::I0+64).map(|o|s::eq(&r[12..32],o)).collect(),
            (s::I0..s::I0+64).map(|o|s::eq(&u[20..40],o)).collect(),
            (s::I0..s::I0+64).map(|o|s::eq(&v[20..40],o)).collect()];
        let out=Self{local,native,cap,tags:[[Fr::one()-u[40],u[40]],[Fr::one()-v[40],v[40]]],
            families:std::array::from_fn(|i|s::eq(&r[32..34],i as u64))};
        assert_eq!((out.native.iter().map(Vec::capacity).sum::<usize>()+out.cap.iter().map(Vec::capacity).sum::<usize>())*32,202752);out
    }
    fn owner(&self,t:Tuple)->Fr{
        let rw=if t.row.family==2{self.cap[0][(t.row.owner-s::I0) as usize]}else{self.native[0][(t.row.owner-s::FIRST) as usize]};
        let axis=|w:Wire,j:usize|if w.tag()==1{self.cap[j][(w.owner()-s::I0) as usize]}else{self.native[j][(w.owner()-s::FIRST) as usize]};
        rw*axis(t.left,1)*axis(t.right,2)*self.families[t.row.family as usize]*self.tags[0][t.left.tag()]*self.tags[1][t.right.tag()]
    }
}
#[derive(Default)]
struct Oracle {counts:Scan,coeff:[Fr;4],previous:Option<Row>}
impl Oracle {
    fn add(&mut self,t:Tuple,p:&ReferencePoint){self.counts.terms+=1;if self.previous!=Some(t.row){self.counts.rows+=1;self.previous=Some(t.row);}
        let w=p.owner(t)*p.local.local(t);for j in 0..4{self.counts.channels[j]+=u64::from(!t.c[j].is_zero());self.coeff[j]+=w*t.c[j];}}
}
fn point(len:usize,a:u64,b:u64)->Vec<Fr>{(0..len).map(|k|Fr::from(a*k as u64+b)).collect()}
fn callable_work_oracle(p:&ReferencePoint,out:&mut Oracle){
    let base=minimal_baseline();let e=&base.endpoints;
    let endpoint_capacity=[&e.raw,&e.length,&e.n_bits,&e.height,&e.lower,&e.upper,&e.work,&e.exponent,&e.work_minus_one,
        &e.leaf,&e.node_left,&e.node_right,&e.node,&e.profile,&e.count,&e.position,&e.level].iter().map(|v|v.capacity()).sum::<usize>();
    assert_eq!(endpoint_capacity,6690);assert_eq!(endpoint_capacity*std::mem::size_of::<usize>(),53520);
    assert_eq!(std::mem::size_of::<CompressionLayout>(),16912);
    let boundary=work::compile(&base,work::WorkProfile::new(3,[0;32],[0;28]).unwrap()).unwrap();
    let report=work::count(&boundary).unwrap();let literal=&report["local_literal_templates"];
    for (key,value) in [("genuine_rows",1435),("genuine_terms",3265),("padding_rows",1152),("padding_terms",1152)]{
        assert_eq!(literal[key].as_u64(),Some(value));}
    assert_eq!(report["retained_local_term_capacity_bytes"].as_u64(),Some(1310720));
    let link_bytes=boundary.links().iter().map(|f|(f.left_wires.capacity()+f.right_wires.capacity())*8).sum::<usize>();
    assert_eq!(report["retained_link_wire_capacity_bytes"].as_u64(),Some(link_bytes as u64));
    assert_eq!(boundary.groups().len(),16);
    let group_string_payload=boundary.groups().iter().map(|g|g.name.capacity()).sum::<usize>();
    let link_string_payload=boundary.links().iter().map(|f|f.name.capacity()).sum::<usize>();
    let link_constant_payload=boundary.links().iter().filter_map(|f|f.constants.as_ref()).map(Vec::capacity).sum::<usize>();
    assert!(group_string_payload<1024&&link_string_payload<256&&link_constant_payload==448);
    // Public count consumes and drops its 4417-Term hash temporary internally.
    assert_eq!(4417*std::mem::size_of::<Term>(),671384);assert_eq!(1310720+671384,1982104);
    assert_eq!((4096+8192)*160,1966080);drop(report);
    let mut reference=Vec::with_capacity(2145);boundary.emit_slot(0,|t|{if retained_work_row(t.row){reference.push(t);}}).unwrap();
    assert_eq!((reference.len(),reference.capacity(),reference.capacity()*std::mem::size_of::<Term>()),(2145,2145,326040));
    assert_eq!(field_counts(&reference),[2,1477,0,1176]);authenticate_decoder(&reference).unwrap();
    for kind in 0..8{let saved0=reference[0].clone();let saved1=reference[1].clone();mutate_tuple(&mut reference,kind);
        assert_eq!(authenticate_decoder(&reference),Err(Error::TupleFields));reference[0]=saved0;reference[1]=saved1;}
    assert_eq!(authenticate_decoder(&reference[..2144]),Err(Error::TupleCount));
    for owner in s::FIRST..s::FIRST+1153{for t in &reference{out.add(convert(t,0,owner),p);}}
    // The inactive projected decoder is not the old padding group (which includes L/U).
    for owner in s::FIRST+1153..s::FIRST+2048{let mut row=0;for [start,width,_] in s::RANGES[..4].iter().copied(){for b in 0..width{
        let t=Term{row,gate:Gate{left:(start+b) as usize,right:0,c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}};
        out.add(convert(&t,0,owner),p);row+=1;}}}
    drop(reference);drop(boundary);drop(base);
}
fn max_oracle(p:&ReferencePoint,out:&mut Oracle){
    let layout=suffix_max::Layout::new(2,2,999424).unwrap();let mut local=Vec::with_capacity(2242);
    layout.emit_owner(0,|t|{local.push(t);Ok(())}).unwrap();assert_eq!((local.len(),local.capacity()),(2242,2242));
    assert_eq!(field_counts(&local),[0,1794,0,1121]);
    let mut index=0;s::emit_max(s::FIRST,true,false,|t|{assert_eq!(t,convert(&local[index],1,s::FIRST));index+=1;});assert_eq!(index,2242);
    // Old Layout's own2242-Term local template and extraction coexist only here.
    assert_eq!(2*2242*std::mem::size_of::<Term>(),681568);drop(layout);
    for owner in s::FIRST..s::FIRST+2048{
        if owner<s::FIRST+1153{for t in &local{out.add(convert(t,1,owner),p);}}
        else{for b in 0..673{out.add(Tuple{row:Row{family:1,owner,local:b},left:s::native(owner,999424+b as usize),
            right:s::native(owner,0),c:[Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()]},p);}}
        if owner>s::FIRST&&owner<=s::FIRST+1153{for b in 0..224{for (left,c) in [(s::native(owner-1,999648+b),Fr::one()),(s::native(owner,999424+b),-Fr::one())]{
            out.add(Tuple{row:Row{family:1,owner,local:(898+b) as u32},left,right:s::native(owner,0),c:[Fr::zero(),c,Fr::zero(),Fr::zero()]},p);}}}
    }
    // Literal old destination-owner placeholder is checked from its emitted terminal edge.
    drop(local);let edge_layout=suffix_max::Layout::new(2,2,999424).unwrap();let mut seen=0;
    let mut inactive_seen=0;edge_layout.emit_owner(1,|t|{if t.row%2048<673{
        let b=t.row%2048;assert_eq!(t,Term{row:2048+b,gate:Gate{left:(1<<20)+999424+b,right:1<<20,
            c0:Fr::zero(),c1:Fr::one(),c2:Fr::zero(),c3:Fr::zero()}});inactive_seen+=1;
    }else if t.row%2048>=898{
        let b=seen/2;let previous=seen%2==0;
        let expected=Term{row:2048+898+b,gate:Gate{left:if previous{999648+b}else{(1<<20)+999424+b},right:1<<20,
            c0:Fr::zero(),c1:if previous{Fr::one()}else{-Fr::one()},c2:Fr::zero(),c3:Fr::zero()}};
        assert_eq!(t,expected);
        let tuple=Tuple{row:Row{family:1,owner:s::FIRST+1,local:(t.row%2048) as u32},
            left:s::native(s::FIRST+(t.gate.left>>20) as u64,t.gate.left% (1<<20)),right:s::native(s::FIRST+1,0),
            c:[t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]};
        // Stream comparison, no second448-Term reference. Only this row's two
        // new tuples are visited; its local inactive-zero rows are filtered out.
        let mut index=0;let mut match_at=false;s::visit_row(tuple.row,|actual|{
            if index==seen%2{assert_eq!(actual,tuple);match_at=true;}index+=1;}).unwrap();
        assert_eq!(index,2);assert!(match_at);seen+=1;
    }Ok(())}).unwrap();assert_eq!((inactive_seen,seen),(673,448));
    let mut new_inactive=0;s::emit_max(s::FIRST+1153,false,false,|t|{
        assert_eq!(t,Tuple{row:Row{family:1,owner:s::FIRST+1153,local:new_inactive},
            left:s::native(s::FIRST+1153,999424+new_inactive as usize),right:s::native(s::FIRST+1153,0),
            c:[Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()]});new_inactive+=1;});assert_eq!(new_inactive,673);
    drop(edge_layout);
}
fn cap_oracle(p:&ReferencePoint,out:&mut Oracle){
    let d=BigUint::from(1u8);let stmt=old_cap::Statement::new(&d,&d).unwrap();let mut local=Vec::with_capacity(6419);
    let scratch=old_cap::emit(&stmt,|t|{
        if (1838..1903).contains(&t.row){return;}
        if (1383..1607).contains(&t.row){if t.gate.c1.is_one(){local.push(t);}else{
            // Source input anchor constant is replaced by the explicit native-M import.
            let b=t.row-1383;local.push(Term{row:t.row,gate:Gate{left:999424+b,right:0,c0:Fr::zero(),c1:-Fr::one(),c2:Fr::zero(),c3:Fr::zero()}});}}
        else{local.push(t);}});
    assert_eq!(scratch,515);assert_eq!((local.len(),local.capacity()),(6419,6419));assert_eq!(field_counts(&local),[3,5034,0,1382]);
    let converted=|t:&Term,origin:u64|{let mut tuple=convert(t,2,origin);if t.gate.left>=999424{tuple.left=s::native(origin-1090,t.gate.left);}tuple};
    let mut index=0;s::emit_cap(s::I0,|t|{assert_eq!(t,converted(&local[index],s::I0));index+=1;});assert_eq!(index,6419);
    for origin in s::I0..s::I0+64{for t in &local{out.add(converted(t,origin),p);}}
    assert_eq!(local.capacity()*std::mem::size_of::<Term>(),975688);drop(local);drop(stmt);
}
fn source_and_coefficients(){
    old_cap::bounds();work::integer_bound().unwrap();assert_eq!(std::mem::size_of::<Port>(),56);
    let r=point(34,1,2);let u=point(41,2,3);let v=point(41,3,5);let p=ReferencePoint::new(&r,&u,&v);let mut oracle=Oracle::default();
    callable_work_oracle(&p,&mut oracle);max_oracle(&p,&mut oracle);cap_oracle(&p,&mut oracle);
    assert_eq!(oracle.counts,Scan{terms:s::TERMS,rows:s::ROWS,channels:[2498,5871238,0,2736889]});
    assert_eq!(oracle.coeff,s::coefficients(&Descriptor::canonical(),&r,&u,&v).unwrap());
    assert!(!oracle.coeff[0].is_zero()&&!oracle.coeff[1].is_zero()&&oracle.coeff[2].is_zero()&&!oracle.coeff[3].is_zero());
    for axis in 0..3{let (rr,uu,vv)=match axis{0=>(&r[..33],u.as_slice(),v.as_slice()),1=>(r.as_slice(),&u[..40],v.as_slice()),_=>(r.as_slice(),u.as_slice(),&v[..40])};
        assert_eq!(s::coefficients(&Descriptor::canonical(),rr,uu,vv),Err(Error::PointDimension));}
    drop(p);
}
fn metadata_and_geometry(){
    let d=Descriptor::canonical();let p=s::ports();assert_eq!((p.len(),p.capacity()),(64,64));let mut cases=0;
    // Empty payload would fail framing if admission read it. Each typed error therefore
    // proves the real constructor rejects the descriptor/roster before witness framing.
    let reject=|descriptor:Descriptor,roster:Vec<Port>,expected:Error|{
        let empty=PackedSuffix{frames:Box::default(),caps:Box::default()};
        assert_eq!(AdmittedSuffix::new(descriptor,roster,empty).map(|_|()),Err(expected));
    };
    reject(d.clone(),p.clone(),Error::Framing);
    for i in 0..50{let mut bad=d.clone();bad.fields[i]^=1;reject(bad,p.clone(),Error::Descriptor(i));cases+=1;}
    for i in 0..4{let mut bad=d.clone();bad.pins[i][0]^=1;reject(bad,p.clone(),Error::Pin(i));cases+=1;}
    for i in 0..8{for j in 0..3{let mut bad=d.clone();bad.ranges[i][j]^=1;reject(bad,p.clone(),Error::Range(i*3+j));cases+=1;}}
    assert_eq!(cases,78);
    for i in 0..64{for j in 0..7{let mut bad=p.clone();bad[i].fields[j]^=1;reject(d.clone(),bad,Error::Port(i));cases+=1;}
        let mut missing=p.clone();missing.remove(i);reject(d.clone(),missing,Error::Roster);cases+=1;
        let mut duplicate=p.clone();duplicate.push(p[i]);assert_eq!(duplicate.capacity(),128);assert_eq!((duplicate.capacity()+p.capacity())*56,10752);
        reject(d.clone(),duplicate,Error::Roster);cases+=1;
        let mut swapped=p.clone();swapped.swap(i,(i+1)%64);reject(d.clone(),swapped,Error::Port(i.min((i+1)%64)));cases+=1;
    }assert_eq!(cases,718);
    for i in 0..64{for source in [987674,999425]{let mut bad=p.clone();bad[i].fields[2]=source;assert_eq!(s::validate_ports(&bad),Err(Error::Port(i)));}
        let mut neighbor=p.clone();neighbor[i].fields[1]+=1;assert_eq!(s::validate_ports(&neighbor),Err(Error::Port(i)));}
    let g=s::GeometryMath::from_interval(s::I0,s::N,s::I0,s::N,20).unwrap();assert_eq!((g.first,g.active,g.slots,g.ports),(s::FIRST,1153,2048,64));
    assert!(s::GeometryMath::from_interval(1,s::N,s::I0,s::N,20).is_err());
    assert!(s::GeometryMath::from_interval(s::I0,u64::MAX,s::I0,s::N,20).is_err());
    assert!(s::GeometryMath::from_interval(s::I0,s::N,s::I0,s::N,19).is_err());
    assert!(s::GeometryMath::from_interval(s::I0,s::N,s::I0,s::N,63).is_err());
    let mut short=PackedSuffix{frames:vec![0;47103].into_boxed_slice(),caps:vec![0;2048].into_boxed_slice()};assert_eq!(short.framing(),Err(Error::Framing));
    short.frames=vec![0;47104].into_boxed_slice();short.caps=vec![0;2047].into_boxed_slice();assert_eq!(short.framing(),Err(Error::Framing));drop(short);
    let mut physical=PackedSuffix::zeroed();for index in [22,47103]{physical.frames[index]=2;assert_eq!(physical.framing(),Err(Error::Framing));physical.frames[index]=0;}drop(physical);
    for w in [s::native(s::FIRST-1,987674),s::native(s::FIRST+2048,987674),s::native(s::FIRST,0),s::native(s::FIRST,1<<20),s::cap(s::I0-1,1),s::cap(s::N,1),s::cap(s::I0,2048)]{assert_eq!(PackedSuffix::index(w),Err(Error::Coordinate));}
    assert_eq!(work::native_decode(0).is_err(),true);assert!(work::native_decode(0x04800001).is_err());assert!(work::native_decode(0x1F000001).is_err());
    for bits in [0x01010000,0x0101FFFF]{let value=work::native_decode(bits).unwrap();assert_eq!(value,BigUint::one());assert_eq!(old_cap::scalar(&value).unwrap(),BigUint::one());}
    assert!(old_cap::admit(&BigUint::zero()).is_err());assert!(old_cap::admit(&((power(65)+1u8)/3u8+1u8)).is_err());
}
fn local_decoder_boundaries(){
    let modulus=BigUint::from_bytes_le(&Fr::MODULUS.to_bytes_le());assert!(power(226)<modulus);
    let mut rows=vec![Fr::zero();2048];assert_eq!(rows.capacity()*32,65536);
    for bits in [0x01010000u32,0x0101FFFF,0x03000000,0x1D010000,0x1E000100,0x04800001]{
        // One23-word local adapter; not framing-admitted as a full suffix witness.
        let mut packed=PackedSuffix{frames:vec![0;23].into_boxed_slice(),caps:Box::default()};
        put(&mut packed,s::FIRST,987162,32,&BigUint::from(bits));
        let exponent=(bits>>24) as usize;packed.set(s::native(s::FIRST,987898+exponent),true).unwrap();
        if let Ok(d)=work::native_decode(bits){put(&mut packed,s::FIRST,987674,224,&d);put(&mut packed,s::FIRST,988154,224,&(&d-1u8));}
        rows.fill(Fr::zero());s::emit_decoder(s::FIRST,true,|t|rows[t.row.local as usize]+=s::evaluate(t,&mut |w|packed.read(w)).unwrap());
        match bits{0x01010000|0x0101FFFF=>{assert!(rows.iter().all(Zero::is_zero));assert_eq!(number(|w|packed.read(s::native(s::FIRST,w)).unwrap(),987674,224),BigUint::one());},
            0x03000000=>{assert_eq!(rows[1433],-Fr::one());assert!(rows[..1433].iter().all(Zero::is_zero));},
            0x1D010000=>assert_eq!(rows[1411],Fr::one()),0x1E000100=>assert_eq!(rows[1418],Fr::one()),
            _=>assert_eq!(rows[1186],Fr::one())}
        assert_eq!(packed.frames.len()*8,184);drop(packed);
    }
    drop(rows);
}
fn residual(a:&AdmittedSuffix,row:Row,delta:&[(Wire,Fr)])->Fr{let mut out=Fr::zero();s::visit_row(row,|t|{out+=s::evaluate(t,&mut |w|delta.iter().find(|(x,_)|*x==w).map(|(_,v)|Ok(*v)).unwrap_or_else(||a.read(w))).unwrap();}).unwrap();out}
fn single(a:&AdmittedSuffix,w:Wire,expected:Row){let delta=[(w,Fr::from(2u64))];
    assert!(s::affected_rows(w).unwrap().contains(&expected));assert!(!residual(a,expected,&delta).is_zero());assert!(matches!(a.check_delta(&delta),Err(Error::Residual(_))));}
fn field_faults(a:&AdmittedSuffix){
    let owner=s::FIRST;let row=|family,local|Row{family,owner,local};
    // Each retained native field, product family and both endpoint frames.
    for (local,expected) in [(987162,0),(987185,1186),(987186,1185),(987898,958),(987899,928),
        (987902,931),(987929,959),(987674,1187),(987897,1410),(988154,1433),(988377,1433)]{
        single(a,s::native(owner,local),row(0,expected));}
    for local in [999424,999647,999648,999871,999872,1000095,1000096]{
        single(a,s::native(owner,local),row(1,if local<999648{674+(local-999424) as u32}else{673}));}
    // Non-Boolean violations use Fr overlays, never a bit conversion.
    for (wire,r) in [(s::native(owner,987162),row(0,0)),(s::native(owner,999424),row(1,0)),
        (s::cap(s::I0,449),Row{family:2,owner:s::I0,local:449})]{assert_eq!(a.check_delta(&[(wire,Fr::from(2u64))]),Err(Error::Residual(r)));}
    let final_owner=s::FIRST+1152;single(a,s::native(final_owner,987674),Row{family:0,owner:final_owner,local:1187});
    // Every native MAX import reaches its cap; N also reaches its successor's edge.
    for i in 0..64{let o=s::FIRST+i;let w=s::native(o,999424);let rows=s::affected_rows(w).unwrap();assert!(rows.contains(&Row{family:2,owner:s::I0+i,local:1383}));
        assert!(!residual(a,Row{family:2,owner:s::I0+i,local:1383},&[(w,Fr::one()-a.read(w).unwrap())]).is_zero());}
    let edge=Row{family:1,owner:owner+1,local:898};single(a,s::native(owner,999648),edge);
    assert_eq!(s::affected_rows(s::native(owner,1000096)).unwrap().len(),226);
    for o in [s::FIRST+1153,s::FIRST+1154,s::FIRST+2047]{
        single(a,s::native(o,987162),Row{family:0,owner:o,local:0});single(a,s::native(o,1000096),Row{family:1,owner:o,local:672});}
    let origin=s::I0;for (wire,local) in [(0,0),(1,1383),(224,1606),(225,1607),(448,1830),(449,1832),(673,1832),
        (674,1832),(675,1833),(739,1833),(740,1834),(804,1834),(805,1835),(868,1835),(869,1836),(933,1836),
        (934,1837),(1158,1837),(1159,1831),(1382,1831),(1383,1903),(2047,2567)]{
        single(a,s::cap(origin,wire),Row{family:2,owner:origin,local});}
    let last= s::N-1;single(a,s::cap(last,1),Row{family:2,owner:last,local:1383});
    single(a,s::cap(last,804),Row{family:2,owner:last,local:1834});
    assert_eq!(a.check_delta(&[(s::cap(origin,0),Fr::zero()),(s::cap(origin,0),Fr::zero())]),Err(Error::Coordinate));
    assert_eq!(a.check_delta(&[(s::native(owner,0),Fr::zero())]),Err(Error::Coordinate));
    assert_eq!(a.check_delta(&vec![(s::native(owner,987674),Fr::zero());225]),Err(Error::DeltaBound));
    assert_eq!(a.check_delta(&[(s::native(owner,987674),Fr::zero()),(s::native(owner+1,987674),Fr::zero())]),Err(Error::DeltaBound));
    assert_eq!(a.check_delta(&[(s::native(owner,987674),Fr::zero()),(s::cap(s::I0,1),Fr::zero())]),Err(Error::DeltaBound));
    assert_eq!(a.check_delta(&[]),Ok(0));
    // Override D-only zero does not acquire a trusted positive result.
    let zero=(0..224).map(|b|(s::native(owner,987674+b),Fr::zero())).collect::<Vec<_>>();assert!(matches!(a.check_delta(&zero),Err(Error::Residual(_))));drop(zero);
}
fn boolean_point(n:usize,value:u64)->Vec<Fr>{(0..n).map(|b|Fr::from((value>>b)&1)).collect()}
fn row_point(row:Row)->Vec<Fr>{let mut r=boolean_point(12,row.local as u64);r.extend(boolean_point(20,row.owner));r.extend(boolean_point(2,row.family as u64));r}
fn wire_point(w:Wire)->Vec<Fr>{let mut p=boolean_point(20,w.local() as u64);p.extend(boolean_point(20,w.owner()));p.push(Fr::from(w.tag() as u64));p}
fn direct_one(t:Tuple,r:&[Fr],u:&[Fr],v:&[Fr])->[Fr;4]{let weight=s::eq(&r[..12],t.row.local as u64)*s::eq(&r[12..32],t.row.owner)*s::eq(&r[32..],t.row.family as u64)
    *s::eq(&u[..20],t.left.local() as u64)*s::eq(&u[20..40],t.left.owner())*s::eq(&u[40..],t.left.tag() as u64)
    *s::eq(&v[..20],t.right.local() as u64)*s::eq(&v[20..40],t.right.owner())*s::eq(&v[40..],t.right.tag() as u64);
    t.c.map(|c|c*weight)}
fn cancellation_and_wiring(a:&AdmittedSuffix){
    let owner=s::FIRST+1154;let row0=Row{family:0,owner,local:0};let row1=Row{local:1,..row0};
    let delta=[(s::native(owner,987162),Fr::from(2u64)),(s::native(owner,987163),Fr::one())];
    assert_eq!(residual(a,row0,&delta),Fr::from(2u64));assert_eq!(residual(a,row1,&delta),Fr::one());
    let mut r=row_point(row0);r[..12].fill(Fr::from(2u64));assert_eq!(s::eq(&r[..12],0),Fr::one());assert_eq!(s::eq(&r[..12],1),-Fr::from(2u64));
    assert_eq!(s::eq(&r[..12],0)*Fr::from(2u64)+s::eq(&r[..12],1),Fr::zero());
    assert_eq!(a.check_delta(&delta),Err(Error::Residual(row0)));
    let mut u=wire_point(s::native(owner,987162));u[0]=Fr::from(3u64).inverse().unwrap();let v=wire_point(s::native(owner,0));
    let mut addends=Vec::with_capacity(2);for row in [row0,row1]{s::visit_row(row,|t|addends.push(direct_one(t,&r,&u,&v)[1])).unwrap();}
    assert_eq!(addends.as_slice(),&[Fr::from(2u64)/Fr::from(3u64),-Fr::from(2u64)/Fr::from(3u64)]);
    assert!(addends.iter().all(|x|!x.is_zero()));assert_eq!(addends.iter().copied().sum::<Fr>(),Fr::zero());
    assert_eq!(s::coefficients(&Descriptor::canonical(),&r,&u,&v).unwrap(),[Fr::zero();4]);drop(addends);
    let destination=s::FIRST+1;let row=Row{family:1,owner:destination,local:898};let mut previous=None;
    s::visit_row(row,|t|if t.left.owner()==s::FIRST{previous=Some(t)}).unwrap();let correct=previous.unwrap();
    let mut wrong=correct;wrong.right=s::native(s::FIRST,0);assert_ne!(wrong,correct);
    let r=row_point(row);let u=wire_point(s::native(s::FIRST,999648));let mut v=wire_point(s::native(destination,0));
    assert_eq!(direct_one(correct,&r,&u,&v)[1],Fr::one());assert_eq!(direct_one(wrong,&r,&u,&v)[1],Fr::zero());
    v[20]=Fr::from(2u64);assert_eq!(direct_one(correct,&r,&u,&v)[1],Fr::from(2u64));assert_eq!(direct_one(wrong,&r,&u,&v)[1],-Fr::one());
    assert_eq!(direct_one(wrong,&r,&u,&v)[1]-direct_one(correct,&r,&u,&v)[1],-Fr::from(3u64));
    assert_eq!(s::evaluate(correct,&mut |w|a.read(w)).unwrap(),s::evaluate(wrong,&mut |w|a.read(w)).unwrap());
    assert_eq!(s::coefficients(&Descriptor::canonical(),&r,&u,&v).unwrap()[1],Fr::from(2u64));
    for row in [Row{family:0,owner:s::FIRST,local:32},Row{family:0,owner:s::FIRST,local:1434},
        Row{family:1,owner:s::FIRST,local:898},Row{family:1,owner:s::FIRST+2047,local:1122},
        Row{family:2,owner:s::I0,local:1838},Row{family:2,owner:s::I0,local:1902},Row{family:2,owner:s::I0,local:2568},
        Row{family:3,owner:s::FIRST,local:0}]{
        let mut terms=0;s::visit_row(row,|_|terms+=1).unwrap();assert_eq!(terms,0);
        let r=row_point(row);let u=point(41,2,3);let v=point(41,3,5);assert_eq!(s::coefficients(&Descriptor::canonical(),&r,&u,&v).unwrap(),[Fr::zero();4]);}
    for row in [Row{family:0,owner:s::FIRST+2048,local:0},Row{family:1,owner:s::FIRST,local:2048},
        Row{family:2,owner:s::I0,local:4096},Row{family:4,owner:0,local:0}]{assert_eq!(s::visit_row(row,|_|panic!("bad row callback")),Err(Error::Coordinate));}
}
fn coefficient_boundaries(){
    let d=Descriptor::canonical();
    let check=|row:Row,left:Wire,right:Wire,j:usize,expected:Fr|{
        let r=row_point(row);let u=wire_point(left);let v=wire_point(right);
        assert_eq!(s::coefficients(&d,&r,&u,&v).unwrap()[j],expected);
    };
    // The final active decoder, final incoming edge, terminal zero and tail zero
    // are distinct polynomials at their original absolute coordinates.
    check(Row{family:0,owner:s::FIRST+1152,local:1187},s::native(s::FIRST+1152,987674),s::native(s::FIRST+1152,0),1,Fr::one());
    check(Row{family:1,owner:s::FIRST+1153,local:898},s::native(s::FIRST+1152,999648),s::native(s::FIRST+1153,0),1,Fr::one());
    check(Row{family:1,owner:s::FIRST+1153,local:0},s::native(s::FIRST+1153,999424),s::native(s::FIRST+1153,0),1,Fr::one());
    check(Row{family:0,owner:s::FIRST+2047,local:735},s::native(s::FIRST+2047,988377),s::native(s::FIRST+2047,0),1,Fr::one());
    for origin in [s::I0,s::N-1]{
        let row=Row{family:2,owner:origin,local:1383};let imported=s::native(origin-1090,999424);let right=s::cap(origin,0);
        let r=row_point(row);let u=wire_point(imported);let v=wire_point(right);
        let correct=s::coefficients(&d,&r,&u,&v).unwrap();assert_eq!(correct,[Fr::zero(),-Fr::one(),Fr::zero(),Fr::zero()]);
        let mut reference=None;s::visit_row(row,|t|if t.left.tag()==0{reference=Some(t)}).unwrap();let original=reference.unwrap();
        // Omission, sign, source-D/neighbor, namespace and right-placeholder are
        // separately visible to the actual coefficient consumer at Boolean selectors.
        assert_ne!([Fr::zero();4],correct);
        for kind in 0..5{let mut mutant=original;match kind{0=>mutant.c[1]=Fr::one(),
            1=>mutant.left=s::native(origin-1090,987674),2=>mutant.left=s::native(origin-1090+1,999424),
            3=>mutant.left=s::cap(origin,1),_=>mutant.right=s::cap(origin,1)}
            assert_ne!(direct_one(mutant,&r,&u,&v),correct);assert_ne!(mutant,original);}
        // Retiring the old q anchor is an actual zero polynomial; restoring its
        // linear half would alter C1, even if a host statement happened to match q.
        let retired=Row{family:2,owner:origin,local:1838};let rr=row_point(retired);let uu=wire_point(s::cap(origin,740));
        assert_eq!(s::coefficients(&d,&rr,&uu,&v).unwrap(),[Fr::zero();4]);
        let restored=Tuple{row:retired,left:s::cap(origin,740),right,c:[Fr::zero(),Fr::one(),Fr::zero(),Fr::zero()]};
        assert_eq!(direct_one(restored,&rr,&uu,&v)[1],Fr::one());
    }
}
fn tiny_literal(){
    // Local templates already differentiated against the three immutable callable sources.
    // Diagnostic2active+terminal+tail/2caps, never passed to AdmittedSuffix.
    let mut tuples=Vec::with_capacity(25326);
    let encoded=|t:Tuple|{let wire=|w:Wire|((w.tag() as u64)<<40)|(w.owner()<<20)|w.local() as u64;
        Term{row:((t.row.family as u64)<<32|t.row.owner<<12|t.row.local as u64) as usize,
            gate:Gate{left:wire(t.left) as usize,right:wire(t.right) as usize,c0:t.c[0],c1:t.c[1],c2:t.c[2],c3:t.c[3]}}};
    let decoded=|t:&Term|{let wire=|w:usize|if w>>40==0{s::native(((w as u64)>>20)&((1<<20)-1),w&((1<<20)-1))}
        else{s::cap(((w as u64)>>20)&((1<<20)-1),w&((1<<20)-1))};
        Tuple{row:Row{family:(t.row>>32) as u8,owner:((t.row as u64)>>12)&((1<<20)-1),local:(t.row&4095) as u32},
            left:wire(t.gate.left),right:wire(t.gate.right),c:[t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3]}};
    for owner in s::FIRST..s::FIRST+4{s::emit_decoder(owner,owner<s::FIRST+2,|t|tuples.push(encoded(t)));}
    for owner in s::FIRST..s::FIRST+4{s::emit_max(owner,owner<s::FIRST+2,owner>s::FIRST&&owner<=s::FIRST+2,|t|tuples.push(encoded(t)));}
    for origin in s::I0..s::I0+2{s::emit_cap(origin,|t|tuples.push(encoded(t)));}
    assert_eq!((tuples.len(),tuples.capacity()),(25326,25326));
    assert_eq!(tuples.capacity()*std::mem::size_of::<Term>(),3849552);
    // Tuple is only a by-value callback record, never a retained template vector.
    let callback_record_bytes=std::mem::size_of::<Tuple>();assert!(callback_record_bytes<=256);
    let r=point(34,1,7);let u=point(41,3,11);let v=point(41,5,13);let p=ReferencePoint::new(&r,&u,&v);
    let mut cached=[Fr::zero();4];let mut direct=[Fr::zero();4];
    for old in &tuples{let t=decoded(old);for (x,c) in cached.iter_mut().zip(t.c){*x+=p.owner(t)*p.local.local(t)*c;}
        for (x,c) in direct.iter_mut().zip(direct_one(t,&r,&u,&v)){*x+=c;}}
    assert_eq!(direct,cached);assert!(direct[2].is_zero());
    let saved=decoded(&tuples[0]);for axis in 0..3{let mut wrong=saved;match axis{0=>wrong.row.local+=1,1=>wrong.left=s::native(s::FIRST,987163),_=>wrong.right=s::native(s::FIRST,987163)}
        assert_ne!(wrong,saved);assert_ne!(direct_one(wrong,&r,&u,&v),direct_one(saved,&r,&u,&v));}
    drop(tuples);drop(p);
}
#[test]
fn complete_suffix_produces_all_modern_v_ports(){
    metadata_and_geometry();source_and_coefficients();local_decoder_boundaries();coefficient_boundaries();tiny_literal();
    let mut frozen_challenge=None;
    for which in 0..3{
        let admitted=AdmittedSuffix::new(Descriptor::canonical(),s::ports(),fixture(which)).unwrap();
        assert_eq!(admitted.counts(),Scan{terms:s::TERMS,rows:s::ROWS,channels:[2498,5871238,0,2736889]});
        let mut count=0;admitted.visit_ports(|p,q|{assert_eq!(p.fields[0],s::I0+count);
            let expected=if which==1&&count>0{power(31)}else{power(38)};assert_eq!(number(|w|q.bit(w).unwrap(),0,65),expected);
            assert_eq!(q.bit(65),Err(Error::Coordinate));count+=1;});assert_eq!(count,64);
        let binding=admitted.binding();assert_eq!((binding.len(),binding.capacity()),(4331,4331));
        let mut literal_transcript=Transcript::new(b"certified-modern-suffix-test");literal_transcript.append_bytes(b"certified-modern-suffix-layout",&binding);
        drop(binding); // Only one4331-byte serialization buffer is live at a time.
        let mut t=Transcript::new(b"certified-modern-suffix-test");let before=t.bytes_absorbed();admitted.bind(&mut t);
        assert_eq!(t.bytes_absorbed()-before,(17+b"certified-modern-suffix-layout".len()+4331) as u64);assert_eq!(t.challenges(),0);
        let challenge=t.challenge_scalar(b"after-complete-suffix");assert!(!challenge.is_zero());assert_eq!(t.challenges(),1);
        assert_eq!(challenge,literal_transcript.challenge_scalar(b"after-complete-suffix"));
        if let Some(previous)=frozen_challenge{assert_eq!(challenge,previous);}else{frozen_challenge=Some(challenge);}
        if which==0{field_faults(&admitted);cancellation_and_wiring(&admitted);}
        // Equality D=N requires s0 at every tie; checking the source row excludes s1.
        for owner in [s::FIRST+1,s::FIRST+1151]{let d=number(|w|admitted.read(s::native(owner,w)).unwrap(),987674,224);
            let n=number(|w|admitted.read(s::native(owner,w)).unwrap(),999648,224);
            if d==n{assert!(admitted.read(s::native(owner,1000096)).unwrap().is_zero());}}
        assert_eq!(admitted.packed().frames.len()*8+admitted.packed().caps.len()*8,393216);
        drop(admitted);
    }
    assert_eq!(3*s::ROWS,11555313);assert_eq!(4*s::TERMS,28986504);
}

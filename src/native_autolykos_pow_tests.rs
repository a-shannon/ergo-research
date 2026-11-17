use super::*;
use crate::{native_work_opening::{NativeWorkMembershipContext, NativeWorkOpening, NativeWorkOpeningError}, packed_owner_assembly::NativePrefix};
use ergo_header_core::Error as CodecError;
use num_traits::One;
use serde_json::Value;

// Minimum field-preserving JSON fixtures, CC0-1.0 from the pinned repositories.
// V1: sigma-rust d6c8fc71bb5b6ad5ad64c16b726e98a3929543b6,
// ergo-chain-types/src/header.rs blob58e706d18fa221afa990077bcc63207fe2a05d3a.
// V2: Ergo8995ff243b140e7fe716bd3204423dd35690c2e4,
// AutolykosPowSchemeSpec.scala blob6c629957f9a4b5a49aeaa1cab664d3a5f3f9a189.
// LICENSE at both revisions: blob0e259d42c996742e9e3cba14c677129b2c1b6311.
// V1 d is rendered as an exact decimal string from the r2 expected record,
// avoiding serde_json's floating fallback for integers wider than u64.
const V1_JSON: &str = r#"{
"version":1,"parentId":"150290bbaf91ccd4dcf307cb9a5113eed67e12694ec9be277e8fa55fb5ebf6ac",
"adProofsRoot":"c9d58eacf6108c9a166b0b76020e3323c6c2ccec5ec8f905ea46f5bcc58aac80",
"transactionsRoot":"01bf55fd587291172f458232a7f58b4b29469d72b8e304aafd68401f915b0c36",
"stateRoot":"144c15900826f6e2aac70cb50e541215b337d0d1674da6b491499944e686b41b0e",
"timestamp":1562027226367,"extensionHash":"ccb136ffd50a16f50a499e1c33d8ae1e8426bdc70b13a4d82275d057be2d04a7",
"nBits":117483687,"height":3132,"votes":"000000",
"powSolutions":{"pk":"02ff03f4b981c59ccd5185fddcd949b8f5697341e60d808d2be0e3e09d2ec78bf4","w":"037427400e5292a177dc242631f78ab322b7845ad2b8491b016b7c36407c6a6d76","n":"0000667700008481","d":"410958177852074551025494081160156537946251159549691138805256284"}}
"#;
const V2_VALID_JSON: &str = r#"{
"version":2,"parentId":"ac2101807f0000ca01ff0119db227f202201007f62000177a080005d440896d0",
"adProofsRoot":"5d3f80dcff7f5e7f59007294c180808d0158d1ff6ba10000f901c7f0ef87dcff",
"transactionsRoot":"f17fffacb6ff7f7f1180d2ff7f1e24ffffe1ff937f807f0797b9ff6ebdae007e",
"stateRoot":"5c8c00b8403d3701557181c8df800001b6d5009e2201c6ff807d71808c00019780",
"timestamp":4928911477310178288,"extensionHash":"1480887f80007f4b01cf7f013ff1ffff564a0000b9a54f00770e807f41ff88c0",
"nBits":37748736,"height":614400,"votes":"000000",
"powSolutions":{"pk":"03bedaee069ff4829500b3c07c4d5fe6b3ea3d3bf76c5c28c1d4dcdb1bed0ade0c","n":"0000000000003105"}}
"#;
const V2_INVALID_JSON: &str = r#"{
"version":2,"parentId":"ab19e6c7a4062979dddb534df83f236d1b949c7cef18bcf434a67e87c593eef9",
"adProofsRoot":"49453875a43035c7640dee2f905efe06128b00d41acd2c8df13691576d4fd85c",
"transactionsRoot":"770cbb6e18673ed025d386487f15d3252115d9a6f6c9b947cf3d04731dd6ab75",
"stateRoot":"c0d0b5eafd07b22487dac66628669c42a242b90bef3e1fcdc76d83140d58b6bc0e",
"timestamp":1611225263165,"extensionHash":"9bc7d54583c5d44bb62a7be0473cd78d601822a626afc13b636f2cbff0d87faf",
"nBits":72286528,"height":2870,"votes":"000000",
"powSolutions":{"pk":"0288114b0586efea9f86e4587f2071bc1c85fb77e15eba96b2769733e0daf57903","n":"000100000580a91b"}}
"#;

fn hex(text: &str) -> Vec<u8> {
    assert_eq!(text.len() % 2, 0);
    text.as_bytes().chunks_exact(2).map(|p| u8::from_str_radix(std::str::from_utf8(p).unwrap(),16).unwrap()).collect()
}
fn fixed<const N: usize>(text: &str) -> [u8; N] { hex(text).try_into().ok().unwrap() }
fn decimal(text: &str) -> BigUint { BigUint::parse_bytes(text.as_bytes(),10).unwrap() }
fn fixture(text: &str) -> Header {
    let v: Value = serde_json::from_str(text).unwrap();
    let p=&v["powSolutions"];
    let pk=GroupElement::from_bytes(fixed(p["pk"].as_str().unwrap())).unwrap();
    let nonce=fixed(p["n"].as_str().unwrap());
    let version=i8::try_from(v["version"].as_i64().unwrap()).unwrap();
    Header {
        version,parent_id:fixed(v["parentId"].as_str().unwrap()),ad_proofs_root:fixed(v["adProofsRoot"].as_str().unwrap()),
        transactions_root:fixed(v["transactionsRoot"].as_str().unwrap()),state_root:fixed(v["stateRoot"].as_str().unwrap()),
        timestamp:v["timestamp"].as_i64().unwrap(),extension_root:fixed(v["extensionHash"].as_str().unwrap()),
        n_bits:u32::try_from(v["nBits"].as_u64().unwrap()).unwrap(),height:u32::try_from(v["height"].as_u64().unwrap()).unwrap(),
        votes:fixed(v["votes"].as_str().unwrap()),unparsed_bytes:Vec::new(),
        pow:if version==1 { PowSolution::V1{pk,w:GroupElement::from_bytes(fixed(p["w"].as_str().unwrap())).unwrap(),nonce,distance:decimal(p["d"].as_str().unwrap()).to_bytes_be()} }
            else { PowSolution::V2{pk,nonce} },
    }
}
fn local_raws() -> Vec<Vec<u8>> {
    // Existing local-only pack; no redistribution grant is inferred.
    let v: Value=serde_json::from_str(include_str!("../vendor/header-core/fixtures/governance-contiguous-header-packs-v1.json")).unwrap();
    v["networks"]["mainnet"]["source_headers_hex"].as_array().unwrap().iter().take(3).map(|v|hex(v.as_str().unwrap())).collect()
}
fn h2() -> Header { Header::decode(&local_raws()[1],None).unwrap() }
fn set_distance(h: &mut Header, value: BigUint) { if let PowSolution::V1{distance,..}=&mut h.pow{*distance=if value.is_zero(){Vec::new()}else{value.to_bytes_be()}}else{panic!("V1 fixture")} }
fn nonce_flip(h: &mut Header){match &mut h.pow{PowSolution::V1{nonce,..}|PowSolution::V2{nonce,..}=>nonce[7]^=1}}

#[test]
fn native_pow_01_qualified_h2_and_source_message() {
    // Qualified Python oracle: input2201/50475F80, RAW278/SHA256
    // 36E463621E0B0AFF0A58439BA9577290FC74AA24BBC9575DD64DD699D0E2A02E.
    // DATA07C68C74, receipt2254/2300335F; not Scala execution.
    let raw=local_raws().remove(1);let h=Header::decode(&raw,None).unwrap();
    assert_eq!(raw.len(),278);assert_eq!(h.height,2);assert_eq!(h.encode().unwrap(),raw);
    assert_eq!(h.id().unwrap(),fixed("855fc5c9eed868b43ea2c3df99ec17dd9d903187d891e2365a89b98125c994b2"));
    assert_eq!(difficulty(h.n_bits).unwrap(),decimal("1199990374400"));
    assert_eq!(message(&h).unwrap(),fixed("b7dbdb5fe472e8345f53700b5c55ca03794ec188836555bccb1a6026b0b169f8"));
    assert_eq!(verify_header(&h),Ok(()));
    let source=fixture(V1_JSON);
    assert_eq!(source.id().unwrap(),fixed("41c73753452a292442799bd884fbcc2a9b0f62d4cff7ad02ccd3dbe65791c908"));
    assert_eq!(message(&source).unwrap(),fixed("9d10fe567f4f02777db77250523bd98c940f76de50bd2c2e51156927c6f37ae1"));
    // This upstream source asserted parser/ID coverage, not a V1 oracle call.
}

#[test]
fn native_pow_02_isolated_reference_rejections() {
    let original=h2();let original_msg=message(&original).unwrap();
    let d=match &original.pow{PowSolution::V1{distance,..}=>BigUint::from_bytes_be(distance),_=>unreachable!()};
    let target=order()/difficulty(original.n_bits).unwrap();assert!(&d+BigUint::one()<target);
    let mut equation=original.clone();set_distance(&mut equation,&d+BigUint::one());
    assert_ne!(equation.encode().unwrap(),original.encode().unwrap());assert_eq!(message(&equation).unwrap(),original_msg);
    assert_eq!(verify_header(&equation),Err(NativePowError::Equation));
    let mut equality=original.clone();set_distance(&mut equality,target);assert_eq!(message(&equality).unwrap(),original_msg);
    assert_eq!(equality.encode().unwrap().len(),original.encode().unwrap().len());assert_eq!(verify_header(&equality),Err(NativePowError::Target));
    for pk_case in [true,false] {let mut changed=original.clone();if let PowSolution::V1{pk,w,..}=&mut changed.pow{if pk_case{*pk=GroupElement::INFINITY}else{*w=GroupElement::INFINITY}};
        assert_eq!(message(&changed).unwrap(),original_msg);assert_eq!(verify_header(&changed),Err(NativePowError::FinitePoint));}
}

#[test]
fn native_pow_03_canonical_zero_scalar_and_identity() {
    let mut h=h2();set_distance(&mut h,BigUint::zero());let raw=h.encode().unwrap();
    assert_eq!(Header::decode(&raw,None).unwrap(),h);assert_eq!(message(&h).unwrap(),message(&h2()).unwrap());
    assert_eq!(verify_header(&h),Err(NativePowError::Equation));
    if let PowSolution::V1{distance,..}=&mut h.pow{distance.push(0)};
    assert_eq!(h.encode(),Err(CodecError::NonCanonicalDistance));assert_eq!(verify_header(&h),Err(NativePowError::Encoding));
    let mut nonminimal=raw.clone();*nonminimal.last_mut().unwrap()=1;nonminimal.push(0);
    assert_eq!(Header::decode(&nonminimal,None),Err(CodecError::NonCanonicalDistance));
    assert_eq!(scalar(&BigUint::zero()).unwrap(),Scalar::ZERO);assert!(scalar(&order()).is_err());assert!(scalar(&(BigUint::one()<<256usize)).is_err());
    let g=ProjectivePoint::GENERATOR;
    assert_eq!(v1_equation(g,g,Scalar::ZERO,Scalar::ONE),Ok(()));
    // Both sides identity are allowed as intermediate equation results.
    assert_eq!(v1_equation(-g,g,Scalar::ONE,Scalar::ZERO),Ok(()));
}

#[test]
fn native_pow_04_finite_substitution_nonce_equation() {
    let original=h2();let g=GroupElement::from_bytes(fixed("0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798")).unwrap();
    for which in 0..3 {let mut h=original.clone();if which==0{nonce_flip(&mut h)}else if let PowSolution::V1{pk,w,..}=&mut h.pow{if which==1{assert_ne!(*pk,g);*pk=g}else{assert_ne!(*w,g);*w=g}};
        assert_ne!(h.encode().unwrap(),original.encode().unwrap());assert_eq!(message(&h).unwrap(),message(&original).unwrap());
        assert_eq!(verify_header(&h),Err(NativePowError::Equation));}
    assert_eq!(GroupElement::from_bytes([1;33]),Err(CodecError::InvalidPoint));
    let mut bad=[0;33];bad[32]=1;assert_eq!(GroupElement::from_bytes(bad),Err(CodecError::NonCanonicalPoint));
}

#[test]
fn native_pow_05_pinned_v2_differential() {
    let valid=fixture(V2_VALID_JSON);let msg=message(&valid).unwrap();
    assert_eq!(msg,fixed("548c3e602a8f36f8f2738f5f643b02425038044d98543a51cabaa9785e7e864f"));
    assert_eq!(valid.id().unwrap(),fixed("5603a937ec1988220fc44fb5022fb82d5565b961f005ebb55d85bd5a9e6f801f"));
    let PowSolution::V2{nonce,..}=&valid.pow else{unreachable!()};
    assert_eq!(v2_hit(&msg,nonce,valid.height).unwrap(),fixed("0002fcb113fe65e5754959872dfdbffea0489bf830beb4961ddc0e9e66a1412a"));
    assert_eq!(order()/difficulty(valid.n_bits).unwrap(),decimal("7067388259113537318333190002971674063283542741642755394446115914399301849"));
    assert_eq!(verify_header(&valid),Ok(()));
    let invalid=fixture(V2_INVALID_JSON);assert_eq!(invalid.id().unwrap(),fixed("5b0ce6711de6b926f60b67040cc4512804517785df375d063f1bf1d75588af3a"));
    assert_eq!(verify_header(&invalid),Err(NativePowError::Target));
    // JSON w/d are deliberately excluded: V2's canonical solution has none.
    let mut changed=valid.clone();nonce_flip(&mut changed);assert_eq!(message(&changed).unwrap(),msg);
    let PowSolution::V2{nonce,..}=&changed.pow else{unreachable!()};assert_ne!(v2_hit(&msg,nonce,changed.height).unwrap(),v2_hit(&msg,&fixed("0000000000003105"),valid.height).unwrap());
    let mut infinity=valid.clone();if let PowSolution::V2{pk,..}=&mut infinity.pow{*pk=GroupElement::INFINITY};
    assert_eq!(message(&infinity).unwrap(),msg);assert_eq!(verify_header(&infinity),Ok(()));
}

#[test]
fn native_pow_06_every_message_field_binding() {
    let h=h2();let before=h.encode().unwrap();let digest=message(&h).unwrap();
    let mutations: [fn(&mut Header);10]=[
        |h|h.parent_id[0]^=1,|h|h.ad_proofs_root[0]^=1,|h|h.transactions_root[0]^=1,|h|h.state_root[0]^=1,
        |h|h.timestamp^=1,|h|h.extension_root[0]^=1,|h|h.n_bits^=1,|h|h.height+=1,|h|h.votes[0]^=1,|h|h.timestamp=-1,
    ];
    for mutate in mutations {let mut changed=h.clone();mutate(&mut changed);let raw=changed.encode().unwrap();assert_ne!(raw,before);assert_ne!(message(&changed).unwrap(),digest);}
    let mut extended=fixture(V2_VALID_JSON);extended.version=5;extended.unparsed_bytes=vec![0x42];let a=message(&extended).unwrap();
    extended.unparsed_bytes[0]^=1;assert_ne!(message(&extended).unwrap(),a);
    let raw=extended.encode().unwrap();assert_eq!(message(&extended).unwrap(),hash(&raw[..raw.len()-41]));
    // Hash binding is asserted; a changed message is not universally invalid PoW.
}

#[test]
fn native_pow_07_strict_target_and_compact_branches() {
    let t=BigUint::from(101u8);assert_eq!(strict_target(&BigUint::from(100u8),&t),Ok(()));
    assert_eq!(strict_target(&t,&t),Err(NativePowError::Target));assert_eq!(strict_target(&BigUint::from(102u8),&t),Err(NativePowError::Target));
    assert_eq!(difficulty(0x0300_0100).unwrap(),difficulty(0x0201_0000).unwrap());
    assert_eq!(difficulty(0x0201_00ff).unwrap(),BigUint::from(256u32));assert_eq!(difficulty(0x0101_ffff).unwrap(),BigUint::one());
    for bits in [0,0x0300_0000,0x0380_0001,0x0100_ffff,0x0001_0000]{assert_eq!(difficulty(bits),Err(NativePowError::Difficulty));}
    // Larger native difficulty is legal; it may make the strict target zero.
    let large=difficulty(0xff7f_ffff).unwrap();assert!(large.bits()>224);assert_eq!(strict_target(&BigUint::zero(),&(order()/large)),Err(NativePowError::Target));
    for bits in [0x0300_0100,0x0201_0000,0x1e00_0001] {assert_eq!(difficulty(bits).unwrap(),crate::work_tree_work::native_decode(bits).unwrap());}
    let mut h=h2();h.n_bits=0x0380_0001;assert_eq!(verify_header(&h),Err(NativePowError::Difficulty));
    h.height=u32::MAX;assert_eq!(verify_header(&h),Err(NativePowError::Encoding));
}

#[test]
fn native_pow_08_n_rounding_transition_and_cap() {
    for (height,n) in [(0,67_108_864),(614_399,67_108_864),(614_400,70_464_240),(614_401,70_464_240),(665_599,70_464_240),(665_600,73_987_410),(788_400,81_571_035),(1_051_200,104_107_290),(4_198_400,2_143_944_600),(u32::MAX,2_143_944_600)]{assert_eq!(table_size(height,2),n);assert_eq!(table_size(height,1),N_BASE);}
    let mut expected=67_108_864u64;
    for step in 0..=70u32 {let boundary=614_400+step*51_200;assert_eq!(u64::from(table_size(boundary-1,2)),expected);expected=(expected/100)*105;assert_eq!(u64::from(table_size(boundary,2)),expected);assert_eq!(u64::from(table_size(boundary+1,2)),expected);}
    assert_ne!(70_464_240u64,(67_108_864u64*105)/100);
}

#[test]
fn native_pow_09_all_signed_version_dispatch_and_extensions() {
    let template=fixture(V2_VALID_JSON);let PowSolution::V2{pk,nonce}=template.pow.clone() else{unreachable!()};
    for byte in 0u8..=255 {let mut h=template.clone();h.version=byte as i8;
        h.unparsed_bytes=if h.version>4{vec![byte,0x55]}else{Vec::new()};
        if h.version==1 {h.pow=h2().pow;let raw=h.encode().unwrap();assert_eq!(message(&h).unwrap(),hash(&raw[..raw.len()-102]));}
        else {h.pow=PowSolution::V2{pk,nonce};let raw=h.encode().unwrap();assert_eq!(Header::decode(&raw,None).unwrap(),h);assert_eq!(message(&h).unwrap(),hash(&raw[..raw.len()-41]));
            let hit=BigUint::from_bytes_be(&v2_hit(&message(&h).unwrap(),&nonce,h.height).unwrap());assert_eq!(verify_header(&h),strict_target(&hit,&(order()/difficulty(h.n_bits).unwrap())));}
        let mut mismatch=h.clone();mismatch.pow=if h.version==1{PowSolution::V2{pk,nonce}}else{h2().pow};assert_eq!(verify_header(&mismatch),Err(NativePowError::Encoding));
        if h.version<=4 {let mut bad=h;bad.unparsed_bytes.push(1);assert_eq!(verify_header(&bad),Err(NativePowError::Encoding));}
    }
    let mut excessive=template;excessive.version=5;excessive.unparsed_bytes=vec![1;256];assert_eq!(verify_header(&excessive),Err(NativePowError::Encoding));
}

#[test]
fn native_pow_10_modq_m_index_and_unreduced_width() {
    let q=order();let qm1=magnitude32(&(&q-BigUint::one())).unwrap();let qp1=magnitude32(&(&q+BigUint::one())).unwrap();
    for accepted in [[0;32],qm1] {let mut calls=0;assert_eq!(mod_q_with(accepted,|_|{calls+=1;panic!("accepted digest must not rehash")}),BigUint::from_bytes_be(&accepted));assert_eq!(calls,0);}
    let mut calls=0;assert_eq!(mod_q_with(Q_BE,|input|{calls+=1;assert_eq!(input,Q_BE);qm1}),&q-BigUint::one());assert_eq!(calls,1);
    let mut calls=0;assert_eq!(mod_q_with([0xff;32],|input|{calls+=1;match calls{1=>{assert_eq!(input,[0xff;32]);qp1},2=>{assert_eq!(input,qp1);Q_BE},3=>{assert_eq!(input,Q_BE);[0;32]},_=>panic!("unexpected rejection iteration")}}),BigUint::zero());assert_eq!(calls,3);
    let m=m_bytes();for i in 0..1024usize{assert_eq!(&m[i*8..i*8+8],&(i as u64).to_be_bytes());}
    assert_eq!(&m[8184..],&1023u64.to_be_bytes());
    let seed=std::array::from_fn(|i|i as u8);let windows=indices(&seed,u32::MAX);
    assert_eq!(windows[0],0x0001_0203);assert_eq!(windows[28],0x1c1d_1e1f);assert_eq!(windows[29],0x1d1e_1f00);assert_eq!(windows[30],0x1e1f_0001);assert_eq!(windows[31],0x1f00_0102);
    assert_eq!(indices(&[0xff;32],N_BASE),[N_BASE-1;32]);
    assert_eq!(magnitude32(&BigUint::zero()).unwrap(),[0;32]);assert_eq!(magnitude32(&(&q+BigUint::one())).unwrap(),qp1);
    let max_term=(BigUint::one()<<248usize)-BigUint::one();let sum=&max_term*BigUint::from(32u8);assert_eq!(sum.bits(),253);assert_eq!(BigUint::from_bytes_be(&magnitude32(&sum).unwrap()),sum);
    assert_eq!(magnitude32(&(BigUint::one()<<256usize)),Err(NativePowError::Sum));
}

#[test]
fn native_pow_11_owning_membership_join_and_resealed_invalid_pow() {
    let prefix=NativePrefix::from_raw_iter(3,local_raws().into_iter().map(Ok)).unwrap();
    let root=prefix.root();let total=prefix.total_be28();let (lower,upper)=prefix.interval(2).unwrap();
    let sibling=prefix.leaf_digest(1).unwrap();let raw=prefix.raw(2).unwrap().to_vec();
    let opening=NativeWorkOpening::new(0,lower,upper,raw.clone(),vec![sibling]);
    let context=NativeWorkMembershipContext::new(3,root,total).unwrap();let membership=context.verify(lower,&opening).unwrap();
    let identity=(membership.headers(),membership.root(),membership.total_be28(),membership.profile(),membership.coordinate_be28(),membership.position(),membership.height(),membership.interval_be28());
    let promoted=verify_membership(membership).unwrap();let m=promoted.membership();
    assert_eq!((m.headers(),m.root(),m.total_be28(),m.profile(),m.coordinate_be28(),m.position(),m.height(),m.interval_be28()),identity);assert_eq!(m.raw(),raw);assert_eq!(m.header().encode().unwrap(),raw);
    let mut changed=h2();nonce_flip(&mut changed);let changed_raw=changed.encode().unwrap();assert_ne!(changed_raw,raw);
    let substituted=NativeWorkOpening::new(0,lower,upper,changed_raw.clone(),vec![sibling]);
    assert!(matches!(context.verify(lower,&substituted),Err(NativeWorkOpeningError::RootMismatch)));
    // A self-consistent supplied root proves membership, not PoW. Rebuild only
    // the changed leaf and parent using literal domain bytes, bypassing no API.
    let mut leaf=vec![b'L'];leaf.extend_from_slice(&identity.3);leaf.extend_from_slice(&3u32.to_be_bytes());leaf.extend_from_slice(&2u32.to_be_bytes());leaf.extend_from_slice(&lower);leaf.extend_from_slice(&upper);leaf.extend_from_slice(&(changed_raw.len() as u16).to_be_bytes());leaf.extend_from_slice(&changed_raw);
    let mut parent=vec![b'N',1];parent.extend_from_slice(&0u32.to_be_bytes());parent.extend_from_slice(&hash(&leaf));parent.extend_from_slice(&sibling);
    let resealed=NativeWorkMembershipContext::new(3,hash(&parent),total).unwrap().verify(lower,&substituted).unwrap();
    assert_eq!(resealed.header().encode().unwrap(),changed_raw);assert!(matches!(verify_membership(resealed),Err(NativePowError::Equation)));
    assert_eq!(promoted.into_membership().raw(),raw);
    // A detached-header argument/private-field mutation is inexpressible through
    // the ordinary API. No unsafe constructor is introduced to simulate one.
}

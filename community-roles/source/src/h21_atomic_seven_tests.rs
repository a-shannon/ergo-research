//! Transport and actual-consumer controls. No H21 success packet, private
//! verified claim, native source or PCS acceptance path is fabricated here.
use super::*;
use super::super as historical;
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use blake2::{digest::consts::U32,Blake2b,Digest};
use crate::legacy_envelope_map::{LowerBranch,LowerSelector,LowerSource};
use dory_pcs::{backends::arkworks::ArkGT,primitives::arithmetic::Group};

const KEY41: &[u8] = include_bytes!("../fixtures/verifier-keys-v1/log41.vk");
fn parameters() -> [historical::PublicMapParameters;2] {
    crate::bank53_map::CutDescriptor::eligible08().terminals().map(|terminal|
        historical::PublicMapParameters {terminal,exponent:55,
            lower:LowerSelector {source:LowerSource::HeaderDifficulty {height:841_729},
                branch:LowerBranch::Pivot(54)}})
}
fn statement() -> codec::H21Statement {
    codec::H21Statement {root:[0x31;32],total:[0x42;28],tip:[0x52;32],tip_time:1,parameters:parameters()}
}
fn commitment() -> Vec<u8> { pcs::encode_commitment(&ArkGT::identity()).unwrap() }
fn state(t:&Transcript) -> (u64,u64,u64) { (t.challenges(),t.raw_queries(),t.bytes_absorbed()) }
fn rejected<T>(result:Result<T,String>) -> String {
    match result {Ok(_)=>panic!("expected rejection"),Err(error)=>error}
}

// A framing fixture only: its scalar streams are canonical, but its common
// bytes are deliberately not a proof. No test treats this as H21 acceptance.
fn transport() -> Result<codec::DecodedH21Packet,String> {
    let statement=statement();
    Ok(codec::DecodedH21Packet {statement_bytes:codec::encode_statement(&statement)?,statement,
        key:KEY41.to_vec(),commitment:commitment(),
        roles:std::array::from_fn(|role|vec![0;codec::GKR_BYTES[role]]),common:vec![1]})
}
struct Offsets { fields:[usize;3],roles:[usize;7],common:usize }
fn offsets(bytes:&[u8]) -> Offsets {
    let mut at=12;
    let fields=std::array::from_fn(|_| {
        let start=at;
        let n=u32::from_le_bytes(bytes[at+1..at+5].try_into().unwrap())as usize;
        at+=5+n;start
    });
    let roles=std::array::from_fn(|_| {
        let start=at;
        let n=u32::from_le_bytes(bytes[at+5..at+9].try_into().unwrap())as usize;
        at+=9+n;start
    });
    Offsets {fields,roles,common:at}
}

#[test]
fn c594_h21_statement_roundtrip_preserves_each_public_field_and_selector() -> Result<(),String> {
    let original=statement();let wire=codec::encode_statement(&original)?;
    assert_eq!(wire.len(),226);assert_eq!(codec::decode_statement(&wire)?,original);
    for field in 0..4 {
        let mut changed=original.clone();
        match field {0=>changed.root[0]^=1,1=>changed.total[27]^=1,2=>changed.tip[31]^=1,_=>changed.tip_time=-1}
        let encoded=codec::encode_statement(&changed)?;
        assert_ne!(encoded,wire);assert_eq!(codec::decode_statement(&encoded)?,changed);
    }
    let variants=[
        (55,LowerSelector {source:LowerSource::HeaderDifficulty {height:841_729},branch:LowerBranch::Equality}),
        (55,LowerSelector {source:LowerSource::LegacyBound {q:1},branch:LowerBranch::Pivot(0)}),
        (40,LowerSelector {source:LowerSource::InitialI,branch:LowerBranch::Literal}),
        (40,LowerSelector {source:LowerSource::Reset417792,branch:LowerBranch::Literal}),
        (40,LowerSelector {source:LowerSource::Reset417793,branch:LowerBranch::Literal}),
    ];
    for (exponent,lower) in variants {
        let mut changed=original.clone();changed.parameters[0].exponent=exponent;changed.parameters[0].lower=lower;
        let encoded=codec::encode_statement(&changed)?;
        assert_eq!(codec::decode_statement(&encoded)?,changed);
        if matches!(lower.source,LowerSource::InitialI|LowerSource::Reset417792|LowerSource::Reset417793) {
            let mut noncanonical=encoded.clone();noncanonical[174]=1;
            assert!(codec::decode_statement(&noncanonical).is_err(),"fixed source reserved value");
        }
        if matches!(lower.branch,LowerBranch::Literal|LowerBranch::Equality) {
            let mut noncanonical=encoded;noncanonical[183]=1;
            assert!(codec::decode_statement(&noncanonical).is_err(),"fixed branch reserved value");
        }
    }
    Ok(())
}

#[test]
fn c594_h21_statement_rejects_single_fault_headers_parameters_and_eof() -> Result<(),String> {
    let wire=codec::encode_statement(&statement())?;
    for at in [0,8,9,10,11,12,44,52,53,54,55,156,191] {
        let mut changed=wire.clone();changed[at]^=0x80;
        assert!(codec::decode_statement(&changed).is_err(),"statement byte {at}");
    }
    for base in [156usize,191] {
        for (relative,value) in [(1,1u64),(9,65),(18,0),(27,224)] {
            let mut changed=wire.clone();
            if relative==1 {
                let old=u64::from_le_bytes(wire[base+1..base+9].try_into().unwrap());
                changed[base+1..base+9].copy_from_slice(&(old+value).to_le_bytes());
            }else{changed[base+relative..base+relative+8].copy_from_slice(&value.to_le_bytes());}
            assert!(codec::decode_statement(&changed).is_err(),"parameter {base}, field {relative}");
        }
        for relative in [17usize,26] {
            let mut changed=wire.clone();changed[base+relative]=0xff;
            assert!(codec::decode_statement(&changed).is_err(),"selector tag {relative}");
        }
    }
    assert!(codec::decode_statement(&wire[..wire.len()-1]).is_err());
    let mut trailing=wire.clone();trailing.push(0);assert!(codec::decode_statement(&trailing).is_err());
    assert!(codec::decode_statement(&vec![0;codec::MAX_STATEMENT_BYTES+1]).is_err());
    Ok(())
}

#[test]
fn c594_h21_packet_roundtrip_rejects_each_tag_length_role_and_trailing_field() -> Result<(),String> {
    let wire=codec::encode_packet(&transport()?)?;let at=offsets(&wire);
    let decoded=codec::decode_packet(&wire)?;
    assert_eq!(codec::encode_packet(&decoded)?,wire);
    for index in [0,8,9,10,11,at.fields[0],at.fields[1],at.fields[2],at.common,
        at.common+1,at.common+2,at.common+3,wire.len()-1] {
        let mut changed=wire.clone();changed[index]^=0x80;
        assert!(codec::decode_packet(&changed).is_err(),"packet tag/header {index}");
    }
    for (offset,bad) in [(at.fields[0]+1,8193u32),(at.fields[1]+1,42863),
        (at.fields[2]+1,383),(at.common+4,65537),(at.common+4,0)] {
        let mut changed=wire.clone();changed[offset..offset+4].copy_from_slice(&bad.to_le_bytes());
        assert!(codec::decode_packet(&changed).is_err(),"packet length {offset}");
    }
    for (role,start) in at.roles.into_iter().enumerate() {
        for relative in 0..5 {
            let mut changed=wire.clone();changed[start+relative]^=0x80;
            assert!(codec::decode_packet(&changed).is_err(),"role {role}, header {relative}");
        }
        let mut changed=wire.clone();changed[start+5..start+9].copy_from_slice(&u32::MAX.to_le_bytes());
        assert!(codec::decode_packet(&changed).is_err(),"role {role} length");
    }
    let mut changed=decoded.clone();changed.statement_bytes[56]^=1;
    assert!(codec::encode_packet(&changed).is_err(),"DTO cannot disagree with its public bytes");
    assert!(codec::decode_packet(&wire[..wire.len()-1]).is_err());
    let mut trailing=wire;trailing.push(0);assert!(codec::decode_packet(&trailing).is_err());
    assert!(codec::decode_packet(&vec![0;codec::MAX_PACKET_BYTES+1]).is_err());
    Ok(())
}

#[test]
fn c594_h21_preflight_rejects_key_c_scalars_and_common_before_context() -> Result<(),String> {
    let before=historical::next36_constructions();
    let base=transport()?;
    let mut wrong_key=base.clone();wrong_key.key[100]^=1;
    assert_eq!(rejected(preflight_packet(&wrong_key)),rejected(verifier_key::admit(41,&wrong_key.key)));
    let mut wrong_log=base.clone();wrong_log.key=include_bytes!("../fixtures/verifier-keys-v1/log22.vk").to_vec();
    assert_eq!(rejected(preflight_packet(&wrong_log)),rejected(verifier_key::admit(41,&wrong_log.key)));
    for bad in [vec![0xff;384],base.commitment[..383].to_vec(),[base.commitment.as_slice(),&[0u8]].concat()] {
        let mut changed=base.clone();changed.commitment=bad;
        assert_eq!(rejected(preflight_packet(&changed)),rejected(pcs::decode_commitment(&changed.commitment)));
    }
    for role in 0..7 {
        let mut changed=base.clone();changed.roles[role][..32].fill(0xff);
        assert_eq!(rejected(preflight_packet(&changed)),rejected(gkr::decode_dimensions(
            &[codec::INPUT_BITS[role]as usize],&changed.roles[role])),"role {role} canonical field rejection");
    }
    let common_error=rejected(opening_batch::decode_proof(&base.common,41));
    assert_eq!(rejected(preflight_packet(&base)),common_error,"valid preceding codecs reach common framing");
    assert_eq!(rejected(verify_h21_packet(&codec::encode_packet(&base)?)),common_error);
    assert_eq!(historical::next36_constructions(),before);
    Ok(())
}

#[test]
fn c594_h21_point_projection_keeps_local_bank_and_owner_coordinates() -> Result<(),String> {
    let local:Vec<_>=(0..34).map(|i|Fr::from((i+2)as u64)).collect();
    let projected=layout::embed_bank(786_432,8192,21,&local)?;
    assert_eq!(projected.len(),41);assert_eq!(&projected[..13],&local[..13]);
    assert_eq!(&projected[13..20],&[Fr::zero(),Fr::zero(),Fr::zero(),Fr::zero(),Fr::zero(),Fr::one(),Fr::one()]);
    assert_eq!(&projected[20..],&local[13..]);
    assert_ne!(projected,layout::embed_bank(778_240,8192,21,&local)?);
    let mut misplaced=local.clone();misplaced.swap(12,13);
    assert_ne!(projected,layout::embed_bank(786_432,8192,21,&misplaced)?);
    assert!(layout::embed_bank(786_433,8192,21,&local).is_err());
    assert!(layout::embed_bank(786_432,8192,21,&local[..33]).is_err());
    Ok(())
}

#[test]
fn c594_h21_role_prefixes_bind_public_identity_c_key_and_role_before_queries() -> Result<(),String> {
    let key=verifier_key::admit(41,KEY41)?;let c=commitment();
    let identity=codec::encode_statement(&statement())?;
    let mut first=Vec::new();
    for role in 0..7 {
        let mut t=fresh_h21_role_prefix(&identity,&key,&c,role)?;
        assert_eq!((t.challenges(),t.raw_queries()),(0,0));
        let challenge=t.challenge_scalar(b"first-prefix-query");
        assert!(!first.contains(&challenge));first.push(challenge);
    }
    assert!(fresh_h21_role_prefix(&identity,&key,&c,7).is_err());
    for changed_field in 0..10 {
        let mut changed=statement();
        match changed_field {0=>changed.root[0]^=1,1=>changed.tip[0]^=1,
            2=>changed.parameters[0].exponent=54,3=>changed.parameters[1].exponent=54,
            4=>changed.total[27]^=1,5=>changed.tip_time+=1,
            6=>changed.parameters[0].lower.source=LowerSource::HeaderDifficulty {height:841_730},
            7=>changed.parameters[1].lower.source=LowerSource::HeaderDifficulty {height:841_730},
            8=>changed.parameters[0].lower.branch=LowerBranch::Pivot(56),
            _=>changed.parameters[1].lower.branch=LowerBranch::Pivot(56)}
        let other=codec::encode_statement(&changed)?;
        for role in 0..7 {
            let mut t=fresh_h21_role_prefix(&other,&key,&c,role)?;
            assert_eq!((t.challenges(),t.raw_queries()),(0,0));
            assert_ne!(t.challenge_scalar(b"first-prefix-query"),first[role],
                "isolated public field {changed_field}, role {role}");
        }
    }
    let other=pcs::encode_commitment(&key.verifier().ht)?;
    assert_ne!(other,c);
    for role in 0..7 {
        assert_ne!(fresh_h21_role_prefix(&identity,&key,&other,role)?.challenge_scalar(b"first-prefix-query"),first[role]);
    }
    let wrong_id=verifier_key::admit_generated_test_key(41,KEY41,[0x99;32])?;
    for role in 0..7 {assert!(fresh_h21_role_prefix(&identity,&wrong_id,&c,role).is_err());}
    Ok(())
}

#[test]
#[ignore="one actual H21 public context; separate 2 GiB/120 s diagnostic Job required"]
fn c594_h21_actual_context_uses_c592_prefix_new_role1_and_exact_point_projection() -> Result<(),String> {
    let owned=historical::H21StructuralDiagnostic::compile([0x31;32],[0x42;28],[0x52;32],1,parameters())?;
    let context=owned.context()?;
    let key=verifier_key::admit(41,KEY41)?;let c=commitment();
    for role in 0..7 {
        let mut t=fresh_h21_role_prefix(context.public_bytes,&key,&c,role)?;
        bind_h21_role(&context,role,&mut t)?;
        assert_eq!((t.challenges(),t.raw_queries()),(0,0));
        t.challenge_scalar(b"already-queried");let before=state(&t);
        assert!(bind_h21_role(&context,role,&mut t).is_err());assert_eq!(state(&t),before);
    }
    let admission=context.admit_role0_diagnostic(KEY41,&c)?;
    let mut previous=admission.inputs.fresh_transcript()?;admission.bind_role0(&mut previous)?;
    let mut joined=fresh_h21_role_prefix(context.public_bytes,&key,&c,0)?;
    bind_h21_role(&context,0,&mut joined)?;
    assert_eq!(state(&previous),state(&joined));
    assert_eq!(previous.challenge_scalar(b"first-query"),joined.challenge_scalar(b"first-query"));
    let bits=|value:usize,n| (0..n).map(|bit|Fr::from(((value>>bit)&1)as u64)).collect::<Vec<_>>();
    let r=bits(1_810_841*(1<<19)+506_925+17,40);
    let u=bits(1_810_840*(1<<20)+987_450+17,41);let v=bits(0,41);
    assert_eq!(historical::role_coefficients(context.refs(),1,&r,&u,&v)?,[Fr::zero();4]);
    assert_eq!(context.coefficients(1,&r,&u,&v)?,[Fr::zero(),-Fr::one(),Fr::zero(),Fr::zero()]);
    let point:Vec<_>=(0..34).map(|i|Fr::from((i+2)as u64)).collect();
    assert_eq!(context.point_role.project(&point)?,layout::embed_bank(786_432,8192,21,&point)?);
    let mut invalid=gkr::decode_dimensions(&[41],&vec![0;(7*41+3)*32])?;
    invalid.layers[0].left_value=Fr::one();invalid.layers[0].line_coefficients[0]=Fr::one();
    invalid.layers[0].line_coefficients[1]=-Fr::one();
    assert_eq!(verify_h21_role(&context,&key,&c,0,&invalid),Err(GkrError::TerminalExpression.to_string()));
    for role in 1..7 {
        let dimension=codec::INPUT_BITS[role]as usize;
        let base=gkr::decode_dimensions(&[dimension],&vec![0;codec::GKR_BYTES[role]])?;
        let terminal=GkrError::TerminalExpression.to_string();
        let expected=if role==3 {terminal}else{format!("H21 atomic role {role}: {terminal}")};
        let mut reached_terminal=false;let mut accepted=0usize;let mut other_errors=Vec::new();
        for (a,b) in [(Fr::zero(),Fr::zero()),(Fr::zero(),Fr::one()),
            (Fr::one(),Fr::zero()),(Fr::one(),Fr::one())] {
            let mut corner=base.clone();
            corner.layers[0].left_value=a;corner.layers[0].right_value=b;
            corner.layers[0].line_coefficients[0]=a;
            corner.layers[0].line_coefficients[1]=b-a;
            let corner=gkr::decode_dimensions(&[dimension],&gkr::encode_proof(&corner)?)?;
            // Every zero sumcheck identity and both line endpoints hold.
            // This exact terminal error occurs only after the real public
            // wiring callback, including PointMath's sparse binder for role3.
            match verify_h21_role(&context,&key,&c,role,&corner) {
                Err(error) if error==expected => {reached_terminal=true;break;},
                Err(error) => other_errors.push(error),
                Ok(claim) => {
                    // A GKR input claim alone has no common PCS or history
                    // authority. A homogeneous corner may legitimately pass.
                    accepted+=1;assert_eq!(claim.point.len(),41);
                    if role==3 {
                        assert_eq!(&claim.point[13..20],&[Fr::zero(),Fr::zero(),Fr::zero(),
                            Fr::zero(),Fr::zero(),Fr::one(),Fr::one()]);
                    }
                },
            }
        }
        assert!(reached_terminal,"role {role}: no real terminal rejection; accepted={accepted}, other_errors={other_errors:?}");
    }
    Ok(())
}

#[cfg(windows)]
#[test]
#[ignore="retained actual N3073 public packet/key/metadata; separate bounded diagnostic Job required"]
fn c594_actual_historical51_shared_finish_requires_frontend_and_pcs() -> Result<(),String> {
    use std::{fs::{File,OpenOptions},io::Read,path::{Path,PathBuf}};
    use std::os::windows::fs::{MetadataExt,OpenOptionsExt};
    struct Held {_file:File,bytes:Vec<u8>}
    fn env_path(name:&str)->Result<PathBuf,String> {
        let path=PathBuf::from(std::env::var_os(name).ok_or_else(||format!("missing {name}"))?);
        if !crate::preview_test_paths::absolute_outside_source(&path) {return Err("C594 external public input path".into());}
        Ok(path)
    }
    fn held(path:&Path,min:usize,max:usize)->Result<Held,String> {
        let md=std::fs::symlink_metadata(path).map_err(|e|e.to_string())?;
        if !md.is_file()||md.file_type().is_symlink()||md.file_attributes()&0x400!=0
            ||md.len()<min as u64||md.len()>max as u64 {return Err("C594 bounded regular public input".into());}
        let mut file=OpenOptions::new().read(true).share_mode(1).open(path).map_err(|e|e.to_string())?;
        if file.metadata().map_err(|e|e.to_string())?.len()!=md.len() {return Err("C594 held public extent".into());}
        let mut bytes=vec![0;md.len()as usize];file.read_exact(&mut bytes).map_err(|e|e.to_string())?;
        let mut extra=[0u8;1];if file.read(&mut extra).map_err(|e|e.to_string())?!=0 {return Err("C594 public input EOF".into());}
        Ok(Held {_file:file,bytes})
    }
    let directory=env_path("NIPOPOW_COMMON51_PUBLIC_DIR")?;
    let names=["statement.bin","commitment.bin","role-0.gkr","role-1.gkr","role-2.gkr","role-3.gkr",
        "role-4.gkr","role-5.gkr","role-6.gkr","common-opening.bin"];
    let mut files=Vec::with_capacity(10);
    for (index,name) in names.iter().enumerate() {
        let size=match index {0=>571,1=>384,5=>5696,2..=8=>7264,_=>65536};
        files.push(held(&directory.join(name),if index==9 {1}else{size},size)?);
    }
    let key=held(&env_path("NIPOPOW_COMMON51_KEY_PATH")?,33264,33264)?;
    let metadata=held(&env_path("NIPOPOW_COMMON51_KEY_METADATA_PATH")?,40,40)?;
    fn views<'a>(files:&'a[Held],common:&'a[u8])->historical::Historical51PublicBytes<'a> {
        historical::Historical51PublicBytes {frame:&files[0].bytes,commitment:&files[1].bytes,
            roles:std::array::from_fn(|role|files[role+2].bytes.as_slice()),common}
    }
    let policy=historical::Historical51TrustedKeyPolicy::fixed32_testonly();
    let base=views(&files,files[9].bytes.as_slice());
    let admitted=policy.admit_key(&base,&key.bytes,&metadata.bytes)?;
    let mut diagnostic=historical::Historical51Diagnostics::default();
    let success=historical::verify_historical_h12_bytes_observed51(&base,&key.bytes,&metadata.bytes,&policy,&mut diagnostic)?;
    assert_eq!(diagnostic.role_completions,[1;7]);assert_eq!(diagnostic.role_completion_order,[0,1,2,3,4,5,6]);
    assert_eq!((diagnostic.common_entries,diagnostic.frontend_entries,diagnostic.frontend_completions,
        diagnostic.pcs_entries,diagnostic.pcs_completions,diagnostic.successes),(1,1,1,1,1,1));
    let proof=opening_batch::decode_proof(base.common,32)?;
    let mut frontend=opening_batch::Proof {rounds:proof.rounds.clone(),terminal:proof.terminal,pcs:proof.pcs.clone()};
    frontend.rounds[0][0]+=Fr::one();let frontend=opening_batch::encode_proof(&frontend,32)?;
    let mut rejected=historical::Historical51Diagnostics::default();
    assert!(historical::verify_historical_h12_bytes_observed51(&views(&files,&frontend),&key.bytes,&metadata.bytes,&policy,&mut rejected).is_err());
    assert_eq!(rejected.role_completions,[1;7]);
    assert_eq!((rejected.frontend_entries,rejected.frontend_completions,rejected.pcs_entries,rejected.successes),(1,0,0,0));
    let mut pcs_only=opening_batch::Proof {rounds:proof.rounds.clone(),terminal:proof.terminal,pcs:proof.pcs.clone()};
    let zero=ArkGT::identity();let prior=pcs_only.pcs.vmv_message.c;
    pcs_only.pcs.vmv_message.c=if prior==zero {admitted.verifier().ht}else{zero};
    assert_ne!(pcs_only.pcs.vmv_message.c,prior);
    let pcs_only=opening_batch::encode_proof(&pcs_only,32)?;
    assert_eq!(opening_batch::encode_proof(&opening_batch::decode_proof(&pcs_only,32)?,32)?,pcs_only);
    let mut rejected=historical::Historical51Diagnostics::default();
    assert!(historical::verify_historical_h12_bytes_observed51(&views(&files,&pcs_only),&key.bytes,&metadata.bytes,&policy,&mut rejected).is_err());
    assert_eq!(rejected.role_completions,[1;7]);
    assert_eq!((rejected.frontend_entries,rejected.frontend_completions,rejected.pcs_entries,rejected.pcs_completions,rejected.successes),(1,1,1,0,0));
    let statement=opening_batch::Statement {log_n:32,setup_id:*admitted.id(),commitment:pcs::decode_commitment(base.commitment)?,
        corpus_id:Some(Blake2b::<U32>::digest(base.frame).into()),claims:success.claims};
    for index in 0..7 {
        let mut altered=statement.clone();altered.claims[index].value+=Fr::one();
        assert!(opening_batch::verify_admitted(&altered,&admitted,&proof).is_err(),"claim {index} must bind before alpha");
    }
    let mut altered=statement;altered.corpus_id=Some([0;32]);
    assert!(opening_batch::verify_admitted(&altered,&admitted,&proof).is_err());
    Ok(())
}

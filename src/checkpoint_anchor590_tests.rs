use super::*;

#[test]
fn c590_cold_environment_allows_only_packet_name() {
    let check=|names:&[&str]|validate_cold_environment_names(names.iter().map(|name|std::ffi::OsString::from(*name)));
    assert!(check(&[]).is_ok()); // The separate path lookup still requires its value.
    assert!(check(&["TEMP","NIPOPOW_C590_PACKET_PATH"]).is_ok());
    assert!(check(&["nipopow_c590_packet_path"]).is_ok());
    for name in ["NIPOPOW_UNKNOWN","NIPOPOW_COMMON51_PACK_PATH","NIPOPOW_COMMON51_PUBLIC_DIR",
        "NIPOPOW_C584_PREFIX_PATH","NIPOPOW_C590_PACKET_OUT","nipopow_hidden_source"] {
        assert!(check(&["NIPOPOW_C590_PACKET_PATH",name]).is_err());
    }
}

#[test]
fn c590_checkpoint_checked_height_and_95bit_integer_boundaries() {
    assert_eq!(floor_height(1024,3073).unwrap(),1087);
    assert_eq!(floor_height(3009,3073).unwrap(),3072);
    for h in [0,1,3010,u64::MAX] {assert!(floor_height(h,3073).is_err());}
    let mut total=[0;28];total[27]=9;let mut floor=[0;28];floor[27]=4;
    assert_eq!(difference(total,floor).unwrap()[27],5);
    assert!(difference(total,total).is_err());assert!(difference(floor,total).is_err());
    let mut top=[0;28];top[16]=0x7f;top[17..].fill(255);assert!(work95(top));
    top[16]=0x80;assert!(!work95(top));assert!(difference(top,floor).is_err());
    top=[0;28];top[15]=1;assert!(!work95(top));
}

#[test]
fn c590_checkpoint_codec_rejects_extent_truncation_trailing_and_unsupported_profile()->Result<(),String> {
    // Codec-only buffers never mint a VerifiedBase or checkpoint result.
    let frame=vec![0;571];let key=vec![0;33264];let metadata=vec![0;40];let c=vec![0;384];
    let roles:[Vec<u8>;7]=std::array::from_fn(|i|vec![0;if i==3{5696}else{7264}]);
    let base=Historical51PublicBytes {frame:&frame,commitment:&c,
        roles:std::array::from_fn(|i|roles[i].as_slice()),common:&[0]};
    let anchor=vec![0;70];let profile=diagnostic_profile();
    let packet=encode_parts(&base,&key,&metadata,&profile,1024,&[1],[0;28],&anchor,&anchor)?;
    let parsed=parse(&packet)?;assert_eq!(parsed.h,1024);assert_eq!(parsed.base.roles[3].len(),5696);
    for n in [0,7,8,packet.len()-1] {assert!(parse(&packet[..n]).is_err());}
    let mut trailing=packet.clone();trailing.push(0);assert!(parse(&trailing).is_err());
    let mut bad=packet.clone();bad[8..12].copy_from_slice(&513u32.to_le_bytes());assert!(parse(&bad).is_err());
    let mut bad=packet.clone();bad[12]^=1;
    assert!(verify_packet(&bad).err().unwrap().contains("unsupported diagnostic profile"));
    assert!(parse(&vec![0;MAX_PACKET_BYTES+1]).is_err());Ok(())
}

pub(super) fn native_negatives(result:&VerifiedCheckpoint<'_>)->Result<usize,String> {
    let profile=diagnostic_profile();let base=&result.base;let d=&result.data;
    let count=std::cell::Cell::new(0usize);
    let reject=|profile:&[u8],h:u64,raw:&[u8],audit:[u8;28],ah:&[u8],af:&[u8]|->Result<(),String> {
        if derive(base,profile,h,raw,audit,ah,af).is_ok() {return Err("C590 isolated checkpoint mutation accepted".into());}
        count.set(count.get()+1);Ok(())
    };
    let mut wrong=profile.clone();wrong[0]^=1;
    reject(&wrong,d.h,&d.raw,d.audit,&result.anchor_h,&result.anchor_f)?;
    for h in [1,u64::MAX,base.history.headers()as u64-63,d.h+1] {
        reject(&profile,h,&d.raw,d.audit,&result.anchor_h,&result.anchor_f)?;
    }
    let mut wrong_raw=d.raw.clone();*wrong_raw.last_mut().ok_or("C590 RAW empty")?^=1;
    reject(&profile,d.h,&wrong_raw,d.audit,&result.anchor_h,&result.anchor_f)?;
    let mut wrong_f=d.audit;wrong_f[27]^=1;
    reject(&profile,d.h,&d.raw,wrong_f,&result.anchor_h,&result.anchor_f)?;
    reject(&profile,d.h,&d.raw,[0;28],&result.anchor_h,&result.anchor_f)?;
    wrong_f=[0;28];wrong_f[16]=0x80;
    reject(&profile,d.h,&d.raw,wrong_f,&result.anchor_h,&result.anchor_f)?;
    reject(&profile,d.h,&d.raw,d.audit,&result.anchor_f,&result.anchor_h)?;
    let mut wrong_path=result.anchor_h.clone();*wrong_path.last_mut().ok_or("C590 opening empty")?^=1;
    reject(&profile,d.h,&d.raw,d.audit,&wrong_path,&result.anchor_f)?;
    let mut wrong_path=result.anchor_f.clone();wrong_path[12]^=1;
    reject(&profile,d.h,&d.raw,d.audit,&result.anchor_h,&wrong_path)?;
    let mut trailing=result.anchor_h.clone();trailing.push(0);
    reject(&profile,d.h,&d.raw,d.audit,&trailing,&result.anchor_f)?;
    reject(&profile,d.h,&d.raw,d.audit,&result.anchor_h,&result.anchor_f[..result.anchor_f.len()-1])?;
    // The namespace comes only from this result's actual base and paths.
    let encoded=result.encode()?;let parsed=parse(&encoded)?;
    if parsed.base.frame!=base.bytes.frame||parsed.base.roles!=base.bytes.roles
        ||parsed.base.common!=base.bytes.common||parsed.key!=base.key||parsed.metadata!=base.metadata
        ||parsed.anchor_h!=result.anchor_h||parsed.anchor_f!=result.anchor_f
        ||result.encode()?!=encoded {return Err("C590 verified envelope byte custody".into());}
    // A canonical changed GKR reaches the actual base verifier. It must not
    // receive acceptance merely because another base was previously verified.
    let mut proof=gkr::decode_dimensions(&[32],base.bytes.roles[0])?;
    proof.layers[0].rounds[0][0]+=Fr::one();let bad=gkr::encode_proof(&proof)?;
    let mut roles=base.bytes.roles;roles[0]=&bad;
    let changed=Historical51PublicBytes {frame:base.bytes.frame,commitment:base.bytes.commitment,
        roles,common:base.bytes.common};
    let mut diagnostic=Historical51Diagnostics::default();
    let outcome=verify_and_seal_historical_h12_prefix51(&changed,base.key,base.metadata,
        &Historical51TrustedKeyPolicy::fixed32_testonly(),&mut diagnostic);
    if outcome.is_ok()||diagnostic.role_entries[0]!=1||diagnostic.role_completions[0]!=0
        ||diagnostic.pcs_entries!=0||diagnostic.successes!=0 {return Err("C590 changed base did not reach real GKR rejection".into());}
    count.set(count.get()+1);Ok(count.get())
}

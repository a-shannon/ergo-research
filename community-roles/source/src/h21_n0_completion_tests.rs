use ark_serialize::CanonicalSerialize;

fn completion_timing(
    rows:&[Vec<u8>], u:&[Fr], v:&[Fr], setup_ns:u128,
    mut apply:impl FnMut(&[u8])->Result<Vec<Fr>,String>,
)->Result<(Vec<Fr>,serde_json::Value),String>{
    let mut line=vec![Fr::zero();42];
    let mut times=[0u128;4];
    for (i,(owner,_)) in ROWS.iter().enumerate(){
        let start=Instant::now();
        let local=apply(&rows[i])?;
        add_owner_line(&mut line,&local,*owner,&u[LOW..],&v[LOW..]);
        times[i]=start.elapsed().as_nanos();
    }
    let total:u128=times.iter().sum();
    Ok((line,serde_json::json!({"setup_ns":setup_ns,"owner_ns":times,"owner_total_ns":total})))
}

fn completion_edge(role:usize,rows:&[Vec<u8>],u:&[Fr],v:&[Fr],expected:&[Fr])->Result<(),String>{
    use super::super::{h21_packed_line::Admission,h21_sixbit_line,h21_role1_input,EdgeFullStats,PackedLineStats};
    let mut input=h21_role1_input(|owner|{
        let i=ROWS.iter().position(|(n,_)|*n==owner).ok_or("unexpected physical N0 owner")?;
        Ok(rows[i].clone())
    })?;
    let admission=Admission::new(role,1<<30,2<<30)?;
    assert_eq!(admission.sixbit(),matches!(role,2|4));
    assert!(Admission::new(role,1<<30,admission.required_bytes()-1).is_err());
    let mut fast=PackedLineStats::default();
    admission.configure(&input,LOW,HIGH,role==1,&mut fast)?;
    let mut stats=EdgeFullStats::default();
    let selected=h21_sixbit_line::selected_edge(Some(&admission),&mut input,u,v,ROWS.map(|(owner,_)|owner),
        Some(&mut fast),&mut stats,&mut |_|Ok(()))?;
    if matches!(role,1|6) {assert!(selected.is_none() && stats.owner_requests==0);return Ok(());}
    let line=selected.ok_or("N0 completion ignored its admitted six-bit role")?;
    assert_eq!(line.as_slice(),expected);
    assert_eq!((fast.owners,fast.coefficients,fast.builds,stats.owner_requests),(4,84,1,4));
    assert_eq!((fast.lut_fields,fast.work_fields),(h21_sixbit_line::LUT_FIELDS,h21_sixbit_line::WORK_FIELDS));
    Ok(())
}

fn completion_fields(fields:&[Fr])->Result<Vec<u8>,String>{
    let mut bytes=Vec::with_capacity(fields.len()*32);
    for field in fields { field.serialize_compressed(&mut bytes).map_err(|e|e.to_string())?; }
    Ok(bytes)
}

#[test]
#[ignore="four authenticated N0 owners in the final lines of tree, height/DAA and adjacency"]
fn n0_sixbit_completion_lines()->Result<(),String>{
    use super::super::{h21_packed_line::Admission,h21_sixbit_line::Plan};
    let path=PathBuf::from(std::env::var_os("NIPOPOW_H21_LINE_WITNESS").ok_or("missing N0 witness")?);
    if !path.is_absolute(){return Err("absolute N0 witness required".into());}
    let _held=packed::open_untrusted_held_regular(&path,1u64<<38)?;
    let file=packed::PackedFile::open_with_limit(&path,41,41)?;
    let mut rows=Vec::new();
    for (owner,pin) in ROWS{
        let row=file.read_h21_table_row(owner)?.into_bytes();
        assert_eq!(row.len(),WIDTH/8);
        assert_eq!(hash(&row)?,pin);
        rows.push(row);
    }
    for role in 0..7{
        let admission=Admission::new(role,1<<30,2<<30);
        assert_eq!(admission.is_ok(),matches!(role,1|2|4|6));
        if let Ok(a)=admission{assert_eq!(a.sixbit(),matches!(role,2|4));}
    }
    assert!(!Role::Core.sixbit() && Role::Adjacency.sixbit());
    let old_bound=packed_line_plan_bound(WIDTH,LOW)?;
    let new_bound=Plan::bound()?;
    assert!(new_bound<=old_bound);
    for case in ["general","full_field","one_equal","equal"]{
        let (u,v):(Vec<Fr>,Vec<Fr>)=if case=="full_field"{
            let mut t=Transcript::new(b"N0-sixbit-line-general-test");
            let u:Vec<_>=(0..41).map(|_|t.challenge_scalar(b"u")).collect();
            let v:Vec<_>=(0..41).map(|_|t.challenge_scalar(b"v")).collect();
            assert!(completion_fields(&u[..1])?[8..].iter().any(|x|*x!=0));
            assert!(completion_fields(&v[..1])?[8..].iter().any(|x|*x!=0));
            (u,v)
        }else{
            let u:Vec<_>=(0..41).map(|i|Fr::from(3+13*i as u64)).collect();
            let v=(0..41).map(|i|if case=="equal" || (case=="one_equal" && i==7){u[i]}else{Fr::from(5+19*i as u64)}).collect();
            (u,v)
        };
        // Independently evaluate each true owner's high-coordinate basis at 42 points.
        // Together with the original dense low line these determine the global polynomial.
        let mut independent=[Fr::zero();42];
        let mut ends=[Fr::zero();2];
        for (&(owner,_),row) in ROWS.iter().zip(&rows){
            let x:Vec<_>=(0..WIDTH).map(|i|Fr::from(((row[i/8]>>(i%8))&1) as u64)).collect();
            let local=gkr::line_polynomial(&x,&u[..LOW],&v[..LOW]);
            for (i,out) in independent.iter_mut().enumerate(){
                let t=Fr::from(i as u64);
                let point=gkr::line_point(&u,&v,t);
                let basis:Fr=point[LOW..].iter().enumerate().map(|(bit,p)|if (owner>>bit)&1==1{*p}else{Fr::one()-p}).product();
                *out+=basis*gkr::eval_polynomial(&local,t);
                if i<2 {ends[i]+=basis*gkr::mle(&x,&point[..LOW]).map_err(|e|e.to_string())?;}
            }
        }
        let three=||{
            let start=Instant::now();
            let mut plan=PackedLinePlan::new(WIDTH,&u[..LOW],&v[..LOW],old_bound)?;
            completion_timing(&rows,&u,&v,start.elapsed().as_nanos(),|row|plan.apply(row))
        };
        let six=||{
            let start=Instant::now();
            let mut plan=Plan::new(&u[..LOW],&v[..LOW],new_bound)?;
            completion_timing(&rows,&u,&v,start.elapsed().as_nanos(),|row|plan.apply(row))
        };
        let (reference,three_first)=three()?;
        let (second,six_second)=six()?;
        let (first,six_first)=six()?;
        let (last,three_second)=three()?;
        for (i,y) in independent.iter().enumerate(){assert_eq!(gkr::eval_polynomial(&reference,Fr::from(i as u64)),*y);}
        assert_eq!([reference[0],gkr::eval_polynomial(&reference,Fr::one())],ends);
        let want=suffix(&reference,ends)?;
        for role in [1,2,4,6]{completion_edge(role,&rows,&u,&v,&reference)?;}
        let (adjacency,n)=sum_rows(&Role::Adjacency,&u,&v,ROWS.map(|(n,_)|n),|owner|{
            let i=ROWS.iter().position(|(n,_)|*n==owner).ok_or("unexpected adjacency owner")?;
            Ok(rows[i].clone())
        })?;
        assert_eq!(n,4);
        for actual in [&second,&first,&last,&adjacency]{
            assert_eq!(*actual,reference);
            assert_eq!(suffix(actual,ends)?,want);
        }
        if case=="general"{
            let mut bad=rows[0].clone();
            let (tile,pos)=bad.chunks_exact(8).enumerate().find_map(|(i,b)|
                b[1..].iter().position(|x|*x!=b[0]).map(|j|(i,j+1))).ok_or("missing byte permutation")?;
            bad.swap(tile*8,tile*8+pos);
            assert!(Plan::new(&u[..LOW],&v[..LOW],new_bound-1).is_err());
            assert!(Plan::new(&u[..LOW-1],&v[..LOW],new_bound).is_err());
            let mut plan=Plan::new(&u[..LOW],&v[..LOW],new_bound)?;
            assert!(plan.apply(&bad[..WIDTH/8-1]).is_err());
            bad.push(0);assert!(plan.apply(&bad).is_err());bad.pop();
            let local=plan.apply(&rows[0])?;
            assert_ne!(plan.apply(&bad)?,local);
            let (mut good,mut wrong)=(vec![Fr::zero();42],vec![Fr::zero();42]);
            add_owner_line(&mut good,&local,ROWS[0].0,&u[LOW..],&v[LOW..]);
            add_owner_line(&mut wrong,&local,ROWS[1].0,&u[LOW..],&v[LOW..]);
            assert_ne!(good,wrong);
        }
        if case=="equal"{assert!(reference[1..].iter().all(Zero::is_zero));}
        if case=="one_equal"{assert!(reference[41].is_zero());}
        assert_eq!(want.0.len(),1408);
        let encoded=hash(&want.0)?;
        let historical=match case{
            "general"=>Some("1122c37a7414ba2a98f598ddea00f6bf49dc2cb9aa9c1e77e99712831db0ce73"),
            "one_equal"=>Some("c9b8db77ba5cfcb9f24d4d98447a55b4196cacbb985d39d673ce64ec2baf741a"),
            "equal"=>Some("5220253b231cbacd50c636947ae172386c3b6d514262592413bca8e1292680e9"),
            _=>None
        };
        if let Some(pin)=historical{assert_eq!(encoded,pin);}
        let mut claim=gkr::line_point(&u,&v,want.1);claim.push(want.2);
        assert_eq!(claim.len(),42);
        println!("N0_SIXBIT_LINE_VECTOR {}",serde_json::json!({
            "case":case,"roles":[2,4,5],"owners":ROWS.map(|(n,_)|n),"global_coefficients":reference.len(),
            "encoded_suffix_bytes":want.0.len(),"encoded_suffix_sha256":encoded,
            "projected_claim_sha256":hash(&completion_fields(&claim)?)?,
            "subsequent_challenge_sha256":hash(&completion_fields(&[want.3])?)?,
            "three_first":three_first,"six_second":six_second,"six_first":six_first,"three_second":three_second
        }));
    }
    println!("N0_SIXBIT_LINE_PARITY roles=2,4,5 owners=4 cases=4");
    Ok(())
}

//! Full-table line for the H21 core and adjacency producers on the held witness.
use super::{add_owner_line, packed_line_extra, packed_line_fields, packed_line_plan_bound, PackedLinePlan};
use crate::packed::{PackedOwnerBits, UntrustedH21CandidateFile};
use ark_bn254::Fr;
use ark_ff::Zero;

const LOW:usize=20;
const HIGH:usize=21;
pub(crate) const OWNERS:usize=1<<HIGH;
const WIDTH:usize=1<<LOW;

pub(crate) fn scratch_bytes()->Result<usize,String>{
    // One original row, old/new selector, 42-term accumulator and convolution;
    // the plan accounts for its allocated work, LUT and local coefficient result.
    let high_fields=2*(HIGH+1)+2*(LOW+HIGH+1)+2;
    [WIDTH/8,packed_line_plan_bound(WIDTH,LOW)?,packed_line_fields(high_fields)?,
        packed_line_extra()?,5*std::mem::size_of::<Vec<Fr>>()]
        .into_iter().try_fold(0usize,|n,v|n.checked_add(v).ok_or_else(||"H21 table line reservation overflow".into()))
}

fn sum_rows(role:&Role,u:&[Fr],v:&[Fr],owners:impl IntoIterator<Item=usize>,
    read:impl FnMut(usize)->Result<Vec<u8>,String>)->Result<(Vec<Fr>,usize),String>{
    if u.len()!=LOW+HIGH || v.len()!=LOW+HIGH{return Err("H21 table line dimensions".into());}
    let reserved=packed_line_plan_bound(WIDTH,LOW)?;
    if role.sixbit(){
        // The sealed log41 role-5 budget covers the incumbent plan; enforce it on the child plan too.
        let mut plan=super::h21_sixbit_line::Plan::new(&u[..LOW],&v[..LOW],reserved)?;
        sum_rows_with(u,v,owners,read,|row|plan.apply(row))
    }else{
        let mut plan=PackedLinePlan::new(WIDTH,&u[..LOW],&v[..LOW],reserved)?;
        sum_rows_with(u,v,owners,read,|row|plan.apply(row))
    }
}

fn sum_rows_with(u:&[Fr],v:&[Fr],owners:impl IntoIterator<Item=usize>,
    mut read:impl FnMut(usize)->Result<Vec<u8>,String>,
    mut apply:impl FnMut(&[u8])->Result<Vec<Fr>,String>)->Result<(Vec<Fr>,usize),String>{
    let mut line=vec![Fr::zero();LOW+HIGH+1];
    let mut count=0;
    for owner in owners{
        if owner>=OWNERS{return Err("H21 table line owner".into());}
        let row=read(owner)?;
        if row.len()!=WIDTH/8 || row.capacity()!=WIDTH/8{return Err("H21 table line packed extent".into());}
        let local=apply(&row)?;
        add_owner_line(&mut line,&local,owner,&u[LOW..],&v[LOW..]);
        count+=1;
    }
    Ok((line,count))
}

pub(crate) enum Role { Core, Adjacency }
impl Role {
    fn sixbit(&self)->bool { cfg!(feature="h21-snapshot-n0") && matches!(self,Self::Adjacency) }
}

pub(crate) fn full(role:Role,source:&UntrustedH21CandidateFile,u:&[Fr],v:&[Fr])->Result<Vec<Fr>,String>{
    if source.untrusted_polynomial().input_len()!=WIDTH*OWNERS{return Err("H21 table line witness extent".into());}
    let started=std::time::Instant::now();
    let (line,count)=sum_rows(&role,u,v,0..OWNERS,|owner|source.read_copy(owner).map(PackedOwnerBits::into_bytes))?;
    if count!=OWNERS{return Err("incomplete H21 full table line".into());}
    println!("H21_TABLE_LINE {}",serde_json::json!({"role":match role{Role::Core=>0,Role::Adjacency=>5},
        "owners":count,"packed_input_bytes":count*(WIDTH/8),"local_coefficients":count*(LOW+1),
        "global_coefficients":line.len(),"plan_builds":1,"packed_scratch_bound":scratch_bytes()?,
        "elapsed_ns":started.elapsed().as_nanos()}));
    if role.sixbit() { super::h21_sixbit_line::report(5,count); }
    Ok(line)
}

#[cfg(all(windows,feature="h21-snapshot-n0"))]
mod tests{
    use super::*;
    use crate::{core_pool_boolean,gkr,packed,segment_adjacency::linear_for_test,transcript::Transcript};
    use ark_ff::One;
    use std::path::PathBuf;
    use std::time::Instant;

    const ROWS:[(usize,&str);4]=[
        (0,"e4132d69ccb280d235bb818055febd9ca000b5c94dbf49a6225d2f9ba528fe58"),
        (600023,"07bd32a9a66037bb94837f0cf32be4ad3c4358e6ef725816f819ca2156283c65"),
        (1804170,"975e9f79703a3e4c0d1033f7f5703ac63327f2882232227425fc4864719779a8"),
        (1819648,"8398a2898c274d80b79e104091846583b5869644fa644adee60a35c0a7d76530"),
    ];

    fn hash(bytes:&[u8])->Result<String,String>{
        Ok(crate::native_prefix_auth_plan::role0_sha256(bytes)?.iter().map(|b|format!("{b:02x}")).collect())
    }

    fn endpoints(p:&packed::PackedFile,point:&[Fr])->Result<Fr,String>{
        let weights=gkr::eq_weights(&point[..LOW]);
        let mut value=Fr::zero();
        for (owner,_) in ROWS{
            let row=p.read_h21_table_row(owner)?;
            let local:Fr=weights.iter().enumerate().filter(|(i,_)|row.bit_at(*i)).map(|(_,w)|*w).sum();
            let high:Fr=point[LOW..].iter().enumerate().map(|(i,x)|if owner>>i&1==1{*x}else{Fr::one()-x}).product();
            value+=local*high;
        }
        Ok(value)
    }

    fn suffix(line:&[Fr],ends:[Fr;2])->Result<(Vec<u8>,Fr,Fr,Fr),String>{
        let bytes=gkr::encode_proof(&gkr::GkrProof{layers:vec![gkr::LayerProof{rounds:vec![],
            left_value:ends[0],right_value:ends[1],line_coefficients:line.to_vec()}]})?;
        let mut t=Transcript::new(b"historical-core-adjacency-line-control");
        t.append_scalar(b"gkr-left-value",&ends[0]);t.append_scalar(b"gkr-right-value",&ends[1]);
        gkr::append_polynomial(&mut t,b"gkr-line-polynomial",line);
        let challenge=t.challenge_scalar(b"gkr-line-challenge");
        Ok((bytes,challenge,gkr::eval_polynomial(line,challenge),t.challenge_scalar(b"continuation")))
    }

    #[test]
    #[ignore="four authenticated N0 witness owners, original core and adjacency lines plus H21 packed line"]
    fn actual_n0_core_and_adjacency_lines()->Result<(),String>{
        let path=PathBuf::from(std::env::var_os("NIPOPOW_H21_LINE_WITNESS").ok_or("missing N0 witness")?);
        if !path.is_absolute(){return Err("absolute N0 witness required".into());}
        let _held=packed::open_untrusted_held_regular(&path,1u64<<38)?;
        let file=packed::PackedFile::open_with_limit(&path,41,41)?;
        // Prove that the native chunk loader and the native packed row reader
        // return the same ordered bits, including untouched banks and padding.
        for (owner,expected) in ROWS{
            let row=file.read_h21_table_row(owner)?;
            for bank in 0..16{
                let chunk=file.read_copy(1<<16,16*owner+bank)?;
                for (j,x) in chunk.iter().enumerate(){assert_eq!(*x,Fr::from(row.bit_at((bank<<16)+j) as u64));}
            }
            assert_eq!(hash(&row.into_bytes())?,expected);
        }
        let owners=ROWS.map(|(i,_)|i);
        let u:Vec<_>=(0..41).map(|i|Fr::from(3+13*i as u64)).collect();
        for case in ["general","one_equal","equal"]{
            let v:Vec<_>=(0..41).map(|i|if case=="equal" || (case=="one_equal" && i==7){
                u[i]
            }else{Fr::from(5+19*i as u64)}).collect();
            let began=Instant::now();
            let mut core_line=vec![Fr::zero();42];
            for owner in owners{
                core_pool_boolean::add_original_h21_line_control(&file.read_h21_table_row(owner)?,owner,&u,&v,&mut core_line)?;
            }
            let core_ns=began.elapsed().as_nanos();
            let began=Instant::now();
            let mut adjacency_line=vec![Fr::zero();42];
            for owner in owners{for bank in 0..16{
                let index=16*owner+bank;
                let x=file.read_copy(1<<16,index)?;
                let (_,_,contribution)=linear_for_test::original_chunk_line(&x,index,16,&u,&v);
                for (sum,c) in adjacency_line.iter_mut().zip(contribution){*sum+=c;}
            }}
            let adjacency_ns=began.elapsed().as_nanos();
            let began=Instant::now();
            let (packed,count)=sum_rows(&Role::Core,&u,&v,owners,|owner|file.read_h21_table_row(owner).map(PackedOwnerBits::into_bytes))?;
            let packed_ns=began.elapsed().as_nanos();
            assert_eq!(count,owners.len());
            assert_eq!(core_line,adjacency_line);
            assert_eq!(packed,core_line);
            let ends=[endpoints(&file,&u)?,endpoints(&file,&v)?];
            assert_eq!([packed[0],gkr::eval_polynomial(&packed,Fr::one())],ends);
            let result=suffix(&packed,ends)?;
            assert_eq!(result,suffix(&core_line,ends)?);
            assert_eq!(result,suffix(&adjacency_line,ends)?);
            if case=="equal"{assert!(packed[1..].iter().all(Zero::is_zero));}
            if case=="one_equal"{assert!(packed[41].is_zero());}
            assert_eq!(result.0.len(),1408);
            println!("H21_TABLE_LINE_VECTOR {}",serde_json::json!({"case":case,"owners":owners,
                "chunks_per_owner":16,"global_coefficients":42,"encoded_suffix_bytes":result.0.len(),
                "encoded_suffix_sha256":hash(&result.0)?,"core_reference_ns":core_ns,"adjacency_reference_ns":adjacency_ns,
                "packed_ns":packed_ns,"plan_reserved_bytes":packed_line_plan_bound(WIDTH,LOW)?,
                "packed_scratch_bound":scratch_bytes()?}));
        }
        println!("H21_TABLE_LINE_DIFFERENTIAL roles=0,5 owners=4 chunks_per_owner=16 cases=3");
        Ok(())
    }

    include!("h21_n0_completion_tests.rs");
}

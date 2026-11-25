//! Prover-side reservation for the log41 line shared by four historical roles.
use super::*;

const LOCAL_BITS: usize = 20;
const OWNER_BITS: usize = 21;
const OWNERS: usize = 1 << OWNER_BITS;
const WIDTH: usize = 1 << LOCAL_BITS;

pub(super) struct Admission {
    role: usize,
    plan_bytes: usize,
    extra_bytes: usize,
    required_bytes: usize,
}

impl Admission {
    pub(super) fn new(role: usize, original_required: usize, limit: usize) -> Result<Self,String> {
        if !matches!(role, 1 | 2 | 4 | 6) || usize::BITS != 64 || std::mem::size_of::<Fr>() != 32 {
            return Err("unsupported H21 packed-line role or ABI".into());
        }
        let plan_bytes = if Self::sixbit_role(role) { h21_sixbit_line::Plan::bound()? }
                         else { packed_line_plan_bound(WIDTH, LOCAL_BITS)? };
        // Explicitly allow both old/new owner selectors, the global accumulator,
        // the convolution output, the current linear factor and Vec headers.
        let high_fields = 2 * (OWNER_BITS + 1) + 2 * (LOCAL_BITS + OWNER_BITS + 1) + 2;
        let high_bytes = packed_line_add(packed_line_fields(high_fields)?, 5 * std::mem::size_of::<Vec<Fr>>())?;
        let extra_bytes = packed_line_add(packed_line_extra()?, high_bytes)?;
        let required_bytes = packed_line_add(original_required, packed_line_add(plan_bytes, extra_bytes)?)?;
        if required_bytes > limit {
            return Err("H21 packed line exceeds the declared role budget".into());
        }
        Ok(Self { role, plan_bytes, extra_bytes, required_bytes })
    }

    fn sixbit_role(role:usize) -> bool { cfg!(feature="h21-snapshot-n0") && matches!(role,2|4) }
    pub(super) fn sixbit(&self) -> bool { Self::sixbit_role(self.role) }
    pub(super) fn required_bytes(&self) -> usize { self.required_bytes }

    pub(super) fn configure(&self, input: &impl EdgeInput, local: usize, owners: usize,
        weighted_role1: bool, stats: &mut PackedLineStats) -> Result<(),String> {
        if (local,owners)!=(LOCAL_BITS,OWNER_BITS) || (input.width(),input.owners())!=(WIDTH,OWNERS)
            || weighted_role1!=(self.role==1) || !input.uses_packed_original_replay()
            || !input.supports_packed_line() {
            return Err("H21 packed line differs from its admitted physical input".into());
        }
        stats.plan_reserved_bytes=self.plan_bytes;
        stats.extra_reserved_bytes=self.extra_bytes;
        stats.component_bound=self.required_bytes;
        Ok(())
    }

    pub(super) fn report(&self, fast: &PackedLineStats, stats: &EdgeFullStats) -> Result<(),String> {
        let (lut,work)=if self.sixbit() {(h21_sixbit_line::LUT_FIELDS,h21_sixbit_line::WORK_FIELDS)} else {(1024,WIDTH/2)};
        if fast.owners!=OWNERS as u64 || fast.builds!=1 || fast.coefficients!=(OWNERS*(LOCAL_BITS+1)) as u64
            || fast.result_fields!=LOCAL_BITS+1 || fast.work_fields!=work || fast.lut_fields!=lut
            || fast.input_expanded_fields!=0 || stats.line_internal_clones!=0 || stats.line_cloned_fields!=0
            || fast.plan_actual_bytes!=self.plan_bytes {
            return Err("incomplete H21 packed line".into());
        }
        println!("H21_PACKED_LINE {}",serde_json::json!({
            "role":self.role,"owners":fast.owners,"local_coefficients":fast.coefficients,
            "global_coefficients":LOCAL_BITS+OWNER_BITS+1,"builds":fast.builds,
            "plan_bytes":fast.plan_actual_bytes,"extra_reserved_bytes":self.extra_bytes,
            "build_ns":fast.build_ns,"apply_ns":fast.apply_ns,"kernel_ns":stats.line_ns,
            "whole_ns":fast.whole_ns,"expanded_line_fields":fast.input_expanded_fields
        }));
        if self.sixbit() { h21_sixbit_line::report(self.role,fast.owners as usize); }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{io::{Read, Seek, SeekFrom}, path::PathBuf};

    // Native N0 measurement e59c2dd0…44df2; the source chunk readback
    // independently authenticated these four 128-KiB owner packets.
    const ROWS: [(usize,&str);4] = [
        (0,"e4132d69ccb280d235bb818055febd9ca000b5c94dbf49a6225d2f9ba528fe58"),
        (600023,"07bd32a9a66037bb94837f0cf32be4ad3c4358e6ef725816f819ca2156283c65"),
        (1804170,"975e9f79703a3e4c0d1033f7f5703ac63327f2882232227425fc4864719779a8"),
        (1819648,"8398a2898c274d80b79e104091846583b5869644fa644adee60a35c0a7d76530"),
    ];

    fn read_packets() -> Result<Vec<Vec<u8>>,String> {
        let path=PathBuf::from(std::env::var_os("NIPOPOW_H21_LINE_WITNESS").ok_or("missing sealed N0 witness")?);
        if !path.is_absolute(){return Err("H21 line requires the absolute original witness path".into());}
        let mut file=crate::packed::open_untrusted_held_regular(&path,1u64<<38)?;
        let mut rows=Vec::new();
        for (owner,expected) in ROWS {
            let mut data=vec![0;WIDTH/8];
            file.seek(SeekFrom::Start((owner*(WIDTH/8)) as u64)).map_err(|e|e.to_string())?;
            file.read_exact(&mut data).map_err(|e|e.to_string())?;
            let digest=crate::native_prefix_auth_plan::role0_sha256(&data)?;
            let hex:String=digest.iter().map(|b|format!("{b:02x}")).collect();
            if hex!=expected{return Err(format!("different N0 owner {owner}"));}
            rows.push(data);
        }
        Ok(rows)
    }

    // Independent high-coordinate basis, evaluated directly at a field point.
    fn owner_basis(owner:usize, point:&[Fr])->Fr {
        point.iter().enumerate().map(|(i,x)|
            if owner>>i&1==1{*x}else{Fr::one()-x}).product()
    }

    fn line_bytes_and_continuation(line:&[Fr],ends:[Fr;2])->Result<(Vec<u8>,Fr,Fr,Fr),String>{
        // Isolate the codec's endpoint + line suffix, omitting earlier rounds.
        let bytes=gkr::encode_proof(&GkrProof{layers:vec![LayerProof{rounds:Vec::new(),
            left_value:ends[0],right_value:ends[1],line_coefficients:line.to_vec()}]})?;
        let mut t=Transcript::new(b"local-dense-vs-packed-H21-line");
        t.append_scalar(b"gkr-left-value",&ends[0]);t.append_scalar(b"gkr-right-value",&ends[1]);
        gkr::append_polynomial(&mut t,b"gkr-line-polynomial",line);
        let challenge=t.challenge_scalar(b"gkr-line-challenge");
        Ok((bytes,challenge,gkr::eval_polynomial(line,challenge),t.challenge_scalar(b"local-continuation")))
    }

    #[test]
    #[ignore="four pinned N0 witness owners in the full log41 coordinates; bounded native Job"]
    fn h21_packed_line_matches_dense_selected_owners()->Result<(),String>{
        let rows=read_packets()?;
        let mut input=h21_role1_input(|owner|{
            let j=ROWS.iter().position(|(n,_)|*n==owner).ok_or("unrequested line owner")?;
            Ok(rows[j].clone())
        })?;
        let baseline=1usize<<30;
        for role in 0..7 {
            let allowed=matches!(role,1|2|4|6);
            let reservation=Admission::new(role,baseline,2*baseline);
            assert_eq!(reservation.is_ok(),allowed);
            if let Ok(a)=reservation {
                a.configure(&input,LOCAL_BITS,OWNER_BITS,role==1,&mut PackedLineStats::default())?;
                assert!(Admission::new(role,baseline,a.required_bytes()-1).is_err());
                assert!(Admission::new(role,usize::MAX,usize::MAX).is_err());
                assert!(a.configure(&input,LOCAL_BITS,12,role==1,&mut PackedLineStats::default()).is_err());
                assert!(a.configure(&input,LOCAL_BITS,OWNER_BITS,role!=1,&mut PackedLineStats::default()).is_err());
            }
        }
        assert!(packed_line_preflight(&input,WIDTH,OWNERS,512<<20).is_err());

        let u:Vec<_>=(0..41).map(|i|Fr::from(3+13*i as u64)).collect();
        for case in ["general","one_equal","equal"] {
            let v:Vec<_>=(0..41).map(|i|if case=="equal" || (case=="one_equal" && i==7){
                u[i]
            }else{Fr::from(5+19*i as u64)}).collect();
            let admission=Admission::new(6,baseline,2*baseline)?;
            let mut fast=PackedLineStats::default();let mut stats=EdgeFullStats::default();
            admission.configure(&input,LOCAL_BITS,OWNER_BITS,false,&mut fast)?;
            let mut plan=PackedLinePlan::new(WIDTH,&u[..LOCAL_BITS],&v[..LOCAL_BITS],fast.plan_reserved_bytes)?;
            let mut packed=vec![Fr::zero();42];let mut dense=vec![Fr::zero();42];
            let mut independent=[Fr::zero();42];
            let samples=[Fr::zero(),Fr::one(),Fr::from(9u64)];
            let mut values=[Fr::zero();3];
            for (j,(owner,_)) in ROWS.iter().copied().enumerate(){
                accumulate_packed_line_owner(&mut input,&mut plan,owner,&u[LOCAL_BITS..],&v[LOCAL_BITS..],
                    &mut packed,&mut fast,&mut stats)?;
                let x:Vec<Fr>=(0..WIDTH).map(|i|Fr::from(((rows[j][i/8]>>(i%8))&1)as u64)).collect();
                let local=gkr::line_polynomial(&x,&u[..LOCAL_BITS],&v[..LOCAL_BITS]);
                let high=copy_line_selector(owner,&u[LOCAL_BITS..],&v[LOCAL_BITS..]);
                for (i,a) in local.iter().enumerate(){for (k,b) in high.iter().enumerate(){dense[i+k]+=*a*b;}}
                // Degree at most 41: these 42 distinct values determine all the
                // global coefficients without invoking the high selector polynomial.
                for (i,expected) in independent.iter_mut().enumerate(){
                    let t=Fr::from(i as u64);
                    let point=gkr::line_point(&u[LOCAL_BITS..],&v[LOCAL_BITS..],t);
                    *expected+=owner_basis(owner,&point)*gkr::eval_polynomial(&local,t);
                }
                for (actual,t) in values.iter_mut().zip(samples){
                    let point=gkr::line_point(&u,&v,t);
                    *actual+=owner_basis(owner,&point[LOCAL_BITS..])*gkr::mle(&x,&point[..LOCAL_BITS]).map_err(|e|e.to_string())?;
                }
            }
            assert_eq!(packed,dense);
            for (i,expected) in independent.iter().enumerate(){
                assert_eq!(gkr::eval_polynomial(&packed,Fr::from(i as u64)),*expected);
            }
            for (expected,t) in values.iter().zip(samples){assert_eq!(gkr::eval_polynomial(&packed,t),*expected);}
            let result=line_bytes_and_continuation(&packed,[values[0],values[1]])?;
            assert_eq!(result,line_bytes_and_continuation(&dense,[values[0],values[1]])?);
            assert_eq!(result.0.len(),44*32);
            let digest=crate::native_prefix_auth_plan::role0_sha256(&result.0)?;
            let hex:String=digest.iter().map(|b|format!("{b:02x}")).collect();
            println!("H21_PACKED_LINE_VECTOR {}",serde_json::json!({"case":case,
                "encoded_suffix_bytes":result.0.len(),"encoded_suffix_sha256":hex,
                "owners":ROWS.map(|(owner,_)|owner),"independent_evaluations":independent.len()}));
            assert_eq!((fast.owners,fast.coefficients,fast.input_expanded_fields),(4,84,0));
            assert_eq!((stats.owner_requests,stats.emitted_fields,stats.line_internal_clones),(4,0,0));
            if case=="equal"{assert!(packed[1..].iter().all(Zero::is_zero));}
            if case=="one_equal"{assert!(packed[41].is_zero());}
        }
        assert_eq!(input.inner.metrics().vector_expansions,0);
        println!("H21_PACKED_LINE_DIFFERENTIAL owners=4 local_bits=20 owner_bits=21 global_coefficients=42 cases=3");
        Ok(())
    }
}

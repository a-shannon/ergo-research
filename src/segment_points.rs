//! New-profile adapter adding point membership to an unchanged header relation.
//! The five-stage consumer must verify every stage under one commitment.
use ark_bn254::Fr;
use ark_ff::{One,Zero};
use std::ops::Range;
use crate::{gkr::Gate,header_hash,packed::PackedFile,point_membership,
    segment_relation,serializer,sparse::Term};

pub const POINT_OFFSET:usize=786432;
pub const POINT_WIDTH:usize=point_membership::POINT_WIDTH;
pub struct Joined {
    pub base:Box<segment_relation::Joined>,pub points:Box<point_membership::Compiled>,
    pub released_rows:Range<usize>,pub alias_rows:Range<usize>,
}
pub fn build(fields:Option<&serializer::Fields>)->Result<Joined,String> {
    let mut base=Box::new(segment_relation::build(fields)?);let points=Box::new(point_membership::build()?);
    let z=Fr::zero();let o=Fr::one();
    if base.boundary.terms.len()!=419961 || base.remaining_padding_rows.end!=405784 {
        return Err("point adapter old boundary shape changed".into());
    }
    let padding_wire=segment_relation::DIGEST_OFFSET+256;
    let start=base.remaining_padding_rows.start+POINT_OFFSET-padding_wire;
    let released_rows=start..start+POINT_WIDTH;
    if released_rows.end>base.remaining_padding_rows.end{return Err("point bank outside padding".into());}
    let first=base.boundary.terms.partition_point(|t|t.row<released_rows.start);
    for bit in 0..POINT_WIDTH {
        let expected=Term {row:start+bit,gate:Gate {left:POINT_OFFSET+bit,right:0,c0:z,c1:o,c2:z,c3:z}};
        if base.boundary.terms.get(first+bit)!=Some(&expected){return Err("point adapter expected exact zero anchor".into());}
    }
    for term in &mut base.boundary.terms[first..first+POINT_WIDTH] {
        term.gate=Gate {left:0,right:0,c0:z,c1:z,c2:z,c3:z};
    }
    let alias_rows=405784..405850;
    let alias_term_start=base.boundary.terms.len();
    for (role,source) in [&base.serializer.layout.fields.pk,&base.serializer.layout.fields.w].into_iter().enumerate() {
        for byte in 0..33 {for bit in 0..8 {
            let weight=Fr::from(1u64<<bit);
            base.boundary.terms.push(Term {row:alias_rows.start+role*33+byte,gate:Gate {
                left:POINT_OFFSET+points.layout.points[role].bytes[byte][bit],
                right:header_hash::SERIALIZER_OFFSET+source[byte][bit],c0:z,c1:weight,c2:-weight,c3:z}});
        }}
    }
    #[cfg(test)]
    crate::c425_span_census::append_source_span(
        "segment_points.build.point_alias_terms", alias_term_start, base.boundary.terms.len());
    assert_eq!(base.boundary.terms.len(),420489);
    if let (Some(fields),Some(input))=(fields,base.input.as_mut()) {
        let bits=point_membership::witness(fields.pk,fields.w)?;
        for (slot,bit) in input[POINT_OFFSET..POINT_OFFSET+POINT_WIDTH].iter_mut().zip(bits){*slot=Fr::from(bit as u64);}
    }
    Ok(Joined {base,points,released_rows,alias_rows})
}
pub fn embed(stage:usize,h:usize,point:&[Fr])->Result<Vec<Fr>,String> {
    if stage<3{return segment_relation::embed(stage,h,point);}
    if stage!=3 || h>2 || point.len()!=13+h{return Err("point stage embedding dimensions invalid".into());}
    let mut out=point[..13].to_vec();out.extend([0u64,0,0,0,0,1,1].map(Fr::from));
    out.extend_from_slice(&point[13..]);Ok(out)
}
pub fn load_copy(source:&PackedFile,stage:usize,n:usize,copy:usize)->Result<Vec<Fr>,String> {
    if stage<3{return segment_relation::load_copy(source,stage,n,copy);}
    segment_relation::validate_n(n)?;
    if stage!=3 || copy>=n || source.input_len()!=n*segment_relation::HEADER_WIDTH {
        return Err("point stage packed source/copy dimensions invalid".into());
    }
    source.read_copy(POINT_WIDTH,copy*128+96)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{sparse::Circuit,sparse_stream_boolean,transcript::Transcript};
    fn generator(prefix:u8)->[u8;33]{let hex="79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798";
        let mut p=[0;33];p[0]=prefix;for i in 0..32{p[i+1]=u8::from_str_radix(&hex[2*i..2*i+2],16).unwrap();}p}
    fn fields()->serializer::Fields{serializer::Fields {version:1,parent_id:[0;32],ad_proofs_root:[0;32],transactions_root:[0;32],
        state_root:[0;33],timestamp:0,extension_root:[0;32],n_bits:1,height:1,votes:[0;3],pk:generator(2),w:generator(3),nonce:[0;8],payload_len:0,payload:[0;255]}}
    fn failed(c:&Circuit,w:&[Fr],skip:Option<Range<usize>>)->Vec<usize>{let mut out=vec![Fr::zero();c.row_count];
        for t in &c.terms{if !skip.as_ref().is_some_and(|r|r.contains(&t.row)){out[t.row]+=t.gate.evaluate(w);}}
        out.into_iter().enumerate().filter_map(|(i,v)|(!v.is_zero()).then_some(i)).collect()}
    fn old_components(base:&segment_relation::Joined,w:&[Fr]) {
        for half in w[..header_hash::SERIALIZER_OFFSET].chunks_exact(1<<18){assert!(failed(&base.core4,half,None).is_empty());}
        assert!(failed(&base.serializer.circuit,&w[header_hash::SERIALIZER_OFFSET..header_hash::AUX_OFFSET],None).is_empty());
        assert!(failed(&base.boundary,w,None).is_empty());
    }
    fn circuit_fingerprint(c:&Circuit)->String {
        use blake2::{Blake2b512,Digest};use ark_serialize::CanonicalSerialize;
        let mut hash=Blake2b512::new();
        for n in [c.input_len,c.row_count,c.terms.len()]{hash.update((n as u64).to_le_bytes());}
        for t in &c.terms {
            for n in [t.row,t.gate.left,t.gate.right]{hash.update((n as u64).to_le_bytes());}
            for scalar in [t.gate.c0,t.gate.c1,t.gate.c2,t.gate.c3] {
                let mut bytes=Vec::new();scalar.serialize_compressed(&mut bytes).unwrap();hash.update(bytes);
            }
        }hash.finalize().iter().map(|b|format!("{b:02x}")).collect()
    }
    #[test]
    fn heap_storage_preserves_frozen_circuits_and_witness() {
        use blake2::{Blake2b512,Digest};
        let j=build(Some(&fields())).unwrap();
        let point=circuit_fingerprint(&j.points.circuit);let boundary=circuit_fingerprint(&j.base.boundary);
        let bits=j.base.input.as_ref().unwrap();let mut packed=vec![0u8;bits.len()/8];
        for (i,bit) in bits.iter().enumerate(){assert!(*bit==Fr::zero()||*bit==Fr::one());if bit.is_one(){packed[i/8]|=1<<(i%8);}}
        let witness:String=Blake2b512::digest(&packed).iter().map(|b|format!("{b:02x}")).collect();
        assert_eq!(point,"b10a9a67e066709e64156494b7ee6a88932371692caf861d6b77bf3f22d3469698654a78c35e7282fb745422f37799111f02d237357b0fb4a7011932373bbdf2");
        assert_eq!(boundary,"ce6e0019a236bc685f09f74c751cef1a01add74023fe93d87fead4911bd7968a783ecf3b794ab97d596fb3a7f3f2c57ae1aa0f1db17f8a5746b0aa298c8ca677");
        assert_eq!(witness,"80654b9fb66bc344e46ad258a587705865100a730412085c3338e5a848c4935c028224958c853be821c2500948e2f4fef5159ae0aa8448f73a94729859d2bef3");
        println!("POINT={point}\nBOUNDARY={boundary}\nWITNESS={witness}\nLAYOUT_BYTES={} POINT_LAYOUT_BYTES={}",
            std::mem::size_of::<point_membership::Layout>(),std::mem::size_of::<point_membership::PointLayout>());
        let terms=&j.points.circuit.terms;
        let a_edges=terms.iter().filter(|t|!t.gate.c3.is_zero()).count();
        let b_edges=terms.iter().filter(|t|!t.gate.c2.is_zero()).count();
        // Same element size and push growth as the private streamer Edge.
        let mut a=Vec::<(usize,usize,Fr)>::new();let mut b=Vec::<(usize,usize,Fr)>::new();
        for _ in 0..a_edges{a.push((0,0,Fr::zero()));}for _ in 0..b_edges{b.push((0,0,Fr::zero()));}
        println!("COMPILED_BYTES={} TERM_BYTES={} TERMS_LEN={} TERMS_CAP={} EDGE_BYTES={} A_EDGES={}/{} B_EDGES={}/{}",
            std::mem::size_of::<point_membership::Compiled>(),std::mem::size_of::<Term>(),terms.len(),terms.capacity(),
            std::mem::size_of::<(usize,usize,Fr)>(),a_edges,a.capacity(),b_edges,b.capacity());
        println!("JOINED_BYTES={} BASE_JOINED_BYTES={}",std::mem::size_of::<Joined>(),std::mem::size_of::<segment_relation::Joined>());
    }
    #[test]
    fn bounded_stack_constructors_in_isolated_child() {
        const CHILD:&str="NIPOPOW_POINT_STACK_REGRESSION_CHILD";
        if std::env::var_os(CHILD).is_some(){
            std::thread::Builder::new().name("point-constructor-1mib".into()).stack_size(1024*1024).spawn(||{
                let public=build(None).unwrap();let private=build(Some(&fields())).unwrap();
                assert_eq!(public.points.circuit,private.points.circuit);
                assert_eq!(public.base.boundary,private.base.boundary);
            }).unwrap().join().unwrap();return;
        }
        // A stack overflow aborts only this child, never the surrounding suite.
        let mut child=std::process::Command::new(std::env::current_exe().unwrap())
            .args(["--exact","segment_points::tests::bounded_stack_constructors_in_isolated_child","--test-threads=1"])
            .env(CHILD,"1").stdout(std::process::Stdio::null()).stderr(std::process::Stdio::inherit()).spawn().unwrap();
        let start=std::time::Instant::now();loop {
            if let Some(status)=child.try_wait().unwrap(){assert!(status.success(),"constructor child failed: {status}");break;}
            if start.elapsed()>std::time::Duration::from_secs(30){child.kill().unwrap();child.wait().unwrap();panic!("constructor child timeout");}
            std::thread::sleep(std::time::Duration::from_millis(10));
        }
    }
    #[test]
    fn topology_aliases_and_exact_released_anchor_shape() {
        let public=build(None).unwrap();let actual=build(Some(&fields())).unwrap();
        assert_eq!(actual.base.boundary,public.base.boundary);assert_eq!(actual.points.circuit,public.points.circuit);
        assert!(public.base.input.is_none());assert_eq!(actual.released_rows,143640..151832);
        assert_eq!(actual.alias_rows,405784..405850);assert_eq!(actual.base.boundary.terms.len(),420489);
        let old=segment_relation::build(None).unwrap();let mut altered=0;
        for (a,b) in old.boundary.terms.iter().zip(&public.base.boundary.terms){
            if a!=b{altered+=1;assert!(public.released_rows.contains(&a.row));assert_eq!(b.gate.c0+b.gate.c1+b.gate.c2+b.gate.c3,Fr::zero());}
        }assert_eq!(altered,8192);
        let w=actual.base.input.as_ref().unwrap();old_components(&actual.base,w);
        assert!(failed(&actual.points.circuit,&w[POINT_OFFSET..POINT_OFFSET+POINT_WIDTH],None).is_empty());
        let mut v2=fields();v2.version=4;v2.w=[0;33];v2.pk=[0;33];
        let other=build(Some(&v2)).unwrap();assert_eq!(other.base.boundary,public.base.boundary);
        old_components(&other.base,other.base.input.as_ref().unwrap());
        let mut bad=v2;bad.w=generator(2);let bad=build(Some(&bad)).unwrap();
        assert!(!failed(&bad.base.serializer.circuit,&bad.base.input.as_ref().unwrap()[header_hash::SERIALIZER_OFFSET..header_hash::AUX_OFFSET],None).is_empty());
    }
    #[test]
    fn separately_valid_point_bank_must_match_same_committed_header_bytes() {
        let j=build(Some(&fields())).unwrap();let mut w=j.base.input.as_ref().unwrap().clone();
        let replacement=point_membership::witness(generator(3),generator(3)).unwrap();
        for (out,bit) in w[POINT_OFFSET..POINT_OFFSET+POINT_WIDTH].iter_mut().zip(replacement){*out=Fr::from(bit as u64);}
        assert!(failed(&j.points.circuit,&w[POINT_OFFSET..POINT_OFFSET+POINT_WIDTH],None).is_empty());
        assert!(failed(&j.base.serializer.circuit,&w[header_hash::SERIALIZER_OFFSET..header_hash::AUX_OFFSET],None).is_empty());
        for half in w[..header_hash::SERIALIZER_OFFSET].chunks_exact(1<<18){assert!(failed(&j.base.core4,half,None).is_empty());}
        assert_eq!(failed(&j.base.boundary,&w,None),vec![j.alias_rows.start]);
        assert!(failed(&j.base.boundary,&w,Some(j.alias_rows.clone())).is_empty());
        for wire in [POINT_OFFSET-1,POINT_OFFSET+POINT_WIDTH]{let mut bad=j.base.input.as_ref().unwrap().clone();bad[wire]=Fr::one();
            assert_eq!(failed(&j.base.boundary,&bad,None).len(),1);}
    }
    #[test]
    fn raw_nonresidue_passes_old_stages_but_point_residual_and_producer_reject() {
        let mut f=fields();f.pk=[0;33];f.pk[0]=2;f.w=[0;33];
        assert!(ergo_header_core::GroupElement::from_bytes(f.pk).is_err());
        let old=segment_relation::build(Some(&f)).unwrap();let mut w=old.input.as_ref().unwrap().clone();old_components(&old,&w);
        let j=build(None).unwrap();let bits=point_membership::witness([0;33],[0;33]).unwrap();
        for (out,bit) in w[POINT_OFFSET..POINT_OFFSET+POINT_WIDTH].iter_mut().zip(bits){*out=Fr::from(bit as u64);}
        w[POINT_OFFSET+j.points.layout.points[0].bytes[0][1]]=Fr::one();
        // The old serializer/hash/digest witness remains valid; shared byte aliases match.
        assert!(failed(&j.base.boundary,&w,None).is_empty());
        let bank=&w[POINT_OFFSET..POINT_OFFSET+POINT_WIDTH];
        assert_eq!(failed(&j.points.circuit,bank,None),vec![j.points.layout.points[0].rows.arithmetic[2].start]);
        let mut t=Transcript::new(b"point-nonresidue");let before=(t.bytes_absorbed(),t.challenges());
        assert!(sparse_stream_boolean::prove(&j.points.circuit,0,|_|Ok(bank.to_vec()),&mut t).is_err());
        assert_eq!((t.bytes_absorbed(),t.challenges()),before);
    }
    #[test]
    fn point_embedding_and_packed_loader_select_exact_bank_for_all_counts() {
        use std::io::Write;
        for n in [1,2,4]{let h=segment_relation::validate_n(n).unwrap();let point:Vec<_>=(0..13+h).map(|i|Fr::from((i+2)as u64)).collect();
            let actual=embed(3,h,&point).unwrap();let mut expected=point[..13].to_vec();
            expected.extend([0u64,0,0,0,0,1,1].map(Fr::from));expected.extend_from_slice(&point[13..]);assert_eq!(actual,expected);
            let bytes:Vec<_>=(0..n*segment_relation::HEADER_WIDTH/8).map(|i|(i as u8).wrapping_mul(73).wrapping_add((i/1024)as u8)).collect();
            let path=std::env::temp_dir().join(format!("point-bank-{}-{}-{}.bits",std::process::id(),n,
                std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH).unwrap().as_nanos()));
            let mut file=std::fs::OpenOptions::new().write(true).create_new(true).open(&path).unwrap();file.write_all(&bytes).unwrap();drop(file);
            let source=PackedFile::open(&path,20+h).unwrap();for copy in 0..n{let got=load_copy(&source,3,n,copy).unwrap();
                for (bit,value) in got.into_iter().enumerate(){let global=copy*segment_relation::HEADER_WIDTH+POINT_OFFSET+bit;
                    assert_eq!(value,Fr::from(((bytes[global/8]>>(global%8))&1)as u64));}}
            assert!(load_copy(&source,3,n,n).is_err());assert!(load_copy(&source,4,n,0).is_err());
            assert!(embed(3,h,&point[..point.len()-1]).is_err());
        }
        assert!(embed(3,3,&[]).is_err());assert!(embed(4,0,&[]).is_err());
    }
}

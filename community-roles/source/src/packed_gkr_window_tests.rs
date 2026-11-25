use crate::{gkr::{self, Gate, GkrError}, one_header_gkr_pcs::*, packed::{self, PackedFile, PackedFileWriter, PackedIoSnapshot},
    packed_gkr_window::{self as engine, Bits, EqCache, Work}, pcs, projection_aux_retirement::Authority,
    serializer, sparse::{self, Circuit, Term}, transcript::Transcript, verifier_key};
use ark_bn254::Fr;
use ark_ff::{One, Zero};
use serde::{Deserialize, Serialize};
use std::{cell::Cell, fs::{self, OpenOptions}, io::{self, Write}, mem::size_of,
    path::{Path, PathBuf}, time::Instant};

const ENV: &str = "NIPOPOW_PACKED_GKR_WINDOW_ARTIFACT_DIR";
const BYTES: usize = N / 8;
const BUFFER_LIMIT: usize = 1 << 20;
fn micros(t: Instant) -> u64 { let n = u64::try_from(t.elapsed().as_micros()).unwrap(); assert!(n <= 120_000_000); n }
fn nanos(n: u128) -> u64 { let n = u64::try_from(n).unwrap(); assert!(n <= 120_000_000_000); n }
fn eq(p: &[Fr], index: usize) -> Fr {
    p.iter().enumerate().fold(Fr::one(), |a,(j,t)| a * if (index >> j) & 1 == 1 { *t } else { Fr::one()-t })
}
fn selector(index: usize) -> [Fr;18] { std::array::from_fn(|j| Fr::from(((index >> j) & 1) as u64)) }
fn points() -> [[Fr;18];2] {
    [[Fr::from(2);18], std::array::from_fn(|j| Fr::from((2*j+3) as u64)/Fr::from((2*j+5) as u64))]
}
fn fields() -> serializer::Fields {
    serializer::Fields { version:4,parent_id:[0x11;32],ad_proofs_root:[0x22;32],transactions_root:[0x33;32],
        state_root:[0x44;33],timestamp:0,extension_root:[0x55;32],n_bits:0x043B9ACA,height:844672,
        votes:[0x66,0x77,0x88],pk:[0;33],w:[0;33],nonce:[1,2,3,4,5,6,7,8],payload_len:0,payload:[0;255] }
}
fn checked_directory(value: Option<&std::ffi::OsStr>) -> Result<PathBuf, &'static str> {
    let path = PathBuf::from(value.ok_or("missing environment")?);
    if !path.is_absolute() { return Err("relative path"); }
    let expected = path.canonicalize().map_err(|_| "missing controller directory")?;
    if !crate::preview_test_paths::absolute_outside_source(&expected) { return Err("artifact directory inside source or filesystem root"); }
    if !fs::metadata(&expected).map_err(|_| "metadata")?.is_dir() { return Err("not directory"); }
    if fs::read_dir(&expected).map_err(|_| "directory")?.count() != 0 { return Err("not fresh"); }
    Ok(expected)
}
#[derive(Debug, PartialEq, Eq)]
enum PackingError { Length, NonBoolean(usize) }
fn pack(x: &[Fr]) -> Result<Box<[u8]>, PackingError> {
    if x.len() != N { return Err(PackingError::Length); }
    let mut bytes = vec![0u8;BYTES].into_boxed_slice();
    for (i,v) in x.iter().enumerate() {
        if v.is_one() { bytes[i/8] |= 1 << (i%8); }
        else if !v.is_zero() { return Err(PackingError::NonBoolean(i)); }
    }
    Ok(bytes)
}
fn snapshot(source: &PackedFile, expected: &[u8]) -> Bits {
    assert_eq!(source.input_len(),N); assert_eq!(expected.len(),BYTES);
    let mut checked = vec![0u8;BYTES].into_boxed_slice();
    for k in 0..4 {
        let chunk = source.read_copy(65536,k).unwrap();
        assert_eq!((chunk.len(),chunk.capacity()),(65536,65536));
        assert_eq!(chunk.capacity()*size_of::<Fr>(),2*1024*1024);
        let mut bytes = [0u8;8192];
        for (i,v) in chunk.iter().enumerate() {
            assert!(v.is_zero() || v.is_one());
            if v.is_one() { bytes[i/8] |= 1 << (i%8); }
        }
        assert_eq!(&bytes[..],&expected[k*8192..(k+1)*8192],"locked complete source byte comparison");
        checked[k*8192..(k+1)*8192].copy_from_slice(&bytes);
        drop(chunk);
    }
    Bits::new(checked,N).unwrap()
}
fn reads(s: PackedIoSnapshot, calls: u64, bytes: u64) {
    assert_eq!((s.read_calls,s.read_bytes),(calls,bytes));
    assert_eq!((s.write_calls,s.write_bytes,s.sync_calls),(0,0,0)); let _ = nanos(s.read_ns);
}
fn probe(t: &Transcript) -> Fr { t.clone().challenge_scalar(b"packed-window-continuation-probe") }
fn counters(t: &Transcript) -> [u64;3] { [t.challenges(),t.raw_queries(),t.bytes_absorbed()] }
fn gate(l: usize,r: usize,c: [Fr;4]) -> Gate { Gate { left:l,right:r,c0:c[0],c1:c[1],c2:c[2],c3:c[3] } }

fn cache_controls() {
    let mut work = Work::default();
    let empty = EqCache::new(&[],&mut work); assert_eq!(empty.at(99),Fr::one());
    for d in [1usize,8,9,10,17,18,19] {
        let p:Vec<_> = (0..d).map(|j| Fr::from((2*j+3) as u64)/Fr::from((2*j+5) as u64)).collect();
        let c = EqCache::new(&p,&mut work);
        assert!(c.bytes() < 131072);
        for i in [0,1,(1usize<<d)-1,((1usize<<d)-1)/3] { assert_eq!(c.at(i),eq(&p,i)); }
        if d<=10 { let full=gkr::eq_weights(&p); for (i,v) in full.iter().enumerate() { assert_eq!(c.at(i),*v); } }
        let b:Vec<_> = (0..d).map(|j| Fr::from((j%2) as u64)).collect();
        let at=b.iter().enumerate().fold(0,|i,(j,v)|i+usize::from(v.is_one())*(1<<j));
        let c=EqCache::new(&b,&mut work); assert_eq!(c.at(at),Fr::one()); assert_eq!(c.at(at^1),Fr::zero());
    }
    let p:Vec<_>=(0..10).map(|j|Fr::from((j+2) as u64)).collect();
    let c=EqCache::new(&p,&mut work);
    assert_ne!(c.at(1),c.at(2),"axis swap has a real nonzero delta");
    let wrong:Vec<_>=p[9..].iter().chain(&p[..9]).copied().collect();
    assert_ne!(c.at(1),eq(&wrong,1),"chunk order mutation");
    let bits=Bits::new(vec![2u8].into_boxed_slice(),8).unwrap();
    let p=[Fr::from(2),Fr::from(3),Fr::from(5)];
    assert_eq!(engine::folded(&bits,0,&p,&mut Work::default()),Fr::from(16));
    assert_eq!(eq(&p,1),Fr::from(16));
    // Wrong recursive half splitting consumes coordinate0 at the highest split.
    let wrong=eq(&[p[2],p[1],p[0]],1); assert_eq!(wrong,Fr::from(10)); assert_eq!(eq(&p,1)-wrong,Fr::from(6));
}
fn tiny() -> (Circuit,Bits,Vec<Fr>) {
    let bytes=0b10110110u8;
    let x:Vec<_>=(0..8).map(|i|Fr::from(((bytes>>i)&1) as u64)).collect();
    let mut terms=Vec::with_capacity(9);
    // Literal input values: (1,1),(0,0),(1,0),(1,1), with residuals17,2,5,17.
    for (row,l,r,residual) in [(0,1,2,17),(1,0,3,2),(2,4,6,5),(3,5,7,17)] {
        terms.push(Term { row,gate:gate(l,r,[Fr::from(2),Fr::from(3),Fr::from(5),Fr::from(7)]) });
        terms.push(Term { row,gate:gate(0,7,[-Fr::from(residual),Fr::zero(),Fr::zero(),Fr::zero()]) });
        if row==0 { terms.push(Term { row,gate:gate(2,3,[Fr::zero(),Fr::zero(),Fr::zero(),Fr::from(5)]) }); }
    }
    (Circuit { input_len:8,row_count:8,terms },Bits::new(vec![bytes].into_boxed_slice(),8).unwrap(),x)
}
fn literal_coefficients(c:&Circuit,x:&[Fr],r:&[Fr],left:Option<(&[Fr],Fr)>) -> (Vec<Fr>,Vec<Fr>) {
    let mut a=vec![Fr::zero();x.len()]; let mut b=a.clone();
    for t in &c.terms { let g=&t.gate; let w=eq(r,t.row);
        if let Some((u,value))=left {
            let w=w*eq(u,g.left); a[g.right]+=w*(g.c2+g.c3*value); b[g.right]+=w*(g.c0+g.c1*value);
        } else { a[g.left]+=w*(g.c1+g.c3*x[g.right]); b[g.left]+=w*(g.c0+g.c2*x[g.right]); }
    }
    (a,b)
}
fn algebra_controls() {
    let (c,bits,x)=tiny(); let r=[Fr::from(2),Fr::from(3),Fr::from(5)];
    let u=[Fr::from(7),Fr::from(11),Fr::from(13)]; let prefixes=[-Fr::one(),Fr::from(2)];
    let value=gkr::mle(&x,&u).unwrap();
    let mut work=Work::default(); let row=EqCache::new(&r,&mut work); let uc=EqCache::new(&u,&mut work);
    for second in [false,true] {
        let (mut dense_a,mut dense_b)=literal_coefficients(&c,&x,&r,second.then_some((&u[..],value)));
        let mut dense_x=x.clone();
        for j in 0..3 {
            let prefix=EqCache::new(&prefixes[..j],&mut work);
            for width in [2usize,4] {
                let mut message=[Fr::zero();3]; let mut seen=0;
                for start in (0..dense_x.len()).step_by(width) {
                    let count=width.min(dense_x.len()-start);
                    let mut a=vec![Fr::zero();count];let mut b=a.clone();let mut xx=a.clone();
                    engine::fill(&c,&bits,&row,second.then_some((&uc,value)),&prefix,j,start,&mut a,&mut b,&mut work);
                    assert_eq!(&a[..],&dense_a[start..start+count]); assert_eq!(&b[..],&dense_b[start..start+count]);
                    for k in 0..count { xx[k]=engine::folded(&bits,(start+k)<<j,&prefixes[..j],&mut work); }
                    assert_eq!(&xx[..],&dense_x[start..start+count]);
                    let m=engine::quadratic(&a,&b,&xx); for k in 0..3 { message[k]+=m[k]; } seen+=count;
                }
                assert_eq!(seen,dense_x.len());
                assert_eq!(&message[..],&gkr::quadratic_message(&dense_a,&dense_b,&dense_x)[..]);
                // Aligned windows keep pairs complete; source contributions on either side are retained.
                if j==0 && width==4 { assert!(!dense_a[..4].iter().all(Zero::is_zero)); assert!(!dense_a[4..].iter().all(Zero::is_zero)); }
            }
            if j<2 { gkr::fold(&mut dense_a,prefixes[j]);gkr::fold(&mut dense_b,prefixes[j]);gkr::fold(&mut dense_x,prefixes[j]); }
        }
    }
    let expected=gkr::line_polynomial(&x,&u,&r);
    assert_eq!(engine::line(&bits,&u,&r,&mut Work::default()),expected);
    let shape=sparse::validate(&c,0).unwrap();let v=EqCache::new(&r,&mut work);
    assert_eq!(engine::terminal(&c,&row,&uc,&v,&mut work),sparse::wiring(&c,&shape,&r,&u,&r).unwrap());
    // Isolated RAW-right edge: x3=0, whereas its folded pair at prefix2 is-1.
    let edge=Circuit { input_len:8,row_count:1,terms:vec![Term { row:0,gate:gate(2,3,[Fr::zero(),Fr::zero(),Fr::zero(),Fr::from(5)]) }] };
    let row0=EqCache::new(&[],&mut work);let p0=EqCache::new(&[Fr::from(2)],&mut work);
    let mut a=[Fr::zero();4];let mut b=a;
    engine::fill(&edge,&bits,&row0,None,&p0,1,0,&mut a,&mut b,&mut work);
    assert!(a.iter().all(Zero::is_zero)); assert_eq!(bits.bit(3),Fr::zero());
    let wrong_right=engine::folded(&bits,2,&[Fr::from(2)],&mut work); assert_eq!(wrong_right,-Fr::one());
    assert_ne!(a[1],p0.at(2)*Fr::from(5)*wrong_right);
    // Genuine adjacent coefficient cancellation, with no zero row mask.
    for channel in [1,2] {
        let terms=(0..2).map(|i| { let mut cc=[Fr::zero();4];cc[channel]=Fr::from((i+1) as u64);
            Term { row:0,gate:gate(if channel==1 {i} else {0},if channel==2 {i} else {0},cc) } }).collect();
        let cc=Circuit { input_len:8,row_count:1,terms };let zero=Bits::new(vec![0].into_boxed_slice(),8).unwrap();
        let empty=EqCache::new(&[],&mut work);let minus=EqCache::new(&[-Fr::one()],&mut work);
        let bu=EqCache::new(&[Fr::zero();3],&mut work);
        let mut aa=[Fr::zero();8];let mut bb=aa;
        engine::fill(&cc,&zero,&empty,(channel==2).then_some((&bu,Fr::zero())),&empty,0,0,&mut aa,&mut bb,&mut work);
        assert_eq!((aa[0],aa[1]),(Fr::one(),Fr::from(2)));
        assert!(!Fr::from(2).is_zero());assert!(!(-Fr::from(2)).is_zero());
        engine::fill(&cc,&zero,&empty,(channel==2).then_some((&bu,Fr::zero())),&minus,1,0,&mut aa[..4],&mut bb[..4],&mut work);
        assert_eq!(aa[0],Fr::zero());
    }
    let mut golden=Transcript::new(b"packed-window-literal-tiny"); let (gp,gc)=sparse::prove(&c,&x,0,&mut golden).unwrap();
    let mut actual=Transcript::new(b"packed-window-literal-tiny"); let (pp,pc,_)=engine::prove(&c,&bits,0,&mut actual).unwrap();
    assert_eq!(gkr::encode_proof(&gp).unwrap(),gkr::encode_proof(&pp).unwrap());assert_eq!(gc,pc);assert_eq!(probe(&golden),probe(&actual));
}

fn admission_controls() {
    let (mut c,bits,_)=tiny();
    let calls=Cell::new(0);
    let reject=|c:&Circuit,b:&Bits,h:usize,expected:engine::Error| {
        let mut t=Transcript::new(b"pre-binding-reject");let before=counters(&t);
        let result=engine::prove_with_binding(c,b,h,&mut t,|_|calls.set(calls.get()+1));
        assert_eq!(result.err(),Some(expected));assert_eq!(calls.get(),0);assert_eq!(counters(&t),before);
    };
    reject(&c,&bits,1,engine::Error::Scope);
    let mut big=c.clone();big.input_len=1<<19;reject(&big,&bits,0,engine::Error::Scope);
    big=c.clone();big.row_count=1<<20;reject(&big,&bits,0,engine::Error::Scope);
    big=Circuit { input_len:1,row_count:1,terms:vec![] };reject(&big,&bits,0,engine::Error::ScalarWidth);
    c.terms[0].gate.left=8;reject(&c,&bits,0,engine::Error::Circuit(GkrError::InvalidWireIndex));
    let (mut c,_,_)=tiny();c.terms.swap(0,3);reject(&c,&bits,0,engine::Error::Order(1));
    let (c,_,_)=tiny();let short=Bits::new(vec![0].into_boxed_slice(),4).unwrap();reject(&c,&short,0,engine::Error::Framing);
    assert_eq!(Bits::new(vec![0,0].into_boxed_slice(),8).err().map(|e|e),Some(engine::Error::Framing));
    assert_eq!(Bits::new(vec![0x80].into_boxed_slice(),4).err().map(|e|e),Some(engine::Error::Framing));
}
fn source_controls(c:&Circuit,bits:&Bits,scalars:[Fr;2]) {
    assert_eq!((c.terms[0].row,c.terms[1].row),(0,1));
    let eval=|g:&Gate,b:&Bits|g.c0+g.c1*b.bit(g.left)+g.c2*b.bit(g.right)+g.c3*b.bit(g.left)*b.bit(g.right);
    assert_eq!((c.terms[0].gate.left,c.terms[1].gate.left),(0,1));
    assert_eq!((eval(&c.terms[0].gate,bits),eval(&c.terms[1].gate,bits)),(Fr::zero(),Fr::zero()));
    for faults in [1u8,2,3] {
        let mut bytes=bits.bytes().to_vec().into_boxed_slice();
        if faults&1!=0 { bytes[0]|=1; }
        if faults&2!=0 { bytes[0]&=!2; }
        let bad=Bits::new(bytes,N).unwrap();
        assert_eq!(eval(&c.terms[0].gate,&bad),if faults&1!=0 {Fr::one()} else {Fr::zero()});
        assert_eq!(eval(&c.terms[1].gate,&bad),if faults&2!=0 {-Fr::one()} else {Fr::zero()});
        if faults==3 {
            let mut r=[Fr::zero();19];r[0]=Fr::one()/Fr::from(2);
            assert_eq!(eq(&r,0)*Fr::one()+eq(&r,1)*(-Fr::one()),Fr::zero());
        }
        let calls=Cell::new(0);let mut t=Transcript::new(b"actual-row-cancellation");let before=counters(&t);
        let row=if faults&1!=0 {0} else {1};
        assert_eq!(engine::prove_with_binding(c,&bad,0,&mut t,|_|calls.set(1)).err(),Some(engine::Error::Residual(row)));
        assert_eq!(calls.get(),0);assert_eq!(counters(&t),before);drop(bad);
    }
    assert_eq!(bits.bit(1),Fr::one());assert_ne!(bits.bit(1),bits.bit(0));
    let endian=(0..N).find(|i|bits.bit(*i)!=bits.bit(*i^7)).unwrap(); assert_ne!(bits.bit(endian),bits.bit(endian^7));
    let transpose=|i:usize|(i%512)*512+i/512;
    let i=(0..N).find(|i|bits.bit(*i)!=bits.bit(transpose(*i))).unwrap();assert_ne!(bits.bit(i),bits.bit(transpose(i)));
    for len in [BYTES-1,BYTES+1] { assert_eq!(Bits::new(vec![0;len].into_boxed_slice(),N).err(),Some(engine::Error::Framing)); }
    assert_eq!(bits.bit(INPUT_USED),Fr::zero());
    let mut bytes=bits.bytes().to_vec().into_boxed_slice();bytes[INPUT_USED/8]|=1<<(INPUT_USED%8);
    let tail=Bits::new(bytes,N).unwrap();engine::check(c,&tail,&mut Work::default()).unwrap();
    for (j,p) in points().into_iter().enumerate() {
        let main=engine::folded(bits,0,&p,&mut Work::default()); assert_eq!(main,scalars[j]);
        let altered=engine::folded(&tail,0,&p,&mut Work::default());assert_eq!(altered-main,eq(&p,INPUT_USED));assert!(!eq(&p,INPUT_USED).is_zero());
        let mainline=engine::line(bits,&p,&p,&mut Work::default());let tailline=engine::line(&tail,&p,&p,&mut Work::default());
        assert_eq!(mainline[0],scalars[j]);assert_eq!(tailline[0]-mainline[0],eq(&p,INPUT_USED));
        assert!(mainline[1..].iter().all(Zero::is_zero));assert!(tailline[1..].iter().all(Zero::is_zero));
    }
    drop(tail);
    // Last-ordinal omission uses a genuine one, rather than the main's zero tail.
    let mut bytes=bits.bytes().to_vec().into_boxed_slice();bytes[BYTES-1]|=0x80;
    let last=Bits::new(bytes,N).unwrap();assert_eq!(last.bit(N-1),Fr::one());
    assert_eq!(engine::folded(&last,0,&selector(N-1),&mut Work::default()),Fr::one());assert_ne!(last.bit(N-1),bits.bit(N-1));
}

#[derive(Debug,Serialize,Deserialize)]
#[serde(deny_unknown_fields)]
struct Diagnostic {
    schema:u64, log_n:u64, row_log:u64, source_terms:u64, packed_bytes:u64,
    fill_term_visits:u64, weighted_terms:u64, residual_terms:u64, terminal_terms:u64, bind_terms:u64,
    fold_leaves:u64, fold_muls:u64, line_bits:u64, line_ones:u64, line_updates:u64,
    cache_build_muls:u64, cache_modeled_peak_bytes:u64, window_bytes:u64, line_stack_bytes:u64,
    multiplication_bound:u64, gkr_bytes:u64, gkr_scalars:u64, gkr_challenges:u64, dory_bytes:u64,
    snapshot_reads:u64, snapshot_read_bytes:u64, commit_reads:u64, commit_read_bytes:u64,
    open_reads:u64, open_read_bytes:u64, write_calls:u64, write_bytes:u64, sync_calls:u64,
    source_us:u64, packing_us:u64, finish_us:u64, setup_us:u64, commit_us:u64,
    golden_us:u64, snapshot_us:u64, candidate_us:u64, controls_us:u64, codec_verify_us:u64,
    pcs_open_us:u64, key_admit_us:u64, pcs_verify_us:u64,
    snapshot_read_ns:u64, commit_read_ns:u64, open_read_ns:u64, write_ns:u64, sync_ns:u64,
    proof_equal:bool, claim_equal:bool, continuation_equal:bool, controls_pass:bool,
}

#[test]
fn packed_windows_match_real_sparse_proof() {
    // All artifact path checks precede any write. No temp directory fallback.
    assert_eq!(checked_directory(None).err(),Some("missing environment"));
    assert_eq!(checked_directory(Some(std::ffi::OsStr::new("relative"))).err(),Some("relative path"));
    let current = std::env::current_dir().unwrap();
    let root = current.ancestors().last().expect("filesystem root");
    assert!(checked_directory(Some(root.as_os_str())).is_err());
    let value=std::env::var_os(ENV);let dir=checked_directory(value.as_deref()).unwrap();let path=dir.join("witness-main.bin");
    let start=Instant::now();let a=Authority::build().unwrap();
    let c=Compact::build(&a,&Descriptor::canonical(&a),&placements(),&rows(),&SETUP_ID).unwrap();
    let f=fields();assert_eq!(u64::from(f.height),OWNER+1,"fixture equality remains an external ownership premise");
    let mut x=assign(&a,&f).unwrap();c.check(&x).unwrap();
    assert_eq!((x.len(),x.capacity()),(N,N));assert_eq!((c.circuit().terms.len(),c.circuit().terms.capacity()),(TERMS,TERMS));
    assert_eq!((size_of::<Fr>(),size_of::<Term>()),(32,152));assert_eq!(TERMS*size_of::<Term>(),48334632);
    assert_eq!(a.serializer().layout.fields.n_bits,std::array::from_fn(|j|1362+j));
    assert_eq!((a.serializer().layout.zero,a.serializer().layout.one),(0,1));
    assert_eq!(engine::admit(c.circuit(),0).unwrap(),(18,19));
    // Unchanged reviewed source-build and golden peaks, with sequential lifetimes.
    assert!(390070272usize<512*1024*1024);
    assert!(94221696usize+48334632+71303168+8388608+33554432+5*1024*1024+3*BYTES<512*1024*1024);
    let source_us=micros(start);
    x[1]=Fr::from(2);assert_eq!(pack(&x).err(),Some(PackingError::NonBoolean(1)));x[1]=Fr::one();
    assert_eq!(pack(&x[..N-1]).err(),Some(PackingError::Length));
    let start=Instant::now();let expected=pack(&x).unwrap();let packing_us=micros(start);
    assert_eq!(expected[0],0x12);assert_eq!(&expected[DECODER/8..DECODER/8+4],&[0xCA,0x9A,0x3B,0x04]);
    assert_eq!(expected[INPUT_USED/8]>>(INPUT_USED%8),0);assert_eq!(expected[BYTES-1],0);
    let scalar_oracles=points().map(|p|gkr::mle(&x,&p).unwrap());
    drop(a);
    assert!(!path.exists());let start=Instant::now();let mut writer=PackedFileWriter::create_new(&path,18).unwrap();
    writer.write_bytes(&expected).unwrap();let main=writer.finish().unwrap();let finish_us=micros(start);
    let written=main.io_metrics_snapshot();assert_eq!((written.write_calls,written.write_bytes,written.sync_calls),(1,BYTES as u64,1));
    assert_eq!((written.read_calls,written.read_bytes),(0,0));
    assert!(OpenOptions::new().write(true).open(&path).is_err());assert!(fs::remove_file(&path).is_err());
    let start=Instant::now();let setup=pcs::generate_setup(18).unwrap();let setup_us=micros(start);assert_eq!(setup.id,SETUP_ID);
    assert_eq!((setup.prover.g1_vec.len(),setup.prover.g2_vec.len()),(512,512));
    main.reset_io_metrics();let start=Instant::now();let committed=packed::commit(&main,&setup).unwrap();let commit_us=micros(start);
    let commit_io=main.io_metrics_snapshot();reads(commit_io,1,BYTES as u64);assert_eq!((committed.rows.len(),committed.rows.capacity()),(512,512));
    let commitment=pcs::encode_commitment(&committed.commitment).unwrap();assert_eq!(commitment.len(),384);assert!(commitment.capacity()<=BUFFER_LIMIT);
    let statement=c.statement(setup.id,&commitment,&commitment).unwrap();
    let start=Instant::now();let mut golden=statement.transcript();
    let (gp,gc)=sparse::prove(c.circuit(),&x,0,&mut golden).unwrap();
    assert_eq!(gkr::mle(&x,&gc.point).unwrap(),gc.value);
    let golden_bytes=gkr::encode_proof(&gp).unwrap();assert_eq!(golden_bytes.len(),4128);assert!(golden_bytes.capacity()<=BUFFER_LIMIT);
    let golden_counters=counters(&golden);let golden_probe=probe(&golden);assert_eq!(golden_counters[0],56);
    drop(gp);drop(x);let golden_us=micros(start);
    // No dense X, folded coefficient tables, Authority or dense PCS polynomial is
    // alive when the immutable snapshot and window producer are created.
    main.reset_io_metrics();let start=Instant::now();let bits=snapshot(&main,&expected);let snapshot_us=micros(start);
    let snapshot_io=main.io_metrics_snapshot();reads(snapshot_io,4,BYTES as u64);
    let start=Instant::now();let mut actual=statement.transcript();
    let (proof,claim,work)=engine::prove(c.circuit(),&bits,0,&mut actual).unwrap();let candidate_us=micros(start);
    let encoded=gkr::encode_proof(&proof).unwrap();assert!(encoded.capacity()<=BUFFER_LIMIT);assert_eq!(encoded,golden_bytes);
    assert_eq!(claim,gc);assert_eq!(counters(&actual),golden_counters);assert_eq!(probe(&actual),golden_probe);
    assert_eq!((work.source_visits,work.weighted_terms),(18443478,11447676));
    assert_eq!((work.residual_terms,work.terminal_terms),(317991,317991));
    assert_eq!((work.fold_leaves,work.fold_muls),(9437184,8388612));
    assert_eq!(work.line_bits,N as u64);assert_eq!(work.line_ones,expected.iter().map(|b|u64::from(b.count_ones())).sum::<u64>());
    assert_eq!(work.line_updates,189*work.line_ones);assert_eq!(work.cache_muls,28546);
    assert_eq!(work.window_bytes,3145728);assert!(work.cache_peak_bytes<=131072);
    assert_eq!(proof.layers[0].line_coefficients.len()*size_of::<Fr>(),608);
    assert!(48334632usize+3145728+131072+1216+3*BYTES+33554432+5*1024*1024<512*1024*1024);
    let start=Instant::now();cache_controls();algebra_controls();admission_controls();source_controls(c.circuit(),&bits,scalar_oracles);let controls_us=micros(start);
    let start=Instant::now();let decoded=sparse::decode_proof(c.circuit(),0,&encoded).unwrap();
    assert!(sparse::decode_proof(c.circuit(),0,&encoded[..encoded.len()-1]).is_err());
    let mut extra=encoded.clone();extra.push(0);assert!(sparse::decode_proof(c.circuit(),0,&extra).is_err());drop(extra);
    let mut verify=statement.transcript();let verified=sparse::verify(c.circuit(),0,&decoded,&mut verify).unwrap();
    assert_eq!(verified,claim);assert_eq!(counters(&verify),golden_counters);assert_eq!(probe(&verify),golden_probe);
    // These ordinary verifier tables are a separate phase; the window producer
    // has already dropped all caches/windows and returned only its small proof.
    let mut changed=decoded.clone();changed.layers[0].rounds[0][1]+=Fr::one();changed.layers[0].rounds[0][2]-=Fr::one();
    let round=&changed.layers[0].rounds[0];assert_eq!(round[0]+gkr::eval_polynomial(round,Fr::one()),Fr::zero());
    assert_eq!(sparse::verify(c.circuit(),0,&changed,&mut statement.transcript()).err(),Some(GkrError::SumcheckIdentity));drop(changed);
    let mut changed=decoded.clone();changed.layers[0].right_value+=Fr::one();
    assert_eq!(sparse::verify(c.circuit(),0,&changed,&mut statement.transcript()).err(),Some(GkrError::TerminalExpression));drop(changed);
    let mut changed=decoded.clone();let h0=changed.layers[0].line_coefficients[0];changed.layers[0].line_coefficients[1]+=Fr::one();
    assert_eq!(changed.layers[0].line_coefficients[0],h0);
    assert_eq!(sparse::verify(c.circuit(),0,&changed,&mut statement.transcript()).err(),Some(GkrError::LineEndpoints));drop(changed);
    let codec_verify_us=micros(start);
    assert_eq!(main.evaluate(&claim.point).unwrap(),claim.value);
    main.reset_io_metrics();let start=Instant::now();let mut open_t=actual.clone();
    let opening=packed::open(&committed,&main,&claim.point,&setup,&mut open_t).unwrap();let pcs_open_us=micros(start);
    let open_io=main.io_metrics_snapshot();reads(open_io,2,2*BYTES as u64);
    let pcs_bytes=pcs::encode_proof(&opening).unwrap();assert_eq!(pcs_bytes.len(),24237);assert!(pcs_bytes.capacity()<=BUFFER_LIMIT);
    let open_counters=counters(&open_t);let open_probe=probe(&open_t);
    drop(opening);drop(decoded);drop(proof);drop(c);drop(bits);drop(expected);drop(committed);drop(main);drop(setup);drop(golden);
    let start=Instant::now();let key=verifier_key::admit(18,KEY).unwrap();let key_admit_us=micros(start);assert_eq!(key.id(),&SETUP_ID);
    assert_eq!(KEY.len(),19824);let opening=pcs::decode_proof(&pcs_bytes,18).unwrap();
    let start=Instant::now();let mut consumer=verify.clone();
    pcs::verify_admitted(statement.commitment(),verified.value,&verified.point,&opening,&key,&mut consumer).unwrap();
    let pcs_verify_us=micros(start);assert_eq!(counters(&consumer),open_counters);assert_eq!(probe(&consumer),open_probe);
    assert!(pcs::verify_admitted(statement.commitment(),verified.value+Fr::one(),&verified.point,&opening,&key,&mut verify.clone()).is_err());
    let meta=fs::symlink_metadata(&path).unwrap();assert!(meta.is_file()&&!meta.file_type().is_symlink());assert_eq!(meta.len(),BYTES as u64);
    assert_eq!(fs::read_dir(&dir).unwrap().count(),1);assert_eq!(fs::read(&path).unwrap().len(),BYTES);
    let diagnostic=Diagnostic {
        schema:1,log_n:18,row_log:19,source_terms:TERMS as u64,packed_bytes:BYTES as u64,
        fill_term_visits:work.source_visits,weighted_terms:work.weighted_terms,residual_terms:work.residual_terms,terminal_terms:work.terminal_terms,bind_terms:TERMS as u64,
        fold_leaves:work.fold_leaves,fold_muls:work.fold_muls,line_bits:work.line_bits,line_ones:work.line_ones,line_updates:work.line_updates,
        cache_build_muls:work.cache_muls,cache_modeled_peak_bytes:work.cache_peak_bytes,window_bytes:work.window_bytes,line_stack_bytes:1216,
        multiplication_bound:214988548,gkr_bytes:encoded.len() as u64,gkr_scalars:129,gkr_challenges:golden_counters[0],dory_bytes:pcs_bytes.len() as u64,
        snapshot_reads:snapshot_io.read_calls,snapshot_read_bytes:snapshot_io.read_bytes,commit_reads:commit_io.read_calls,commit_read_bytes:commit_io.read_bytes,
        open_reads:open_io.read_calls,open_read_bytes:open_io.read_bytes,write_calls:written.write_calls,write_bytes:written.write_bytes,sync_calls:written.sync_calls,
        source_us,packing_us,finish_us,setup_us,commit_us,golden_us,snapshot_us,candidate_us,controls_us,codec_verify_us,pcs_open_us,key_admit_us,pcs_verify_us,
        snapshot_read_ns:nanos(snapshot_io.read_ns),commit_read_ns:nanos(commit_io.read_ns),open_read_ns:nanos(open_io.read_ns),write_ns:nanos(written.write_ns),sync_ns:nanos(written.sync_ns),
        proof_equal:true,claim_equal:true,continuation_equal:true,controls_pass:true,
    };
    let json=serde_json::to_string(&diagnostic).unwrap();assert!(json.len()<=8192);assert!(!json.contains('\n'));
    let _:Diagnostic=serde_json::from_str(&json).unwrap();
    assert!(serde_json::from_str::<Diagnostic>(&format!("{{\"extra\":0,{}",&json[1..])).is_err());
    assert!(serde_json::from_str::<Diagnostic>(&format!("{{\"schema\":1,{}",&json[1..])).is_err());
    let mut out=io::stdout().lock();out.write_all(format!("\nPACKED_GKR_WINDOW_DIAGNOSTIC_V1 {json}\n").as_bytes()).unwrap();out.flush().unwrap();
}

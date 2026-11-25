//! Small I/O and request-boundary controls. No complete H21 candidate or
//! native source is constructed from a mock, digest or small fixture.
use super::*;
use std::io::{self,Cursor};

fn digest(bytes:&[u8])->[u8;64] { Blake2b512::digest(bytes).into() }
fn transcript_state(t:&Transcript)->(u64,u64,u64) {
    (t.challenges(),t.raw_queries(),t.bytes_absorbed())
}

#[derive(Clone,Copy)]
enum ReadFailure { None,Immediate,Eof }
#[derive(Clone,Copy)]
enum SeekFailure { None,First,Rewind }
struct SmallStream {
    cursor:Cursor<Vec<u8>>,read_failure:ReadFailure,seek_failure:SeekFailure,
    seeks:usize,read_calls:usize,max_request:usize,max_chunk:usize,
}
impl SmallStream {
    fn new(bytes:Vec<u8>)->Self {
        Self {cursor:Cursor::new(bytes),read_failure:ReadFailure::None,
            seek_failure:SeekFailure::None,seeks:0,read_calls:0,max_request:0,max_chunk:usize::MAX}
    }
}
impl Read for SmallStream {
    fn read(&mut self,out:&mut [u8])->io::Result<usize> {
        self.read_calls+=1;self.max_request=self.max_request.max(out.len());
        match self.read_failure {
            ReadFailure::Immediate=>return Err(io::Error::other("small injected read error")),
            ReadFailure::Eof if self.cursor.position()>=self.cursor.get_ref().len()as u64=>
                return Err(io::Error::other("small injected EOF read error")),
            _=>{},
        }
        let take=out.len().min(self.max_chunk);
        self.cursor.read(&mut out[..take])
    }
}
impl Seek for SmallStream {
    fn seek(&mut self,from:SeekFrom)->io::Result<u64> {
        self.seeks+=1;
        if matches!((self.seek_failure,self.seeks),(SeekFailure::First,1)|(SeekFailure::Rewind,2)) {
            return Err(io::Error::other("small injected seek error"));
        }
        self.cursor.seek(from)
    }
}

#[test]
fn c593_untrusted_hash_reads_exact_bytes_eof_and_rewinds() -> Result<(),String> {
    let bytes:Vec<_>=(0..65_553).map(|n|((n*29+7)%256)as u8).collect();
    let expected=digest(&bytes);let mut stream=SmallStream::new(bytes.clone());
    stream.cursor.set_position(17);stream.max_chunk=113;
    assert_eq!(hash_untrusted_h21_stream(&mut stream,bytes.len()as u64,None)?,expected);
    assert_eq!(stream.cursor.position(),0);assert_eq!(stream.seeks,2);
    assert!(stream.max_request<=65_536);assert!(stream.read_calls>2);
    let mut changed=bytes;changed[65_536]^=1;
    let changed_digest=hash_untrusted_h21_stream(&mut SmallStream::new(changed),65_553,None)?;
    assert_ne!(changed_digest,expected);
    Ok(())
}

#[test]
fn c593_untrusted_hash_expected_digest_is_only_an_optional_check() -> Result<(),String> {
    let bytes=vec![0x51,0x04,0xff,0x80,0x11];let actual=digest(&bytes);
    let mut correct=SmallStream::new(bytes.clone());
    assert_eq!(hash_untrusted_h21_stream(&mut correct,5,Some(actual))?,actual);
    assert_eq!(correct.cursor.position(),0);
    let mut wrong=actual;wrong[31]^=1;
    assert!(hash_untrusted_h21_stream(&mut SmallStream::new(bytes.clone()),5,Some(wrong)).is_err());
    assert_eq!(hash_untrusted_h21_stream(&mut SmallStream::new(bytes),5,None)?,actual);
    Ok(())
}

#[test]
fn c593_untrusted_hash_refuses_short_trailing_read_and_seek_failures() {
    assert!(hash_untrusted_h21_stream(&mut SmallStream::new(vec![1,2,3]),4,None).is_err());
    assert!(hash_untrusted_h21_stream(&mut SmallStream::new(vec![1,2,3,4,5]),4,None).is_err());
    for fault in [ReadFailure::Immediate,ReadFailure::Eof] {
        let mut stream=SmallStream::new(vec![1,2,3,4]);stream.read_failure=fault;
        assert!(hash_untrusted_h21_stream(&mut stream,4,None).is_err());
    }
    for fault in [SeekFailure::First,SeekFailure::Rewind] {
        let mut stream=SmallStream::new(vec![1,2,3,4]);stream.seek_failure=fault;
        assert!(hash_untrusted_h21_stream(&mut stream,4,None).is_err());
    }
}

#[test]
fn c593_untrusted_hash_held_borrow_conflict_returns_error() -> Result<(),String> {
    let handle=RefCell::new(SmallStream::new(vec![0x35,0x89]));
    let held=handle.borrow_mut();
    assert!(hash_untrusted_h21_handle(&handle,2,None).is_err());
    assert_eq!(held.read_calls,0);drop(held);
    assert_eq!(hash_untrusted_h21_handle(&handle,2,None)?,digest(&[0x35,0x89]));
    assert_eq!(handle.borrow().cursor.position(),0);
    Ok(())
}

#[test]
fn c593_untrusted_geometry_refuses_every_other_log_or_extent() {
    let extent=274_877_906_944u64;
    assert!(require_untrusted_h21_geometry(41,extent).is_ok());
    for log in [0,24,32,40,42,usize::MAX] {
        assert!(require_untrusted_h21_geometry(log,extent).is_err());
    }
    for bytes in [0,extent-1,extent+1,u64::MAX] {
        assert!(require_untrusted_h21_geometry(41,bytes).is_err());
    }
}

#[test]
fn c593_untrusted_owner_reader_returns_only_checked_lsb_data() -> Result<(),String> {
    let bytes:Vec<_>=(0..131_072).map(|n|((n*17+0xa5)%256)as u8).collect();
    let handle=RefCell::new(SmallStream::new(bytes.clone()));
    let bits=read_h21_owner_from_handle(&handle,0,|_,_,_|{})?;
    assert_eq!(bits.len(),1<<20);
    for index in [0,1,7,8,15,(1<<20)-1] {
        assert_eq!(bits.bit_at(index),(bytes[index/8]>>(index%8))&1!=0);
    }
    let short=RefCell::new(SmallStream::new(bytes[..bytes.len()-1].to_vec()));
    assert!(read_h21_owner_from_handle(&short,0,|_,_,_|{}).is_err());
    let mut failing=SmallStream::new(bytes);failing.read_failure=ReadFailure::Immediate;
    assert!(read_h21_owner_from_handle(&RefCell::new(failing),0,|_,_,_|{}).is_err());
    let held=handle.borrow_mut();
    assert!(read_h21_owner_from_handle(&handle,0,|_,_,_|{}).is_err());
    assert!(read_h21_owner_from_handle(&handle,1<<21,|_,_,_|{}).is_err());
    drop(held);
    Ok(())
}

#[test]
fn c593_untrusted_requested_identity_mismatch_prevents_all_work() -> Result<(),String> {
    use crate::historical_prefix_proof::with_matching_h21_requested_identity;
    let requested=b"requested-H21-public-statement";
    let mut changed=requested.to_vec();changed[11]^=1;
    let operations=std::cell::Cell::new(0usize);
    let mut transcript=Transcript::new(b"c593-untrusted-request-boundary-only");
    let before=transcript_state(&transcript);
    let rejected=with_matching_h21_requested_identity(requested,&changed,|| {
        operations.set(operations.get()+1);
        Ok(transcript.challenge_scalar(b"must-not-query"))
    });
    assert!(rejected.is_err());assert_eq!(operations.get(),0);
    assert_eq!(transcript_state(&transcript),before);
    with_matching_h21_requested_identity(requested,requested,|| {
        operations.set(operations.get()+1);
        transcript.challenge_scalar(b"matching-request-only");Ok(())
    })?;
    assert_eq!(operations.get(),1);assert_eq!(transcript.challenges(),1);
    Ok(())
}

#[test]
fn c593_untrusted_typed_producer_and_precommit_open_call_sites() {
    use crate::core_pool_boolean::{CandidateRole0Proof,H21Role0DiagnosticBudget};
    type Bind=fn(&mut Transcript)->Result<(),String>;
    type Wiring=fn(&[Fr],&[Fr],&[Fr])->Result<[Fr;4],String>;
    fn entry(plan:&crate::core_pool::Plan,candidate:&UntrustedH21CandidateFile,
        budget:H21Role0DiagnosticBudget,t:&mut Transcript,bind:Bind,wiring:Wiring)
        ->Result<CandidateRole0Proof,String> {
        crate::core_pool_boolean::prove_packed_h21_untrusted_role0_candidate(
            plan,candidate,budget,t,bind,wiring)
    }
    fn before_commitment(public:&crate::historical_prefix_proof::H21StructuralDiagnostic,path:&Path)
        ->Result<UntrustedH21CandidateFile,String> {
        public.open_untrusted_candidate(path,None)
    }
    fn polynomial(candidate:&UntrustedH21CandidateFile)->&PackedFile {candidate.untrusted_polynomial()}
    let _entry:fn(&crate::core_pool::Plan,&UntrustedH21CandidateFile,H21Role0DiagnosticBudget,
        &mut Transcript,Bind,Wiring)->Result<CandidateRole0Proof,String>=entry;
    let _open:fn(&crate::historical_prefix_proof::H21StructuralDiagnostic,&Path)
        ->Result<UntrustedH21CandidateFile,String>=before_commitment;
    let _polynomial:fn(&UntrustedH21CandidateFile)->&PackedFile=polynomial;
}

#[cfg(windows)]
#[test]
#[ignore="external project-owned tiny fixture directory required via NIPOPOW_C593_TEST_DIR"]
fn c593_untrusted_small_actual_held_file_denies_write_delete_and_keeps_hash() -> Result<(),String> {
    use std::os::windows::fs::MetadataExt;
    let directory=PathBuf::from(std::env::var_os("NIPOPOW_C593_TEST_DIR")
        .ok_or("missing NIPOPOW_C593_TEST_DIR")?);
    if !crate::preview_test_paths::absolute_outside_source(&directory) {
        return Err("C593 external project-owned fixture directory".into());
    }
    let md=std::fs::symlink_metadata(&directory).map_err(|e|e.to_string())?;
    if !md.is_dir() || md.file_type().is_symlink() || md.file_attributes()&0x400!=0 {
        return Err("C593 regular fixture directory".into());
    }
    let nonce=std::time::SystemTime::now().duration_since(std::time::UNIX_EPOCH)
        .map_err(|e|e.to_string())?.as_nanos();
    let path=directory.join(format!("c593-small-held-{}-{nonce}.bits",std::process::id()));
    let bytes:Vec<_>=(0..4096).map(|n|((n*19+3)%256)as u8).collect();
    let mut writer=OpenOptions::new().write(true).create_new(true).open(&path).map_err(|e|e.to_string())?;
    writer.write_all(&bytes).map_err(|e|e.to_string())?;writer.sync_all().map_err(|e|e.to_string())?;
    drop(writer);
    assert!(open_untrusted_held_regular(&path,4095).is_err());
    let handle=RefCell::new(open_untrusted_held_regular(&path,4096)?);
    require_regular_untrusted_held_file(&handle.borrow(),4096)?;
    assert!(require_regular_untrusted_held_file(&handle.borrow(),4095).is_err());
    let expected=digest(&bytes);
    assert_eq!(hash_untrusted_h21_handle(&handle,4096,None)?,expected);
    assert!(OpenOptions::new().write(true).open(&path).is_err());
    assert!(std::fs::remove_file(&path).is_err());
    assert_eq!(hash_untrusted_h21_handle(&handle,4096,Some(expected))?,expected);
    assert!(UntrustedH21CandidateFile::open_requested(&path,b"requested-only",None).is_err());
    drop(handle);
    assert!(OpenOptions::new().write(true).open(&path).is_ok());
    println!("C593_SMALL_HELD_FIXTURE_RETAINED {}",path.display());
    Ok(())
}

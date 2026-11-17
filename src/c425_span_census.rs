//! Test-only source-callsite spans for the C425 nonserializer HEADER census.
//! This records producer ownership; it does not propose or evaluate a grammar.
use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use crate::{daa_history_layout, sparse::Term};
use ark_ff::{BigInteger,PrimeField};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct SerializerFamilyOrigin {
    pub(crate) serializer_term_ordinal: usize,
    pub(crate) label: &'static str,
    pub(crate) family_ordinal: usize,
}

const C397_SOURCE_CLOSURE_SHA256: &str =
    "50B0A3A03482F58B02AE37C1C9710E40986C014A2ECD5597248E34CF5D52CC9A";
const C423_PRECODE_SHA256: &str =
    "55EF77CA39A3E9299FD4262B2EB83F98D0473E981ECC2BE605A3D9BC8AF86AB3";
const C397_FILE_PINS: &[(&str, &str)] = &[
    ("daa_history_layout.rs", "DF4A9002BA9A1AB02A62F8A2A8796ADA65CB29BF3F049813A82F6F2D27EF924A"),
    ("header_history_boundary.rs", "C110376EF38F70A2B64EEE96E2322E5520796F8CE1DEE68349D459B6FF4C6BF5"),
    ("work_tree_history_plan.rs", "4F74DB124431BDF5AC425A8D7BDE1B5C5CE5A7E29EDF174A34C3C09D80759E2D"),
    ("daa_history_roster.rs", "5C4CDFACE845FD7A8BFFE562ADC3BC1356CE1F30A7CBA7623F8EC03280BD5152"),
    ("header_scheduled_retirement.rs", "EA55866D578AACF03F7921192A224B29378A63FB6BE68E63F19879AA9DA19C69"),
    ("header_daa_row_placement.rs", "EB764570FFCEC6D8A4EA11F64C80180DE5832651C5722A76C43874A25ABE09A3"),
    ("header_compact_links.rs", "83CAFF672EF1989CA65BA01B401FD7986C12FDCEA0D85B4432B4D6006DF495D3"),
    ("header_order.rs", "4E8F013E237AE9D03AA4E70BAE22BC02BB1FFACD144A8FD02FDBD81305D38AAC"),
    ("segment_relation.rs", "FBBD07EF2642327A77B4C89BA0A05E035FA062C427768B534E92B19B0389A1A7"),
    ("segment_points.rs", "723F580FF7B11F96AE28F20DE77774AD3821886CB9814F4AC6CD7751982CEA28"),
    ("header_hash.rs", "44123BCF2160A1785C6FB57FD6EBDA47195BFFFC30925409558EB8217C61DAF1"),
    ("serializer.rs", "91EA77B9CB25DD6CC2D268CC21BB37423119E0ED40E928E7BEFC51A25F4A19B1"),
];

// These are the reviewed pre-instrumentation source identities. The clone's
// instrumented files necessarily have different hashes; this table preserves
// provenance and is not a runtime check of modified source bytes.

thread_local! {
    static ACTIVE: Cell<bool> = const { Cell::new(false) };
    static SOURCE_SPANS: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
    static SOURCE_FAMILY_ORIGINS: RefCell<Vec<Option<SerializerFamilyOrigin>>> = const { RefCell::new(Vec::new()) };
    static SERIALIZER_FAMILY_EVENTS: RefCell<Vec<SerializerFamilyOrigin>> = const { RefCell::new(Vec::new()) };
    static CURRENT_SOURCE_ORDINAL: Cell<Option<usize>> = const { Cell::new(None) };
}

struct SourceOrdinalRestore(Option<usize>);
impl Drop for SourceOrdinalRestore {
    fn drop(&mut self) {
        CURRENT_SOURCE_ORDINAL.with(|current| current.set(self.0));
    }
}

/// Keep the literal canonical occurrence ordinal active only during the
/// synchronous producer callback. The guard restores nested state on `Err`
/// and during panic unwinding.
pub(crate) fn with_source_ordinal<T>(ordinal: usize, f: impl FnOnce() -> T) -> T {
    let previous = CURRENT_SOURCE_ORDINAL.with(|current| current.replace(Some(ordinal)));
    let _restore = SourceOrdinalRestore(previous);
    f()
}

pub(crate) fn current_source_ordinal() -> Option<usize> {
    CURRENT_SOURCE_ORDINAL.with(Cell::get)
}

pub(crate) fn begin_source_spans() {
    SOURCE_SPANS.with(|spans| spans.borrow_mut().clear());
    SOURCE_FAMILY_ORIGINS.with(|origins| origins.borrow_mut().clear());
    SERIALIZER_FAMILY_EVENTS.with(|events| events.borrow_mut().clear());
    ACTIVE.with(|active| {
        assert!(!active.replace(true), "C425 span capture already active");
    });
}

/// Record a disjoint term-index interval at the actual generator callsite.
pub(crate) fn append_source_span(label: &'static str, start: usize, end: usize) {
    ACTIVE.with(|active| {
        if !active.get() { return; }
        SOURCE_SPANS.with(|spans| {
            let mut spans = spans.borrow_mut();
            assert_eq!(start, spans.len(), "C425 source span gap/overlap at {label}");
            assert!(end >= start, "C425 source span reversed at {label}");
            spans.resize(end, label);
        });
        SOURCE_FAMILY_ORIGINS.with(|origins| {
            let mut origins = origins.borrow_mut();
            assert_eq!(start, origins.len(), "C427 source-origin gap/overlap at {label}");
            origins.resize(end, None);
        });
    });
}

/// Record the serializer Builder's direct term index at the family emission
/// callsite. The index is source provenance, not a tuple/row classification.
pub(crate) fn record_serializer_family_term(
    serializer_term_ordinal: usize,
    label: &'static str,
    family_ordinal: usize,
) {
    ACTIVE.with(|active| {
        if !active.get() { return; }
        assert!(matches!(label, "serializer_boolean_diagonal" | "serializer_input_padding"),
            "C427 unknown serializer family label {label}");
        SERIALIZER_FAMILY_EVENTS.with(|events| events.borrow_mut().push(SerializerFamilyOrigin {
            serializer_term_ordinal, label, family_ordinal,
        }));
    });
}

/// Mirror the exact prefix/serializer/suffix splice in the attachment producer.
pub(crate) fn replace_source_span_range(first: usize, after: usize, serializer_terms: usize) {
    ACTIVE.with(|active| {
        if !active.get() { return; }
        SOURCE_SPANS.with(|spans| {
            let mut spans = spans.borrow_mut();
            assert!(first <= after && after <= spans.len(), "C425 serializer splice bounds");
            spans.splice(first..after, std::iter::repeat("serializer.attach").take(serializer_terms));
        });
        let events = SERIALIZER_FAMILY_EVENTS.with(|events| std::mem::take(&mut *events.borrow_mut()));
        let mut local = vec![None; serializer_terms];
        for event in events {
            let target = local.get_mut(event.serializer_term_ordinal)
                .expect("C427 serializer family source ordinal outside attached source");
            assert!(target.replace(event).is_none(), "C427 duplicate serializer source ordinal");
        }
        SOURCE_FAMILY_ORIGINS.with(|origins| {
            let mut origins = origins.borrow_mut();
            assert!(first <= after && after <= origins.len(), "C427 source-origin splice bounds");
            origins.splice(first..after, local);
        });
    });
}

pub(crate) fn finish_source_spans() -> Vec<&'static str> {
    ACTIVE.with(|active| assert!(active.replace(false), "C425 span capture is not active"));
    SOURCE_SPANS.with(|spans| std::mem::take(&mut *spans.borrow_mut()))
}

/// Return the serializer family sidecar aligned to the canonical global
/// source ordinals. `None` denotes an attached serializer term outside C427.
pub(crate) fn finish_source_family_origins() -> Vec<Option<SerializerFamilyOrigin>> {
    SOURCE_FAMILY_ORIGINS.with(|origins| std::mem::take(&mut *origins.borrow_mut()))
}

pub(crate) fn tuple(term: &Term) -> (usize, usize, usize, ark_bn254::Fr, ark_bn254::Fr, ark_bn254::Fr, ark_bn254::Fr) {
    (term.row, term.gate.left, term.gate.right, term.gate.c0, term.gate.c1,
        term.gate.c2, term.gate.c3)
}

#[cfg(windows)]
#[link(name="advapi32")]
extern "system" {
    fn CryptAcquireContextW(provider:*mut usize,container:*const u16,provider_name:*const u16,
        provider_type:u32,flags:u32)->i32;
    fn CryptCreateHash(provider:usize,algorithm:u32,key:usize,flags:u32,hash:*mut usize)->i32;
    fn CryptHashData(hash:usize,data:*const u8,len:u32,flags:u32)->i32;
    fn CryptGetHashParam(hash:usize,parameter:u32,data:*mut u8,len:*mut u32,flags:u32)->i32;
    fn CryptDestroyHash(hash:usize)->i32;
    fn CryptReleaseContext(provider:usize,flags:u32)->i32;
}

#[cfg(windows)]
struct Sha256Stream{provider:usize,hash:usize}
#[cfg(windows)]
impl Sha256Stream {
    fn new()->Result<Self,String>{
        let mut provider=0;
        if unsafe{CryptAcquireContextW(&mut provider,std::ptr::null(),std::ptr::null(),24,0xf000_0000)}==0{
            return Err(format!("C425 SHA256 provider: {}",std::io::Error::last_os_error()));}
        let mut hash=0;
        if unsafe{CryptCreateHash(provider,0x800c,0,0,&mut hash)}==0{
            unsafe{CryptReleaseContext(provider,0)};
            return Err(format!("C425 SHA256 hash: {}",std::io::Error::last_os_error()));}
        Ok(Self{provider,hash})
    }
    fn update(&mut self,bytes:&[u8])->Result<(),String>{
        if bytes.len()>64*1024 || unsafe{CryptHashData(self.hash,bytes.as_ptr(),bytes.len() as u32,0)}==0{
            return Err(format!("C425 SHA256 update: {}",std::io::Error::last_os_error()));}Ok(())
    }
    fn finish(self)->Result<[u8;32],String>{
        let mut digest=[0u8;32];let mut len=32u32;
        if unsafe{CryptGetHashParam(self.hash,2,digest.as_mut_ptr(),&mut len,0)}==0 || len!=32{
            return Err(format!("C425 SHA256 finish: {}",std::io::Error::last_os_error()));}Ok(digest)
    }
}
#[cfg(windows)]
impl Drop for Sha256Stream{fn drop(&mut self){unsafe{CryptDestroyHash(self.hash);CryptReleaseContext(self.provider,0);}}}

/// C425-local diagnostic digests. Their framing is intentionally distinct from
/// C423's published digest contract. Source ordinals come only from the
/// test-only visitor guard; identity is never inferred from tuple matching.
#[cfg(windows)]
pub(crate) fn owner_sha256(owner:usize,records:&[(usize,Term,Term)])->Result<(String,String),String>{
    fn n(value:usize)->[u8;8]{u64::try_from(value).expect("C425 usize fits u64").to_le_bytes()}
    fn fr(value:ark_bn254::Fr)->[u8;32]{
        let mut bytes=value.into_bigint().to_bytes_le();
        if bytes.len()>32{panic!("C425 Fr encoding exceeds 32 bytes");}
        bytes.resize(32,0);bytes.try_into().unwrap()
    }
    fn append_record(hash:&mut Sha256Stream,owner:usize,ordinal:usize,source:&Term,placed:&Term,
        tuple_term:&Term)->Result<(),String>{
        for value in [owner,ordinal,source.row,placed.row]{hash.update(&n(value))?;}
        hash.update(&n(tuple_term.gate.left))?;hash.update(&n(tuple_term.gate.right))?;
        for coefficient in [tuple_term.gate.c0,tuple_term.gate.c1,tuple_term.gate.c2,tuple_term.gate.c3]{
            hash.update(&fr(coefficient))?;
        }Ok(())
    }
    let owner_bytes=n(owner);
    let mut source=Sha256Stream::new()?;let mut placed=Sha256Stream::new()?;
    source.update(b"c425-local-header-owner-source-v1\0")?;source.update(&owner_bytes)?;
    placed.update(b"c425-local-header-owner-placed-v1\0")?;placed.update(&owner_bytes)?;
    for (ordinal,source_term,placed_term) in records{
        append_record(&mut source,owner,*ordinal,source_term,placed_term,source_term)?;
        append_record(&mut placed,owner,*ordinal,source_term,placed_term,placed_term)?;
    }
    let source=source.finish()?.iter().map(|b|format!("{b:02x}")).collect();
    let placed=placed.finish()?.iter().map(|b|format!("{b:02x}")).collect();
    Ok((source,placed))
}

#[cfg(not(windows))]
pub(crate) fn owner_sha256(_owner:usize,_records:&[(usize,Term,Term)])->Result<(String,String),String>{
    Err("C425 owner SHA256 digest implementation requires Windows CryptoAPI".into())
}

/// C427 ordered family record digests under independent source and placed
/// domains. Each retained record binds owner, global ordinal, both rows,
/// endpoints, and all four canonical Fr coefficients.
#[cfg(windows)]
pub(crate) fn c427_owner_sha256(owner:usize,records:&[(usize,Term,Term)])->Result<(String,String),String>{
    fn n(value:usize)->[u8;8]{u64::try_from(value).expect("C427 usize fits u64").to_le_bytes()}
    fn fr(value:ark_bn254::Fr)->[u8;32]{
        let mut bytes=value.into_bigint().to_bytes_le();
        if bytes.len()>32{panic!("C427 Fr encoding exceeds 32 bytes");}
        bytes.resize(32,0);bytes.try_into().unwrap()
    }
    fn record(hash:&mut Sha256Stream,owner:usize,ordinal:usize,source:&Term,placed:&Term,
        tuple_term:&Term)->Result<(),String>{
        for value in [owner,ordinal,source.row,placed.row,tuple_term.gate.left,tuple_term.gate.right]{
            hash.update(&n(value))?;
        }
        for coefficient in [tuple_term.gate.c0,tuple_term.gate.c1,tuple_term.gate.c2,tuple_term.gate.c3]{
            hash.update(&fr(coefficient))?;
        }Ok(())
    }
    let owner_bytes=n(owner);
    let mut source=Sha256Stream::new()?;let mut placed=Sha256Stream::new()?;
    source.update(b"c427-header-family-source-v1\0")?;source.update(&owner_bytes)?;
    placed.update(b"c427-header-family-placed-v1\0")?;placed.update(&owner_bytes)?;
    for (ordinal,source_term,placed_term) in records{
        record(&mut source,owner,*ordinal,source_term,placed_term,source_term)?;
        record(&mut placed,owner,*ordinal,source_term,placed_term,placed_term)?;
    }
    let source=source.finish()?.iter().map(|b|format!("{b:02x}")).collect();
    let placed=placed.finish()?.iter().map(|b|format!("{b:02x}")).collect();
    Ok((source,placed))
}

#[cfg(not(windows))]
pub(crate) fn c427_owner_sha256(_owner:usize,_records:&[(usize,Term,Term)])->Result<(String,String),String>{
    Err("C427 ordered family digest requires Windows CryptoAPI".into())
}

fn first_divergence(expected: &[Term], observed: &[Term]) -> Option<usize> {
    let shared = expected.len().min(observed.len());
    (0..shared).find(|&ordinal| expected[ordinal] != observed[ordinal])
        .or_else(|| (expected.len() != observed.len()).then_some(shared))
}

#[test]
fn source_ordinal_guard_restores_after_error_and_unwind() {
    assert_eq!(current_source_ordinal(),None);
    let result:Result<(),&str>=with_source_ordinal(17,||{
        assert_eq!(current_source_ordinal(),Some(17));Err("sentinel")
    });
    assert_eq!(result,Err("sentinel"));
    assert_eq!(current_source_ordinal(),None);
    let unwind=std::panic::catch_unwind(||with_source_ordinal(23,||{
        assert_eq!(current_source_ordinal(),Some(23));panic!("sentinel unwind")
    }));
    assert!(unwind.is_err());
    assert_eq!(current_source_ordinal(),None);
}

#[test]
fn source_spans_partition_nonserializer_header_and_match_cold_literal() {
    // This cold traversal runs without span capture and is the ordered literal
    // authority. The second traversal emits labels only at pinned source
    // generator callsites; labels never classify the cold stream.
    let literal = daa_history_layout::full_header_boundary(None).unwrap();
    let literal_circuit = &literal.base.base.base.boundary;
    let expected = &literal_circuit.terms;
    assert_eq!(expected.len(), 474_755);
    assert_eq!(literal_circuit.input_len, 1 << 20);
    assert_eq!(literal_circuit.row_count, 1 << 19);
    assert!(expected.windows(2).all(|pair| pair[0].row <= pair[1].row),
        "C425 literal source rows are not monotone");
    assert_eq!(
        crate::work_tree_layout::hash_terms(expected),
        "580f92b15945029ea82a9f1e0b97cfc9917df940380211a8fd6701e39336ab76",
        "C425 literal canonical fingerprint changed",
    );

    begin_source_spans();
    let instrumented = daa_history_layout::full_header_boundary(None).unwrap();
    let spans = finish_source_spans();
    let observed = &instrumented.base.base.base.boundary.terms;

    assert_eq!(spans.len(), observed.len(), "C425 span/term length divergence");
    if let Some(ordinal) = first_divergence(expected, observed) {
        panic!("C425 literal first divergence ordinal={ordinal} expected={:?} observed={:?}",
            expected.get(ordinal).map(tuple), observed.get(ordinal).map(tuple));
    }

    let serializer_rows = 12_836..274_980;
    let mut counts = BTreeMap::<&'static str, usize>::new();
    let mut first_last = BTreeMap::<&'static str, (usize, usize, (usize, usize, usize, ark_bn254::Fr, ark_bn254::Fr, ark_bn254::Fr, ark_bn254::Fr), (usize, usize, usize, ark_bn254::Fr, ark_bn254::Fr, ark_bn254::Fr, ark_bn254::Fr))>::new();
    let mut instrumented_nonserializer = Vec::new();
    let literal_nonserializer = expected.iter().enumerate()
        .filter(|(_, term)| !serializer_rows.contains(&term.row))
        .map(|(ordinal, term)| (ordinal, tuple(term))).collect::<Vec<_>>();
    for (ordinal, (span, term)) in spans.iter().copied().zip(observed).enumerate() {
        if span == "serializer.attach" {
            assert!(serializer_rows.contains(&term.row),
                "C425 serializer attachment outside pinned replacement rows at ordinal {ordinal}");
            continue;
        }
        assert!(!serializer_rows.contains(&term.row),
            "C425 nonserializer generator owns replaced padding at ordinal {ordinal}");
        let term_tuple = tuple(term);
        let count = counts.entry(span).or_default();
        *count += 1;
        first_last.entry(span)
            .and_modify(|entry| { entry.1 = ordinal; entry.3 = term_tuple; })
            .or_insert((ordinal, ordinal, term_tuple, term_tuple));
        instrumented_nonserializer.push((ordinal, span, term_tuple));
    }

    assert_eq!(counts.values().sum::<usize>(), 159_209,
        "C425 source-callsite nonserializer terms must match C423 exactly");
    assert_eq!(instrumented_nonserializer.len(), 159_209);
    assert_eq!(literal_nonserializer.len(), 159_209);
    if let Some(index) = literal_nonserializer.iter().zip(&instrumented_nonserializer)
        .position(|(literal, (_, _, observed))| literal.1 != *observed) {
        panic!("C425 nonserializer projection first divergence index={index} literal={:?} span={} observed={:?}",
            literal_nonserializer[index], instrumented_nonserializer[index].1,
            instrumented_nonserializer[index].2);
    }
    assert!(counts.keys().all(|span|
        span.starts_with("header_hash.boundary.") || span.starts_with("segment_points.")
            || span.starts_with("header_order.") || span.starts_with("header_compact_links.")),
        "C425 contains an unclassified nonserializer source span");

    let spans_json = counts.iter().map(|(name, count)| (*name, *count, *first_last.get(name).unwrap()))
        .collect::<Vec<_>>();
    println!("C425 recorded authority pins (not runtime validation of modified files): C397={C397_SOURCE_CLOSURE_SHA256} C423_PRECODE={C423_PRECODE_SHA256}");
    println!("C425 deciding source file baseline pins: {C397_FILE_PINS:?}");
    println!("C425 source-only pre-retirement census: total=474755 serializer=315546 nonserializer=159209 spans={spans_json:?}");
}

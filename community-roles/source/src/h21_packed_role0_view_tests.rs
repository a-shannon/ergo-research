//! Descriptor and private I/O controls. No mock constructs a native complete
//! source, a native view, a proof or a verified-history handle.
use super::*;
use crate::legacy_envelope_map::{LowerBranch, LowerSelector, LowerSource, Map};
use std::io;

fn maps() -> [Binding; 2] {
    crate::bank53_map::CutDescriptor::eligible08().terminals().map(|n| {
        Map::new_modern_global_u_selected_lower(n as u64, 21, 55, LowerSelector {
            source: LowerSource::HeaderDifficulty { height: 841_729 },
            branch: LowerBranch::Pivot(54),
        }).unwrap().binding()
    })
}

#[test]
fn c591_complete_source_constructor_has_exact_native_signature() {
    type Constructor = for<'source, 'parent> fn(
        &'source NativeH21PackedSource, &'parent WorkTreeHistoryPlan, [Binding; 2],
    ) -> Result<PackedH21Role0View<'source>, String>;
    // The impl lifetime of from_complete is early-bound. This real call site
    // checks the constructor while the wrapper exposes late-bound lifetimes.
    fn native_constructor<'source, 'parent>(
        source: &'source NativeH21PackedSource, parent: &'parent WorkTreeHistoryPlan,
        maps: [Binding; 2],
    ) -> Result<PackedH21Role0View<'source>, String> {
        PackedH21Role0View::from_complete(source, parent, maps)
    }
    let _: Constructor = native_constructor;
}

#[test]
fn c591_descriptor_parent_and_both_full_maps_are_bound() {
    let parent = HeaderSourceBinding::diagnostic_for_test(0);
    let expected_maps = maps();
    assert!(require_h21_source_bindings(&parent, &expected_maps, &parent, &expected_maps).is_ok());
    for field in 0..6 {
        let wrong = parent.mutated_field_for_test(field);
        assert_eq!(require_h21_source_bindings(&wrong, &expected_maps, &parent, &expected_maps)
            .unwrap_err(), "H21 complete role0 parent binding mismatch", "parent field {field}");
    }
    for context in 0..2 {
        for field in 0..10 {
            let mut actual = expected_maps.clone();
            match field {
                0 => actual[context].n += 1,
                1 => actual[context].h += 1,
                2 => actual[context].e += 1,
                3 => actual[context].parent_root = Some([0x91; 32]),
                4..=9 => actual[context] = actual[context].mutated_private_field_for_test(field-4),
                _ => unreachable!(),
            }
            assert_eq!(require_h21_source_bindings(&parent, &actual, &parent, &expected_maps)
                .unwrap_err(), "H21 complete role0 full Map bindings mismatch",
                "context {context}, isolated field {field}");
        }
    }
    let mut swapped = expected_maps.clone(); swapped.swap(0, 1);
    assert!(require_h21_source_bindings(&parent, &swapped, &parent, &expected_maps).is_err());
}

#[test]
fn c591_geometry_host_and_exact_file_extent() {
    assert!(require_h21_host(true, 64).is_ok());
    assert!(require_h21_host(false, 64).is_err());
    assert!(require_h21_host(true, 32).is_err());
    assert!(require_h21_plan_geometry(H21_ROLE0_HEADERS, 21, H21_ROLE0_OWNER_COUNT).is_ok());
    for (n,h,slots) in [
        (H21_ROLE0_HEADERS-1,21,H21_ROLE0_OWNER_COUNT),
        (H21_ROLE0_HEADERS,20,H21_ROLE0_OWNER_COUNT),
        (H21_ROLE0_HEADERS,21,H21_ROLE0_OWNER_COUNT-1),
    ] { assert!(require_h21_plan_geometry(n,h,slots).is_err()); }
    assert!(require_packed_h21_geometry(41, H21_ROLE0_INPUT_BITS).is_ok());
    assert!(require_packed_h21_geometry(32, H21_ROLE0_INPUT_BITS).is_err());
    assert!(require_packed_h21_geometry(41, H21_ROLE0_INPUT_BITS-1).is_err());
    for bytes in [H21_ROLE0_FILE_BYTES as u64-1,H21_ROLE0_FILE_BYTES as u64+1] {
        assert!(require_packed_h21_file_size(bytes).is_err());
    }
    assert!(require_packed_h21_file_size(H21_ROLE0_FILE_BYTES as u64).is_ok());
}

#[test]
fn c591_owner_offsets_bounds_and_checked_overflows() {
    let range = |owner| checked_packed_owner_range(owner,H21_ROLE0_OWNER_COUNT,
        H21_ROLE0_OWNER_BYTES,H21_ROLE0_FILE_BYTES);
    assert_eq!(range(0).unwrap(), (0,131_072));
    assert_eq!(range(1).unwrap(), (131_072,262_144));
    assert_eq!(range(H21_ROLE0_OWNER_COUNT-1).unwrap(), (274_877_775_872,274_877_906_944));
    assert_eq!(range(H21_ROLE0_OWNER_COUNT).unwrap_err(), "H21 packed owner range");
    assert!(range(usize::MAX).is_err());
    assert_eq!(checked_packed_owner_range(0,1,131072,131071).unwrap_err(),
        "H21 packed owner file extent");
    assert_eq!(checked_packed_owner_range(usize::MAX/131072+1,usize::MAX,131072,usize::MAX)
        .unwrap_err(), "H21 packed owner offset overflow");
    assert_eq!(checked_packed_owner_range(1,2,usize::MAX,usize::MAX)
        .unwrap_err(), "H21 packed owner end overflow");
}

fn pattern_byte(offset: u64) -> u8 {
    let row = H21_ROLE0_OWNER_BYTES as u64;
    ((offset / row).wrapping_mul(29) ^ (offset % row).wrapping_mul(17) ^ 0xA5) as u8
}
struct VirtualBackend {
    position: u64, fault: Option<PackedReaderFault>, short_left: usize,
    seek_fails: bool, seeks: usize, reads: usize,
}
impl VirtualBackend {
    fn new(fault: Option<PackedReaderFault>) -> Self {
        Self { position:0,fault,short_left:H21_ROLE0_OWNER_BYTES-1,
            seek_fails:false,seeks:0,reads:0 }
    }
}
impl Read for VirtualBackend {
    fn read(&mut self, out: &mut [u8]) -> io::Result<usize> {
        self.reads += 1;
        let count = match self.fault {
            Some(PackedReaderFault::Io) => return Err(io::Error::other("mock read fault")),
            Some(PackedReaderFault::Short) => 0,
            Some(PackedReaderFault::ShortByOneByte) => {
                let n = out.len().min(self.short_left); self.short_left -= n; n
            },
            None => out.len().min((H21_ROLE0_FILE_BYTES as u64).saturating_sub(self.position) as usize),
        };
        for byte in out.iter_mut().take(count) {
            *byte = pattern_byte(self.position); self.position += 1;
        }
        Ok(count)
    }
}
impl Seek for VirtualBackend {
    fn seek(&mut self, from: SeekFrom) -> io::Result<u64> {
        self.seeks += 1;
        if self.seek_fails { return Err(io::Error::other("mock seek fault")); }
        let next = match from {
            SeekFrom::Start(n) => i128::from(n),
            SeekFrom::Current(n) => i128::from(self.position)+i128::from(n),
            SeekFrom::End(n) => H21_ROLE0_FILE_BYTES as i128+i128::from(n),
        };
        if next < 0 || next > i128::from(u64::MAX) {
            return Err(io::Error::new(io::ErrorKind::InvalidInput,"mock seek range"));
        }
        self.position=next as u64; Ok(self.position)
    }
}

#[test]
fn c591_mock_reads_owner_zero_one_last_in_lsb_order() {
    for owner in [0,1,H21_ROLE0_OWNER_COUNT-1] {
        let handle = RefCell::new(VirtualBackend::new(None));
        let metrics: SharedPackedIo = Arc::new(Mutex::new(PackedIoSnapshot::default()));
        let bits = read_h21_owner_from_handle(&handle,owner,|n,r,t|record_read(&metrics,n,r,t)).unwrap();
        assert_eq!(bits.len(),H21_ROLE0_OWNER_BITS);
        let start=owner as u64*H21_ROLE0_OWNER_BYTES as u64;
        for i in [0,1,7,8,15,H21_ROLE0_OWNER_BITS-1] {
            assert_eq!(bits.bit_at(i),(pattern_byte(start+(i/8) as u64)>>(i%8))&1!=0);
        }
        assert!(bits.bit(16,0).is_err());
        let bytes=bits.into_bytes();
        assert_eq!(bytes.len(),H21_ROLE0_OWNER_BYTES);
        for (i,byte) in bytes.iter().enumerate() {
            assert_eq!(*byte,pattern_byte(start+i as u64));
        }
        let io=*metrics.lock().unwrap();
        assert_eq!((io.read_calls,io.read_bytes),(1,H21_ROLE0_OWNER_BYTES as u64));
        let backend=handle.borrow();
        assert_eq!(backend.position,start+H21_ROLE0_OWNER_BYTES as u64);
        assert_eq!(backend.seeks,1);
    }
}

#[test]
fn c591_mock_short_short_one_and_io_faults_never_return_bits() {
    for fault in [PackedReaderFault::Short,PackedReaderFault::ShortByOneByte,PackedReaderFault::Io] {
        let handle=RefCell::new(VirtualBackend::new(Some(fault)));
        let metrics: SharedPackedIo=Arc::new(Mutex::new(PackedIoSnapshot::default()));
        let result=read_h21_owner_from_handle(&handle,1,|n,r,t|record_read(&metrics,n,r,t));
        assert!(result.is_err(),"fault {fault:?}");
        let io=*metrics.lock().unwrap();
        assert_eq!((io.read_calls,io.read_bytes),(0,0));
    }
}

#[test]
fn c591_mock_seek_and_borrow_faults_fail_closed_and_bounds_precede_io() {
    let handle=RefCell::new(VirtualBackend::new(None));
    assert!(read_h21_owner_from_handle(&handle,H21_ROLE0_OWNER_COUNT,|_,_,_|panic!("no read"))
        .is_err());
    assert_eq!((handle.borrow().seeks,handle.borrow().reads),(0,0));
    handle.borrow_mut().seek_fails=true;
    assert!(read_h21_owner_from_handle(&handle,0,|_,_,_|panic!("no read")).is_err());
    assert_eq!(handle.borrow().reads,0);
    let _held=handle.borrow_mut();
    assert_eq!(read_h21_owner_from_handle(&handle,0,|_,_,_|panic!("no read"))
        .err().as_deref(),Some("H21 complete role0 handle already borrowed"));
}

#[test]
fn c591_source_identity_is_pointer_identity_not_equal_contents() {
    #[derive(Debug,PartialEq)]
    struct Marker(u8);
    let a=Marker(7);let b=Marker(7);
    assert_eq!(a,b);
    assert!(same_source_pointer(&a,&a));
    assert!(!same_source_pointer(&a,&b));
}

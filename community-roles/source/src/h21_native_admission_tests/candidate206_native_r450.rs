//! One-use native R450 source custody diagnostic. No MAX/Score stream or sink.
use super::*;
use crate::packed_owner_assembly::H21EligibleContext;

fn phase(label: &str, started: Instant) {
    println!("C206_PHASE label={label} elapsed_s={:.6}", started.elapsed().as_secs_f64());
    std::io::stdout().flush().expect("flush c206 phase");
}

#[test]
#[ignore = "one-use native R450 frame run requires exact-source runner prelaunch review"]
fn c206_native_r450_publication_from_pinned_frame() {
    let started = Instant::now();
    phase("frame_start", started);
    let path = std::env::var_os("NIPOPOW_H21_FRAME").expect("pinned frame environment");
    let path = Path::new(&path);
    assert!(path.is_absolute());
    let before = fs::symlink_metadata(path).expect("frame metadata");
    assert!(before.is_file() && !before.file_type().is_symlink());
    assert_eq!(before.len(), FRAME_BYTES);
    let file = File::open(path).expect("open existing pinned frame");
    assert_eq!(file.metadata().unwrap().len(), FRAME_BYTES);
    let mut frame = FrameReader::new(BufReader::with_capacity(CHUNK, file), FRAME_BYTES)
        .expect("frame SHA setup");
    preamble(&mut frame, 1_827_839, N as u32).expect("pinned ERFV preamble");
    let (prefix, extensions) = {
        let mut headers = HeaderIter::new(&mut frame, N);
        let prefix = NativePrefix::from_raw_iter(N, &mut headers)
            .expect("single linked native H21 prefix");
        assert_eq!(headers.remaining, 0);
        (prefix, headers.extensions)
    };
    assert_eq!(prefix.header_count(), N);
    assert_eq!(frame.offset, PREFIX_BYTES);
    assert_eq!(extensions, EXTENSIONS);
    frame.finish(PREFIX_BYTES, TAIL_BYTES, FRAME_SHA256).expect("whole existing frame exact SHA");
    let after = fs::symlink_metadata(path).expect("frame restat");
    assert!(after.is_file() && !after.file_type().is_symlink());
    assert_eq!(after.len(), before.len());
    assert_eq!(after.modified().unwrap(), before.modified().unwrap());
    phase("frame_verified", started);
    let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())
        .expect("native H21 plan");
    validate_native_plan_input(&plan, &prefix).expect("native plan/prefix identity");
    phase("plan_verified", started);
    let context = H21EligibleContext::new(&plan, &prefix).expect("native Eligible08 pair");
    phase("context_verified", started);
    let anchors = context.premodern_score_anchors().expect("native premodern Score anchors");
    phase("anchors_verified", started);
    let publication = context.premodern_r_publication(anchors)
        .expect("physical Upper417789/845757 and independent R450 replay");
    phase("publication_verified", started);
    std::hint::black_box(&publication);
    println!("C206_NATIVE_R450_PASS anchor_owners=417790,845758 physical_upper_owners=417789,845757 contexts=2 retained_r_leases=4 projection_cells=900 sink=false max_score_stream=false global_x_row=false pcs_proof_client=false");
    std::io::stdout().flush().expect("flush c206 result");
    drop(publication);
}

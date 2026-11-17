//! C443 no-frame predecessor boundary coverage.
//! This checks the retained first packed anchor and generic physical claims;
//! it does not construct or admit the production second-anchor bundle.

use super::*;
use crate::daa_history_roster::OwnerClass;

#[test]
fn c443_second_anchor_physical_join_no_frame() {
    let owner = 417_790usize;
    let class = OwnerClass::Carry;
    let (binding, bundle) = Eligible08MapSlackAnchorBundle::synthetic_for_test()
        .expect("synthetic first-anchor boundary fixture");
    let mask = vec![false; WIDTH];
    let reserved = preflight_map_slack_anchor_reservation(
        &bundle, &binding, owner, class, &mask,
    ).expect("complete Map+Score+Slack HEADER reservation");
    assert_eq!(reserved.iter().filter(|bit| **bit).count(),
        BANK53_CONTEXTS * BANK53_CONTEXT_BITS);

    let mut rows = OwnedRows::new(OwnerSelection::Single { owner, class });
    claim_map_slack_anchor_live(&mut rows, &bundle, &binding, owner, class)
        .expect("generic Map+Score+Slack physical claim");
    require_map_slack_anchor_claim_census(&rows, &bundle, &binding, owner, class)
        .expect("complete generic source claim census");
    let packed = rows.bytes(0).expect("synthetic first packed owner bytes");
    require_map_slack_anchor_packed(&packed, &bundle, &binding, owner, class)
        .expect("first source matches packed physical boundary");

    let row = NativePackedRow {
        owner,
        class,
        root: binding.root,
        total: binding.total,
        bytes: packed,
        header_source_binding: Some(binding.clone()),
        cap0_source: None,
        cap1_source: None,
        max_binding: None,
        map_binding: None,
        map_context: None,
        legacy_binding: None,
    };
    bundle.checked_packed_for_test(&row)
        .expect("first typed Score source matches retained packed row");

    // Flip one packed bit in the first anchor. The C443 predecessor boundary
    // must reject it before any second-anchor physical producer can run.
    let first_score = bundle.checked_score_cells(&binding, owner, class)
        .expect("first typed Score cells");
    let local = BANK53_BASE + BANK53_MAP_LIVE_BITS
        + crate::origin_score::Layout::new().r.start;
    assert!(first_score.iter().any(|cell| cell.physical_wire() == owner * WIDTH + local),
        "mutated predecessor coordinate is a typed R cell");
    let mut mutated_bytes = row.packed_bytes().to_vec();
    mutated_bytes[local / 8] ^= 1 << (local % 8);
    let mutated = row.with_packed_bytes_for_test(&mutated_bytes)
        .expect("same-metadata packed mutation fixture");
    assert!(bundle.checked_packed_for_test(&mutated).is_err(),
        "changed first packed Score/R bit rejected at predecessor boundary");

    println!("C443_NOFRAME_PREDECESSOR_BOUNDARY_PASS owner=417790 class=Carry contexts=2 reserved_claimed_packed_cells=16384 first_r_flip_rejected=true second_bundle=false frame=false authentic_source=false proof=false client=false");
}

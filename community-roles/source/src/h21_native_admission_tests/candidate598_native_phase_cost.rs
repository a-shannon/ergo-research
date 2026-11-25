//! Phase timings for the retained base owner producer at one real and one
//! physical-padding owner. This does not include the final H21 value overlay.
use super::*;
use crate::packed_owner_assembly::{H21EligibleContext, NativePhaseTimings};

#[test]
#[ignore = "retained frame; separately reviewed bounded native phase-cost diagnostic"]
fn c598_native_base_producer_phase_costs() -> Result<(), String> {
    fn phases(t: &NativePhaseTimings) -> [u128; 12] {
        [
            t.allocation_ns,
            t.header_fields_ns,
            t.header_boundary_ns,
            t.header_order_ns,
            t.header_claims_ns,
            t.tree_ns,
            t.pack_initial_ns,
            t.retarget_ns,
            t.bank_claims_ns,
            t.completeness_ns,
            t.pack_final_ns,
            t.total_ns,
        ]
    }

    c574_with_pinned_prefix(|prefix| {
        let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())?;
        let context = H21EligibleContext::new(&plan, prefix)?;
        let producer = context.native_owner_values_producer();
        for owner in [1_000_001, N] {
            // The unprofiled pass warms this same immutable producer/source;
            // the phase sample below times the producer body only.
            let normal = producer.produce(owner)?;
            let (profiled, timing) = producer.produce_profile_for_test(owner)?;
            if normal.packed_bytes() != profiled.packed_bytes()
                || normal.owner() != profiled.owner()
                || normal.class() != profiled.class()
                || normal.owner() != owner
                || normal.packed_bytes().len() != 131_072
            {
                return Err(format!("C598 normal/profiled base row mismatch owner={owner}"));
            }
            let [
                allocation_ns,
                header_fields_ns,
                header_boundary_ns,
                header_order_ns,
                header_claims_ns,
                tree_ns,
                pack_initial_ns,
                retarget_ns,
                bank_claims_ns,
                completeness_ns,
                pack_final_ns,
                total_ns,
            ] = phases(&timing);
            println!("C598_NATIVE_PHASE_OWNER owner={owner} class={:?} bytes=131072 base_only=true normal_profile_byte_equal=true warm_context=true allocation_ns={allocation_ns} header_fields_ns={header_fields_ns} header_boundary_ns={header_boundary_ns} header_order_ns={header_order_ns} header_claims_ns={header_claims_ns} tree_ns={tree_ns} pack_initial_ns={pack_initial_ns} retarget_ns={retarget_ns} bank_claims_ns={bank_claims_ns} completeness_ns={completeness_ns} pack_final_ns={pack_final_ns} total_ns={total_ns}", normal.class());
            std::io::stdout().flush().map_err(|e| e.to_string())?;
        }
        println!("C598_NATIVE_PHASE_PASS owners=2 base_only=true final_h21_overlay=false full_witness=false proof=false pcs=false");
        std::io::stdout().flush().map_err(|e| e.to_string())?;
        Ok(())
    })
}

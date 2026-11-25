//! Per-owner production costs on the retained history, separate from literal
//! checks. This bounded warm-context sample does not measure a full witness.
use super::*;
use crate::{
    h21_scheduled_max_cap::{Eligible08NativeSnapshot, MaxStream, Plan as MaxPlan},
    packed_owner_assembly::{
        h21_structural_roster::{H21StructuralRoster, PublicMapParameters}, H21EligibleContext,
    },
};

#[test]
#[ignore = "retained frame; separately reviewed 8 GiB/180 s native production-cost diagnostic"]
fn c597_native_production_costs_separate_generation_from_literal_checks() -> Result<(), String> {
    c574_with_pinned_prefix(|prefix| {
        let prepare = Instant::now();
        let plan = WorkTreeHistoryPlan::compile(N as u64, H, prefix.root(), prefix.total_be28())?;
        let context = H21EligibleContext::new(&plan, prefix)?;
        let producer = context.native_owner_values_producer();
        let snapshot = Eligible08NativeSnapshot::new(&plan, prefix)?;
        let mut max = MaxStream::new(&plan, prefix, &snapshot)?;
        let calendar = MaxPlan::eligible08().max_calendar();
        if calendar.len() != 7_683 { return Err("C597 MAX calendar census".into()); }
        for (owner, _) in calendar { max.push_native(producer, owner)?; }
        max.closed_native_snapshot(&plan, prefix)?;
        let mut score = context.score_endpoint_stream(&max)?;
        let mut pushes = 0usize;
        while let Some(owner) = score.next_owner() {
            if pushes >= 7_542 { return Err("C597 Score calendar extent".into()); }
            score.push_native(owner)?;
            pushes += 1;
        }
        if pushes != 7_542 || !score.is_closed() {
            return Err("C597 Score calendar census".into());
        }
        score.terminal_r()?;
        let context_max_score_us = prepare.elapsed().as_micros();
        let parameters = crate::bank53_map::CutDescriptor::eligible08().terminals()
            .map(|terminal| PublicMapParameters {
                terminal, exponent: 55,
                lower: LowerSelector {
                    source: LowerSource::HeaderDifficulty { height: 841_729 },
                    branch: LowerBranch::Pivot(54),
                },
            });
        let roster = H21StructuralRoster::from_public(&plan, parameters)?;
        let mut generation_total = 0u128;
        let mut literal_total = 0u128;
        let mut rows = 0usize;
        // Reuse the validated boundary classes and add ordinary legacy/modern
        // owners. This is not a random or frequency-weighted history sample.
        for owner in [
            0, 1_000, 844_672, 844_798, 417_790, 845_758, 845_759, 846_014,
            846_015, 1_000_001, 1_500_001, 1_810_840, 1_810_841, 1_810_904,
            N, (1 << 21) - 1,
        ] {
            let started = Instant::now();
            let row = score.native_owner_values(owner)?;
            let generation_us = started.elapsed().as_micros();
            row.require_context(&context)?;
            if row.packed_bytes().len() != 131_072 || row.owner() != owner {
                return Err("C597 native owner extent/identity".into());
            }
            let started = Instant::now();
            score.check_native_role1_values(&row, &roster)?;
            let literal_us = started.elapsed().as_micros();
            generation_total = generation_total.checked_add(generation_us)
                .ok_or("C597 generation timer overflow")?;
            literal_total = literal_total.checked_add(literal_us)
                .ok_or("C597 literal timer overflow")?;
            rows += 1;
            let census = row.census();
            println!("C597_NATIVE_COST_OWNER owner={owner} bytes=131072 generation_us={generation_us} literal_role1_us={literal_us} literal_role1=true map={:?} score={:?} slack={:?} max={:?} cap={:?}",
                census.map, census.score, census.slack, census.max, census.cap);
            std::io::stdout().flush().map_err(|e| e.to_string())?;
        }
        if rows != 16 { return Err("C597 native cost sample census".into()); }
        println!("C597_NATIVE_COST_PASS sampled_owners=16 context_max_score_us={context_max_score_us} generation_us_total={generation_total} literal_us_total={literal_total} prefix_read_timed=false roster_build_timed=false prefix_passes=1 max_passes=1 score_passes=1 warm_shared_context=true frequency_weighted=false full_witness=false disk_export=false pcs=false proof=false whole_history_throughput=false");
        Ok(())
    })
}

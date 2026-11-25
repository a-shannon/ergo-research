//! Simultaneous custody through the actual native source APIs.

use super::*;
use crate::h21_scheduled_max_cap::{Eligible08NativeSnapshot, MaxStream, Plan as MaxPlan};
use crate::packed_owner_assembly::H21EligibleContext;

// This helper owns no test, frame reader, native marker or claim. Only the
// distinct C494 ignored selector may call it after authenticating its frame.
// Infer the private Score stream type through its production constructor.
#[allow(dead_code)]
pub(super) fn c494_combined_owner0_score_compile_only<'src>(
    plan: &'src WorkTreeHistoryPlan,
    prefix: &'src NativePrefix,
    context: &H21EligibleContext<'src>,
) -> Result<(), String> {
    const GENESIS_OWNER: usize = 0;
    const SCORE_OWNER: usize = 845_887;

    validate_native_plan_input(plan, prefix)?;
    let producer = NativeOwnerProducer::new_for_history(plan, prefix)?;
    let genesis_binding = HeaderSourceBinding::for_plan(plan, GENESIS_OWNER)?;
    let score_binding = HeaderSourceBinding::for_plan(plan, SCORE_OWNER)?;
    let cut = crate::bank53_map::CutDescriptor::eligible08().canonical_identity();

    // Each full binding has its own owner. matches_sink checks the common
    // root, total, profile, cut and fixed layout without equating owner fields.
    for (binding, owner) in [(&genesis_binding, GENESIS_OWNER), (&score_binding, SCORE_OWNER)] {
        if !binding.matches_sink(prefix.root(), prefix.total_be28(), prefix.profile(), &cut, owner) {
            return Err("C494 common parent/profile/cut/layout binding".into());
        }
    }

    let genesis_bundle = context.map_pair_slack_bundle(GENESIS_OWNER)?;
    if genesis_bundle.map_lease().binding() != &genesis_binding {
        return Err("C494 owner0 exact Map+Slack binding".into());
    }
    let retained_genesis = producer.produce_genesis_header_zero_with_map_slack_bundle(
        GENESIS_OWNER, &genesis_bundle,
    )?;

    // Construct the same native MAX/Score chain used by the existing C390
    // path. No fixture values or preconstructed owner relation enter here.
    let snapshot = Eligible08NativeSnapshot::new(plan, prefix)?;
    let mut closed_max = MaxStream::new(plan, prefix, &snapshot)?;
    let max_calendar = MaxPlan::eligible08().max_calendar();
    if max_calendar.len() != 7_683 || closed_max.remaining_owners() != max_calendar.len() {
        return Err("C494 MAX source calendar census".into());
    }
    for (owner, _) in max_calendar {
        closed_max.push_native(&producer, owner)?;
    }
    closed_max.closed_native_snapshot(plan, prefix)?;

    let mut closed_score = context.score_endpoint_stream(&closed_max)?;
    let mut appended = 0usize;
    while let Some(owner) = closed_score.next_owner() {
        if appended >= 7_542 {
            return Err("C494 Score source calendar bound".into());
        }
        closed_score.push_native(owner)?;
        appended += 1;
    }
    if appended != 7_542 || !closed_score.is_closed() || closed_score.remaining_owners() != 0 {
        return Err("C494 terminal Score source closure".into());
    }
    closed_score.terminal_r()?;
    let relation = closed_score.closed_owner_relation(SCORE_OWNER)?;
    if relation.owner() != SCORE_OWNER || relation.parent_root() != prefix.root()
        || relation.parent_total() != prefix.total_be28()
        || relation.parent_profile() != prefix.profile() || relation.cut_identity() != cut
    {
        return Err("C494 terminal Score common parent identity".into());
    }

    // This wrapper joins the terminal-closed relation to MAX, constructs the
    // checked packing view, installs the partial, ends its borrow and moves
    // that same view into the private retained carrier.
    let retained_partial = context.stage_c492_partial_score_slack(
        SCORE_OWNER, relation, &closed_max, &score_binding,
    )?;
    let summary = retained_partial.checked_installed_summary(&score_binding, SCORE_OWNER)?;
    if (summary.terms, summary.row_leases, summary.assignments, summary.reservations,
        summary.score_reads) != (17_864, 7_516, 4_870, 4_870, 1_028)
    {
        return Err("C494 checked installed partial census".into());
    }
    retained_genesis.validate_for(&genesis_binding, &genesis_bundle)?;
    retained_partial.checked_installed_summary(&score_binding, SCORE_OWNER)?;
    Ok(())
}

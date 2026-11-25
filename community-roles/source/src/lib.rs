#![cfg_attr(not(test), allow(dead_code))]
pub(crate) mod h21_snapshot;
#[cfg(test)]
pub(crate) mod preview_test_paths;
pub mod circuit;
pub mod gkr;
pub mod history_join;
pub mod header_hash;
pub mod segment_relation;
pub mod segment_adjacency;
pub mod point_membership;
mod point_role;
pub mod segment_points;
pub mod header_order;
pub mod header_compact_links;
pub mod pcs;
pub mod packed;
mod packed_rows;
pub mod opening_batch;
pub mod sparse;
pub mod sparse_stream;
pub mod sparse_stream_boolean;
#[cfg(test)]
pub(crate) mod sparse_stream_terms;
pub(crate) mod sparse_stream_roster;
pub mod serializer;
pub(crate) mod serializer_field_projection;
pub mod transcript;
pub mod wiring;
pub mod verifier_key;
#[cfg(test)]
pub(crate) mod c425_span_census;
pub mod daa_integer;
pub mod daa_count;
pub mod work_tree_layout;
pub mod work_tree_wiring;
pub mod daa_regression;
pub mod work_tree_fixed_hash;
pub mod work_tree_leaf_hash;
pub mod work_tree_work;
pub mod work_tree_composition;
pub mod daa_finish;
pub(crate) mod daa_one_ratio_finish;
#[cfg(test)]
mod daa_one_ratio_finish_tests;
pub(crate) mod mapped_one_daa;
pub(crate) mod one_daa_layout;
#[cfg(test)]
mod one_daa_layout_tests;
mod daa_header_window;
mod daa_schedule_wiring;
mod daa_serializer_join;
mod daa_serializer_packet;
mod daa_two_ratio_join;
mod daa_two_ratio_packet;
mod daa_short_legacy_join;
mod daa_short_legacy_packet;
mod four_header_link_join;
mod four_header_link_packet;
mod mapped_daa_plan;
mod short_daa_layout;
mod short_header_history_boundary;
mod short_common_owner;
mod selected_header_auth;
#[cfg(test)]
mod selected_header_auth_tests;
#[cfg(test)]
mod selected_header_auth_proof_tests;
#[cfg(test)]
mod selected_header_auth_replay_tests;
#[cfg(test)]
mod short_common_owner_tests;
#[cfg(test)]
mod short_common_owner_fixture_tests;
#[cfg(test)]
mod short_daa_layout_tests;
mod daa_history_layout;
mod daa_history_roster;
mod daa_history_producer;
#[cfg(test)]
mod daa_history_producer_tests;
#[cfg(test)]
pub(crate) mod q9_selected_raw_fixture;
mod packed_owner_assembly;
mod h21_work_local_source;
mod max_header_adapter;
mod schedule_anchor_allocator;
mod suffix_max;
mod native_owner_exports;
#[cfg(test)]
mod packed_owner_assembly_tests;
#[cfg(test)]
mod native_w_loan;
#[cfg(test)]
mod native_v_max_cap_loan;
#[cfg(test)]
mod daa_history_roster_tests;
#[cfg(test)]
mod daa_mature_admission_tests;
mod header_height_layout;
mod header_adjacency_layout;
mod header_metadata_order_layout;
#[cfg(test)]
mod daa_alias_stream_tests;
#[cfg(not(test))]
mod header_history_boundary;
#[cfg(test)]
pub(crate) mod header_history_boundary;
#[cfg(test)]
mod header_history_stream_join_tests;
pub mod dyadic_edge_join;
pub mod h3_parent_root;
pub mod h4_packet;
mod h4_analytic;
pub mod nph2_header_source;
mod core_pool;
mod core_pool_boolean;
mod work_tree_history_plan;
mod retained_header_pairs;
mod daa_work_actions;
mod native_work_relation;
mod global_producer_endpoint_plan;
mod native_work_opening;
mod native_autolykos_pow;
mod numeric_daa_authenticated;
#[cfg(test)]
mod historical_prefix_witness;
#[cfg(test)]
mod historical_prefix_public;
#[cfg(test)]
mod historical_prefix_checks;
mod historical_prefix_height_work;
mod checkpoint_output_layout;
mod checkpoint_role4_internal;
mod prefix_difficulty_context_layout;
#[cfg(test)]
mod historical_prefix_proof;
#[cfg(test)]
mod historical_prefix_max_proof;
#[cfg(test)]
mod core_pool_join_tests;
#[cfg(test)]
mod core_bank_projection_tests;
#[cfg(test)]
mod envelope_fragment;
#[cfg(test)]
mod envelope_fragment_tests;
mod legacy_envelope_map;
#[cfg(test)]
mod legacy_envelope_map_tests;
#[cfg(test)]
mod global_u_filtered_relation_tests;
#[cfg(test)]
mod legacy_native_adapter;
#[cfg(test)]
mod legacy_composition;
#[cfg(test)]
mod legacy_composition_tests;

#[cfg(test)]
mod native_adjacency_stream;

#[cfg(test)]
mod certified_legacy_bound;
#[cfg(test)]
mod certified_legacy_bound_native;

mod certified_modern_cap;
#[cfg(test)]
mod certified_modern_cap_native;

mod origin_score;
#[cfg(test)]
mod origin_score_map;
mod bank53_map;
mod bank53_slack;
mod bank53_required_writer;
#[cfg(test)]
mod bank53_map_score;
#[cfg(test)]
mod origin_score_tests;

#[cfg(test)]
mod envelope_cover;
mod global_u_roster;
#[cfg(test)]
mod global_u_roster_tests;
#[cfg(test)]
mod global_u_h21_differential_tests;
#[cfg(test)]
mod h21_native_admission_tests;
#[cfg(test)]
mod envelope_score_join;
#[cfg(test)]
mod envelope_score_join_tests;

#[cfg(test)]
mod implicit_witness;
#[cfg(test)]
mod implicit_witness_tests;

#[cfg(test)]
mod ratio_contraction;
#[cfg(test)]
mod ratio_contraction_tests;

#[cfg(test)]
mod ratio_import_contraction;
#[cfg(test)]
mod ratio_import_contraction_tests;

#[cfg(test)]
mod ratio_packet_contraction;
#[cfg(test)]
mod ratio_packet_contraction_tests;

#[cfg(test)]
mod certified_modern_suffix;
#[cfg(test)]
mod certified_modern_suffix_tests;

#[cfg(test)]
mod projection_aux_retirement;
#[cfg(test)]
mod projection_aux_retirement_tests;

#[cfg(test)]
mod one_header_gkr_pcs;
#[cfg(test)]
mod one_header_gkr_pcs_tests;

#[cfg(test)]
mod one_header_packed_pcs_tests;

#[cfg(test)]
mod packed_gkr_window;
#[cfg(test)]
mod packed_gkr_window_tests;

#[cfg(test)]
mod packed_gkr_role1;

#[cfg(test)]
mod compact_compression;
#[cfg(test)]
mod compact_compression_tests;

#[cfg(test)]
mod high_phase_spool;

#[cfg(test)]
mod native_prefix_auth_plan;
#[cfg(test)]
mod native_prefix_auth_plan_tests;

#[cfg(test)]
mod native_role4_join;

#[cfg(test)]
mod sparse_log41_full_opening_tests;

#[cfg(test)]
mod bounded_cap_coeff;

#[cfg(test)]
mod score_cap_v_alias;

mod h21_scheduled_max_cap;

mod header_scheduled_retirement;

mod h21_scheduled_family_ledger;

mod header_daa_row_placement;

#[cfg(test)]
mod x_lease_diagnostic;

#[cfg(test)]
mod h21_row_support;

#[cfg(test)]
mod score_window_join;

#[cfg(test)]
mod score_prefix_r_anchor;

#[cfg(test)]
mod native_map_cut_source;

#[cfg(test)]
mod selected_raw_map_source;

#[cfg(test)]
mod q9_common_join;

#[cfg(test)]
mod h21_tagged_census;

#[cfg(test)]
mod h21_local_merged_ledger;

#[cfg(test)]
mod c146_phase1_session;

#[cfg(test)]
mod c244_shift_tuple_probe;

#[cfg(test)]
mod h21_shift_callback_falsifier_tests;

#[cfg(test)]
mod h21_full_shift_attachment_tests;

#[cfg(test)]
mod h21_two_owner_cut16_differential_tests;

#[cfg(test)]
mod h21_filebacked_cut16_differential_tests;

#[cfg(test)]
mod h21_role1_support_census_tests;

#[cfg(test)]
mod h21_booleanity_ab_join_tests;

pub use numeric_daa_authenticated::{
    verify_internal_four_claim_case, ColdCaseError, ColdCaseVerification,
};

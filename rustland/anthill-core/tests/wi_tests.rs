//! Consolidated per-WI validation tests (WI-244). One submodule per historical wi### test file.

mod common;

#[path = "include/wi009_phase3_builtins_test.rs"]
mod wi009_phase3_builtins_test;

#[path = "include/wi275_hof_inference_test.rs"]
mod wi275_hof_inference_test;

#[path = "include/wi279_dot_dispatch_test.rs"]
mod wi279_dot_dispatch_test;

#[path = "include/wi281_spec_dot_dispatch_test.rs"]
mod wi281_spec_dot_dispatch_test;

#[path = "include/wi343_provider_requires_test.rs"]
mod wi343_provider_requires_test;

#[path = "include/wi363_provider_operations_test.rs"]
mod wi363_provider_operations_test;

#[path = "include/wi365_abstract_self_typing_test.rs"]
mod wi365_abstract_self_typing_test;

#[path = "include/wi345_warnings_channel_test.rs"]
mod wi345_warnings_channel_test;

#[path = "include/wi346_requires_shadow_test.rs"]
mod wi346_requires_shadow_test;

#[path = "include/wi347_override_refinement_test.rs"]
mod wi347_override_refinement_test;

#[path = "include/wi246_rule_body_desc_test.rs"]
mod wi246_rule_body_desc_test;

#[path = "include/wi304_native_op_body_occ_test.rs"]
mod wi304_native_op_body_occ_test;

#[path = "include/wi071_positional_sort_binding_test.rs"]
mod wi071_positional_sort_binding_test;

#[path = "include/wi182_fresh_var_test.rs"]
mod wi182_fresh_var_test;

#[path = "include/kb_query_test.rs"]
mod kb_query_test;

#[path = "include/wi186_free_standing_parametric_test.rs"]
mod wi186_free_standing_parametric_test;

#[path = "include/wi202_retrieve_test.rs"]
mod wi202_retrieve_test;

#[path = "include/wi204_smoke_test.rs"]
mod wi204_smoke_test;

#[path = "include/wi204_let_ctor_env_test.rs"]
mod wi204_let_ctor_env_test;

#[path = "include/wi204_sort_param_test.rs"]
mod wi204_sort_param_test;

#[path = "include/wi205_cell_test.rs"]
mod wi205_cell_test;

#[path = "include/wi210_dispatch_test.rs"]
mod wi210_dispatch_test;

#[path = "include/wi211_typing_test.rs"]
mod wi211_typing_test;

#[path = "include/wi218_static_dispatch_test.rs"]
mod wi218_static_dispatch_test;

#[path = "include/wi219_modify_transitivity_test.rs"]
mod wi219_modify_transitivity_test;

#[path = "include/wi221_defer_to_requirement_test.rs"]
mod wi221_defer_to_requirement_test;

#[path = "include/wi222_defer_rewrite_test.rs"]
mod wi222_defer_rewrite_test;

#[path = "include/wi223_apply_within_test.rs"]
mod wi223_apply_within_test;

#[path = "include/wi223_closure_requirements_test.rs"]
mod wi223_closure_requirements_test;

#[path = "include/wi223_requirement_value_forms_test.rs"]
mod wi223_requirement_value_forms_test;

#[path = "include/wi224_sld_resolution_test.rs"]
mod wi224_sld_resolution_test;

#[path = "include/wi226_caches_and_binding_test.rs"]
mod wi226_caches_and_binding_test;

#[path = "include/wi227_projection_search_test.rs"]
mod wi227_projection_search_test;

#[path = "include/wi228_tree_threaded_dispatch_test.rs"]
mod wi228_tree_threaded_dispatch_test;

#[path = "include/wi230_requires_tree_test.rs"]
mod wi230_requires_tree_test;

#[path = "include/wi231_req_insertion_pass_test.rs"]
mod wi231_req_insertion_pass_test;

#[path = "include/wi236_call_with_requirements_test.rs"]
mod wi236_call_with_requirements_test;

#[path = "include/wi237_diag_test.rs"]
mod wi237_diag_test;

#[path = "include/wi260_term_as_entity_test.rs"]
mod wi260_term_as_entity_test;

#[path = "include/wi261_result_in_effects_test.rs"]
mod wi261_result_in_effects_test;

#[path = "include/wi270_expected_type_test.rs"]
mod wi270_expected_type_test;

#[path = "include/wi272_op_type_args_frame_test.rs"]
mod wi272_op_type_args_frame_test;

#[path = "include/wi284_min_sort_test.rs"]
mod wi284_min_sort_test;

#[path = "include/wi285_unrec_test.rs"]
mod wi285_unrec_test;

#[path = "include/wi283_typeresult_node_test.rs"]
mod wi283_typeresult_node_test;

#[path = "include/wi283_typer_firing_test.rs"]
mod wi283_typer_firing_test;

#[path = "include/wi283_type_directed_guard_test.rs"]
mod wi283_type_directed_guard_test;

#[path = "include/match_branch_join_test.rs"]
mod match_branch_join_test;

#[path = "include/if_branch_join_test.rs"]
mod if_branch_join_test;

#[path = "include/wi314_region_mask_test.rs"]
mod wi314_region_mask_test;

#[path = "include/wi320_bridge_fact_test.rs"]
mod wi320_bridge_fact_test;

#[path = "include/wi325_missing_requires_test.rs"]
mod wi325_missing_requires_test;

#[path = "include/wi351_callback_place_test.rs"]
mod wi351_callback_place_test;

#[path = "include/wi352_flow_derive_test.rs"]
mod wi352_flow_derive_test;

#[path = "include/wi341_callback_modify_test.rs"]
mod wi341_callback_modify_test;
#[path = "include/wi357_element_typing_test.rs"]
mod wi357_element_typing_test;

#[path = "include/wi365_effect_grounding_test.rs"]
mod wi365_effect_grounding_test;

#[path = "include/wi413_effect_self_recursion_test.rs"]
mod wi413_effect_self_recursion_test;

#[path = "include/wi375_effect_row_surface_test.rs"]
mod wi375_effect_row_surface_test;

#[path = "include/wi377_effect_row_absent_fold_test.rs"]
mod wi377_effect_row_absent_fold_test;

#[path = "include/wi366_value_in_type_facts_test.rs"]
mod wi366_value_in_type_facts_test;

#[path = "include/wi348_operation_info_queryable_test.rs"]
mod wi348_operation_info_queryable_test;

#[path = "include/wi087_operation_meta_test.rs"]
mod wi087_operation_meta_test;

#[path = "include/wi379_inference_order_test.rs"]
mod wi379_inference_order_test;

#[path = "include/wi368_iterator_threading_test.rs"]
mod wi368_iterator_threading_test;

#[path = "include/wi376_projection_test.rs"]
mod wi376_projection_test;

#[path = "include/wi397_compound_projection_test.rs"]
mod wi397_compound_projection_test;

#[path = "include/wi398_cross_param_projection_test.rs"]
mod wi398_cross_param_projection_test;

#[path = "include/wi399_let_projection_test.rs"]
mod wi399_let_projection_test;

#[path = "include/wi400_body_projection_test.rs"]
mod wi400_body_projection_test;

#[path = "include/wi427_bidirectional_flow_test.rs"]
mod wi427_bidirectional_flow_test;

#[path = "include/wi392_op_type_param_rigid_test.rs"]
mod wi392_op_type_param_rigid_test;

#[path = "include/wi385_arg_field_validation_test.rs"]
mod wi385_arg_field_validation_test;

#[path = "include/wi381_alias_resolution_test.rs"]
mod wi381_alias_resolution_test;

#[path = "include/wi407_provider_edges_test.rs"]
mod wi407_provider_edges_test;

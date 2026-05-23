//! Consolidated per-WI validation tests (WI-244). One submodule per historical wi### test file.

mod common;

#[path = "include/wi009_phase3_builtins_test.rs"]
mod wi009_phase3_builtins_test;

#[path = "include/wi071_positional_sort_binding_test.rs"]
mod wi071_positional_sort_binding_test;

#[path = "include/wi182_fresh_var_test.rs"]
mod wi182_fresh_var_test;

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

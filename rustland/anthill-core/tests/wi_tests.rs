//! Consolidated per-WI validation tests (WI-244). One submodule per historical wi### test file.

mod common;

#[path = "include/tuple_order_test.rs"]
mod tuple_order_test;

#[path = "include/wi638_named_tuple_field_test.rs"]
mod wi638_named_tuple_field_test;

#[path = "include/wi639_distributive_projection_test.rs"]
mod wi639_distributive_projection_test;

#[path = "include/wi009_phase3_builtins_test.rs"]
mod wi009_phase3_builtins_test;

#[path = "include/wi206_is_modifiable_test.rs"]
mod wi206_is_modifiable_test;

#[path = "include/wi707_type_application_value_test.rs"]
mod wi707_type_application_value_test;

#[path = "include/wi709_type_arg_validation_test.rs"]
mod wi709_type_arg_validation_test;

#[path = "include/wi710_rule_body_type_arg_test.rs"]
mod wi710_rule_body_type_arg_test;

#[path = "include/wi708_body_type_arg_read_test.rs"]
mod wi708_body_type_arg_read_test;

#[path = "include/wi716_optional_fact_none_fill_test.rs"]
mod wi716_optional_fact_none_fill_test;

#[path = "include/wi718_prelude_ctor_preregistration_test.rs"]
mod wi718_prelude_ctor_preregistration_test;

#[path = "include/wi714_relation_materialize_test.rs"]
mod wi714_relation_materialize_test;

#[path = "include/wi714_relation_reference_test.rs"]
mod wi714_relation_reference_test;

#[path = "include/wi714_where_test.rs"]
mod wi714_where_test;

#[path = "include/wi714_join_test.rs"]
mod wi714_join_test;

#[path = "include/wi730_boolean_condition_test.rs"]
mod wi730_boolean_condition_test;

#[path = "include/wi714_project_test.rs"]
mod wi714_project_test;

#[path = "include/wi714_drain_test.rs"]
mod wi714_drain_test;

#[path = "include/wi714_recursive_relation_test.rs"]
mod wi714_recursive_relation_test;

#[path = "include/wi738_operand_call_delay_test.rs"]
mod wi738_operand_call_delay_test;

#[path = "include/wi737_floundered_relation_test.rs"]
mod wi737_floundered_relation_test;

#[path = "include/wi739_guard_generator_delay_test.rs"]
mod wi739_guard_generator_delay_test;

#[path = "include/wi727_fix_test.rs"]
mod wi727_fix_test;

#[path = "include/wi734_abstract_operand_test.rs"]
mod wi734_abstract_operand_test;

#[path = "include/wi725_self_carried_spec_simp_test.rs"]
mod wi725_self_carried_spec_simp_test;

#[path = "include/wi723_row_lambda_binder_test.rs"]
mod wi723_row_lambda_binder_test;

#[path = "include/wi724_eq_int64_coherence_test.rs"]
mod wi724_eq_int64_coherence_test;

#[path = "include/wi023_quantified_constraint_test.rs"]
mod wi023_quantified_constraint_test;

#[path = "include/wi525_naf_allowedness_test.rs"]
mod wi525_naf_allowedness_test;

#[path = "include/wi526_equational_migration_test.rs"]
mod wi526_equational_migration_test;

#[path = "include/wi519_residual_honesty_test.rs"]
mod wi519_residual_honesty_test;

#[path = "include/wi419_same_spec_requires_test.rs"]
mod wi419_same_spec_requires_test;

#[path = "include/wi613_same_spec_direct_dispatch_test.rs"]
mod wi613_same_spec_direct_dispatch_test;

#[path = "include/wi275_hof_inference_test.rs"]
mod wi275_hof_inference_test;

#[path = "include/wi278_dot_chain_test.rs"]
mod wi278_dot_chain_test;

#[path = "include/wi492_transitive_provision_test.rs"]
mod wi492_transitive_provision_test;

#[path = "include/wi491_covariant_return_test.rs"]
mod wi491_covariant_return_test;

#[path = "include/wi173_type_print_test.rs"]
mod wi173_type_print_test;

#[path = "include/wi493_effect_row_tolerance_test.rs"]
mod wi493_effect_row_tolerance_test;

#[path = "include/wi495_non_stream_iterable_test.rs"]
mod wi495_non_stream_iterable_test;

#[path = "include/wi496_transitive_iterator_test.rs"]
mod wi496_transitive_iterator_test;

#[path = "include/wi364_mutable_stack_test.rs"]
mod wi364_mutable_stack_test;

#[path = "include/wi507_carrier_only_dispatch_test.rs"]
mod wi507_carrier_only_dispatch_test;

#[path = "include/wi508_nullary_carrier_dispatch_test.rs"]
mod wi508_nullary_carrier_dispatch_test;

#[path = "include/wi506_modify_field_coverage_test.rs"]
mod wi506_modify_field_coverage_test;

#[path = "include/wi279_dot_dispatch_test.rs"]
mod wi279_dot_dispatch_test;

#[path = "include/wi281_spec_dot_dispatch_test.rs"]
mod wi281_spec_dot_dispatch_test;

#[path = "include/wi282_rule_body_dot_test.rs"]
mod wi282_rule_body_dot_test;

#[path = "include/wi603_rule_body_var_typing_test.rs"]
mod wi603_rule_body_var_typing_test;

#[path = "include/wi487_op_body_param_symbol_test.rs"]
mod wi487_op_body_param_symbol_test;

#[path = "include/wi523_unify_test.rs"]
mod wi523_unify_test;

#[path = "include/wi483_rule_body_method_eval_test.rs"]
mod wi483_rule_body_method_eval_test;

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

#[path = "include/wi531_solution_residual_test.rs"]
mod wi531_solution_residual_test;

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

#[path = "include/wi066_division_effect_test.rs"]
mod wi066_division_effect_test;

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

#[path = "include/wi578_typed_value_test.rs"]
mod wi578_typed_value_test;

#[path = "include/wi285_unrec_test.rs"]
mod wi285_unrec_test;

#[path = "include/wi283_typeresult_node_test.rs"]
mod wi283_typeresult_node_test;

#[path = "include/wi283_typer_firing_test.rs"]
mod wi283_typer_firing_test;

#[path = "include/wi283_type_directed_guard_test.rs"]
mod wi283_type_directed_guard_test;

#[path = "include/wi596_container_guard_test.rs"]
mod wi596_container_guard_test;

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

#[path = "include/wi642_rule_body_requires_test.rs"]
mod wi642_rule_body_requires_test;

#[path = "include/wi645_float_nan_ieee_test.rs"]
mod wi645_float_nan_ieee_test;

#[path = "include/wi658_eq_noneq_exclusive_test.rs"]
mod wi658_eq_noneq_exclusive_test;

#[path = "include/wi664_composite_eq_test.rs"]
mod wi664_composite_eq_test;

#[path = "include/wi644_use_site_requires_test.rs"]
mod wi644_use_site_requires_test;

#[path = "include/wi625_eval_semantic_eq_test.rs"]
mod wi625_eval_semantic_eq_test;

#[path = "include/wi625_sld_eval_bridge_test.rs"]
mod wi625_sld_eval_bridge_test;

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

#[path = "include/wi478_guarded_effect_test.rs"]
mod wi478_guarded_effect_test;

#[path = "include/wi067_guard_discharge_test.rs"]
mod wi067_guard_discharge_test;

#[path = "include/wi592_constructor_arg_discharge_test.rs"]
mod wi592_constructor_arg_discharge_test;

#[path = "include/wi573_eq_override_discharge_test.rs"]
mod wi573_eq_override_discharge_test;

#[path = "include/wi539_call_site_contracts_test.rs"]
mod wi539_call_site_contracts_test;

#[path = "include/wi557_rule_body_precondition_scope_test.rs"]
mod wi557_rule_body_precondition_scope_test;

#[path = "include/wi622_rule_body_dot_obligations_test.rs"]
mod wi622_rule_body_dot_obligations_test;

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

#[path = "include/wi485_find_dot_call_test.rs"]
mod wi485_find_dot_call_test;

#[path = "include/wi397_compound_projection_test.rs"]
mod wi397_compound_projection_test;

#[path = "include/wi398_cross_param_projection_test.rs"]
mod wi398_cross_param_projection_test;

#[path = "include/wi425_dotapply_view_isomorphism_test.rs"]
mod wi425_dotapply_view_isomorphism_test;

#[path = "include/wi429_unresolved_type_name_test.rs"]
mod wi429_unresolved_type_name_test;

#[path = "include/wi399_let_projection_test.rs"]
mod wi399_let_projection_test;

#[path = "include/wi400_body_projection_test.rs"]
mod wi400_body_projection_test;

#[path = "include/wi401_escape_free_return_test.rs"]
mod wi401_escape_free_return_test;

#[path = "include/wi402_manifest_provider_test.rs"]
mod wi402_manifest_provider_test;

#[path = "include/wi402_existential_return_test.rs"]
mod wi402_existential_return_test;

#[path = "include/wi405_uniform_subtype_test.rs"]
mod wi405_uniform_subtype_test;

#[path = "include/wi428_rigid_projection_test.rs"]
mod wi428_rigid_projection_test;

#[path = "include/wi430_carrier_precise_projection_test.rs"]
mod wi430_carrier_precise_projection_test;

#[path = "include/wi391_binding_extractability_test.rs"]
mod wi391_binding_extractability_test;

#[path = "include/wi383_op_type_param_projection_test.rs"]
mod wi383_op_type_param_projection_test;

#[path = "include/wi383_hk_application_test.rs"]
mod wi383_hk_application_test;

#[path = "include/wi427_bidirectional_flow_test.rs"]
mod wi427_bidirectional_flow_test;

#[path = "include/wi392_op_type_param_rigid_test.rs"]
mod wi392_op_type_param_rigid_test;

#[path = "include/wi385_arg_field_validation_test.rs"]
mod wi385_arg_field_validation_test;

#[path = "include/wi510_typeerror_origin_test.rs"]
mod wi510_typeerror_origin_test;

#[path = "include/wi381_alias_resolution_test.rs"]
mod wi381_alias_resolution_test;

#[path = "include/wi407_provider_edges_test.rs"]
mod wi407_provider_edges_test;

#[path = "include/wi431_instance_fact_coverage_test.rs"]
mod wi431_instance_fact_coverage_test;

#[path = "include/wi450_witness_dispatch_test.rs"]
mod wi450_witness_dispatch_test;

#[path = "include/wi451_sort_type_param_binders_test.rs"]
mod wi451_sort_type_param_binders_test;

#[path = "include/wi452_marked_param_backing_var_test.rs"]
mod wi452_marked_param_backing_var_test;

#[path = "include/wi453_hk_concrete_fill_test.rs"]
mod wi453_hk_concrete_fill_test;

#[path = "include/wi454_per_statement_binders_test.rs"]
mod wi454_per_statement_binders_test;

#[path = "include/wi457_join_escape_gate_test.rs"]
mod wi457_join_escape_gate_test;

#[path = "include/wi480_destructure_escape_gate_test.rs"]
mod wi480_destructure_escape_gate_test;

#[path = "include/wi488_producer_component_escape_test.rs"]
mod wi488_producer_component_escape_test;

#[path = "include/wi424_iterable_members_test.rs"]
mod wi424_iterable_members_test;

#[path = "include/wi439_iterable_filter_test.rs"]
mod wi439_iterable_filter_test;

#[path = "include/wi440_callback_lacks_test.rs"]
mod wi440_callback_lacks_test;

#[path = "include/wi441_iterable_arrow_pred_test.rs"]
mod wi441_iterable_arrow_pred_test;
#[path = "include/wi443_identifier_dot_call_test.rs"]
mod wi443_identifier_dot_call_test;

#[path = "include/wi280_dot_field_test.rs"]
mod wi280_dot_field_test;

#[path = "include/wi262_type_level_projection_test.rs"]
mod wi262_type_level_projection_test;

#[path = "include/wi408_some_coercion_test.rs"]
mod wi408_some_coercion_test;

#[path = "include/wi445_named_subpattern_test.rs"]
mod wi445_named_subpattern_test;

#[path = "include/wi374_expansion_test.rs"]
mod wi374_expansion_test;

#[path = "include/wi448_comment_before_op_requires_test.rs"]
mod wi448_comment_before_op_requires_test;

#[path = "include/wi459_projection_delta_recursion_test.rs"]
mod wi459_projection_delta_recursion_test;

#[path = "include/wi461_self_receiver_provider_test.rs"]
mod wi461_self_receiver_provider_test;

#[path = "include/wi462_tuple_literal_threading_test.rs"]
mod wi462_tuple_literal_threading_test;

#[path = "include/wi463_unqualified_witness_dispatch_test.rs"]
mod wi463_unqualified_witness_dispatch_test;

#[path = "include/wi476_scope_chain_test.rs"]
mod wi476_scope_chain_test;

#[path = "include/wi040_reserved_vocab_test.rs"]
mod wi040_reserved_vocab_test;

#[path = "include/wi521_prelude_test.rs"]
mod wi521_prelude_test;

#[path = "include/wi466_swapped_nominal_subtype_test.rs"]
mod wi466_swapped_nominal_subtype_test;

#[path = "include/wi469_callback_arg_validation_test.rs"]
mod wi469_callback_arg_validation_test;

#[path = "include/wi474_dispatched_projection_test.rs"]
mod wi474_dispatched_projection_test;

#[path = "include/wi475_effects_projection_test.rs"]
mod wi475_effects_projection_test;

#[path = "include/wi201_bare_spec_member_sugar_test.rs"]
mod wi201_bare_spec_member_sugar_test;

#[path = "include/wi481_modify_row_equality_test.rs"]
mod wi481_modify_row_equality_test;

#[path = "include/wi404_denoted_self_conformance_test.rs"]
mod wi404_denoted_self_conformance_test;

#[path = "include/wi411_unqualified_spec_op_dispatch_test.rs"]
mod wi411_unqualified_spec_op_dispatch_test;

#[path = "include/wi426_named_arg_op_call_test.rs"]
mod wi426_named_arg_op_call_test;

#[path = "include/wi433_positional_ctor_desugar_test.rs"]
mod wi433_positional_ctor_desugar_test;

#[path = "include/wi499_forward_ref_ctor_test.rs"]
mod wi499_forward_ref_ctor_test;

#[path = "include/wi500_runtime_positional_ctor_test.rs"]
mod wi500_runtime_positional_ctor_test;

#[path = "include/wi321_cross_file_mutual_recursion_test.rs"]
mod wi321_cross_file_mutual_recursion_test;

#[path = "include/wi369_internal_visibility_test.rs"]
mod wi369_internal_visibility_test;

#[path = "include/wi516_graded_effect_row_test.rs"]
mod wi516_graded_effect_row_test;

#[path = "include/wi517_typed_lambda_binder_test.rs"]
mod wi517_typed_lambda_binder_test;

#[path = "include/wi529_boolean_operator_split_test.rs"]
mod wi529_boolean_operator_split_test;

#[path = "include/wi077_long_stream_stress_test.rs"]
mod wi077_long_stream_stress_test;

#[path = "include/wi084_const_phase1_test.rs"]
mod wi084_const_phase1_test;

#[path = "include/wi084_const_phase2_test.rs"]
mod wi084_const_phase2_test;

#[path = "include/wi084_const_phase3_test.rs"]
mod wi084_const_phase3_test;

#[path = "include/wi084_const_purity_test.rs"]
mod wi084_const_purity_test;

#[path = "include/wi532_float_infinity_test.rs"]
mod wi532_float_infinity_test;

#[path = "include/wi562_indexed_seq_nth_dispatch_test.rs"]
mod wi562_indexed_seq_nth_dispatch_test;

#[path = "include/wi585_finite_collection_test.rs"]
mod wi585_finite_collection_test;

#[path = "include/wi594_finite_map_effect_threading_test.rs"]
mod wi594_finite_map_effect_threading_test;

#[path = "include/wi582_typed_rule_pattern_test.rs"]
mod wi582_typed_rule_pattern_test;

#[path = "include/wi588_finite_combinators_test.rs"]
mod wi588_finite_combinators_test;

#[path = "include/wi598_finite_collect_dispatch_test.rs"]
mod wi598_finite_collect_dispatch_test;

#[path = "include/wi599_carrier_arg_provision_test.rs"]
mod wi599_carrier_arg_provision_test;

#[path = "include/wi601_abstract_spec_self_receiver_test.rs"]
mod wi601_abstract_spec_self_receiver_test;

#[path = "include/wi604_iterable_consumer_effect_grounding_test.rs"]
mod wi604_iterable_consumer_effect_grounding_test;

#[path = "include/wi608_iterator_over_finite_collection_test.rs"]
mod wi608_iterator_over_finite_collection_test;

#[path = "include/wi609_collect_effect_over_finite_collection_test.rs"]
mod wi609_collect_effect_over_finite_collection_test;

#[path = "include/wi612_abstract_stream_consumer_effect_test.rs"]
mod wi612_abstract_stream_consumer_effect_test;

#[path = "include/wi614_requires_dot_dispatch_test.rs"]
mod wi614_requires_dot_dispatch_test;

#[path = "include/wi590_witness_param_carrier_test.rs"]
mod wi590_witness_param_carrier_test;

#[path = "include/wi605_bare_arrow_lambda_test.rs"]
mod wi605_bare_arrow_lambda_test;

#[path = "include/wi606_unqualified_dispatch_return_threading_test.rs"]
mod wi606_unqualified_dispatch_return_threading_test;

#[path = "include/wi618_bare_arrow_logic_test.rs"]
mod wi618_bare_arrow_logic_test;

#[path = "include/wi620_paren_lambda_param_test.rs"]
mod wi620_paren_lambda_param_test;

#[path = "include/wi619_two_ary_head_introducer_test.rs"]
mod wi619_two_ary_head_introducer_test;

#[path = "include/wi515_entity_schema_fact_test.rs"]
mod wi515_entity_schema_fact_test;

#[path = "include/wi662_carrier_agnostic_requires_test.rs"]
mod wi662_carrier_agnostic_requires_test;

#[path = "include/wi698_row_param_refinement_test.rs"]
mod wi698_row_param_refinement_test;

#[path = "include/wi729_qualified_rule_method_call_test.rs"]
mod wi729_qualified_rule_method_call_test;

#[path = "include/wi749_rule_ref_zero_arg_member_test.rs"]
mod wi749_rule_ref_zero_arg_member_test;

#[path = "include/wi750_chained_receiver_method_call_test.rs"]
mod wi750_chained_receiver_method_call_test;

#[path = "include/wi751_namespace_root_shadow_test.rs"]
mod wi751_namespace_root_shadow_test;

#[path = "include/wi752_dotted_ladder_test.rs"]
mod wi752_dotted_ladder_test;

#[path = "include/wi759_field_of_type_test.rs"]
mod wi759_field_of_type_test;

#[path = "include/wi732_project_ctor_test.rs"]
mod wi732_project_ctor_test;

#[path = "include/wi763_written_keep_spec_test.rs"]
mod wi763_written_keep_spec_test;

#[path = "include/wi766_one_component_tuple_type_test.rs"]
mod wi766_one_component_tuple_type_test;

#[path = "include/wi775_positional_tuple_bridge_test.rs"]
mod wi775_positional_tuple_bridge_test;

#[path = "include/wi782_param_list_alignment_test.rs"]
mod wi782_param_list_alignment_test;

#[path = "include/wi791_arrow_arity_test.rs"]
mod wi791_arrow_arity_test;

#[path = "include/wi783_function_value_named_args_test.rs"]
mod wi783_function_value_named_args_test;

#[path = "include/wi458_head_span_occurrence_test.rs"]
mod wi458_head_span_occurrence_test;

#[path = "include/wi764_relation_binding_order_test.rs"]
mod wi764_relation_binding_order_test;

#[path = "include/wi768_dispatch_binding_key_test.rs"]
mod wi768_dispatch_binding_key_test;

#[path = "include/wi785_named_tuple_destructuring_test.rs"]
mod wi785_named_tuple_destructuring_test;

#[path = "include/wi786_tuple_component_order_test.rs"]
mod wi786_tuple_component_order_test;

#[path = "include/wi784_closure_arity_test.rs"]
mod wi784_closure_arity_test;

#[path = "include/wi787_eta_spread_named_tuple_test.rs"]
mod wi787_eta_spread_named_tuple_test;

#[path = "include/wi792_function_value_args_test.rs"]
mod wi792_function_value_args_test;

#[path = "include/wi793_literal_receiver_projection_test.rs"]
mod wi793_literal_receiver_projection_test;

#[path = "include/wi794_multi_binder_annotation_test.rs"]
mod wi794_multi_binder_annotation_test;

#[path = "include/wi795_arity_mismatch_diagnostic_test.rs"]
mod wi795_arity_mismatch_diagnostic_test;

#[path = "include/wi790_positional_label_convention_test.rs"]
mod wi790_positional_label_convention_test;

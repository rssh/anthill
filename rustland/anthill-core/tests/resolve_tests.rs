//! Consolidated resolver / dispatch / proof integration tests (WI-244).

mod common;

#[path = "include/forall_impl_resolve_test.rs"]
mod forall_impl_resolve_test;

#[path = "include/push_choice_test.rs"]
mod push_choice_test;

#[path = "include/wi615_struct_eq_test.rs"]
mod wi615_struct_eq_test;

#[path = "include/wi616_semantic_eq_test.rs"]
mod wi616_semantic_eq_test;

#[path = "include/wi627_carrier_eq_classification_test.rs"]
mod wi627_carrier_eq_classification_test;

#[path = "include/wi300_rule_body_requires_test.rs"]
mod wi300_rule_body_requires_test;

#[path = "include/cut_test.rs"]
mod cut_test;

#[path = "include/route_dispatch_test.rs"]
mod route_dispatch_test;

#[path = "include/guard_trigger_test.rs"]
mod guard_trigger_test;

#[path = "include/nested_implication_test.rs"]
mod nested_implication_test;

#[path = "include/bounded_quant_test.rs"]
mod bounded_quant_test;

#[path = "include/proof_load_test.rs"]
mod proof_load_test;

#[path = "include/tactic_ir_test.rs"]
mod tactic_ir_test;

#[path = "include/incremental_load_test.rs"]
mod incremental_load_test;

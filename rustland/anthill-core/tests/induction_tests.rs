//! Consolidated induction / axiom-witness integration tests (WI-244).

mod common;

#[path = "include/induction_axiom_witness_test.rs"]
mod induction_axiom_witness_test;

#[path = "include/induction_rule_test.rs"]
mod induction_rule_test;

#[path = "include/numeric_induction_test.rs"]
mod numeric_induction_test;

#[path = "include/scope_axiom_witness_test.rs"]
mod scope_axiom_witness_test;

#[path = "include/specialization_witness_test.rs"]
mod specialization_witness_test;

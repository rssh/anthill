//! Single-binary integration test target.
//!
//! Each `tests/*_test.rs` file used to compile + link as its own
//! Cargo binary. Total ~26 binaries × ~3s of link/codegen each turned
//! into a 2-minute wait that dwarfed the actual test execution
//! (~0.3s per binary). Consolidating them into one binary cuts link
//! cost ~26× and incremental rebuilds win even more.
//!
//! Module list ordered as per the original tests/ folder for grep-
//! ability — adding a new test means dropping it under
//! `tests/integration/` and adding one `mod foo_test;` line here.

mod common;

mod carrier_include_test;
mod carrier_test;
mod conversion_test;
mod entity_struct_test;
mod expr_body_b_test;
mod expr_body_c_test;
mod expr_body_d_test;
mod expr_body_e_test;
mod expr_body_f_test;
mod expr_body_test;
mod generated_facts_test;
mod generic_sort_test;
mod generic_sum_test;
mod header_compile_test;
mod indexed_seq_test;
mod lf1_test;
mod match_binding_test;
mod math_vocab_test;
mod namespace_traits_test;
mod option_test;
mod parameterized_test;
mod runtime_header_test;
mod traits_struct_test;
mod variant_test;

// Diagnostics — `#[ignore]`-gated dev-time helpers, kept in the
// same binary so they stay buildable.
mod diag_generated;
mod diag_lf1;
mod diag_match_bind;
mod diag_phase_b;
mod diag_phase_c;
mod diag_phase_d;
mod diag_phase_f;

//! Single-binary integration test target — same pattern as
//! anthill-cpp-gen's tests/. Each `tests/integration/*.rs` file is a
//! module here, NOT a separate Cargo binary, so the slow Rust link
//! step happens once per run.

mod common;

mod assumptions_test;
mod comm_delay_test;
mod cross_namespace_inline_test;
mod inductive_test;
mod lf1_real_spec_test;
mod lift_implication_test;
mod qfnra_field_access_test;
mod step_distance_test;
mod wi680_ite_lowering_test;

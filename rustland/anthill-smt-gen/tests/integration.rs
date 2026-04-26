//! Single-binary integration test target — same pattern as
//! anthill-cpp-gen's tests/. Each `tests/integration/*.rs` file is a
//! module here, NOT a separate Cargo binary, so the slow Rust link
//! step happens once per run.

mod common;

mod comm_delay_test;
mod inductive_test;
mod lf1_real_spec_test;
mod step_distance_test;

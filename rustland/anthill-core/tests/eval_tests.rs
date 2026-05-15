//! Consolidated eval integration tests (WI-244). Each module below was
//! a separate integration test binary; merging amortizes the per-binary
//! linker setup that dominates wall time on macOS / debug builds.

mod common;

#[path = "include/eval_test.rs"]
mod eval_test;

#[path = "include/eval_q3_test.rs"]
mod eval_q3_test;

#[path = "include/eval_q4_test.rs"]
mod eval_q4_test;

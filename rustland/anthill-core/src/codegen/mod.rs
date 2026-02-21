/// Code generation from parse IR.
///
/// Phase 1: generate Rust skeletons from `ParsedFile`.
/// No CLI, no cross-file resolution, no KB boundary checking.

pub mod rust;
pub use rust::generate_rust;

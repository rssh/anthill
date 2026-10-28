/// Code generation from parse IR.
///
/// Phase 1: generate Rust skeletons from `ParsedFile`.
/// No CLI, no cross-file resolution, no KB boundary checking.
pub mod rust;
pub mod type_template;
pub use rust::{
    collect_sorts, generate_rust, generate_rust_with_config, generate_rust_with_context,
    CodegenConfig, CodegenError, SortCatalog,
};

//! Consolidated `anthill` CLI integration tests — ONE test binary.
//!
//! Each `tests/*_test.rs` used to be its own Cargo target: 28 separate
//! compile+link units, and 28 separate process launches. On macOS the second
//! half is the expensive one — the first execution of a never-run binary blocks
//! in the kernel's exec path on an out-of-process launch assessment (35-90s
//! measured on an Intel host, zero CPU in the process itself), and the verdict
//! is cached by CONTENT, so every rebuild pays it again per target. The tax is
//! per-FILE and flat regardless of size, so it scales down with target count and
//! with nothing else.
//!
//! Mirrors `anthill-core/tests/wi_tests.rs`, which is why the modules live under
//! `tests/include/` and are named with `#[path]`: a plain `mod foo;` from a test
//! crate root resolves to `tests/foo.rs`, which is exactly the location Cargo
//! auto-discovers as its own target — so leaving them there would compile and
//! RUN every test twice, once standalone and once here.
//!
//! Adding a test means dropping it in `tests/include/` and adding one `#[path]`
//! line below. `common` is declared once, here; the modules reach it as
//! `crate::common`. Fixture paths are unaffected by the move — they resolve
//! through `CARGO_MANIFEST_DIR`, not relative to the source file.

mod common;

#[path = "include/wi1047_query_stdlib_test.rs"]
mod wi1047_query_stdlib_test;

#[path = "include/load_cmd_test.rs"]
mod load_cmd_test;

#[path = "include/prove_body_derived_test.rs"]
mod prove_body_derived_test;

#[path = "include/prove_cache_test.rs"]
mod prove_cache_test;

#[path = "include/prove_derivation_test.rs"]
mod prove_derivation_test;

#[path = "include/prove_hint_test.rs"]
mod prove_hint_test;

#[path = "include/prove_induction_test.rs"]
mod prove_induction_test;

#[path = "include/prove_outcome_test.rs"]
mod prove_outcome_test;

#[path = "include/prove_ranking_test.rs"]
mod prove_ranking_test;

#[path = "include/prove_structured_test.rs"]
mod prove_structured_test;

#[path = "include/prove_tactic_test.rs"]
mod prove_tactic_test;

#[path = "include/prove_topo_test.rs"]
mod prove_topo_test;

#[path = "include/prove_trust_test.rs"]
mod prove_trust_test;

#[path = "include/prove_using_test.rs"]
mod prove_using_test;

#[path = "include/query_cmd_test.rs"]
mod query_cmd_test;

#[path = "include/run_cmd_test.rs"]
mod run_cmd_test;

#[path = "include/wi416_overflow_test.rs"]
mod wi416_overflow_test;

#[path = "include/wi564_check_discharge_test.rs"]
mod wi564_check_discharge_test;

#[path = "include/wi754_unknown_functor_test.rs"]
mod wi754_unknown_functor_test;

#[path = "include/wi767_query_resolve_default_test.rs"]
mod wi767_query_resolve_default_test;

#[path = "include/wi781_policy_dispatch_test.rs"]
mod wi781_policy_dispatch_test;

#[path = "include/wi852_parse_error_location_test.rs"]
mod wi852_parse_error_location_test;

#[path = "include/wi853_query_import_test.rs"]
mod wi853_query_import_test;

#[path = "include/wi863_nested_unknown_functor_test.rs"]
mod wi863_nested_unknown_functor_test;

#[path = "include/wi863_operator_arithmetic_test.rs"]
mod wi863_operator_arithmetic_test;

#[path = "include/wi878_marker_arity_test.rs"]
mod wi878_marker_arity_test;

#[path = "include/wi907_ambiguous_query_name_test.rs"]
mod wi907_ambiguous_query_name_test;

#[path = "include/wi914_listing_mode_name_test.rs"]
mod wi914_listing_mode_name_test;

#[path = "include/wi917_ambiguous_nested_query_name_test.rs"]
mod wi917_ambiguous_nested_query_name_test;

#[path = "include/wi1044_query_supplier_tie_test.rs"]
mod wi1044_query_supplier_tie_test;

#[path = "include/wi987_domain_sentinel_test.rs"]
mod wi987_domain_sentinel_test;

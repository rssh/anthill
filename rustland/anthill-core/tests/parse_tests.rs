//! Consolidated parse / typing / cli / codegen integration tests (WI-244).

mod common;

#[path = "include/parse_test.rs"]
mod parse_test;

#[path = "include/typing_test.rs"]
mod typing_test;

#[path = "include/cli_parse_test.rs"]
mod cli_parse_test;

#[path = "include/codegen_test.rs"]
mod codegen_test;

#[path = "include/fact_substitution_test.rs"]
mod fact_substitution_test;

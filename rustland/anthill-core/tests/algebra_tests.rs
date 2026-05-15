//! Consolidated algebra / spec / equational integration tests (WI-244).

mod common;

#[path = "include/algebra_spec_test.rs"]
mod algebra_spec_test;

#[path = "include/ring_polynom_test.rs"]
mod ring_polynom_test;

#[path = "include/logic_sorts_test.rs"]
mod logic_sorts_test;

#[path = "include/console_stdlib_test.rs"]
mod console_stdlib_test;

#[path = "include/operation_equation_test.rs"]
mod operation_equation_test;

#[path = "include/equational_attr_test.rs"]
mod equational_attr_test;

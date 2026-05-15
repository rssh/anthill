//! Consolidated built-in / persistence / time / serde integration tests (WI-244).

mod common;

#[path = "include/persistence_test.rs"]
mod persistence_test;

#[path = "include/persistence_builtins_test.rs"]
mod persistence_builtins_test;

#[path = "include/map_builtins_test.rs"]
mod map_builtins_test;

#[path = "include/time_now_test.rs"]
mod time_now_test;

#[path = "include/toml_ser_test.rs"]
mod toml_ser_test;

#[path = "include/vec3_ops_test.rs"]
mod vec3_ops_test;

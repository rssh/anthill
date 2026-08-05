//! Consolidated `anthill-todo` CLI integration tests — ONE test binary.
//!
//! Each `tests/*_test.rs` used to be its own Cargo target: 24 separate
//! compile+link units, and 24 separate process launches. On macOS the second
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
//! `crate::common` (a bare `use common::…` also resolves, since Rust 2018 `use`
//! paths start at the crate root).

mod common;

#[path = "include/cmd_add_test.rs"]
mod cmd_add_test;

#[path = "include/cmd_bundled_domain_test.rs"]
mod cmd_bundled_domain_test;

#[path = "include/cmd_claim_test.rs"]
mod cmd_claim_test;

#[path = "include/cmd_claim_unbalanced_paren_test.rs"]
mod cmd_claim_unbalanced_paren_test;

#[path = "include/cmd_default_parity_test.rs"]
mod cmd_default_parity_test;

#[path = "include/cmd_feedback_test.rs"]
mod cmd_feedback_test;

#[path = "include/cmd_insert_bundle_test.rs"]
mod cmd_insert_bundle_test;

#[path = "include/cmd_list_id_order_test.rs"]
mod cmd_list_id_order_test;

#[path = "include/cmd_list_tagged_bundle_test.rs"]
mod cmd_list_tagged_bundle_test;

#[path = "include/cmd_list_unblocked_test.rs"]
mod cmd_list_unblocked_test;

#[path = "include/cmd_preopen_promote_test.rs"]
mod cmd_preopen_promote_test;

#[path = "include/cmd_shim_test.rs"]
mod cmd_shim_test;

#[path = "include/cmd_status_transitions_test.rs"]
mod cmd_status_transitions_test;

#[path = "include/cmd_tag_bundle_test.rs"]
mod cmd_tag_bundle_test;

#[path = "include/cmd_tag_test.rs"]
mod cmd_tag_test;

#[path = "include/cmd_unclaim_test.rs"]
mod cmd_unclaim_test;

#[path = "include/cmd_update_status_test.rs"]
mod cmd_update_status_test;

#[path = "include/cmd_update_test.rs"]
mod cmd_update_test;

#[path = "include/cmd_version_stamp_test.rs"]
mod cmd_version_stamp_test;

#[path = "include/cmd_version_test.rs"]
mod cmd_version_test;

#[path = "include/wi203_store_test.rs"]
mod wi203_store_test;

#[path = "include/wi711_preopened_dep_blocks_test.rs"]
mod wi711_preopened_dep_blocks_test;

#[path = "include/wi717_omitted_optional_claimable_test.rs"]
mod wi717_omitted_optional_claimable_test;

#[path = "include/wi748_init_honors_dir_test.rs"]
mod wi748_init_honors_dir_test;


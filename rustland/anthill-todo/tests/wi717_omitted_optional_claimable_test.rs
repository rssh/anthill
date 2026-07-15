//! WI-717: the bundled workflow rules must classify a work item whose
//! OPTIONAL fields (`depends_on`, `description`) are omitted from the store.
//!
//! Since WI-716 an omitted optional is persisted/loaded as `none()`, not a
//! wildcard var — so a rule matching only the `nil()`/`cons(…)`/`some(?)`
//! shapes silently drops such an item from claimable/ready/open views. The
//! bundled rules read none() as "no dependencies" / "no description, still
//! listed"; `next` resolves the KB `claimable` rule directly, so it is the
//! CLI surface where the drop showed.

mod common;

use std::process::Command;

use common::setup_domainless_project;

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

const OMITTED_OPTIONAL_FIELDS: &str = "\
fact StoreFormat(version: 1)

fact WorkItem(
  id: \"WI-001\",
  description: \"omits depends_on entirely\",
  acceptance: [ToolPasses(\"cargo-test\")],
  status: Open)

fact WorkItem(
  id: \"WI-002\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)
";

#[test]
fn omitted_optionals_stay_claimable_and_listed() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_domainless_project(&tmp, OMITTED_OPTIONAL_FIELDS);
    let dir = proj.to_str().unwrap();

    // `next` is the CLI surface that resolves the bundled `claimable` rule.
    let next = Command::new(ANTHILL_TODO_BIN)
        .args(["-d", dir, "next", "--all"])
        .output()
        .unwrap();
    assert!(next.status.success(), "next failed: {}", String::from_utf8_lossy(&next.stderr));
    let next_out = String::from_utf8_lossy(&next.stdout);
    assert!(
        next_out.contains("WI-001"),
        "an item omitting depends_on must be claimable, got: {next_out}"
    );
    assert!(
        next_out.contains("WI-002"),
        "an item omitting description must still be claimable, got: {next_out}"
    );

    // list agrees: both items are ready, neither is blocked.
    let list = Command::new(ANTHILL_TODO_BIN)
        .args(["-d", dir, "list"])
        .output()
        .unwrap();
    assert!(list.status.success(), "list failed: {}", String::from_utf8_lossy(&list.stderr));
    let list_out = String::from_utf8_lossy(&list.stdout);
    assert!(list_out.contains("WI-001"), "WI-001 missing from list: {list_out}");
    assert!(list_out.contains("WI-002"), "WI-002 missing from list: {list_out}");
    assert!(
        !list_out.contains("-- blocked --"),
        "neither item has unmet deps, so no blocked section: {list_out}"
    );
}

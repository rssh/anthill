//! WI-505: the anthill.stage0 domain + workflow rules ship bundled in the
//! binary, so a project no longer needs (and is no longer trusted for) a
//! per-project domain.anthill/rules.anthill. These tests pin the three
//! behaviours that follow:
//!   1. a project with NO domain.anthill/rules.anthill loads and runs
//!      status/list/next against the bundled definitions;
//!   2. a stale, unparseable domain.anthill is ignored with a single note,
//!      not a wall of unresolved-import errors (the heimdall regression);
//!   3. `init` scaffolds a project that carries no drift-prone domain/rules.

mod common;

use std::process::Command;

use common::setup_domainless_project;

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

const TWO_ITEMS_ONE_BLOCKED: &str = "\
fact StoreFormat(version: 1)

fact WorkItem(
  id: \"WI-001\",
  description: \"first item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [],
  status: Open)

fact WorkItem(
  id: \"WI-002\",
  description: \"second item\",
  acceptance: [ToolPasses(\"cargo-test\")],
  depends_on: [\"WI-001\"],
  status: Open)
";

#[test]
fn domainless_project_runs_status_list_next() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_domainless_project(&tmp, TWO_ITEMS_ONE_BLOCKED);
    let dir = proj.to_str().unwrap();

    // status: both items load against the bundled anthill.stage0.WorkItem.
    let status = Command::new(ANTHILL_TODO_BIN)
        .args(["-d", dir, "status"])
        .output()
        .unwrap();
    assert!(
        status.status.success(),
        "status failed on domain-less project: {}",
        String::from_utf8_lossy(&status.stderr)
    );
    let status_out = String::from_utf8_lossy(&status.stdout);
    assert!(
        status_out.contains("Open: 2"),
        "expected 2 open items, got: {status_out}"
    );
    // No unresolved-import / parse noise on stderr.
    let status_err = String::from_utf8_lossy(&status.stderr);
    assert!(
        !status_err.contains("unresolved") && !status_err.contains("error:"),
        "unexpected load errors on domain-less project: {status_err}"
    );

    // list: WI-002 is blocked by WI-001 — proves the bundled workflow rules
    // (claimable/blocked) resolve without a project rules.anthill.
    let list = Command::new(ANTHILL_TODO_BIN)
        .args(["-d", dir, "list"])
        .output()
        .unwrap();
    assert!(list.status.success(), "list failed: {}", String::from_utf8_lossy(&list.stderr));
    let list_out = String::from_utf8_lossy(&list.stdout);
    assert!(list_out.contains("WI-001"), "WI-001 missing from list: {list_out}");
    assert!(list_out.contains("blocked"), "expected a blocked section: {list_out}");

    // next: the unblocked WI-001 is the claimable item — exercises the
    // bundled `anthill.stage0.workflow.claimable` rule via KB.execute.
    let next = Command::new(ANTHILL_TODO_BIN)
        .args(["-d", dir, "next"])
        .output()
        .unwrap();
    assert!(next.status.success(), "next failed: {}", String::from_utf8_lossy(&next.stderr));
    let next_out = String::from_utf8_lossy(&next.stdout);
    assert!(next_out.contains("WI-001"), "expected WI-001 as next, got: {next_out}");
    assert!(!next_out.contains("WI-002"), "blocked WI-002 must not be claimable: {next_out}");
}

#[test]
fn stale_domain_does_not_cascade_into_unresolved_imports() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = setup_domainless_project(&tmp, TWO_ITEMS_ONE_BLOCKED);

    // A domain.anthill from before a grammar change: the multi-name `export`
    // clause no longer parses. Pre-WI-505 the unparsed domain left WorkItem
    // undefined, cascading into a wall of unresolved-import errors from the
    // bundle and workitems; now the bundled domain supplies those names, so the
    // command still succeeds and only the honest parse diagnostic remains.
    std::fs::write(
        proj.join("anthill-todo").join("domain.anthill"),
        "namespace anthill.stage0\n  export WorkItem, WorkStatus, Tag\n  entity WorkItem(id: String, status: WorkStatus)\nend\n",
    )
    .unwrap();

    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["-d", proj.to_str().unwrap(), "status"])
        .output()
        .unwrap();
    assert!(
        out.status.success(),
        "status must still succeed despite a stale domain.anthill: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(stdout.contains("Open: 2"), "items lost with stale domain: {stdout}");

    let stderr = String::from_utf8_lossy(&out.stderr);
    // The key regression: no wall of unresolved-import errors, and load is not
    // fatal (the bundle covers the names the broken file failed to define).
    assert!(
        !stderr.contains("unresolved import"),
        "stale domain must not cascade into unresolved-import errors: {stderr}"
    );
    assert!(
        !stderr.contains("error:"),
        "a stale domain must not make the load fatal: {stderr}"
    );
    // The broken file itself is still surfaced honestly (loud over silent),
    // rather than swallowed.
    assert!(
        stderr.contains("domain.anthill"),
        "expected the parse diagnostic to name the broken file, got: {stderr}"
    );
}

#[test]
fn init_scaffolds_no_domain_or_rules() {
    let tmp = tempfile::tempdir().unwrap();
    let proj = tmp.path().to_path_buf();

    let init = Command::new(ANTHILL_TODO_BIN)
        .args(["init", "demo"])
        .current_dir(&proj)
        .output()
        .unwrap();
    assert!(init.status.success(), "init failed: {}", String::from_utf8_lossy(&init.stderr));

    let inner = proj.join("anthill-todo");
    assert!(inner.join("project.anthill").exists(), "project.anthill missing");
    assert!(inner.join("workitems.anthill").exists(), "workitems.anthill missing");
    // The drift-prone scaffolds are gone — the domain/rules ship bundled.
    assert!(
        !inner.join("domain.anthill").exists(),
        "init must not scaffold a drift-prone domain.anthill"
    );
    assert!(
        !inner.join("rules.anthill").exists(),
        "init must not scaffold a drift-prone rules.anthill"
    );

    // The freshly-scaffolded project is immediately usable.
    let add = Command::new(ANTHILL_TODO_BIN)
        .args(["-d", proj.to_str().unwrap(), "add", "first task"])
        .output()
        .unwrap();
    assert!(add.status.success(), "add failed: {}", String::from_utf8_lossy(&add.stderr));
    let list = Command::new(ANTHILL_TODO_BIN)
        .args(["-d", proj.to_str().unwrap(), "list"])
        .output()
        .unwrap();
    assert!(list.status.success(), "list failed: {}", String::from_utf8_lossy(&list.stderr));
    assert!(
        String::from_utf8_lossy(&list.stdout).contains("first task"),
        "added item missing from list"
    );
}

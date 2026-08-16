//! WI-830 — ANTHILL-TODO BUILDS ITS STORE FROM THE PROJECT'S DECLARATION.
//!
//! The store used to be a fixed `IndexedFileStore` at a fixed path, with the functors it
//! covers spelled as a literal array in `main.rs`. None of that was a project's to change,
//! which is what WI-437 (a GitHub-backed tracker) is blocked on. It is now
//! `fact ExtentBinding(store:, role:, covers:)` in `project.anthill`, and the host's only
//! remaining job is the one part that must stay native: mapping a declared store to one of
//! its compiled-in backends.
//!
//! WHAT IS DEFAULTED AND WHAT IS REFUSED. A project that declares no binding gets the
//! default one — `PROJECT_MARKERS` accepts a directory holding nothing but
//! `workitems.anthill`, so a zero-config tracker is a supported shape and refusing it
//! would delete a capability rather than tighten one. A binding that is PRESENT and wrong
//! is loud, because that is a project saying something it did not mean.
//!
//! WHAT FAILS WITHOUT THE CHANGE: `a_declared_binding_drives_the_real_store` and
//! `a_declared_owner_role_is_refused` — neither the fact nor its handling exists, so the
//! first sees its write land nowhere the declaration named and the second is not refused
//! at all. `default_matches_the_scaffolded_binding` fails too: `init` scaffolded no
//! binding to compare against.
//!
//! TWO OF THESE CAME OUT OF REVIEW, and each pins a hole the first cut had:
//! `a_lookalike_backend_name_is_refused` (the backend guard was a suffix match, so
//! `GitHubIndexedFileStore` was silently built as the local file store) and
//! `a_root_other_than_the_scanned_directory_is_refused` (the declared `root` was read by
//! nothing, so `root: "elsewhere"` wrote to the project directory anyway). Backed out,
//! each writes to disk on a path that should have refused.
//!
//! WHAT PASSES EITHER WAY BY DESIGN: `a_project_without_a_binding_still_works` — the
//! zero-config path behaves identically before and after, which is the point of it.

use std::fs;
use std::path::Path;
use std::process::Command;

use crate::common::{setup_domainless_project, setup_project};

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

/// Run against `proj` through the documented `-d <dir>` form.
fn run_in(proj: &Path, args: &[&str]) -> std::process::Output {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    Command::new(BIN).args(&full).output().expect("run anthill-todo")
}

/// A binding naming a NON-default file, so "the write went where the declaration said"
/// is distinguishable from "the write went where it always went".
const CUSTOM_FILE_BINDING: &str = r#"fact Project(
  name: "declared",
  language: "rust",
  build: "cargo",
  tools: ["cargo-test"])

fact anthill.persistence.ExtentBinding(
  store: anthill.persistence.filesystem.IndexedFileStore(
    root: ".",
    convention: anthill.persistence.filesystem.FileConvention.single_file(
      file: "workitems.anthill")),
  role: anthill.persistence.ExtentRole.mirror(),
  covers: [WorkItem, Feedback, Tag, StoreFormat])
"#;

/// THE LOAD-BEARING ONE: a declared binding really is what the running CLI writes through.
/// Driven end to end — add, then read back from the file the binding named, then delete
/// and see the row leave that file (the retract leg, which only works when the row's
/// reference carries the mirror the declared `covers` established).
#[test]
fn a_declared_binding_drives_the_real_store() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        CUSTOM_FILE_BINDING,
    )
    .expect("write project config");

    let out = run_in(&proj, &["add", "declared-store probe"]);
    assert!(out.status.success(), "add failed: {out:?}");

    let items = fs::read_to_string(proj.join("anthill-todo/workitems.anthill"))
        .expect("read workitems.anthill");
    assert!(
        items.contains("declared-store probe"),
        "the row landed in the file the binding named:\n{items}"
    );

    // The retract leg. `delete` reaches the row through `stored_facts_of`, whose reference
    // carries a mirror only for a COVERED functor — so this is the declared `covers`
    // being honoured, not just the persist path.
    let out = run_in(&proj, &["delete", "WI-001"]);
    assert!(out.status.success(), "delete failed: {out:?}");
    let items = fs::read_to_string(proj.join("anthill-todo/workitems.anthill"))
        .expect("read workitems.anthill");
    assert!(
        !items.contains("declared-store probe"),
        "the retract reached durability, so the row left the file:\n{items}"
    );
}

/// A project declaring `owner` is refused with the reason, not silently treated as a
/// mirror. anthill-todo loads every work item at startup and answers reads from the KB;
/// an owner would have to serve reads from its own query engine, which this host has no
/// backend for.
#[test]
fn a_declared_owner_role_is_refused() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        CUSTOM_FILE_BINDING.replace("ExtentRole.mirror()", "ExtentRole.owner()"),
    )
    .expect("write project config");

    let out = run_in(&proj, &["status"]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        !out.status.success(),
        "an owner-role declaration must not be accepted: {out:?}"
    );
    assert!(
        stderr.contains("owner") && stderr.contains("mirror()"),
        "the refusal says what was declared and what to write instead; got: {stderr}"
    );
}

/// A store this build has no backend for is named back, rather than silently becoming the
/// file store. This is the arm a SQL or GitHub backend is added to (WI-437).
#[test]
fn an_unknown_backend_is_named_back() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        CUSTOM_FILE_BINDING.replace(
            "anthill.persistence.filesystem.IndexedFileStore",
            "anthill.persistence.filesystem.FileStore",
        ),
    )
    .expect("write project config");

    let out = run_in(&proj, &["status"]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success(), "unknown backend must be refused");
    assert!(
        stderr.contains("FileStore") && stderr.contains("IndexedFileStore"),
        "the refusal names the declared store and what this build provides; got: {stderr}"
    );
}

/// A backend whose name merely ENDS WITH the supported one is still refused.
///
/// The first cut tested `store_name.ends_with("IndexedFileStore")`, which reads naturally
/// and accepted `GitHubIndexedFileStore` — a functor defined nowhere — as the local file
/// store. A project asking for a backend this build does not have therefore got a silent
/// write into its own directory instead of a refusal, which is exactly the WI-437 case the
/// guard exists for. Found in review; the fix compares resolved SYMBOLS.
///
/// `an_unknown_backend_is_named_back` above does NOT cover this: `FileStore` happens not
/// to end with the supported name, so it passed either way.
#[test]
fn a_lookalike_backend_name_is_refused() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        CUSTOM_FILE_BINDING.replace(
            "anthill.persistence.filesystem.IndexedFileStore",
            "GitHubIndexedFileStore",
        ),
    )
    .expect("write project config");

    let out = run_in(&proj, &["add", "must not be written"]);
    assert!(
        !out.status.success(),
        "a store this build has no backend for must be refused, not treated as the \
         local file store: {out:?}"
    );
    let items = fs::read_to_string(proj.join("anthill-todo/workitems.anthill"))
        .expect("read workitems.anthill");
    assert!(
        !items.contains("must not be written"),
        "and nothing may reach disk on the refused path:\n{items}"
    );
}

/// The declared `root` is CHECKED, not decorative. anthill-todo's store must write the
/// files the loader read — it seeds the store's source map with their byte ranges — so
/// there is one correct root and any other is refused.
///
/// The first cut ignored the field entirely: `root: "elsewhere"` wrote to the project
/// directory anyway, with no diagnostic. Found in review.
#[test]
fn a_root_other_than_the_scanned_directory_is_refused() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        CUSTOM_FILE_BINDING.replace(r#"root: ".""#, r#"root: "elsewhere""#),
    )
    .expect("write project config");

    let out = run_in(&proj, &["status"]);
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(!out.status.success(), "a foreign root must be refused");
    assert!(
        stderr.contains("elsewhere") && stderr.contains(r#"root: ".""#),
        "the refusal names what was declared and what to write; got: {stderr}"
    );
}

/// CONTROL — a project with no `project.anthill` at all behaves exactly as before. This is
/// the shape `PROJECT_MARKERS` admits and `setup_domainless_project` exists for, and the
/// reason the binding is defaulted rather than required.
#[test]
fn a_project_without_a_binding_still_works() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_domainless_project(&tmp, "");

    // `--acceptance` explicitly: a project with no `project.anthill` has no `Project`
    // fact to take a default acceptance set from. That is pre-existing and orthogonal —
    // what this test is about is that the STORE still works without a declaration.
    let out = run_in(&proj, &["add", "zero-config probe", "--acceptance", "cargo-test"]);
    assert!(out.status.success(), "add failed: {out:?}");
    let items = fs::read_to_string(proj.join("anthill-todo/workitems.anthill"))
        .expect("read workitems.anthill");
    assert!(
        items.contains("zero-config probe"),
        "the default binding writes to workitems.anthill:\n{items}"
    );

    let out = run_in(&proj, &["delete", "WI-001"]);
    assert!(out.status.success(), "delete failed: {out:?}");
    let items = fs::read_to_string(proj.join("anthill-todo/workitems.anthill"))
        .expect("read workitems.anthill");
    assert!(
        !items.contains("zero-config probe"),
        "and its retract reaches durability the same way:\n{items}"
    );
}

/// The scaffolded binding and the defaulted one must agree — they are the same
/// configuration written twice, once as text for `init` and once as a value for the
/// no-binding path, and nothing else ties them together.
///
/// Measured behaviourally rather than by comparing the two spellings: scaffold a project
/// with `init`, then run the same commands against it and against a project with no
/// config at all, and require the same on-disk outcome. `--acceptance` is passed to both
/// so the rows differ only in what the STORE did, not in what the scaffolded `Project`
/// fact supplies as a default acceptance set.
#[test]
fn default_matches_the_scaffolded_binding() {
    let scaffolded = tempfile::tempdir().expect("tempdir");
    let init = Command::new(BIN)
        .args(["-d", scaffolded.path().to_str().unwrap(), "init"])
        .output()
        .expect("run init");
    assert!(init.status.success(), "init failed: {init:?}");

    let config = fs::read_to_string(scaffolded.path().join("anthill-todo/project.anthill"))
        .expect("read scaffolded project.anthill");
    assert!(
        config.contains("ExtentBinding"),
        "init scaffolds the store binding:\n{config}"
    );

    let out = run_in(scaffolded.path(), &["add", "parity probe", "--acceptance", "cargo-test"]);
    assert!(out.status.success(), "add failed: {out:?}");
    let scaffolded_items =
        fs::read_to_string(scaffolded.path().join("anthill-todo/workitems.anthill"))
            .expect("read workitems");

    let bare = tempfile::tempdir().expect("tempdir");
    let bare_proj = setup_domainless_project(&bare, "");
    let out = run_in(&bare_proj, &["add", "parity probe", "--acceptance", "cargo-test"]);
    assert!(out.status.success(), "add failed: {out:?}");
    let bare_items =
        fs::read_to_string(bare_proj.join("anthill-todo/workitems.anthill")).expect("read");

    let row_of = |s: &str| {
        s.lines()
            .find(|l| l.contains("parity probe"))
            .unwrap_or("<no row>")
            .to_string()
    };
    assert_eq!(
        row_of(&scaffolded_items),
        row_of(&bare_items),
        "the scaffolded binding and the default one produce the same write"
    );
}

//! WI-20260828-C8SG5 — project discovery walks UP from the cwd.
//!
//! Discovery used to look in exactly two places, both AT the cwd: `<cwd>/anthill-todo/`
//! and `<cwd>` itself. That was adequate while a project was a single flat directory,
//! and stopped being so when the item-per-file layout (WI-1118) gave every new project
//! SUBDIRECTORIES: `<proj>/anthill-todo/open/` is where a user stands while editing a
//! `WI-….anthill.md`, and a bare `list` from there exited 1 — advising `init`, which
//! would have nested a SECOND project inside the tracker.
//!
//! THE WI-744 INVARIANT IS UNCHANGED, and that is what
//! `a_marker_less_anthill_todo_directory_never_wins_at_any_depth` is for: it is the
//! MARKER test, not the search depth, that rejects `rustland/anthill-todo/` (this CLI's
//! own crate). Deeper searching cannot resurrect that footgun because the crate is not
//! a candidate at any depth — while the tracker one level above it now IS found, which
//! is the project WI-744 wanted `anthill-todo list` in `rustland/` to reach.
//!
//! CONTROL, per the repo's testing rule. MEASURED against HEAD (`cargo test … wic8sg5`
//! with `src/main.rs` reverted): 7 of the 8 FAIL, 1 passes either way.
//!
//! Six fail on the BEHAVIOUR — each stands somewhere strictly below the project and
//! gets `no anthill-todo project found`, exit 1 — including
//! `a_marker_less_anthill_todo_directory_never_wins_at_any_depth`, whose cwd is a
//! level below the real project, and
//! `a_state_change_from_inside_the_item_tree_lands_in_the_same_tracker`, which is
//! the WRITE half. `no_project_anywhere_up_the_tree_is_a_loud_error` fails on its
//! WORDING assertion alone: its other two halves — a non-zero exit rather than
//! `No work items found`, and the refusal naming what it could not find — hold
//! either way, and pin that widening the search neither made discovery succeed by
//! accident nor ran off the end of the tree.
//!
//! `a_marker_less_anthill_todo_directory_beside_a_flat_project_is_not_the_scan_root`
//! fails for a DIFFERENT reason, and it is the one worth reading: it is a regression
//! test for the split between the MARKER decision and the SCAN target (found by
//! /code-review), and it fails at HEAD from the flat project's own directory, with no
//! walking involved. The walk only decided how far that damage reached.
//!
//! `a_nested_project_wins_over_the_one_above_it` passes EITHER WAY by design —
//! nearest-first is trivially satisfied by a search that never leaves the cwd. Its
//! control is REVERSING the iteration (`cwd.ancestors().rev()`), under which it is
//! the only test here that fails: every other one puts a single project on the
//! chain, so direction cannot be observed.
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

/// Scaffold a project exactly as a user would: `init`, which since WI-1118 writes the
/// item-per-file binding — so the item DIRECTORIES this ticket is about are the ones
/// `add` actually creates. Returns the project's `anthill-todo/` directory.
fn init_project(base: &Path) -> PathBuf {
    let out = Command::new(BIN)
        .args(["-d", base.to_str().unwrap(), "init"])
        .output()
        .expect("run init");
    assert!(
        out.status.success(),
        "init failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    base.join("anthill-todo")
}

/// File an item through `-d` (the arm this ticket does not touch) and return its
/// minted id — the needle every discovery assertion below looks for.
fn add(base: &Path, description: &str) -> String {
    let out = Command::new(BIN)
        .args(["-d", base.to_str().unwrap(), "add", description])
        .output()
        .expect("run add");
    assert!(
        out.status.success(),
        "add failed: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout)
        .split_whitespace()
        .nth(1)
        .expect("`added: <id> — …`")
        .to_string()
}

/// Run with NO `-d` and the cwd set — i.e. drive discovery, which is the whole point.
fn list_from(cwd: &Path) -> std::process::Output {
    Command::new(BIN)
        .current_dir(cwd)
        .args(["list"])
        .output()
        .expect("run list")
}

fn stdout_of(out: &std::process::Output, what: &str) -> String {
    assert!(
        out.status.success(),
        "{what}: discovery failed\nstdout: {}\nstderr: {}",
        String::from_utf8_lossy(&out.stdout),
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// THE TICKET'S CASE: standing in the tracker's own item tree.
#[test]
fn list_from_inside_the_item_tree_finds_the_project() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let inner = init_project(tmp.path());
    let id = add(tmp.path(), "an item filed in a file of its own");

    let open = inner.join("open");
    assert!(
        open.is_dir(),
        "the layout under test must have an item directory to stand in"
    );

    let listing = stdout_of(&list_from(&open), "from <proj>/anthill-todo/open");
    assert!(
        listing.contains(&id),
        "the project one level up must be the one found; got: {listing}"
    );
}

/// Depth is not one: a project is found from anywhere beneath it.
#[test]
fn list_from_a_deeply_nested_working_directory_finds_the_project() {
    let tmp = tempfile::tempdir().expect("tempdir");
    init_project(tmp.path());
    let id = add(tmp.path(), "found from four levels down");

    let deep = tmp.path().join("crates/core/src/parse");
    fs::create_dir_all(&deep).expect("mkdir nested");

    let listing = stdout_of(&list_from(&deep), "from four levels down");
    assert!(
        listing.contains(&id),
        "the ancestor project must be found; got: {listing}"
    );
}

/// WI-744, restated at depth. A directory NAMED `anthill-todo` that holds no marker is
/// not a project, so it cannot shadow the real one above it — this repo's own shape,
/// where `rustland/anthill-todo/` is the CLI's crate and the tracker sits a level up.
///
/// THE CONTROL IS THE ID. MEASURED, because the obvious phrasing of it was wrong:
/// dropping the marker test does NOT give an empty listing here — the crate dir
/// this test scaffolds carries `anthill/domain.anthill`, so the run dies at
/// `stdout_of`'s success check with "discovery failed", which reads as the
/// opposite of the truth (discovery SUCCEEDED, at the wrong directory). Either way
/// the id is absent, which is the assertion that matters; a maintainer who weakens
/// `is_project_dir` should read this note before hunting for a broken walk.
#[test]
fn a_marker_less_anthill_todo_directory_never_wins_at_any_depth() {
    let tmp = tempfile::tempdir().expect("tempdir");
    init_project(tmp.path());
    let id = add(tmp.path(), "the real tracker's item");

    // `<top>/rustland/anthill-todo/` — a crate, not a project: Cargo.toml, src/, and
    // `.anthill` sources of its own, and no `project.anthill` / `workitems.anthill`.
    let crate_dir = tmp.path().join("rustland/anthill-todo");
    fs::create_dir_all(crate_dir.join("src")).expect("mkdir crate src");
    fs::create_dir_all(crate_dir.join("anthill")).expect("mkdir crate anthill");
    fs::write(
        crate_dir.join("Cargo.toml"),
        "[package]\nname = \"anthill-todo\"\n",
    )
    .expect("write Cargo.toml");
    fs::write(crate_dir.join("src/main.rs"), "fn main() {}\n").expect("write main.rs");
    fs::write(
        crate_dir.join("anthill/domain.anthill"),
        "namespace anthill.stage0\nend\n",
    )
    .expect("write bundle source");

    let listing = stdout_of(&list_from(&tmp.path().join("rustland")), "from rustland/");
    assert!(
        listing.contains(&id),
        "discovery must skip the marker-less crate dir and reach the tracker above it; \
         got: {listing}"
    );
}

/// The flat "cwd IS the project" layout — a bare `workitems.anthill`, no
/// `anthill-todo/` subdirectory — is reached from below too. This is the loop's second
/// arm at a non-zero level; the first arm carries the tests above.
#[test]
fn the_flat_single_file_layout_is_found_from_a_subdirectory() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = tmp.path();
    fs::write(
        proj.join("workitems.anthill"),
        r#"
fact WorkItem(
  id: "WI-FLAT",
  created: "2026-01-01T00:00:00Z",
  description: "a row in the flat layout",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  last_status_change: StatusChange(status: Open()))
"#,
    )
    .expect("write workitems.anthill");

    let sub = proj.join("notes");
    fs::create_dir(&sub).expect("mkdir notes");

    let listing = stdout_of(&list_from(&sub), "from a flat project's subdirectory");
    assert!(
        listing.contains("WI-FLAT"),
        "the flat project above must be found; got: {listing}"
    );
}

/// Widening the search must not make discovery succeed by accident, nor run off the end
/// of the tree: with no project at any level the answer is still a loud, non-zero
/// refusal — and one that now says it looked at the parents too.
#[test]
fn no_project_anywhere_up_the_tree_is_a_loud_error() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let deep = tmp.path().join("a/b");
    fs::create_dir_all(&deep).expect("mkdir nested");

    crate::common::assert_no_project_above(&deep);

    let out = list_from(&deep);
    assert!(
        !out.status.success(),
        "no project anywhere must be a failure, not `No work items found`, exit 0: {}",
        String::from_utf8_lossy(&out.stdout)
    );
    let err = String::from_utf8_lossy(&out.stderr);
    assert!(
        err.contains("no anthill-todo project found"),
        "the refusal must name what it could not find; got: {err}"
    );
    assert!(
        err.contains("or any parent directory"),
        "and must say the parents were searched, so the reader does not retry one level \
         up; got: {err}"
    );
}

/// NEAREST FIRST — the only safety property the walk itself needs, and the one the
/// tests above cannot see, because each puts exactly ONE project on the cwd's
/// ancestor chain. Every one of them stays green under a farthest-first rewrite.
///
/// THE CONTROL IS THE ID: reverse the iteration (`cwd.ancestors().rev()`) and this
/// lists the OUTER item instead. `add`, below, is the half that matters — a
/// misordered walk does not merely list the wrong project, it WRITES to it.
#[test]
fn a_nested_project_wins_over_the_one_above_it() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let outer = tmp.path();
    init_project(outer);
    let outer_id = add(outer, "belongs to the outer project");

    let inner = outer.join("inner");
    fs::create_dir(&inner).expect("mkdir inner");
    init_project(&inner);
    let inner_id = add(&inner, "belongs to the inner project");

    let listing = stdout_of(&list_from(&inner), "from the inner project");
    assert!(
        listing.contains(&inner_id),
        "the NEAREST project must win; got: {listing}"
    );
    assert!(
        !listing.contains(&outer_id),
        "the outer project's items must not appear; got: {listing}"
    );

    // And the write lands in the nearest one too.
    let out = Command::new(BIN)
        .current_dir(&inner)
        .args(["add", "filed while standing in the inner project"])
        .output()
        .expect("run add");
    assert!(
        out.status.success(),
        "add from the inner project: {}",
        String::from_utf8_lossy(&out.stderr)
    );
    let filed = fs::read_dir(inner.join("anthill-todo/open"))
        .expect("inner open/")
        .count();
    assert_eq!(filed, 2, "both inner items are in the INNER tracker");
    assert_eq!(
        fs::read_dir(outer.join("anthill-todo/open"))
            .expect("outer open/")
            .count(),
        1,
        "the outer tracker gained nothing"
    );
}

/// THE WRITE PATH, from the cwd this ticket exists for. Every test above drives
/// discovery through the read-only `list`; the user standing in
/// `<proj>/anthill-todo/claimed/` is there to edit an item, and the next command
/// is a state change. A store anchored anywhere but the discovered root moves the
/// file into a second tracker and drops it out of the listing.
#[test]
fn a_state_change_from_inside_the_item_tree_lands_in_the_same_tracker() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let inner = init_project(tmp.path());
    let id = add(tmp.path(), "to be claimed from inside the tree");

    let open = inner.join("open");
    let out = Command::new(BIN)
        .current_dir(&open)
        .args(["claim", &id, "--agent", "claude"])
        .output()
        .expect("run claim");
    assert!(
        out.status.success(),
        "claim from inside the item tree: {}",
        String::from_utf8_lossy(&out.stderr)
    );

    assert!(
        inner.join(format!("claimed/{id}.anthill.md")).is_file(),
        "the item moved inside the SAME tracker"
    );
    assert!(
        !inner.join(format!("open/{id}.anthill.md")).exists(),
        "and left no copy behind"
    );
    let listing = stdout_of(&list_from(&open), "after claiming from inside the tree");
    assert!(
        listing.contains(&id),
        "the claimed item is still the discovered project's; got: {listing}"
    );
}

/// THE MARKER TEST AND THE SCAN TARGET ARE ONE DECISION (found by /code-review).
/// A flat project beside a MARKER-LESS `anthill-todo/` — a crate, a scratch
/// directory — used to resolve on the flat marker and then SCAN the marker-less
/// directory, because `find_project_dir` answered by marker and a separate
/// `scan_dir` re-derived the root by name.
///
/// CONTROL, and it is not the ancestor walk: this fails whenever those two
/// decisions are split again, and it fails the same way from `<top>` itself. The
/// walk only decides how far the damage reaches — before it, one had to stand
/// exactly on `<top>`; after it, every directory beneath.
#[test]
fn a_marker_less_anthill_todo_directory_beside_a_flat_project_is_not_the_scan_root() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let top = tmp.path();
    fs::write(
        top.join("workitems.anthill"),
        r#"
fact WorkItem(
  id: "WI-BESIDE",
  created: "2026-01-01T00:00:00Z",
  description: "the flat project's only row",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [],
  last_status_change: StatusChange(status: Open()))
"#,
    )
    .expect("write workitems.anthill");

    // A directory NAMED anthill-todo holding no marker — here, a crate.
    let decoy = top.join("anthill-todo");
    fs::create_dir_all(decoy.join("src")).expect("mkdir decoy");
    fs::write(decoy.join("Cargo.toml"), "[package]\nname = \"decoy\"\n").expect("Cargo.toml");

    let sub = top.join("sub");
    fs::create_dir(&sub).expect("mkdir sub");

    for (cwd, what) in [(top, "at the flat project"), (&sub as &Path, "below it")] {
        let listing = stdout_of(&list_from(cwd), what);
        assert!(
            listing.contains("WI-BESIDE"),
            "{what}: the scan must root at the directory the MARKER was found in, \
             not the marker-less anthill-todo/; got: {listing}"
        );
    }
}

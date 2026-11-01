//! `graph` must terminate on a corrupt CYCLIC store, keep rendering a DAG diamond under
//! both of its parents, and print every item; and the two "does A reach B" walks must
//! not walk every path through a cycle.
//!
//! `print_tree`/`print_children` walk `dep_map` through `direct_dependents_m`.
//! They carried no visited set and no depth bound, so a store whose items
//! depend on each other recursed until the process was killed -- while the two
//! sibling walks over the same map (`row_reaches`, `reaches_dep`) both guard,
//! with the comment "a corrupt cyclic store must not hang the CLI". The cycle
//! refusals on `add-dependency`/`insert` do not cover facts written straight
//! into the store, and `list` answers correctly on that data, so nothing
//! pointed at the store.
//!
//! The guard that fixed it was the PATH: a node already on the path from the root is
//! printed `(cycle)` and not descended into. That bounds the depth, not the count. Items
//! that depend on each other still printed every path through them (82,202 lines for
//! seven, measured on f180223c's bundle, whose walk is 502d4e0c's), and so did `dependents`. An item on a cycle is
//! now descended into once (`cyclic_items`; a later occurrence off the path prints
//! `(shown above)`), and every other item is printed as before, every path: decided with
//! the user (option (b), 2026-11-01) over descending into every item once, which would
//! have shortened this project's own `graph` from 3,364 lines to 1,928.
//!
//! A store with no item free of dependencies printed NOTHING and exited 0, and so was
//! every item no root reaches dropped in silence: one on a cycle beside a root, one whose
//! dependency names no item. `cmd_graph` now prints, after the roots' trees, the tree of
//! each dependency that names no item (`[?]`) and then each item still not printed.
//!
//! `row_reaches` (the tag view's order) and `reaches_dep` (the cycle refusal of
//! `add-dependency` and `insert`) guarded with a path too, and walked every path through
//! a cycle: at nine items depending on each other each ran out of the step budget after
//! 16 s and exited 1. They keep a visited set now; for a yes-or-no question that is
//! exact.
//!
//! CONTROLS -- measured, each piece backed out on its own in the bundle:
//!
//!   `cyclic_items` answering no item -- FAIL:
//!     an_item_on_a_cycle_is_descended_into_once
//!     items_that_depend_on_each_other_print_each_once (82,202 lines)
//!     dependents_prints_each_item_on_a_cycle_once
//!     an_item_below_an_unreached_cycle_is_printed_under_it
//!   `cyclic_items` answering every item (descending into every item once) -- FAIL:
//!     a_shared_item_on_no_cycle_renders_its_dependents_under_each_parent
//!     an_item_below_an_unreached_cycle_is_printed_under_it
//!   the missing and unreached trees left out of `cmd_graph` -- FAIL:
//!     a_store_with_no_item_free_of_dependencies_prints_every_item
//!     an_item_no_root_reaches_is_printed
//!     an_item_below_an_unreached_cycle_is_printed_under_it
//!   the unreached trees started at every row, not at the rows on a cycle first -- FAIL:
//!     an_item_below_an_unreached_cycle_is_printed_under_it
//!   `row_reaches` and `reaches_dep` with a path again -- FAIL:
//!     a_reachability_question_walks_each_item_once (step budget)
//!
//!   PASS UNDER EVERY BACK-OUT, by design: `cyclic_store_terminates_and_marks_the_cycle`
//!   (the path guard, which none of them touches) and
//!   `dag_diamond_still_renders_under_both_parents` (a leaf is printed whole either way).
//!   The path guard's own back-out (`let cycle = false`) does not return: `cargo test
//!   graph_cycle` was killed at 240 s, exit 143.

use std::path::Path;
use std::process::{Command, Output};

use crate::common::setup_project;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

fn item(id: &str, deps: &[&str]) -> String {
    let deps = deps
        .iter()
        .map(|d| format!("\"{d}\""))
        .collect::<Vec<_>>()
        .join(", ");
    format!(
        r#"
fact WorkItem(
  id: "{id}",
  created: "2026-01-01T00:00:00Z",
  description: "{id}",
  acceptance: [ToolPasses("cargo-test")],
  depends_on: [{deps}],
  last_status_change: StatusChange(status: Open()))
"#
    )
}

/// `WI-000`, and `n` items that each depend on it and on every other of them.
fn clique(n: usize) -> String {
    let ids: Vec<String> = (1..=n).map(|i| format!("WI-{i:03}")).collect();
    let mut fixture = item("WI-000", &[]);
    for id in &ids {
        let mut deps = vec!["WI-000"];
        deps.extend(ids.iter().filter(|o| *o != id).map(String::as_str));
        fixture.push_str(&item(id, &deps));
    }
    fixture
}

fn run(proj: &Path, args: &[&str]) -> Output {
    Command::new(BIN)
        .args(["-d", proj.to_str().unwrap()])
        .args(args)
        .output()
        .expect("run anthill-todo")
}

fn run_ok(proj: &Path, args: &[&str]) -> String {
    let out = run(proj, args);
    assert!(
        out.status.success(),
        "{args:?} failed: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

fn run_graph(fixture: &str) -> String {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, fixture);
    run_ok(&proj, &["graph"])
}

/// The store the reviewer drove: WI-002 and WI-003 depend on each other, so the
/// dependent edges form a 2-cycle. Before the guard this printed 52,000+ lines
/// of alternating ids and was killed at 60s.
#[test]
fn cyclic_store_terminates_and_marks_the_cycle() {
    let fixture = format!(
        "{}{}{}",
        item("WI-001", &[]),
        item("WI-002", &["WI-001", "WI-003"]),
        item("WI-003", &["WI-002"]),
    );
    let stdout = run_graph(&fixture);

    // Terminating at all is the point; bound the output so a future regression
    // that merely recurses *slower* still fails here.
    assert!(
        stdout.lines().count() < 40,
        "graph did not terminate compactly ({} lines): {stdout}",
        stdout.lines().count()
    );
    // The cycle is MARKED, not silently truncated.
    assert!(
        stdout.contains("(cycle)"),
        "a re-entered node must be marked, not dropped: {stdout}"
    );
    // And the store is still walked, not abandoned at the first edge.
    assert!(
        stdout.contains("WI-001") && stdout.contains("WI-002") && stdout.contains("WI-003"),
        "every item should still appear: {stdout}"
    );
}

/// A legitimate DAG diamond is NOT a cycle: WI-003 has two parents and must
/// render under each. This is the row a global visited set would break.
#[test]
fn dag_diamond_still_renders_under_both_parents() {
    let fixture = format!(
        "{}{}{}{}",
        item("WI-001", &[]),
        item("WI-002", &["WI-001"]),
        item("WI-004", &["WI-001"]),
        item("WI-003", &["WI-002", "WI-004"]),
    );
    let stdout = run_graph(&fixture);

    let renderings = stdout.matches("WI-003").count();
    assert_eq!(
        renderings, 2,
        "WI-003 has two parents and must print under both: {stdout}"
    );
    assert!(
        !stdout.contains("(cycle)"),
        "a DAG diamond is not a cycle: {stdout}"
    );
}

/// WI-002 and WI-003 depend on each other and on WI-001: the first of them reached is
/// printed with what depends on it, and the second time WI-003 is reached, off the path,
/// it is marked and not descended into again.
#[test]
fn an_item_on_a_cycle_is_descended_into_once() {
    let fixture = format!(
        "{}{}{}",
        item("WI-001", &[]),
        item("WI-002", &["WI-001", "WI-003"]),
        item("WI-003", &["WI-001", "WI-002"]),
    );
    assert_eq!(
        run_graph(&fixture),
        "WI-001 [Open]\n   \
         ├─ WI-002 [Open]\n   \
         │  └─ WI-003 [Open]\n   \
         │     └─ WI-002 [Open] (cycle)\n   \
         └─ WI-003 [Open] (shown above)\n"
    );
}

/// Seven items that depend on each other: the root's line, its seven dependents, and the
/// six dependents of each of the seven, printed once — 50 lines, where every path through
/// them was 82,202.
#[test]
fn items_that_depend_on_each_other_print_each_once() {
    let stdout = run_graph(&clique(7));
    assert_eq!(stdout.lines().count(), 50, "{stdout}");
    assert!(stdout.contains("(shown above)") && stdout.contains("(cycle)"), "{stdout}");
}

/// The same walk under `dependents`.
#[test]
fn dependents_prints_each_item_on_a_cycle_once() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, &clique(7));
    let stdout = run_ok(&proj, &["dependents", "WI-000"]);
    assert_eq!(stdout.lines().count(), 50, "{stdout}");
}

/// An item on no cycle is printed whole under each parent, the items that depend on it
/// too: only an item on a cycle is descended into once.
#[test]
fn a_shared_item_on_no_cycle_renders_its_dependents_under_each_parent() {
    let fixture = format!(
        "{}{}{}{}{}",
        item("WI-001", &[]),
        item("WI-002", &["WI-001"]),
        item("WI-004", &["WI-001"]),
        item("WI-003", &["WI-002", "WI-004"]),
        item("WI-005", &["WI-003"]),
    );
    assert_eq!(
        run_graph(&fixture),
        "WI-001 [Open]\n   \
         ├─ WI-002 [Open]\n   \
         │  └─ WI-003 [Open]\n   \
         │     └─ WI-005 [Open]\n   \
         └─ WI-004 [Open]\n      \
         └─ WI-003 [Open]\n         \
         └─ WI-005 [Open]\n"
    );
}

/// No item is free of dependencies: the first item no tree printed is a root of its own.
#[test]
fn a_store_with_no_item_free_of_dependencies_prints_every_item() {
    let fixture = format!("{}{}", item("WI-001", &["WI-002"]), item("WI-002", &["WI-001"]));
    assert_eq!(
        run_graph(&fixture),
        "WI-001 [Open]\n   \
         └─ WI-002 [Open]\n      \
         └─ WI-001 [Open] (cycle)\n"
    );
}

/// A dependency that names no item is a root printed `[?]`, with what depends on it; a
/// cycle beside a root is printed after the roots' trees.
#[test]
fn an_item_no_root_reaches_is_printed() {
    let dangling = format!("{}{}", item("WI-001", &[]), item("WI-002", &["WI-009"]));
    assert_eq!(
        run_graph(&dangling),
        "WI-001 [Open]\n\
         WI-009 [?]\n   \
         └─ WI-002 [Open]\n"
    );
    let beside = format!(
        "{}{}{}",
        item("WI-001", &[]),
        item("WI-002", &["WI-003"]),
        item("WI-003", &["WI-002"]),
    );
    assert_eq!(
        run_graph(&beside),
        "WI-001 [Open]\n\
         WI-002 [Open]\n   \
         └─ WI-003 [Open]\n      \
         └─ WI-002 [Open] (cycle)\n"
    );
}

/// An item that depends only on a cycle no root reaches is printed under it, not as a
/// root of its own first, though the store names it first.
#[test]
fn an_item_below_an_unreached_cycle_is_printed_under_it() {
    let fixture = format!(
        "{}{}{}",
        item("WI-003", &["WI-002"]),
        item("WI-001", &["WI-002"]),
        item("WI-002", &["WI-001"]),
    );
    assert_eq!(
        run_graph(&fixture),
        "WI-001 [Open]\n   \
         └─ WI-002 [Open]\n      \
         ├─ WI-003 [Open]\n      \
         └─ WI-001 [Open] (cycle)\n"
    );
}

/// Nine items that depend on each other, and WI-099 beside them: the tag view orders
/// WI-001 and WI-099, and `add-dependency WI-099 WI-001` asks whether WI-001 reaches
/// WI-099 — each walked every path through the nine. The refusal of a dependency that
/// closes a cycle still refuses.
#[test]
fn a_reachability_question_walks_each_item_once() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, &format!("{}{}", clique(9), item("WI-099", &[])));
    run_ok(&proj, &["tag", "WI-001", "t"]);
    run_ok(&proj, &["tag", "WI-099", "t"]);
    let listed = run_ok(&proj, &["list", "--tag", "t"]);
    assert!(listed.contains("2 item(s), sequence order"), "{listed}");
    let added = run_ok(&proj, &["add-dependency", "WI-099", "WI-001"]);
    assert!(added.contains("added dependency: WI-099 -> WI-001"), "{added}");
    let closing = run(&proj, &["add-dependency", "WI-000", "WI-099"]);
    let said = String::from_utf8_lossy(&closing.stderr);
    assert!(
        !closing.status.success() && said.contains("would create a cycle"),
        "a dependency closing a cycle must be refused: {said}"
    );
}

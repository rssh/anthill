//! `graph` must terminate on a corrupt CYCLIC store, and must keep rendering a
//! DAG diamond under both of its parents.
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
//! CONTROL, and it is asymmetric between the two rows -- MEASURED, not assumed.
//!
//! `cyclic_store_terminates_and_marks_the_cycle` FAILS on back-out. Neutralize
//! the guard by mutating `let cycle = list_contains_string(seen, id)` to
//! `let cycle = false` (keeping `seen` threaded, so the file still loads) and
//! the row does not mis-render -- it never returns. Measured: `cargo test
//! graph_cycle` was killed at 240s, exit 143.
//!
//! `dag_diamond_still_renders_under_both_parents` IS NOT DRIVEN BY THAT SAME
//! BACK-OUT, and saying otherwise would credit it with an observation nobody
//! made: the neutralized binary hangs, so this row cannot report either way.
//! Its job is the OTHER axis -- path-local versus GLOBAL visited, the other
//! obvious way to break the cycle, which would break the cycle just as well and
//! silently delete WI-003's second rendering. THAT back-out is NOT MEASURED
//! here: a global set requires `print_tree` to RETURN its accumulated set and
//! `print_children` to fold it through the siblings, which is a restructure of
//! the walk rather than a mutation of it. So this row states an invariant the
//! current shape satisfies and pins it against a future rewrite; it is not
//! evidence that the present code chose path-local for a measured reason.

use std::process::Command;

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

fn run_graph(fixture: &str) -> String {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, fixture);
    let out = Command::new(BIN)
        .args(["-d", proj.to_str().unwrap(), "graph"])
        .output()
        .expect("run anthill-todo graph");
    assert!(
        out.status.success(),
        "graph failed: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
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

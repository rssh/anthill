//! `[unblocks N]` counts DISTINCT reachable tickets, not incoming edges.
//!
//! `count_transitive` (anthill/main.anthill) threads a visited set so a
//! dependent reached by several paths is walked once. The `1 +` used to live in
//! `count_transitive_walk`, i.e. on the EDGE, while the dedup lived on the NODE
//! -- so every extra path to an already-counted node still added one.
//!
//! CONTROL. Both `#[test]`s below FAIL when the fix is backed out (restore
//! `pair(1 + sub + more, v3)` in `count_transitive_walk` and drop
//! `count_closure`): the two-level diamond reports 4 for 3 distinct, the
//! shallow one reports 3 for 2. `chain_and_tree_counts_are_unchanged` PASSES
//! EITHER WAY BY DESIGN -- it is the adjacent-shape control that pins the fix
//! to diamonds only, since in a graph where every node has exactly one
//! incoming path the edge count and the node count coincide.
//!
//! EACH DIAMOND ROW ASSERTS THE FIXTURE'S SHAPE, NOT ONLY THE COUNT, and that
//! is load-bearing rather than belt-and-braces. THE COUNT ALONE CANNOT SEE THE
//! DIAMOND: measured on the shipped binary, `two_level_diamond`'s fixture with
//! WI-004's second parent edge dropped -- a tree -- prints `[unblocks 3]` too,
//! and so does the same fixture with that edge typo'd to a dangling id, which
//! is not an error on this path. Degenerate shapes give every node one incoming
//! path, so per-edge and per-node counting agree and the arm silently becomes a
//! third copy of the adjacent-shape control. Asserting the rendered
//! `(depends: ...)` line pins the edge set, so a rename, a copy-paste slip, or
//! an id-format migration fails here instead of going green on a graph that no
//! longer contains a diamond.

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

fn run_list(fixture: &str) -> String {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, fixture);
    let out = Command::new(BIN)
        .args(["-d", proj.to_str().unwrap(), "list", "--status", "open"])
        .output()
        .expect("run anthill-todo");
    assert!(
        out.status.success(),
        "command failed: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// The shape `main.anthill`'s own doc comment promises to handle: `X -> A -> D`
/// and `X -> B -> D`. D is reachable by two paths and must be counted once, so
/// X's closure is {A, B, D} = 3.
#[test]
fn two_level_diamond_counts_the_shared_node_once() {
    let fixture = format!(
        "{}{}{}{}",
        item("WI-001", &[]),
        item("WI-002", &["WI-001"]),
        item("WI-003", &["WI-001"]),
        item("WI-004", &["WI-002", "WI-003"]),
    );
    let stdout = run_list(&fixture);
    // SHAPE FIRST: WI-004 must still have BOTH parents, or there is no diamond
    // left for the count below to be about.
    assert!(
        stdout.contains("WI-004 [Open] WI-004 (depends: WI-002, WI-003)"),
        "fixture lost the diamond -- WI-004 needs both parents: {stdout}"
    );
    assert!(
        stdout.contains("WI-002 [Open] WI-002 (depends: WI-001)")
            && stdout.contains("WI-003 [Open] WI-003 (depends: WI-001)"),
        "fixture lost a fork arm: {stdout}"
    );
    assert!(
        stdout.contains("WI-001 [Open] WI-001 [unblocks 3]"),
        "X reaches A, B, D -- 3 distinct, not 4 edges: {stdout}"
    );
}

/// The shallower diamond, and the one the real backlog hits: a node is both a
/// direct dependent of X and a dependent of another direct dependent of X.
/// `X -> A -> D` with `X -> D`. Closure is {A, D} = 2.
#[test]
fn direct_and_indirect_path_to_one_node_counts_it_once() {
    let fixture = format!(
        "{}{}{}",
        item("WI-001", &[]),
        item("WI-002", &["WI-001"]),
        item("WI-003", &["WI-001", "WI-002"]),
    );
    let stdout = run_list(&fixture);
    // SHAPE FIRST: WI-003 must reach WI-001 BOTH directly and through WI-002.
    // Drop either edge and this degenerates to a chain or a fork, both of which
    // print the same `[unblocks 2]` the assertion below matches.
    assert!(
        stdout.contains("WI-003 [Open] WI-003 (depends: WI-001, WI-002)"),
        "fixture lost a path -- WI-003 needs the direct AND the indirect edge: {stdout}"
    );
    assert!(
        stdout.contains("WI-002 [Open] WI-002 (depends: WI-001)"),
        "fixture lost the indirect path's middle node: {stdout}"
    );
    assert!(
        stdout.contains("WI-001 [Open] WI-001 [unblocks 2]"),
        "X reaches A and D -- 2 distinct, not 3 edges: {stdout}"
    );
}

/// ADJACENT-SHAPE CONTROL: passes both with and without the fix, by design.
/// A chain and a fan-out have one path per node, so counting edges and counting
/// nodes agree. Its job is to show the change did not move those.
#[test]
fn chain_and_tree_counts_are_unchanged() {
    let chain = format!(
        "{}{}{}",
        item("WI-001", &[]),
        item("WI-002", &["WI-001"]),
        item("WI-003", &["WI-002"]),
    );
    let stdout = run_list(&chain);
    assert!(
        stdout.contains("WI-001 [Open] WI-001 [unblocks 2]"),
        "chain X->A->B is 2: {stdout}"
    );

    let tree = format!(
        "{}{}{}",
        item("WI-001", &[]),
        item("WI-002", &["WI-001"]),
        item("WI-003", &["WI-001"]),
    );
    let stdout = run_list(&tree);
    assert!(
        stdout.contains("WI-001 [Open] WI-001 [unblocks 2]"),
        "fan-out X->{{A,B}} is 2: {stdout}"
    );
}

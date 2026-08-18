//! `list` orders ids NUMERICALLY, which for monotonically-allocated ids is
//! chronologically. The comparator used to be `lt` on the whole id string, i.e.
//! code units — so at id 1000 the newest items stopped appearing last: `WI-1000`
//! sorts between `WI-094` and `WI-102` lexicographically, burying every
//! four-digit item in the middle of a listing whose own comment
//! (`chrono_topo`, main.anthill) calls the cursor chronological.
//!
//! WHAT EACH ROW MEASURES — established by running both backouts, not by
//! reasoning about them. The two failing rows are NOT interchangeable:
//!
//!   restore `lt(yid, xid)` in `merge_by_id` (the old comparator)
//!     => `four_digit_ids_sort_after_three_digit` alone fails, with exactly the
//!        reported symptom: WI-094, WI-1000, WI-1005, WI-102, WI-999.
//!   drop `drop_leading_zeros` from `id_number` (the tempting simplification —
//!   compare the digit run as written, by length then code units)
//!     => `zero_padding_does_not_decide_the_order` alone fails: WI-0094 lands
//!        after WI-999, four digits beating three.
//!
//! So the padding row does NOT guard against the old code — it passes with it,
//! since below 1000 lexicographic and numeric agree. It guards the normalisation
//! step, which nothing else here would notice the loss of.
//!
//! `ids_below_the_boundary_are_unchanged` passes in all three configurations, BY
//! DESIGN: it is what makes the two failures attributable to the boundary and to
//! padding rather than to the sort having broken generally.

use std::process::Command;

use crate::common::setup_project;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

fn run(proj: &std::path::Path, args: &[&str]) -> String {
    let mut full = vec!["-d", proj.to_str().unwrap()];
    full.extend_from_slice(args);
    let out = Command::new(BIN)
        .args(&full)
        .output()
        .expect("run anthill-todo");
    assert!(
        out.status.success(),
        "command failed: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    String::from_utf8_lossy(&out.stdout).into_owned()
}

/// The ids a `list` printed, in the order printed. Read off the rendered output
/// rather than any internal ordering, because the rendered order is the whole
/// subject.
fn listed_ids(stdout: &str) -> Vec<String> {
    stdout
        .lines()
        .filter_map(|l| {
            let t = l.trim_start();
            t.starts_with("WI-")
                .then(|| t.split_whitespace().next().unwrap_or("").to_owned())
        })
        .filter(|s| !s.is_empty())
        .collect()
}

fn item(id: &str) -> String {
    format!(
        "\nfact WorkItem(\n  id: \"{id}\",\n  created: \"2026-01-01T00:00:00Z\",\n  description: \"item {id}\",\n  \
         acceptance: [ToolPasses(\"cargo-test\")],\n  depends_on: [],\n  status: Open)\n"
    )
}

fn project_of(tmp: &tempfile::TempDir, ids: &[&str]) -> std::path::PathBuf {
    let fixture: String = ids.iter().map(|id| item(id)).collect();
    setup_project(tmp, &fixture)
}

/// The boundary itself. No dependencies anywhere, so the topological pass in
/// `chrono_topo` is the identity and what is left is purely the id order.
#[test]
fn four_digit_ids_sort_after_three_digit() {
    let tmp = tempfile::tempdir().expect("tempdir");
    // Deliberately supplied out of order, so a pass-through would not pass.
    let proj = project_of(&tmp, &["WI-1000", "WI-102", "WI-094", "WI-1005", "WI-999"]);

    assert_eq!(
        listed_ids(&run(&proj, &["list"])),
        vec!["WI-094", "WI-102", "WI-999", "WI-1000", "WI-1005"],
        "ids must be ordered by NUMBER; lexicographically WI-1000 would follow WI-094",
    );
}

/// Zero-padding must not decide the order, which is why the digit run is
/// normalised instead of compared as written. A bare length compare gets the
/// row above right and this one backwards.
#[test]
fn zero_padding_does_not_decide_the_order() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = project_of(&tmp, &["WI-999", "WI-0094", "WI-94"]);

    let got = listed_ids(&run(&proj, &["list"]));
    assert_eq!(got.len(), 3, "all three rows must be listed: {got:?}");
    assert_eq!(
        got[2], "WI-999",
        "94 comes before 999 however 94 is written: {got:?}"
    );
    // The two spellings of 94 tie on number, so the whole-id tie-break decides
    // and the order is defined rather than arbitrary — `lt` on the full string.
    assert_eq!(
        &got[..2],
        &["WI-0094", "WI-94"],
        "tie-break is the whole id: {got:?}"
    );
}

/// CONTROL — passes with or without the fix. Below 1000 the two orders agree,
/// so this row measures that the sort still works at all, and the failures above
/// are attributable to the boundary.
#[test]
fn ids_below_the_boundary_are_unchanged() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = project_of(&tmp, &["WI-102", "WI-010", "WI-094"]);

    assert_eq!(
        listed_ids(&run(&proj, &["list"])),
        vec!["WI-010", "WI-094", "WI-102"],
    );
}

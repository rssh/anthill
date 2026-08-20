//! `anthill-todo --anthill add <description> [--depends ...]* [--acceptance ...]*`
//! integration test. Phase 2 of WI-009: cmd_add is the second mutating
//! command on the bundle, exercising the same persist+flush path as
//! cmd_feedback plus a freshly-derived id (max-WI-NNN + 1) and
//! repeatable-flag collection.

use std::fs;
use std::process::Command;

use crate::common::setup_project;

const ANTHILL_TODO_BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

fn read_all_anthill(inner: &std::path::Path) -> String {
    let mut combined = String::new();
    for entry in fs::read_dir(inner).expect("read_dir") {
        let path = entry.expect("entry").path();
        if path.extension().and_then(|s| s.to_str()) == Some("anthill") {
            combined.push_str(&fs::read_to_string(&path).expect("read"));
        }
    }
    combined
}

/// WI-1121 REPLACED THE TWO TESTS THAT USED TO SIT HERE.
///
/// `add_assigns_next_id_after_max` and `add_empty_project_starts_at_wi_001`
/// pinned the counter: the first asserted `WI-006` after `WI-005`, the second
/// `WI-001` in an empty project. There is no counter to pin any more — an id is
/// derived from the item (§6.5) — so both moved to
/// `wi1121_content_hash_ids_test`, which asserts what replaced them: the shape
/// of a minted id, that it does NOT continue the sequence on disk, and that the
/// same `add` twice re-derives one id rather than filing two items.
///
/// What stays here is everything about `add` that the mint did not change.

#[test]
fn add_repeatable_depends_in_caller_order() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args([
            "--anthill",
            "-d",
            proj.to_str().unwrap(),
            "add",
            "with deps",
            "--depends",
            "WI-A",
            "--depends",
            "WI-B",
            "--depends",
            "WI-C",
        ])
        .output()
        .expect("run");
    assert!(
        out.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );

    let combined = read_all_anthill(&proj.join("anthill-todo"));
    // WI-A precedes WI-B precedes WI-C in the persisted depends_on
    // list — confirms the repeatable-flag collection preserves the
    // order the user typed them.
    let a_pos = combined.find("\"WI-A\"").expect("WI-A in output");
    let b_pos = combined.find("\"WI-B\"").expect("WI-B in output");
    let c_pos = combined.find("\"WI-C\"").expect("WI-C in output");
    assert!(
        a_pos < b_pos && b_pos < c_pos,
        "depends order wrong: {combined}"
    );
}

#[test]
fn add_default_acceptance_comes_from_single_project_tool() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        "fact Project(\n  name: \"one-module\",\n  language: \"rust\",\n  build: \"cargo\",\n  modules: [\"core\"],\n  tools: [\"project-check\"])\n\nfact Module(name: \"core\", root: \"core\", language: \"rust\", build: \"cargo\")\n",
    )
    .expect("write project config");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args([
            "--anthill",
            "-d",
            proj.to_str().unwrap(),
            "add",
            "default-accept",
        ])
        .output()
        .expect("run");
    assert!(
        out.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );

    // WI-1068 CONTROL: read the persisted WorkItem itself, not the project file
    // that also names this tool. This passes before and after only when the
    // single-project default is actually embedded in the new fact.
    let combined =
        fs::read_to_string(proj.join("anthill-todo/workitems.anthill")).expect("read workitems");
    assert!(
        combined.contains("ToolPasses(tool: \"project-check\")"),
        "expected Project.tools acceptance, got: {combined}"
    );
    assert!(
        !combined.contains("cargo-test"),
        "hardcoded default survived: {combined}"
    );
}

#[test]
fn add_embeds_every_project_tool_for_a_multi_module_project() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    fs::write(
        proj.join("anthill-todo/project.anthill"),
        "fact Project(\n  name: \"multi\",\n  language: \"rust\",\n  build: \"cargo\",\n  modules: [\"rustland\", \"scaland\"],\n  tools: [\"cargo-test\", \"scaland-sbt-test\"])\n\nfact Module(name: \"rustland\", root: \"rustland\", language: \"rust\", build: \"cargo\")\nfact Module(name: \"scaland\", root: \"scaland\", language: \"scala\", build: \"sbt\")\n",
    )
    .expect("write project config");

    let out = Command::new(ANTHILL_TODO_BIN)
        .args([
            "--anthill",
            "-d",
            proj.to_str().unwrap(),
            "add",
            "fix scaland/core/src/main/scala/anthill/Typing.scala",
        ])
        .output()
        .expect("run");
    assert!(
        out.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );

    let workitems =
        fs::read_to_string(proj.join("anthill-todo/workitems.anthill")).expect("read workitems");
    // WI-1068 DRIVES the capability: backing out the Project.tools reader drops
    // scaland-sbt-test and restores only cargo-test. We intentionally embed ALL
    // project tools: unlike --module it needs no module->tool mapping, unlike
    // path inference it does not interpret prose, and unlike requiring an
    // explicit flag it keeps a safe default. The extra Rust gate is conservative.
    assert!(
        workitems.contains("ToolPasses(tool: \"cargo-test\")")
            && workitems.contains("ToolPasses(tool: \"scaland-sbt-test\")"),
        "new work item did not embed the complete Project.tools list: {workitems}"
    );
}

#[test]
fn add_without_project_refuses_before_writing() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = crate::common::setup_domainless_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args([
            "--anthill",
            "-d",
            proj.to_str().unwrap(),
            "add",
            "must not be written",
        ])
        .output()
        .expect("run");

    assert!(!out.status.success(), "missing Project must be loud");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("default acceptance requires exactly one Project fact"),
        "unexpected diagnostic: {stderr}"
    );
    let workitems =
        fs::read_to_string(proj.join("anthill-todo/workitems.anthill")).expect("read workitems");
    assert!(
        !workitems.contains("must not be written"),
        "failed resolution mutated workitems: {workitems}"
    );
}

#[test]
fn add_custom_acceptance_overrides_default() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args([
            "--anthill",
            "-d",
            proj.to_str().unwrap(),
            "add",
            "custom-accept",
            "--acceptance",
            "my-tool",
        ])
        .output()
        .expect("run");
    assert!(
        out.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );

    let combined = read_all_anthill(&proj.join("anthill-todo"));
    assert!(combined.contains("ToolPasses(tool: \"my-tool\")"));
    // The default cargo-test must not appear when the user supplied
    // an explicit acceptance — it would mean the default-fallback
    // branch fired even though the user opted out.
    // WI-1121: keyed on the ONE fact the file holds rather than on a counter's
    // `WI-001`, which is no longer what an id looks like.
    let added_block_start = combined.find("fact WorkItem(").expect("the added item lives");
    let added_block = &combined[added_block_start..];
    let block_end = added_block
        .find("last_status_change: StatusChange(status: Open,")
        .map(|i| added_block_start + i)
        .unwrap_or(combined.len());
    let added_block = &combined[added_block_start..block_end];
    assert!(
        !added_block.contains("\"cargo-test\""),
        "cargo-test default leaked into custom-acceptance block: {added_block}"
    );
}

#[test]
fn add_missing_description_errors() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let proj = setup_project(&tmp, "");
    let out = Command::new(ANTHILL_TODO_BIN)
        .args(["--anthill", "-d", proj.to_str().unwrap(), "add"])
        .output()
        .expect("run");
    assert!(!out.status.success(), "expected failure");
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(
        stderr.contains("argument error") || stderr.contains("missing"),
        "expected diagnostic, got stderr: {stderr}"
    );
}

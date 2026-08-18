//! WI-009 shim regressions: the host-side interceptions (`init`, `skill`)
//! must fire regardless of where the global flags sit — the documented
//! invocation form is `anthill-todo -d "$PWD" <subcommand>`, so the strip
//! runs BEFORE the interception check (the /code-review round caught
//! `-d X init` exploding into a bundle load with no project).

use std::process::Command;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

#[test]
fn init_with_leading_dir_flag_scaffolds() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = Command::new(BIN)
        .current_dir(tmp.path())
        .args(["-d", tmp.path().to_str().unwrap(), "init"])
        .output()
        .expect("run init");
    assert!(
        out.status.success(),
        "init with leading -d must scaffold: stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
    assert!(
        tmp.path().join("anthill-todo/workitems.anthill").exists(),
        "scaffold missing"
    );
}

#[test]
fn skill_with_leading_dir_flag_prints_frontmatter() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = Command::new(BIN)
        .args(["-d", tmp.path().to_str().unwrap(), "skill"])
        .output()
        .expect("run skill");
    assert!(out.status.success());
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.starts_with("---\nname: anthill-todo\n"),
        "skill must print the YAML frontmatter (Claude Code parses it): {stdout}"
    );
}

#[test]
fn agent_equals_form_is_accepted() {
    let tmp = tempfile::tempdir().expect("tempdir");
    let init = Command::new(BIN)
        .current_dir(tmp.path())
        .arg("init")
        .output()
        .unwrap();
    assert!(init.status.success());
    let proj = tmp.path().to_str().unwrap().to_string();
    let add = Command::new(BIN)
        .args(["-d", &proj, "add", "item"])
        .output()
        .unwrap();
    assert!(add.status.success());
    // WI-1121: the id is minted from the item, so the test asks what was filed
    // rather than naming a counter's `WI-001`.
    let id = String::from_utf8_lossy(&add.stdout)
        .split_whitespace()
        .nth(1)
        .expect("`added: <id> — …`")
        .to_string();
    let out = Command::new(BIN)
        .args([
            format!("--agent=claude"),
            format!("-d={proj}"),
            "claim".into(),
            id.clone(),
        ])
        .output()
        .expect("run claim");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        stdout.contains(&format!("claimed: {id} by claude")),
        "=-joined globals must work: stdout={stdout} stderr={}",
        String::from_utf8_lossy(&out.stderr)
    );
}

#[test]
fn dangling_dir_flag_errors_loudly() {
    let out = Command::new(BIN)
        .args(["list", "-d"])
        .output()
        .expect("run");
    assert!(
        !out.status.success(),
        "-d with no value must error, not fall back to cwd"
    );
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("requires a value"), "stderr: {stderr}");
}

#[test]
fn removed_stdlib_flag_errors_loudly() {
    let out = Command::new(BIN)
        .args(["--stdlib", "/x", "list"])
        .output()
        .expect("run");
    assert!(!out.status.success());
    let stderr = String::from_utf8_lossy(&out.stderr);
    assert!(stderr.contains("--stdlib"), "stderr: {stderr}");
}

//! WI-160: `anthill-todo` reports its build version (semver + git SHA +
//! build date). `--version`, `-V`, and the `version` subcommand all print
//! the same non-empty stamp; `--version` works in any position; and the
//! embedded SHA matches the repo HEAD. None of these need a project dir.

use std::process::Command;

const BIN: &str = env!("CARGO_BIN_EXE_anthill-todo");

fn run(args: &[&str]) -> (String, bool) {
    let out = Command::new(BIN).args(args).output().expect("run anthill-todo");
    (
        String::from_utf8_lossy(&out.stdout).trim().to_string(),
        out.status.success(),
    )
}

#[test]
fn version_flag_prints_nonempty_stamp() {
    let (stdout, ok) = run(&["--version"]);
    assert!(ok, "--version must exit 0");
    assert!(!stdout.is_empty(), "--version must print a non-empty string");
    assert!(
        stdout.starts_with("anthill-todo "),
        "version line must name the binary: {stdout}"
    );
}

#[test]
fn version_subcommand_and_short_flag_match_long_flag() {
    let (long, _) = run(&["--version"]);
    let (short, _) = run(&["-V"]);
    let (sub, _) = run(&["version"]);
    assert_eq!(long, sub, "`version` subcommand must match `--version`");
    assert_eq!(long, short, "`-V` must match `--version`");
}

#[test]
fn version_flag_accepted_after_global_dir_flag() {
    // "accepted at any subcommand position" — the global `-d` strip must not
    // swallow the flag, and no project directory is required.
    let (stdout, ok) = run(&["-d", ".", "--version"]);
    assert!(ok, "`-d . --version` must exit 0");
    assert!(stdout.starts_with("anthill-todo "), "got: {stdout}");
}

#[test]
fn version_flag_after_subcommand_is_not_hijacked() {
    // Regression (code-review): `--version` / `-V` appearing AFTER the
    // subcommand is a normal argument (e.g. a description word), not the
    // version flag — it must reach the bundle, not short-circuit the version
    // print. Run in an empty dir with no project so the fall-through fails
    // loudly (proving the token was NOT consumed as the version flag); the
    // pre-fix code would have printed the stamp and exited 0 instead.
    let tmp = tempfile::tempdir().expect("tempdir");
    let out = Command::new(BIN)
        .current_dir(tmp.path())
        .args(["add", "--version"])
        .output()
        .expect("run anthill-todo");
    let stdout = String::from_utf8_lossy(&out.stdout);
    assert!(
        !stdout.contains("0.1.0"),
        "`add --version` must not print the version stamp: {stdout}"
    );
    assert!(
        !out.status.success(),
        "`add --version` in an empty dir must fall through to (failing) project resolution"
    );
}

#[test]
fn embedded_sha_matches_head() {
    let head = match Command::new("git")
        .args(["rev-parse", "--short", "HEAD"])
        .output()
    {
        Ok(o) if o.status.success() => String::from_utf8(o.stdout).unwrap().trim().to_string(),
        _ => {
            eprintln!("not a git checkout — skipping SHA-match assertion");
            return;
        }
    };
    let (stdout, _) = run(&["version"]);
    assert!(
        stdout.contains(&head),
        "version line must embed HEAD sha {head}: {stdout}"
    );
}

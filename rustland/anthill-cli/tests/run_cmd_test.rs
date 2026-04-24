//! Acceptance tests for `anthill run` (WI-051, proposal 028).
//! Invokes the built binary against fixture programs and asserts on
//! stdout, stderr, and exit code.

use std::path::PathBuf;
use std::process::Command;

fn bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_anthill"))
}

fn fixtures_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/fixtures/run")
}

struct Output {
    code: i32,
    stdout: String,
    stderr: String,
}

fn run_with(args: &[&str]) -> Output {
    let out = Command::new(bin())
        .arg("run")
        .args(args)
        .output()
        .expect("run anthill binary");
    Output {
        code: out.status.code().unwrap_or(-1),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

#[test]
fn hello_program_prints_and_exits_zero() {
    let path = fixtures_dir().join("hello.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "hello, world\n");
}

#[test]
fn no_main_fails_with_exit_2() {
    let path = fixtures_dir().join("no-main.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 2);
    assert!(out.stderr.contains("no program entry found"),
            "stderr did not mention missing entry:\n{}", out.stderr);
}

#[test]
fn ambiguous_entries_list_candidates_and_exit_2() {
    let path = fixtures_dir().join("two-mains.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 2);
    assert!(out.stderr.contains("ambiguous program entry"),
            "stderr missing ambiguity banner:\n{}", out.stderr);
    assert!(out.stderr.contains("my.two.One"),
            "stderr missing `my.two.One` candidate:\n{}", out.stderr);
    assert!(out.stderr.contains("my.two.Two"),
            "stderr missing `my.two.Two` candidate:\n{}", out.stderr);
}

#[test]
fn entry_flag_disambiguates() {
    let path = fixtures_dir().join("two-mains.anthill");
    let out = run_with(&["--entry", "my.two.Two", path.to_str().unwrap()]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "two\n");
}

#[test]
fn args_passed_after_double_dash() {
    let path = fixtures_dir().join("args.anthill");
    let out = run_with(&[path.to_str().unwrap(), "--", "first", "second", "third"]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "first\nsecond\nthird\n");
}

#[test]
fn main_return_value_is_exit_code() {
    let path = fixtures_dir().join("exit7.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 7, "stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "");
}

#[test]
fn eprintln_writes_to_stderr_not_stdout() {
    let path = fixtures_dir().join("eprintln.anthill");
    let out = run_with(&[path.to_str().unwrap()]);
    assert_eq!(out.code, 0, "stderr:\n{}", out.stderr);
    assert_eq!(out.stdout, "stdout-line\n");
    assert!(out.stderr.contains("stderr-line\n"),
            "expected `stderr-line` on stderr; got:\n{}", out.stderr);
    assert!(!out.stdout.contains("stderr-line"),
            "stderr-line leaked to stdout:\n{}", out.stdout);
}

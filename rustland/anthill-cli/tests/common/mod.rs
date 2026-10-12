//! Shared harness for the `anthill` CLI acceptance tests.
//!
//! `run_cmd_test`, `load_cmd_test` and `query_cmd_test` all drive the built
//! binary and assert on stdout/stderr/exit code. Each Rust integration test file
//! is its own crate, so they share this via `mod common;` — the convention
//! anthill-core, anthill-cpp-gen and anthill-smt-gen already follow.

#![allow(dead_code)] // each test file uses a subset

use std::path::PathBuf;
use std::process::Command;

pub struct Output {
    pub code: i32,
    pub stdout: String,
    pub stderr: String,
}

impl Output {
    /// Lines of stderr that are diagnostics of `kind` (`"error:"` / `"warning:"`).
    ///
    /// Line-wise on purpose: a bare `stderr.contains("warning:")` cannot tell a
    /// warning ABOUT this file from an unrelated advisory sharing the stream (the
    /// stdlib emits requires-shadow warnings on every load), and a bare
    /// `contains("error:")` once matched a diagnostic's own text rather than the
    /// CLI's prefix — vacuous against the regression it was meant to pin.
    pub fn diagnostics<'a>(&'a self, kind: &'a str) -> impl Iterator<Item = &'a str> {
        self.stderr.lines().filter(move |l| l.starts_with(kind))
    }

    /// Is there a `kind` diagnostic mentioning `needle`?
    pub fn has_diagnostic(&self, kind: &str, needle: &str) -> bool {
        self.diagnostics(kind).any(|l| l.contains(needle))
    }

    /// Whole-line stdout match for count/summary lines — `"12 solution(s)"`
    /// contains `"2 solution(s)"`, so a substring check cannot pin a count.
    pub fn has_stdout_line(&self, needle: &str) -> bool {
        self.stdout.lines().any(|l| l.trim() == needle)
    }
}

pub fn bin() -> PathBuf {
    PathBuf::from(env!("CARGO_BIN_EXE_anthill"))
}

/// `tests/fixtures/<group>` — e.g. `fixtures_dir("run")`.
pub fn fixtures_dir(group: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures")
        .join(group)
}

/// Write `contents` to a uniquely-named temp dir and return the path.
///
/// `name` is the full filename including extension. Every `prove_*` test file
/// carries its own copy of this; new tests should call this one instead. The
/// directory is deliberately left behind for failure-mode debugging, matching
/// the convention in `anthill-smt-gen/tests/common`.
pub fn write_temp(name: &str, contents: &str) -> PathBuf {
    let dir = std::env::temp_dir().join(format!("anthill-test-{}-{}", std::process::id(), name));
    std::fs::create_dir_all(&dir).unwrap();
    let path = dir.join(name);
    std::fs::write(&path, contents).unwrap();
    path
}

/// `anthill prove <src> --dry-run --no-cache`: the emitted SMT documents on stdout, and
/// no solver asked — a dry run returns where the document is printed. For a row whose
/// subject is what is EMITTED, which must not pass for want of a z3 on the path.
pub fn prove_dry_run(name: &str, src: &str) -> Output {
    let path = write_temp(&format!("{name}.anthill"), src);
    anthill(&["prove", path.to_str().unwrap(), "--dry-run", "--no-cache"])
}

/// Is there a `z3` on the path? A row that returns when there is none has asked
/// nothing: keep what it holds to a verdict, and put the rest under [`prove_dry_run`].
/// (Twelve `prove_*` / `check_*` files carry their own copy of this, as they do of
/// `write_temp`; new rows call this one.)
pub fn z3_available() -> bool {
    Command::new("z3")
        .arg("--version")
        .output()
        .map(|o| o.status.success())
        .unwrap_or(false)
}

/// Run the built binary with `args`.
pub fn anthill(args: &[&str]) -> Output {
    let out = Command::new(bin())
        .args(args)
        .output()
        .expect("run anthill binary");
    Output {
        code: out.status.code().unwrap_or(-1),
        stdout: String::from_utf8_lossy(&out.stdout).into_owned(),
        stderr: String::from_utf8_lossy(&out.stderr).into_owned(),
    }
}

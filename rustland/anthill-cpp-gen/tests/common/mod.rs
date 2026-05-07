//! Shared test helpers for anthill-cpp-gen integration tests.
//!
//! Stdlib parsing is `LazyLock`-cached so the ~40 .anthill files
//! parse once per test binary; KB construction is per-test.
//! Compiler-discovery is also cached.

use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::LazyLock;

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;
use anthill_core::parse::ir::ParsedFile;

/// Recursively collect .anthill files under a directory.
pub fn collect_anthill_files(dir: &Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if dir.is_dir() {
        for entry in std::fs::read_dir(dir).expect("read dir") {
            let entry = entry.expect("read dir entry");
            let path = entry.path();
            if path.is_dir() {
                files.extend(collect_anthill_files(&path));
            } else if path.extension().is_some_and(|e| e == "anthill") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

/// Path to the workspace's stdlib/anthill/ directory.
pub fn stdlib_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/anthill")
}

/// Path to the workspace root (parent of `rustland/`).
#[allow(dead_code)]
pub fn rustland_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Parsed stdlib, computed once per test binary.
static STDLIB_PARSED: LazyLock<Vec<ParsedFile>> = LazyLock::new(|| {
    let files = collect_anthill_files(&stdlib_dir());
    assert!(!files.is_empty(), "stdlib must be loadable from {}", stdlib_dir().display());
    files.iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect()
});

/// Build a KB with the cached stdlib + a user source string.
#[allow(dead_code)]
pub fn load_kb_with(source: &str) -> KnowledgeBase {
    load_kb_with_extras(source, &[])
}

/// First C++ compiler that responds to `--version`, cached so the
/// subprocess runs once per test binary. `None` means tests that
/// invoke a compiler should skip with a warning, not fail.
#[allow(dead_code)]
pub fn find_cxx() -> Option<&'static str> {
    static CXX: LazyLock<Option<&'static str>> = LazyLock::new(|| {
        for candidate in ["clang++", "g++", "c++"] {
            if Command::new(candidate)
                .arg("--version")
                .output()
                .map(|o| o.status.success())
                .unwrap_or(false)
            {
                return Some(candidate);
            }
        }
        None
    });
    *CXX
}

/// Per-test scratch directory under `temp_dir()`. Test name + PID +
/// nanos keeps it unique across parallel runs without bringing in a
/// tempfile crate.
#[allow(dead_code)]
pub fn scratch_dir(test_name: &str) -> PathBuf {
    use std::time::{SystemTime, UNIX_EPOCH};
    let nanos = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos())
        .unwrap_or(0);
    let dir = std::env::temp_dir().join(format!(
        "anthill-cpp-gen-{}-{}-{}",
        test_name,
        std::process::id(),
        nanos
    ));
    std::fs::create_dir_all(&dir).expect("create scratch dir");
    dir
}

/// Build a KB with the cached stdlib + the user source + any
/// additional file paths' contents (re-parsed each call). Use this
/// for tests that load real project files alongside an inline spec.
#[allow(dead_code)]
pub fn load_kb_with_extras(source: &str, extra_paths: &[PathBuf]) -> KnowledgeBase {
    let user = parse::parse(source).expect("parse user source");
    let extras: Vec<ParsedFile> = extra_paths.iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();

    let mut refs: Vec<&ParsedFile> = STDLIB_PARSED.iter().collect();
    refs.extend(extras.iter());
    refs.push(&user);

    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .unwrap_or_else(|errs| {
            for e in &errs { eprintln!("{}", e); }
            if std::env::var("ANTHILL_TEST_IGNORE_LOAD_ERRORS").is_err() {
                panic!("load failed with {} errors", errs.len());
            }
            load::LoadResult { defined_sorts: Vec::new(), fact_rule_ids: Vec::new() }
        });
    kb
}

/// Variant of `load_kb_with` that does not panic on load errors —
/// useful for diagnostics that need to inspect post-typing term
/// shapes even when the type checker rejects an expression.
#[allow(dead_code)]
pub fn load_kb_with_lenient(source: &str) -> KnowledgeBase {
    let user = parse::parse(source).expect("parse user source");
    let mut refs: Vec<&ParsedFile> = STDLIB_PARSED.iter().collect();
    refs.push(&user);
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

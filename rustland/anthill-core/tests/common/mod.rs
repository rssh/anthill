/// Shared test utilities for anthill-core integration tests.

use std::path::PathBuf;

/// WI-605/WI-618: the marker phrase of both bare-arrow lambda-typo
/// diagnostics — a stable slice of `load::LAMBDA_KEYWORD_HINT`, the tail the
/// two messages share. One const so the wi605/wi618 suites pin the same
/// invariant.
#[allow(dead_code)]
pub const LAMBDA_HINT: &str = "needs the `lambda` keyword";

use anthill_core::eval::{self, Interpreter};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Collect all .anthill files under a directory, recursively.
pub fn collect_anthill_files(dir: &std::path::Path) -> Vec<PathBuf> {
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

/// Workspace root (the `oss/anthill/` directory containing rustland/, stdlib/,
/// anthill-todo/, etc.). Computed from the anthill-core crate's manifest
/// directory.
#[allow(dead_code)]
pub fn workspace_root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../..")
}

/// Path to stdlib/anthill/ relative to the anthill-core crate root.
pub fn stdlib_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/anthill")
}

/// Path to rustland/anthill-stl/anthill/ — Rust host bindings for the
/// builtin spec sorts (proposal 038).
pub fn rust_stl_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../anthill-stl/anthill")
}

/// Collect all .anthill files from stdlib + the Rust host bindings.
/// Use this in place of `collect_anthill_files(&stdlib_dir())` for tests
/// that depend on `fact Spec[Carrier]` records emitted by the rustland
/// `provides Carrier language rust` blocks.
#[allow(dead_code)]
pub fn collect_stdlib_and_rust_bindings() -> Vec<PathBuf> {
    let mut files = collect_anthill_files(&stdlib_dir());
    files.extend(collect_anthill_files(&rust_stl_dir()));
    files.sort();
    files
}

/// Path to anthill-testcases/ relative to the anthill-core crate root.
#[allow(dead_code)]
pub fn testcases_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../anthill-testcases")
}

/// Path to examples/ relative to the anthill-core crate root.
#[allow(dead_code)]
pub fn examples_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../examples")
}

/// Load the stdlib + the given user source into a fresh KB. Panics with a
/// readable diagnostic on parse or load errors. Used across every eval
/// integration test; previously hand-copied in each file.
#[allow(dead_code)]
pub fn load_kb_with(source: &str) -> KnowledgeBase {
    try_load_kb_with(source).unwrap_or_else(|errs| {
        for e in &errs { eprintln!("{}", e); }
        panic!("load failed with {} errors", errs.len());
    })
}

/// Same load as [`load_kb_with`] (full stdlib + Rust host bindings + `source`)
/// but returns the load errors instead of panicking, so a test can assert an
/// expected load-time (typer) error. The error strings are the rendered
/// `LoadError`s. Parse failures still panic (they are test-authoring bugs).
#[allow(dead_code)]
pub fn try_load_kb_with(source: &str) -> Result<KnowledgeBase, Vec<String>> {
    try_load_kb_with_files(&[source])
}

/// Like [`try_load_kb_with`] but loads MULTIPLE user source strings as SEPARATE
/// files (each its own `ParsedFile`) alongside the stdlib — for asserting
/// cross-file load behavior, e.g. WI-321 cross-file mutual structural recursion
/// (two files whose entities reference each other's sorts must both load).
#[allow(dead_code)]
pub fn try_load_kb_with_files(sources: &[&str]) -> Result<KnowledgeBase, Vec<String>> {
    let files = collect_stdlib_and_rust_bindings();
    assert!(!files.is_empty(), "stdlib empty");

    let mut parsed: Vec<_> = files.iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for source in sources {
        parsed.push(parse::parse(source).expect("parse user source"));
    }

    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => Ok(kb),
        Err(errs) => Err(errs.iter().map(|e| e.to_string()).collect()),
    }
}

/// Load stdlib + user source, construct an `Interpreter`, and register the
/// standard eval builtins. The one-liner every eval_mN_test file needs.
#[allow(dead_code)]
pub fn interp_for(source: &str) -> Interpreter {
    let kb = load_kb_with(source);
    let mut interp = Interpreter::new(kb);
    eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    interp
}

// ── Effect handler test helpers (M5) ─────────────────────────

/// Build a buffered Console handler and return `(buffer, handler)`.
/// Works for ConsoleOutput or ConsoleError — the caller registers the
/// handler against whichever effect sort it wants to capture.
#[allow(dead_code)]
pub fn buffered_console() -> (
    std::rc::Rc<std::cell::RefCell<String>>,
    anthill_core::eval::effects::EffectHandler,
) {
    let buf = std::rc::Rc::new(std::cell::RefCell::new(String::new()));
    let handler = anthill_core::eval::effects::buffered_console_handler(buf.clone());
    (buf, handler)
}

/// Build a scripted `ConsoleInput` handler from a list of lines and
/// return `(queue, handler)`. The queue holds any lines the program
/// didn't consume — useful for assertions.
#[allow(dead_code)]
pub fn scripted_console_input(lines: &[&str]) -> (
    std::rc::Rc<std::cell::RefCell<std::collections::VecDeque<String>>>,
    anthill_core::eval::effects::EffectHandler,
) {
    let queue = std::rc::Rc::new(std::cell::RefCell::new(
        lines.iter().map(|s| s.to_string()).collect()
    ));
    let handler = anthill_core::eval::effects::scripted_console_input_handler(queue.clone());
    (queue, handler)
}

/// Register the default `Modify` arena-backed handler on the interpreter.
/// Shared across Modify-focused tests that don't want to depend on the
/// stdio-binding side effects of `register_standard_effect_handlers`.
#[allow(dead_code)]
pub fn register_modify_handler(interp: &mut Interpreter) {
    interp.register_effect_handler("anthill.prelude.Modify",
        anthill_core::eval::effects::default_modify_handler())
        .expect("register Modify handler");
}

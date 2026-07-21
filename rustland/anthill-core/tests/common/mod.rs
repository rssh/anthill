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

/// Collect all .anthill files under a directory, recursively. WI-747: the walk
/// is the shared `anthill_core::fs_util`; the test suites' policy is to panic on
/// an unreadable directory (a broken fixture is a test-authoring bug).
pub fn collect_anthill_files(dir: &std::path::Path) -> Vec<PathBuf> {
    anthill_core::fs_util::collect_files(dir, &["anthill"]).expect("collect .anthill files")
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

/// The messages of a source that must NOT parse — for a rule enforced at
/// parse/convert rather than at load, where `try_load_kb_with` would panic
/// instead of returning the diagnostic. Panics if the source parses clean, since
/// a fixture that no longer trips the rule is a test-authoring bug.
///
/// Shared because the checks that report here have multiplied: the projection
/// well-formedness rules (`validate_projection_labels`, WI-639) and the tuple
/// component-label distinctness rule (`check_tuple_label_unique`, WI-805),
/// whose fixtures live in four suites. Assert on the returned messages; the
/// panic here only says the source parsed at all.
#[allow(dead_code)]
pub fn parse_errs(src: &str) -> Vec<String> {
    match parse::parse(src) {
        Ok(_) => panic!("expected a parse error, but the source parsed clean"),
        Err(errs) => errs.iter().map(|e| e.message.clone()).collect(),
    }
}

/// The control twin of [`parse_errs`]: a source that MUST parse. Panics with the
/// diagnostics if it does not, so a guard that over-fires names what it caught
/// rather than failing as a bare `false`.
#[allow(dead_code)]
pub fn parses_clean(src: &str) {
    if let Err(errs) = parse::parse(src) {
        panic!("expected a clean parse; got: {errs:?}");
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

/// The stdlib-only KB the re-type suites build on: parse + `register_prelude` +
/// `register_standard_builtins` + `load_stdlib`, with NO user source. WI-732 lifted this here
/// after finding six verbatim copies across the test tree (typing_test, incremental_load_test,
/// wi211, wi219, wi759, and its own) — a change to the load sequence otherwise has to land in
/// every one, and the copy that misses it fails as though the code under test were broken.
///
/// Distinct from [`try_load_kb_with`], which loads the stdlib AND a user source in one shot and
/// returns only errors. A caller needing the `LoadResult` (to type-check the user file's OWN
/// sorts, then RE-type-check to exercise the free-op sweep) needs the two steps split, which
/// is what this and [`load_stdlib_kb_with_source`] provide.
#[allow(dead_code)]
pub fn load_stdlib_kb() -> KnowledgeBase {
    let files = collect_anthill_files(&stdlib_dir());
    assert!(!files.is_empty(), "no stdlib files found");
    let parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {p:?}: {e}"));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {p:?}: {e:?}"))
        })
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_stdlib(&mut kb, &refs, &NullResolver).expect("stdlib load");
    kb
}

/// [`load_stdlib_kb`] plus ONE user source, returning the `LoadResult` too — the split-step
/// form a re-type test needs (`type_check_sorts(&result.defined_sorts)`, then
/// `type_check_sorts(&[])`). Parse and load failures panic: both are test-authoring bugs here,
/// since a test asserting a LOAD error uses [`try_load_kb_with`] instead.
#[allow(dead_code)]
pub fn load_stdlib_kb_with_source(source: &str) -> (KnowledgeBase, anthill_core::kb::load::LoadResult) {
    let mut kb = load_stdlib_kb();
    let parsed = parse::parse(source).expect("parse failed");
    let result = load::load(&mut kb, &parsed, &NullResolver).expect("load failed");
    (kb, result)
}

/// Walk an anthill cons-list `Value` into its `Int64` elements.
///
/// A list is a chain of `cons(head, tail)` entities terminated by a
/// zero-field `nil`; each `cons` carries its two components as NAMED fields, so
/// the head is the `Int` among them and the tail the `Entity`. Several
/// per-WI suites grew a private copy of this walk (wi714_*, wi727, wi730);
/// this is the shared one to reach for.
#[allow(dead_code)]
pub fn list_ints(v: &eval::Value) -> Vec<i64> {
    use eval::Value;
    let mut out = Vec::new();
    let mut cur = v.clone();
    while let Value::Entity { named, .. } = &cur {
        if named.is_empty() {
            break; // nil
        }
        let mut head: Option<i64> = None;
        let mut tail: Option<Value> = None;
        for (_k, item) in named.iter() {
            match item {
                Value::Int(i) => head = Some(*i),
                Value::Entity { .. } => tail = Some(item.clone()),
                _ => {}
            }
        }
        match (head, tail) {
            (Some(h), Some(t)) => {
                out.push(h);
                cur = t;
            }
            _ => break,
        }
    }
    out
}

// ── Tuple-cluster fixture builder (WI-786 / 788 / 803) ───────

/// Build `ap(f) = f(<lit>)` over a `Function[A = <ty>, B = Int64]`, driven by
/// `drive() = ap(<lam>)`.
///
/// ONE builder for the program shape the WI-775 → 786 → 788 → 804 → 803 cluster
/// is argued over: a tuple literal reaching a destructuring binder list through a
/// `Function` slot. It had been copy-pasted into three test files, and
/// `wi788_..`'s copy carried a doc comment claiming it was "the same builder as
/// `wi786_..`'s" — a claim nothing enforced, and exactly the property those files
/// need, since their value is being comparable line for line. WI-803 was about to
/// add a fourth copy.
///
/// `imports` is the brace-list body (e.g. `"Int64, String, Function"`).
#[allow(dead_code)]
pub fn function_slot_case(ns: &str, imports: &str, ty: &str, lit: &str, lam: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{{imports}}}
  operation ap(f: Function[A = {ty}, B = Int64]) -> Int64
    = f({lit})
  operation drive() -> Int64
    = ap({lam})
end
"#
    )
}

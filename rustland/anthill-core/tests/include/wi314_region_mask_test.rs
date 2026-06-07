//! WI-314 — region / escape masking for `Modify[result]`.
//!
//! `Cell.new : Modify[result]` (proposal 045 §5.5) is masked at the
//! operation boundary by `kb::region`: an op whose return type cannot
//! carry the fresh region has the effect dropped (so it stays non-viral),
//! while an op that returns the region keeps it (re-keyed to its own
//! `result`) and must declare it. These tests pin both directions —
//! including the let-bound escaping case that wi205 does not exercise.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Load stdlib + user source together (mirrors `common::load_kb_with`, the
/// path the effect check runs on) and surface load errors as strings
/// rather than panicking.
fn load_result(source: &str) -> Result<(), Vec<String>> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    parsed.push(parse::parse(source).expect("parse user source"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver)
        .map(|_| ())
        .map_err(|errs| errs.iter().map(|e| format!("{}", e)).collect())
}

#[test]
fn discarded_allocation_is_masked() {
    // A cell allocated then discarded — the return type `Int64` cannot carry
    // the region, so `Modify[result]` is masked and no effect declaration
    // is needed. This is the non-virality win.
    let src = r#"
namespace test.wi314.discard
  import anthill.prelude.{Int64, Cell}

  operation discard(n: Int64) -> Int64 =
    let c = Cell.new(n)
    Cell.get(c)
end
"#;
    load_result(src).expect("a discarded allocation must not require an effect declaration");
}

#[test]
fn escaping_let_bound_cell_requires_declaration() {
    // The fresh cell escapes via the result (it is returned). It must NOT
    // be silently dropped — the op is obliged to declare `Modify[result]`.
    let src = r#"
namespace test.wi314.escape_undeclared
  import anthill.prelude.{Int64, Cell}

  operation dup(n: Int64) -> Cell =
    let c = Cell.new(n)
    c
end
"#;
    let errs = load_result(src)
        .expect_err("an op returning a freshly-allocated cell must declare Modify[result]");
    assert!(
        errs.iter()
            .any(|e| e.contains("result") && (e.contains("Modify") || e.contains("effect"))),
        "expected an undeclared-Modify[result] effect error; got: {:#?}",
        errs,
    );
}

#[test]
fn escaping_let_bound_cell_with_declaration_loads() {
    // Same op, now declaring the effect it genuinely has — loads cleanly.
    let src = r#"
namespace test.wi314.escape_declared
  import anthill.prelude.{Int64, Cell}

  operation dup(n: Int64) -> Cell effects Modify[result] =
    let c = Cell.new(n)
    c
end
"#;
    load_result(src).expect("declaring Modify[result] must satisfy the boundary check");
}

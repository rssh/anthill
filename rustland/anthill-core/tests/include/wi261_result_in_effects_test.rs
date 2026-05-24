//! WI-261 / proposal 041: `result` reserved in effects rows.
//!
//! Today `result` is reserved in `ensures` clauses (spec §5.4). Proposal
//! 041 lifts the reservation to effects rows so allocator-style ops
//! (027.1) can declare `effects Modify[result]` and named-tuple ops
//! can declare per-component effects via field projection
//! (`Modify[result.a]`, `Modify[result.b]`) using existing §6.7 syntax.
//!
//! No grammar or new IR — only the loader's scope registration changes.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

fn load_stdlib_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let parsed: Vec<_> = files.iter()
        .map(|p| parse::parse(&std::fs::read_to_string(p).unwrap()).unwrap())
        .collect();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib load");
    kb
}

#[test]
fn result_in_effects_single_return() {
    // `effects Modify[result]` on a paramless allocator-shaped op:
    // `result` must resolve through the operation's scope (added by 041).
    let source = r#"
namespace anthill.test.wi261.single
  import anthill.prelude.{Cell, Int}

  operation fresh_counter() -> Cell[V = Int]
    effects Modify[result]
end
"#;
    let mut kb = load_stdlib_kb();
    let parsed = parse::parse(source).expect("parse failed");
    load::load(&mut kb, &parsed, &NullResolver)
        .expect("load should accept `effects Modify[result]`");
}

#[test]
fn result_in_effects_single_return_with_params() {
    // Same as above but with a parameter alongside `result`. Param `c`
    // and reserved `result` both live in the op scope.
    let source = r#"
namespace anthill.test.wi261.with_params
  import anthill.prelude.{Cell, Int}

  operation init_counter(initial: Int) -> Cell[V = Int]
    effects Modify[result]
end
"#;
    let mut kb = load_stdlib_kb();
    let parsed = parse::parse(source).expect("parse failed");
    load::load(&mut kb, &parsed, &NullResolver)
        .expect("load should accept `effects Modify[result]` with params");
}

#[test]
fn result_field_projection_in_effects() {
    // Named-tuple return + per-component effect attribution via field
    // projection. `result.a` and `result.b` go through existing §6.7
    // field-access machinery; 041 only needs `result` to resolve.
    let source = r#"
namespace anthill.test.wi261.tuple
  import anthill.prelude.{Cell, Int}

  operation make_pair() -> (a: Cell[V = Int], b: Cell[V = Int])
    effects {Modify[result.a], Modify[result.b]}
end
"#;
    let mut kb = load_stdlib_kb();
    let parsed = parse::parse(source).expect("parse failed");
    load::load(&mut kb, &parsed, &NullResolver)
        .expect("load should accept per-component `Modify[result.a]` / `Modify[result.b]`");
}

#[test]
fn param_named_result_rejected() {
    // A parameter named `result` collides with the reserved return-value
    // name. The loader should emit a clear error.
    let source = r#"
namespace anthill.test.wi261.conflict
  import anthill.prelude.{Int}

  operation bad(result: Int) -> Int
end
"#;
    let mut kb = load_stdlib_kb();
    let parsed = parse::parse(source).expect("parse failed");
    let errors = match load::load(&mut kb, &parsed, &NullResolver) {
        Ok(_) => panic!("loading an operation with param named 'result' should error"),
        Err(errs) => errs,
    };
    let conflict_match: Vec<_> = errors.iter()
        .filter(|e| {
            let m = format!("{}", e);
            m.contains("result") && m.contains("reserved")
        })
        .collect();
    assert!(
        !conflict_match.is_empty(),
        "expected an error mentioning 'result' and 'reserved'; got: {:#?}",
        errors
    );
}

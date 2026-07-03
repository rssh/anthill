//! WI-620 — parenthesized single lambda binder: `lambda (x) -> body`.
//!
//! `(x)` matched no `_pattern` alternative (`pattern_tuple` admits 0 or 2+
//! elements, `pattern_typed` requires `x: T`), so the parenthesized spelling
//! of a single unannotated binder was a SYNTAX error — in rule bodies and
//! requires/ensures alike (the WI's "rule bodies accept both spellings" was
//! stale; only the bare/tuple/typed forms parsed). Fixed by a grammar
//! `pattern_paren` grouping node (`(p)` = `p`, NOT a 1-tuple) admitted in
//! every pattern position, which the converter unwraps to the inner pattern.
//!
//! The eval assertions are arithmetic-free on purpose: this harness
//! (`load_kb_with` + `Interpreter::new`) registers no eval builtins, so any
//! `+` would die `UnknownOperation("add")` regardless of grouping. Binding
//! transparency doesn't need arithmetic; a test that does should build its
//! interpreter via `common::interp_for` (which registers
//! `register_standard_builtins`) instead.
//!
//! The grammar/parse side is exercised in
//! `tree-sitter-anthill/test/corpus/expressions.txt`.

use anthill_core::eval::{Interpreter, Value};
use crate::common::{load_kb_with, try_load_kb_with};

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

fn call_ints(src: &str, calls: &[(&str, i64)]) {
    let kb = load_kb_with(src);
    let mut interp = Interpreter::new(kb);
    for (op, expected) in calls {
        let result = interp
            .call(op, &[])
            .unwrap_or_else(|e| panic!("call {op}: {e:?}"));
        assert_eq!(expect_int(result), *expected, "{op}");
    }
}

/// Grouping is semantically transparent, all the way through eval: a grouped
/// bare binder, a grouped typed binder, and a grouped tuple all bind exactly
/// like their unparenthesized forms (a wrap-as-1-tuple regression would
/// change the results, not just the tree shape).
#[test]
fn paren_binders_bind_and_apply() {
    let src = r#"
namespace test.wi620.eval
  import anthill.prelude.{Int64, Function}

  operation call_bare() -> Int64 =
    let f = lambda (x) -> x
    f(5)

  operation call_typed() -> Int64 =
    let g = lambda ((y: Int64)) -> y
    g(10)

  operation call_tuple() -> Int64 =
    let h: Function[(Int64, Int64), Int64] = lambda ((a, b)) -> a
    h((100, 200))
end
"#;
    call_ints(src, &[
        ("test.wi620.eval.call_bare", 5),
        ("test.wi620.eval.call_typed", 10),
        ("test.wi620.eval.call_tuple", 100),
    ]);
}

/// Grouping in `match` case position (grouped literal and grouped binder
/// cases) and `let` pattern position evaluates like the bare spellings.
#[test]
fn paren_pattern_in_match_case_and_let_positions() {
    let src = r#"
namespace test.wi620.positions
  import anthill.prelude.{Int64}

  operation pick(n: Int64) -> Int64 =
    match n
      case (0) -> 100
      case (m) -> m

  operation match_lit() -> Int64 = pick(0)
  operation match_bind() -> Int64 = pick(7)

  operation let_group() -> Int64 =
    let (k) = 3
    k
end
"#;
    call_ints(src, &[
        ("test.wi620.positions.match_lit", 100),
        ("test.wi620.positions.match_bind", 7),
        ("test.wi620.positions.let_group", 3),
    ]);
}

/// The WI repro positions: a parenthesized-binder lambda as a call argument
/// in `requires`, `ensures`, and a rule body — one source, one load.
#[test]
fn paren_binder_lambda_in_contract_and_rule_positions_loads() {
    let src = r#"
namespace test.wi620.logic
  import anthill.prelude.{Int64, Bool, List, Function}

  operation is_pos(n: Int64) -> Bool = n > 0
  operation all_match(xs: List[T = Int64], p: Function[Int64, Bool]) -> Bool = true

  operation f(xs: List[T = Int64]) -> Bool
    requires all_match(xs, lambda (x) -> is_pos(x))
    ensures all_match(xs, lambda (x) -> is_pos(x))

  rule all_pos(?xs) :- all_match(?xs, lambda (x) -> is_pos(x))
end
"#;
    let errs = try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.is_empty(),
        "parenthesized lambda binder in requires/ensures/rule-body must load; got: {errs:?}",
    );
}

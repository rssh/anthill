//! WI-426: named-argument OPERATION calls.
//!
//! A body call passing arguments by name — `two(b: …, a: …)` — was broken two
//! ways. (1) TYPER: the named-arg label is interned at parse as a use-site
//! symbol, distinct from the callee's scoped, resolved param symbol; the typer
//! matched them by symbol IDENTITY, so every named argument was silently
//! dropped (no unification, no validation) and a cross-parameter projection
//! receiver passed by name (`check(s: w, k: s.cell.T-typed)`) reported its
//! receiver "is not an argument-bound parameter". (2) EVAL: `start_apply`
//! discards labels and binds args positionally in SOURCE order, delegating
//! ordering to the typer — but the typer never reordered, so `two(b: 1, a: 2)`
//! bound `a := 1` at runtime.
//!
//! Fix: match named args to params by NAME (`match_named_arg_param`) and, in the
//! typed node eval consumes, reorder named args into parameter declaration order
//! (`reorder_named_args_in_apply`). Constructor named args already worked (eval's
//! `start_constructor` preserves labels), so this only touches operation calls.

use anthill_core::eval::{Interpreter, Value};
use crate::common::{interp_for, try_load_kb_with};

fn load_errors(source: &str) -> Vec<String> {
    match try_load_kb_with(source) {
        Ok(_) => vec![],
        Err(errs) => errs,
    }
}

fn expect_int(v: Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

// ── Type-checking ──────────────────────────────────────────────────

/// A no-projection op called entirely by name, in REVERSE order, type-checks —
/// the WI probe (`two(a, b)` called `two(b: …, a: …)`).
#[test]
fn named_arg_op_call_typechecks() {
    let src = r#"
namespace test.wi426.ok
  import anthill.prelude.Int64
  operation two(a: Int64, b: Int64) -> Int64 = a
  operation caller(a: Int64, b: Int64) -> Int64 = two(b: b, a: a)
end
"#;
    assert!(
        load_errors(src).is_empty(),
        "two(b: b, a: a) must type-check, got: {:?}",
        load_errors(src),
    );
}

/// The match is REAL: a wrong-typed named argument is REJECTED, proving the arg
/// is validated against its param and not silently dropped.
#[test]
fn named_arg_wrong_type_is_rejected() {
    let src = r#"
namespace test.wi426.wrong
  import anthill.prelude.{Int64, String}
  operation two(a: Int64, b: Int64) -> Int64 = a
  operation caller() -> Int64 = two(a: "nope", b: 5)
end
"#;
    assert!(
        !load_errors(src).is_empty(),
        "a String passed for the Int64 param `a` by name must be rejected",
    );
}

/// CROSS-PARAMETER projection with the receiver passed BY NAME — the path
/// WI-398 review found blocked. `k : s.cell.T` resolves to `String` once `s`'s
/// argument type is found by name, so `k: "abc"` conforms.
#[test]
fn cross_param_projection_receiver_by_name_conforms() {
    let src = r#"
namespace test.wi426.proj
  import anthill.prelude.String
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation check(s: Wrapper, k: s.cell.T) -> String
  operation caller(w: Wrapper[P = Inner[T = String]]) -> String = check(s: w, k: "abc")
end
"#;
    assert!(
        load_errors(src).is_empty(),
        "check(s: w, k: \"abc\") with the projection receiver passed by name must conform, got: {:?}",
        load_errors(src),
    );
}

/// The projection-by-name is REAL: a wrong argument for the projected param is
/// rejected (`k : s.cell.T` is `String`, so `k: 42` must fail).
#[test]
fn cross_param_projection_receiver_by_name_wrong_arg_rejected() {
    let src = r#"
namespace test.wi426.proj_wrong
  import anthill.prelude.{String, Int64}
  sort Inner
    sort T = ?
    entity inner(v: T)
  end
  sort Wrapper
    sort P = ?
    entity wrap(cell: P)
  end
  operation check(s: Wrapper, k: s.cell.T) -> String
  operation caller(w: Wrapper[P = Inner[T = String]]) -> String = check(s: w, k: 42)
end
"#;
    assert!(
        !load_errors(src).is_empty(),
        "k : s.cell.T is String, so k: 42 (by name) must be rejected",
    );
}

// ── Eval (runtime binding order) ───────────────────────────────────

/// `two(a, b) = a` returns the FIRST param. Called all-named in REVERSE order,
/// the value labelled `a` must bind to param `a`.
#[test]
fn eval_all_named_reversed_binds_by_name() {
    let mut interp: Interpreter = interp_for(
        r#"
namespace test.wi426.eval1
  import anthill.prelude.Int64
  operation two(a: Int64, b: Int64) -> Int64 = a
  operation main() -> Int64 = two(b: 100, a: 200)
end
"#,
    );
    let r = interp.call("test.wi426.eval1.main", &[]).expect("call main");
    assert_eq!(expect_int(r), 200, "named arg a: 200 must bind to param a");
}

/// A POSITIONAL prefix plus a reordered named tail binds correctly:
/// `pick(a, b, c) = b`, called `pick(1, c: 3, b: 2)` ⇒ 2.
#[test]
fn eval_positional_prefix_plus_named_tail() {
    let mut interp: Interpreter = interp_for(
        r#"
namespace test.wi426.eval2
  import anthill.prelude.Int64
  operation pick(a: Int64, b: Int64, c: Int64) -> Int64 = b
  operation main() -> Int64 = pick(1, c: 3, b: 2)
end
"#,
    );
    let r = interp.call("test.wi426.eval2.main", &[]).expect("call main");
    assert_eq!(expect_int(r), 2, "named arg b: 2 must bind to param b");
}

const SIBLING_SRC: &str = r#"
namespace test.wi426.sib
  import anthill.prelude.{List, Int64, Bool, Stream, Iterable, Option}
  import anthill.prelude.List.{nil, cons}
  import anthill.prelude.Iterable.{find}
  import anthill.prelude.FiniteCollection.{size}
  sort IntBag
    import anthill.prelude.{List, Int64, Stream, Iterable, FiniteCollection, FiniteStream}
    entity ibag(items: List[T = Int64])
    provides Iterable[C = IntBag, Element = Int64, E = {}]
    operation iterator(b: IntBag) -> Stream[T = Int64, E = {}] = b.items
    -- WI-589: finite, so it also provides FiniteCollection (size moved there).
    provides FiniteCollection[C = IntBag, Element = Int64, E = {}]
    operation collect(b: IntBag) -> List[T = Int64] = b.items
  end
  operation big(n: Int64) -> Bool = n > 1
  operation mk() -> IntBag =
    ibag(items: cons(head: 1, tail: cons(head: 2, tail: cons(head: 3, tail: nil))))
  operation bag_size_byname(b: IntBag) -> Int64 = size(c: b)
  operation bag_find_byname(b: IntBag) -> Int64 =
    match find(c: b, pred: big)
      case some(v) -> v
      case none() -> 0 - 1
end
"#;

/// A carrier-param SPEC op (`FiniteCollection.size`) AND a higher-order spec op
/// (`Iterable.find`, callback also by name) called with the carrier passed BY
/// NAME type-check and evaluate. Before WI-426 the dispatch helpers
/// (`carrier_param_receiver` / `dispatched_impl_effects` / the HOF hint path)
/// matched the carrier param by symbol identity, so the named form failed to
/// derive the carrier — the access effect row `E` leaked as `?_`.
#[test]
fn carrier_param_spec_op_by_name_typechecks_and_evaluates() {
    assert!(
        load_errors(SIBLING_SRC).is_empty(),
        "size(c: b) / find(c: b, pred: big) must type-check, got: {:?}",
        load_errors(SIBLING_SRC),
    );
    let mut interp = interp_for(SIBLING_SRC);
    let b = interp.call("test.wi426.sib.mk", &[]).expect("mk");
    let n = interp
        .call("test.wi426.sib.bag_size_byname", &[b.clone()])
        .expect("size(c: b)");
    assert_eq!(expect_int(n), 3, "size(c: b) over a 3-element bag");
    let f = interp
        .call("test.wi426.sib.bag_find_byname", &[b])
        .expect("find(c: b, pred: big)");
    assert_eq!(expect_int(f), 2, "find(c: b, pred: big) → first element > 1");
}

/// COVERAGE: a label naming NO parameter is a loud error, not a silent drop
/// (a silent drop would let the reorder rebind an omitted param at eval).
#[test]
fn unknown_named_label_is_rejected() {
    let src = r#"
namespace test.wi426.unknown
  import anthill.prelude.Int64
  operation two(a: Int64, b: Int64) -> Int64 = a
  operation caller() -> Int64 = two(a: 1, zzz: 2)
end
"#;
    let errs = load_errors(src);
    assert!(
        errs.iter().any(|e| e.contains("zzz")),
        "an unknown named label must be a loud error, got: {errs:?}",
    );
}

/// COVERAGE: a label that duplicates a positionally-bound parameter is rejected
/// (otherwise the duplicate would silently shift later bindings).
#[test]
fn named_label_duplicating_positional_is_rejected() {
    let src = r#"
namespace test.wi426.dup
  import anthill.prelude.Int64
  operation two(a: Int64, b: Int64) -> Int64 = a
  operation caller() -> Int64 = two(7, a: 1)
end
"#;
    let errs = load_errors(src);
    assert!(
        !errs.is_empty(),
        "a named label duplicating a positionally-bound param must be rejected",
    );
}

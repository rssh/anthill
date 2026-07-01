//! WI-604 (finiteness): a qualified `Iterable` consumer (`isEmpty` / `find`)
//! over a bare lazy `Iterable.map(...)` result must GROUND the produced stream's
//! access row to `{}` instead of leaking it as `s.E`.
//!
//! `Iterable.map(xs, inc)` on a pure `List` returns a bare `Stream[T=Int64, E={}]`
//! (a `MappedStream` value with a written pure row). `Iterable.isEmpty` / `find`
//! are DEFAULTED spec ops (they have bodies), so consuming them on that Stream
//! value dispatches (WI-444) to Stream's own `isEmpty` / `find` override, whose
//! effect is the self-receiver projection `effects s.E`. Before WI-604,
//! `dispatched_impl_effects` blanket-re-keyed that projection without δ-reducing
//! it, so `s.E` survived un-grounded and the pure consumer was rejected with
//! `type mismatch: expected declared [], got undeclared effect: s.E`. WI-604
//! δ-reduces the override's projection against the receiver's concrete type
//! (`s.E` off `Stream[E={}]` → `{}`), so the consumer type-checks PURE.

use anthill_core::eval::{Interpreter, Value};

fn run_int(interp: &mut Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

fn run_bool(interp: &mut Interpreter, op: &str) -> bool {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        Value::Bool(b) => b,
        other => panic!("call {op}: expected Bool, got {other:?}"),
    }
}

/// The generic consumers `empty_of` / `find_of` (over a `List` PARAM, so the
/// produced `Iterable.map` stream is a bare `Stream[E={}]`) declare NO effects.
/// Merely LOADING them proves the access row grounded to `{}` — before WI-604
/// this raised `undeclared effect: s.E`. The eval callers confirm the dispatch
/// still runs end to end on a concrete `MappedStream`:
/// `[1,2,3,4] -map(+1)-> [2,3,4,5]` is non-empty (`isEmpty = false`), and
/// `find(> 2)` over it returns the first match `3`.
#[test]
fn iterable_isempty_and_find_over_lazy_map_ground_to_pure() {
    let src = r#"
namespace test.wi604
  import anthill.prelude.{List, Int64, Bool, Option, Stream, Iterable}
  import anthill.prelude.Option.{some, none}

  operation inc(n: Int64) -> Int64 = n + 1
  operation is_big(n: Int64) -> Bool = n > 2

  -- PURE (no `effects` clause): isEmpty / find over a bare lazy MappedStream.
  -- Loading these IS the regression assertion (pre-WI-604: `undeclared s.E`).
  operation empty_of(xs: List[T = Int64]) -> Bool =
    Iterable.isEmpty(Iterable.map(xs, inc))
  operation find_of(xs: List[T = Int64]) -> Option[Int64] =
    Iterable.find(Iterable.map(xs, inc), is_big)

  operation unwrap_or_zero(o: Option[Int64]) -> Int64 =
    match o
      case some(x) -> x
      case none() -> 0

  -- eval callers over a concrete list (the MappedStream materializes at runtime).
  operation empty_eval() -> Bool = empty_of([1, 2, 3, 4])
  operation find_eval() -> Int64 = unwrap_or_zero(find_of([1, 2, 3, 4]))
end
"#;
    // interp_for panics on load/typecheck failure — reaching eval proves the two
    // pure consumers type-checked (the access row grounded to `{}`).
    let mut interp = crate::common::interp_for(src);
    // [1,2,3,4] -map(inc)-> [2,3,4,5]: non-empty.
    assert!(!run_bool(&mut interp, "test.wi604.empty_eval"));
    // find(> 2) over [2,3,4,5]: first match is 3.
    assert_eq!(run_int(&mut interp, "test.wi604.find_eval"), 3);
}

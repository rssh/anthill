//! WI-411 — an UNQUALIFIED self-named spec-op call inside a provider's OWN impl
//! must value-dispatch on the receiver's runtime carrier, not statically
//! self-dispatch to the enclosing impl.
//!
//! Repro: a lazy carrier `Rewrap` that `provides Stream` by defining `splitFirst`
//! over its source. The source peel `splitFirst(src)` is UNQUALIFIED and its
//! receiver `src` is the abstract source `Stream`. Before WI-411 the unqualified
//! call self-dispatched to `Rewrap.splitFirst` (its `case rewrapped` arm), so a
//! `List` source's `cons` hit the wrong arm → `MatchFailed`; it must instead
//! value-dispatch on `src`'s real carrier (`List.splitFirst`). The typecheck alone
//! did NOT catch the original bug (the signatures are compatible) — only eval did,
//! so this is an eval test.
//!
//! The fix routes the unqualified function-call form like the dot form
//! (`src.splitFirst`): the typer redirects it to the spec op `Stream.splitFirst`
//! when the receiver is not the enclosing carrier, and the existing dispatch
//! value-dispatches it. A receiver that IS the enclosing carrier keeps a static
//! self-call (covered by `wi413_lazy_filter_skips_via_self_recursion`).

use anthill_core::eval::Interpreter;

fn expect_int(v: anthill_core::eval::Value) -> i64 {
    v.as_int().unwrap_or_else(|| panic!("expected Int64, got {v:?}"))
}

// A lazy identity carrier (`map` without the transform): wraps a source Stream and
// re-exposes its elements verbatim. The source peel `splitFirst(src)` is the bare
// spec op (WI-411). Shapes mirror the proven `wi413` `Rec` carrier (explicit
// `[Elem, Eff]` params bound from the receiver `Rewrap[T = Elem, E = Eff]`).
const REWRAP: &str = r#"
sort test.wi411.Rewrap
  import anthill.prelude.{Stream, Option, Pair, List, Int64, EffectsRuntime}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Pair.{pair}

  sort T = ?
  effects E = ?
  entity rewrapped(source: Stream[T = T, E = E])
  provides Stream[T = T, E = E]

  -- WI-411: UNQUALIFIED self-named spec-op call on the ABSTRACT source `src`.
  operation splitFirst[Elem, Eff](r: Rewrap[T = Elem, E = Eff]) -> Option[T = Pair[A = Elem, B = Rewrap[T = Elem, E = Eff]]] effects Eff =
    match r
      case rewrapped(src) ->
        match splitFirst(src)
          case none() -> none
          case some(pair(h, rest)) -> some(pair(h, rewrapped(rest)))

  operation rewrap[Elem, Eff](s: Stream[T = Elem, E = Eff]) -> Stream[T = Elem, E = Eff] = rewrapped(s)
end
"#;

#[test]
fn unqualified_source_peel_value_dispatches_on_list() {
    let src = r#"
namespace test.wi411.use
  import anthill.prelude.{List, Int64, Stream}
  import anthill.prelude.List.{nil, cons}
  import anthill.prelude.Stream.{collect, foldLeft}
  import test.wi411.Rewrap.{rewrap}

  operation addp(a: Int64, b: Int64) -> Int64 = a + b

  operation encode3(xs: List[T = Int64]) -> Int64 =
    match xs
      case cons(a, cons(b, cons(c, _))) -> a * 100 + b * 10 + c
      case _ -> 0

  -- rewrap([1,2,3]) is a Stream that re-exposes [1,2,3] verbatim. collect peels
  -- via the carrier's UNQUALIFIED splitFirst(src), which must value-dispatch on the
  -- List source ⇒ [1,2,3] ⇒ 123; folded ⇒ 6; empty ⇒ 0.
  operation rewrapped_collect() -> Int64 = encode3(collect(rewrap[Elem = Int64, Eff = {}]([1, 2, 3])))
  operation rewrapped_sum() -> Int64 = foldLeft(rewrap[Elem = Int64, Eff = {}]([1, 2, 3]), 0, addp)
  operation rewrapped_empty() -> Int64 = foldLeft(rewrap[Elem = Int64, Eff = {}]([]), 0, addp)
end
"#;
    let mut interp = crate::common::interp_for(&format!("{REWRAP}\n{src}"));
    let run = |interp: &mut Interpreter, op: &str| {
        expect_int(interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")))
    };
    // The acceptance: the unqualified source peel value-dispatches on the List
    // carrier rather than self-dispatching to Rewrap.splitFirst (a MatchFailed).
    assert_eq!(run(&mut interp, "test.wi411.use.rewrapped_collect"), 123);
    assert_eq!(run(&mut interp, "test.wi411.use.rewrapped_sum"), 6);
    assert_eq!(run(&mut interp, "test.wi411.use.rewrapped_empty"), 0);
}

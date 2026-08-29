//! WI-439: `filter` lifted onto `Iterable`, deriving via `iterator(c)` — the
//! sibling of the WI-424 `find`/`map` members. The body returns the lazy
//! `filtered` carrier (FilteredStream provides Stream), so the keep/drop walk
//! and its laziness are the delivered WI-410/413 engine; these tests pin the
//! Iterable-level derivation: typecheck (pure / wrong-element rejected), eval
//! keep/drop, a non-Stream carrier reached only through Iterable, and parity
//! with the erasing Stream-level spelling `Iterable.filter` (which was
//! `FilteredStream.filter` until WI-20260829-X13YV re-typed that one onto a
//! `FilteredStream` receiver — see the parity test's own note).

/// Call a nullary op and expect an Int result.
fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp
        .call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
    {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// `Iterable.filter` on a List typechecks PURE and keeps the element type:
/// the collected result is `List[Int64]`.
#[test]
fn iterable_filter_on_list_typechecks_pure() {
    let src = r#"
namespace test.wi439.filter_list
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.FiniteCollection.{filter, collect}
  operation is_big(n: Int64) -> Bool = n > 2
  operation keep_big(xs: List[T = Int64]) -> List[T = Int64] = collect(filter(xs, is_big))
end
"#;
    let errs = crate::wi424_iterable_members_test::load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "collect(Iterable.filter(xs, is_big)) must typecheck pure as List[Int64]; got: {errs:?}",
    );
}

/// The element really threads: claiming the collected filter result is
/// `List[String]` is REJECTED.
#[test]
fn iterable_filter_on_list_wrong_element_rejected() {
    let src = r#"
namespace test.wi439.filter_wrong
  import anthill.prelude.{List, Int64, String, Bool}
  import anthill.prelude.FiniteCollection.{filter, collect}
  operation is_big(n: Int64) -> Bool = n > 2
  operation keep_big(xs: List[T = Int64]) -> List[T = String] = collect(filter(xs, is_big))
end
"#;
    let errs = crate::wi424_iterable_members_test::load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "filter on List[Int64] collects to List[Int64]; returning List[String] must be rejected",
    );
}

/// EVAL: keep/drop on a List, including the drop-everything case, plus parity
/// with the Stream-level filter on the same input.
///
/// THE PARITY PARTNER CHANGED, and the reason is worth keeping. It used to be
/// `FilteredStream.filter`, which was then a STATIC CONSTRUCTOR over any `Stream` and so
/// took this `List` directly. WI-20260829-X13YV re-typed it to take a `FilteredStream`
/// receiver and return a carrier built from that input, because as a static constructor
/// it SHADOWED `FiniteCollection.filter` in dot dispatch and broke
/// `xs.filter(p).filter(q)` — see its note in `combinators.anthill`. So it no longer
/// accepts a `List`, and the erasing Stream-level spelling that still does is
/// `Iterable.filter` (`filtered(iterator(c), pred)`), which is the partner here now.
///
/// THE EXPERIMENT IS UNCHANGED: two spellings of the one keep/drop engine, over the same
/// input, must agree on the value — the non-erasing `FiniteCollection.filter` against the
/// erasing Stream-level one. The chaining spelling is driven in
/// `x13yv_map_map_chain_test`, which is where the re-typed operation is exercised.
///
/// The parity op lives in its OWN namespace because the short name `filter` in the main
/// namespace is taken by the FiniteCollection import.
#[test]
fn iterable_filter_eval_on_list_and_stream_parity() {
    let src = r#"
namespace test.wi439.eval
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.List.{cons}
  import anthill.prelude.FiniteCollection.{filter, collect}

  operation is_big(n: Int64) -> Bool = n > 2

  operation encode2(xs: List[T = Int64]) -> Int64 =
    match xs
      case cons(a, cons(b, _)) -> a * 10 + b
      case _ -> 0

  operation kept() -> Int64 = encode2(collect(filter([1, 2, 3, 4], is_big)))
  operation kept_none() -> Int64 = encode2(collect(filter([1, 2], is_big)))
end

namespace test.wi439.parity
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.Iterable.{filter}
  import anthill.prelude.Stream.{takeN}
  import test.wi439.eval.{is_big, encode2}

  -- Stream-level engine on the same input (List provides Iterable); the finite
  -- member must agree. This spelling ERASES the source to a bare `Stream`, so it is
  -- not collect-able (Phase C / WI-589) — drain it with the still-Stream-level
  -- `takeN` (bound >= the list length yields every kept element), which runs the same
  -- keep/drop self-recursion.
  operation kept_stream() -> Int64 = encode2(takeN(filter([1, 2, 3, 4], is_big), 1000))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi439.eval.kept"), 34);
    assert_eq!(run_int(&mut interp, "test.wi439.eval.kept_none"), 0);
    assert_eq!(
        run_int(&mut interp, "test.wi439.parity.kept_stream"),
        run_int(&mut interp, "test.wi439.eval.kept"),
        "FiniteCollection.filter and Iterable.filter must agree on the same input",
    );
}

/// A NON-Stream Iterable carrier (the WI-424 BoxColl shape): `filter` reaches
/// it ONLY through the Iterable member, never through List-provides-Stream.
#[test]
fn iterable_filter_on_non_stream_carrier() {
    let src = r#"
namespace test.wi439.boxcoll
  import anthill.prelude.{List, Int64, Bool, Stream, Iterable}
  import anthill.prelude.List.{cons}
  import anthill.prelude.FiniteCollection.{filter, collect}

  sort BoxColl
    import anthill.prelude.{List, Int64, Stream, Iterable, FiniteCollection, FiniteStream}
    entity boxed(items: List[T = Int64])
    provides Iterable[C = BoxColl, Element = Int64, E = {}]
    operation iterator(b: BoxColl) -> Stream[Int64, {}] =
      match b
        case boxed(items) -> items
    -- WI-589: finite, so also provides FiniteCollection (filter/collect moved there).
    provides FiniteCollection[C = BoxColl, Element = Int64, E = {}]
    operation collect(b: BoxColl) -> List[T = Int64] =
      match b
        case boxed(items) -> items
  end

  operation is_big(n: Int64) -> Bool = n > 2

  operation encode2(xs: List[T = Int64]) -> Int64 =
    match xs
      case cons(a, cons(b, _)) -> a * 10 + b
      case _ -> 0

  -- `filter` over the non-Stream BoxColl resolves FiniteCollection.filter (a
  -- `filtered` carrier over BoxColl), then FiniteCollection.collect — supplied for
  -- it by the FilteredStreamFinite witness — materializes it.
  operation kept() -> Int64 = encode2(collect(filter(boxed([1, 2, 3, 4]), is_big)))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi439.boxcoll.kept"), 34);
}

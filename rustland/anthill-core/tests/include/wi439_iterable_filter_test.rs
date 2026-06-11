//! WI-439: `filter` lifted onto `Iterable`, deriving via `iterator(c)` — the
//! sibling of the WI-424 `find`/`map` members. The body returns the lazy
//! `filtered` carrier (FilteredStream provides Stream), so the keep/drop walk
//! and its laziness are the delivered WI-410/413 engine; these tests pin the
//! Iterable-level derivation: typecheck (pure / wrong-element rejected), eval
//! keep/drop, a non-Stream carrier reached only through Iterable, and parity
//! with the Stream-level `FilteredStream.filter`.

/// Call a nullary op and expect an Int result.
fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
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
  import anthill.prelude.Iterable.{filter}
  import anthill.prelude.Stream.{collect}
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
  import anthill.prelude.Iterable.{filter}
  import anthill.prelude.Stream.{collect}
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
/// with the Stream-level `FilteredStream.filter` on the same input.
///
/// The parity op lives in its OWN namespace: it needs the unqualified
/// `filter[S = …, Eff = …]` form (the eval_test.rs convention) because a
/// QUALIFIED call with explicit type-arg brackets
/// (`FilteredStream.filter[S = …](…)`) does not parse, and the short name
/// `filter` in the main namespace is taken by the Iterable import.
#[test]
fn iterable_filter_eval_on_list_and_stream_parity() {
    let src = r#"
namespace test.wi439.eval
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.List.{cons}
  import anthill.prelude.Iterable.{filter}
  import anthill.prelude.Stream.{collect}

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
  import anthill.prelude.FilteredStream.{filter}
  import anthill.prelude.Stream.{collect}
  import test.wi439.eval.{is_big, encode2}

  -- Stream-level engine on the same input (List provides Stream); the
  -- Iterable member must agree. The direct Stream-level call needs the
  -- explicit bindings; the Iterable member gets E from the provision.
  operation kept_stream() -> Int64 = encode2(collect(filter[S = Int64, EffS = {}, EffP = {}]([1, 2, 3, 4], is_big)))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi439.eval.kept"), 34);
    assert_eq!(run_int(&mut interp, "test.wi439.eval.kept_none"), 0);
    assert_eq!(
        run_int(&mut interp, "test.wi439.parity.kept_stream"),
        run_int(&mut interp, "test.wi439.eval.kept"),
        "Iterable.filter and FilteredStream.filter must agree on the same input",
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
  import anthill.prelude.Iterable.{filter}
  import anthill.prelude.Stream.{collect}

  sort BoxColl
    import anthill.prelude.{List, Int64, Stream, Iterable}
    entity boxed(items: List[T = Int64])
    provides Iterable[C = BoxColl, Element = Int64, E = {}]
    operation iterator(b: BoxColl) -> Stream[Int64, {}] =
      match b
        case boxed(items) -> items
  end

  operation is_big(n: Int64) -> Bool = n > 2

  operation encode2(xs: List[T = Int64]) -> Int64 =
    match xs
      case cons(a, cons(b, _)) -> a * 10 + b
      case _ -> 0

  -- Explicit collect bindings: inference does NOT ground collect's Elem from
  -- a member result whose Element comes from a CONCRETE provision binding
  -- (`Element = Int64`) — the generic List provision (`Element = T`) grounds
  -- fine (see iterable_filter_eval_…). Likely the WI-391 Ref-vs-nullary-Fn
  -- lowering divergence for ground provides bindings; recorded as WI-439
  -- feedback, root-cause with WI-391.
  operation kept() -> Int64 = encode2(collect[Elem = Int64, Eff = {}](filter(boxed([1, 2, 3, 4]), is_big)))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi439.boxcoll.kept"), 34);
}

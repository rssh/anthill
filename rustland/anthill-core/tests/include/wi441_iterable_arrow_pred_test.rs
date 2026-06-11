//! WI-441: the arrow-typed dependent-absence pred form on the Iterable
//! members. `find` carries the DECOUPLED rows (user direction 2026-06-11):
//! `find[EffP](c: C, pred: (x: Element) -> Bool @ {EffP, -Modify[x]})
//! effects {E, EffP}` — the pred's row is its OWN (`EffP`), the op's effect
//! the MERGE of the access row and the pred row. An effectful-but-element-
//! pure pred works on a PURE carrier (List), and its effects THREAD to the
//! caller's boundary (undeclared → loud). The lazy `filter`/`map` stay on
//! the TIED form `{E, -Modify[x]}` (their decoupling needs merge-rows in
//! the result TYPE position — the produced stream pays the pred row on
//! consumption).

fn load_errors(extras: &[&str]) -> Vec<String> {
    crate::wi424_iterable_members_test::load_errors(extras)
}

/// A pred DECLARING `Modify` on its own param is rejected by `Iterable.find`
/// (the `-Modify[x]` lacks-constraint, binder-aligned: pred param 0 ↔ the
/// arrow binder `x`). The declared-but-not-incurred body keeps the probe
/// minimal — the check reads the DECLARED row.
#[test]
fn modifying_pred_rejected_by_find() {
    let src = r#"
namespace wi441.findviol
  import anthill.prelude.{List, Option, Bool, Int64, Cell, Modify}
  import anthill.prelude.Iterable.{find}
  operation touchy(c: Cell[V = Int64]) -> Bool effects Modify[c] = true
  operation boom(xs: List[T = Cell[V = Int64]]) -> Option[T = Cell[V = Int64]] =
    find(xs, touchy)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.iter().any(|e| e.contains("lack") && e.contains("Modify")),
        "a Modify[c]-declaring pred must be rejected by Iterable.find's \
         -Modify[x] lacks-constraint; got: {errs:?}",
    );
}

/// The same violation through `filter` and `map`.
#[test]
fn modifying_pred_rejected_by_filter_and_map() {
    let filter_src = r#"
namespace wi441.filterviol
  import anthill.prelude.{List, Stream, Bool, Int64, Cell, Modify}
  import anthill.prelude.Iterable.{filter}
  operation touchy(c: Cell[V = Int64]) -> Bool effects Modify[c] = true
  operation boom(xs: List[T = Cell[V = Int64]]) -> Stream[Cell[V = Int64], {}] =
    filter(xs, touchy)
end
"#;
    let errs = load_errors(&[filter_src]);
    assert!(
        errs.iter().any(|e| e.contains("lack") && e.contains("Modify")),
        "a Modify[c]-declaring pred must be rejected by Iterable.filter; got: {errs:?}",
    );

    let map_src = r#"
namespace wi441.mapviol
  import anthill.prelude.{List, Stream, Int64, Cell, Modify}
  import anthill.prelude.Iterable.{map}
  operation extract(c: Cell[V = Int64]) -> Int64 effects Modify[c] = 0
  operation boom(xs: List[T = Cell[V = Int64]]) -> Stream[Int64, {}] =
    map[Dst = Int64](xs, extract)
end
"#;
    let errs = load_errors(&[map_src]);
    assert!(
        errs.iter().any(|e| e.contains("lack") && e.contains("Modify")),
        "a Modify[c]-declaring transform must be rejected by Iterable.map; got: {errs:?}",
    );
}

/// THE decoupled-row payoff: an effectful-but-element-pure pred works on a
/// PURE carrier (List) — `EffP := {Beep}` independent of `E := {}` — and the
/// pred's effects THREAD through `find` to the CALLER's boundary: declaring
/// `effects Beep` loads; omitting it is the loud undeclared-effect error.
#[test]
fn effectful_element_pure_pred_threads_to_caller() {
    let declared = r#"
namespace wi441.thread
  import anthill.prelude.{Effect, List, Option, Bool, Int64}
  import anthill.prelude.Iterable.{find}
  sort Beep end
  fact Effect[T = Beep]
  operation noisy(n: Int64) -> Bool effects Beep = true
  operation ok(xs: List[T = Int64]) -> Option[T = Int64] effects Beep = find(xs, noisy)
end
"#;
    let errs = load_errors(&[declared]);
    assert!(
        errs.is_empty(),
        "a Beep pred on a List must typecheck when the caller declares Beep \
         (EffP decoupled from E); got: {errs:?}",
    );

    let undeclared = r#"
namespace wi441.thread2
  import anthill.prelude.{Effect, List, Option, Bool, Int64}
  import anthill.prelude.Iterable.{find}
  sort Beep end
  fact Effect[T = Beep]
  operation noisy(n: Int64) -> Bool effects Beep = true
  operation boom(xs: List[T = Int64]) -> Option[T = Int64] = find(xs, noisy)
end
"#;
    let errs = load_errors(&[undeclared]);
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect") && e.contains("Beep")),
        "the pred's Beep must surface at the CALLER's boundary when \
         undeclared; got: {errs:?}",
    );
}

/// Pure preds keep working end-to-end through the arrow form: the WI-424 /
/// WI-439 suites pin typecheck + eval on List and the BoxColl carrier; this
/// is the smoke double-check that the converted signatures still EVAL.
#[test]
fn pure_pred_eval_smoke() {
    let src = r#"
namespace wi441.eval
  import anthill.prelude.{List, Int64, Option, Bool}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Iterable.{find}
  operation is_big(n: Int64) -> Bool = n > 2
  operation unwrap(o: Option[T = Int64]) -> Int64 =
    match o
      case some(x) -> x
      case none() -> 0 - 1
  operation found() -> Int64 = unwrap(find([1, 2, 3, 4], is_big))
end
"#;
    let mut interp = crate::common::interp_for(src);
    match interp.call("wi441.eval.found", &[]).expect("eval find") {
        anthill_core::eval::Value::Int(3) => {}
        other => panic!("expected Int(3), got {other:?}"),
    }
}

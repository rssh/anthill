//! WI-441: the arrow-typed dependent-absence pred form on the Iterable
//! members — `pred: (x: Element) -> Bool @ {E, -Modify[x]}` on `find` /
//! `filter`, `f: (x: Element) -> Dst @ {E, -Modify[x]}` on `map`.
//!
//! v1 semantics (scope item b, option 2): the pred's row stays TIED to the
//! collection's access row `E` — `{E | -Modify[x]}` — so the form gains
//! MUTATION SAFETY (the WI-440 checking direction rejects a pred that
//! modifies its element) while keeping today's row semantics (a List's
//! `E = {}` still forces an otherwise-pure pred). The decoupled independent
//! pred row + result-row merge is the deferred half (blocked on the
//! WI-440-recorded boundary gaps).

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

/// v1 row-tie documented behavior: on a List (`E = {}`) the pred's row closes
/// to `{ -Modify[x] }`, so an UNRELATED effect is also rejected — the same
/// pure-pred-forced-on-List semantics the Function[…, E] form had, now with a
/// loud row message instead of a silent unify discard. (The decoupled
/// independent pred row is the deferred WI-441 half.)
#[test]
fn unrelated_effect_pred_on_list_rejected_under_v1_row_tie() {
    let src = r#"
namespace wi441.rowtie
  import anthill.prelude.{Effect, List, Option, Bool, Int64, Modify}
  import anthill.prelude.Iterable.{find}
  sort Beep end
  fact Effect[T = Beep]
  operation noisy(n: Int64) -> Bool effects Beep = true
  operation boom(xs: List[T = Int64]) -> Option[T = Int64] = find(xs, noisy)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "a Beep pred on a List (E = {{}}) must be rejected under the v1 \
         row-tie (pred row = {{E | -Modify[x]}} with E := {{}}); got clean load",
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

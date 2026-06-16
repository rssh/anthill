//! WI-424: `find` / `map` lifted onto `Iterable` (the shared read interface),
//! deriving via `iterator(c)` — every Iterable carrier (List, Stream, a future
//! non-Stream carrier) gets them, instead of reaching them only through
//! List-provides-Stream.
//!
//! The abstract member bodies (`Stream.find(iterator(c), pred)` /
//! `mapped(iterator(c), f)`) exercise the abstract-carrier iterator-walk: the
//! sibling `iterator(c)` must thread Iterable's own `Element` / `E` into the
//! produced Stream. The concrete call sites ground `Element`/`E` through the
//! written provisions — `provides Iterable[C = Stream, Element = T, E = E]`, and
//! for a `List` (since WI-495) the COMPOSED transitive view `List provides
//! Stream[T, {}]` ∘ `Stream provides Iterable` ⇒ `{Element = List.T, E = {}}`.

use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

/// Call a nullary op and expect an Int result.
fn run_int(interp: &mut anthill_core::eval::Interpreter, op: &str) -> i64 {
    match interp.call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

pub(crate) fn load_errors(extras: &[&str]) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p)
                .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    for ex in extras {
        parsed.push(parse::parse(ex).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// The stdlib itself (with the Iterable members + written provisions) loads
/// clean — the abstract bodies typecheck.
#[test]
fn stdlib_with_iterable_members_loads_clean() {
    let errs = load_errors(&[]);
    assert!(
        errs.is_empty(),
        "stdlib with Iterable.find/map must load clean; got: {errs:?}",
    );
}

/// `Iterable.find` on a List (via List-provides-Iterable) typechecks PURE and
/// threads the element: the result is `Option[T = Int64]`.
#[test]
fn iterable_find_on_list_typechecks_pure() {
    let src = r#"
namespace test.wi424.find_list
  import anthill.prelude.{List, Int64, Option, Bool}
  import anthill.prelude.Iterable.{find}
  operation is_big(n: Int64) -> Bool = n > 2
  operation first_big(xs: List[T = Int64]) -> Option[T = Int64] = find(xs, is_big)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "Iterable.find on a List must typecheck pure with Option[Int64]; got: {errs:?}",
    );
}

/// The element really threads: claiming the find result is `Option[String]`
/// is REJECTED.
#[test]
fn iterable_find_on_list_wrong_element_rejected() {
    let src = r#"
namespace test.wi424.find_wrong
  import anthill.prelude.{List, Int64, String, Option, Bool}
  import anthill.prelude.Iterable.{find}
  operation is_big(n: Int64) -> Bool = n > 2
  operation first_big(xs: List[T = Int64]) -> Option[T = String] = find(xs, is_big)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.is_empty(),
        "find on List[Int64] is Option[Int64]; returning Option[String] must be rejected",
    );
}

/// `Iterable.map` on a List typechecks: the produced stream collects back to
/// `List[Int64]` in a pure op.
#[test]
fn iterable_map_on_list_typechecks_pure() {
    let src = r#"
namespace test.wi424.map_list
  import anthill.prelude.{List, Int64}
  import anthill.prelude.Iterable.{map}
  import anthill.prelude.Stream.{collect}
  operation inc(n: Int64) -> Int64 = n + 1
  operation bump(xs: List[T = Int64]) -> List[T = Int64] = collect(map[Dst = Int64](xs, inc))
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        errs.is_empty(),
        "collect(Iterable.map(xs, inc)) must typecheck pure as List[Int64]; got: {errs:?}",
    );
}

/// `Iterable.isEmpty` / `Iterable.size` on a List typecheck PURE (List's
/// access row is `{}`) and evaluate — the read observations derived from
/// the iterator alone.
#[test]
fn iterable_is_empty_and_size_on_list() {
    let src = r#"
namespace test.wi424.isempty_list
  import anthill.prelude.{List, Int64, Bool}
  import anthill.prelude.Iterable.{isEmpty, size}

  operation check(xs: List[T = Int64]) -> Bool = isEmpty(xs)
  operation on_empty() -> Int64 = if check([]) then 1 else 0
  operation on_full() -> Int64 = if check([1, 2]) then 1 else 0
  operation count(xs: List[T = Int64]) -> Int64 = size(xs)
  operation size_empty() -> Int64 = count([])
  operation size_three() -> Int64 = count([1, 2, 3])
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi424.isempty_list.on_empty"), 1);
    assert_eq!(run_int(&mut interp, "test.wi424.isempty_list.on_full"), 0);
    assert_eq!(run_int(&mut interp, "test.wi424.isempty_list.size_empty"), 0);
    assert_eq!(run_int(&mut interp, "test.wi424.isempty_list.size_three"), 3);
}

/// `Iterable.foldLeft` / `foldRight` on a List: typecheck pure + EVAL.
/// Non-commutative subtraction separates the two directions (and would
/// catch a swapped tuple order): foldLeft ((0-1)-2)-3 = -6; foldRight
/// 1-(2-(3-0)) = 2.
#[test]
fn iterable_folds_eval_on_list() {
    let src = r#"
namespace test.wi424.folds
  import anthill.prelude.{List, Int64}
  import anthill.prelude.Iterable.{foldLeft, foldRight}

  operation addp(a: Int64, b: Int64) -> Int64 = a + b
  operation subt(a: Int64, b: Int64) -> Int64 = a - b

  operation sum() -> Int64 = foldLeft([1, 2, 3, 4], 0, addp)
  operation sumr() -> Int64 = foldRight([1, 2, 3, 4], 0, addp)
  operation foldl_sub() -> Int64 = foldLeft([1, 2, 3], 0, subt)
  operation foldr_sub() -> Int64 = foldRight([1, 2, 3], 0, subt)
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi424.folds.sum"), 10);
    assert_eq!(run_int(&mut interp, "test.wi424.folds.sumr"), 10);
    assert_eq!(run_int(&mut interp, "test.wi424.folds.foldl_sub"), -6);
    assert_eq!(run_int(&mut interp, "test.wi424.folds.foldr_sub"), 2);
}

/// The folds' decoupled row (WI-441, like find): an effectful-but-element-
/// pure callback works on a PURE carrier (List) — `EffP := {Beep}`
/// independent of `E := {}` — and the callback's effects THREAD to the
/// caller's boundary: declaring `Beep` loads; omitting it is the loud
/// undeclared-effect error.
#[test]
fn iterable_fold_effectful_callback_decoupled_row() {
    let declared = r#"
namespace test.wi424.foldeff
  import anthill.prelude.{Effect, List, Int64}
  import anthill.prelude.Iterable.{foldLeft}
  sort Beep end
  fact Effect[T = Beep]
  operation noisy_add(a: Int64, b: Int64) -> Int64 effects Beep = a + b
  operation ok(xs: List[T = Int64]) -> Int64 effects Beep = foldLeft(xs, 0, noisy_add)
end
"#;
    let errs = load_errors(&[declared]);
    assert!(
        errs.is_empty(),
        "an effectful callback on a pure List must typecheck with the caller \
         declaring Beep (decoupled EffP); got: {errs:?}",
    );

    let undeclared = r#"
namespace test.wi424.foldeff2
  import anthill.prelude.{Effect, List, Int64}
  import anthill.prelude.Iterable.{foldLeft}
  sort Beep end
  fact Effect[T = Beep]
  operation noisy_add(a: Int64, b: Int64) -> Int64 effects Beep = a + b
  operation boom(xs: List[T = Int64]) -> Int64 = foldLeft(xs, 0, noisy_add)
end
"#;
    let errs = load_errors(&[undeclared]);
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect") && e.contains("Beep")),
        "the callback's Beep must surface at the caller's boundary when \
         undeclared; got: {errs:?}",
    );
}

/// PINS the fold-mutation design + the remaining engine gap. DESIGN: the fold
/// callback carries NO `-Modify[x]` lacks (a fold is the run-once terminal
/// consumer — an in-place sweep is legitimate), so a `Modify[c]`-declaring
/// callback must NOT be rejected by a lacks constraint (contrast
/// `find_over_cell_list_rejects_mutating_pred_accepts_reader`). ENGINE GAP
/// (post-WI-442): WI-442 fixed the named-binder→eta-arrow alignment, so a
/// GROUND-effect callback now binds `EffP` from the argument
/// (see `iterable_fold_effectful_callback_decoupled_row`, `EffP := {Beep}`).
/// This case stays LOUD for a SEPARATE reason: the callback's effect
/// `Modify[c]` is DENOTED on the callback's OWN bound parameter `c`, so
/// binding the caller-side row var `EffP` to `{Modify[c]}` would ESCAPE `c`
/// out of the arrow scope — a dependent-effect abstraction the row machinery
/// does not yet perform (proposal 046 / modify-effect-derive territory), not
/// the named-binder issue. When that lands, this test flips: replace it with
/// an eval test of the sweep.
#[test]
fn iterable_fold_mutating_callback_not_lacks_rejected_but_row_gated() {
    let src = r#"
namespace test.wi424.foldmut
  import anthill.prelude.{List, Int64, Cell, Modify}
  import anthill.prelude.Iterable.{foldLeft}

  operation take_and_zero(acc: Int64, c: Cell[V = Int64]) -> Int64 effects Modify[c] =
    let v = Cell.get(c)
    let u = Cell.set(c, 0)
    acc + v

  operation sweep() -> Int64 =
    let xs = [Cell.new(1), Cell.new(2)]
    foldLeft(xs, 0, take_and_zero)
end
"#;
    let errs = load_errors(&[src]);
    assert!(
        !errs.iter().any(|e| e.contains("lack")),
        "a mutating fold callback must NOT be rejected by a lacks constraint \
         (the folds deliberately carry no -Modify[x]); got: {errs:?}",
    );
    assert!(
        errs.iter().any(|e| e.contains("unconstrained") && e.contains("EffP")),
        "the known row-inference gap for a denoted-bearing callback arrow \
         must stay LOUD (unconstrained EffP) until it binds; got: {errs:?}",
    );
}

/// A NON-Stream Iterable carrier: `BoxColl` provides Iterable (with its own
/// `iterator` unwrapping to a List) but does NOT provide Stream — so
/// `find`/`map` reach it ONLY through the Iterable members, never through
/// List-provides-Stream. Typecheck + eval.
#[test]
fn iterable_members_on_non_stream_carrier() {
    let src = r#"
namespace test.wi424.boxcoll
  import anthill.prelude.{List, Int64, Option, Bool, Stream, Iterable}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.Iterable.{find, isEmpty, foldLeft, size}

  sort BoxColl
    import anthill.prelude.{List, Int64, Stream, Iterable}
    entity boxed(items: List[T = Int64])
    provides Iterable[C = BoxColl, Element = Int64, E = {}]
    operation iterator(b: BoxColl) -> Stream[Int64, {}] =
      match b
        case boxed(items) -> items
  end

  operation is_big(n: Int64) -> Bool = n > 2

  operation unwrap(o: Option[T = Int64]) -> Int64 =
    match o
      case some(x) -> x
      case none() -> 0 - 1

  operation found() -> Int64 = unwrap(find(boxed([1, 2, 3, 4]), is_big))
  operation found_none() -> Int64 = unwrap(find(boxed([1, 2]), is_big))
  operation empty_box() -> Int64 = if isEmpty(boxed([])) then 1 else 0
  operation full_box() -> Int64 = if isEmpty(boxed([1])) then 1 else 0
  operation addp(a: Int64, b: Int64) -> Int64 = a + b
  operation box_sum() -> Int64 = foldLeft(boxed([1, 2, 3, 4]), 0, addp)
  operation box_size() -> Int64 = size(boxed([1, 2, 3]))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi424.boxcoll.found"), 3);
    assert_eq!(run_int(&mut interp, "test.wi424.boxcoll.found_none"), -1);
    assert_eq!(run_int(&mut interp, "test.wi424.boxcoll.empty_box"), 1);
    assert_eq!(run_int(&mut interp, "test.wi424.boxcoll.full_box"), 0);
    assert_eq!(run_int(&mut interp, "test.wi424.boxcoll.box_sum"), 10);
    assert_eq!(run_int(&mut interp, "test.wi424.boxcoll.box_size"), 3);
}

/// WI-444: a carrier's OWN member OVERRIDES a DEFAULTED spec op (typeclass
/// default-method semantics — defaults fill gaps, they do NOT shadow).
/// `Counted` declares its own O(1) `size` (stored count 99, deliberately
/// disagreeing with the walk's 3); the Iterable-imported `size` call on a
/// CONCRETE carrier (`counted(…)` literal) is statically PinNow'd to
/// `Counted.size` by the typer. `Plain` (no own `size`) still falls back to the
/// spec's default walk (3) — defaults fire for carriers WITHOUT an override,
/// and the override does not leak across carriers. The ABSTRACT-receiver
/// (eval value-directed) half is covered by
/// [`defaulted_spec_op_override_via_abstract_receiver`].
#[test]
fn iterable_size_carrier_override() {
    let src = r#"
namespace test.wi424.sizedbox
  import anthill.prelude.{List, Int64, Stream, Iterable}
  import anthill.prelude.Iterable.{size}

  sort Counted
    import anthill.prelude.{List, Int64, Stream, Iterable}
    entity counted(items: List[T = Int64], n: Int64)
    provides Iterable[C = Counted, Element = Int64, E = {}]
    operation iterator(b: Counted) -> Stream[Int64, {}] =
      match b
        case counted(items, _) -> items
    operation size(b: Counted) -> Int64 =
      match b
        case counted(_, n) -> n
  end

  -- No own `size` — must keep the spec default (the walk).
  sort Plain
    import anthill.prelude.{List, Int64, Stream, Iterable}
    entity plain(items: List[T = Int64])
    provides Iterable[C = Plain, Element = Int64, E = {}]
    operation iterator(b: Plain) -> Stream[Int64, {}] =
      match b
        case plain(items) -> items
  end

  operation probe() -> Int64 = size(counted([1, 2, 3], 99))
  operation default_still_fires() -> Int64 = size(plain([1, 2, 3]))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(
        run_int(&mut interp, "test.wi424.sizedbox.probe"),
        99,
        "the carrier's own `size` (99) must OVERRIDE the spec default walk (3)",
    );
    assert_eq!(
        run_int(&mut interp, "test.wi424.sizedbox.default_still_fires"),
        3,
        "a carrier WITHOUT its own `size` must still use the spec default walk (3) \
         — defaults fill gaps, the override does not leak to other carriers",
    );
}

/// WI-444 EVAL HALF: a DEFAULTED spec op called on a STATICALLY-ABSTRACT
/// receiver (typed as the bare spec sort) cannot be PinNow'd by the typer, so
/// the override is resolved at runtime from the receiver value's own sort —
/// eval's value-directed `resolve_carrier_override_by_value`, the dynamic dual
/// of the typer's static PinNow. `Describable.describe` has a pure default body
/// returning 0; `Widget` provides `Describable` with its own `describe`
/// returning the stored field. `via_spec(d: Describable)` reads `d` through the
/// abstract interface; calling it with a `Widget` value must run `Widget.describe`
/// (42), NOT the default (0). A pure user spec (no effect param) keeps the
/// abstract call off the orthogonal effect-row-closing path (WI-415..423).
#[test]
fn defaulted_spec_op_override_via_abstract_receiver() {
    let src = r#"
namespace test.wi444.evalhalf
  import anthill.prelude.{Int64}

  sort Describable
    sort T = ?
    operation describe(x: Describable) -> Int64 = 0
  end

  sort Widget
    import anthill.prelude.{Int64}
    entity widget(n: Int64)
    provides Describable[T = Int64]
    operation describe(x: Widget) -> Int64 =
      match x
        case widget(n) -> n
  end

  operation via_spec(d: Describable) -> Int64 = Describable.describe(d)
  operation use_it() -> Int64 = via_spec(widget(42))
  operation default_fires() -> Int64 = via_spec(widget(7))
end
"#;
    let mut interp = crate::common::interp_for(src);
    // The abstract-receiver call dispatches to Widget's own `describe` (the
    // stored field), NOT the spec default (0). If this returns 0, the eval
    // value-directed override did not fire.
    assert_eq!(run_int(&mut interp, "test.wi444.evalhalf.use_it"), 42);
    assert_eq!(run_int(&mut interp, "test.wi444.evalhalf.default_fires"), 7);
}

/// EVAL: Iterable.find / Iterable.map run end-to-end on a List.
#[test]
fn iterable_members_eval_on_list() {
    let src = r#"
namespace test.wi424.eval
  import anthill.prelude.{List, Int64, Option, Bool}
  import anthill.prelude.Option.{some, none}
  import anthill.prelude.List.{cons}
  import anthill.prelude.Iterable.{find, map}
  import anthill.prelude.Stream.{collect}

  operation is_big(n: Int64) -> Bool = n > 2
  operation inc(n: Int64) -> Int64 = n + 1

  operation unwrap(o: Option[T = Int64]) -> Int64 =
    match o
      case some(x) -> x
      case none() -> 0 - 1

  operation encode3(xs: List[T = Int64]) -> Int64 =
    match xs
      case cons(a, cons(b, cons(c, _))) -> a * 100 + b * 10 + c
      case _ -> 0

  operation found() -> Int64 = unwrap(find([1, 2, 3, 4], is_big))
  operation found_none() -> Int64 = unwrap(find([1, 2], is_big))
  operation mapped_inc() -> Int64 = encode3(collect(map[Dst = Int64]([1, 2, 3], inc)))
end
"#;
    let mut interp = crate::common::interp_for(src);
    assert_eq!(run_int(&mut interp, "test.wi424.eval.found"), 3);
    assert_eq!(run_int(&mut interp, "test.wi424.eval.found_none"), -1);
    assert_eq!(run_int(&mut interp, "test.wi424.eval.mapped_inc"), 234);
}

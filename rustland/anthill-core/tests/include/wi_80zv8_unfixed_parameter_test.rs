//! WI-20261001-80ZV8, stage (c), part 5 — A PARAMETER THE CALL LEFT UNFIXED FILLS NO SLOT.
//!
//! `operation empty() -> Self` is `-> List[T = T]`, and a call fixes `T` by its bracket, its
//! arguments or the expected type (proposal 070 §1.1). This file is about the call where
//! none of them does. The user's answer (2026-10-03, option (a) of three): THE SLOT STAYS
//! OPEN IN THE RESULT, as it was while the declaration read `-> List` — the element is not
//! said, and whatever the value meets says it.
//!
//! Before this, written `Self`, such a call returned the callee's own open variable, which
//! a branch join refuses: `match xs  case nil() -> List.empty()  case cons(_, _) -> ys` was
//! `match.rule: expected List[T = ?_], got List[T = Int64]`, and the anthill-todo program,
//! which has that shape, did not load (264 tests) — so the stdlib's seven receiver-less
//! operations could not be written with `Self` at all. They are now.
//!
//! Every row that can RUNS and names its value; a row about the result's TYPE reads it out
//! of a refusal that prints it.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED (2026-10-03), each part present but disabled, over this file's 9 rows:
//!
//! 1. THE SLOT LEFT OPEN (typing/slots.rs `leave_unfixed_slots_open`, returning the type it
//!    was given). 5 FAIL:
//!    [`a_call_that_fixes_nothing_joins_with_the_instance_it_meets`] (`match.rule (rule):
//!    expected Bag[T = ?_], got Bag[T = Int64]`), [`the_result_names_no_element`] (`got
//!    Bag[T = ?_]`), [`an_unfixed_effect_row_slot_is_left_open_too`],
//!    [`a_fixed_parameter_keeps_its_slot`] (`got Duo[A = Int64, B = ?_]`) and
//!    [`the_stdlibs_receiverless_constructors_join`] (both of its `match`es refused).
//! 2. UNFIXED IS "NOTHING BOUND IT" (the same function, reading a parameter as unfixed
//!    wherever the chain it is bound into ENDS at a variable). No row of this file fails; the
//!    rows that do are `wi_0rp29_review9_regressions_test`'s
//!    `a_receiverless_call_in_a_lambda_is_typed_by_its_argument` and
//!    `a_receiverless_call_through_a_callback_is_typed_by_its_argument` — a parameter bound
//!    to the CALLER's open variable lost its slot, and `g(7)` passed for a `String`.
//! 3. A CONSTRUCTOR IS NOT A RECEIVER (typing/constructor.rs
//!    `bare_spec_arg_self_projection`'s gate, removed). 1 FAILS:
//!    [`a_receiverless_constructor_over_nil_is_written_with_self`] — `expected Bag[T = ?T],
//!    got Bag[T = nil.T]`.
//!
//! Three pass under every part by design and say so at their sites:
//! [`a_call_that_fixes_the_parameter_names_it`],
//! [`a_parameter_in_another_sorts_slot_is_left_as_it_was`] and
//! [`an_open_slot_is_not_an_inference_variable`].

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

/// `Bag` with a receiver-less `empty() -> Self`; `rest` is what follows the sort.
fn bag_program(ns: &str, rest: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  import anthill.prelude.List.{{nil, cons}}
  sort Bag
    sort T = ?
    entity bag(items: List[T = T])
    operation empty() -> Self = bag(items: [])
    operation add(b: Self, x: T) -> Self =
      match b
        case bag(items) -> bag(items: cons(head: x, tail: items))
    operation size(b: Self) -> Int64 =
      match b
        case bag(items) -> List.length(items)
  end
{rest}
end
"#
    )
}

/// THE CALL JOINS WITH THE INSTANCE IT MEETS. The first arm of the `match` has no expected
/// type, so nothing fixes `Bag.empty()`'s `T`; the second arm is a `Bag[T = Int64]`. The
/// two join, and the program runs both ways round: 1 element after adding to the empty
/// bag, 2 after adding to the one handed in.
#[test]
fn a_call_that_fixes_nothing_joins_with_the_instance_it_meets() {
    let src = bag_program(
        "wi80zv8u.a1",
        r#"  operation pick(xs: List[T = Int64], ys: Bag[T = Int64]) -> Int64 =
    let known = match xs
      case nil() -> Bag.empty()
      case cons(_, _) -> ys
    Bag.size(Bag.add(known, 5))
  operation go() -> Int64 =
    pick([], Bag.add(Bag.empty(), 1)) * 10 + pick([7], Bag.add(Bag.empty(), 1))"#,
    );
    assert_eq!(run_src(&src, "wi80zv8u.a1.go"), Ok(12));
}

/// THE RESULT NAMES NO ELEMENT. Read out of a refusal that prints it: `Bag.empty()` where
/// an `Int64` is wanted is `got Bag`, not `got Bag[T = ?_]` — the callee's variable is not
/// in the caller's type.
#[test]
fn the_result_names_no_element() {
    let errs = load_errors(&bag_program(
        "wi80zv8u.a2",
        "  operation bad() -> Int64 = Bag.empty()",
    ));
    assert_refused_naming(&errs, &["expected Int64, got Bag"], "`Bag.empty()` as an Int64");
    assert!(
        !errs.join(" | ").contains("Bag["),
        "the result must name no slot, got: {errs:?}"
    );
}

/// AN EFFECT-ROW PARAMETER IS A PARAMETER: `Flow.nothing() -> Self` in a sort with `sort T`
/// and `effects E` leaves both unfixed, and the result names neither — `got Flow` — so it
/// joins with a `Flow[T = Int64, E = {}]`.
#[test]
fn an_unfixed_effect_row_slot_is_left_open_too() {
    let program = |ns: &str, rest: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, List}}
  import anthill.prelude.List.{{nil, cons}}
  sort Flow
    sort T = ?
    effects E = ?
    entity flow(n: Int64)
    operation nothing() -> Self = flow(n: 0)
    operation count(f: Self) -> Int64 =
      match f
        case flow(n) -> n
  end
{rest}
end
"#
        )
    };
    let errs = load_errors(&program(
        "wi80zv8u.f1",
        "  operation bad() -> Int64 = Flow.nothing()",
    ));
    assert_refused_naming(&errs, &["expected Int64, got Flow"], "`Flow.nothing()` as an Int64");
    assert!(
        !errs.join(" | ").contains("Flow["),
        "the result must name no slot, got: {errs:?}"
    );

    let joined = program(
        "wi80zv8u.f2",
        r#"  operation pick(xs: List[T = Int64], f: Flow[T = Int64, E = {}]) -> Int64 =
    let known = match xs
      case nil() -> Flow.nothing()
      case cons(_, _) -> f
    Flow.count(known)
  operation go() -> Int64 = pick([], flow(n: 5)) * 10 + pick([1], flow(n: 5))"#,
    );
    assert_eq!(run_src(&joined, "wi80zv8u.f2.go"), Ok(5));
}

/// ONLY THE PARAMETER NOTHING FIXED. `Duo.left(1)` fixes `A` by its argument and says
/// nothing of `B`: the result is a `Duo[A = Int64]`. It joins with a `Duo[A = Int64, B =
/// String]` and runs, and is refused beside a `Duo[A = String, …]` — the slot the call
/// bound is the call's.
#[test]
fn a_fixed_parameter_keeps_its_slot() {
    let program = |ns: &str, rest: &str| {
        format!(
            r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List}}
  import anthill.prelude.List.{{nil, cons}}
  sort Duo
    sort A = ?
    sort B = ?
    entity duo(l: A)
    operation left(a: A) -> Self = duo(l: a)
    operation leftOf(d: Self) -> A =
      match d
        case duo(a) -> a
  end
{rest}
end
"#
        )
    };
    assert_refused_naming(
        &load_errors(&program("wi80zv8u.b1", "  operation bad() -> Int64 = Duo.left(1)")),
        &["expected Int64, got Duo[A = Int64]"],
        "`Duo.left(1)` as an Int64",
    );

    let joined = program(
        "wi80zv8u.b2",
        r#"  operation pick(xs: List[T = Int64], d: Duo[A = Int64, B = String]) -> Int64 =
    let known = match xs
      case nil() -> Duo.left(4)
      case cons(_, _) -> d
    Duo.leftOf(known)
  operation go() -> Int64 = pick([], Duo.left(9)) * 10 + pick([1], Duo.left(9))"#,
    );
    assert_eq!(run_src(&joined, "wi80zv8u.b2.go"), Ok(49));

    assert_refused_naming(
        &load_errors(&program(
            "wi80zv8u.b3",
            r#"  operation pick(xs: List[T = Int64], d: Duo[A = String, B = String]) -> Int64 =
    let known = match xs
      case nil() -> Duo.left(4)
      case cons(_, _) -> d
    0"#,
        )),
        &["match.rule (rule): expected Duo[A = Int64], got Duo[A = String, B = String]"],
        "a `Duo` whose `A` the call fixed, beside one of another `A`",
    );
}

/// A RECEIVER-LESS CONSTRUCTOR OVER `nil` CAN BE WRITTEN WITH `Self`. `empty() -> Self =
/// bag(items: nil)` builds its value from a constant whose type says nothing of the element;
/// the constructor used to name that element `nil.T` — a projection off a constant, which
/// nothing can ever resolve — and the declared `Bag[T = T]` did not admit it: `expected
/// Bag[T = ?T], got Bag[T = nil.T]`. Only the bare `-> Bag`, which claims nothing, loaded.
/// The slot is left open now, as it is for `bag(items: [])`, and the program runs.
#[test]
fn a_receiverless_constructor_over_nil_is_written_with_self() {
    let src = r#"
namespace wi80zv8u.n1
  import anthill.prelude.{Int64, List, Option}
  import anthill.prelude.List.{nil, cons}
  import anthill.prelude.Option.{some, none}
  sort Bag
    sort T = ?
    entity bag(items: List[T = T])
    operation empty() -> Self = bag(items: nil)
    operation add(b: Self, x: T) -> Self =
      match b
        case bag(items) -> bag(items: cons(head: x, tail: items))
    operation size(b: Self) -> Int64 =
      match b
        case bag(items) -> List.length(items)
  end
  sort Maybe
    sort T = ?
    entity maybe(v: Option[T = T])
    operation nothing() -> Self = maybe(v: none)
    operation orElse(m: Self, dflt: T) -> T =
      match m
        case maybe(some(v)) -> v
        case maybe(none()) -> dflt
  end
  operation go() -> Int64 = Bag.size(Bag.add(Bag.empty(), 4)) * 10 + Maybe.orElse(Maybe.nothing(), 3)
end
"#;
    assert_eq!(run_src(src, "wi80zv8u.n1.go"), Ok(13));
}

/// CONTROL — the three ways a call DOES fix the parameter still do, and the result then
/// names it: the expected type, the bracket in either spelling. Each prints `Bag[T =
/// Int64]` where a `String` is wanted. Passes with or without the change by design.
#[test]
fn a_call_that_fixes_the_parameter_names_it() {
    for (ns, call) in [
        ("wi80zv8u.c1", "let b: Bag[T = Int64] = Bag.empty()\n    b"),
        ("wi80zv8u.c2", "Bag.empty[T = Int64]()"),
        ("wi80zv8u.c3", "Bag[T = Int64].empty()"),
    ] {
        assert_refused_naming(
            &load_errors(&bag_program(
                ns,
                &format!("  operation bad() -> String =\n    {call}"),
            )),
            &["expected String, got Bag[T = Int64]"],
            call,
        );
    }
}

/// CONTROL — ONLY A SLOT OF THE CALLEE'S OWN SORT. A parameter standing anywhere else in
/// the result is the variable it was: `Src.noneOf() -> Option[T = T]` with nothing to fix
/// `T` is still an `Option[T = ?_]`. Passes with or without the change by design; it is
/// here so that the boundary of the rule is a row and not a sentence.
#[test]
fn a_parameter_in_another_sorts_slot_is_left_as_it_was() {
    let src = r#"
namespace wi80zv8u.d1
  import anthill.prelude.{Int64, Option}
  import anthill.prelude.Option.{none}
  sort Src
    sort T = ?
    entity src(v: T)
    operation noneOf() -> Option[T = T] = none
  end
  operation bad() -> Int64 = Src.noneOf()
end
"#;
    assert_refused_naming(
        &load_errors(src),
        &["expected Int64, got Option[T = ?_]"],
        "`Src.noneOf()` as an Int64",
    );
}

/// WHAT (a) DOES NOT DO, pinned so that it is a decision and not an accident: an open slot
/// is not an inference variable. `let e = Bag.empty()` is a bag of nothing said, and it is
/// read as a bag of `Int64` on one line and of `String` on the next — as it was while
/// `empty` returned the bare `Bag`. Passes with or without the change by design. A join
/// that BINDS is the stricter rule (option (c)), and would turn this row into a refusal.
#[test]
fn an_open_slot_is_not_an_inference_variable() {
    let src = bag_program(
        "wi80zv8u.e1",
        r#"  operation go() -> Int64 =
    let e = Bag.empty()
    let ints = Bag.add(e, 1)
    let strs = Bag.add(e, "s")
    Bag.size(ints) + Bag.size(strs)"#,
    );
    assert_eq!(run_src(&src, "wi80zv8u.e1.go"), Ok(2));
}

/// THE STDLIB'S OWN, which is what the rule was decided on: `List.empty()` and
/// `Map.empty()` as the first arm of a `match`, the user's program. `empty` is written `->
/// Self` in both since this change.
#[test]
fn the_stdlibs_receiverless_constructors_join() {
    let src = r#"
namespace wi80zv8u.s1
  import anthill.prelude.{Int64, String, List, Map}
  import anthill.prelude.List.{nil, cons}
  operation f(xs: List[T = Int64], ys: List[T = Int64]) -> Int64 =
    let known = match xs
      case nil() -> List.empty()
      case cons(_, _) -> ys
    List.length(known)
  operation g(xs: List[T = Int64], m: Map[K = String, V = Int64]) -> Int64 =
    let known = match xs
      case nil() -> Map.empty()
      case cons(_, _) -> m
    Map.size(Map.put(known, "k", 1))
  operation go() -> Int64 =
    f([], [1, 2]) * 1000 + f([5], [1, 2]) * 100
      + g([], Map.put(Map.empty(), "a", 1)) * 10 + g([5], Map.put(Map.empty(), "a", 1))
end
"#;
    assert_eq!(run_src(src, "wi80zv8u.s1.go"), Ok(212));
}

//! WI-20261001-80ZV8 — AN OPEN SLOT IS CLOSED WHERE THE VALUE GETS A NAME.
//!
//! A call that fixes none of a sort's parameters leaves the slot open in its result (the
//! user's rule of 2026-10-03, `wi_80zv8_unfixed_parameter_test`): the element is not said,
//! and whatever the value meets says it. That is one answer for a value used ONCE. Bound to
//! a name it is used as often as the name is written, and every use said the slot again:
//! `let e = Bag.empty()` was a bag of `Int64` on one line and of `String` on the next. For a
//! value one can write through — a stack, a cell, a logic variable — that is one value read
//! at two types.
//!
//! The user's decision (2026-10-04, the fourth of five variants): inside ONE EXPRESSION the
//! slot stays open, so what encloses the call says it — an argument position, a branch join.
//! Where the value gets a NAME the slot is closed to that name's own unknown, `e.T`, the type
//! a declared parameter left bare has: a `let`, a pattern variable. A destructured scrutinee
//! has no name to project off, and its slot is one unnamed unknown, shared by every binder of
//! that destructuring. Saying the slot is an annotation or a bracket. Inferring it from the
//! later uses — Hindley–Milner over the body — is WI-20261004-KEGNC.
//!
//! Every row that can RUNS and names its value; a row about a TYPE reads it out of a refusal
//! that prints it.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED (2026-10-04, on the tree this file is committed with), each part present but
//! disabled, on the temporary binary `wi_80zv8_bare_own_sort_test` describes (28 suites, 707
//! rows):
//!
//! 1. A NAME CLOSES THE SLOT (typing/pattern.rs, the `Pattern::Var` arm's
//!    `closed_where_named`). 11 FAIL: nine here — [`a_named_value_is_one_instance`],
//!    [`a_named_value_does_not_meet_a_declared_instance`], [`a_pattern_variable_is_a_name`],
//!    [`two_names_are_two_unknowns_and_one_name_is_one`],
//!    [`a_slot_nested_in_a_named_value_is_closed_too`],
//!    [`a_writable_value_is_not_read_at_two_types`],
//!    [`a_named_function_is_not_the_values_its_calls_make`] (its named call result),
//!    [`two_unknowns_of_one_name_are_said_to_be_two`],
//!    [`a_named_nil_is_closed_and_a_named_literal_keeps_its_variable`] — and `wi508
//!    wi508_concrete_new_element_is_not_inferred_from_use`, `wi_0rp29_review9
//!    a_named_reduced_return_is_closed_at_the_name`. Each loads: the value is read as the
//!    use likes.
//! 2. A DESTRUCTURED SCRUTINEE IS ONE INSTANCE (the `Pattern::Constructor` arm's). 1 FAILS:
//!    [`a_destructured_value_is_one_instance`].
//!    WITH 1 AND 2 BOTH OUT, 13 FAIL: those twelve and
//!    [`a_name_nothing_reads_at_an_instance_runs`], which passes under either alone — see
//!    its site.
//! 3. A NAME DOES NOT CLOSE A FUNCTION'S RESULT (typing/elaborate.rs, the
//!    `SlotPosition::Named` gate of the arrow arm). 1 FAILS:
//!    [`a_named_function_is_not_the_values_its_calls_make`] (its two calls).
//! 4. A JOIN TAKES WHAT THE OTHER BRANCH SAYS (typing/subtype.rs `open_slots_said_by`, not
//!    called from `join_types`). 8 FAIL: [`a_branch_join_takes_what_the_other_branch_says`],
//!    [`a_branch_join_takes_each_slot_from_the_branch_that_says_it`],
//!    [`a_branch_join_reaches_a_slot_one_level_down`],
//!    [`a_branch_join_reaches_a_named_tuple_and_a_functions_result`],
//!    [`a_branch_join_does_not_launder_an_element`], `if_branch_join
//!    if_bare_vs_parameterized_branches_join_in_both_orders`, and
//!    `wi_80zv8_unfixed_parameter`'s `a_call_that_fixes_nothing_joins_with_the_instance_it_
//!    meets` and `the_stdlibs_receiverless_constructors_join`. Its three descents, each off
//!    alone: one level down — 1 FAILS, [`a_branch_join_reaches_a_slot_one_level_down`]; a
//!    named tuple, and an arrow's result — 1 FAILS under each,
//!    [`a_branch_join_reaches_a_named_tuple_and_a_functions_result`].
//! 5. A PROVIDER IN A REQUIREMENT SLOT IS NOT WALKED (typing/elaborate.rs, the
//!    `named_requirement_slots` gate in `rigidify_unwritten_sort_params`). 3 FAIL, all in
//!    `wi858_pair_orderings_test`, which has the orderings:
//!    `union_of_two_parameters_at_one_ordering_merges`, `union_within_one_ordering_merges`,
//!    `union_across_two_orderings_is_a_type_error`.
//! 6. TWO UNKNOWNS OF ONE NAME ARE NAMED AS THE CAUSE (typing/display.rs
//!    `like_named_unknowns`). 1 FAILS: [`two_unknowns_of_one_name_are_said_to_be_two`].
//!
//! Pass under every part, by design, and say so at their sites:
//! [`an_annotation_or_a_bracket_says_the_slot`],
//! [`one_expression_leaves_the_slot_to_what_encloses_it`] and
//! [`a_join_of_two_said_branches_is_unchanged`].

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

/// `Bag` with a receiver-less `empty() -> Self` and two fields of its element; `rest` is
/// what follows the sort.
fn bag_program(ns: &str, rest: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, Bool, String, List, Option, Map, Pair}}
  import anthill.prelude.List.{{nil, cons}}
  import anthill.prelude.Option.{{none, some}}
  import anthill.prelude.Pair.{{pair}}
  sort Bag
    sort T = ?
    entity bag(items: List[T = T], spare: List[T = T])
    operation empty() -> Self = bag(items: [], spare: [])
    operation add(b: Self, x: T) -> Self =
      match b
        case bag(items, spare) -> bag(items: cons(head: x, tail: items), spare: spare)
    operation size(b: Self) -> Int64 =
      match b
        case bag(items, spare) -> List.length(items)
  end
  operation takes_strings(xs: List[T = String]) -> Int64 = 0
  operation takes_opt_str(o: Option[T = String]) -> Int64 = 0
  operation both[X](a: Bag[T = X], b: Bag[T = X]) -> Int64 = 0
{rest}
end
"#
    )
}

/// A NAMED VALUE IS ONE INSTANCE. `let e = Bag.empty()` is a bag of `e.T`, and adding an
/// `Int64` to it is refused with the unknown named. This is `wi_80zv8_unfixed_parameter_
/// test`'s `an_open_slot_is_not_an_inference_variable` at the opposite verdict: there `e`
/// took an `Int64` on one line and a `String` on the next, and the program ran to 2.
#[test]
fn a_named_value_is_one_instance() {
    let errs = load_errors(&bag_program(
        "wi80zv8n.a1",
        r#"  operation go() -> Int64 =
    let e = Bag.empty()
    let ints = Bag.add(e, 1)
    let strs = Bag.add(e, "s")
    Bag.size(ints) + Bag.size(strs)"#,
    ));
    assert_refused_naming(
        &errs,
        &["add.x (op-arg): expected e.T, got Int64"],
        "a named bag read as a bag of Int64",
    );
}

/// … AND NOT THE DECLARED INSTANCE EITHER: `let e = Bag.empty()` returned where a `Bag[T =
/// Int64]` is declared is `got Bag[T = e.T]`. The name is where the slot had to be said.
#[test]
fn a_named_value_does_not_meet_a_declared_instance() {
    let errs = load_errors(&bag_program(
        "wi80zv8n.a2",
        r#"  operation go() -> Bag[T = Int64] =
    let e = Bag.empty()
    e"#,
    ));
    assert_refused_naming(
        &errs,
        &["expected Bag[T = Int64], got Bag[T = e.T]"],
        "a named bag returned as a bag of Int64",
    );
}

/// A PATTERN VARIABLE IS A NAME: `match Bag.empty()  case b -> …` binds `b` as a `let` does.
#[test]
fn a_pattern_variable_is_a_name() {
    let errs = load_errors(&bag_program(
        "wi80zv8n.a3",
        r#"  operation go() -> Int64 =
    match Bag.empty()
      case b -> Bag.size(Bag.add(b, 1))"#,
    ));
    assert_refused_naming(
        &errs,
        &["add.x (op-arg): expected b.T, got Int64"],
        "a pattern variable over an open bag",
    );
}

/// TWO NAMES ARE TWO UNKNOWNS, ONE NAME TWICE IS ONE. `both[X](a: Bag[T = X], b: Bag[T =
/// X])` over `e` and `f` — two calls of `Bag.empty()` — is refused at `expected Bag[T =
/// e.T], got Bag[T = f.T]`; over `e` and `e` it runs. An unknown that could not be named
/// would refuse the second as well.
#[test]
fn two_names_are_two_unknowns_and_one_name_is_one() {
    let two = load_errors(&bag_program(
        "wi80zv8n.b1",
        r#"  operation go() -> Int64 =
    let e = Bag.empty()
    let f = Bag.empty()
    both(e, f)"#,
    ));
    assert_refused_naming(
        &two,
        &["both.b (op-arg): expected Bag[T = e.T], got Bag[T = f.T]"],
        "two named bags as one instance",
    );

    let one = bag_program(
        "wi80zv8n.b2",
        r#"  operation go() -> Int64 =
    let e = Bag.empty()
    both(e, e) + Bag.size(e) + 7"#,
    );
    assert_eq!(run_src(&one, "wi80zv8n.b2.go"), Ok(7));
}

/// A DESTRUCTURED SCRUTINEE IS ONE INSTANCE, WITH NO NAME. `match Bag.empty()  case
/// bag(items, spare)`: the two binders are lists of one element, so `List.append(items,
/// spare)` runs — and of no element anyone said, so consing an `Int64` onto one is refused.
#[test]
fn a_destructured_value_is_one_instance() {
    let agree = bag_program(
        "wi80zv8n.c1",
        r#"  operation go() -> Int64 =
    match Bag.empty()
      case bag(items, spare) -> List.length(List.append(items, spare)) + 3"#,
    );
    assert_eq!(run_src(&agree, "wi80zv8n.c1.go"), Ok(3));

    let errs = load_errors(&bag_program(
        "wi80zv8n.c2",
        r#"  operation go() -> Int64 =
    match Bag.empty()
      case bag(items, spare) -> List.length(cons(head: 1, tail: spare))"#,
    ));
    assert_refused_naming(
        &errs,
        &["cons.tail (entity-field): expected List[T = Int64], got List[T = ?T]"],
        "a binder of a destructured open bag as a list of Int64",
    );
}

/// A SLOT NESTED IN A NAMED VALUE IS CLOSED TOO: `let p = pair(fst: Bag.empty(), snd: 1)`
/// names the pair, and the bag inside it is one bag. Nothing can name its element (there is
/// no `p.A.T`), so the refusal prints an unknown of its own.
#[test]
fn a_slot_nested_in_a_named_value_is_closed_too() {
    let errs = load_errors(&bag_program(
        "wi80zv8n.d1",
        r#"  operation go() -> Int64 =
    let p = pair(fst: Bag.empty(), snd: 1)
    Bag.size(Bag.add(p.fst, 1))"#,
    ));
    assert_refused_naming(
        &errs,
        &["add.x (op-arg): expected ?T, got Int64"],
        "a bag inside a named pair as a bag of Int64",
    );
}

/// THE VALUE THE RULE IS FOR — one you can write through. `let x = MutableStack.new()`
/// took an `Int64` and then a `String`: one stack, two element types. Refused at the first
/// push, the unknown named.
#[test]
fn a_writable_value_is_not_read_at_two_types() {
    let errs = load_errors(
        r#"
namespace wi80zv8n.w1
  import anthill.prelude.{Int64, String, MutableStack}
  import anthill.prelude.FiniteCollection.{size}
  operation mixed() -> Int64 effects Modify[result] =
    let x = MutableStack.new()
    let _ = MutableStack.push(x, 10)
    let _ = MutableStack.push(x, "s")
    size(x)
end
"#,
    );
    assert_refused_naming(
        &errs,
        &["push.elem (op-arg): expected x.T, got Int64"],
        "one stack pushed an Int64 and a String",
    );
}

/// A NAMED FUNCTION IS NOT THE VALUES ITS CALLS MAKE. `let mk = lambda (n: Int64) ->
/// Bag.empty()` names a function; each `mk(i)` is a new bag, said by what it meets — an
/// `Int64` added to one, a `String` to the next. Runs to 1 + 1. The first cut of the naming
/// rule walked into the arrow and closed its result, so every call returned one unknown and
/// the first `add` was refused `expected ?T, got Int64` (MEASURED, found by /code-review).
/// A call's result bound to a name of its own is closed there, as any value is.
#[test]
fn a_named_function_is_not_the_values_its_calls_make() {
    let src = bag_program(
        "wi80zv8n.h1",
        r#"  operation go() -> Int64 =
    let mk = lambda (n: Int64) -> Bag.empty()
    Bag.size(Bag.add(mk(1), 5)) + Bag.size(Bag.add(mk(2), "s"))"#,
    );
    assert_eq!(run_src(&src, "wi80zv8n.h1.go"), Ok(2));

    let errs = load_errors(&bag_program(
        "wi80zv8n.h2",
        r#"  operation go() -> Int64 =
    let mk = lambda (n: Int64) -> Bag.empty()
    let b = mk(1)
    Bag.size(Bag.add(b, 5))"#,
    ));
    assert_refused_naming(
        &errs,
        &["add.x (op-arg): expected b.T, got Int64"],
        "a call's result, named",
    );
}

/// TWO UNKNOWNS UNDER ONE PRINTED NAME ARE SAID TO BE TWO. A second `let e` shadowing the
/// first is another binding, and its unknown another unknown: `both(first, e)` is refused,
/// and both sides print `Bag[T = e.T]`. Two bags nested in two named pairs print `Bag[T =
/// ?T]` twice. The refusal used to end "these render alike but are not the same type … please
/// report it" — the backstop for a renderer gap, said of an ordinary author error.
#[test]
fn two_unknowns_of_one_name_are_said_to_be_two() {
    for (ns, body, name) in [
        (
            "wi80zv8n.u1",
            "let e = Bag.empty()\n    let first = e\n    let e = Bag.empty()\n    both(first, e)",
            "`e` is two different unknowns here",
        ),
        (
            "wi80zv8n.u2",
            "let p = pair(fst: Bag.empty(), snd: 1)\n    let q = pair(fst: Bag.empty(), snd: \
             1)\n    both(p.fst, q.fst)",
            "`?T` is two different unknowns here",
        ),
    ] {
        let errs = load_errors(&bag_program(
            ns,
            &format!("  operation go() -> Int64 =\n    {body}"),
        ));
        assert_refused_naming(&errs, &["both.b (op-arg)", name], body);
        assert!(
            !errs.join(" | ").contains("please report it"),
            "an author's error, not a renderer's: {errs:?}"
        );
    }
}

/// A NAME NOTHING READS AT AN INSTANCE RUNS. `Bag.size` takes any bag, and a `match` on the
/// name binds two lists of the name's own element, which `List.append` takes together. Runs
/// to 0 + 0 + 5.
///
/// It runs with either half of the rule alone, and NOT with neither: left open, `e`'s two
/// binders were each an unknown of their own — a binder over a field that leaves a slot open
/// is an instance of its own, decided earlier the same day — and `append(items, spare)` was
/// `expected List[T = items.T], got List[T = spare.T]`. The name's one unknown, or the
/// scrutinee's, is what makes them one bag's.
#[test]
fn a_name_nothing_reads_at_an_instance_runs() {
    let src = bag_program(
        "wi80zv8n.e1",
        r#"  operation go() -> Int64 =
    let e = Bag.empty()
    let n = match e
      case bag(items, spare) -> List.length(List.append(items, spare))
    Bag.size(e) + n + 5"#,
    );
    assert_eq!(run_src(&src, "wi80zv8n.e1.go"), Ok(5));
}

/// CONTROL — SAYING THE SLOT: an annotation on the `let`, a bracket on the call, a bracket
/// on the receiver. Each runs to 1. Passes with or without the change, by design.
#[test]
fn an_annotation_or_a_bracket_says_the_slot() {
    for (ns, bound) in [
        ("wi80zv8n.f1", "let e: Bag[T = Int64] = Bag.empty()"),
        ("wi80zv8n.f2", "let e = Bag.empty[T = Int64]()"),
        ("wi80zv8n.f3", "let e = Bag[T = Int64].empty()"),
    ] {
        let src = bag_program(
            ns,
            &format!("  operation go() -> Int64 =\n    {bound}\n    Bag.size(Bag.add(e, 1))"),
        );
        assert_eq!(run_src(&src, &format!("{ns}.go")), Ok(1), "{bound}");
    }
}

/// CONTROL — ONE EXPRESSION LEAVES THE SLOT TO WHAT ENCLOSES IT: the argument position says
/// it, for a user sort and for the stdlib's `Map`. Runs to 11. Passes with or without the
/// change, by design — it is what the rule must NOT take away.
#[test]
fn one_expression_leaves_the_slot_to_what_encloses_it() {
    let src = bag_program(
        "wi80zv8n.g1",
        r#"  operation go() -> Int64 =
    Bag.size(Bag.add(Bag.empty(), 5)) * 10 + Map.size(Map.put(Map.empty(), "a", 1))"#,
    );
    assert_eq!(run_src(&src, "wi80zv8n.g1.go"), Ok(11));
}

/// A BRANCH JOIN TAKES WHAT THE OTHER BRANCH SAYS, in either order: `if c then none() else
/// some(1)` is an `Option[T = Int64]`, read out of a refusal that prints it. The join used to
/// keep the open side (WI-287, "the more general type"), which the name then closed — `got
/// Option[T = x.T]`.
#[test]
fn a_branch_join_takes_what_the_other_branch_says() {
    for (ns, branches) in [
        ("wi80zv8n.j1", "if c then none() else some(1)"),
        ("wi80zv8n.j2", "if c then some(1) else none()"),
    ] {
        let errs = load_errors(&bag_program(
            ns,
            &format!(
                "  operation go(c: Bool) -> Int64 =\n    let x = {branches}\n    takes_opt_str(x)"
            ),
        ));
        assert_refused_naming(
            &errs,
            &["expected Option[T = String], got Option[T = Int64]"],
            branches,
        );
    }
}

/// … SLOT BY SLOT: `Duo.left(1)` says `A` and `Duo.right("s")` says `B`, and their join says
/// both — `got Duo[A = Int64, B = String]`.
#[test]
fn a_branch_join_takes_each_slot_from_the_branch_that_says_it() {
    let errs = load_errors(
        r#"
namespace wi80zv8n.j3
  import anthill.prelude.{Int64, Bool, String, List}
  sort Duo
    sort A = ?
    sort B = ?
    entity duo(n: Int64)
    operation left(a: A) -> Self = duo(n: 1)
    operation right(b: B) -> Self = duo(n: 2)
  end
  operation takes_strings(xs: List[T = String]) -> Int64 = 0
  operation go(c: Bool) -> Int64 =
    let d = if c then Duo.left(1) else Duo.right("s")
    takes_strings(d)
end
"#,
    );
    assert_refused_naming(
        &errs,
        &["expected List[T = String], got Duo[A = Int64, B = String]"],
        "the join of a `Duo` saying `A` and one saying `B`",
    );
}

/// … AND ONE LEVEL DOWN: `pair(fst: nil, snd: 1)` beside `pair(fst: cons(head: "s", tail:
/// nil), snd: 2)` says the pair's `A` on both sides, and it is the LIST inside that one side
/// leaves open. The join is a `Pair[A = List[T = String], B = Int64]` in either order; with
/// the fill stopping at the first level it was whichever branch came first, and the open one
/// was admitted as a pair of `List[T = Int64]`.
#[test]
fn a_branch_join_reaches_a_slot_one_level_down() {
    for (ns, branches) in [
        (
            "wi80zv8n.j4",
            r#"if c then pair(fst: nil, snd: 1) else pair(fst: cons(head: "s", tail: nil), snd: 2)"#,
        ),
        (
            "wi80zv8n.j5",
            r#"if c then pair(fst: cons(head: "s", tail: nil), snd: 2) else pair(fst: nil, snd: 1)"#,
        ),
    ] {
        let errs = load_errors(&bag_program(
            ns,
            &format!(
                "  operation takes_pi(p: Pair[A = List[T = Int64], B = Int64]) -> Int64 = 0\n  \
                 operation go(c: Bool) -> Int64 =\n    takes_pi({branches})"
            ),
        ));
        assert_refused_naming(
            &errs,
            &["expected Pair[A = List[T = Int64], B = Int64], got Pair[A = List[T = String], B = Int64]"],
            branches,
        );
    }
}

/// … AND THROUGH A NAMED TUPLE AND A FUNCTION'S RESULT, which hold a sort application as a
/// slot does. With the fill reading sort applications only, the open branch still won
/// wherever it came first: `(a: nil, b: 1)` beside `(a: cons(head: 1, tail: nil), b: 2)`
/// loaded against `(a: List[T = String], b: Int64)` in that order and was refused in the
/// other, and `lambda (x: Int64) -> nil` beside a lambda returning a list of `Int64` the
/// same (MEASURED, found by /code-review). Refused both ways round now.
#[test]
fn a_branch_join_reaches_a_named_tuple_and_a_functions_result() {
    let tuple = "expected (a: List[T = String], b: Int64), got (a: List[T = Int64], b: Int64)";
    let arrow = "expected Int64 -> List[T = String], got Int64 -> List[T = Int64]";
    for (ns, body, naming) in [
        (
            "wi80zv8n.t1",
            "takes_tuple(if c then (a: nil, b: 1) else (a: cons(head: 1, tail: nil), b: 2))",
            tuple,
        ),
        (
            "wi80zv8n.t2",
            "takes_tuple(if c then (a: cons(head: 1, tail: nil), b: 2) else (a: nil, b: 1))",
            tuple,
        ),
        (
            "wi80zv8n.t3",
            "takes_fn(if c then lambda (x: Int64) -> nil else lambda (x: Int64) -> cons(head: \
             x, tail: nil))",
            arrow,
        ),
        (
            "wi80zv8n.t4",
            "takes_fn(if c then lambda (x: Int64) -> cons(head: x, tail: nil) else lambda (x: \
             Int64) -> nil)",
            arrow,
        ),
    ] {
        let errs = load_errors(&bag_program(
            ns,
            &format!(
                "  operation takes_tuple(t: (a: List[T = String], b: Int64)) -> Int64 = 0\n  \
                 operation takes_fn(f: (x: Int64) -> List[T = String]) -> Int64 = 0\n  \
                 operation go(c: Bool) -> Int64 =\n    {body}"
            ),
        ));
        assert_refused_naming(&errs, &[naming], body);
    }
}

/// A BRANCH JOIN DOES NOT LAUNDER AN ELEMENT. `if c then nil else cons(head: 1, tail: nil)`
/// was the bare `List`, which every instance admits: handed to `takes_strings` it loaded, in
/// one expression and through a `let` alike, and an `Int64` was read as a `String`. It is a
/// `List[T = Int64]` in either order.
#[test]
fn a_branch_join_does_not_launder_an_element() {
    for (ns, body) in [
        (
            "wi80zv8n.k1",
            "takes_strings(if c then nil else cons(head: 1, tail: nil))",
        ),
        (
            "wi80zv8n.k2",
            "takes_strings(if c then cons(head: 1, tail: nil) else nil)",
        ),
        (
            "wi80zv8n.k3",
            "let x = if c then nil else cons(head: 1, tail: nil)\n    takes_strings(x)",
        ),
    ] {
        let errs = load_errors(&bag_program(
            ns,
            &format!("  operation go(c: Bool) -> Int64 =\n    {body}"),
        ));
        assert_refused_naming(
            &errs,
            &["takes_strings.xs (op-arg): expected List[T = String], got List[T = Int64]"],
            body,
        );
    }
}

/// CONTROL — the join of two branches that both say the slot is what it was: runs to 2 with
/// or without the change, by design.
#[test]
fn a_join_of_two_said_branches_is_unchanged() {
    let src = bag_program(
        "wi80zv8n.l1",
        r#"  operation pick(c: Bool) -> List[T = Int64] =
    let x = if c then cons(head: 1, tail: nil) else cons(head: 2, tail: cons(head: 3, tail: nil))
    x
  operation go() -> Int64 = List.length(pick(false))"#,
    );
    assert_eq!(run_src(&src, "wi80zv8n.l1.go"), Ok(2));
}

/// WHAT THE RULE DOES NOT REACH, pinned so that it is a recorded limit and not an accident:
/// `nil` named is closed — it is a constructor that fixes nothing, like any call — while the
/// literal `[]` carries a variable of its own, which a name does not close, so `let xs = []`
/// is still read at two element types. One value, two spellings, two verdicts. Reported to
/// the user 2026-10-04 with the refinement that would align them (a slot in a covariant
/// position stays open); not decided.
#[test]
fn a_named_nil_is_closed_and_a_named_literal_keeps_its_variable() {
    let errs = load_errors(&bag_program(
        "wi80zv8n.m1",
        r#"  operation go() -> Int64 =
    let xs = nil
    List.length(cons(head: 1, tail: xs))"#,
    ));
    assert_refused_naming(
        &errs,
        &["cons.tail (entity-field): expected List[T = Int64], got List[T = xs.T]"],
        "`nil` named, then consed onto",
    );

    let literal = bag_program(
        "wi80zv8n.m2",
        r#"  operation go() -> Int64 =
    let xs = []
    List.length(cons(head: 1, tail: xs)) + List.length(cons(head: "s", tail: xs))"#,
    );
    assert_eq!(run_src(&literal, "wi80zv8n.m2.go"), Ok(2));
}

//! WI-20261001-80ZV8 — A SORT'S PARAMETER BOUND BY SEVERAL ARGUMENTS TAKES THEIR JOIN, as an
//! operation's own `[A]` does (WI-20260926-NEKR0) and a collection literal's element does
//! (WI-20260829-WBXGX). The user's decision of 2026-10-04: "we have this decision for list
//! constants, so yes".
//!
//! A call let the FIRST argument naming the sort's parameter decide it — the receiver, or a
//! constructor's first field — and held every later one to that. With a named `nil` at the
//! bottom type (`wi_80zv8_named_open_slot_test`) that order became visible in the most ordinary
//! program: `List.append([1], acc)` loaded and `List.append(acc, [1])` was refused, `expected
//! List[T = nothing], got List[T = Int64]`. It had always been visible over an invariant sort:
//! `push(top: c, rest: shapes)`, a `Circle` on a `Stack[T = Shape]`, was refused `push.rest:
//! expected Stack[T = Circle], got Stack[T = Shape]`.
//!
//! The parameter is now instantiated as an operation's own `[A]` is: AT AN INVARIANT
//! OCCURRENCE WHERE THERE IS ONE — a stack of shapes says `T = Shape`, and the other arguments
//! are checked against that — ELSE AT THE JOIN OF THE COVARIANT ONES.
//!
//! IT ONLY EVER ADMITS. Where the arguments have no join nothing is bound, and the call
//! decides in its own order, refusing the argument by name with the message it always had.
//! What a refusal NAMES does move where an invariant occurrence follows a covariant one: the
//! invariant one says the parameter, so the covariant argument is the one that does not fit
//! ([`an_invariant_occurrence_refuses_what_does_not_fit_it`]). And the rule is a DATA sort's:
//! a spec's parameters are a provision's, read off the receiver's carrier or the enclosing
//! `requires` clause, whether or not anything provides the spec yet.
//!
//! THREE SITES ASK IT, and must agree: the operation-body call, the constructor, and the hint
//! a lambda argument is typed from — the call checks the lambda against the instantiation it
//! made ([`a_lambdas_hint_carries_the_calls_instantiation`]).
//!
//! Every row that can RUNS and names its value; a row about a TYPE reads it out of a refusal
//! that prints it.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! MEASURED (2026-10-04, on the tree this file is committed with), each part present but
//! disabled, on a binary of seven suites — this file, `wi_80zv8_named_open_slot`,
//! `wi_80zv8_self`, `wi_mdwew_bare_spec_arg_provision`, `wi_0rp29_call_binding`,
//! `wi_80zv8_written_wildcard`, `wi_nekr0_repeated_type_param_join`; 189 rows:
//!
//! 1. THE CALL'S JOIN (typing/apply.rs, `join_repeated_sort_params` not called). 7 FAIL:
//!    [`both_orders_answer_for_a_sorts_parameter`],
//!    [`a_subtype_and_its_supertype_join_in_either_order`],
//!    [`an_invariant_occurrence_says_the_parameter_in_either_order`],
//!    [`an_invariant_occurrence_refuses_what_does_not_fit_it`],
//!    [`a_lambdas_hint_carries_the_calls_instantiation`],
//!    [`the_joined_instance_is_the_one_whose_requirement_is_supplied`] and
//!    `wi_80zv8_named_open_slot_test a_named_nil_stands_first_or_second`.
//! 2. THE CONSTRUCTOR'S JOIN (typing/constructor.rs, the same call not made). 6 FAIL:
//!    [`a_constructors_fields_join_in_either_order`], the two invariant rows of part 1 — each
//!    has a constructor line — [`a_parameter_with_no_join_does_not_keep_another_from_its_own`],
//!    and two rows whose refusal it rewords: `wi_80zv8_self_test
//!    self_in_an_entity_field_refuses_another_instance` (the head is named, where the tail
//!    was) and `wi_mdwew_bare_spec_arg_provision_test
//!    foreign_provision_binding_is_refused_like_its_concrete_twin` (the field's result prints
//!    as the callback's, where it printed unbound).
//! 3. THE HINT'S JOIN (typing/arg_hints.rs, `join_sort_params_for_hint` not called). 2 FAIL:
//!    [`a_lambdas_hint_carries_the_calls_instantiation`] and
//!    [`a_lambda_is_refused_in_its_body_in_either_order`].
//! 4. OF A DATA SORT ONLY (`sort_params_join` without that leg, so that a spec's parameter
//!    joins too). 13 FAIL: [`a_specs_parameter_is_its_provisions`],
//!    [`a_spec_nothing_provides_yet_is_a_spec_too`], and eleven rows of
//!    `wi_0rp29_call_binding_test`, `wi_80zv8_self_test` and `wi_80zv8_written_wildcard_test`
//!    about a provision's bindings at a call.
//! 5. …AND NOT "A SORT NOTHING PROVIDES" (that leg in its place — how this was first
//!    written). 1 FAILS: [`a_spec_nothing_provides_yet_is_a_spec_too`], which then LOADS.
//! 6. EACH PARAMETER BY ITSELF (one pass over all the sort's parameters). 1 FAILS:
//!    [`a_parameter_with_no_join_does_not_keep_another_from_its_own`].
//!
//! NOT A PART OF ITS OWN: that an invariant occurrence FIXES the parameter is
//! `join_repeated_type_params`' rule, shared with `[A]` and measured in
//! `wi_nekr0_repeated_type_param_join_test`. Asked of a sort's parameter it is parts 1 and 2,
//! whose invariant rows fail without them.
//!
//! Pass under every part, by design, and say so at their sites:
//! [`no_join_is_refused_by_the_argument_as_before`],
//! [`an_invariant_sort_parameter_still_demands_one_type`],
//! [`a_written_bracket_outranks_the_join`], the `put2` line of
//! [`an_invariant_occurrence_refuses_what_does_not_fit_it`] and the `Shape`-first line of
//! [`a_lambda_is_refused_in_its_body_in_either_order`].
//! [`both_orders_answer_for_a_sorts_parameter`] also fails with the bottom type backed out
//! (`wi_80zv8_named_open_slot_test`'s ledger, part 7): its `acc` is then the name's unknown,
//! which has no join with `Int64`.

use crate::common::{assert_refused_naming, load_errors_of as load_errors, run_int64 as run_src};

/// `Circle provides Shape`, an invariant `Bag`, an invariant `Stack`, and `rest`.
fn program(ns: &str, rest: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, List, Bool}}
  import anthill.prelude.List.{{nil, cons}}
  sort Shape
  end
  sort Circle
    provides Shape
    entity circle
  end
  sort Bag
    sort T = ?
    entity bag(items: List[T = T])
    operation merge(a: Self, b: Self) -> Self =
      match a
        case bag(xs) ->
          match b
            case bag(ys) -> bag(items: List.append(xs, ys))
  end
  sort Stack
    sort T = ?
    entity empty
    entity push(top: T, rest: Self)
    operation put(x: T, s: Self) -> Self = push(top: x, rest: s)
    operation put2(s: Self, x: T) -> Self = push(top: x, rest: s)
    operation each(x: T, s: Self, f: (v: T) -> Int64) -> Int64 = f(x)
    operation each2(s: Self, x: T, f: (v: T) -> Int64) -> Int64 = f(x)
    operation pick(x: T, y: T, f: (v: T) -> Int64) -> Int64 = f(y)
    operation depth(s: Self) -> Int64 =
      match s
        case empty() -> 0
        case push(_, r) -> 1 + depth(r)
  end
  operation takes_strings(xs: List[T = String]) -> Int64 = 0
  operation takes_string_stack(s: Stack[T = String]) -> Int64 = 0
  operation area(s: Shape) -> Int64 = 1
  operation radius(c: Circle) -> Int64 = 2
{rest}
end
"#
    )
}

/// BOTH ORDERS ANSWER. A list of nothing standing first no longer fixes `T = nothing`: the
/// two arguments join at `Int64`, and the list of nothing is a list of that. Runs to 1 + 1.
#[test]
fn both_orders_answer_for_a_sorts_parameter() {
    let src = program(
        "wi80zv8j.a1",
        r#"  operation go() -> Int64 =
    let acc = nil
    List.length(List.append(acc, [1])) + List.length(List.append([1], acc))"#,
    );
    assert_eq!(run_src(&src, "wi80zv8j.a1.go"), Ok(2));
}

/// A SUBTYPE AND ITS SUPERTYPE JOIN AT THE SUPERTYPE, IN EITHER ORDER, through an operation:
/// a list of `Circle` appended to a list of `Shape` (`Circle provides Shape`) is a `List[T =
/// Shape]` whichever comes first — read out of a refusal that prints it — and both orders run,
/// 2 + 2. With the first argument deciding, the circles first fixed `T = Circle` and the list of
/// shapes was refused, `append.ys (op-arg): expected List[T = Circle], got List[T = Shape]`.
#[test]
fn a_subtype_and_its_supertype_join_in_either_order() {
    for (ns, expr) in [
        ("wi80zv8j.b1", "List.append(cs, ss)"),
        ("wi80zv8j.b2", "List.append(ss, cs)"),
    ] {
        let errs = load_errors(&program(
            ns,
            &format!(
                "  operation go(cs: List[T = Circle], ss: List[T = Shape]) -> Int64 = \
                 takes_strings({expr})"
            ),
        ));
        assert_refused_naming(
            &errs,
            &["expected List[T = String], got List[T = Shape]"],
            expr,
        );
    }
    let runs = program(
        "wi80zv8j.b3",
        r#"  operation both(cs: List[T = Circle], ss: List[T = Shape]) -> Int64 =
    List.length(List.append(cs, ss)) + List.length(List.append(ss, cs))
  operation go() -> Int64 = both([circle], [circle])"#,
    );
    assert_eq!(run_src(&runs, "wi80zv8j.b3.go"), Ok(4));
}

/// A CONSTRUCTOR IS A CALL: `cons(head: c, tail: ss)` over a `Circle` and a `List[T = Shape]`
/// is a `List[T = Shape]`, as `cons(head: s, tail: cs)` over a `Shape` and a `List[T =
/// Circle]` is and the literal `[c, s]` always was. The first field used to decide, so the
/// first of these was refused, `cons.tail (entity-field): expected List[T = Circle], got
/// List[T = Shape]`.
#[test]
fn a_constructors_fields_join_in_either_order() {
    for (ns, params, expr) in [
        ("wi80zv8j.k1", "c: Circle, ss: List[T = Shape]", "cons(head: c, tail: ss)"),
        ("wi80zv8j.k2", "s: Shape, cs: List[T = Circle]", "cons(head: s, tail: cs)"),
    ] {
        let errs = load_errors(&program(
            ns,
            &format!("  operation go({params}) -> Int64 = takes_strings({expr})"),
        ));
        assert_refused_naming(
            &errs,
            &["expected List[T = String], got List[T = Shape]"],
            expr,
        );
    }
    let runs = program(
        "wi80zv8j.k3",
        r#"  operation one(c: Circle, ss: List[T = Shape]) -> Int64 = List.length(cons(head: c, tail: ss))
  operation go() -> Int64 = one(circle, [circle])"#,
    );
    assert_eq!(run_src(&runs, "wi80zv8j.k3.go"), Ok(2));
}

/// CONTROL — WHERE THERE IS NO JOIN THE ARGUMENT IS REFUSED BY NAME, as before: the first
/// argument decides, and the message is the one each site always gave. Passes with or without
/// the change, by design — it is what the change must not reword.
#[test]
fn no_join_is_refused_by_the_argument_as_before() {
    for (ns, expr, naming) in [
        (
            "wi80zv8j.c1",
            r#"List.length(List.append([1], ["s"]))"#,
            "append.ys (op-arg): expected List[T = Int64], got List[T = String]",
        ),
        (
            "wi80zv8j.c2",
            r#"List.length(cons(head: "s", tail: [1]))"#,
            "cons.tail (entity-field): expected List[T = String], got List[T = Int64]",
        ),
    ] {
        let errs = load_errors(&program(ns, &format!("  operation go() -> Int64 = {expr}")));
        assert_refused_naming(&errs, &[naming], expr);
    }
}

/// CONTROL — WHAT IS WRITTEN WINS: a bracket for the sort's parameter is in place before the
/// join is asked, which binds only what is still free. `List[T = Shape].append(cs, cs)` over
/// two lists of `Circle` is a `List[T = Shape]`, and under `List[T = Circle]` a list of
/// `Shape` is refused wherever it stands. Passes with or without the change, by design — it
/// is the order of the two that a later edit must not turn round.
#[test]
fn a_written_bracket_outranks_the_join() {
    for (ns, expr, naming) in [
        (
            "wi80zv8j.w1",
            "takes_strings(List[T = Shape].append(cs, cs))",
            "expected List[T = String], got List[T = Shape]",
        ),
        (
            "wi80zv8j.w2",
            "List.length(List[T = Circle].append(cs, ss))",
            "append.ys (op-arg): expected List[T = Circle], got List[T = Shape]",
        ),
        (
            "wi80zv8j.w3",
            "List.length(List[T = Circle].append(ss, cs))",
            "append.xs (op-arg): expected List[T = Circle], got List[T = Shape]",
        ),
    ] {
        let errs = load_errors(&program(
            ns,
            &format!(
                "  operation go(cs: List[T = Circle], ss: List[T = Shape]) -> Int64 = {expr}"
            ),
        ));
        assert_refused_naming(&errs, &[naming], expr);
    }
}

/// CONTROL — AN INVARIANT PARAMETER STILL DEMANDS ONE TYPE: `Bag` declares no variance, so
/// two bags of different elements do not merge. Passes with or without the change, by design.
#[test]
fn an_invariant_sort_parameter_still_demands_one_type() {
    let errs = load_errors(&program(
        "wi80zv8j.d1",
        r#"  operation go(a: Bag[T = Int64], b: Bag[T = String]) -> Int64 =
    match Bag.merge(a, b)
      case bag(xs) -> List.length(xs)"#,
    ));
    assert_refused_naming(
        &errs,
        &["merge.b (op-arg): expected Bag[T = Int64], got Bag[T = String]"],
        "two bags of different elements",
    );
}

/// AN INVARIANT OCCURRENCE SAYS THE PARAMETER, WHEREVER IT STANDS. `Stack` declares no
/// variance, so a `Stack[T = Shape]` says `T = Shape` and a `Circle` beside it is checked
/// against that: `Stack.put(c, shapes)`, `Stack.put2(shapes, c)` and the constructor
/// `push(top: c, rest: shapes)` are each a `Stack[T = Shape]` — read out of a refusal that
/// prints it — and each runs, 2 + 2 + 2. With the first argument deciding, the circle first
/// fixed `T = Circle` and the stack was refused: `put.s (op-arg): expected Stack[T = Circle],
/// got Stack[T = Shape]`, `push.rest (entity-field): …` the same; only `put2` loaded.
#[test]
fn an_invariant_occurrence_says_the_parameter_in_either_order() {
    for (ns, expr) in [
        ("wi80zv8j.i1", "Stack.put(c, shapes)"),
        ("wi80zv8j.i2", "Stack.put2(shapes, c)"),
        ("wi80zv8j.i3", "push(top: c, rest: shapes)"),
    ] {
        let errs = load_errors(&program(
            ns,
            &format!(
                "  operation go(shapes: Stack[T = Shape], c: Circle) -> Int64 = \
                 takes_string_stack({expr})"
            ),
        ));
        assert_refused_naming(
            &errs,
            &["expected Stack[T = String], got Stack[T = Shape]"],
            expr,
        );
    }
    let runs = program(
        "wi80zv8j.i4",
        r#"  operation all(shapes: Stack[T = Shape], c: Circle) -> Int64 =
    Stack.depth(Stack.put(c, shapes)) + Stack.depth(Stack.put2(shapes, c))
      + Stack.depth(push(top: c, rest: shapes))
  operation one(s: Shape) -> Stack[T = Shape] = push(top: s, rest: empty)
  operation go() -> Int64 = all(one(circle), circle)"#,
    );
    assert_eq!(run_src(&runs, "wi80zv8j.i4.go"), Ok(6));
}

/// …AND WHAT DOES NOT FIT IT IS REFUSED BY NAME, THE SAME IN EITHER ORDER: a `Shape` does not
/// go on a `Stack[T = Circle]`, and the refusal names the shape wherever it stands. With the
/// first argument deciding, the shape first fixed `T = Shape` and the STACK was blamed —
/// `put.s (op-arg): expected Stack[T = Shape], got Stack[T = Circle]`, `push.rest
/// (entity-field): …` the same. The `put2` line is the control: its stack stands first, so it
/// read this way before the change and passes with or without it, by design.
#[test]
fn an_invariant_occurrence_refuses_what_does_not_fit_it() {
    for (ns, expr, naming) in [
        (
            "wi80zv8j.r1",
            "Stack.put(s, circles)",
            "put.x (op-arg): expected Circle, got Shape",
        ),
        (
            "wi80zv8j.r2",
            "push(top: s, rest: circles)",
            "push.top (entity-field): expected Circle, got Shape",
        ),
        (
            "wi80zv8j.r3",
            "Stack.put2(circles, s)",
            "put2.x (op-arg): expected Circle, got Shape",
        ),
    ] {
        let errs = load_errors(&program(
            ns,
            &format!(
                "  operation go(circles: Stack[T = Circle], s: Shape) -> Int64 = \
                 Stack.depth({expr})"
            ),
        ));
        assert_refused_naming(&errs, &[naming], expr);
    }
}

/// THE HINT A LAMBDA IS TYPED FROM CARRIES THE CALL'S INSTANTIATION. The call checks a lambda
/// argument against its parameter at the instantiation it made, so the binder has to be
/// hinted at that one: over a `Circle` and a `Stack[T = Shape]` — or a `Circle` and a `Shape`
/// at two bare `T`s — `v` is a `Shape` whichever argument comes first, and each call runs its
/// callback, 1 + 1 + 1 + 1. Hinted from the first sibling, as it was, `v` was a `Circle` in
/// `each(c, shapes, …)` and in `pick(c, s, …)`, and the lambda was then refused against the
/// slot the call had instantiated: `each.f (op-arg): expected Shape -> Int64, got Circle ->
/// Int64` (MEASURED).
#[test]
fn a_lambdas_hint_carries_the_calls_instantiation() {
    let runs = program(
        "wi80zv8j.h1",
        r#"  operation all(shapes: Stack[T = Shape], c: Circle, s: Shape) -> Int64 =
    Stack.each(c, shapes, lambda (v) -> area(v)) + Stack.each2(shapes, c, lambda (v) -> area(v))
      + Stack.pick(c, s, lambda (v) -> area(v)) + Stack.pick(s, c, lambda (v) -> area(v))
  operation one(s: Shape) -> Stack[T = Shape] = push(top: s, rest: empty)
  operation go() -> Int64 = all(one(circle), circle, circle)"#,
    );
    assert_eq!(run_src(&runs, "wi80zv8j.h1.go"), Ok(4));
}

/// …AND A LAMBDA THAT NEEDS MORE THAN THE INSTANTIATION GIVES IS REFUSED INSIDE ITS BODY, THE
/// SAME IN EITHER ORDER: `radius` takes a `Circle`, and `v` is a `Shape`. Hinted from the
/// first sibling, the `Circle`-first order typed the lambda at `Circle` and refused the
/// ARGUMENT instead, `pick.f (op-arg): expected Shape -> Int64, got Circle -> Int64`
/// (MEASURED). The `Shape`-first line is the control: it read this way before, and passes
/// with or without the hint's join, by design.
#[test]
fn a_lambda_is_refused_in_its_body_in_either_order() {
    for (ns, expr) in [
        ("wi80zv8j.h2", "Stack.pick(c, s, lambda (v) -> radius(v))"),
        ("wi80zv8j.h3", "Stack.pick(s, c, lambda (v) -> radius(v))"),
    ] {
        let errs = load_errors(&program(
            ns,
            &format!("  operation go(c: Circle, s: Shape) -> Int64 = {expr}"),
        ));
        assert_refused_naming(
            &errs,
            &["radius.c (op-arg): expected Circle, got Shape"],
            expr,
        );
    }
}

/// `Keyed`, a data sort that `requires Cmp` of its parameter: `Circle`'s own `Cmp` answers
/// `1`, `ShapeCmp`'s `2`, so an answer of `2` says `A = Shape` was instantiated AND its
/// dictionary handed to the call.
fn keyed_program(ns: &str, rest: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Cmp
    sort T = ?
    operation cmp(a: T, b: T) -> Int64
  end
  sort Shape
  end
  sort Circle
    provides Shape
    entity circle
    provides Cmp[T = Circle]
    operation cmp(a: Circle, b: Circle) -> Int64 = 1
  end
  sort ShapeCmp
    provides Cmp[T = Shape]
    operation cmp(a: Shape, b: Shape) -> Int64 = 2
  end
  sort Keyed
    sort A = ?
    requires Cmp[T = A]
    entity keyed(k: A)
    operation cmp2(x: A, y: A) -> Int64 = Cmp.cmp(x, y)
  end
{rest}
end
"#
    )
}

/// THE JOINED INSTANCE IS THE ONE WHOSE REQUIREMENT IS SUPPLIED. `Keyed.cmp2(c, s)` over a
/// `Circle` and a `Shape` is at `A = Shape` in either order, and the `Cmp` it runs is
/// `ShapeCmp`'s: 2 + 2. (A rule-body goal is not asked: a goal calling an operation of a sort
/// that `requires` something of its parameter is refused where the clause declares no
/// `require[…]`, before any instantiation is in question.)
#[test]
fn the_joined_instance_is_the_one_whose_requirement_is_supplied() {
    let src = keyed_program(
        "wi80zv8j.d1q",
        r#"  operation both(c: Circle, s: Shape) -> Int64 = Keyed.cmp2(c, s) + Keyed.cmp2(s, c)
  operation go() -> Int64 = both(circle, circle)"#,
    );
    assert_eq!(run_src(&src, "wi80zv8j.d1q.go"), Ok(4));
}

/// EACH PARAMETER BY ITSELF: one with no join does not keep another from its own. `A` is
/// given an `Int64` and a `String`, which have no join, so `a2` is refused as it always was;
/// `B` is given a `Circle` and then a `Shape`, which join, so `b2` is NOT refused beside it.
/// Instantiated in one pass, the pass stopped at `A` and the first field decided `B` as well:
/// the refusal named `four.b2 (entity-field): expected Circle, got Shape` too (MEASURED).
#[test]
fn a_parameter_with_no_join_does_not_keep_another_from_its_own() {
    let errs = load_errors(&program(
        "wi80zv8j.e1",
        r#"  sort Two
    sort A = ?
    sort B = ?
    entity four(a1: A, a2: A, b1: B, b2: B)
  end
  operation go(c: Circle, s: Shape) -> Int64 =
    match four(a1: 1, a2: "s", b1: c, b2: s)
      case four(_, _, _, _) -> 0"#,
    ));
    assert_refused_naming(
        &errs,
        &["four.a2 (entity-field): expected Int64, got String"],
        "two fields of one parameter with no join",
    );
    assert!(
        !errs.iter().any(|e| e.contains("four.b2")),
        "`B` has a join and must take it: {errs:?}"
    );
}

/// `Cmp`, a spec whose carrier is its `T`; `Circle provides Shape`; `in_circle` goes into
/// `Circle`'s body and `rest` after it.
fn spec_program(ns: &str, in_circle: &str, rest: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  sort Cmp
    sort T = ?
    operation cmp(a: T, b: T) -> Int64
  end
  sort Shape
  end
  sort Circle
    provides Shape
    entity circle
{in_circle}
  end
{rest}
end
"#
    )
}

/// THE RULE'S SCOPE — A SPEC'S PARAMETER IS ITS PROVISION'S, NOT THE ARGUMENTS' JOIN. `Cmp`
/// is provided by `Circle` at `T = Circle` and by `ShapeCmp` at `T = Shape`; a call of its
/// `cmp(a: T, b: T)` takes `T` from its receiver's carrier, so `Cmp.cmp(c, s)` over a `Circle`
/// and a `Shape` is refused at `b` and the other order loads — as before this change. Joined
/// as a data sort's parameter is, both orders load at `T = Shape` (MEASURED, the gate
/// removed) — and the provider that runs is still the receiver's, so `Circle`'s `cmp` would be
/// handed a `Shape`.
#[test]
fn a_specs_parameter_is_its_provisions() {
    let program = |ns: &str, call: &str| {
        spec_program(
            ns,
            "    provides Cmp[T = Circle]\n    operation cmp(a: Circle, b: Circle) -> Int64 = 1",
            &format!(
                r#"  sort ShapeCmp
    provides Cmp[T = Shape]
    operation cmp(a: Shape, b: Shape) -> Int64 = 2
  end
  operation go(c: Circle, s: Shape) -> Int64 = {call}"#
            ),
        )
    };
    assert_refused_naming(
        &load_errors(&program("wi80zv8j.p1", "Cmp.cmp(c, s)")),
        &["cmp.b (op-arg): expected Circle, got Shape"],
        "a spec's own operation over a subtype, then its supertype",
    );
    assert_eq!(
        load_errors(&program("wi80zv8j.p2", "Cmp.cmp(s, c)")),
        Vec::<String>::new()
    );
}

/// …WHETHER OR NOT ANYTHING PROVIDES IT YET. Here nothing does, and the call is licensed by
/// the enclosing sort's `requires Cmp[T = Circle]`: `T` is the clause's, and a `Shape` at `b`
/// is refused exactly as it is once a provider exists. The gate is that the sort is a DATA
/// sort. Asked instead whether anything provides the spec — which is how this was first
/// written — this program LOADED at `T = Shape` (MEASURED), and declaring `Circle provides
/// Cmp[T = Circle]` somewhere else then refused it.
#[test]
fn a_spec_nothing_provides_yet_is_a_spec_too() {
    let requiring = r#"  sort Sorter
    requires Cmp[T = Circle]
    entity sorter
    operation go(c: Circle, s: Shape) -> Int64 = Cmp.cmp(c, s)
  end"#;
    for (ns, in_circle) in [
        ("wi80zv8j.q1", ""),
        (
            "wi80zv8j.q2",
            "    provides Cmp[T = Circle]\n    operation cmp(a: Circle, b: Circle) -> Int64 = 1",
        ),
    ] {
        assert_refused_naming(
            &load_errors(&spec_program(ns, in_circle, requiring)),
            &["cmp.b (op-arg): expected Circle, got Shape"],
            "a `Shape` where the clause says `T = Circle`",
        );
    }
}

//! WI-20260904-34J8Z — A TUPLE PATTERN OVER A TYPE THE TYPER HAS NOT DECIDED is held to each use
//! of the value it takes apart (kernel-language §6.7, §4.7).
//!
//! A tuple nested in a lambda's binder list (`lambda ((a, b), c) -> …`), or one a `let` or a
//! `match` takes apart from an un-annotated binder (`lambda p -> let (a, b) = p …`), stands where
//! the value's type is a variable. WI-20261104-6HVXM gave the TOP-LEVEL binder list its own tuple,
//! so a use's arguments meet the binders; one level down, each binder still got a variable nothing
//! tied to the parent's, and a use reached none of them. The pattern now records a SHAPE — the
//! parent is a tuple of as many components as it has binders, component `i` meeting binder `i` —
//! and each call whose σ decides the parent is held to it there: another width or no tuple is
//! refused at the call, a component meets its binder there, and an un-annotated binder takes the
//! component's type in that call's σ. The shape decides no LABELS — a pattern spells none, and a
//! positional tuple would refuse every named value handed to it (§4.5) — so the labels the uses'
//! tuples carry are written onto the pattern once the walk has seen them all, and the run time
//! fetches by them; two uses giving one pattern two sets of labels are refused (user, 2026-11-05).
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: an admitted program RUNS to its value, a refusal is asserted by
//! the words that name it, beside the twin that differs in one thing and runs. The bracket in a
//! row's comment is the program's verdict on the tree before this change (bd5d1bd9, measured
//! 2026-11-05 with the debug CLI).
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! SEVENTEEN PARTS, each backed out in place over a temporary binary of this file and the twenty
//! suites nearest it — the binder lists, the tuple components and their order, destructuring by
//! label, the arity rows, the arrow's binders, a pattern typed at its position (`wi517`, `wi620`,
//! `wi782`–`wi788`, `wi791`, `wi792`, `wi794`, `wi795`, `wi801`, `wi803`, `wi_12nkg`, `wi_50b2k`,
//! `wi_6hvxm`, `wi_80259`, `wi_edpf6`): 240 rows, green with nothing backed out. Measured
//! 2026-11-05. NO ROW OF THE TWENTY FAILS UNDER ANY PART: what moves is this file's.
//!
//! 1. NO SHAPE RECORDED (the tuple arm's `shapes.push`). 11 FAIL: every row but the width row
//!    ([`another_width_is_refused_where_the_pattern_cannot_fail`]) and the control.
//! 2. NO FREEZE where the lambda's body ends (`freeze_shapes`). 3 FAIL:
//!    [`each_use_types_the_nested_binders_its_own_way`], the second use read at the first's types;
//!    [`a_generalized_binder_is_held_to_its_pattern_at_each_use`]; and
//!    [`two_uses_giving_one_pattern_two_label_sets_are_refused`] (`two4`).
//! 3. SHAPES NOT COPIED AT A ∀-ELIMINATION (`instantiate_shapes`). 1 FAILS:
//!    [`a_generalized_binder_is_held_to_its_pattern_at_each_use`], which loads and stops.
//! 4. LABELS NOT WRITTEN onto the pattern (the walk's end, `write_shape_labels`). 2 FAIL:
//!    [`the_pattern_reads_by_the_labels_its_uses_give`] (`"s"` again) and
//!    [`two_uses_giving_one_pattern_two_label_sets_are_refused`] (`two3`).
//! 5. ANOTHER LABEL SET ADMITTED (an unknown label met at component 0). 1 FAILS:
//!    [`two_uses_giving_one_pattern_two_label_sets_are_refused`].
//! 6. ONE LABEL SET IN ANOTHER ORDER MET BY POSITION, not by name. 1 FAILS: the same row (`two4`
//!    loads).
//! 7. THE COMPONENTS NOT HANDED TO THE BINDERS (`at_hole_comp`), each binder its own variable as
//!    before. 6 FAIL: [`a_nested_binder_is_solved_by_its_use`],
//!    [`a_let_or_a_match_over_an_unannotated_binder_is_held_to_its_use`],
//!    [`each_use_types_the_nested_binders_its_own_way`],
//!    [`a_pattern_after_the_call_that_decided_its_binder_reads_that_call`],
//!    [`a_generalized_binder_is_held_to_its_pattern_at_each_use`] and
//!    [`two_uses_giving_one_pattern_two_label_sets_are_refused`]. An annotated binder is held
//!    either way: its fallback is the annotation the shape holds.
//! 8. NO CLOSURE AT A CALL (`report_walk_solutions`). 10 FAIL: every row but the width row, the
//!    projection row and the control.
//! 9. A COMPONENT NOT CHECKED against its binder (`validate_arg_against_param`), only unified. 4
//!    FAIL: the refusal rows — [`a_nested_binder_list_is_held_to_its_use`],
//!    [`a_let_or_a_match_over_an_unannotated_binder_is_held_to_its_use`],
//!    [`a_function_value_at_a_slot_is_held_to_its_nested_binders`],
//!    [`a_generalized_binder_is_held_to_its_pattern_at_each_use`].
//! 10. A COMPONENT NOT UNIFIED with its binder, only checked. 4 FAIL:
//!    [`a_nested_binder_is_solved_by_its_use`], [`each_use_types_the_nested_binders_its_own_way`],
//!    [`a_pattern_after_the_call_that_decided_its_binder_reads_that_call`] and
//!    [`two_uses_giving_one_pattern_two_label_sets_are_refused`].
//! 11. THE GATE ON WHAT THIS ARGUMENT DECIDED dropped (`before`). NONE FAILS — UNDRIVEN, as the
//!    same gate of [`report_call_solutions`] is: what separates the two is an argument whose
//!    unify binds the parent and then fails while the call still types, and the argument's own
//!    check refuses such a call first. Kept for that gate's reason, and for the cost it saves.
//! 12. A LATER PATTERN NOT READ THROUGH WHAT THE WALK SOLVED (`decided_for_pattern`). 1 FAILS:
//!    [`a_pattern_after_the_call_that_decided_its_binder_reads_that_call`].
//! 13. A KNOWN TUPLE OF ANOTHER WIDTH NOT REFUSED at an irrefutable pattern. 1 FAILS:
//!    [`another_width_is_refused_where_the_pattern_cannot_fail`].
//! 14. THE PROJECTION-TYPED PARAMETER NOT HELD (the shapes at WI-398's deferred unify, held by
//!    `report_walk_solutions` there since WI-20261105-MHF0B). 1 FAILS:
//!    [`a_projection_typed_parameter_holds_the_pattern`].
//! 15. A LABELLED PATTERN MISSING FROM THE BODY NOT REFUSED (`write_shape_labels`'s `Err`). NONE
//!    FAILS — UNDRIVEN by design: no program reaches it, and it is the loud form of what would
//!    otherwise be a slot read (the full gate ran with it, and nothing raised it).
//! 16. AN OPTION COMPONENT ADMITTED, unwrapped. 1 FAILS: [`a_component_is_not_wrapped_in_some`].
//! 17. A REFUTABLE ARM OF ANOTHER WIDTH REFUSED AT A USE. 1 FAILS:
//!    [`another_width_is_refused_where_the_pattern_cannot_fail`] (`kw4`).
//!
//! PASSES UNDER EVERY PART, by design: [`what_the_shape_does_not_decide_is_unchanged`] — a named
//! value at a pattern nothing declares, labels from the type and not the binder names, a lambda
//! no use gives types to.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// A program whose `go()` is `body`, beside `decls`.
fn program(ns: &str, decls: &str, body: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, String, Bool, Function}}\n{decls}\n  operation go() -> Int64 =\n{body}\nend\n"
    )
}

fn runs(ns: &str, decls: &str, body: &str) -> Result<i64, String> {
    run_int64(&program(ns, decls, body), &format!("{ns}.go"))
}

fn refused(ns: &str, decls: &str, body: &str, tokens: &[&str], why: &str) {
    assert_refused_naming(&load_errors_of(&program(ns, decls, body)), tokens, why);
}

/// A nested binder list whose binders write their types.
const NESTED_ANN: &str = "    let g = lambda ((a: Int64, b: Int64), c) -> a * 100 + b * 10 + c";
/// The same, unannotated.
const NESTED: &str = "    let g = lambda ((a, b), c) -> a * 100 + b * 10 + c";
/// A value whose components it writes in another order than its type's.
const PERMUTED: &str = "  operation f() -> (x: Int64, y: String) = (y: \"s\", x: 1)";
const PERMUTED_INTS: &str = "  operation f() -> (x: Int64, y: Int64) = (y: 2, x: 1)";

/// A use's tuple meets the binders of a nested binder list: a component its binder's type does
/// not admit is refused at the use, and a tuple of another width, or no tuple, where the pattern
/// stands is refused there too — each was a clean load that stopped when it ran.
#[test]
fn a_nested_binder_list_is_held_to_its_use() {
    // [loads, stops: "type mismatch: expected Int64, got String and Int64"]
    refused(
        "wi_34j8z.ann",
        "",
        &format!("{NESTED_ANN}\n    g((\"x\", true), 3)"),
        &["g.a (op-arg)", "expected Int64, got String"],
        "a component the binder's annotation does not admit",
    );
    assert_eq!(runs("wi_34j8z.ann2", "", &format!("{NESTED_ANN}\n    g((1, 2), 3)")), Ok(123));
    assert_eq!(runs("wi_34j8z.ann3", "", &format!("{NESTED}\n    g((1, 2), 3)")), Ok(123));
    // [loads, raises match_failed]
    refused(
        "wi_34j8z.wide",
        "",
        &format!("{NESTED}\n    g((1, 2, 9), 3)"),
        &["(pattern-position)", "_3: Int64"],
        "a tuple of three where the pattern takes two",
    );
    // [loads, raises match_failed]
    refused(
        "wi_34j8z.scalar",
        "",
        "    let g = lambda ((a, b), c) -> c\n    g(5, 3)",
        &["(pattern-position)", "got Int64"],
        "no tuple where the pattern takes one apart",
    );
    assert_eq!(runs("wi_34j8z.scalar2", "", "    let g = lambda ((a, b), c) -> c\n    g((5, 6), 3)"), Ok(3));
}

/// A `let` or a `match` that takes apart an un-annotated binder is held to the binder's uses the
/// same way.
#[test]
fn a_let_or_a_match_over_an_unannotated_binder_is_held_to_its_use() {
    const LET: &str = "    let g = lambda p -> (let (a, b) = p  a * 10 + b)";
    // [loads, stops: "type mismatch: expected Int64, got String and Int64"]
    refused(
        "wi_34j8z.let",
        "",
        &format!("{LET}\n    g((1, true))"),
        &["g.b (op-arg)", "expected Int64, got Bool"],
        "a let over the binder, given what its body does not take",
    );
    // `a * 10` types `a` too (WI-20261105-MHF0B): before, `b` alone was held, and this refusal
    // named `g.b`. Fails with that ticket's turn-round backed out, as `matcha` below does.
    refused(
        "wi_34j8z.leta",
        "",
        &format!("{LET}\n    g((\"x\", true))"),
        &["g.a (op-arg)", "expected Int64, got String"],
        "a let over the binder, its first component what `a * 10` does not take",
    );
    assert_eq!(runs("wi_34j8z.let2", "", &format!("{LET}\n    g((1, 2))")), Ok(12));
    // [loads, raises match_failed]
    refused(
        "wi_34j8z.letscalar",
        "",
        "    let g = lambda p -> (let (a, b) = p  b)\n    g(5)",
        &["(pattern-position)", "got Int64"],
        "no tuple where the let takes one apart",
    );
    const MATCH: &str = "    let g = lambda p -> (match p case (a, b) -> a * 10 + b)";
    refused(
        "wi_34j8z.match",
        "",
        &format!("{MATCH}\n    g((1, true))"),
        &["g.b (op-arg)", "expected Int64, got Bool"],
        "a match over the binder, given what its arm does not take",
    );
    refused(
        "wi_34j8z.matcha",
        "",
        &format!("{MATCH}\n    g((\"x\", true))"),
        &["g.a (op-arg)", "expected Int64, got String"],
        "a match over the binder, its first component what `a * 10` does not take",
    );
    assert_eq!(runs("wi_34j8z.match2", "", &format!("{MATCH}\n    g((1, 2))")), Ok(12));
}

/// A pattern written AFTER a call of the body decided the binder is bound against that call's type,
/// as one written before it is held to it — the order of the two `let`s says nothing.
#[test]
fn a_pattern_after_the_call_that_decided_its_binder_reads_that_call() {
    const H: &str = "  operation h(q: (Int64, Int64)) -> Int64 = 0";
    let at = |ns: &str, body: &str| {
        format!(
            "namespace {ns}\n  import anthill.prelude.{{Int64, String}}\n{H}\n  \
             operation go() -> String =\n    let g = lambda p -> ({body})\n    g((1, 2))\nend\n"
        )
    };
    // [loads, and `go`, declared `-> String`, returns 1]
    assert_refused_naming(
        &load_errors_of(&at("wi_34j8z.ord", "let w = h(p)  let (a, b) = p  a")),
        &["go.return (op-return)", "expected String, got Int64"],
        "a pattern after the call that decided its binder",
    );
    assert_refused_naming(
        &load_errors_of(&at("wi_34j8z.ord2", "let (a, b) = p  let w = h(p)  a")),
        &["go.return (op-return)", "expected String, got Int64"],
        "the same two lets the other way round, refused before and after",
    );
    // And by the labels that call's type carries.
    assert_eq!(
        runs(
            "wi_34j8z.ord3",
            "  operation h(q: (x: Int64, y: String)) -> Int64 = 0",
            "    let g = lambda p -> (let w = h(p)  let (a, b) = p  a)\n    g((x: 1, y: \"s\"))"
        ),
        Ok(1)
    );
}

/// A shape decided at a parameter whose type is a projection — WI-398's deferred unify, which
/// reports nothing else to the walk — is held to it there.
#[test]
fn a_projection_typed_parameter_holds_the_pattern() {
    const HOLD: &str = "  sort Holder[T]\n    entity holder(v: T)\n  end\n  \
                        operation put(h: Holder, x: h.T) -> Int64 = 1";
    // [loads]
    refused(
        "wi_34j8z.proj",
        HOLD,
        "    let g = lambda p -> (let (a, b) = p  put(holder(v: (1, 2, 3)), p))\n    g((1, 2))",
        &["(pattern-position)", "_3: Int64"],
        "a three-tuple at a projection-typed parameter, over a pattern of two",
    );
    assert_eq!(
        runs("wi_34j8z.proj2", HOLD, "    let g = lambda p -> (let (a, b) = p  put(holder(v: (1, 2)), p))\n    g((1, 2))"),
        Ok(1)
    );
}

/// An irrefutable pattern over a KNOWN tuple of another width is refused, as one the uses decide
/// is. A `match` arm of another width does not match, and the next arm is tried
/// (WI-20261012-80259), whether the width is known at the arm or given by a use.
#[test]
fn another_width_is_refused_where_the_pattern_cannot_fail() {
    // [loads, raises match_failed]
    refused("wi_34j8z.kw", "", "    let (a, b) = (1, 2, 3)\n    a", &["(pattern-position)", "_3: Int64"], "a let of two over three");
    assert_eq!(runs("wi_34j8z.kw2", "", "    let (a, b) = (1, 2)\n    a"), Ok(1));
    // Refutable, both ways, before and after.
    assert_eq!(runs("wi_34j8z.kw3", "", "    match (1, 2, 3) case (a, b) -> a case _ -> 9"), Ok(9));
    assert_eq!(
        runs("wi_34j8z.kw4", "", "    let g = lambda p -> (match p case (a, b) -> a * 1 case _ -> 9)\n    g((1, 2, 3))"),
        Ok(9)
    );
    assert_eq!(
        runs("wi_34j8z.kw5", "", "    let g = lambda p -> (match p case (a, b) -> a * 1 case _ -> 9)\n    g((1, 2))"),
        Ok(1)
    );
}

/// A component is not coerced: a `some(…)` wraps an argument, and a component of a value taken
/// apart has no expression of its own to wrap — where a binder of the list itself is coerced.
#[test]
fn a_component_is_not_wrapped_in_some() {
    let opt = |ns: &str, body: &str| {
        run_int64(
            &format!(
                "namespace {ns}\n  import anthill.prelude.{{Int64, Option}}\n  \
                 import anthill.prelude.Option.{{some}}\n  operation go() -> Int64 =\n{body}\nend\n"
            ),
            &format!("{ns}.go"),
        )
    };
    // [loads; `a` is the `Int64` 1 where its type says an option]
    let errs = load_errors_of(
        "namespace wi_34j8z.opt\n  import anthill.prelude.{Int64, Option}\n  operation go() -> Int64 =\n    \
         let g = lambda ((a: Option[T = Int64], b), c) -> b\n    g((1, 2), 3)\nend\n",
    );
    assert_refused_naming(&errs, &["g.a (op-arg)", "expected Option[T = Int64], got Int64"], "a bare component at an option binder");
    assert_eq!(
        opt("wi_34j8z.opt2", "    let s = some(1)\n    let g = lambda ((a: Option[T = Int64], b), c) -> b\n    g((s, 2), 3)"),
        Ok(2)
    );
    // A binder of the list itself is an argument, and is coerced.
    assert_eq!(opt("wi_34j8z.opt3", "    let g = lambda (a: Option[T = Int64], b) -> b\n    g(1, 2)"), Ok(2));
}

/// A dispatch on a nested binder is answered by the type its use gives it, as one on a binder of
/// the list itself is (`lambda (a, b) -> a + b` then `g(1, 2)` answers 3).
#[test]
fn a_nested_binder_is_solved_by_its_use() {
    // [refused: "missing `requires Additive[T = …]` on `….go`"] for each.
    assert_eq!(runs("wi_34j8z.add", "", "    let g = lambda ((a, b), c) -> a + b\n    g((1, 2), 3)"), Ok(3));
    assert_eq!(runs("wi_34j8z.add2", "", "    let g = lambda ((a, b), c) -> a + c\n    g((1, 2), 3)"), Ok(4));
    assert_eq!(
        runs("wi_34j8z.add3", "", "    let g = lambda p -> (let (a, b) = p  a + b)\n    g((1, 2))"),
        Ok(3)
    );
}

/// A lambda handed on as a value is held to the slot it meets, at its nested binders as at its
/// own: the lambda written at the slot was refused, the same lambda bound by a `let` and passed
/// by name loaded.
#[test]
fn a_function_value_at_a_slot_is_held_to_its_nested_binders() {
    const TAKE: &str =
        "  operation take(f: ((String, Bool), Int64) -> Int64) -> Int64 = f((\"x\", true), 3)";
    // [loads, stops: "type mismatch: expected Int64, got String and Int64"]
    refused(
        "wi_34j8z.slot",
        TAKE,
        &format!("{NESTED_ANN}\n    take(g)"),
        &["take.f (op-arg)", "expected Int64, got String"],
        "a function value whose nested binder the slot contradicts",
    );
    // The lambda written at the slot, refused before and after.
    refused(
        "wi_34j8z.slot2",
        TAKE,
        "    take(lambda ((a: Int64, b: Int64), c) -> a * 100 + b * 10 + c)",
        &["(binder-annotation)", "expected String, got Int64"],
        "the same lambda written at the slot",
    );
    const APP: &str = "  operation app(f: Function[A = ((Int64, Int64), Int64), B = Int64]) -> Int64 = f((1, 2), 3)";
    assert_eq!(runs("wi_34j8z.slot3", APP, &format!("{NESTED}\n    app(g)")), Ok(123));
}

/// Each use gives the nested binders its own types, as each use gives a binder of the list its
/// own (`lambda (a, b) -> a` at `g(1, 2)` and at `g("s", true)` in one body loads).
#[test]
fn each_use_types_the_nested_binders_its_own_way() {
    // [refused: "expected Int64, got ??pat"]
    assert_eq!(
        runs(
            "wi_34j8z.uses",
            "",
            "    let g = lambda ((a, b), c) -> a\n    let x: Int64 = g((1, 2), 3)\n    let y: String = g((\"s\", true), 3)\n    x"
        ),
        Ok(1)
    );
    assert_eq!(
        runs(
            "wi_34j8z.uses2",
            "",
            "    let g = lambda ((a, b), c) -> c\n    let x = g((1, 2), 3)\n    g((\"s\", true), 4)"
        ),
        Ok(4)
    );
}

/// A binder a dispatch generalizes, where the lambda also takes it apart: `Weigh.weigh(p)` holds a
/// requirement on `p`, so the `let` quantifies `p`, and each use eliminates the ∀ to a variable of
/// its own — which the shape, naming `p`, does not mention. The elimination copies the shape at
/// the instance, and the use is held to the pattern as an unquantified one is.
#[test]
fn a_generalized_binder_is_held_to_its_pattern_at_each_use() {
    const WEIGH: &str = "  sort Weigh[T]\n    operation weigh(x: T) -> Int64\n  end\n  \
                         sort StrWeigh\n    provides Weigh[T = (String, Bool)]\n    \
                         operation weigh(x: (String, Bool)) -> Int64 = 5\n  end";
    // [loads, stops: "type mismatch: expected Int64, got Int64 and Bool"]
    refused(
        "wi_34j8z.gen",
        WEIGH,
        "    let g = lambda p -> (let (a, b) = p  let w = Weigh.weigh(p)  w + b)\n    g((\"x\", true))",
        &["g.b (op-arg)", "expected Int64, got Bool"],
        "a destructured binder whose dispatch would have generalized it",
    );
    assert_eq!(
        runs(
            "wi_34j8z.gen2",
            WEIGH,
            "    let g = lambda p -> (let (a, b) = p  let w = Weigh.weigh(p)  w)\n    g((\"x\", true))"
        ),
        Ok(5)
    );
    // Generalized, and used at two types: each use is held to the pattern at its own instance.
    // A guard that kept the binder from generalizing refused this, "one type for the lambda's
    // parameter" (review, 2026-11-05); without the `let (a, b) = p` it loads either way.
    const TWO_WEIGHS: &str = "    let g = lambda p -> (let (a, b) = p  Weigh.weigh(p))\n    \
                              g((\"x\", true)) + g((1, 2))";
    let int_weigh = format!(
        "{WEIGH}\n  sort IntWeigh\n    provides Weigh[T = (Int64, Int64)]\n    \
         operation weigh(x: (Int64, Int64)) -> Int64 = 7\n  end"
    );
    assert_eq!(runs("wi_34j8z.gen3", &int_weigh, TWO_WEIGHS), Ok(12));
}

/// The pattern reads by the labels its uses' tuples carry, as one whose type was known does: a
/// value whose components are written in another order than its type's is read by name.
#[test]
fn the_pattern_reads_by_the_labels_its_uses_give() {
    // ["s", from an operation declared `-> Int64`]
    assert_eq!(runs("wi_34j8z.lab", PERMUTED, "    let g = lambda ((a, b), c) -> a\n    g(f(), 3)"), Ok(1));
    // [2]
    assert_eq!(runs("wi_34j8z.lab2", PERMUTED_INTS, "    let g = lambda ((a, b), c) -> a\n    g(f(), 3)"), Ok(1));
    // [2]
    assert_eq!(
        runs("wi_34j8z.lab3", PERMUTED_INTS, "    let g = lambda p -> (let (a, b) = p  a)\n    g(f())"),
        Ok(1)
    );
    assert_eq!(
        runs("wi_34j8z.lab4", PERMUTED_INTS, "    let g = lambda p -> (match p case (a, b) -> a)\n    g(f())"),
        Ok(1)
    );
    // The type known at the pattern, the control: read by label before and after.
    assert_eq!(runs("wi_34j8z.lab5", PERMUTED_INTS, "    let (a, b) = f()\n    a"), Ok(1));
    // A permuted value beside a literal at the same labels, and a positional use beside a
    // labelled one: a positional value is read by slot whatever labels the pattern holds.
    assert_eq!(
        runs(
            "wi_34j8z.lab6",
            PERMUTED_INTS,
            "    let g = lambda ((a, b), c) -> a\n    g(f(), 3) + g((x: 10, y: 20), 3) * 100"
        ),
        Ok(1001)
    );
    assert_eq!(
        runs(
            "wi_34j8z.lab7",
            "",
            "    let g = lambda ((a, b), c) -> a\n    g((x: 1, y: 2), 3) + g((10, 20), 3) * 100"
        ),
        Ok(1001)
    );
}

/// A pattern reads one set of labels, so two uses giving it two are refused, naming both.
#[test]
fn two_uses_giving_one_pattern_two_label_sets_are_refused() {
    refused(
        "wi_34j8z.two",
        "",
        "    let g = lambda ((a, b), c) -> a\n    g((x: 1, y: 2), 3) + g((p: 10, q: 20), 3)",
        &["(pattern-position)", "`(x, y)`", "`(p, q)`"],
        "two label sets at one pattern",
    );
    assert_eq!(
        runs(
            "wi_34j8z.two2",
            "",
            "    let g = lambda ((a, b), c) -> a\n    g((x: 1, y: 2), 3) + g((x: 10, y: 20), 3)"
        ),
        Ok(11)
    );
    // The same labels in another order are one set, met by name: `a` is `x` at both uses. Read
    // in order they were refused as two (review, 2026-11-05).
    assert_eq!(
        runs(
            "wi_34j8z.two3",
            "",
            "    let g = lambda ((a, b), c) -> a\n    g((x: 1, y: 2), 3) + g((y: 20, x: 10), 3)"
        ),
        Ok(11)
    );
    // ... and typed by name: the second use's `x` is a `String`, which `a` takes.
    refused(
        "wi_34j8z.two4",
        "",
        "    let g = lambda ((a, b), c) -> a\n    let n: Int64 = g((x: 1, y: \"s\"), 3)\n    let m: Int64 = g((y: 2, x: \"t\"), 3)\n    n",
        &["m.annotation (let-binding)", "expected Int64, got String"],
        "a permuted use typed by name",
    );
}

/// What the shape does not decide is as it was. A named value at a pattern no type declares is
/// read by the labels its type carries (§6.7's fallback, now the use's type), not refused as a
/// positional tuple type would refuse it; the labels are the type's, never the binder names; and
/// a lambda nothing uses has no evidence for its binders.
#[test]
fn what_the_shape_does_not_decide_is_unchanged() {
    // [1]
    assert_eq!(runs("wi_34j8z.same", "", "    let g = lambda ((a, b), c) -> a\n    g((x: 1, y: 2), 3)"), Ok(1));
    // [12]
    assert_eq!(
        runs("wi_34j8z.same2", "", "    let g = lambda p -> (let (a, b) = p  a * 10 + b)\n    g((x: 1, y: 2))"),
        Ok(12)
    );
    // [2]: the use's type is `(b: Int64, a: Int64)`, and the binder named `a` reads its first.
    assert_eq!(runs("wi_34j8z.same3", "", "    let g = lambda ((a, b), c) -> a\n    g((b: 2, a: 1), 3)"), Ok(2));
    // [refused: "missing `requires Additive[T = …]`"]
    refused(
        "wi_34j8z.same4",
        "",
        "    let g = lambda ((a, b), c) -> a + b\n    1",
        &["Additive"],
        "a lambda no use gives its binders' types",
    );
}

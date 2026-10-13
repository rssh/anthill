//! WI-20261012-80259 — A PATTERN IS TYPED AT THE POSITION IT IS WRITTEN AT. A literal of
//! another type and an applied constructor of another sort are load errors, at any depth,
//! in a `match` arm, a `let` and a lambda's parameter.
//!
//! ```text
//!   sort Box   { entity box(v: Int64) }
//!   sort Shape { entity circle(r: Int64); entity square(s: Int64) }
//!
//!   f(b: Box) -> Int64 = match b case 0 -> 1 case _ -> 2                    answered 2
//!   f(b: Box) -> Int64 = match b case circle(r) -> r case box(v) -> v + 100  answered 107
//!   f(b: Box) -> Int64 = let circle(r) = b  r                               died match_failed
//! ```
//!
//! All three LOADED. The arm of such a pattern never matches, and nothing said so; the
//! second one's body even type-checked, `r` being typed from `circle`'s own field. Where a
//! pattern may not fail — a `let`, a lambda's parameter — the program died at run time.
//!
//! THE RULE (`typing::pattern_outside_position`): a pattern is asked what an expression is
//! — would a value of its sort be admitted at this position. So a position admits a literal
//! of its type, its own sort's constructors, and those of every sort it is provided by
//! ([`a_position_admits_what_its_sort_is_provided_by`]). It is asked of every sub-pattern
//! with the type threaded to it, which is what "at any depth" is.
//!
//! A RIGID POSITION ADMITS NONE OF THEM
//! ([`a_position_typed_at_a_rigid_admits_no_pattern_of_another_type`]): a type parameter of
//! the operation or its sort, a slot a declared type leaves open. Inside a body it is a
//! type equal to nothing but itself (kernel-language §8.1), so `f[T](x: T) = match x case 0
//! -> …` is refused as `if x then …` is. It RAN before, as a test of the value's type.
//!
//! WHAT IS NOT JUDGED, and stays a run-time test
//! ([`a_position_still_to_be_inferred_is_not_judged`]): a position whose type is still to
//! be inferred — an unannotated binder's variable.
//!
//! A TUPLE PATTERN is held to the same rule ([`a_tuple_pattern_where_no_tuple_can_stand`]):
//! `case (x, y)` over a `Box` loaded, and never matched.
//!
//! WHAT A PATTERN'S CONSTRUCTOR NAME DENOTES — three things found on the way, one rule:
//!
//! * A CASE IS NAMED AMONG THE SCRUTINEE'S OWN CONSTRUCTORS, so it needs no import
//!   (kernel-language, "Constructor patterns resolve against the scrutinee"): over `x: X`,
//!   `case e1(v)` is `X.e1` (`typing::position_constructor`). The loader left such a name
//!   unresolved and the typer typed its sub-patterns from no declaration at all: `case
//!   pair(x, y) -> String.length(x)` over a pair of `Int64` LOADED (MEASURED), and `x + y`
//!   was refused as an ambiguous `add`. The typer now stores the constructor it found.
//!   [`a_case_is_named_among_the_scrutinees_own_constructors`].
//! * NOTHING ELSE IS READ BY THE LAST SEGMENT OF A NAME. The matcher compared last segments
//!   where two symbols differed (`eval::pattern::functor_matches`), so `case B.leaf(s)` took
//!   an `A.leaf(v: 7)` and bound `s`, typed a `String`, to the `Int64` (MEASURED); and a
//!   name that denotes no constructor at all ran against whatever arrived. One symbol is
//!   compared now, and a name that denotes no constructor is a load error at any position:
//!   `SetLiteral` is no case of `Set`, and is written `anthill.reflect.SetLiteral`.
//!   [`a_constructor_is_never_matched_by_its_last_segment`],
//!   [`a_collection_marker_is_the_collection_it_builds`]. ONE READING BY NAME IS LEFT, and
//!   it is of DATA, not of a pattern: a value whose functor the loader left unresolved
//!   ([`a_name_the_loader_left_unresolved_in_data_is_read_by_that_name`]).
//! * A lambda's parameter with no annotation and no expected arrow takes the type its
//!   pattern states (`typing::pattern_own_type`), so `lambda circle(r) -> r` applied to a
//!   `Box` is refused at the call. NOT REACHED: a constructor of a PARAMETRIC sort there
//!   ([`known_gap_a_parametric_constructor_as_an_unannotated_parameter`]).
//!
//! ── WHICH ROWS FAIL WHEN THE CHANGE IS BACKED OUT ───────────────────────────
//!
//! Each back-out is PRESENT AND WRONG — the named check answers "admitted", the named
//! reader its old answer — APPLIED AND RUN over this file's 18 rows and the rows of the
//! older suites named below.
//!
//! * THE LITERAL CHECK — 7 FAIL: [`a_literal_of_another_type_is_refused`], [`at_any_depth`],
//!   [`where_the_pattern_may_not_fail`] (`let 0 = b` loads), the literal halves of
//!   [`an_alias_is_the_type_it_stands_for`],
//!   [`a_position_typed_at_a_rigid_admits_no_pattern_of_another_type`] and
//!   [`a_case_is_named_among_the_scrutinees_own_constructors`], and
//!   [`a_bottom_typed_position_holds_nothing`].
//! * THE CONSTRUCTOR CHECK — 9 FAIL: [`a_constructor_of_another_sort_is_refused`],
//!   [`at_any_depth`], [`where_the_pattern_may_not_fail`],
//!   [`under_a_guard_and_in_a_constants_value`], and the refusing halves of
//!   [`a_position_admits_what_its_sort_is_provided_by`],
//!   [`an_alias_is_the_type_it_stands_for`],
//!   [`a_position_typed_at_a_rigid_admits_no_pattern_of_another_type`],
//!   [`a_constructor_is_never_matched_by_its_last_segment`] (`case B.leaf(v)` over an `A`)
//!   and [`a_collection_marker_is_the_collection_it_builds`] (the marker over a `Box`).
//! * THE TUPLE CHECK — 2 FAIL: [`a_tuple_pattern_where_no_tuple_can_stand`] and the tuple
//!   row of [`a_position_typed_at_a_rigid_admits_no_pattern_of_another_type`].
//! * A RIGID POSITION LEFT UNJUDGED — 1 FAILS:
//!   [`a_position_typed_at_a_rigid_admits_no_pattern_of_another_type`]; every program in it
//!   loads and runs.
//! * THE LOOKUP OF A CASE AMONG THE POSITION'S OWN (`position_constructor`) — 2 FAIL:
//!   [`a_case_is_named_among_the_scrutinees_own_constructors`], "e1.constructor: expected
//!   known constructor", and the `known_gap_` row of a qualified operation name, which is
//!   then refused. The same two fail where the lookup stays and THE STORED PATTERN keeps
//!   the written name: the load is clean and the match fails at run time, in a plain
//!   body, a constant, and under a rule body alike. Its two parts each fail that row
//!   alone: AN ENTITY-TYPED POSITION given no case of its own (`x: X.e1`), and AN
//!   UNRESOLVED QUALIFIED NAME looked up by its last segment (`Bogus.e1(v)` loads).
//! * A NAME THAT DENOTES NO CONSTRUCTOR ADMITTED — 3 FAIL:
//!   [`a_constructor_is_never_matched_by_its_last_segment`] (the `no_such_ctor` rows
//!   load), [`a_collection_marker_is_the_collection_it_builds`] (the unnamed marker) and
//!   the `Bogus.e1` row above. Dropped only INSIDE A MISCOUNTED TUPLE — 1 FAILS, the first.
//! * THE MATCHER COMPARING LAST SEGMENTS FOR EVERY PAIR AGAIN — 1 FAILS:
//!   [`a_constructor_is_never_matched_by_its_last_segment`], 11 for 21. Comparing ONE
//!   SYMBOL AND NOTHING ELSE instead — 1 FAILS:
//!   [`a_name_the_loader_left_unresolved_in_data_is_read_by_that_name`], `match_failed`.
//! * A PARAMETER NOT GIVEN ITS PATTERN'S TYPE — 2 FAIL: [`where_the_pattern_may_not_fail`],
//!   the two rows of a parameter nothing types, and the lambda row of
//!   [`a_position_admits_what_its_sort_is_provided_by`]. THE RESTRICTION TO A SORT WITHOUT
//!   PARAMETERS removed instead — 1 FAILS: the control of
//!   [`known_gap_a_parametric_constructor_as_an_unannotated_parameter`].
//! * A LAMBDA'S BINDER LIST HELD AS A TUPLE PATTERN — 3 FAIL: the binder-list row of
//!   [`a_tuple_pattern_where_no_tuple_can_stand`], and the two older rows that own the
//!   message, `wi784_closure_arity_test::a_callback_arity_pinned_by_a_sibling_argument_is_
//!   refused_at_load` and `wi801_function_slot_arity_test::a_scalar_argument_type_admits_
//!   only_a_one_parameter_callback` ("no components to spread").
//! * NONE FAILS, and why: the exhaustiveness check reading the stored constructor
//!   (`collect_covered_entities`) where it looked the name up by its last segment again.
//!   The two differ only on a constructor of another sort that ends as one of the
//!   scrutinee's does, and that pattern is refused before coverage is read.
//!
//! WHAT THE WHOLE WORKSPACE HELD OF THE OLD BEHAVIOUR, measured by the full run: five rows
//! that wrote `SetLiteral` unimported (`eval_test` ×3, `wi_50b2k…`, `wi_80zv8_named_open_
//! slot…`), now qualified; one that took the sort's own `T` apart by a provider's
//! constructor to read which instance ran (`wi_80zv8_sibling_call_test::the_expected_type_
//! places_a_receiverless_sibling_call`), now read through the spec; and one whose
//! hand-built value named its constructor by an interned, dotted string the matcher met
//! by last segment (`wi204_sort_param_test::form_c_runtime_dispatch_through_polymorphic_
//! op`), now the resolved symbol. Nothing in the standard library, the examples or
//! anthill-todo.
//!
//! PASSES EITHER WAY, by design: [`the_controls_run_as_written`],
//! [`a_position_still_to_be_inferred_is_not_judged`], and the accepting halves of
//! [`a_position_admits_what_its_sort_is_provided_by`], [`an_alias_is_the_type_it_stands_for`]
//! and [`a_tuple_pattern_where_no_tuple_can_stand`] — each is the program beside a refusal
//! that the refusal must not reach.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// The ticket's sorts, and `decls`, which declares `go() -> Int64`.
fn program(ns: &str, decls: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String, Bool, Float, List, Option, Set, Stream}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.List.{{cons, nil}}

  sort Box
    entity box(v: Int64)
  end
  sort Shape
    entity circle(r: Int64)
    entity square(s: Int64)
  end
  enum Color
    entity red
    entity green
  end
{decls}
end
"#
    )
}

/// `decls` is refused at load, and the refusal names `tokens`.
#[track_caller]
fn refused(ns: &str, decls: &str, tokens: &[&str]) {
    assert_refused_naming(&load_errors_of(&program(ns, decls)), tokens, decls);
}

/// `decls` loads, and its `go()` runs to `n`.
#[track_caller]
fn answers(ns: &str, decls: &str, n: i64) {
    assert_eq!(
        run_int64(&program(ns, decls), &format!("{ns}.go")),
        Ok(n),
        "{decls}"
    );
}

/// `match x case {pattern} -> 1 case _ -> 2` over `x: {position}`, called with `arg`.
fn one_arm(position: &str, pattern: &str, arg: &str) -> String {
    format!(
        "  operation f(x: {position}) -> Int64 = match x case {pattern} -> 1 case _ -> 2\n  \
         operation go() -> Int64 = f({arg})"
    )
}

#[test]
fn a_literal_of_another_type_is_refused() {
    for (i, (position, pattern, arg, expected)) in [
        ("Box", "0", "box(v: 7)", "expected Box, got Int64"),
        ("String", "0", "\"a\"", "expected String, got Int64"),
        ("Int64", "\"a\"", "3", "expected Int64, got String"),
        ("Int64", "true", "3", "expected Int64, got Bool"),
        ("Bool", "1", "true", "expected Bool, got Int64"),
        ("Int64", "1.5", "3", "expected Int64, got Float"),
        // `k() -> Float = 1` is refused "expected Float, got Int64": the same question.
        ("Float", "1", "1.5", "expected Float, got Int64"),
        (
            "Option[T = Int64]",
            "0",
            "some(7)",
            "expected Option[T = Int64], got Int64",
        ),
    ]
    .into_iter()
    .enumerate()
    {
        refused(
            &format!("wi80259.lit{i}"),
            &one_arm(position, pattern, arg),
            &["pattern.literal", "pattern-position", expected],
        );
    }
}

#[test]
fn a_constructor_of_another_sort_is_refused() {
    // The ticket's second program: the first arm was dead, and `r` typed from `circle`.
    refused(
        "wi80259.ctor.box",
        "  operation f(b: Box) -> Int64 = match b case circle(r) -> r case box(v) -> v + 100\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["pattern.circle", "pattern-position", "expected Box, got Shape"],
    );
    for (i, (position, pattern, arg, tokens)) in [
        ("Int64", "box(v)", "3", ["pattern.box", "expected Int64, got Box"]),
        (
            "String",
            "some(x)",
            "\"a\"",
            ["pattern.some", "expected String, got Option"],
        ),
        // The applied spelling of a nullary constructor of another sort. The BARE name is
        // a binder there, by the rule a bare name already has.
        ("Color", "nil()", "red", ["pattern.nil", "expected Color, got List"]),
    ]
    .into_iter()
    .enumerate()
    {
        refused(
            &format!("wi80259.ctor{i}"),
            &one_arm(position, pattern, arg),
            &tokens,
        );
    }
    // Beside the scrutinee's own constructors, which cover the match: the foreign arm
    // covered nothing, so only a match of it ALONE was refused, as non-exhaustive.
    refused(
        "wi80259.ctor.enum",
        "  operation f(c: Color) -> Int64 =\n    \
           match c case circle(r) -> 0 case red -> 1 case green -> 2\n  \
         operation go() -> Int64 = f(red)",
        &["pattern.circle", "expected Color, got Shape"],
    );
}

#[test]
fn at_any_depth() {
    for (i, (position, pattern, arg, tokens)) in [
        ("Box", "box(v: \"a\")", "box(v: 7)", ["pattern.literal", "expected Int64, got String"]),
        ("Box", "box(\"a\")", "box(v: 7)", ["pattern.literal", "expected Int64, got String"]),
        (
            "Option[T = Int64]",
            "some(\"a\")",
            "some(7)",
            ["pattern.literal", "expected Int64, got String"],
        ),
        (
            "Option[T = Int64]",
            "some(box(v))",
            "some(7)",
            ["pattern.box", "expected Int64, got Box"],
        ),
        (
            "Option[T = Option[T = Box]]",
            "some(some(circle(r)))",
            "some(some(box(v: 7)))",
            ["pattern.circle", "expected Box, got Shape"],
        ),
        // A tuple's component.
        (
            "(Int64, Box)",
            "(0, circle(r))",
            "(1, box(v: 7))",
            ["pattern.circle", "expected Box, got Shape"],
        ),
        (
            "(Int64, Box)",
            "(\"a\", box(v))",
            "(1, box(v: 7))",
            ["pattern.literal", "expected Int64, got String"],
        ),
    ]
    .into_iter()
    .enumerate()
    {
        refused(
            &format!("wi80259.deep{i}"),
            &one_arm(position, pattern, arg),
            &tokens,
        );
    }
}

/// A `let` and a lambda's parameter: the programs that LOADED and died `match_failed`.
#[test]
fn where_the_pattern_may_not_fail() {
    refused(
        "wi80259.let.ctor",
        "  operation f(b: Box) -> Int64 =\n    let circle(r) = b\n    r\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["pattern.circle", "expected Box, got Shape"],
    );
    refused(
        "wi80259.let.lit",
        "  operation f(b: Box) -> Int64 =\n    let 0 = b\n    1\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["pattern.literal", "expected Box, got Int64"],
    );
    // A parameter typed by the arrow the lambda is checked against.
    refused(
        "wi80259.lambda.expected",
        "  operation ap(g: (b: Box) -> Int64, b: Box) -> Int64 = g(b)\n  \
         operation f(b: Box) -> Int64 = ap(lambda circle(r) -> r, b)\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["pattern.circle", "expected Box, got Shape"],
    );
    // A parameter nothing types: it is what its pattern states, and the CALL is refused.
    refused(
        "wi80259.lambda.own.ctor",
        "  operation f(b: Box) -> Int64 =\n    let g = lambda circle(r) -> r\n    g(b)\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["expected Shape, got Box"],
    );
    refused(
        "wi80259.lambda.own.lit",
        "  operation f(b: Box) -> Int64 =\n    let g = lambda 0 -> 1\n    g(b)\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["expected Int64, got Box"],
    );
}

/// A guarded arm and a constant's value are held to the same rule; a bare nullary name the
/// typer rewrites to a constructor is one of the position's own by construction.
#[test]
fn under_a_guard_and_in_a_constants_value() {
    refused(
        "wi80259.guard",
        "  operation f(b: Box) -> Int64 = match b case circle(r) | r > 0 -> r case _ -> 2\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["pattern.circle", "expected Box, got Shape"],
    );
    refused(
        "wi80259.constant",
        "  const k: Int64 = match box(v: 1) case circle(r) -> r case _ -> 0\n  \
         operation go() -> Int64 = k",
        &["pattern.circle", "expected Box, got Shape"],
    );
    answers(
        "wi80259.rewritten",
        "  operation f(c: Color) -> Int64 = match c case red -> 1 case green -> 2\n  \
         operation go() -> Int64 = f(green)",
        2,
    );
}

#[test]
fn the_controls_run_as_written() {
    for (i, (position, pattern, arg)) in [
        ("Int64", "3", "3"),
        ("String", "\"x\"", "\"x\""),
        ("Bool", "true", "true"),
        ("Float", "1.5", "1.5"),
        ("Box", "box(v: 7)", "box(v: 7)"),
        ("Box", "box(7)", "box(v: 7)"),
        ("Option[T = Int64]", "some(7)", "some(7)"),
        ("Option[T = Box]", "some(box(v))", "some(box(v: 7))"),
        ("List[T = Int64]", "cons(7, nil())", "[7]"),
        ("(Int64, Box)", "(1, box(v))", "(1, box(v: 7))"),
        ("Shape", "circle(r)", "circle(r: 7)"),
    ]
    .into_iter()
    .enumerate()
    {
        answers(
            &format!("wi80259.control{i}"),
            &one_arm(position, pattern, arg),
            1,
        );
    }
    answers(
        "wi80259.control.let",
        "  operation f(b: Box) -> Int64 =\n    let box(v) = b\n    v\n  \
         operation go() -> Int64 = f(box(v: 7))",
        7,
    );
    answers(
        "wi80259.control.lambda",
        "  operation f(b: Box) -> Int64 =\n    let g = lambda box(v) -> v\n    g(b)\n  \
         operation go() -> Int64 = f(box(v: 7))",
        7,
    );
    // A BARE name that is a nullary constructor of ANOTHER sort is a binder, and catches
    // everything: the rule a bare name already has, which this ticket leaves.
    answers(
        "wi80259.control.bare",
        "  operation f(c: Color) -> Int64 = match c case nil -> 1 case _ -> 2\n  \
         operation go() -> Int64 = f(red)",
        1,
    );
}

/// The ticket's second question: a position typed at a sort that others provide, or at an
/// entity. It admits the constructors of every sort a value there may be of.
#[test]
fn a_position_admits_what_its_sort_is_provided_by() {
    const ANIMALS: &str = r#"
  sort Animal
  end
  sort Dog
    provides Animal
    entity dog(n: Int64)
  end
  sort Cat
    provides Animal
    entity cat(n: Int64)
  end
"#;
    answers(
        "wi80259.provided.ok",
        &format!(
            "{ANIMALS}  operation f(a: Animal) -> Int64 = match a case dog(n) -> n case _ -> 0\n  \
             operation go() -> Int64 = f(dog(n: 7))"
        ),
        7,
    );
    // The other way round: a `Dog` is never a `cat`.
    refused(
        "wi80259.provided.sibling",
        &format!(
            "{ANIMALS}  operation f(a: Dog) -> Int64 = match a case cat(n) -> n case _ -> 0\n  \
             operation go() -> Int64 = f(dog(n: 7))"
        ),
        &["pattern.cat", "expected Dog, got Cat"],
    );
    // And a sort that provides nothing the position is: `box` under an `Animal`.
    refused(
        "wi80259.provided.unrelated",
        &format!(
            "{ANIMALS}  operation f(a: Animal) -> Int64 = match a case box(v) -> v case _ -> 0\n  \
             operation go() -> Int64 = f(dog(n: 7))"
        ),
        &["pattern.box", "expected Animal, got Box"],
    );
    // A PARAMETER NOTHING TYPES is what its pattern states, a `Dog`: such a lambda is not
    // a function of an `Animal`, and the call says so. (It ran, and failed at the match on
    // a `cat`.) Typed by the arrow it is passed at, the same lambda is one.
    refused(
        "wi80259.provided.lambda",
        &format!(
            "{ANIMALS}  operation f(a: Animal) -> Int64 =\n    let g = lambda dog(n) -> n\n    g(a)\n  \
             operation go() -> Int64 = f(dog(n: 7))"
        ),
        &["expected Dog, got Animal"],
    );
    answers(
        "wi80259.provided.lambda.typed",
        &format!(
            "{ANIMALS}  operation ap(g: (a: Animal) -> Int64, a: Animal) -> Int64 = g(a)\n  \
             operation go() -> Int64 = ap(lambda dog(n) -> n, dog(n: 7))"
        ),
        7,
    );
    // A `List` is a `Stream`.
    answers(
        "wi80259.provided.stream",
        "  operation f(s: Stream[T = Int64]) -> Int64 = match s case cons(h, _) -> h case _ -> 0\n  \
         operation go() -> Int64 = f([7])",
        7,
    );
    // A position typed at an ENTITY holds that entity's values alone.
    answers(
        "wi80259.entity.ok",
        "  operation f(c: circle) -> Int64 = match c case circle(r) -> r\n  \
         operation go() -> Int64 = f(circle(r: 7))",
        7,
    );
    refused(
        "wi80259.entity.sibling",
        "  operation f(c: circle) -> Int64 = match c case square(s) -> s case _ -> 2\n  \
         operation go() -> Int64 = f(circle(r: 7))",
        &["pattern.square", "expected circle, got Shape"],
    );
}

#[test]
fn an_alias_is_the_type_it_stands_for() {
    const STRM: &str = r#"
  sort Strm
    sort T = ?
    entity strm(a: T)
  end
  sort IntS = Strm[T = Int64]
"#;
    answers(
        "wi80259.alias.ok",
        &format!(
            "{STRM}  operation f(x: IntS) -> Int64 = match x case strm(a) -> a\n  \
             operation go() -> Int64 = f(strm(a: 7))"
        ),
        7,
    );
    refused(
        "wi80259.alias.ctor",
        &format!(
            "{STRM}  operation f(x: IntS) -> Int64 = match x case box(v) -> v case _ -> 2\n  \
             operation go() -> Int64 = f(strm(a: 7))"
        ),
        &["pattern.box", "got Box"],
    );
    refused(
        "wi80259.alias.deep",
        &format!(
            "{STRM}  operation f(x: IntS) -> Int64 = match x case strm(\"q\") -> 3 case _ -> 2\n  \
             operation go() -> Int64 = f(strm(a: 7))"
        ),
        &["pattern.literal", "expected Int64, got String"],
    );
}

/// The ticket's first question, and kernel-language §8.1 answers the half of it that is a
/// RIGID: inside a body a type parameter of the operation or of its sort, and a slot a
/// declared type leaves open, is a type equal to nothing but itself — so it is no
/// literal's, no constructor's and no tuple's, as it is no `Bool` for an `if`.
#[test]
fn a_position_typed_at_a_rigid_admits_no_pattern_of_another_type() {
    // These RAN: `f(0)` answered 1 and `f(box(v: 7))` 2, a test of the value's type at
    // run time that the signature does not allow the body.
    refused(
        "wi80259.rigid.lit",
        "  operation f[T](x: T) -> Int64 = match x case 0 -> 1 case _ -> 2\n  \
         operation go() -> Int64 = f(0)",
        &["pattern.literal", "expected ?T, got Int64"],
    );
    refused(
        "wi80259.rigid.ctor",
        "  operation f[T](x: T) -> Int64 = match x case box(v) -> v case _ -> 2\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["pattern.box", "expected ?T, got Box"],
    );
    refused(
        "wi80259.rigid.tuple",
        "  operation f[T](x: T) -> Int64 = match x case (a, b) -> 1 case _ -> 2\n  \
         operation go() -> Int64 = f((1, 2))",
        &["pattern.tuple", "expected ?T, got (_1: "],
    );
    // A sort's own parameter, under one of its constructors.
    refused(
        "wi80259.rigid.sort",
        "  sort Tree\n    sort T = ?\n    entity leaf(v: T)\n    \
           operation lit(t: Self) -> Int64 = match t case leaf(0) -> 1 case _ -> 2\n  end\n  \
         operation go() -> Int64 = Tree.lit(leaf(v: 0))",
        &["pattern.literal", "expected ?T, got Int64"],
    );
    // A slot the declared type leaves open: any list, so an element of a type the body
    // does not know.
    refused(
        "wi80259.rigid.open",
        "  operation f(xs: List) -> Int64 = match xs case cons(0, _) -> 1 case _ -> 2\n  \
         operation go() -> Int64 = f([0])",
        &["pattern.literal", "expected xs.T, got Int64"],
    );
    // What such a position does admit: a binder, a wildcard, and under a sort's own
    // constructor whatever that constructor's fields admit. Passes either way.
    answers(
        "wi80259.rigid.control",
        "  operation f[T](o: Option[T = T], d: Int64) -> Int64 =\n    \
           match o case some(y) -> d case none() -> 0\n  \
         operation g(xs: List) -> Int64 = match xs case cons(h, _) -> 1 case _ -> 2\n  \
         operation go() -> Int64 = f(some(box(v: 1)), 6) + g([0])",
        7,
    );
}

/// The other half: a position whose type is STILL TO BE INFERRED is not judged, and the
/// pattern is a run-time test there. Passes either way.
#[test]
fn a_position_still_to_be_inferred_is_not_judged() {
    answers(
        "wi80259.flexible",
        "  operation f(b: Box) -> Int64 =\n    \
           let g = lambda x -> match x case 0 -> 1 case _ -> 2\n    g(b)\n  \
         operation go() -> Int64 = f(box(v: 7))",
        2,
    );
}

/// `X` and its two cases in one namespace, and `decls` — which declares `go() -> Int64` —
/// in another that imports the SORT alone.
fn shop_and_user(decls: &str) -> String {
    format!(
        r#"
namespace wi80259.shop
  import anthill.prelude.{{Int64}}
  sort X
    entity e1(v: Int64)
    entity e2(w: Int64)
  end
  enum Color
    entity red
    entity green
  end
  sort Item
    entity item(c: Color, n: Int64)
  end
end

namespace wi80259.user
  import anthill.prelude.{{Int64, String, List, Error}}
  import anthill.prelude.List.{{length, cons, nil}}
  import wi80259.shop.{{X, Color, Item}}
{decls}
end
"#
    )
}

/// The whole program of the rule: `X`'s entities are named in a `match` over an `X` by a
/// namespace that imports the sort alone.
#[test]
fn a_case_is_named_among_the_scrutinees_own_constructors() {
    let runs = |decls: &str, n: i64| {
        assert_eq!(run_int64(&shop_and_user(decls), "wi80259.user.go"), Ok(n), "{decls}");
    };
    const F: &str =
        "  operation f(x: X) -> Int64 = match x case e1(v) -> v case e2(w) -> w + 100\n";
    runs(
        &format!("{F}  operation go() -> Int64 = f(X.e1(v: 7)) + f(X.e2(w: 7))"),
        114,
    );
    // `v` is typed from `X.e1`'s field.
    assert_refused_naming(
        &load_errors_of(&shop_and_user(
            "  operation f(x: X) -> Int64 = match x case e1(v) -> String.length(v) case _ -> 0\n  \
             operation go() -> Int64 = f(X.e1(v: 7))",
        )),
        &["expected String, got Int64"],
        "a sub-pattern of a case named without an import is typed from its field",
    );
    // A position typed at an ENTITY has that entity for its one case.
    runs(
        "  operation f(x: X.e1) -> Int64 = match x case e1(v) -> v\n  \
         operation go() -> Int64 = f(X.e1(v: 7))",
        7,
    );
    // An operation of the same name in scope does not hide the case.
    runs(
        "  operation e1(n: Int64) -> Int64 = n + 1\n  \
         operation f(x: X) -> Int64 = match x case e1(v) -> v case _ -> 0\n  \
         operation go() -> Int64 = f(X.e1(v: 7))",
        7,
    );
    // The bare spelling of a nullary case, and the applied one.
    runs(
        "  operation f(c: Color) -> Int64 = match c case red -> 3 case green() -> 4\n  \
         operation go() -> Int64 = f(Color.red()) + f(Color.green())",
        7,
    );
    // WHERE THE STORED PATTERN IS WHAT RUNS, outside a plain call: a constant's value, an
    // operation called from a rule body, a lambda written in one. Each holds the
    // constructor the typer found; a pattern left with the written name matches nothing.
    runs(
        "  const k: Int64 = match X.e1(v: 7) case e1(v) -> v case e2(w) -> w + 100\n  \
         operation go() -> Int64 = k",
        7,
    );
    const PICK: &str =
        "  operation pick(c: Color) -> Int64 = match c case red -> 1 case green -> 2\n";
    const GO: &str = "  operation go() -> Int64\n    effects Error\n  = length(which.takeN(5))";
    runs(
        &format!("{F}{PICK}  rule which(?c) :- pick(?c) = 2, f(X.e1(v: 7)) = 7\n{GO}"),
        1,
    );
    runs(
        &format!(
            "{PICK}  operation ap(g: (x: X) -> Int64, x: X) -> Int64 = g(x)\n  \
             rule which(?c) :- pick(?c) = 2,\n    \
               ap(lambda (y: X) -> match y case e1(v) -> v case _ -> 0, X.e1(v: 7)) = 7\n{GO}"
        ),
        1,
    );
    // The name as written, whole: a qualifier that resolves to nothing names nothing. It
    // was read as `X.e1` by its last segment.
    assert_refused_naming(
        &load_errors_of(&shop_and_user(
            "  operation f(x: X) -> Int64 = match x case Bogus.e1(v) -> v case _ -> 2\n  \
             operation go() -> Int64 = f(X.e1(v: 7))",
        )),
        &["Bogus.e1.constructor", "expected known constructor"],
        "an unresolved qualified name is no case of the position's sort",
    );

    const PAIR: &str = "anthill.prelude.Pair[A = Int64, B = Int64]";
    const MK: &str = "anthill.prelude.Pair.pair(fst: 3, snd: 4)";
    // `pair` is not imported.
    answers(
        "wi80259.name.match",
        &format!(
            "  operation f(o: {PAIR}) -> Int64 = match o case pair(x, y) -> x + y\n  \
             operation go() -> Int64 = f({MK})"
        ),
        7,
    );
    answers(
        "wi80259.name.let",
        &format!(
            "  operation f(o: {PAIR}) -> Int64 =\n    let pair(x, y) = o\n    x + y\n  \
             operation go() -> Int64 = f({MK})"
        ),
        7,
    );
    refused(
        "wi80259.name.deep",
        &format!(
            "  operation f(o: {PAIR}) -> Int64 = match o case pair(\"a\", y) -> 1 case _ -> 2\n  \
             operation go() -> Int64 = f({MK})"
        ),
        &["pattern.literal", "expected Int64, got String"],
    );
    // At depth: the field's own constructors, as the whole pattern's are the scrutinee's.
    answers(
        "wi80259.name.nested",
        &format!(
            "  operation f(o: Option[T = {PAIR}]) -> Int64 =\n    \
               match o case some(pair(x, y)) -> x + y case _ -> 0\n  \
             operation go() -> Int64 = f(some({MK}))"
        ),
        7,
    );
}

/// A lookup among ONE sort's constructors is the only reading by name there is. Two
/// constructors that end in the same segment are two constructors, and a name that denotes
/// none is an error wherever it is written.
#[test]
fn a_constructor_is_never_matched_by_its_last_segment() {
    const LEAVES: &str = "  sort A\n    entity leaf(v: Int64)\n  end\n  \
                          sort B\n    entity leaf(s: String)\n  end\n";
    // Where the position is not judged the matcher decides, and it compares the symbol:
    // the first of these answered 1, the arm taking the `A.leaf`.
    answers(
        "wi80259.segment.run",
        &format!(
            "{LEAVES}  operation f(a: A) -> Int64 =\n    \
               let g = lambda x -> match x case B.leaf(s) -> 1 case _ -> 2\n    g(a)\n  \
             operation h(b: B) -> Int64 =\n    \
               let g = lambda x -> match x case B.leaf(s) -> 1 case _ -> 2\n    g(b)\n  \
             operation go() -> Int64 = f(A.leaf(v: 7)) * 10 + h(B.leaf(s: \"q\"))"
        ),
        21,
    );
    // Where it is judged, a name the scope resolved to a constructor is that constructor,
    // whatever the position has under the same last segment.
    refused(
        "wi80259.segment.load",
        &format!(
            "{LEAVES}  operation f(a: A) -> Int64 = match a case B.leaf(v) -> 1 case _ -> 2\n  \
             operation go() -> Int64 = f(A.leaf(v: 7))"
        ),
        &["pattern.leaf", "expected A, got B"],
    );
    // A name that is no case of the position's sort and nothing in scope.
    refused(
        "wi80259.segment.none",
        &one_arm("Box", "no_such_ctor(x)", "box(v: 7)"),
        &["no_such_ctor.constructor", "expected known constructor"],
    );
    // The same where the position is not judged: it ran against whatever arrived.
    refused(
        "wi80259.segment.none.variable",
        "  operation f(b: Box) -> Int64 =\n    \
           let g = lambda x -> match x case no_such_ctor(a) -> 1 case _ -> 2\n    g(b)\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["no_such_ctor.constructor", "expected known constructor"],
    );
    // Inside a tuple pattern whose count differs from the position's, where what is
    // judged against a component is not reported: this is judged against none.
    refused(
        "wi80259.segment.none.tuple",
        &one_arm("(Int64, Int64, Int64)", "(no_such_ctor(a), y)", "(1, 2, 3)"),
        &["no_such_ctor.constructor", "expected known constructor"],
    );
    refused(
        "wi80259.segment.none.let",
        "  operation f(b: Box) -> Int64 =\n    let no_such_ctor(x) = b\n    1\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["no_such_ctor.constructor", "expected known constructor"],
    );
}

/// WHAT IS STILL READ BY ITS NAME, pinned as it is: a value whose functor the LOADER left
/// unresolved. A fact written where `red` is not imported holds the name `red` — an atom,
/// no constructor of anything — and `case red()` over that field answers through the
/// matcher's comparison of the atom's name (`eval::pattern::functor_matches`). With one
/// symbol compared and nothing else this died `match_failed` (MEASURED, review): the
/// defect is the fact, which is not held to its field's type where it is loaded.
#[test]
fn a_name_the_loader_left_unresolved_in_data_is_read_by_that_name() {
    let src = r#"
namespace wi80259.data.shop
  import anthill.prelude.{Int64}
  enum Color
    entity red
    entity green
  end
  sort Item
    entity item(c: Color, n: Int64)
  end
end

namespace wi80259.data.facts
  import wi80259.data.shop.{Item}
  import wi80259.data.shop.Item.{item}
  fact item(c: red, n: 1)
end

namespace wi80259.data.user
  import anthill.prelude.{Int64, List, Error}
  import anthill.prelude.List.{cons, nil}
  import wi80259.data.shop.{Color, Item}
  import wi80259.data.shop.Item.{item}
  rule col(?c) :- item(c: ?c, n: ?n)
  operation go() -> Int64
    effects Error
  =
    match col.takeN(5)
      case cons(row, _) -> (match row.c case red -> 7 case green -> 3)
      case nil() -> 0
end
"#;
    assert_eq!(run_int64(src, "wi80259.data.user.go"), Ok(7));
}

/// NOT REACHED, pinned as it is. A name the scope resolved to something that is no
/// constructor is looked up among the position's own by the name it has, so that an
/// operation called `e1` in scope does not hide the case `e1`. A pattern does not carry
/// whether its name was written with a qualifier, so `H.e1(v)`, which names an OPERATION,
/// is read as the case too — as it was before, by the matcher.
#[test]
fn known_gap_a_qualified_name_of_no_constructor_is_read_as_the_case() {
    assert_eq!(
        run_int64(
            &shop_and_user(
                "  sort H\n    operation e1(n: Int64) -> Int64 = n + 1\n  end\n  \
                 operation f(x: X) -> Int64 = match x case H.e1(v) -> v case _ -> 0\n  \
                 operation go() -> Int64 = f(X.e1(v: 7))",
            ),
            "wi80259.user.go"
        ),
        Ok(7),
    );
}

/// `case anthill.reflect.SetLiteral(a, _, _)` over a `Set` is how a set's elements are
/// taken apart. The marker is the collection it builds; it is no case of `Set`, so it is
/// named as any other constructor is — qualified, or imported.
#[test]
fn a_collection_marker_is_the_collection_it_builds() {
    answers(
        "wi80259.marker.qualified",
        "  operation f(s: Set[T = Int64]) -> Int64 =\n    \
           match s case anthill.reflect.SetLiteral(a, _, _) -> a case _ -> 0\n  \
         operation go() -> Int64 = f({7, 20, 30})",
        7,
    );
    answers(
        "wi80259.marker.imported",
        "  import anthill.reflect.{SetLiteral}\n  \
         operation f(s: Set[T = Int64]) -> Int64 =\n    \
           match s case SetLiteral(a, _, _) -> a case _ -> 0\n  \
         operation go() -> Int64 = f({7, 20, 30})",
        7,
    );
    // Neither: the name denotes nothing. It ran, the matcher comparing last segments.
    refused(
        "wi80259.marker.unnamed",
        "  operation f(s: Set[T = Int64]) -> Int64 =\n    \
           match s case SetLiteral(a, _, _) -> a case _ -> 0\n  \
         operation go() -> Int64 = f({7, 20, 30})",
        &["SetLiteral.constructor", "expected known constructor"],
    );
    refused(
        "wi80259.marker.other",
        &one_arm("Box", "anthill.reflect.SetLiteral(a, _, _)", "box(v: 7)"),
        &["pattern.SetLiteral", "expected Box, got Set"],
    );
}

/// A tuple pattern matches a tuple and nothing else. The count of its components is not
/// part of this: a tuple-typed position admits a tuple pattern of any count, and a count
/// that differs is the match's to refuse at run time, as it was.
#[test]
fn a_tuple_pattern_where_no_tuple_can_stand() {
    refused(
        "wi80259.tuple.match",
        &one_arm("Box", "(x, y)", "box(v: 7)"),
        &["pattern.tuple", "pattern-position", "expected Box, got (_1: "],
    );
    refused(
        "wi80259.tuple.let",
        "  operation f(b: Box) -> Int64 =\n    let (x, y) = b\n    1\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["pattern.tuple", "expected Box, got (_1: "],
    );
    refused(
        "wi80259.tuple.deep",
        &one_arm("Option[T = Int64]", "some((x, y))", "some(7)"),
        &["pattern.tuple", "expected Int64, got (_1: "],
    );
    refused(
        "wi80259.tuple.unit",
        &one_arm("Box", "()", "box(v: 7)"),
        &["pattern.tuple", "expected Box, got Unit"],
    );
    // A lambda's binder LIST is its parameters and no tuple pattern: two binders where the
    // callback takes one `Box` is the arity check's to refuse, in its own words. Passes
    // either way.
    refused(
        "wi80259.tuple.lambda",
        "  operation ap(g: (a: Box) -> Int64, b: Box) -> Int64 = g(b)\n  \
         operation f(b: Box) -> Int64 = ap(lambda (x, y) -> 1, b)\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["expected a 1-parameter function", "got a 2-parameter function"],
    );
    // A tuple pattern INSIDE the list is one.
    refused(
        "wi80259.tuple.lambda.inner",
        "  operation ap(g: (a: Box, n: Int64) -> Int64, b: Box) -> Int64 = g(b, 1)\n  \
         operation f(b: Box) -> Int64 = ap(lambda ((x, y), n) -> n, b)\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["pattern.tuple", "expected Box, got (_1: "],
    );
    for (i, (position, pattern, arg, n)) in [
        ("(Int64, Int64)", "(3, y)", "(3, 4)", 1),
        ("(a: Int64, b: Int64)", "(3, y)", "(a: 3, b: 4)", 1),
        ("anthill.prelude.Unit", "()", "()", 1),
        // A count that differs loads, and does not match.
        ("(Int64, Int64, Int64)", "(x, y)", "(3, 4, 5)", 2),
    ]
    .into_iter()
    .enumerate()
    {
        answers(
            &format!("wi80259.tuple.control{i}"),
            &one_arm(position, pattern, arg),
            n,
        );
    }
    answers(
        "wi80259.tuple.alias",
        "  sort Pt = (x: Int64, y: Int64)\n  \
         operation f(p: Pt) -> Int64 = match p case (a, b) -> a + b\n  \
         operation go() -> Int64 = f((x: 3, y: 4))",
        7,
    );
    answers(
        "wi80259.tuple.callback",
        "  operation ap(g: (a: Int64, b: Int64) -> Int64) -> Int64 = g(3, 4)\n  \
         operation go() -> Int64 = ap(lambda (x, y) -> x + y)",
        7,
    );
}

/// A value bound to a name with a slot nothing fills is at the bottom type there (proposal
/// 070), and the bottom type holds no value: a literal under it is outside it.
#[test]
fn a_bottom_typed_position_holds_nothing() {
    refused(
        "wi80259.bottom",
        "  operation f(b: Box) -> Int64 =\n    let xs = nil\n    \
           match xs case cons(0, _) -> 1 case _ -> 2\n  \
         operation go() -> Int64 = f(box(v: 7))",
        &["pattern.literal", "expected nothing, got Int64"],
    );
}

/// NOT REACHED, pinned as it is. A constructor of a PARAMETRIC sort written as a parameter
/// nothing types states its sort and not the sort's arguments; the parameter keeps its
/// inference variable (`typing::pattern_own_type` says why), so a value of another sort
/// binds it and the program fails at the match.
#[test]
fn known_gap_a_parametric_constructor_as_an_unannotated_parameter() {
    // The row the restriction is there for: it was refused "expected Int64, got ?T" when
    // the parameter was given the bare sort.
    answers(
        "wi80259.gap.control",
        "  operation f(o: Option[T = Int64]) -> Int64 =\n    let g = lambda some(x) -> x\n    g(o)\n  \
         operation go() -> Int64 = f(some(7))",
        7,
    );
    let died = run_int64(
        &program(
            "wi80259.gap",
            "  operation f(b: Box) -> Int64 =\n    let g = lambda some(x) -> 1\n    g(b)\n  \
             operation go() -> Int64 = f(box(v: 7))",
        ),
        "wi80259.gap.go",
    );
    // Loaded, and raised at the match: a load error is the refusals joined, and names
    // neither.
    assert!(
        died.as_ref()
            .is_err_and(|e| e.contains("did not run to an Int64") && e.contains("Raised")),
        "{died:?}"
    );
}

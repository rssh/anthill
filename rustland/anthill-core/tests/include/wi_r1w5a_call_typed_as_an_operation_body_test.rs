//! WI-20261013-R1W5A (068 C1c) — A CALL IN A RULE BODY IS TYPED AS AN OPERATION BODY IS
//! (068-implementation §6.2, decision 4): an operation's application written in a value slot,
//! or as the goal that is its call (`f(args)` of a `Bool`, `f(args, ?r)`), is handed to the
//! operation-body typer whole, equations on, and the stored call is the rewritten one. Before,
//! such a call was a data term the walk only name-checked, so an operation defined by its
//! equation had nothing to run, an argument list was held to nothing, and one call answered
//! by the shape the walk handed the typer: `?x <=> Box.open(Box.mk(4))` left a residual where
//! `?x <=> Box.mk(4).open()` answered 4.
//!
//! What the call is typed in is the operation body's text (`RuleText::Fragment`): a literal,
//! a `()` and a bare operation name read as an operation body reads them. Its callee's own
//! `requires` is a condition of the clause there, which the clause's inference supplies as
//! before (`infer_rule_body_requirements`); making the typer's classification that
//! inference's input is WI-20261013-RYDNV's.
//!
//! Decided with the user on the way (2026-10-23): a `cons`/`nil` spine at a slot that declares
//! its element type is checked as the literal it is lowered from (kernel-language §4.6), in
//! both bodies; and a type written in a call's argument — a dotted sort path, a sort's
//! bracket — is the type value it denotes there, as in an operation body.
//!
//! Found on the way, and fixed: the clause typing read a call's positional arguments only, so
//! a labelled argument typed nothing (`constrain_application`).
//!
//! ## Back-out
//!
//! Each piece made a no-op in place under a switch of its own, one optimized build, and the
//! whole `wi_tests` binary run under each (measured 2026-10-23; the last two pieces over
//! this file alone):
//!
//! | backed out | fails |
//! |---|---|
//! | an operation's application a fragment (`operation_application`) | here every row of decision 4's table, the three spellings, the rewrite's calls, the some-coercion, the Bool goal and the argument list; `wi_mhrn1…::a_labelled_call_with_a_positional_argument_left_over_does_not_run` and `wi_qqpq2…::a_positional_tuple_meeting_a_name_keyed_pattern_reads_by_slot` (each loads again) |
//! | a goal on an operation a fragment (the goal rung of `call_dispatch_shape`) | `a_bool_goal_runs_its_equation`, `the_goal_with_a_result_column_runs_the_equation`, `a_calls_argument_list_and_types_are_held_to_its_parameters` (its goal) |
//! | a goal of another shape left to the goal check (`operation_goal_reading`) | `wi_8k4rb…::a_declared_operation_carrying_equations_keeps_the_operation_diagnosis` |
//! | `f(args, ?r)` stored as `?r <=> …` (`rewritten_functional_goal`) | `the_goal_with_a_result_column_runs_the_equation` |
//! | the operation body's text (`TypingEnv::as_fragment`) | `the_unit_an_equation_leaves_in_an_argument_is_unit`, and every row of the next line: typed in the rule's text, a call stamps its callee's slots |
//! | a callee's own `requires` left to the clause (`check_apply_iter`'s op-scoped stamp) | 37: `wi_p7vp4` ×15, `wi_nekr0` ×10, `wi_gfs6a` ×4, `wi_prva2` ×3, `wi_0rrqp` ×2, `wi_mhrn1` ×2, `wi_9wvt7_reify_rule_body` ×1 |
//! | a labelled argument typing its variable (`constrain_application`) | `a_labelled_argument_types_its_variable`, `wi_p7vp4…::a_named_argument_bool_view_call_answers_through_the_callers_dictionary` |
//! | a bare name a reference the slot hints (`is_hof_shaped`'s `Ref`) | `wi_50b2k…::a_positional_argument_beside_a_named_one_is_hinted_from_the_slot_it_takes`, `wi_qqpq2…::an_eta_d_operation_name_is_a_known_gap` (refused at load) |
//! | a dotted name no call (`operation_application`'s `field_access`) | `dotted_nullary_op_call` ×5, `wi_4nekz` ×3, `wi_2nxac`, `wi_rxt6s…::a_data_slot_still_stores_the_chain` |
//! | the spine's seed (`check_constructor_iter`), its fields' hints (`spine_field_expected`), its argument's hint (`seq_literal_kind`), each alone | `a_spine_at_a_declaring_slot_is_checked_as_the_literal` |
//! | a type in a call's argument built as an operation body's (`Loader::written_type_in_call_argument`) | `a_type_in_a_calls_argument_is_its_type_value`, `wi_rxt6s…::a_rule_bodys_call_argument_is_the_sort`, `wi_tcsgt…::the_three_walks_build_one_value` |
//! | a method call's arguments a call's (`Loader::dot_apply_expr`) | `a_type_in_a_calls_argument_is_its_type_value`, by its dot |
//! | a connective's goals not a call's arguments (the loader's goal-slot test) | `wi_vnwaw` ×2, `wi_vzc2c` |
//! | a comparison's operands not a call's arguments (the loader's equality test) | `wi_4nekz…::the_five_other_name_kinds_still_agree_with_the_operation_body`, `wi_vnwaw…::a_data_slot_keeps_the_dotted_reference_on_both_sides_of_a_match` |
//! | a dot's value read in the operation body's text (`dot_value_type`) | `the_unit_an_equation_leaves_in_an_argument_is_unit` |
//! | a goal's arguments the rule's own term (the loader's `!at_goal`) | `a_goal_on_an_operation_with_clauses_matches_as_written`, `a_type_in_a_calls_argument_is_its_type_value` (its goal answers 21) |
//! | a goal holding such a type keeping its goal reading (`holds_a_type_as_the_rules_term`) | `a_type_in_a_calls_argument_is_its_type_value`, by its goal: refused, a plain reference to the sort |
//!
//! Not driven, and said rather than claimed: a `Ref` is a reference the slot hints only where
//! it names an operation, so an operation body's `Ref` — a nullary constructor, a resolved
//! name — is staged as before (WI-793); widened back to every `Ref`, no row fails. The same
//! for the inline-description guard on a type candidate the loader declines, and the one
//! `@[simp]` gate per pass, a cost.
//!
//! CONTROLS, green under every back-out: `control_the_lambda_and_the_test_answered_before`,
//! and the controls of the rows that name one.

use crate::common::{
    assert_refused_naming, load_errors_of, load_kb_with, query_unary, run_int64, try_load_kb_with,
};
use anthill_core::eval::Value;

fn ns(name: &str, body: &str) -> String {
    format!(
        "namespace test.r1w5a.{name}\n  import anthill.prelude.{{Int64, String, Bool, Unit, Option, List, Function}}\n{body}\nend\n"
    )
}

/// `test.r1w5a.<name>.<rule>`'s one answer, which must be definite.
#[track_caller]
fn sole_int(src: &str, qn: &str) -> i64 {
    let mut kb = load_kb_with(src);
    let rows = query_unary(&mut kb, qn);
    match rows.as_slice() {
        [(Value::Int(v), true)] => *v,
        other => panic!("{qn}: one definite Int64, got {other:?}"),
    }
}

// ── decision 4's table ──────────────────────────────────────────────────────────────

const DBL: &str = "  operation dbl(n: Int64) -> Int64\n  rule dbl(?n) <=> ?n + ?n @[simp]\n  operation app(f: (Int64) -> Int64, x: Int64) -> Int64 = f(x)\n  operation twin() -> Int64 = dbl(2)\n";

/// `?x <=> dbl(2)` answers 4, as the operation-body twin does. It was a residual,
/// `unify(?_, dbl(2))`: the call was data, and no body backs `dbl`.
#[test]
fn an_equation_defines_a_call_in_a_value_slot() {
    let src = ns("value", &format!("{DBL}  rule r(?x) :- ?x <=> dbl(2)"));
    assert_eq!(sole_int(&src, "test.r1w5a.value.r"), 4);
    assert_eq!(run_int64(&src, "test.r1w5a.value.twin"), Ok(4));
}

/// The goal `dbl(2, ?x)` is `?x <=> dbl(2)`, and answers 4. It answered nothing, silently.
#[test]
fn the_goal_with_a_result_column_runs_the_equation() {
    let src = ns("goal", &format!("{DBL}  rule r(?x) :- dbl(2, ?x)"));
    assert_eq!(sole_int(&src, "test.r1w5a.goal.r"), 4);
}

/// CONTROLS — a lambda's body was typed whole before (a binder form), and `dbl(2) = 4` was
/// typed as the `=` call it is: both answered before and after.
#[test]
fn control_the_lambda_and_the_test_answered_before() {
    let src = ns(
        "ctl",
        &format!(
            "{DBL}  rule lam(?x) :- ?x <=> app(lambda (y: Int64) -> dbl(y), 2)\n  rule tst(?x) :- dbl(2) = 4, ?x <=> 1"
        ),
    );
    assert_eq!(sole_int(&src, "test.r1w5a.ctl.lam"), 4);
    assert_eq!(sole_int(&src, "test.r1w5a.ctl.tst"), 1);
}

/// `app(dbl, 2)` is refused as its operation-body twin is: no bare reference can lift an
/// operation that carries no body. It loaded and left a residual with an incomplete search.
#[test]
fn a_reference_no_lift_can_supply_is_refused_as_in_an_operation_body() {
    let rule = load_errors_of(&ns("refrule", &format!("{DBL}  rule r(?x) :- ?x <=> app(dbl, 2)")));
    let op = load_errors_of(&ns("refop", &format!("{DBL}  operation o() -> Int64 = app(dbl, 2)")));
    for (label, errs) in [("rule body", &rule), ("operation body", &op)] {
        assert_refused_naming(errs, &["dbl", "carries no body"], label);
    }
}

/// The Bool view of an operation defined by its equation: `isPos(3)` holds. It answered
/// nothing, so `not(isPos(3))` proved a falsehood.
#[test]
fn a_bool_goal_runs_its_equation() {
    let src = ns(
        "boolv",
        "  operation isPos(n: Int64) -> Bool\n  rule isPos(?n) <=> ?n > 0 @[simp]\n  rule holds(?x) :- isPos(3), ?x <=> 1\n  rule negated(?x) :- not(isPos(3)), ?x <=> 1",
    );
    assert_eq!(sole_int(&src, "test.r1w5a.boolv.holds"), 1);
    let mut kb = load_kb_with(&src);
    assert!(query_unary(&mut kb, "test.r1w5a.boolv.negated").is_empty());
}

// ── one call, one answer, whatever shape the walk hands the typer ───────────────────

const BOX: &str = "  sort Box\n    entity mk(v: Int64)\n    operation peek(b: Box) -> Int64 = b.v\n    operation open(b: Box) -> Int64\n    rule open(?b) <=> peek(?b) @[simp]\n  end\n  sort PBox\n    sort V = ?\n    entity pmk(v: Int64)\n    operation peek(b: PBox) -> Int64 = b.v\n    operation open(b: PBox) -> Int64\n    rule open(?b) <=> peek(?b) @[simp]\n  end\n";

/// The three spellings of `Box.open` agree at 4. The written call on the plain sort was the
/// residual `unify(?_, open(mk(v: 4)))`; the dot and the parametric sort's call answered 4.
#[test]
fn the_three_spellings_of_one_call_agree() {
    let src = ns(
        "spell",
        &format!(
            "{BOX}  rule written(?x) :- ?x <=> Box.open(Box.mk(4))\n  rule dotted(?x) :- ?x <=> Box.mk(4).open()\n  rule param(?x) :- ?x <=> PBox.open(PBox.pmk(4))"
        ),
    );
    for rule in ["written", "dotted", "param"] {
        assert_eq!(sole_int(&src, &format!("test.r1w5a.spell.{rule}")), 4, "{rule}");
    }
}

/// A rewrite's result is typed as the operation-body typer types it, so the calls it leaves
/// are dispatched: `Tw.twice(m(v: 3), "km")` answers 14. It was the residual `unify(?_,
/// twice(m(v: 3), "km"))` (7D48J's 2026-09-26 row).
#[test]
fn the_calls_a_rewrite_leaves_are_dispatched() {
    let src = ns(
        "twice",
        "  sort Conv\n    sort A = ?\n    sort B = ?\n    operation conv(a: A, b: B) -> Int64\n  end\n  sort Meters\n    entity m(v: Int64)\n    provides Conv[A = Meters, B = String]\n    operation conv(a: Meters, b: String) -> Int64 = 7\n  end\n  sort Tw\n    operation twice[X, Y](a: X, b: Y) -> Int64 requires Conv[A = X, B = Y]\n    rule twice(?a, ?b) <=> Int64.add(Conv.conv(?a, ?b), Conv.conv(?a, ?b)) @[simp]\n  end\n  rule r(?r) :- ?r <=> Tw.twice(m(v: 3), \"km\")\n  operation twin() -> Int64 = Tw.twice(m(v: 3), \"km\")",
    );
    assert_eq!(sole_int(&src, "test.r1w5a.twice.r"), 14);
    assert_eq!(run_int64(&src, "test.r1w5a.twice.twin"), Ok(14));
}

/// The `()` an equation leaves in a call's argument is the `Unit` the operation body reads:
/// WI-20261011-7G99A's program (5) answers 4. It was refused, `value.body (rule): expected
/// Unit, got ()`.
#[test]
fn the_unit_an_equation_leaves_in_an_argument_is_unit() {
    let src = ns(
        "unit",
        "  sort Box\n    entity mk(v: Int64)\n    operation nothing(b: Box) -> Unit\n    rule nothing(?b) <=> () @[simp]\n  end\n  operation takes(u: Unit, n: Int64) -> Int64 = n\n  rule r(?r) :- ?r <=> takes(Box.mk(4).nothing(), 4)",
    );
    assert_eq!(sole_int(&src, "test.r1w5a.unit.r"), 4);
}

/// The some-coercion is performed at a rule body's call: a bare `Int64` handed to an
/// `Option[T = Int64]` parameter is wrapped, and `viaHead(3, ?r)` answers 3, as the
/// operation-body twin does. `len` raised `match_failed` on the bare 3 (WF14Z's note).
#[test]
fn a_bare_value_at_an_option_parameter_is_wrapped() {
    let src = ns(
        "some",
        "  sort Opt\n    operation len(o: Option[T = Int64]) -> Int64 = match o case some(v) -> v case none -> 0\n  end\n  rule viaHead(?a: Int64, ?r) :- ?r <=> Opt.len(?a)\n  rule r(?r) :- viaHead(3, ?r)",
    );
    assert_eq!(sole_int(&src, "test.r1w5a.some.r"), 3);
}

// ── decision 3's class: a call's argument list and types ────────────────────────────

const UTIL: &str = "  sort Util\n    operation sub2(x: Int64, y: Int64) -> Int64 = Int64.sub(x, y)\n    operation rep(s: String, n: Int64) -> String = s\n    operation ilen(n: Int64) -> Int64 = n\n  end\n";

/// A call's argument list and types are held to its parameter list, in a value slot and as
/// a goal, with the operation body's verdicts. Each loaded: a surplus argument and a stray
/// label were dropped (-4), a missing one left a residual, a wrong type ran (`rep(3, 3)`
/// answered the `Int64` 3 out of a `String` column) or faulted.
#[test]
fn a_calls_argument_list_and_types_are_held_to_its_parameters() {
    for (tag, body, tokens) in [
        ("surplus", "?c <=> Util.sub2(1, 5, 9)", &["sub2", "expected 2 arguments", "got 3"][..]),
        ("label", "?c <=> Util.sub2(1, 5, bogus: 9)", &["bogus", "names no parameter"][..]),
        ("missing", "?c <=> Util.sub2(1)", &["sub2", "no argument fills parameter `y`"][..]),
        ("type", "?c <=> Util.sub2(\"a\", 5)", &["sub2.x", "expected Int64, got String"][..]),
        ("goaltype", "Util.rep(3, 3, ?c)", &["rep.s", "expected String, got Int64"][..]),
    ] {
        let rule = load_errors_of(&ns(&format!("args{tag}"), &format!("{UTIL}  rule r(?c) :- {body}")));
        assert_refused_naming(&rule, tokens, tag);
    }
    // CONTROL: the call that fits answers.
    let ok = ns("argsok", &format!("{UTIL}  rule r(?c) :- ?c <=> Util.sub2(1, 5)"));
    assert_eq!(sole_int(&ok, "test.r1w5a.argsok.r"), -4);
}

/// A labelled argument types its variable, as a positional one does: `?n` is a `String` by
/// `rep`'s `s` and an `Int64` by `ilen`'s `n`, the contradiction the positional spelling is
/// refused for. The clause typing read a call's positional arguments only, and the labelled
/// clause loaded.
#[test]
fn a_labelled_argument_types_its_variable() {
    for (tag, call) in [("positional", "Util.rep(?n, 2)"), ("labelled", "Util.rep(s: ?n, n: 2)")] {
        let errs = load_errors_of(&ns(
            &format!("label{tag}"),
            &format!("{UTIL}  rule r(?c) :- ?c <=> {call}, ?d <=> Util.ilen(?n)"),
        ));
        assert_refused_naming(&errs, &["contradictory variable types"], tag);
    }
}

// ── decided 2026-10-23: the rule's own term inside a call ───────────────────────────

const SP: &str = "  sort Sp\n    operation size(s: Sp) -> Int64\n  end\n  sort Car\n    entity car(n: Int64)\n    provides Sp\n    operation size(c: Car) -> Int64 = 40\n  end\n  sort Van\n    entity van(n: Int64)\n    provides Sp\n    operation size(c: Van) -> Int64 = 2\n  end\n  operation total(xs: List[T = Sp]) -> Int64 = List.foldLeft(xs, 0, lambda (acc, c) -> acc + Sp.size(c))\n";

/// A `cons`/`nil` spine at a slot declaring its element type is checked as the literal is
/// (§4.6). A rule body's literal is lowered to the spine before typing, and answers 42; the
/// operation body's written spine, refused (`cons.tail: expected List[T = Car], got List[T =
/// Van]`), answers 42 too. An element that is no `Sp` is refused once, at the element.
#[test]
fn a_spine_at_a_declaring_slot_is_checked_as_the_literal() {
    let src = ns(
        "spine",
        &format!(
            "{SP}  import anthill.prelude.List.{{cons, nil}}\n  rule r(?x) :- ?x <=> total([car(n: 1), van(n: 2)])\n  operation written() -> Int64 = total(cons(car(n: 1), cons(van(n: 2), nil)))"
        ),
    );
    assert_eq!(sole_int(&src, "test.r1w5a.spine.r"), 42);
    assert_eq!(run_int64(&src, "test.r1w5a.spine.written"), Ok(42));
    let errs = load_errors_of(&ns("spinebad", &format!("{SP}  rule r(?x) :- ?x <=> total([car(n: 1), 5])")));
    assert_eq!(errs.len(), 1, "{errs:#?}");
    assert_refused_naming(&errs, &["cons.head", "expected Sp, got Int64"], "an element no Sp");
}

/// A type written in a call's argument is the type value it denotes, as in an operation body:
/// `which(Outer.Inner)`, the written call `H.keep(Outer.Inner)` and the dot `(H).keep(Outer.Inner)`
/// each hand `which` the sort and answer 21, as the operation-body twin does. Each answered 0,
/// `which` handed the chain (WI-20260823-53W12's rows). A path in a clause's data slot is the
/// type value its bare name is (WI-20261024-QK77S): `fact holds(Outer.Inner)` is found by
/// `holds(Inner)`.
#[test]
fn a_type_in_a_calls_argument_is_its_type_value() {
    let src = ns(
        "path",
        "  import anthill.prelude.Type\n  sort Outer\n    sort Inner\n      operation deep() -> Int64 = 21\n    end\n  end\n  import test.r1w5a.path.Outer.Inner\n  operation which(t: Type) -> Int64 = if t = Inner then 21 else 0\n  sort H\n    operation keep(t: Type) -> Int64 = which(t)\n  end\n  rule direct(?x) :- ?x <=> which(Outer.Inner)\n  rule goalForm(?x) :- which(Outer.Inner, ?x)\n  rule written(?x) :- ?x <=> H.keep(Outer.Inner)\n  rule dotted(?x) :- ?x <=> (H).keep(Outer.Inner)\n  operation twin() -> Int64 = which(Outer.Inner)\n  fact holds(Outer.Inner)\n  rule matched(?x) :- holds(Inner), ?x <=> 1",
    );
    for rule in ["direct", "written", "dotted"] {
        assert_eq!(sole_int(&src, &format!("test.r1w5a.path.{rule}")), 21, "{rule}");
    }
    assert_eq!(run_int64(&src, "test.r1w5a.path.twin"), Ok(21));
    let mut kb = load_kb_with(&src);
    assert_eq!(query_unary(&mut kb, "test.r1w5a.path.matched").len(), 1);
    // A goal's arguments are the rule's own term (§5.3), where a path is the type value its
    // bare name is: the goal hands `which` the sort, as `which(Inner, ?x)` does.
    assert_eq!(sole_int(&src, "test.r1w5a.path.goalForm"), 21);
}

/// A goal on an operation that has clauses is a relation they define, matched as written:
/// `f(Outer.Inner)` finds `rule f(Outer.Inner) :- true`. Whether a goal is the operation's
/// call or such a relation is known only once every clause is loaded, so a goal's arguments
/// are built as the rule's own term. Built as a call's, the goal's path was the type value
/// and its own clause, holding the chain, no longer matched (found by `/code-review`).
#[test]
fn a_goal_on_an_operation_with_clauses_matches_as_written() {
    let src = ns(
        "relgoal",
        "  import anthill.prelude.Type\n  sort Outer\n    sort Inner\n    end\n  end\n  import test.r1w5a.relgoal.Outer.Inner\n  operation f(t: Type) -> Bool\n  rule f(Outer.Inner) :- true\n  rule r(?x) :- f(Outer.Inner), ?x <=> 1",
    );
    assert_eq!(sole_int(&src, "test.r1w5a.relgoal.r"), 1);
}

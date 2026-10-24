//! WI-20261011-7G99A — `Unit` is the tuple of no components (kernel-language.md §4.5).
//!
//! THE RULE. The prelude declares `sort Unit = ()`, so `()` and `Unit` written as types are
//! one type, and the literal `()` is its one value wherever it is written: an operation
//! body, a fact, a goal, a rule's own term. And a tuple is one value on either carrier: the
//! tuple an operation built reads as the term a rule writes for the same text,
//! `TupleLiteral(_1: …, name: …)`, so it matches a fact's tuple and equals a rule's.
//!
//! BEFORE. The prelude declared `sort Unit = ?`, a sort of its own, and only the `()` an
//! operation body writes was typed as it; everywhere else `()` was the tuple of no
//! components, another type. `operation f() -> () = ()` was refused `expected (), got Unit`,
//! a fact `U.u(v: (), n: 4)` at a `Unit` field `expected Unit, got TupleLiteral`, and a
//! goal `U.u(v: (), n: ?r)` `expected Unit, got ()`. A tuple an operation built had no
//! functor where a rule's has `TupleLiteral`, so `?u <=> mp(), hp(?u)` over
//! `rule hp((1, 2)) :- true` answered nothing, at every arity.
//!
//! EVERY ROW HAS ITS OWN SOURCE: a row that shares a fixture with another measures the
//! fixture.
//!
//! CONTROLS — measured on the parent commit, the whole change backed out.
//!
//!   FAIL, refused at load:
//!     the_type_and_the_value_of_one_operation_agree — `expected (), got Unit`
//!     a_unit_value_meets_a_tuple_slot — `expected (), got Unit`
//!     a_tuple_value_meets_a_unit_slot — `expected Unit, got ()`
//!     a_fact_holds_unit — `expected Unit, got TupleLiteral`
//!     a_goal_matches_a_facts_unit — the fact and the goal
//!     the_unit_an_operation_built_matches_a_facts_unit — `expected Unit, got Unit`
//!     an_entity_an_operation_built_with_unit_equals_the_one_a_rule_writes —
//!       `expected Unit, got ()`
//!     a_callback_of_one_unit_parameter_fits_a_unit_slot — `got Unit -> Int64`
//!   FAIL, answering nothing:
//!     a_tuple_an_operation_built_matches_a_facts_tuple
//!     a_tuple_with_a_leading_positional_label_matches_a_facts_tuple — also with the
//!       tuple view's keys read named-first
//!     a_tuple_an_operation_built_equals_the_tuple_a_rule_writes
//!     a_named_tuple_an_operation_built_matches_a_facts_tuple
//!   FAIL, loading clean:
//!     a_tuple_field_refuses_a_value_of_another_type — a tuple-typed field was not checked
//!   FAIL, on the text:
//!     a_tuple_answer_prints_as_its_literal — a fact's tuple printed
//!       `TupleLiteral(_1: 1, _2: 2)`
//!     a_refusal_names_the_empty_tuple_unit — `expected (), got Int64`
//!
//!   FAIL with one mechanism backed out (a tuple value read and printed as a term):
//!     reflection_reads_a_tuple_value — `reads_as_term` refusing a tuple value
//!       (`expected Term`); passes with the lowering backed out, which it never asks
//!     a_written_tuple_at_a_term_slot_prints_as_its_literal — the printer writing a
//!       `TupleLiteral` constructor occurrence by its name, `TupleLiteral(_1: 1, _2: 2)`;
//!       and a lone positional component without its label, `(7)`
//!     persistence_builtins_test::a_fact_holding_an_operation_built_tuple_is_persisted —
//!       `value_to_term` refusing a tuple, as on the parent (`UnsupportedVariant`)
//!     a_raised_tuple_is_named_as_its_literal — the payload renderer naming a tuple by
//!       its head, `TupleLiteral(_1: 1, _2: 2)`
//!     a_tuple_holding_nan_is_not_equal_to_itself — the tuple left out of the
//!       partial-transparent carriers: `(n, 1) = (n, 1)` answered true once a tuple
//!       value read as `TupleLiteral(…)`. It passes on the parent, where a tuple value
//!       had no functor and was walked.
//!
//!   PASS with the change backed out, by design — what it must not move:
//!     what_an_equation_leaves_in_a_rule_body_is_unit — delivered with proposal 068's
//!       rule-body typing
//!     a_constructor_in_an_operation_body_takes_unit
//!     two_units_are_equal
//!     a_list_of_units_meets_its_slot
//!     a_plain_relation_holds_unit
//!     an_entity_an_operation_built_matches_a_facts_entity
//!     a_tuple_matches_only_its_own_components
//!     a_named_tuple_does_not_match_a_positional_one
//!     a_unit_field_refuses_a_value_of_another_type — `expected Unit, got Int64`; with
//!       `Unit` a tuple it is the tuple arm of the fact check that refuses it, and with
//!       that arm backed out the fact loads clean
//!     a_unit_field_refuses_a_tuple_of_components
//!     a_tuple_field_holds_its_tuple
//!     a_tuple_field_holds_components_the_value_typer_reads — a tuple field was not
//!       checked, and the check takes each
//!     an_entity_named_like_the_tuple_prints_as_itself — the parent printed no tuple as
//!       its literal; FAILS with the printer asking for `TupleLiteral` by its short name

use anthill_core::eval::Value;
use anthill_core::persistence::print::TermPrinter;

use crate::common::{assert_refused_naming, load_errors_of, load_kb_with, query_unary, run_int64};

/// `test.<name>`, holding `body`, with the prelude names the rows use.
fn ns(name: &str, body: &str) -> String {
    format!(
        "namespace test.{name}\n  import anthill.prelude.{{Int64, Bool, List, Unit, Function}}\n{body}\nend\n"
    )
}

#[track_caller]
fn assert_runs(src: &str, entry: &str, expected: i64) {
    assert_eq!(run_int64(src, entry), Ok(expected), "{entry}");
}

#[track_caller]
fn assert_answers(src: &str, rule: &str, expected: i64) {
    let mut kb = load_kb_with(src);
    let answers = query_unary(&mut kb, rule);
    assert!(
        matches!(answers.as_slice(), [(Value::Int(n), true)] if *n == expected),
        "{rule}: {answers:?}"
    );
}

#[track_caller]
fn assert_answers_nothing(src: &str, rule: &str) {
    let mut kb = load_kb_with(src);
    let answers = query_unary(&mut kb, rule);
    assert!(answers.is_empty(), "{rule}: {answers:?}");
}

// ── the programs of the ticket ──────────────────────────────────────────────

/// (1) The return type `()` and the value `()` of one operation.
#[test]
fn the_type_and_the_value_of_one_operation_agree() {
    assert_runs(
        &ns(
            "g99aone",
            "  operation f() -> () = ()\n  operation go() -> Int64 = if f() = () then 4 else 0",
        ),
        "test.g99aone.go",
        4,
    );
}

/// (2) A `Unit` value handed to a `()` slot …
#[test]
fn a_unit_value_meets_a_tuple_slot() {
    assert_runs(
        &ns(
            "g99atwo",
            "  operation f() -> Unit = ()\n  operation g(u: ()) -> Int64 = 4\n  operation go() -> Int64 = g(f())",
        ),
        "test.g99atwo.go",
        4,
    );
}

/// … and a `()` value to a `Unit` slot.
#[test]
fn a_tuple_value_meets_a_unit_slot() {
    assert_runs(
        &ns(
            "g99atwob",
            "  operation f() -> () = ()\n  operation g(u: Unit) -> Int64 = 4\n  operation go() -> Int64 = g(f())",
        ),
        "test.g99atwob.go",
        4,
    );
}

/// (3) A fact holds `()` at a `Unit` field.
#[test]
fn a_fact_holds_unit() {
    assert_answers(
        &ns(
            "g99athree",
            "  sort U\n    entity u(v: Unit, n: Int64)\n  end\n  fact U.u(v: (), n: 4)\n  rule value(?r) :- U.u(v: ?v, n: ?r)",
        ),
        "test.g99athree.value",
        4,
    );
}

/// (4) A goal writes `()` at the field, and matches the fact.
#[test]
fn a_goal_matches_a_facts_unit() {
    assert_answers(
        &ns(
            "g99afour",
            "  sort U\n    entity u(v: Unit, n: Int64)\n  end\n  fact U.u(v: (), n: 4)\n  rule value(?r) :- U.u(v: (), n: ?r)",
        ),
        "test.g99afour.value",
        4,
    );
}

/// (5) The `()` an equation leaves in a rule body's own term.
#[test]
fn what_an_equation_leaves_in_a_rule_body_is_unit() {
    assert_answers(
        &ns(
            "g99afive",
            "  sort Box\n    entity mk(v: Int64)\n    operation nothing(b: Box) -> Unit\n    rule nothing(?b) <=> () @[simp]\n  end\n  operation takes(u: Unit, n: Int64) -> Int64 = n\n  rule value(?r) :- ?r <=> takes(Box.mk(4).nothing(), 4)",
        ),
        "test.g99afive.value",
        4,
    );
}

// ── what loaded before ──────────────────────────────────────────────────────

#[test]
fn a_constructor_in_an_operation_body_takes_unit() {
    assert_answers(
        &ns(
            "g99amk",
            "  sort U\n    entity u(v: Unit, n: Int64)\n  end\n  operation mk() -> U = U.u(v: (), n: 4)\n  operation nn(x: U) -> Int64 = x.n\n  rule value(?r) :- ?r <=> nn(mk())",
        ),
        "test.g99amk.value",
        4,
    );
}

/// The entity an operation built with `()` equals the one a rule body writes with `()`.
#[test]
fn an_entity_an_operation_built_with_unit_equals_the_one_a_rule_writes() {
    assert_answers(
        &ns(
            "g99amkeq",
            "  sort U\n    entity u(v: Unit, n: Int64)\n  end\n  operation mk() -> U = U.u(v: (), n: 4)\n  rule value(?r) :- ?x <=> mk(), ?x = U.u(v: (), n: 4), ?r <=> 4",
        ),
        "test.g99amkeq.value",
        4,
    );
}

#[test]
fn two_units_are_equal() {
    assert_runs(
        &ns(
            "g99asame",
            "  operation same() -> Bool = () = ()\n  operation go() -> Int64 = if same() then 4 else 0",
        ),
        "test.g99asame.go",
        4,
    );
}

#[test]
fn a_list_of_units_meets_its_slot() {
    assert_runs(
        &ns(
            "g99alist",
            "  operation f(xs: List[T = Unit]) -> Int64 = 4\n  operation go() -> Int64 = f([(), ()])",
        ),
        "test.g99alist.go",
        4,
    );
}

#[test]
fn a_plain_relation_holds_unit() {
    assert_answers(
        &ns(
            "g99arel",
            "  rule holds(()) :- true\n  rule value(?r) :- holds(()), ?r <=> 4",
        ),
        "test.g99arel.value",
        4,
    );
}

// ── a tuple is one value on either carrier ──────────────────────────────────

#[test]
fn a_tuple_an_operation_built_matches_a_facts_tuple() {
    assert_answers(
        &ns(
            "g99atup",
            "  rule hp((1, 2)) :- true\n  operation mp() -> (Int64, Int64) = (1, 2)\n  rule value(?r) :- ?u <=> mp(), hp(?u), ?r <=> 4",
        ),
        "test.g99atup.value",
        4,
    );
}

#[test]
fn a_tuple_an_operation_built_equals_the_tuple_a_rule_writes() {
    assert_answers(
        &ns(
            "g99atupeq",
            "  operation mp() -> (Int64, Int64) = (1, 2)\n  rule value(?r) :- ?u <=> mp(), ?u = (1, 2), ?r <=> 4",
        ),
        "test.g99atupeq.value",
        4,
    );
}

#[test]
fn a_named_tuple_an_operation_built_matches_a_facts_tuple() {
    assert_answers(
        &ns(
            "g99atupn",
            "  rule hp((a: 1, b: 2)) :- true\n  operation mp() -> (a: Int64, b: Int64) = (a: 1, b: 2)\n  rule value(?r) :- ?u <=> mp(), hp(?u), ?r <=> 4",
        ),
        "test.g99atupn.value",
        4,
    );
}

#[test]
fn the_unit_an_operation_built_matches_a_facts_unit() {
    assert_answers(
        &ns(
            "g99aunit",
            "  rule holds(()) :- true\n  operation mkf() -> Unit = ()\n  rule value(?r) :- ?u <=> mkf(), holds(?u), ?r <=> 4",
        ),
        "test.g99aunit.value",
        4,
    );
}

/// The twin the ticket's tuple rows are measured against: an entity matched already.
#[test]
fn an_entity_an_operation_built_matches_a_facts_entity() {
    assert_answers(
        &ns(
            "g99aent",
            "  sort Box\n    entity bx(v: Int64)\n  end\n  rule hb(Box.bx(1)) :- true\n  operation mb() -> Box = Box.bx(1)\n  rule value(?r) :- ?u <=> mb(), hb(?u), ?r <=> 4",
        ),
        "test.g99aent.value",
        4,
    );
}

/// A tuple whose first component is labelled `_1` and whose second is named: eval holds the
/// first positional and the second named, and the tuple reads in the order it is written.
#[test]
fn a_tuple_with_a_leading_positional_label_matches_a_facts_tuple() {
    assert_answers(
        &ns(
            "g99alead",
            "  rule hp((_1: 1, b: 2)) :- true\n  operation mp() -> (_1: Int64, b: Int64) = (_1: 1, b: 2)\n  rule value(?r) :- ?u <=> mp(), hp(?u), ?r <=> 4",
        ),
        "test.g99alead.value",
        4,
    );
}

/// A tuple matches the fact of its own components, in their order, and no other.
#[test]
fn a_tuple_matches_only_its_own_components() {
    let src = ns(
        "g99aother",
        "  rule hp((1, 2)) :- true\n  operation other() -> (Int64, Int64) = (1, 3)\n  operation swapped() -> (Int64, Int64) = (2, 1)\n  rule byother(?r) :- ?u <=> other(), hp(?u), ?r <=> 4\n  rule byswapped(?r) :- ?u <=> swapped(), hp(?u), ?r <=> 4",
    );
    assert_answers_nothing(&src, "test.g99aother.byother");
    assert_answers_nothing(&src, "test.g99aother.byswapped");
}

/// `(a: 1, b: 2)` and `(1, 2)` are two types (§4.5): the goal is refused at the column.
#[test]
fn a_named_tuple_does_not_match_a_positional_one() {
    let errs = load_errors_of(&ns(
        "g99anamed",
        "  rule hp((1, 2)) :- true\n  operation mp() -> (a: Int64, b: Int64) = (a: 1, b: 2)\n  rule value(?r) :- ?u <=> mp(), hp(?u), ?r <=> 4",
    ));
    assert_refused_naming(
        &errs,
        &["hp._1", "expected (_1: Int64, _2: Int64), got (a: Int64, b: Int64)"],
        "a named tuple at a positional column",
    );
}

/// A tuple is printed as its literal on either carrier: the one a fact holds, and the one
/// an operation built.
#[test]
fn a_tuple_answer_prints_as_its_literal() {
    let src = ns(
        "g99aprint",
        "  rule hp((1, 2)) :- true\n  rule hu(()) :- true\n  rule hn((a: 1, b: 2)) :- true\n  operation mp() -> (Int64, Int64) = (1, 2)\n  operation mu() -> Unit = ()\n  rule fp(?r) :- hp(?r)\n  rule fu(?r) :- hu(?r)\n  rule fnm(?r) :- hn(?r)\n  rule op(?r) :- ?r <=> mp()\n  rule ou(?r) :- ?r <=> mu()",
    );
    let mut kb = load_kb_with(&src);
    for (rule, printed) in [
        ("fp", "(1, 2)"),
        ("fu", "()"),
        ("fnm", "(a: 1, b: 2)"),
        ("op", "(1, 2)"),
        ("ou", "()"),
    ] {
        let answers = query_unary(&mut kb, &format!("test.g99aprint.{rule}"));
        let [(v, true)] = answers.as_slice() else {
            panic!("{rule}: {answers:?}");
        };
        assert_eq!(TermPrinter::new(&kb).print_value(v), printed, "{rule}");
    }
}

/// A user's own entity named `TupleLiteral` is not the tuple: it prints as the
/// application it is.
#[test]
fn an_entity_named_like_the_tuple_prints_as_itself() {
    let src = ns(
        "g99aowntl",
        "  sort T\n    entity TupleLiteral(a: Int64)\n  end\n  rule hu(T.TupleLiteral(a: 1)) :- true\n  rule value(?r) :- hu(?r)",
    );
    let mut kb = load_kb_with(&src);
    let answers = query_unary(&mut kb, "test.g99aowntl.value");
    let [(v, true)] = answers.as_slice() else {
        panic!("{answers:?}");
    };
    assert_eq!(TermPrinter::new(&kb).print_value(v), "TupleLiteral(a: 1)");
}

/// What `term_to_string` / `term_field` answer for `t`, called on a fresh interpreter.
fn reflect_answer(name: &str, body: &str, entry: &str) -> String {
    let src = format!(
        "namespace test.{name}\n  import anthill.prelude.{{Int64, String, Option, Unit}}\n  import anthill.reflect.{{term_to_string, term_field, Term}}\n{body}\nend\n"
    );
    let mut interp = crate::common::interp_for(&src);
    let v = interp
        .call(&format!("test.{name}.{entry}"), &[])
        .unwrap_or_else(|e| panic!("{entry}: {e:?}"));
    match v {
        Value::Str(s) => s,
        other => TermPrinter::new(interp.kb()).print_value(&other),
    }
}

/// A tuple value is a term: the `TupleLiteral(_1: …)` a rule writes for it. Reflection
/// reads it, and prints it as its literal.
#[test]
fn reflection_reads_a_tuple_value() {
    let body = "  operation mp(a: Int64) -> (Int64, Int64) = (a, 2)\n  operation s() -> String =\n    let t = mp(1)\n    term_to_string(t)\n  operation f() -> Option[T = Term] =\n    let t = mp(1)\n    term_field(t, \"_1\")";
    assert_eq!(reflect_answer("g99arefl", body, "s"), "(1, 2)");
    assert_eq!(reflect_answer("g99arefl", body, "f"), "some(value: 1)");
}

/// The tuple an operation body writes is a constructor over `TupleLiteral`, and a rule
/// body's call hands a `Term` slot that node: it is printed as the literal it was written
/// as, as a `(…)` node is.
#[test]
fn a_written_tuple_at_a_term_slot_prints_as_its_literal() {
    let src = "namespace test.g99areflw\n  import anthill.prelude.{Int64, String}\n  import anthill.reflect.{term_to_string, TupleLiteral}\n  operation mp() -> (Int64, Int64) = (1, 2)\n  operation s() -> String = term_to_string(mp())\n  operation su() -> String = term_to_string(())\n  operation s1() -> String = term_to_string(TupleLiteral(7))\n  rule vs(?r) :- ?r <=> s()\n  rule vu(?r) :- ?r <=> su()\n  rule v1(?r) :- ?r <=> s1()\nend\n";
    let mut kb = load_kb_with(src);
    // A lone positional component keeps its label: `(7)` would be grouping.
    for (rule, printed) in [("vs", "(1, 2)"), ("vu", "()"), ("v1", "(_1: 7)")] {
        let answers = query_unary(&mut kb, &format!("test.g99areflw.{rule}"));
        assert!(
            matches!(answers.as_slice(), [(Value::Str(s), true)] if s == printed),
            "{rule}: {answers:?}"
        );
    }
}

/// A tuple holding `NaN` is not equal to itself: its equality is its components', as a
/// parametric composite's is, and `Float`'s `=` is partial.
#[test]
fn a_tuple_holding_nan_is_not_equal_to_itself() {
    assert_runs(
        &ns(
            "g99anan",
            "  import anthill.prelude.Float\n  operation nan() -> Float = 0.0 / 0.0\n  operation go() -> Int64 =\n    let n = nan()\n    if (n, 1) = (n, 1) then 0 else 4",
        ),
        "test.g99anan.go",
        4,
    );
    assert_runs(
        &ns(
            "g99anano",
            "  import anthill.prelude.Float\n  operation go() -> Int64 = if (1.5, 1) = (1.5, 1) then 4 else 0",
        ),
        "test.g99anano.go",
        4,
    );
}

/// A raised payload holding a tuple names it as its literal, `(1, 2)`, and `()` as `()`.
#[test]
fn a_raised_tuple_is_named_as_its_literal() {
    let src = "namespace test.g99araise\n  import anthill.prelude.{Int64, Unit, Error}\n  sort Boom\n    entity boom(at: (Int64, Int64), u: Unit)\n  end\n  operation fail() -> Int64 effects {Error[Boom]} = Error.raise(boom(at: (1, 2), u: ()))\nend\n";
    let mut interp = crate::common::interp_for(src);
    let err = interp
        .call("test.g99araise.fail", &[])
        .expect_err("the raise escapes");
    let anthill_core::eval::EvalError::Raised { payload, .. } = err else {
        panic!("expected a raise, got {err:?}");
    };
    assert_eq!(
        anthill_core::eval::error::render_raised_payload(interp.kb(), &payload),
        "boom(at: (1, 2), u: ())"
    );
}

// ── a fact's field is checked at its tuple type ─────────────────────────────

#[test]
fn a_unit_field_refuses_a_value_of_another_type() {
    let errs = load_errors_of(&ns(
        "g99aufield",
        "  sort U\n    entity u(v: Unit, n: Int64)\n  end\n  fact U.u(v: 5, n: 4)",
    ));
    assert_refused_naming(&errs, &["u.v", "expected Unit", "got Int64"], "`5` at a `Unit` field");
}

#[test]
fn a_unit_field_refuses_a_tuple_of_components() {
    let errs = load_errors_of(&ns(
        "g99aufieldt",
        "  sort U\n    entity u(v: Unit, n: Int64)\n  end\n  fact U.u(v: (1, 2), n: 4)",
    ));
    assert_refused_naming(&errs, &["u.v", "expected Unit"], "`(1, 2)` at a `Unit` field");
}

#[test]
fn a_tuple_field_refuses_a_value_of_another_type() {
    for (i, (value, actual)) in [("5", "got Int64"), ("(1, \"a\")", "_2: String")]
        .into_iter()
        .enumerate()
    {
        let errs = load_errors_of(&ns(
            &format!("g99atfield{i}"),
            &format!(
                "  sort W\n    entity w(v: (Int64, Int64), n: Int64)\n  end\n  fact W.w(v: {value}, n: 4)"
            ),
        ));
        assert_refused_naming(&errs, &["w.v", "expected (_1: Int64, _2: Int64)", actual], value);
    }
}

#[test]
fn a_tuple_field_holds_its_tuple() {
    assert_answers(
        &ns(
            "g99atfieldok",
            "  sort W\n    entity w(v: (Int64, Int64), n: Int64)\n  end\n  fact W.w(v: (1, 2), n: 4)\n  rule value(?r) :- W.w(v: (1, 2), n: ?r)",
        ),
        "test.g99atfieldok.value",
        4,
    );
}

/// A component of an entity whose sort provides the slot's spec, a list and a parametric
/// entity: the tuple field takes each, as a field of that type does.
#[test]
fn a_tuple_field_holds_components_the_value_typer_reads() {
    assert_answers(
        &ns(
            "g99atfieldspec",
            "  sort Tagged\n    operation tag(x: Self) -> Int64\n  end\n  sort Box\n    provides Tagged\n    entity mk(v: Int64)\n    operation tag(x: Box) -> Int64 = 1\n  end\n  sort Pair\n    sort V = ?\n    entity pr(a: V, b: V)\n  end\n  sort W\n    entity w(v: (Tagged, Int64), n: Int64)\n    entity wl(v: (List[T = Int64], Int64), n: Int64)\n    entity wp(v: (Pair[V = Int64], Int64), n: Int64)\n  end\n  fact W.w(v: (Box.mk(1), 2), n: 4)\n  fact W.wl(v: ([1, 2], 2), n: 4)\n  fact W.wp(v: (Pair.pr(1, 2), 2), n: 4)\n  rule value(?r) :- W.w(v: ?a, n: ?r), W.wl(v: ?b, n: ?r), W.wp(v: ?c, n: ?r)",
        ),
        "test.g99atfieldspec.value",
        4,
    );
}

// ── a function of one `Unit` parameter, and the name a refusal gives ────────

/// A function of one `Unit` parameter fits a `Function[A = (), B]` slot, where `A`'s one
/// call is `f()` (§4.4: the slot admits a callback of `A`'s component count or of one).
#[test]
fn a_callback_of_one_unit_parameter_fits_a_unit_slot() {
    assert_runs(
        &ns(
            "g99acb",
            "  operation force(f: Function[A = (), B = Int64]) -> Int64 = f()\n  operation g(u: Unit) -> Int64 = 4\n  operation go() -> Int64 = force(g)",
        ),
        "test.g99acb.go",
        4,
    );
}

#[test]
fn a_refusal_names_the_empty_tuple_unit() {
    let errs = load_errors_of(&ns("g99aname", "  operation m() -> () = 5"));
    assert_refused_naming(&errs, &["m.return", "expected Unit, got Int64"], "`5` at `-> ()`");
}

//! A VARIABLE READ AS A VALUE IN AN EXECUTABLE BODY IS THE BINDER OF ITS NAME, and one nothing
//! binds is refused at load (kernel-language.md §4.8).
//!
//! WI-20261020-VQPRP — an anonymous `?`, or a `?y` with no parameter and no `let`, `lambda` or
//! `match` binder named `y` in scope, read in an operation body loaded clean and died when the
//! body ran: the typer typed it as a fresh type variable and accepted it, and the evaluator
//! read it as a call of its name. MEASURED on 6b72e648 with the CLI, every program of
//! `each_measured_program_is_refused_naming_the_variable` died `unknown operation: _` — the
//! named ones `… y`, `… t`, `… T`, `… v` — and so did a parameter's default and a const's
//! value. The typed body is now walked for such a read (`unbound_value_variable`), after
//! `@[simp]` rewriting, and the operation, the default or the const is refused naming it.
//!
//! Found driving the default rows: a default naming an earlier parameter as `?x` was read as
//! no name of it. The splice at a call left the `?x` in the copy, so the call read `x` in the
//! CALLER's frame — MEASURED with the splice and the body walk backed out, `g() = f(3)` under
//! `f(x: Int64, y: Int64 = ?x)` died `UnknownOperation { name: "wivqprp.defvar.f.x" }`, and
//! `h(1)` over `h(x: Int64) = f(x + 10)` answered 1, `h`'s own `x`, where 11 is the argument;
//! in a rule body the goal answered nothing. And `for_each_named_reference` did not count it,
//! so a compound argument it names was not bound to a local first and ran twice, and a `?y`
//! naming a LATER parameter escaped the loader's refusal of one. `?x` is now the name `x` in
//! both (`splice_default`, `for_each_named_reference`). A default's own text spliced at a call
//! is judged where it is declared and not again in each caller (`is_spliced_default`), and a
//! default is held to the rigid-read rule a body is (`unbacked_value_reads`, proposal 065),
//! which it escaped: `f(x: ?t, y: Type = ?t)` with no `TypeValue` clause loaded clean.
//!
//! ## Back-out
//!
//! Measured 2026-11-02 over these rows, one build, a temporary switch per part:
//!
//! | backed out | fails |
//! |---|---|
//! | the walk at an operation body | `each_measured_program_is_refused_naming_the_variable`, `a_binder_reaches_only_its_own_scope` |
//! | the walk at a parameter's default | `a_default_is_held_to_it` (its `?` default loads) |
//! | the walk at a const's value | `a_const_value_is_held_to_it` |
//! | `?x` replaced in a spliced default | `a_default_reading_an_earlier_parameter_as_a_variable_takes_the_argument`, `a_compound_argument_a_variable_default_names_is_evaluated_once`, `a_variable_default_taken_in_a_rule_body_reads_the_goals_term` (no answer) |
//! | `?x` counted as naming `x` | `a_compound_argument_a_variable_default_names_is_evaluated_once` (`121002`), `a_default_naming_a_later_parameter_as_a_variable_is_refused_as_ordered` |
//! | the spliced default skipped in a caller | `a_default_is_held_to_it` (three refusals, two of them the callers') |
//! | the rigid-read rule at a default | `a_default_is_held_to_it` (its `?t` and `T` defaults load) |
//!
//! PASS EITHER WAY, BY DESIGN: `a_bound_variable_is_read`, `a_question_mark_where_no_value_is_read_is_left`
//! — the positions the walk must not move — under every part above.

use crate::common::{definite_unary, load_errors_of, load_kb_with, run_int64};

fn program(ns: &str, decls: &str) -> String {
    format!(
        r#"
namespace wivqprp.{ns}
  import anthill.prelude.{{Int64, Bool, Option, Type, List, Cell, Modify}}
  import anthill.prelude.Option.{{some, none}}
  import anthill.prelude.PartialEq.{{eq, neq}}
  import anthill.reflect.{{TypeValue, type_admits}}
  import anthill.prelude.Bool.{{ite}}
  sort Boom
    sort Reason = ?
    entity boom(reason: Reason)
  end
  sort Fault
    entity fault(reason: Int64)
  end
  sort Bag
    sort T = ?
  end
  operation ap(g: (Int64) -> Int64) -> Int64 = g(3)
{decls}
end
"#
    )
}

/// The one refusal `src` gets, which must name `var` — `?` for an anonymous variable — read
/// in `owner`'s `field`; returned for a row that asks more of it.
fn refused_naming(src: &str, var: &str, owner: &str, field: &str) -> String {
    let mut errors = load_errors_of(src);
    assert_eq!(errors.len(), 1, "one refusal expected, got {errors:#?}\n{src}");
    let e = errors.remove(0);
    for token in [
        format!("in {owner}.{field}:"),
        format!("got `{var}`,"),
        "kernel-language.md §4.8".to_string(),
    ] {
        assert!(e.contains(&token), "`{token}` expected in {e}\n{src}");
    }
    e
}

#[test]
fn each_measured_program_is_refused_naming_the_variable() {
    let rows: &[(&str, &str, &str)] = &[
        ("admits", "operation f(n: Int64) -> Bool = type_admits(?, Int64)", "?"),
        ("result", "operation f() -> Int64 = ?", "?"),
        ("some", "operation f() -> Option[T = Int64] = some(?)", "?"),
        ("cond", "operation f() -> Int64 = if ? then 1 else 2", "?"),
        ("guard", "operation f(x: Int64) -> Int64 = match x case y | ? -> 1 case _ -> 2", "?"),
        ("field", "operation f() -> Fault = fault(reason: ?)", "?"),
        ("element", "operation f() -> List[T = Int64] = [1, ?]", "?"),
        ("scrutinee", "operation f() -> Int64 = match ? case _ -> 1", "?"),
        (
            "relation",
            "rule edge(?a, ?b) :- ?a = 1, ?b = 2\n  operation f() -> Int64 = let r = edge(1, ?) 0",
            "?",
        ),
        (
            "relnamed",
            "rule edge(?a, ?b) :- ?a = 1, ?b = 2\n  operation f() -> Int64 = let r = edge(1, ?y) 0",
            "?y",
        ),
        ("typevalue", "operation f() -> Type = Boom[Reason = ?t]", "?t"),
        ("bracket", "operation f[T](x: T) -> Type requires TypeValue[T = T] = ?T", "?T"),
        ("lambda", "operation f() -> Int64 = ap(lambda (x: Int64) -> ?)", "?"),
        (
            "proofbody",
            "operation f(n: Int64) -> Int64 =\n    proof h by derivation conclude eq(n, n) end\n    ?",
            "?",
        ),
    ];
    for (ns, decls, var) in rows {
        refused_naming(&program(ns, decls), var, &format!("wivqprp.{ns}.f"), "body");
    }
}

#[test]
fn a_binder_reaches_only_its_own_scope() {
    // Another arm's pattern, and a `let`'s own value, bind nothing here.
    let rows: &[(&str, &str, &str)] = &[
        (
            "arm",
            "operation f(o: Option[T = Int64]) -> Int64 = match o case some(v) -> v case none -> ?v",
            "?v",
        ),
        ("letvalue", "operation f() -> Int64 = let y = ?y y", "?y"),
        ("lambdaout", "operation f() -> Int64 = let k = ap(lambda (x: Int64) -> x) ?x", "?x"),
    ];
    for (ns, decls, var) in rows {
        refused_naming(&program(ns, decls), var, &format!("wivqprp.{ns}.f"), "body");
    }
}

#[test]
fn a_default_is_held_to_it() {
    let src = program("default", "operation f(x: Int64 = ?) -> Int64 = x");
    let e = refused_naming(&src, "?", "wivqprp.default.f", "x");
    assert!(e.contains("the default of `x` in `wivqprp.default.f`"), "{e}");
    // Refused where it is declared, and not again at each call that takes it: the callers
    // have nothing to repair.
    let src = program(
        "callers",
        "operation f(x: Int64, y: Int64 = ?) -> Int64 = y\n  operation g() -> Int64 = f(3)\n  \
         operation h() -> Int64 = f(4)",
    );
    refused_naming(&src, "?", "wivqprp.callers.f", "y");
    // A default read of a type parameter is held to the rule a body's is (proposal 065):
    // inline, or the bracket's.
    for (ns, decls, param) in [
        ("inline", "operation f(x: ?t, y: Type = ?t) -> Type = y", "?t"),
        ("bracket", "operation f[T](x: T, y: Type = T) -> Type = y", "T"),
    ] {
        let errors = load_errors_of(&program(ns, decls));
        assert_eq!(errors.len(), 1, "{errors:#?}");
        let want = format!("`{param}` is read as a VALUE and nothing in scope requires `TypeValue[T = {param}]`");
        assert!(errors[0].contains(&want), "{}", errors[0]);
    }
}

/// `?y` naming a LATER parameter is the loader's refusal of a default naming one, as `y` is.
#[test]
fn a_default_naming_a_later_parameter_as_a_variable_is_refused_as_ordered() {
    let errors = load_errors_of(&program("later", "operation f(x: Int64 = ?y, y: Int64) -> Int64 = x"));
    assert_eq!(errors.len(), 1, "{errors:#?}");
    assert!(
        errors[0].contains("the default of `x` of `wivqprp.later.f` names `y`, which is declared after it"),
        "{}",
        errors[0]
    );
}

#[test]
fn a_const_value_is_held_to_it() {
    refused_naming(&program("konst", "const c: Int64 = ?"), "?", "wivqprp.konst.c", "value");
    refused_naming(
        &program("konstn", "const c: Option[T = Int64] = some(?z)"),
        "?z",
        "wivqprp.konstn.c",
        "value",
    );
}

/// A default naming an earlier parameter as `?x`, the twin of `wi_cx743`'s `last = first`.
fn defvar() -> String {
    program(
        "defvar",
        "operation f(x: Int64, y: Int64 = ?x) -> Int64 = y\n  operation g() -> Int64 = f(3)\n  \
         operation h(x: Int64) -> Int64 = f(x + 10)\n  operation k() -> Int64 = h(1)\n  \
         operation range3(first: Int64, last: Int64 = ?first, step: Int64 = 1) -> Int64 =\n    \
         first * 100 + last * 10 + step\n  \
         operation bump(c: Cell[V = Int64]) -> Int64 effects Modify[c] =\n    \
         let n = Cell.get(c) + 1\n    let u = Cell.set(c, n)\n    n\n  \
         operation once() -> Int64 =\n    let c = Cell.new(0)\n    let r = range3(bump(c))\n    \
         r * 1000 + Cell.get(c)\n  \
         fact num(3)\n  rule rangeValue(?r) :- num(?x), ?r <=> range3(?x)",
    )
}

#[test]
fn a_default_reading_an_earlier_parameter_as_a_variable_takes_the_argument() {
    let src = defvar();
    assert_eq!(run_int64(&src, "wivqprp.defvar.g"), Ok(3));
    // The caller's own `x` is not what the default reads: the argument is.
    assert_eq!(run_int64(&src, "wivqprp.defvar.k"), Ok(11));
}

/// A compound argument a `?first` default names is evaluated once, as one `last = first`
/// names is (`wi_cx743`'s `rangeOnce`): bumped twice it would be `121002`.
#[test]
fn a_compound_argument_a_variable_default_names_is_evaluated_once() {
    assert_eq!(run_int64(&defvar(), "wivqprp.defvar.once"), Ok(111001));
}

/// In a rule body the default reads the goal's term.
#[test]
fn a_variable_default_taken_in_a_rule_body_reads_the_goals_term() {
    let mut kb = load_kb_with(&defvar());
    let answers: Vec<i64> = definite_unary(&mut kb, "wivqprp.defvar.rangeValue")
        .into_iter()
        .map(|v| match v {
            anthill_core::eval::value::Value::Int(n) => n,
            other => panic!("rangeValue: expected an Int64, got {other:?}"),
        })
        .collect();
    assert_eq!(answers, vec![331]);
}

#[test]
fn a_bound_variable_is_read() {
    let rows: &[(&str, &str, i64)] = &[
        ("param", "operation f(n: Int64) -> Int64 = ?n\n  operation g() -> Int64 = f(5)", 5),
        ("let", "operation f(n: Int64) -> Int64 = let y = n ?y\n  operation g() -> Int64 = f(6)", 6),
        ("lambda", "operation g() -> Int64 = ap(lambda (x: Int64) -> ?x)", 3),
        (
            "arm",
            "operation f(o: Option[T = Int64]) -> Int64 = match o case some(v) | ?v > 0 -> ?v case _ -> 0\n  \
             operation g() -> Int64 = f(some(4))",
            4,
        ),
        // A parameter the signature writes inline is read through its `TypeValue` slot.
        (
            "inline",
            "operation t(x: ?t) -> Type requires TypeValue[T = ?t] = ?t\n  \
             operation g() -> Int64 = match t(3) case _ -> 1",
            1,
        ),
    ];
    for (ns, decls, want) in rows {
        let src = program(ns, decls);
        assert_eq!(run_int64(&src, &format!("wivqprp.{ns}.g")), Ok(*want), "{src}");
    }
}

#[test]
fn a_question_mark_where_no_value_is_read_is_left() {
    let rows: &[(&str, &str, i64)] = &[
        // A type value's `?` argument is an open slot (WI-20261016-SQZPQ).
        (
            "openslot",
            "operation t() -> Type = Boom[Reason = ?]\n  operation g() -> Int64 = match t() case _ -> 1",
            1,
        ),
        // An argument a `@[simp]` rewrite discards.
        ("ite", "operation g() -> Int64 = ite(true, 4, ?)", 4),
        (
            "simp",
            "operation firstOf(a: Int64, b: Int64) -> Int64\n  \
             rule firstOf(?a, ?_) <=> ?a @[simp]\n  operation g() -> Int64 = firstOf(4, ?)",
            4,
        ),
        // An in-body proof's `conclude` is a proposition.
        (
            "conclude",
            "operation f(n: Int64) -> Int64 =\n    proof h by derivation conclude neq(n, ?) end\n    n\n  \
             operation g() -> Int64 = f(7)",
            7,
        ),
        // Type positions: an annotation, a lambda binder's, a call's bracket.
        (
            "annotation",
            "operation g() -> Int64 = let x: Option[T = ?] = some(3) match x case some(v) -> v case none -> 0",
            3,
        ),
        (
            "binder",
            "operation one(h: (Option[T = Int64]) -> Int64) -> Int64 = h(none)\n  \
             operation g() -> Int64 = one(lambda (x: Option[T = ?]) -> 4)",
            4,
        ),
        (
            "bracket",
            "operation id[A](x: Int64) -> Int64 = x\n  operation g() -> Int64 = id[A = Bag[T = ?]](5)",
            5,
        ),
    ];
    for (ns, decls, want) in rows {
        let src = program(ns, decls);
        assert_eq!(run_int64(&src, &format!("wivqprp.{ns}.g")), Ok(*want), "{src}");
    }
}

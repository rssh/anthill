//! WI-20261104-6HVXM — EVERY ARROW IS A `Function`, in the typer and the run time (proposal 002
//! §"Correction (2026-11-03)" and §"Four more consequences", kernel-language §4.4).
//!
//! `(p₁: T₁, …, pₙ: Tₙ) -> R` is `Function[A = (p₁: T₁, …, pₙ: Tₙ), B = R]`: the parameter list
//! is the tuple `A` and no parameter count stands beside it, so `((a: A, b: B)) -> R` and
//! `(a: A, b: B) -> R` are one type. An application is checked by the APPLICATION MATCH against
//! `A` — a positional argument meets the component at its position, a named one the component
//! with its label — and one tuple is always the argument list. A callable written where a
//! function type is expected meets the slot by label where the two tuples carry the same labels,
//! by position otherwise; one of one parameter takes the whole tuple and drops what its own
//! tuple lacks. A function VALUE drops nothing and meets another function type only where the
//! two tuples carry the same labels in the same order, or one of them is positional.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: an admitted program RUNS to the value 002 states, and a
//! refusal is asserted by the words that name where it is refused. The bracket in each row's
//! comment is the program's value on the tree before this change (measured on 0eaa2e86 and
//! 89500f50, the trees 002 cites).
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! SEVENTEEN PARTS, each backed out in place; the first fourteen run over a temporary binary of the 89 suites
//! that state an arrow, a function value, a lambda's binders or a tuple's components (1 301
//! rows; green with nothing backed out). Measured 2026-11-04:
//!
//! 1. ONE TUPLE NOT SPREAD (`spread_one_tuple_argument` answering `None`). 87 FAIL across 23
//!    files: the stdlib's own typing (`typing_test::type_check_stdlib_no_spurious_errors` and
//!    four more — the library applies function values to one tuple), and here
//!    [`one_tuple_is_always_the_argument_list`],
//!    [`a_function_value_is_applied_by_the_application_match`],
//!    [`a_callable_meets_its_slot_by_label_or_by_position`],
//!    [`a_function_value_drops_nothing_and_keeps_its_mapping`] and
//!    [`a_rule_body_expression_reads_one_tuple_as_the_argument_list`].
//! 2. SEVERAL ARGUMENTS NOT GATHERED into a one-parameter operation's tuple
//!    (`gather_one_parameter_arguments` answering `None`). 2 FAIL:
//!    [`one_tuple_is_always_the_argument_list`] and
//!    [`a_rule_body_expression_reads_one_tuple_as_the_argument_list`].
//! 3. NO MEETING BY LABEL at a slot (`meets_slot_by_label` answering `false`). 5 FAIL:
//!    [`a_callable_meets_its_slot_by_label_or_by_position`],
//!    [`a_callbacks_row_places_follow_the_mapping`],
//!    [`a_function_value_is_applied_by_the_application_match`],
//!    `op_fn_value_labelled_arrow_test::a_labelled_arrow_takes_an_operation_of_two_parameters`
//!    and `wi803…::an_operation_written_at_a_slot_of_its_labels_in_another_order_meets_it_by_label`.
//! 4. A FUNCTION VALUE RELATED AS DATA, by width and permutation (`arrow_params_compatible` at
//!    `TupleAlign::DATA`). 11 FAIL: [`a_function_value_drops_nothing_and_keeps_its_mapping`],
//!    three of `wi1088`, two of `wi782`, three of `wi_0gyw1`, one of `wi775`, one of `wi_qqpq2`.
//! 5. A REPEATED ARROW LABEL NOT REFUSED (the check in `parse/convert.rs`). 2 FAIL:
//!    [`an_arrow_parameter_list_has_distinct_labels`] and
//!    `wi805…::an_arrow_parameter_list_is_covered`.
//! 6. NO OWN TUPLE for a binder list (`lambda_own_tuple` answering `None`). 18 FAIL:
//!    [`a_lambdas_count_is_its_tuple`], [`a_function_value_is_applied_by_the_application_match`],
//!    and rows of `wi784`, `wi785`, `wi794`, `wi795`, `wi801`, `wi803`, `wi_12nkg`, `wi_50b2k`,
//!    `wi_80259`.
//! 7. NO REFUSAL AT THE PATTERN of a lambda its context does not fit (`context_fits_lambda`
//!    answering `true`). 14 FAIL: [`a_lambdas_count_is_its_tuple`] and the count rows of
//!    `wi784`, `wi785`, `wi794`, `wi795`, `wi801`, `wi803`, `wi_80259`.
//! 8. RUN TIME, BY POSITION: a many-parameter `OpRef` takes the components in its own order,
//!    not the slot's mapping (`spread_eta_args`). The same 5 as part 3 — the run time follows
//!    the typer's mapping, and each row runs to the other value.
//! 9. RUN TIME, NO RELABEL of the positional tuple for a one-parameter `OpRef`. 13 FAIL:
//!    [`a_callable_meets_its_slot_by_label_or_by_position`],
//!    [`a_function_value_is_applied_by_the_application_match`], and rows of `wi782`, `wi783`,
//!    `wi785`, `wi791`, `wi801`.
//! 10. RUN TIME, NO RELABEL for a one-binder closure (`lambda_relabel` answering `None`). 8 FAIL:
//!    [`a_callable_meets_its_slot_by_label_or_by_position`],
//!    [`a_function_value_is_applied_by_the_application_match`], and rows of `wi785`, `wi795`,
//!    `wi801`, `wi_0rp29`, `wi_gr5en`, `wi_sg16k`.
//! 11. BINDERS NOT REORDERED with the components a callable meets its slot by. 1 FAILS:
//!    [`a_callbacks_row_places_follow_the_mapping`].
//! 12. A ONE-PARAMETER CALLABLE DROPS NOTHING (the tuple match at `callable_at_slot` asked both
//!    ways). 2 FAIL: [`a_callable_meets_its_slot_by_label_or_by_position`] and
//!    `wi782…::narrower_tuple_typed_parameter_still_applies`.
//! 13. AN ANNOTATED ONE BINDER TYPED AT THE WIDER SLOT, not at what it wrote. 1 FAILS:
//!    [`a_callable_meets_its_slot_by_label_or_by_position`] (`w1d`, which then loads).
//! 14. A RULE BODY'S EVALUATED EXPRESSION NOT SPREAD (the spread gated on any rule body, not
//!    on a rule body's own term). 1 FAILS: [`a_rule_body_expression_reads_one_tuple_as_the_argument_list`].
//! 15. A LAMBDA'S BINDER NAMES NAME NOTHING (`components_named_by_binders` answering `A`'s own
//!    components), measured apart over this file and the nine suites nearest it (123 rows). 2
//!    FAIL: [`a_lambdas_binder_names_name_its_arguments`] and
//!    `wi_50b2k…::a_direct_application_of_a_multi_binder_lambda_no_longer_aborts_the_typer`.
//! 16. NO LABELS IN THE GATHER for an `A` the call decides (`gather_args_into_tuple`'s
//!    `keep_labels`), over this file. 1 FAILS: [`a_function_value_is_applied_by_the_application_match`]
//!    (`qa`, `qb`).
//! 17. AN OPERATION'S BINDERS ITS ARGUMENT PLACES, not one per parameter (`eta.rs`), over this
//!    file. 1 FAILS: [`an_operation_value_has_one_binder_per_parameter`], the typer panicking.
//!
//! Every row of this file fails under at least one part. Measured apart, in
//! `anthill-cpp-gen`: a call through a function value lowered with the tupled form as written
//! fails `higher_kinded_arrow_test::a_call_through_a_function_value_passes_the_components`.
//!
//! UNDRIVEN: the refusal in Path 2 of an application whose `A` is an un-annotated lambda's
//! variable when the arguments' tuple fails the occurs check — a `let`-bound lambda is
//! generalized, so each use gets its own variable and no program here reaches it; the run time's
//! refusal of a relabel at another width (`Value::at_tuple_labels`), which a typed application
//! never hands; the trial σ a refused callable of one parameter is judged on (see the `pick`
//! row); and the callback pair a waited slot re-records for the row discharge (WI-329) — a
//! row naming the callback's own parameter (`Modify[x]`) is no row the caller's `R` can take,
//! whether the slot's `A` waited or not.

use crate::common::{assert_refused_naming, load_errors_of, parse_errs, run_int64};

/// A program whose `go()` is `body`, beside `decls`.
fn program(ns: &str, decls: &str, body: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, List, String, Function, Bool, Cell, Modify}}\n{decls}\n  operation go() -> Int64 =\n{body}\nend\n"
    )
}

fn runs(ns: &str, decls: &str, body: &str) -> Result<i64, String> {
    run_int64(&program(ns, decls, body), &format!("{ns}.go"))
}

fn refused(ns: &str, decls: &str, body: &str, tokens: &[&str], why: &str) {
    assert_refused_naming(&load_errors_of(&program(ns, decls, body)), tokens, why);
}

const GET_A: &str = "  operation get_a(t: (a: Int64, b: Int64)) -> Int64 = t.a";
const TWO: &str = "  operation two(a: Int64, b: Int64) -> Int64 = a * 10 + b";
const R: &str = "  operation r(t: (Int64, Int64), n: Int64 = 100) -> Int64 = t._1 * 10 + t._2 + n";

/// One tuple is any one argument of tuple type, for a call of an operation by its name and
/// through a function value alike; an operation of one parameter called by its name may still
/// name it, and gathers what several arguments say into its parameter's tuple.
#[test]
fn one_tuple_is_always_the_argument_list() {
    // fr1: `(1, 2)` is the argument list, `t = 1` and `n = 2` [112].
    refused("wi_6hvxm.fr1", R, "    r((1, 2))", &["r.t (op-arg)", "got Int64"], "a written tuple is the argument list");
    assert_eq!(runs("wi_6hvxm.fr2", R, "    r(t: (1, 2))"), Ok(112));
    // A tuple bound by a `let` is the argument list too [112].
    refused(
        "wi_6hvxm.one1",
        R,
        "    let p = (1, 2)\n    r(p)",
        &["r.t (op-arg)", "got Int64"],
        "a tuple-typed value is the argument list",
    );
    assert_eq!(runs("wi_6hvxm.one2", R, "    let p = (1, 2)\n    r(t: p)"), Ok(112));
    assert_eq!(runs("wi_6hvxm.one3", GET_A, "    get_a(t: (a: 1, b: 2))"), Ok(1));
    // [refused, count]
    assert_eq!(runs("wi_6hvxm.one4", GET_A, "    get_a(1, 2)"), Ok(1));
    assert_eq!(runs("wi_6hvxm.one5", GET_A, "    get_a(b: 2, a: 1)"), Ok(1));
    // fw's direct call [refused, count].
    assert_eq!(runs("wi_6hvxm.fw2", TWO, "    two((a: 1, b: 2))"), Ok(12));
    assert_eq!(runs("wi_6hvxm.fadd", TWO, "    two((1, 2))"), Ok(12));
    // A name-keyed value permuted against the parameters, read by its labels.
    assert_eq!(runs("wi_6hvxm.tup1", TWO, "    let t = (b: 2, a: 1)\n    two(t)"), Ok(12));
}

/// `rule value(?r) :- ?r <=> {expr}` beside `decls`, its one answer.
fn rule_answers(ns: &str, decls: &str, expr: &str) -> i64 {
    use anthill_core::kb::term_view::TermView;
    let src = format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, Function}}\n{decls}\n  rule value(?r) :- ?r <=> {expr}\nend\n"
    );
    let mut kb = crate::common::load_kb_with(&src);
    let vs = crate::common::definite_unary(&mut kb, &format!("{ns}.value"));
    assert_eq!(vs.len(), 1, "{ns}: one answer, got {vs:?}");
    vs[0].literal_int64(&kb).unwrap_or_else(|| panic!("{ns}: an Int64 answer, got {vs:?}"))
}

/// What a rule body EVALUATES — a call of its own term, an expression under a `let` — is written
/// as an operation body is, and one tuple is its argument list there too: `f((3, 10))` through a
/// function value [40], `two((3, 10))` by name [refused at `two.a`], and a one-parameter
/// operation gathering several arguments [refused at `get_a.t`].
#[test]
fn a_rule_body_expression_reads_one_tuple_as_the_argument_list() {
    let decls = format!("{TWO}\n{GET_A}");
    assert_eq!(
        rule_answers(
            "wi_6hvxm.rb1",
            &decls,
            "(let f: Function[A = (Int64, Int64), B = Int64] = lambda (a, b) -> a * 10 + b\n    f((3, 10)))"
        ),
        40
    );
    assert_eq!(rule_answers("wi_6hvxm.rb2", &decls, "two((3, 10))"), 40);
    assert_eq!(rule_answers("wi_6hvxm.rb3", &decls, "get_a(1, 2)"), 1);
}

/// A call through a function value is checked against its `A` by the application match, and
/// `f(x, y)` and `f((x, y))` are one application.
#[test]
fn a_function_value_is_applied_by_the_application_match() {
    // q3: the lambda's own tuple is what its binders write [loads, dies at run time].
    refused(
        "wi_6hvxm.q3",
        "",
        "    let h = lambda (s: Int64, b: Int64) -> s + b\n    h(\"a\", 1)",
        &["expected Int64, got String"],
        "an annotated binder list is the lambda's tuple",
    );
    assert_eq!(runs("wi_6hvxm.q3b", "", "    let h = lambda (s: Int64, b: Int64) -> s + b\n    h(1, 2)"), Ok(3));
    assert_eq!(runs("wi_6hvxm.q3c", "", "    let h = lambda (s: Int64, b: Int64) -> s + b\n    h((1, 2))"), Ok(3));
    // q6 [refused, count].
    assert_eq!(
        runs("wi_6hvxm.q6", "", "    let h: (Int64, Int64) -> Int64 = lambda (s, b) -> s + b\n    h(1, 2) + h((1, 2))"),
        Ok(6)
    );
    let fa = |call: &str| {
        format!(
            "    let f: Function[A = (a: Int64, b: Int64), B = Int64] = get_a\n    let g: Function[A = (a: Int64, b: Int64), B = Int64] = two\n    {call}"
        )
    };
    let decls = format!("{GET_A}\n{TWO}");
    assert_eq!(runs("wi_6hvxm.fa1", &decls, &fa("f(1, 2)")), Ok(1));
    assert_eq!(runs("wi_6hvxm.fa2", &decls, &fa("f((a: 1, b: 2))")), Ok(1));
    assert_eq!(runs("wi_6hvxm.fa3", &decls, &fa("g(1, 2)")), Ok(12));
    assert_eq!(runs("wi_6hvxm.fa4", &decls, &fa("g((a: 1, b: 2))")), Ok(12));
    // fe2 [1] and its `Function`-typed twin [refused: no parameter names].
    let impl_yx = "  operation impl(y: Int64, x: Int64) -> Int64 = x";
    for (ns, slot) in [("fe2", "(x: Int64, y: Int64) -> Int64"), ("fe2b", "Function[A = (x: Int64, y: Int64), B = Int64]")] {
        let decls = format!("  operation take(f: {slot}) -> Int64 = f(x: 7, y: 1)\n{impl_yx}");
        assert_eq!(runs(&format!("wi_6hvxm.{ns}"), &decls, "    take(impl)"), Ok(7), "{ns}");
    }
    // A one-binder lambda bound by a `let` is a function value whose `A` is its binder's tuple,
    // and a tuple-typed argument is the argument list: wider by a component it is refused, the
    // value dropping nothing; permuted it is met by label; in another order of positions it is
    // refused (the g-compatibility family's lambda position at a tuple, which it skips) [runs 1,
    // runs 1, refused].
    let mk = |a: &str, lit: &str| format!("  operation mkA() -> {a} = {lit}");
    refused(
        "wi_6hvxm.lam_width",
        &mk("(a: Int64, b: String, c: Bool)", "(a: 1, b: \"s\", c: true)"),
        "    let f = lambda (x: (a: Int64, c: Bool)) -> 1\n    f(mkA())",
        &["named argument 'b' names no parameter of this function value's type"],
        "a function value applied to a wider tuple",
    );
    assert_eq!(
        runs(
            "wi_6hvxm.lam_perm",
            &mk("(b: String, a: Int64)", "(b: \"s\", a: 1)"),
            "    let f = lambda (x: (a: Int64, b: String)) -> x.a\n    f(mkA())"
        ),
        Ok(1)
    );
    refused(
        "wi_6hvxm.lam_order",
        &mk("(String, Int64)", "(\"s\", 1)"),
        "    let f = lambda (x: (Int64, String)) -> 1\n    f(mkA())",
        &["expected Int64, got String"],
        "a function value applied to a tuple of another order",
    );
    // A one-binder lambda whose `A` the call decides takes the arguments as the tuple they make,
    // labelled as the call labels them [refused: `a` is not a component of `(_1, _2)`].
    let q = "    let g = lambda q -> q\n";
    assert_eq!(runs("wi_6hvxm.qa", "", &format!("{q}    g(a: 1, b: 2).a")), Ok(1));
    assert_eq!(runs("wi_6hvxm.qb", "", &format!("{q}    g(1, b: 7).b")), Ok(7));
    // A one tuple named otherwise than `A` is the arguments it holds, met by label.
    let decls = format!("  operation take(f: (x: Int64, y: Int64) -> Int64, t: (y: Int64, x: Int64)) -> Int64 = f(t)\n  operation impl(y: Int64, x: Int64) -> Int64 = x * 10 + y");
    assert_eq!(runs("wi_6hvxm.ftup", &decls, "    take(impl, (y: 1, x: 7))"), Ok(71));
}

/// A callable written where a function type is expected meets the slot by label where the two
/// tuples carry the same labels, by position otherwise; one of one parameter takes the whole
/// tuple and drops a component its own does not name.
#[test]
fn a_callable_meets_its_slot_by_label_or_by_position() {
    let take2 = "  operation take2(f: Function[A = (Int64, Int64), B = Int64]) -> Int64 = f(1, 2)";
    let decls = format!("{GET_A}\n{TWO}\n{take2}");
    // fd: [refused] and [12].
    assert_eq!(runs("wi_6hvxm.fd1", &decls, "    take2(get_a)"), Ok(1));
    assert_eq!(runs("wi_6hvxm.fd2", &decls, "    take2(two)"), Ok(12));
    // q8, fg1: a lambda's binders and unrelated parameter names meet `foldLeft`'s by position.
    assert_eq!(runs("wi_6hvxm.q8", "", "    let f = lambda (a: Int64, b: Int64) -> a + b\n    List.foldLeft([1, 2, 3], 0, f)"), Ok(6));
    let add2 = "  operation add2(a: Int64, b: Int64) -> Int64 = a + b";
    assert_eq!(runs("wi_6hvxm.fg1", add2, "    List.foldLeft([1, 2, 3], 0, add2)"), Ok(6));
    // fc2 [1], and its `y: Bool` twin [refused]: the same labels meet by label.
    let decls = "  operation take(f: Function[A = (x: Int64, y: Int64), B = Int64]) -> Int64 = f(7, 1)\n  operation impl(y: Int64, x: Int64) -> Int64 = x";
    assert_eq!(runs("wi_6hvxm.fc2", decls, "    take(impl)"), Ok(7));
    let decls = "  operation take(f: Function[A = (x: Int64, y: Bool), B = Int64]) -> Int64 = f(7, true)\n  operation impl(y: Bool, x: Int64) -> Int64 = x";
    assert_eq!(runs("wi_6hvxm.fc2b", decls, "    take(impl)"), Ok(7));
    // fh1 [1]: labels that are not the same set meet by position.
    let decls = "  operation take(f: (x: Int64, y: Int64) -> Int64) -> Int64 = f(7, 1)\n  operation impl(z: Int64, x: Int64) -> Int64 = x";
    assert_eq!(runs("wi_6hvxm.fh1", decls, "    take(impl)"), Ok(1));
    // fw: [refused, count], [1]; and the slot's `A` a sibling argument decides.
    let fwd = "  operation forward[A, B](a: A, g: (A) -> B) -> B = g(a)";
    let decls = format!("{fwd}\n{TWO}\n{GET_A}");
    assert_eq!(runs("wi_6hvxm.fw1", &decls, "    forward((a: 1, b: 2), two)"), Ok(12));
    assert_eq!(runs("wi_6hvxm.fw3", &decls, "    forward((a: 1, b: 2), get_a)"), Ok(1));
    assert_eq!(runs("wi_6hvxm.fwl", &decls, "    forward((1, 2), lambda (x, y) -> x * 10 + y)"), Ok(12));
    let ap = "  operation ap[A](f: Function[A = A, B = Int64], x: A) -> Int64 = f(x)";
    let decls = format!("{ap}\n{TWO}");
    assert_eq!(runs("wi_6hvxm.app1", &decls, "    ap(two, (1, 2))"), Ok(12));
    assert_eq!(runs("wi_6hvxm.app2", &decls, "    ap(two, (b: 2, a: 1))"), Ok(12));
    // 002's `forward` with a `Function`-typed slot, both shapes of operation [112].
    let fwd2 = "  operation forward(a: (a: Int64, b: Int64), g: Function[A = (a: Int64, b: Int64), B = Int64]) -> Int64 = g(a)";
    let decls = format!("{fwd2}\n{TWO}\n{GET_A}");
    assert_eq!(
        runs("wi_6hvxm.fw4", &decls, "    forward((a: 1, b: 2), two) + forward((a: 1, b: 2), get_a) * 100"),
        Ok(112)
    );
    // w1: a callable of one parameter drops what its tuple lacks [7 each].
    let age_of = "  operation age_of(p: (age: Int64)) -> Int64 = p.age";
    let app = "  operation app(f: ((age: Int64, name: String)) -> Int64, v: (age: Int64, name: String)) -> Int64 = f(v)";
    let decls = format!("{age_of}\n{app}");
    assert_eq!(runs("wi_6hvxm.w1a", &decls, "    let person = (name: \"x\", age: 7)\n    age_of(person)"), Ok(7));
    assert_eq!(runs("wi_6hvxm.w1b", &decls, "    app(age_of, (age: 7, name: \"x\"))"), Ok(7));
    assert_eq!(runs("wi_6hvxm.w1c", &decls, "    app(lambda (p: (age: Int64)) -> p.age, (age: 7, name: \"x\"))"), Ok(7));
    // The binder keeps the type it wrote: the component it drops is not its to read.
    refused(
        "wi_6hvxm.w1d",
        &decls,
        "    app(lambda (p: (age: Int64)) -> p.name.length(), (age: 7, name: \"x\"))",
        &[".name", "no such member"],
        "a dropped component is not read through the binder",
    );
    // A callable of one parameter the slot refuses is judged on a trial σ (`callable_at_slot`):
    // `T` is the `Int64` of `x`. PASSES EITHER WAY, by measurement — the join of the arguments
    // binding a shared type parameter binds `T` from `x` before `f` is read (WI-20260926-NEKR0),
    // and with `f` alone the conformance unify after the refusal binds what the trial would have.
    refused(
        "wi_6hvxm.pick",
        "  operation pick[T](f: Function[A = (a: T, b: T), B = Int64], x: T) -> Int64 = f(x, x)\n  operation onlyac(p: (a: String, b: Int64)) -> Int64 = p.b",
        "    pick(onlyac, 5)",
        &["pick.f (op-arg): expected Function[A = (a: Int64, b: Int64)"],
        "a refused callable pins nothing",
    );
    // A `let` annotation is a slot too.
    let inner = "  operation inner(g: (x: Int64, y: Int64) -> Int64) -> Int64 = g(7, 1)";
    let decls = format!("{inner}\n  operation impl(y: Int64, x: Int64) -> Int64 = x");
    assert_eq!(runs("wi_6hvxm.gval", &decls, "    let g: (x: Int64, y: Int64) -> Int64 = impl\n    inner(g)"), Ok(7));
}

/// A function value drops nothing, and meets another function type only where the two tuples
/// carry the same labels in the same order or one of them is positional (WI-1088).
#[test]
fn a_function_value_drops_nothing_and_keeps_its_mapping() {
    let age_of = "  operation age_of(p: (age: Int64)) -> Int64 = p.age";
    let app = "  operation app(f: ((age: Int64, name: String)) -> Int64, v: (age: Int64, name: String)) -> Int64 = f(v)";
    // [7]
    refused(
        "wi_6hvxm.w1g",
        &format!("{age_of}\n{app}"),
        "    let g: ((age: Int64)) -> Int64 = age_of\n    app(g, (age: 7, name: \"x\"))",
        &["app.f (op-arg)", "got (age: Int64) -> Int64"],
        "a function value is refused at a wider `A`",
    );
    let two = "  operation two(age: Int64, name: String) -> Int64 = age";
    let pair_of = "  operation pair_of(p: (age: Int64, name: String)) -> Int64 = p.age";
    let app3 = "  operation app3(f: ((age: Int64, name: String, id: Int64)) -> Int64, v: (age: Int64, name: String, id: Int64)) -> Int64 = f(v)";
    let app2 = "  operation app2(f: ((age: Int64, name: String)) -> Int64, v: (age: Int64, name: String)) -> Int64 = f(v)";
    // [7]
    refused(
        "wi_6hvxm.w1i",
        &format!("{pair_of}\n{app3}"),
        "    let g: ((age: Int64, name: String)) -> Int64 = pair_of\n    app3(g, (age: 7, name: \"x\", id: 3))",
        &["app3.f (op-arg)"],
        "a function value is refused at a wider `A`, whichever callable it holds",
    );
    // [refused, count]
    refused(
        "wi_6hvxm.w1j",
        &format!("{two}\n{app3}"),
        "    let g: (age: Int64, name: String) -> Int64 = two\n    app3(g, (age: 7, name: \"x\", id: 3))",
        &["app3.f (op-arg)"],
        "the same with an operation of two parameters",
    );
    // [refused, count] both.
    let decls = format!("{two}\n{app2}");
    assert_eq!(runs("wi_6hvxm.w1k", &decls, "    let g: (age: Int64, name: String) -> Int64 = two\n    app2(g, (age: 7, name: \"x\"))"), Ok(7));
    assert_eq!(runs("wi_6hvxm.w1l", &decls, "    app2(two, (age: 7, name: \"x\"))"), Ok(7));
    // cnt [refused, count]: the two spellings are one type.
    assert_eq!(
        runs(
            "wi_6hvxm.cnt",
            two,
            "    let f1: (age: Int64, name: String) -> Int64 = two\n    let f2: ((age: Int64, name: String)) -> Int64 = f1\n    f2((age: 7, name: \"x\"))"
        ),
        Ok(7)
    );
    // w3: through `outer`, a function value meets `inner`'s slot.
    let inner = "  operation inner(g: (x: Int64, y: Int64) -> Int64) -> Int64 = g(7, 1)";
    let lpq = "    outer(lambda (p, q) -> p * 10 + q)";
    for (ns, ty) in [
        ("w3a", "(y: Int64, x: Int64) -> Int64"),
        ("w3b", "Function[A = (y: Int64, x: Int64), B = Int64]"),
        ("w3c", "(p: Int64, q: Int64) -> Int64"),
        ("w3d", "Function[A = (p: Int64, q: Int64), B = Int64]"),
    ] {
        let decls = format!("{inner}\n  operation outer(f: {ty}) -> Int64 = inner(f)");
        refused(&format!("wi_6hvxm.{ns}"), &decls, lpq, &["inner.g (op-arg)"], ns);
    }
    for (ns, ty) in [("w3e", "(Int64, Int64) -> Int64"), ("w3f", "(x: Int64, y: Int64) -> Int64")] {
        let decls = format!("{inner}\n  operation outer(f: {ty}) -> Int64 = inner(f)");
        assert_eq!(runs(&format!("wi_6hvxm.{ns}"), &decls, lpq), Ok(71), "{ns}");
    }
    let decls = "  operation inner(g: (Int64, Int64) -> Int64) -> Int64 = g(7, 1)\n  operation outer(f: (p: Int64, q: Int64) -> Int64) -> Int64 = inner(f)";
    assert_eq!(runs("wi_6hvxm.w3g", decls, lpq), Ok(71));
}

/// A lambda's binder names name its arguments in a call of its value, while its tuple stays
/// positional (decided with the user 2026-11-04; kernel-language §4.4): a named argument meets
/// the binder of its name, in a call written so and in one tuple's spread alike [refused, before
/// this rule; on `50d54d05` `lambda (a, b) -> a` gave 1 for `(a: 1, b: 2)` and 2 for `(b: 2, a:
/// 1)`, the tuple read in its written order — `wi_50b2k`'s known-gap row]. The names are no part
/// of the type: a relation between two function types
/// still sees the positional tuple (002's q8 is `a_callable_meets_its_slot_by_label_or_by_position`'s
/// 6), a lambda written at a slot meets it by position, and a `let` annotated with a positional
/// arrow names nothing.
#[test]
fn a_lambdas_binder_names_name_its_arguments() {
    let g = "    let g = lambda (a, b) -> a * 10 + b\n";
    for (ns, call) in [
        ("bn1", "g((a: 1, b: 2))"),
        ("bn2", "g((b: 2, a: 1))"),
        ("bn3", "g(b: 2, a: 1)"),
        ("bn4", "g(1, b: 2)"),
        ("bn5", "let t = (b: 2, a: 1)\n    g(t)"),
    ] {
        assert_eq!(runs(&format!("wi_6hvxm.{ns}"), "", &format!("{g}    {call}")), Ok(12), "{call}");
    }
    refused(
        "wi_6hvxm.bn6",
        "",
        &format!("{g}    g(c: 1, b: 2)"),
        &["g.c (op-arg)", "named argument 'c' names no parameter"],
        "a name no binder has",
    );
    let take = "  operation take(f: (x: Int64, y: Int64) -> Int64) -> Int64 = f(7, 1)";
    assert_eq!(runs("wi_6hvxm.bn7", take, "    take(lambda (y, x) -> x)"), Ok(1), "by position at a slot");
    refused(
        "wi_6hvxm.bn8",
        TWO,
        "    let h: (Int64, Int64) -> Int64 = two\n    h(a: 1, b: 2)",
        &["h.a (op-arg)"],
        "a positional arrow names nothing",
    );
}

/// No parameter count stands beside the tuple: a lambda's count is its pattern's, refused by
/// the application match where the slot's `A` has another width (WI-801's program).
#[test]
fn a_lambdas_count_is_its_tuple() {
    let take2 = "  operation take2(f: Function[A = (Int64, Int64), B = Int64]) -> Int64 = f(1, 2)";
    refused(
        "wi_6hvxm.l3",
        take2,
        "    take2(lambda (a, b, c) -> a + b + c)",
        &["pattern-position", "expected (_1: Int64, _2: Int64)"],
        "three binders meet two components",
    );
}

/// An operation taken as a value records one binder per parameter, so one whose parameter is no
/// argument place — named `result`, which the declaration then refuses — reaches that refusal
/// [the typer panicked, its binders one short of its parameters].
#[test]
fn an_operation_value_has_one_binder_per_parameter() {
    refused(
        "wi_6hvxm.res",
        "  operation odd(result: Int64, b: Int64) -> Int64 = b\n  operation take(f: (y: Int64, x: Int64) -> Int64) -> Int64 = f(7, 1)",
        "    take(odd)",
        &["parameter name 'result' is reserved"],
        "a parameter named `result`",
    );
}

/// An arrow's parameter list is a tuple type, so its labels are distinct (§4.5) [loads, 12].
#[test]
fn an_arrow_parameter_list_has_distinct_labels() {
    let errs = parse_errs(&program(
        "wi_6hvxm.dup",
        "  operation app(f: (a: Int64, a: Int64) -> Int64) -> Int64 = f(1, 2)",
        "    app(lambda (x, y) -> x * 10 + y)",
    ));
    assert!(
        errs.iter().any(|e| e.contains("duplicate arrow parameter label `a`")),
        "a repeated arrow label is refused where it is written: {errs:?}",
    );
    assert_eq!(
        runs(
            "wi_6hvxm.dup_ok",
            "  operation app(f: (a: Int64, b: Int64) -> Int64) -> Int64 = f(1, 2)",
            "    app(lambda (x, y) -> x * 10 + y)"
        ),
        Ok(12)
    );
}

/// A callback's row places are aligned to the argument's parameters by the mapping it meets the
/// slot with — by label here, so `impl`'s `Modify[x]` is the slot's `Modify[x]` [refused].
#[test]
fn a_callbacks_row_places_follow_the_mapping() {
    let decls = "  operation put(c: Cell[V = Int64], n: Int64) -> Int64 effects Modify[c] =\n    let _ = Cell.set(c, n)\n    n\n  operation hand(f: (x: Cell[V = Int64], y: Cell[V = Int64]) -> Int64 @ {Modify[x]}, p: Cell[V = Int64], q: Cell[V = Int64]) -> Int64 effects {Modify[p]} = f(p, q)\n  operation impl(y: Cell[V = Int64], x: Cell[V = Int64]) -> Int64 effects {Modify[x]} = put(x, 5)";
    // `n * 20 + c * 4 + d`: `impl` writes the cell its `x` takes, which is `p`.
    assert_eq!(
        runs(
            "wi_6hvxm.row1",
            decls,
            "    let c: Cell[V = Int64] = Cell.new(1)\n    let d: Cell[V = Int64] = Cell.new(2)\n    let n = hand(impl, c, d)\n    n * 20 + Cell.get(c) * 4 + Cell.get(d)"
        ),
        Ok(122)
    );
}

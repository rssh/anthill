//! WI-20261105-MHF0B — A LAMBDA BINDER TYPED BY A CALL IN ITS BODY ONLY THROUGH THE CALLEE'S OWN
//! TYPE VARIABLE reaches the lambda's arrow.
//!
//! A callee's type parameter is one variable at every call site, and a call's σ binds it for that
//! call alone. `x * 10` binds the binder's variable to `Multiplicative`'s `T` at `x` and `T` to
//! `Int64` at `10`; the walk keeps a binding only where every variable in it is its own, so the
//! link `?x := ?T` was dropped, the arrow said `?x`, and a use at another type bound `?x` again in
//! its own σ — `g("a")` loaded and stopped at run time. Three places, each a part below: the link
//! is turned round in the call's σ (`?T := ?x`), so `10` binds the binder itself and a call whose
//! result is `T` answers the binder; a binding is read through the call's σ where it names the
//! callee's variable, so `?x := ?T` with `?T := Int64` in the same unify is kept as `Int64`; and a
//! tuple literal handed as an argument is not unified, in a σ nothing reads, with the callee's
//! parameter type, which put the callee's variable in place of the binder's.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: a refusal is asserted by the words that name it, beside the
//! twin that differs in one thing and runs to its value. The bracket in a row's comment is the
//! program's verdict on the tree before this change (ed245d14, measured 2026-11-11 with the debug
//! CLI).
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! THREE PARTS, each backed out in place over a temporary binary of this file and the
//! twenty-seven suites nearest it — the binder lists and their arrows, the tuple patterns, the
//! components and their order, destructuring by label, the arity rows, the binder's variable
//! carrier, the polytype (`wi517`, `wi620`, `wi782`–`wi788`, `wi791`, `wi792`, `wi794`, `wi795`,
//! `wi801`, `wi803`, `wi1010`, `wi1012`, `wi1078`, `wi1083`, `wi_02err`, `wi_12nkg`, `wi_34j8z`,
//! `wi_50b2k`, `wi_6hvxm`, `wi_6nmgq`, `wi_80259`, `wi_edpf6`): 304 rows, green with nothing backed
//! out. Measured 2026-11-11.
//!
//! 1. THE LINK NOT TURNED ROUND (`root_callee_links_at_walk_vars`). 5 FAIL: four rows here —
//!    [`a_binder_typed_through_the_callees_variable_is_held_at_the_use`],
//!    [`a_binder_of_a_list_is_held_at_the_use`], [`a_nested_binder_is_held_at_the_use`],
//!    [`a_call_typed_at_the_callees_variable_answers_the_binder`] — and
//!    `wi_34j8z_tuple_pattern_shape_test::a_let_or_a_match_over_an_unannotated_binder_is_held_to_its_use`,
//!    whose `g(("x", true))` is refused at `g.b` again.
//! 2. A BINDING NOT READ THROUGH THE CALL'S σ (`report_call_solutions`). 2 FAIL:
//!    [`one_argument_linking_and_deciding_the_variable_types_the_binder`] and
//!    [`a_literal_whose_binder_meets_the_variable_first_is_read_through_the_call`].
//! 3. THE LITERAL UNIFIED WITH THE CALLEE'S PARAMETER TYPE (`thread_expected_tuple_fields`). 2
//!    FAIL: [`a_literal_handed_to_the_call_keeps_its_binders`] and
//!    [`a_literal_whose_binder_meets_the_variable_first_is_read_through_the_call`].
//!
//! PASSES UNDER EVERY PART, by design: [`what_the_change_does_not_decide_is_unchanged`] — an
//! operation's own type parameter nothing at the call fixes, an annotated binder — and the
//! `g(1, true)` arm of the list row, refused at `g.b` before this change as after.
//!
//! Where the link is turned round, the callee's variable is bound to the binder's on a bare
//! `Value::Var`. On an interned `Term::Var` the binding entered the hash-consed store, and
//! `wi_02err`'s two counting rows failed. On the occurrence carrier a binder's variable rides, a
//! reader of σ stopped at it and interned it there (`splice_non_term_bindings`): a call's result
//! read `?a` where σ said `Int64`, and `g(1, true)` over `a * 10 + b` was refused for an
//! `Additive` at `Bool`.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// A program whose `go()` is `body`, beside `decls`.
fn program(ns: &str, decls: &str, body: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, String, Bool, List}}\n{decls}\n  operation go() -> Int64 =\n{body}\nend\n"
    )
}

fn runs(ns: &str, decls: &str, body: &str) -> Result<i64, String> {
    run_int64(&program(ns, decls, body), &format!("{ns}.go"))
}

fn refused(ns: &str, decls: &str, body: &str, tokens: &[&str], why: &str) {
    assert_refused_naming(&load_errors_of(&program(ns, decls, body)), tokens, why);
}

/// A binder the body's dispatch types through the callee's variable is typed at the use.
#[test]
fn a_binder_typed_through_the_callees_variable_is_held_at_the_use() {
    const G: &str = "    let g = lambda x -> x * 10";
    // [loads, stops: "type mismatch: expected Int64, got String and Int64"]
    refused(
        "wi_mhf0b.one",
        "",
        &format!("{G}\n    g(\"a\")"),
        &["g._1 (op-arg)", "expected Int64, got String"],
        "a binder `x * 10` types at Int64, used at a String",
    );
    assert_eq!(runs("wi_mhf0b.one2", "", &format!("{G}\n    g(2)")), Ok(20));
}

/// The same, a binder of a list: `a * 10` pins `a` as `+ b` pins `b`.
#[test]
fn a_binder_of_a_list_is_held_at_the_use() {
    const G: &str = "    let g = lambda (a, b) -> a * 10 + b";
    // [loads, stops: "type mismatch: expected Int64, got String and Int64"]
    refused(
        "wi_mhf0b.list",
        "",
        &format!("{G}\n    g(\"a\", 1)"),
        &["g.a (op-arg)", "expected Int64, got String"],
        "the binder `a * 10` types",
    );
    // [refused at `b`, as here: `+ b` reached the arrow before]
    refused(
        "wi_mhf0b.list2",
        "",
        &format!("{G}\n    g(1, true)"),
        &["g.b (op-arg)", "expected Int64, got Bool"],
        "the binder `+ b` types, unchanged",
    );
    assert_eq!(runs("wi_mhf0b.list3", "", &format!("{G}\n    g(3, 1)")), Ok(31));
}

/// The same, a binder nested in the list.
#[test]
fn a_nested_binder_is_held_at_the_use() {
    const G: &str = "    let g = lambda ((a, b), c) -> a * 100";
    // [loads, stops: "type mismatch: expected Int64, got String and Int64"]
    refused(
        "wi_mhf0b.nest",
        "",
        &format!("{G}\n    g((\"x\", true), 3)"),
        &["g.a (op-arg)", "expected Int64, got String"],
        "a nested binder `a * 100` types",
    );
    assert_eq!(runs("wi_mhf0b.nest2", "", &format!("{G}\n    g((2, true), 3)")), Ok(200));
}

/// A call whose result is the callee's variable answers the binders it was linked to: `a + b`
/// over two binders is typed at `a`, where it was typed at `Additive`'s `T` and a use read it at
/// whatever the use bound `T` to.
#[test]
fn a_call_typed_at_the_callees_variable_answers_the_binder() {
    const G: &str = "    let g = lambda ((a, b), c) -> (s: a + b, t: a)";
    // [loads]
    refused(
        "wi_mhf0b.res",
        "",
        &format!("{G}\n    let x: String = g((1, 2), 3).s\n    1"),
        &["x.annotation (let-binding)", "expected String, got Int64"],
        "the sum of two Int64 binders read as a String",
    );
    assert_eq!(
        runs("wi_mhf0b.res2", "", &format!("{G}\n    let x: Int64 = g((1, 2), 3).s\n    x")),
        Ok(3)
    );
    // A lambda the `let` generalizes: each use is its own instance, and its result is what the
    // use gave the binder. [refused naming `?_`, the callee's variable, for `Int64`]
    const TWICE: &str = "    let g = lambda x -> x + x";
    refused(
        "wi_mhf0b.gen",
        "",
        &format!("{TWICE}\n    let y: String = g(2)\n    1"),
        &["y.annotation (let-binding)", "expected String, got Int64"],
        "a generalized lambda's result at a use",
    );
    assert_eq!(
        runs("wi_mhf0b.gen2", "", &format!("{TWICE}\n    let y: Int64 = g(2)\n    y + g(3)")),
        Ok(10)
    );
}

const BOTH: &str = "  operation both[T](p: (a: T, b: T)) -> T = p.a";
const BOTH_L: &str = "  operation bothL[T](p: (a: List[T = T], b: T)) -> T = p.b";

/// One unify can link the binder to the callee's variable and decide that variable both: an
/// argument `(a: x, b: 10)` at `(a: T, b: T)`. The link is read through the call's σ.
#[test]
fn one_argument_linking_and_deciding_the_variable_types_the_binder() {
    const G: &str = "    let g = lambda x -> (let p = (a: x, b: 10)\n      both(p))";
    // [loads]
    refused(
        "wi_mhf0b.one_unify",
        BOTH,
        &format!("{G}\n    g(\"a\")"),
        &["g._1 (op-arg)", "expected Int64, got String"],
        "a binder in a tuple whose other component decides the callee's variable",
    );
    assert_eq!(runs("wi_mhf0b.one_unify2", BOTH, &format!("{G}\n    g(4)")), Ok(4));
}

/// A tuple literal handed as the argument keeps its binders: the parameter type it is expected
/// at names the callee's variable, and is met by the call's unify, not unified into the literal.
/// Here the component before the binder decides the variable, and the call's unify binds the
/// binder at it.
#[test]
fn a_literal_handed_to_the_call_keeps_its_binders() {
    // [loads]
    refused(
        "wi_mhf0b.lit",
        BOTH,
        "    let g = lambda x -> both((a: 10, b: x))\n    g(\"a\")",
        &["g._1 (op-arg)", "expected Int64, got String"],
        "a binder in a literal, after the component that decides the callee's variable",
    );
    assert_eq!(
        runs("wi_mhf0b.lit2", BOTH, "    let g = lambda x -> both((a: 10, b: x))\n    g(4)"),
        Ok(10)
    );
}

/// The same literal with the binder first: the call's one unify links the binder to the
/// variable and then decides the variable, so the link is read through the call's σ.
#[test]
fn a_literal_whose_binder_meets_the_variable_first_is_read_through_the_call() {
    // [loads]
    refused(
        "wi_mhf0b.first",
        BOTH,
        "    let g = lambda x -> both((a: x, b: 10))\n    g(\"a\")",
        &["g._1 (op-arg)", "expected Int64, got String"],
        "a binder in a literal at the callee's variable",
    );
    assert_eq!(
        runs("wi_mhf0b.first2", BOTH, "    let g = lambda x -> both((a: x, b: 10))\n    g(4)"),
        Ok(4)
    );
    // [loads]
    refused(
        "wi_mhf0b.first3",
        BOTH_L,
        "    let g = lambda h -> bothL((a: h, b: 10))\n    g(5)",
        &["g._1 (op-arg)", "expected List[T = Int64], got Int64"],
        "a binder at a parameter type the callee's variable stands inside",
    );
    assert_eq!(
        runs("wi_mhf0b.first4", BOTH_L, "    let g = lambda h -> bothL((a: h, b: 10))\n    g([1])"),
        Ok(10)
    );
}

/// What the change does not decide: a call that leaves an operation's own type parameter open is
/// refused for it, as before, and a binder typed by an annotation is held as it was.
#[test]
fn what_the_change_does_not_decide_is_unchanged() {
    refused(
        "wi_mhf0b.open",
        "  operation pick[T](a: List[T = T], b: List[T = T]) -> List[T = T] = a",
        "    let g = lambda h -> pick(h, h)\n    1",
        &["pick.type_arg", "expected a type for 'T', got unconstrained"],
        "an operation's type parameter nothing at the call fixes",
    );
    refused(
        "wi_mhf0b.ann",
        "",
        "    let g = lambda (x: Int64) -> x * 10\n    g(\"a\")",
        &["g._1 (op-arg)", "expected Int64, got String"],
        "an annotated binder",
    );
}

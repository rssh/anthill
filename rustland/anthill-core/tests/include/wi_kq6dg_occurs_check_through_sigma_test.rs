//! WI-20261003-KQ6DG — THE UNIFIER'S OCCURS CHECK READS A BINDING THROUGH σ, so a call that would
//! bind a variable inside itself is refused at the argument that closes the cycle.
//!
//! `two[A, B](f: (x: A) -> B, g: (y: B) -> A)` called with `lambda (x) -> [x]` and `lambda (y) ->
//! [y]` binds `B` to a list of `A` at `f`; at `g` the binding of `A` to a list of `B` holds no `A`
//! as written, and is `A` inside itself once `B` is read. The check read the binding as written,
//! σ held the cycle, and every deep reader of it recursed until the loader's stack overflowed. The
//! check now follows each bound variable it meets (`occurs_through`, from `bind_resolved`), and the
//! argument loops refuse the argument whose unify it refused (`no_finite_type_since`):
//! `two.g (op-arg): expected a finite type, got ?A = List[T = List[T = ?A]], a type inside itself`.
//! The same program with its lambdas held in `let`s loaded and ran: it meets the cycle in the
//! same unify, and is refused alike.
//!
//! A variable met against itself on another carrier (`Term::Var(v)` against `Value::Var(v)`, which
//! the identity fast-path of `unify_types` tells apart) binds nothing and agrees: the occurs check
//! refused it before as it does now, but the refusal had no reader, and with one it named a
//! variable inside itself where nothing is.
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: a refusal is asserted by the words that name it; a control
//! runs to its value. The bracket in a row's comment is the program's verdict on the tree before
//! this change (f8f5c582, measured 2026-11-11 with the debug CLI).
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! FOUR PARTS, each backed out alone by a temporary switch over a binary of this file and the
//! suites the change reaches — the declaration rule's (`wi_0rp29_member_rule`), the ninth review's
//! (`wi_0rp29_review9_regressions`), the nested callback rows (`wi_rdns4_nested_callback_row`),
//! the provision narrowing (`wi_zbwmc`), the binder rows (`wi_mhf0b`, `wi_34j8z`): 299 rows, green
//! with nothing backed out; and over the family `d-mutual-callbacks`. Measured 2026-11-11.
//!
//! 1. THE OCCURS CHECK THROUGH σ (`occurs_through` in `bind_resolved`, read as written instead).
//!    6 DIE of a stack overflow: [`a_pair_binding_each_parameter_inside_the_other_is_refused_at_the_closing_argument`],
//!    [`the_pair_beside_an_option_is_refused_alike`],
//!    [`the_pair_at_an_operation_applying_it_is_refused_at_the_call`], the ninth review's
//!    `a_cyclic_call_beside_a_projection_over_a_wrong_argument_is_refused`, and the declaration
//!    rule's `a_receiver_binding_circular_around_another_parameter_is_refused` and
//!    `a_written_receiver_argument_admitting_no_receiver_is_not_reached`, which the `binds_a_cycle`
//!    scans this change removed had guarded. 2 FAIL, loading and running:
//!    [`the_pair_held_in_lets_is_refused_alike`] and RDNS4's
//!    `a_cyclic_binding_the_arguments_leave_is_refused_at_the_closing_argument`. The family: 3
//!    moved, the two `let` pairs `runs 1` and the lambda pair `DIED stack overflow`.
//! 2. THE REFUSAL AT THE ARGUMENT (`no_finite_type_since` answering nothing). 7 FAIL, each refused
//!    as `A` unconstrained: the five refusals here — the pair, beside an option, at a body, in
//!    `let`s, [`a_lambda_returning_its_parameter_in_a_list_is_refused_at_its_argument`] — the
//!    ninth review's row and RDNS4's. The family: the six cyclic programs `refused TypeMismatch`.
//! 3. A VARIABLE MET AGAINST ITSELF BINDS NOTHING (the identity test in `bind_resolved`). 2 FAIL:
//!    [`a_pair_of_identities_leaves_its_parameter_unconstrained_in_both_spellings`], its `let`
//!    spelling refused as a variable inside itself, and
//!    `wi_mhf0b_binder_typed_through_callee_var_test::a_call_typed_at_the_callees_variable_answers_the_binder`.
//!    The family: `first=x,second=y,passed=let` moved to `refused TypeMismatch/op-arg`.
//! 4. THE VARIABLE NAMED BY THE CALL'S TYPE PARAMETER LINKED TO IT. 1 FAILS:
//!    [`the_pair_held_in_lets_is_refused_alike`], which names `??param`.
//!
//! PASSES UNDER EVERY PART, by design: [`a_chained_acyclic_pair_runs`] and
//! [`a_pair_of_identities_at_a_fixed_type_runs`]. The direct bind the declaration rule makes of a
//! spec parameter the provision binds (`occurs_through` ahead of it, where a `binds_a_cycle` scan
//! of the whole σ stood) passes every row and family program either way: since the deep σ walk
//! reads a binding holding its own variable once, no verdict reads that binding. The occurs
//! check's own reader is driven by `kb::typing::tests::occurs_through_sigma_tests`.

use crate::common::{assert_refused_naming, load_errors_of, run_int64};

/// A program whose `go()` is `body`, beside `decls`.
fn program(ns: &str, decls: &str, body: &str) -> String {
    format!(
        "namespace {ns}\n  import anthill.prelude.{{Int64, String, List, Option}}\n  import anthill.prelude.Option.{{none}}\n  import anthill.prelude.List.{{cons, nil}}\n{decls}\n  operation go() -> Int64 =\n{body}\nend\n"
    )
}

fn runs(ns: &str, decls: &str, body: &str) -> Result<i64, String> {
    run_int64(&program(ns, decls, body), &format!("{ns}.go"))
}

fn errors(ns: &str, decls: &str, body: &str) -> Vec<String> {
    load_errors_of(&program(ns, decls, body))
}

const TWO: &str = "  operation two[A, B](f: (x: A) -> B, g: (y: B) -> A) -> Int64 = 1";

/// The words of the refusal at `two.g`: the argument that closes the cycle, and the cycle.
const AT_G: &[&str] = &[
    "two.g (op-arg)",
    "expected a finite type, got ?A = List[T = List[T = ?A]], a type inside itself",
];

/// Two lambdas each returning a list of its parameter: `B` a list of `A`, then `A` a list of `B`.
#[test]
fn a_pair_binding_each_parameter_inside_the_other_is_refused_at_the_closing_argument() {
    // [the loader's stack overflowed]
    assert_refused_naming(
        &errors("wi_kq6dg.pair", TWO, "    two(lambda (x) -> [x], lambda (y) -> [y])"),
        AT_G,
        "`A` a list of lists of `A`",
    );
}

/// The same pair beside an option of `A`, which nothing fixes.
#[test]
fn the_pair_beside_an_option_is_refused_alike() {
    // [the loader's stack overflowed]
    assert_refused_naming(
        &errors(
            "wi_kq6dg.opt",
            "  operation two[A, B](k: Option[T = A], f: (x: A) -> B, g: (y: B) -> A) -> Int64 = 1",
            "    two(none, lambda (x) -> [x], lambda (y) -> [y])",
        ),
        AT_G,
        "the pair beside an option",
    );
}

/// The same pair at an operation whose body applies it, `g(f(g(f(1))))`; the body is refused for
/// its own reason (`1` for the rigid `A`), and the call for the cycle.
#[test]
fn the_pair_at_an_operation_applying_it_is_refused_at_the_call() {
    // [the loader's stack overflowed]
    let errs = errors(
        "wi_kq6dg.body",
        "  operation two[A, B](f: (x: A) -> B, g: (y: B) -> A) -> A = g(f(g(f(1))))",
        "    let r = two(lambda (x) -> [x], lambda (y) -> [y])\n    1",
    );
    assert_refused_naming(&errs, AT_G, "the pair at a body applying it");
    assert_refused_naming(&errs, &["f._1 (op-arg)", "expected ?A, got Int64"], "the body's own");
}

/// The pair held in `let`s meets the cycle in the same unify, and is refused in the same words.
/// The variable refused is the first lambda's binder, which the call's `A` was bound to, and it is
/// named `A`.
#[test]
fn the_pair_held_in_lets_is_refused_alike() {
    // [loaded and ran to 1]
    assert_refused_naming(
        &errors(
            "wi_kq6dg.lets",
            TWO,
            "    let f = lambda (x) -> [x]\n    let g = lambda (y) -> [y]\n    two(f, g)",
        ),
        AT_G,
        "the pair from `let`s",
    );
}

/// One lambda returning a list of its parameter where the slot returns the parameter's type: the
/// binding is refused as written, as it was, and the refusal names the argument where it named the
/// parameter as unconstrained.
#[test]
fn a_lambda_returning_its_parameter_in_a_list_is_refused_at_its_argument() {
    // [refused: "one.type_arg: expected a type for 'A', got unconstrained — use `one[A = …](…)`"]
    assert_refused_naming(
        &errors(
            "wi_kq6dg.one",
            "  operation one[A](f: (x: A) -> A) -> Int64 = 1",
            "    one(lambda (x) -> [x])",
        ),
        &["one.f (op-arg)", "expected a finite type, got ?A = List[T = ?A], a type inside itself"],
        "`A` a list of `A`",
    );
}

/// CONTROL — a chained but acyclic call: `B` a list of `A`, `A` what `g` returns, `Int64`. Runs to
/// 42, before and after.
#[test]
fn a_chained_acyclic_pair_runs() {
    // [runs to 42]
    assert_eq!(
        runs(
            "wi_kq6dg.chain",
            "  operation two[A, B](f: (x: A) -> B, g: (y: Int64) -> A) -> B = f(g(41))",
            "    match two(lambda (x) -> [x], lambda (y) -> y + 1)\n      case cons(h, t) -> h\n      case nil -> 0",
        ),
        Ok(42)
    );
}

/// The two identities: `A` and `B` one variable, which nothing fixes. Refused as unconstrained in
/// both spellings — held in `let`s, the variable meets itself on another carrier, and binds nothing.
#[test]
fn a_pair_of_identities_leaves_its_parameter_unconstrained_in_both_spellings() {
    const WHY: &[&str] = &["two.type_arg", "expected a type for 'A', got unconstrained"];
    // [refused, as here]
    assert_refused_naming(
        &errors("wi_kq6dg.ids", TWO, "    two(lambda (x) -> x, lambda (y) -> y)"),
        WHY,
        "two identities",
    );
    // [refused, as here]
    let lets = errors(
        "wi_kq6dg.idlets",
        TWO,
        "    let f = lambda (x) -> x\n    let g = lambda (y) -> y\n    two(f, g)",
    );
    assert_refused_naming(&lets, WHY, "two identities from `let`s");
    assert!(
        !lets.iter().any(|e| e.contains("inside itself")),
        "a variable met against itself is no cycle: {lets:#?}"
    );
}

/// CONTROL — the identities where an argument fixes `A`, in both spellings: run to 7.
#[test]
fn a_pair_of_identities_at_a_fixed_type_runs() {
    const THREE: &str =
        "  operation three[A, B](f: (x: A) -> B, g: (y: B) -> A, a: A) -> A = g(f(a))";
    // [runs to 7]
    assert_eq!(
        runs("wi_kq6dg.fixed", THREE, "    three(lambda (x) -> x, lambda (y) -> y, 7)"),
        Ok(7)
    );
    // [runs to 7]
    assert_eq!(
        runs(
            "wi_kq6dg.fixedlets",
            THREE,
            "    let f = lambda (x) -> x\n    let g = lambda (y) -> y\n    three(f, g, 7)",
        ),
        Ok(7)
    );
}

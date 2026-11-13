//! WI-20261105-P0QGF part 3 — proposal 073 §2: A LAMBDA'S PARAMETER TYPED AT A SPEC OVER A
//! PARAMETER IS AN INSTANCE OF IT, as an operation's is since part 2
//! (`docs/design/instance-values.md` §7).
//!
//! `lambda (x: Additive, a: x.T, b: x.T) -> a + b` holds `Additive`'s operations at `x.T`: the
//! body's `a + b` reads the dictionary the lambda's application hands it as `x`. One closure
//! passed to `sumWith` runs at the instance each call of it is handed — `Int64`'s at
//! `sumWith(f, 2, 3)`, `Float`'s at `sumWith(f, 1.5, 2.5)`.
//!
//! MEASURED before (c17589c8): every lambda here that reads its instance was refused in its body,
//! "missing `requires Additive[T = …]`" at the call, and so was an operation handing its own
//! instance on as `Additive[T = x.T]`.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! Each part backed out by a temporary switch, in one build, over this file and the suites
//! beside it (part 1's and part 2's, `wi_dndzf` both, `wi_6nmgq`, `wi_50b2k`, `wi_mhf0b`,
//! `wi223` three, `wi341`, `wi784`, `wi_0rp29` three, `wi_edpf6`, `wi_n2yek`, `wi_sg16k`,
//! `wi_w2jp7`, `wi_34j8z`: 576 rows). No row outside this file fails under any of them.
//!
//! 1. THE BINDER STANDS FOR ITS REQUIREMENT (`lambda_instance_requires` in the typer's lambda
//!    arm). 6 FAIL, refused at load: every value row but the rule body's, which then runs by
//!    the untyped route a rule-written lambda still takes (instance-values.md §6).
//! 2. THE CLOSURE FILLS THE SLOT FROM ITS ARGUMENT (`enter_closure`). 7 FAIL at the call, the
//!    rule body's among them: the typed route reads the slot.
//! 3. A CALL COVERED BY A LAMBDA'S SLOT READS IT BY NAME (`deferral_to_frame_slot`) — by its
//!    place in the operation's chain. 6 FAIL: the place is past the operation's chain.
//! 4. THE CHAIN NAMES A LAMBDA'S SLOTS (`DictChain::name_at`). 1 FAILS,
//!    [`the_lambdas_instance_is_passed_on`]: a forward to a callee's `requires` and an
//!    application read no name.
//! 5. `x.T` IN A SPEC APPLICATION IS THE PROJECTION TYPE (`type_member_of_variable`). 2 FAIL:
//!    [`an_operations_instance_handed_on_as_its_application`],
//!    [`the_lambdas_instance_is_passed_on`].
//! 6. THE DOT BACKSTOP DOES NOT LOOK INSIDE AN INSTANCE (`surviving_dot_apply`). The same 2.
//!
//! PASSES EITHER WAY, BY DESIGN: the three refusals, of programs refused before too. Added after
//! the ledger, from review: [`a_generalized_lambda_in_the_body_reads_each_use`] and
//! [`a_bare_zero_reads_the_instance_in_both_spellings`], not measured under the switches.

use anthill_core::eval::{Interpreter, Value};

use crate::common::{interp_for, load_errors_of, one_definite_int, show_value};

fn call(interp: &mut Interpreter, op: &str) -> Value {
    match interp.call(op, &[]) {
        Ok(v) => v,
        Err(e) => panic!("`{op}`: {e:?}"),
    }
}

fn shown(interp: &mut Interpreter, op: &str) -> String {
    let v = call(interp, op);
    show_value(interp.kb(), &v)
}

/// A program of `ops` beside 073 §2's `add2`, `sum2` and `sumWith`.
fn program(ns: &str, ops: &str) -> String {
    format!(
        r#"
namespace p0qgf3.{ns}
  import anthill.prelude.{{Int64, Float, Additive}}
  operation add2(x: Additive, a: x.T, b: x.T) -> x.T = a + b
  operation sum2[X](a: X, b: X) -> X requires Additive[T = X] = add2(Additive[T = X], a, b)
  operation sumWith[X](f: (x: Additive, a: x.T, b: x.T) -> x.T, a: X, b: X) -> X
    requires Additive[T = X]
  = f(Additive[T = X], a, b)
{ops}
end
"#
    )
}

const LAMBDA: &str = "lambda (x: Additive, a: x.T, b: x.T) -> a + b";

/// The ticket's row: one closure, each call of `sumWith` handing it the instance its own caller
/// supplied, `Int64`'s and then `Float`'s; and the lambda written at the argument.
#[test]
fn one_closure_runs_at_the_instance_each_call_hands_it() {
    let src = program(
        "sum_with",
        &format!(
            "  operation both() -> (Int64, Float) =
    let f = {LAMBDA}
    let ints = sumWith(f, 2, 3)
    (ints, sumWith(f, 1.5, 2.5))
  operation written() -> Int64 = sumWith({LAMBDA}, 2, 3)
  operation writtenFloat() -> Float = sumWith({LAMBDA}, 1.5, 2.5)"
        ),
    );
    let mut interp = interp_for(&src);
    assert_eq!(shown(&mut interp, "p0qgf3.sum_with.both"), "(5, 4.0)");
    assert_eq!(shown(&mut interp, "p0qgf3.sum_with.written"), "5");
    assert_eq!(shown(&mut interp, "p0qgf3.sum_with.writtenFloat"), "4.0");
}

/// The lambda applied where it is bound, to an application at a known type.
#[test]
fn a_lambda_applied_to_an_application() {
    let src = program(
        "direct",
        &format!(
            "  operation direct() -> Int64 =
    let f = {LAMBDA}
    f(Additive[T = Int64], 2, 3)"
        ),
    );
    assert_eq!(shown(&mut interp_for(&src), "p0qgf3.direct.direct"), "5");
}

/// `zero` takes no `T`: both spellings read the lambda's instance.
#[test]
fn a_member_that_takes_no_carrier_reads_the_lambdas_instance() {
    let src = program(
        "zero",
        "  operation zeros() -> (Int64, Float) =
    let z = lambda (x: Additive) -> Additive.zero[T = x.T]()
    let za = lambda (x: Additive) -> Additive[T = x.T].zero()
    let i = z(Additive[T = Int64])
    (i, za(Additive[T = Float]))",
    );
    assert_eq!(shown(&mut interp_for(&src), "p0qgf3.zero.zeros"), "(0, 0.0)");
}

/// The instance passed on: as a value to an operation typed at the spec, as the dictionary a
/// generic callee's `requires` is owed, and as an application the body writes.
#[test]
fn the_lambdas_instance_is_passed_on() {
    let src = program(
        "pass",
        "  operation passed() -> (Int64, Int64, Float) =
    let asValue = lambda (x: Additive, a: x.T, b: x.T) -> add2(x, a, b)
    let toGeneric = lambda (x: Additive, a: x.T, b: x.T) -> sum2(a, b)
    let asApplication = lambda (x: Additive, a: x.T, b: x.T) -> add2(Additive[T = x.T], a, b)
    let v = asValue(Additive[T = Int64], 2, 3)
    let g = toGeneric(Additive[T = Int64], 2, 3)
    (v, g, asApplication(Additive[T = Float], 1.5, 2.5))",
    );
    assert_eq!(shown(&mut interp_for(&src), "p0qgf3.pass.passed"), "(5, 5, 4.0)");
}

/// An operation's instance parameter handed on as the application `Additive[T = x.T]`, which
/// is the parameter's own instance (instance-values.md §7). Refused on c17589c8, "expected the
/// instance `Additive[T = x.T]`, got an argument that names no type": the argument `x.T` was
/// read as a value's dot, and the dot left in the stored body was then refused as one eval
/// cannot run.
#[test]
fn an_operations_instance_handed_on_as_its_application() {
    let src = program(
        "op_app",
        "  operation viaApp(x: Additive, a: x.T, b: x.T) -> x.T = add2(Additive[T = x.T], a, b)
  operation viaAppInts() -> Int64 = viaApp(Additive[T = Int64], 2, 3)
  operation viaAppFloats() -> Float = viaApp(Additive[T = Float], 1.5, 2.5)",
    );
    let mut interp = interp_for(&src);
    assert_eq!(shown(&mut interp, "p0qgf3.op_app.viaAppInts"), "5");
    assert_eq!(shown(&mut interp, "p0qgf3.op_app.viaAppFloats"), "4.0");
}

/// Two instances, of one lambda and of a lambda written in its body: each call reads its own.
#[test]
fn two_instances_each_answer_their_own_carrier() {
    let src = program(
        "two",
        "  operation oneLambda() -> Float =
    let f = lambda (x: Additive, y: Additive, a: x.T, b: y.T) -> b + b
    f(Additive[T = Int64], Additive[T = Float], 1, 2.5)
  operation nested() -> (Int64, Float) =
    let f = lambda (x: Additive, a: x.T) ->
      let g = lambda (y: Additive, b: y.T) -> (a + a, b + b)
      g(Additive[T = Float], 1.25)
    f(Additive[T = Int64], 1)",
    );
    let mut interp = interp_for(&src);
    assert_eq!(shown(&mut interp, "p0qgf3.two.oneLambda"), "5.0");
    assert_eq!(shown(&mut interp, "p0qgf3.two.nested"), "(2, 2.5)");
}

/// A lambda's parameter named as the operation's is another instance: the lambda's body reads
/// its own, and the operation's body the operation's.
#[test]
fn a_lambda_parameter_named_as_the_operations_is_its_own_instance() {
    let src = program(
        "shadow",
        "  operation sh(x: Additive, a: x.T) -> (x.T, Float) =
    let f = lambda (x: Additive, b: x.T) -> b + b
    let own = a + a
    let other = f(Additive[T = Float], 1.5)
    (own, other)
  operation shInts() -> (Int64, Float) = sh(Additive[T = Int64], 3)",
    );
    assert_eq!(shown(&mut interp_for(&src), "p0qgf3.shadow.shInts"), "(6, 3.0)");
}

/// A rule body's lambda, handed to an operation.
#[test]
fn a_rule_bodys_lambda_reads_its_instance() {
    let src = program(
        "rule",
        &format!("  rule viaRule(?r) :- ?r <=> sumWith({LAMBDA}, 2, 3)"),
    );
    let mut interp = interp_for(&src);
    assert_eq!(one_definite_int(interp.kb_mut(), "p0qgf3.rule.viaRule"), Some(5));
}

fn refused(ns: &str, ops: &str) -> Vec<String> {
    let errors = load_errors_of(&program(ns, ops));
    assert!(!errors.is_empty(), "expected a refusal of:\n{ops}");
    errors
}

fn says(errors: &[String], text: &str) -> bool {
    errors.iter().any(|e| e.contains(text))
}

/// kernel-language §8.2: the instance is no value of its carrier, in a lambda as in an
/// operation. Refused before too.
#[test]
fn an_instance_is_no_value_of_its_carrier() {
    let errors = refused(
        "bad_carrier",
        "  operation bad() -> Int64 =\n    let f = lambda (x: Additive, a: x.T) -> x + a\n    f(Additive[T = Int64], 2)",
    );
    assert!(says(&errors, "got Additive[T = x.T]"), "{errors:?}");
}

/// The body's `1` is no `x.T`: no value chooses the carrier. Refused before too.
#[test]
fn a_literal_is_no_value_at_the_instance() {
    let errors = refused(
        "bad_literal",
        "  operation bad() -> Int64 = sumWith(lambda (x: Additive, a: x.T, b: x.T) -> a + 1, 2, 3)",
    );
    assert!(says(&errors, "expected x.T, got Int64"), "{errors:?}");
}

/// `2` is no `Additive`: the application reads the arrow's result `x.T` at the argument `2`,
/// whose type has no `T` (an operation's call is refused at its parameter first, "expected
/// Additive, got Int64"). Refused before too, there for the body's missing `requires`.
#[test]
fn a_value_of_a_provider_is_no_instance() {
    let errors = refused(
        "bad_arg",
        &format!("  operation bad() -> Int64 =\n    let f = {LAMBDA}\n    f(2, 2, 3)"),
    );
    assert!(says(&errors, "type 'anthill.prelude.Int64' has no member 'T'"), "{errors:?}");
}

/// A lambda generalized in an instance lambda's body, used at `Int64` and at the instance's `T`:
/// each use reads its own dictionary, the instance's at `a`. The operation spelling answers the
/// same. Found by review as a shape that might hold a call on the lambda's slot; measured, it
/// does not.
#[test]
fn a_generalized_lambda_in_the_body_reads_each_use() {
    let src = program(
        "general",
        "  operation go() -> Float =
    let f = lambda (x: Additive, a: x.T) ->
      let g = lambda v -> v + v
      let i = g(1)
      g(a)
    f(Additive[T = Float], 1.25)
  operation viaOp(x: Additive, a: x.T) -> x.T =
    let g = lambda v -> v + v
    let i = g(1)
    g(a)
  operation go2() -> Float = viaOp(Additive[T = Float], 1.25)",
    );
    let mut interp = interp_for(&src);
    assert_eq!(shown(&mut interp, "p0qgf3.general.go"), "2.5");
    assert_eq!(shown(&mut interp, "p0qgf3.general.go2"), "2.5");
}

/// `Additive.zero()` with no bracket reads the instance in a lambda as in an operation.
#[test]
fn a_bare_zero_reads_the_instance_in_both_spellings() {
    let src = program(
        "bare_zero",
        "  operation go() -> Int64 =
    let z = lambda (x: Additive) -> Additive.zero()
    z(Additive[T = Int64])
  operation zo(x: Additive) -> x.T = Additive.zero()
  operation go2() -> Int64 = zo(Additive[T = Int64])",
    );
    let mut interp = interp_for(&src);
    assert_eq!(shown(&mut interp, "p0qgf3.bare_zero.go"), "0");
    assert_eq!(shown(&mut interp, "p0qgf3.bare_zero.go2"), "0");
}

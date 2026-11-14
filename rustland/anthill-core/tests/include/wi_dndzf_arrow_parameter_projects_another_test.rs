//! WI-20261002-DNDZF part 3 — a parameter type or the result of an arrow may project another of
//! its parameters, in either order, as an operation's may (kernel-language §4.4).
//!
//! Over `sort Box { sort E = ?  entity box(v: E) }`: `lambda (x: Box, y: x.E) -> y` applied to
//! `box(v: 1)` and `7` takes `y: Int64` and answers `Int64`, and `takes(f: (x: Box, y: x.E) ->
//! x.E)` accepts that lambda. A cycle (`(x: y.E, y: x.E)`, `(x: x.E)`) is refused, as it is in
//! an operation's signature.
//!
//! MEASURED before (6348891e): every arrow and lambda spelling here was refused "unresolved type
//! name 'x.E' … not a value projection"; the operation controls ran.
//!
//! ── WHICH ROWS FAIL WHEN A PART IS BACKED OUT ────────────────────────────────
//!
//! Each part backed out by a temporary switch, in one build, over this file's rows and the suites
//! beside it (part 1's list, and `wi398`, `wi376`, `wi397`, `wi400`, `wi459`, `wi460`, `wi1059`,
//! `wi1083`, `wi_sg16k`, `wi_p0qgf`, `wi_mhf0b`, `wi_p1pvt`, `wi341`: 778 rows). Parts 1–9 were
//! measured before rows 10 and 11's were written; no row outside this file fails under any of
//! them.
//!
//! 1. A PROJECTION'S RECEIVER IS AN ARROW'S PARAMETER WHERE ONE IS IN SCOPE
//!    (`Loader::arrow_binder` in the projection classifier) — read as before. 6 FAIL: every row
//!    with a written arrow, the cycle row included.
//! 2. … OF AN ENCLOSING ARROW TOO (`arrow_binder` over every frame) — the innermost only. 1
//!    FAILS: [`an_arrow_projects_its_own_parameter_wherever_it_is_written`], the curried slot.
//! 3. A LAMBDA'S BINDERS ARE IN SCOPE IN ITS OWN ANNOTATIONS (the pattern visited inside the
//!    lambda's frame) — outside. 5 FAIL: every row with a lambda projecting its parameter.
//! 4. AN APPLICATION READS THE ARROW AT ITS ARGUMENTS (`ApplicationPlaces::read_at_arguments`)
//!    — as written. 5 FAIL.
//! 5. A WALK FROM OUTSIDE LEAVES AN ARROW'S OWN PROJECTION AS IT IS (`ArrowBinders`) — read at
//!    the call's arguments. 4 FAIL: a written arrow as an operation's parameter.
//! 6. A LAMBDA CHECKED AGAINST AN ARROW READS IT IN ITS OWN NAMES (`in_lambda_binders`) — as
//!    written. 4 FAIL; [`a_function_that_does_not_keep_the_dependency_is_refused`] by another
//!    refusal than its own (`binder-annotation`, `expected f.x.E, got x.E`).
//! 7. AN OCCURRENCE'S HASH-CONSED CHILD IS RE-KEYED (`rewrite_ref_child`) — passed through. The
//!    same 4 FAIL as 6: the renaming in 6 and in the comparison of two arrows reaches a
//!    single-reference projection only through it.
//! 8. A LAMBDA'S BINDERS ARE BOUND BEFORE ANY ANNOTATION IS READ — one at a time. 2 FAIL: a
//!    parameter projecting a later one.
//! 9. A CYCLE IS REFUSED — written (`LoadError::CyclicArrowProjection`), and a lambda's: 1 FAILS
//!    each, [`a_cycle_among_an_arrows_parameters_is_refused`].
//! 10. A BARE NAME READS A PARAMETER ONLY IN A ROW (`ArrowBinderFrame::in_row`) — in a parameter
//!    type and the result too. 2 FAIL: [`a_parameter_named_like_a_type_parameter_is_not_that_type`]
//!    and `wi341_callback_modify_test::arrow_param_name_colliding_with_type_param_is_not_captured`.
//! 11. AN APPLICATION RE-KEYS THE RESULT'S LABELS TO ITS ARGUMENTS
//!    (`ApplicationPlaces::result_at_arguments`) — kept as written. 4 FAIL:
//!    [`an_inner_arrow_names_the_outer_ones_parameter`],
//!    [`a_returned_lambda_writes_the_cell_its_application_was_given`], and two rows beside whose
//!    reason it changes, not their verdict (refused, now as a write to the cell the application
//!    was given rather than as a binder out of its scope): `wi_edpf6`'s and `wi_0rp29`'s
//!    returned-lambda rows.
//!
//! PASSES EITHER WAY, BY DESIGN: [`the_operation_and_scope_controls_run`].
//!
//! EVERY ROW DRIVES WHAT IT CLAIMS: an admitted program RUNS to its value; a refusal is asserted
//! by the words that name it, beside a program that differs in one thing and runs.

use anthill_core::eval::Value;

use crate::common::{assert_refused_naming, interp_for, load_errors_of, run_int64, show_value};

/// A program over `Box` with `decls` beside it; `go()` answers an `Int64`.
fn program(ns: &str, decls: &str) -> String {
    format!(
        r#"
namespace wi_dndzf3.{ns}
  import anthill.prelude.{{Int64, Float, String, Additive, Cell, Unit, Modify}}
  import anthill.realization.runtime.Dictionary
  sort Box
    sort E = ?
    entity box(v: E)
  end
{decls}
end
"#
    )
}

fn runs(ns: &str, decls: &str) -> Result<i64, String> {
    run_int64(&program(ns, decls), &format!("wi_dndzf3.{ns}.go"))
}

fn refused(ns: &str, decls: &str, tokens: &[&str], why: &str) {
    assert_refused_naming(&load_errors_of(&program(ns, decls)), tokens, why);
}

const TAKES: &str = "  operation takes(f: (x: Box, y: x.E) -> x.E) -> Int64 = f(box(v: 1), 7)";
const TAKES_REV: &str = "  operation takesRev(f: (y: x.E, x: Box) -> x.E) -> Int64 = f(7, box(v: 1))";

/// A LAMBDA'S PARAMETER PROJECTS ANOTHER, in either order, and the application reads it at the
/// argument that parameter takes.
#[test]
fn a_lambda_parameter_projects_another_in_either_order() {
    let lam = "  operation go() -> Int64 =\n    let f = lambda (x: Box, y: x.E) -> y\n    f(box(v: 1), 7)";
    assert_eq!(runs("lam", lam), Ok(7));
    let rev = "  operation go() -> Int64 =\n    let g = lambda (y: x.E, x: Box) -> y\n    g(7, box(v: 1))";
    assert_eq!(runs("lam_rev", rev), Ok(7));
    let wrong = "  operation go() -> Int64 =\n    let f = lambda (x: Box, y: x.E) -> y\n    f(box(v: 1), \"s\")";
    refused("lam_wrong", wrong, &["f.y (op-arg)", "expected Int64, got String"], "y is the box's E");
}

/// AN ARROW WRITTEN AS A PARAMETER'S TYPE PROJECTS ITS OWN PARAMETER, in either order: the lambda
/// written for it, an un-annotated one and an operation each fit it.
#[test]
fn a_written_arrow_parameter_projects_another_in_either_order() {
    let lam = format!("{TAKES}\n  operation go() -> Int64 = takes(lambda (x: Box, y: x.E) -> y)");
    assert_eq!(runs("takes", &lam), Ok(7));
    let rev = format!("{TAKES_REV}\n  operation go() -> Int64 = takesRev(lambda (y: x.E, x: Box) -> y)");
    assert_eq!(runs("takes_rev", &rev), Ok(7));
    let untyped = format!("{TAKES}\n  operation go() -> Int64 = takes(lambda (x, y) -> y)");
    assert_eq!(runs("takes_untyped", &untyped), Ok(7));
    let op = format!(
        "{TAKES}\n  operation pick(b: Box, v: b.E) -> b.E = v\n  operation go() -> Int64 = takes(pick)"
    );
    assert_eq!(runs("takes_op", &op), Ok(7));
}

/// A FUNCTION THAT DOES NOT KEEP THE DEPENDENCY IS REFUSED where the arrow is expected: one
/// answering `Int64` for `x.E`, one taking `Int64` for `x.E`, and an operation whose parameters
/// stand in the other order.
#[test]
fn a_function_that_does_not_keep_the_dependency_is_refused() {
    let five = format!("{TAKES}\n  operation go() -> Int64 = takes(lambda (x: Box, y: x.E) -> 5)");
    refused("keeps_result", &five, &["takes.f (op-arg)"], "an Int64 is no x.E");
    let narrow = format!("{TAKES}\n  operation go() -> Int64 = takes(lambda (x: Box, y: Int64) -> y)");
    refused("keeps_param", &narrow, &["binder-annotation", "expected x.E, got Int64"], "x.E is no Int64");
    let swapped = format!(
        "{TAKES}\n  operation pick(v: b.E, b: Box) -> b.E = v\n  operation go() -> Int64 = takes(pick)"
    );
    refused("keeps_order", &swapped, &["takes.f (op-arg)"], "parameters in the other order");
}

/// THE PROJECTION IS READ AT THE ARGUMENT: a variable whose type fixes the member gives it, and
/// one of an open `Box` gives its own `b.E`, which `7` is not and a `z: b.E` is.
#[test]
fn the_projection_is_read_at_the_argument_it_takes() {
    let fixed = "  operation h(b: Box[E = Int64], f: (x: Box, y: x.E) -> x.E) -> Int64 = f(b, 7)\n  operation go() -> Int64 = h(box(v: 1), lambda (x: Box, y: x.E) -> y)";
    assert_eq!(runs("arg_fixed", fixed), Ok(7));
    let open = "  operation h(b: Box, z: b.E, f: (x: Box, y: x.E) -> x.E) -> b.E = f(b, z)\n  operation go() -> Int64 = h(box(v: 1), 7, lambda (x: Box, y: x.E) -> y)";
    assert_eq!(runs("arg_open", open), Ok(7));
    let literal = "  operation h(b: Box, f: (x: Box, y: x.E) -> x.E) -> b.E = f(b, 7)";
    refused("arg_open_literal", literal, &["f.y (op-arg)", "expected b.E, got Int64"], "7 is no b.E");
}

/// AN ARROW PROJECTING ITS OWN PARAMETER IN ANY TYPE POSITION: an entity's field, an alias, a
/// `let` annotation, an operation's result, and an arrow returned by an arrow.
#[test]
fn an_arrow_projects_its_own_parameter_wherever_it_is_written() {
    let field = "  entity hold(f: (x: Box, y: x.E) -> x.E)\n  operation go() -> Int64 =\n    let h = hold(f: lambda (x: Box, y: x.E) -> y)\n    let g = h.f\n    g(box(v: 1), 7)";
    assert_eq!(runs("field", field), Ok(7));
    let alias = "  sort Dep = (x: Box, y: x.E) -> x.E\n  operation takes(f: Dep) -> Int64 = f(box(v: 1), 7)\n  operation go() -> Int64 = takes(lambda (x: Box, y: x.E) -> y)";
    assert_eq!(runs("alias", alias), Ok(7));
    let annotation = "  operation go() -> Int64 =\n    let f: (x: Box, y: x.E) -> x.E = lambda (a: Box, b: a.E) -> b\n    f(box(v: 1), 7)";
    assert_eq!(runs("annotation", annotation), Ok(7));
    let result = "  operation mk() -> (x: Box, y: x.E) -> x.E = lambda (a: Box, b: a.E) -> b\n  operation go() -> Int64 =\n    let f = mk()\n    f(box(v: 1), 7)";
    assert_eq!(runs("result", result), Ok(7));
    let curried = "  operation takesC(f: (x: Box) -> (y: x.E) -> x.E) -> Int64 =\n    let g = f(box(v: 1))\n    g(7)\n  operation go() -> Int64 = takesC(lambda (x: Box) -> lambda (y: x.E) -> y)";
    assert_eq!(runs("curried", curried), Ok(7));
}

/// AN ARROW INSIDE AN ARROW NAMES THE OUTER ONE'S PARAMETER, in its row as in a projection, and
/// applying the outer one re-keys it to the argument: `g(c)` answers a function writing `c` —
/// run, and refused where the caller declares no write to `c`. A destructured parameter beside
/// a projecting one fits the slot too.
#[test]
fn an_inner_arrow_names_the_outer_ones_parameter() {
    let mk = "  operation mk(c: Cell[V = Int64]) -> (k: Cell[V = Int64]) -> (u: Unit) -> Unit @ {Modify[k]} =\n    lambda (k: Cell[V = Int64]) -> lambda (u: Unit) -> Cell.set(k, 5)";
    let fresh = format!("{mk}\n  operation go() -> Int64 =\n    let c: Cell[V = Int64] = Cell.new(1)\n    let d: Cell[V = Int64] = Cell.new(2)\n    let g = mk(d)\n    let h = g(c)\n    let _ = h(())\n    Cell.get(c) * 10 + Cell.get(d)");
    assert_eq!(runs("inner_row", &fresh), Ok(52));
    let held = format!("{mk}\n  operation w(c: Cell[V = Int64]) -> Int64 =\n    let g = mk(c)\n    let h = g(c)\n    let _ = h(())\n    1");
    refused("inner_row_held", &held, &["w.effects (op-effects)", "Modify[T = c]"], "writes the caller's c");
    let destructured = format!("{TAKES}\n  operation go() -> Int64 = takes(lambda (box(v: q), y) -> y)");
    assert_eq!(runs("destructured", &destructured), Ok(7));
}

/// A RETURNED LAMBDA WRITES THE CELL ITS APPLICATION WAS GIVEN, as the callback an operation
/// returns does: `mk(d)` writes `d`, which `EffP = {Modify[d]}` admits beside `-Modify[x]` over
/// `c` (1 + 42); and the same over `c` itself loads whether the callback is a lambda's result or
/// an operation's (`setter(c)`), the label naming a value in scope.
#[test]
fn a_returned_lambda_writes_the_cell_its_application_was_given() {
    let app = "  operation app[EffP](q: Cell[V = Int64], f: (x: Cell[V = Int64]) -> Unit @ {EffP, -Modify[x]}) -> Unit effects {EffP} = f(q)\n  operation mkOf(k: Cell[V = Int64]) -> (j: Cell[V = Int64]) -> Unit @ {Modify[k]} =\n    lambda (j: Cell[V = Int64]) -> Cell.set(k, 42)";
    let other = format!("{app}\n  operation other(c: Cell[V = Int64], d: Cell[V = Int64]) -> Int64 effects {{Modify[d]}} =\n    let mk = lambda (k: Cell[V = Int64]) -> lambda (j: Cell[V = Int64]) -> Cell.set(k, 42)\n    let _ = app[EffP = {{Modify[d]}}](c, mk(d))\n    Cell.get(c) + Cell.get(d)\n  operation go() -> Int64 =\n    let c: Cell[V = Int64] = Cell.new(1)\n    let d: Cell[V = Int64] = Cell.new(1)\n    other(c, d)");
    assert_eq!(runs("returned_other", &other), Ok(43));
    for (spelling, callback) in [("lambda", "mk(c)"), ("operation", "mkOf(c)")] {
        let same = format!("{app}\n  operation same(c: Cell[V = Int64]) -> Int64 effects {{Modify[c]}} =\n    let mk = lambda (k: Cell[V = Int64]) -> lambda (j: Cell[V = Int64]) -> Cell.set(k, 42)\n    let _ = app[EffP = {{Modify[c]}}](c, {callback})\n    Cell.get(c)\n  operation go() -> Int64 =\n    let c: Cell[V = Int64] = Cell.new(1)\n    same(c)");
        assert_eq!(runs(&format!("returned_same_{spelling}"), &same), Ok(42), "{spelling}");
    }
}

/// A BARE NAME IN A PARAMETER TYPE OR THE RESULT IS A TYPE, though a parameter has that name:
/// `(a: a) -> a` and `lambda (a: a) -> a` under a type parameter `a` (a parameter is named there
/// only as a projection's receiver).
#[test]
fn a_parameter_named_like_a_type_parameter_is_not_that_type() {
    let decls = "  operation applyId[a](v: a, f: (a: a) -> a) -> a = f(v)\n  operation lamId[a](v: a) -> a =\n    let f = lambda (a: a) -> a\n    f(v)\n  operation lamTwo[a](v: a, w: a) -> a =\n    let f = lambda (a: a, b: a) -> b\n    f(v, w)\n  operation go() -> Int64 = applyId(3, lambda (q: Int64) -> q) + lamId(4) + lamTwo(1, 5)";
    assert_eq!(runs("type_named", decls), Ok(12));
}

/// A CYCLE AMONG AN ARROW'S PARAMETERS IS REFUSED — written, onto itself, and a lambda's.
#[test]
fn a_cycle_among_an_arrows_parameters_is_refused() {
    let written = "  operation takesCyc(f: (x: y.E, y: x.E) -> Int64) -> Int64 = 1";
    refused("cycle_written", written, &["cyclic projection among an arrow's parameters: x -> y -> x"], "x and y");
    let own = "  operation takesSelf(f: (x: x.E) -> Int64) -> Int64 = 1";
    refused("cycle_self", own, &["cyclic projection among an arrow's parameters: x -> x"], "x onto itself");
    let lambda = "  operation go() -> Int64 =\n    let g = lambda (x: y.E, y: x.E) -> 1\n    1";
    refused("cycle_lambda", lambda, &["cyclic projection among a lambda's parameters: x -> y -> x"], "a lambda's");
}

/// WI-817's witness, P0QGF's `sumWith`, with the operation it takes: the instance a call hands
/// the arrow's `x` fixes `x.T`. (The lambda spelling, `lambda (x: Additive, a: x.T, b: x.T) -> a
/// + b`, waits on a lambda's parameter typed at a spec being an instance, WI-20261105-P0QGF.)
#[test]
fn sum_with_reads_its_callbacks_projection_at_the_instance_it_hands() {
    let decls = "  operation sumWith[X](f: (x: Additive, a: x.T, b: x.T) -> x.T, a: X, b: X) -> X\n    requires Additive[T = X]\n  = f(Dictionary.instance[Additive[T = X]](), a, b)\n  operation add2(x: Additive, a: x.T, b: x.T) -> x.T = a + b\n  operation go() -> Int64 = sumWith(add2, 2, 3)\n  operation floats() -> Float = sumWith(add2, 1.5, 2.5)";
    assert_eq!(runs("sum_with", decls), Ok(5));
    let mut interp = interp_for(&program("sum_with_float", decls));
    let v: Value = interp
        .call("wi_dndzf3.sum_with_float.floats", &[])
        .unwrap_or_else(|e| panic!("floats: {e:?}"));
    assert_eq!(show_value(interp.kb(), &v), "4.0");
}

/// CONTROLS, run before this change as after: an operation's parameter projecting an earlier or
/// a later one, and a lambda's binder projecting a receiver in scope.
#[test]
fn the_operation_and_scope_controls_run() {
    let ops = "  operation viaOp(x: Box, y: x.E) -> x.E = y\n  operation viaOpRev(y: x.E, x: Box) -> x.E = y\n  operation go() -> Int64 = viaOp(box(v: 1), 7) + viaOpRev(7, box(v: 1))";
    assert_eq!(runs("ctrl_ops", ops), Ok(14));
    let scope = "  operation u(b: Box[E = Int64]) -> Int64 =\n    let f = lambda (y: b.E) -> y\n    f(7)\n  operation go() -> Int64 = u(box(v: 1))";
    assert_eq!(runs("ctrl_scope", scope), Ok(7));
}

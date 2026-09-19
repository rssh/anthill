//! WI-20260918-R541X — A BODY READ OF A TYPE PARAMETER MUST NOT DANGLE SILENTLY.
//!
//! A run-time `Type` value came back naming a type PARAMETER (`T`, `Box(V: !P)`) where the
//! program asked for the type it stands for. Every fixture below LOADED CLEAN and answered
//! that wrong value before this ticket. Rows by the ticket's letters:
//!
//!  (A) a sort-parameter entry whose walk is the ENCLOSING OPERATION's own rigid — and, for a
//!      receiver-less spec member, a sort parameter nothing at the call pins at all although
//!      the scope's own `requires` clause names it.
//!  (B) a rigid NESTED inside an entry (`Box[V = !P]`).
//!  (C) a provider's / witness's own parameters on a member entered through a requirement
//!      slot — NOT fixed here (its own ticket, it needs a design decision); its rows assert
//!      (D)'s LOCATED fault instead of the old wrong answer.
//!  (D) the bare-head arms (`Expr::TypeValue`, `reduce_var`'s WI-206 arm) refuse a type
//!      parameter that missed the frame channel: `EvalError::UnboundTypeParam`.
//!
//! BACK-OUTS, each a mutation measured on its own over this file's rows:
//!
//! * **(A-rewrite)** — the sort-parameter loop of the `resolved_type_args` write skips the
//!   enclosing-operation skolem again (no `apply_enclosing_param_refs` there): 5 red —
//!   [`a_generic_caller_grounds_a_sort_param_read`], [`two_generic_levels_ground_a_sort_param_read`],
//!   [`a_nested_rigid_under_a_sort_param_is_grounded`], and the two binder rows below,
//!   because what the binder writes is the enclosing operation's RIGID and only this
//!   rewrite makes that readable at run time.
//! * **(A-binder)** — `bind_sort_params_from_sole_enclosing_requirement` returns at entry:
//!   2 red, [`a_spec_default_reads_the_requirement_it_runs_under`],
//!   [`the_requirement_reaches_through_two_generic_levels`].
//! * **(B)** — `apply_enclosing_param_refs` rewrites the WHOLE entry only: 2 red,
//!   [`a_nested_rigid_under_an_op_param_is_grounded`],
//!   [`a_nested_rigid_under_a_sort_param_is_grounded`].
//! * **(D)** — `refuse_unbound_type_param` returns `Ok(())`: 3 red,
//!   [`two_clauses_over_one_spec_are_a_located_fault`] and both (C) rows, which then answer
//!   the silent `T` / `Box(V: V)` / `Crate(W: E)` again. (Measured before the channel-half
//!   row below existed; it too goes through that function.)
//! * **(sort rewrite)** — `enclosing_sort_param_ref_rewrite`'s pairs not added: 1 red,
//!   [`a_sort_level_requirement_reaches_the_member`]. Found by `/code-review`.
//! * **(D, channel half)** — `refuse_ungrounded_channel_value` returns `Ok(())`: red
//!   [`an_ungrounded_channel_value_is_a_located_fault`], which then answers `SHold.E`'s
//!   name as a type.
//!
//! WHY (C)'s SPEC IS BODY-LESS. A receiver-less member WITH a default body
//! (`TypeTerm.valueOf`) is typed as a plain call to that default (WI-365's route), so a
//! provider's override of it is never reached through the slot — MEASURED here: with
//! `Box` overriding `TypeTerm.valueOf` as `Option[T = V]`, `tagOfP(box(…))` still answered
//! the default's `Box(V: Boom)`. That is a dispatch defect of its own, not this ticket's; a
//! body-less `TypeTermB.valueOfB` does dispatch to the provider, which is (C)'s subject.
//!
//! PASS EITHER WAY BY DESIGN — controls, stated at their sites:
//! [`control_the_monomorphic_site`], [`control_the_unwitnessed_constructor`],
//! [`control_wi708_whole_entry_op_param`], [`control_rs2g4_receiver_bracket`],
//! [`control_the_expression_form`].

use anthill_core::eval::{EvalError, Value};
use anthill_core::persistence::print::TermPrinter;

use crate::common::interp_for;

const SRC: &str = r#"
namespace test.r541x
  import anthill.prelude.{Option, Int64, String, Type}
  import anthill.prelude.Option.{none}

  sort TypeTerm
    import anthill.prelude.Type
    sort T = ?
    operation valueOf() -> Type = T
  end

  sort Boom
    entity boom(why: String)
    provides TypeTerm[T = Boom]
  end

  sort Err2
    import anthill.prelude.Type
    sort T = ?
    operation tagOf(error: T) -> Type = T
  end

  -- (C)'s spec is BODY-LESS, so a call through its slot really dispatches to the
  -- provider's member. A DEFAULTED member called receiver-less is typed as a plain call
  -- to the default and never reaches a provider's override — see the module doc.
  sort TypeTermB
    import anthill.prelude.Type
    sort T = ?
    operation valueOfB() -> Type
  end

  sort Box
    import anthill.prelude.Type
    sort V = ?
    entity box(v: V)
    provides TypeTermB[T = Box[V = V]]
    operation valueOfB() -> Type = Box[V = V]
  end

  sort Crate
    sort W = ?
    entity crate(w: W)
  end

  sort CrateTT
    import anthill.prelude.Type
    sort E = ?
    provides TypeTermB[T = Crate[W = E]]
    operation valueOfB() -> Type = Crate[W = E]
  end

  -- A SORT-level clause: the member runs under `TypeTerm[T = E]` for its own instance.
  sort SHold
    import anthill.prelude.Type
    sort E = ?
    entity shold(e: E)
    requires TypeTerm[T = E]
    operation f() -> Type = TypeTerm.valueOf()
  end

  operation tagOfP[P](x: P) -> Type requires TypeTerm[T = P] = TypeTerm.valueOf()
  operation outer[Q](y: Q) -> Type requires TypeTerm[T = Q] = tagOfP(y)
  operation tagOfB[P](x: P) -> Type requires TypeTermB[T = P] = TypeTermB.valueOfB()
  operation twoReq[P, Q](x: P, y: Q) -> Type requires TypeTerm[T = P], TypeTerm[T = Q] =
    TypeTerm.valueOf()

  operation g[P](x: P) -> Type = Err2.tagOf(x)
  operation g2[Q](y: Q) -> Type = g(y)
  operation tagOp[T](x: T) -> Type = T
  operation gOp[P](x: P) -> Type = tagOp(x)
  operation gBox[P](x: P) -> Type = tagOp(box(x))
  operation gBox2[Q](y: Q) -> Type = gBox(y)
  operation gBoxS[P](x: P) -> Type = Err2.tagOf(box(x))
  operation tagExpr[P](x: P) -> Type = Box[V = P]
  operation noneInt() -> Option[T = Int64] = none()

  operation a1() -> Type = tagOfP(boom("x"))
  operation a2() -> Type = outer(boom("x"))
  operation a1s() -> Type = SHold[E = Boom].f()
  operation a1u() -> Type = SHold.f()
  operation a3() -> Type = g("s")
  operation a3b() -> Type = g2("s")
  operation b1() -> Type = gBox("s")
  operation b1b() -> Type = gBox2("s")
  operation b2() -> Type = gBoxS("s")
  operation c1() -> Type = tagOfB(box(boom("x")))
  operation c2() -> Type = tagOfB(crate(boom("x")))
  operation d1() -> Type = twoReq(boom("x"), boom("y"))
  operation k_mono() -> Type = Err2.tagOf(box("s"))
  operation k_none() -> Type = Err2.tagOf(noneInt())
  operation k_op() -> Type = gOp("s")
  operation k_recv() -> Type = Box[V = Boom].valueOfB()
  operation k_expr() -> Type = tagExpr("s")
end
"#;

fn eval(op: &str) -> Result<String, EvalError> {
    let mut interp = interp_for(SRC);
    match interp.call(&format!("test.r541x.{op}"), &[])? {
        Value::Term { id, .. } => Ok(TermPrinter::new(interp.kb()).print_term(id)),
        other => panic!("{op}: expected a term-carried type, got {other:?}"),
    }
}

fn eval_type(op: &str) -> String {
    eval(op).unwrap_or_else(|e| panic!("{op}: {e:?}"))
}

/// The (D) fault, and the parameter it names — a located fault, not merely "an error".
fn unbound_param(op: &str) -> String {
    match eval(op) {
        Err(EvalError::UnboundTypeParam { param, .. }) => param,
        other => panic!("{op}: expected UnboundTypeParam, got {other:?}"),
    }
}

// ── (A) ──────────────────────────────────────────────────────────────────────────────

/// THE HEADLINE ROW, and the shape a NOMINAL `ErrorTag` default needs
/// (WI-20260911-3MV2C): a spec's DEFAULT body reads the spec's own `T`, entered from a
/// scope that `requires TypeTerm[T = P]`. Before: `T`.
#[test]
fn a_spec_default_reads_the_requirement_it_runs_under() {
    assert_eq!(eval_type("a1"), "Boom");
}

/// …through TWO generic levels: `outer[Q]` pins `tagOfP`'s `P := Q`, which the caller's
/// frame grounds.
#[test]
fn the_requirement_reaches_through_two_generic_levels() {
    assert_eq!(eval_type("a2"), "Boom");
}

/// …and from a SORT-level clause, read at the RECEIVER's instance. Found by review: the
/// binder pinned `TypeTerm.T` to `SHold`'s rigid and the channel dropped it, so this was
/// refused where it should answer.
#[test]
fn a_sort_level_requirement_reaches_the_member() {
    assert_eq!(eval_type("a1s"), "Boom");
}

/// NO DICTIONARY ANYWHERE: `Err2.tagOf(x)` inside `g[P]` pins `Err2.T := P` from the
/// argument, and the channel entry is `g`'s own skolem. Before: skipped, answered `T`.
#[test]
fn a_generic_caller_grounds_a_sort_param_read() {
    assert_eq!(eval_type("a3"), "String");
}

#[test]
fn two_generic_levels_ground_a_sort_param_read() {
    assert_eq!(eval_type("a3b"), "String");
}

// ── (B) ──────────────────────────────────────────────────────────────────────────────

/// A skolem NESTED in a type application, on the operation-parameter loop. Before:
/// `Box(V: !P)`.
#[test]
fn a_nested_rigid_under_an_op_param_is_grounded() {
    assert_eq!(eval_type("b1"), "Box(V: String)");
    assert_eq!(eval_type("b1b"), "Box(V: String)");
}

/// …and on the sort-parameter loop, which needs (A)'s rewrite there as well.
#[test]
fn a_nested_rigid_under_a_sort_param_is_grounded() {
    assert_eq!(eval_type("b2"), "Box(V: String)");
}

// ── (C), asserted as (D)'s located fault ─────────────────────────────────────────────

/// A PROVIDER's member entered through the requirement slot: its frame never learns `V`
/// (a `Dictionary` carries no type bindings). NOT FIXED BY THIS TICKET — the direction is
/// undecided. Pinned as the located fault so the old silent `Box(V: V)` cannot return,
/// and so the fix that lands turns this row red on purpose.
#[test]
fn a_providers_own_param_is_a_located_fault_not_a_wrong_answer() {
    assert_eq!(unbound_param("c1"), "test.r541x.Box.V");
}

/// The WITNESS idiom (`DESC_INSTANCES`): `CrateTT.E` is derivable only from the spec's
/// `T`, and nothing derives it. Same status as the row above.
#[test]
fn a_witnesss_own_param_is_a_located_fault_not_a_wrong_answer() {
    assert_eq!(unbound_param("c2"), "test.r541x.CrateTT.E");
}

// ── (D) ──────────────────────────────────────────────────────────────────────────────

/// A fixture that STILL CANNOT BIND: two clauses over one spec, and no rule picks one, so
/// (A)'s binder takes neither. The body read is refused, naming the parameter and the
/// frame. Before (D): the silent `T`.
#[test]
fn two_clauses_over_one_spec_are_a_located_fault() {
    match eval("d1") {
        Err(EvalError::UnboundTypeParam { param, running }) => {
            assert_eq!(param, "test.r541x.TypeTerm.T");
            assert_eq!(running, "test.r541x.TypeTerm.valueOf");
        }
        other => panic!("expected UnboundTypeParam, got {other:?}"),
    }
}

/// (D)'s CHANNEL half: `SHold.f()` with no bracket says nothing about `E`, so `valueOf`'s
/// channel carries `Ref(SHold.E)` and the calling frame has nothing to ground it with.
/// The read is refused naming `SHold.E` — the parameter actually missing — rather than
/// delivering its name as a type.
#[test]
fn an_ungrounded_channel_value_is_a_located_fault() {
    assert_eq!(unbound_param("a1u"), "test.r541x.SHold.E");
}

// ── CONTROLS — green with or without every mechanism above ───────────────────────────

/// The monomorphic site: the argument pins `Err2.T` to a ground type.
#[test]
fn control_the_monomorphic_site() {
    assert_eq!(eval_type("k_mono"), "Box(V: String)");
}

/// The UNWITNESSED constructor: `none()` carries no `Int64` any value walk could recover —
/// the answer can only come from the type, and it does.
#[test]
fn control_the_unwitnessed_constructor() {
    assert_eq!(eval_type("k_none"), "Option(T: Int64)");
}

/// WI-708's whole-entry OPERATION parameter, the row this ticket's (A) extends to the
/// sort loop.
#[test]
fn control_wi708_whole_entry_op_param() {
    assert_eq!(eval_type("k_op"), "String");
}

/// WI-20260911-RS2G4's receiver bracket: the direct call to the provider's member, which
/// (C) cannot reach through a slot.
#[test]
fn control_rs2g4_receiver_bracket() {
    assert_eq!(eval_type("k_recv"), "Box(V: Boom)");
}

/// The same type written as an EXPRESSION, which never went through the channel.
#[test]
fn control_the_expression_form() {
    assert_eq!(eval_type("k_expr"), "Box(V: String)");
}

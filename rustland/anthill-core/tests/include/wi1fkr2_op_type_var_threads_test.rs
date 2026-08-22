//! WI-1FKR2 — AN OPERATION'S OWN TYPE VARIABLE MUST THREAD THROUGH A CALL WHEN THE CALLER
//! IS GENERIC IN IT, so a generic operation can be implemented in terms of another one.
//!
//! ## The root, and why the two reported symptoms are one
//!
//! §5.4 "Which variables the ∀ quantifies" says a variable written in a parameter type is
//! quantified — "an operation that writes no brackets at all still generalizes". The body
//! check skolemized only two of the three families that reach it (`rec.type_params` and the
//! enclosing sort's), so a variable the author wrote INLINE stayed a flexible `Var::Global`
//! in the body, and that one absence produced both reported failures:
//!
//! * NESTED (`operation via(b: Box[?t]) -> Box[?t] = id(b)`) — a flexible variable is what
//!   [`SlotPosition::written_slot_is_unwritten`]'s body answer reads as an UNWRITTEN slot,
//!   so `rigidify_unwritten_sort_params` overwrote the author's `?t` with the projection
//!   `b.T`. The parameter and the return then named different things: `expected Box[T = ?t],
//!   got Box[T = b.T]`. That predicate's own doc states the premise the fix restores —
//!   "by then … nothing else is left flexible".
//! * BARE (`operation via_bare(x: ?t) -> ?t = idv(x)`) — nothing rewrites a top-level
//!   variable, so the two sides stayed two distinct flexible Globals, which
//!   `types_compatible` has no arm for at all: `expected ?t, got ?t`, the two rendering
//!   alike because the difference was the `VarId`.
//!
//! ## Which rows measure the fix
//!
//! MEASURED, by backing the fix out AS A MUTATION (`inline_signature_type_params` returning
//! `Vec::new()`, which leaves every declaration present and only stops the skolemization):
//! SIX rows fail — the three `threads_` rows, `a_threaded_label_is_still_enforced_at_the_sink`,
//! `the_measurement_file_loads`, and `refuses_a_body_that_pins_the_callers_own_variable`. The
//! last of those fails the OTHER way — it loads clean without the fix, which is the
//! unsoundness the universal quantifier exists to stop and the reason this is a soundness fix
//! and not only an expressiveness one. The remaining four pass either way.
//!
//! Every `control_` row passes either way BY DESIGN, and each pins a different accept the
//! fix must not take away: the GROUND caller (which is what makes the failures about the
//! caller's polymorphism and not about delegation), the direct identity body (which passed
//! before only because both sides were literally one `TermId`), the anonymous / omitted
//! slot, which must keep taking `UnwrittenFill::Projection`'s `b.T` rather than a skolem —
//! that is the WI-1059 design and the reason this fix excludes anonymous variables — and
//! the label enforced through a BODY-LESS middle, which is the sink half of the flow rows
//! said without any body check in it. `refuses_returning_a_different_variable` also passes
//! either way and pins the obvious over-correction: skolemizing must not make two DIFFERENT
//! variables one.
//!
//! Each row is its OWN namespace in its OWN load, so a back-out that breaks an arm cannot
//! take a control down with it.
//!
//! ## What is NOT here
//!
//! `types_compatible` still has no variable arm — the bare case is fixed by making both
//! sides one `TermId`, not by teaching the subtype relation about variables. That is the
//! WI-1063 polarity design: a parameter's variable is rigid in the body and a return-only
//! one is opened per call, so a variable is meant to be determined by the time it reaches
//! the relation. No row here asserts otherwise.

use super::common::{interp_for, try_load_kb_with};
use anthill_core::eval::Value;

fn errors(src: &str) -> Vec<String> {
    match try_load_kb_with(src) {
        Ok(_) => Vec::new(),
        Err(e) => e,
    }
}

fn loads_clean(src: &str) {
    let errs = errors(src);
    assert!(errs.is_empty(), "expected a clean load, got: {errs:#?}");
}

fn sole_error(src: &str) -> String {
    let errs = errors(src);
    assert_eq!(errs.len(), 1, "expected exactly one error, got: {errs:#?}");
    errs.into_iter().next().unwrap()
}

/// A one-parameter carrier whose parameter is carried by a FIELD, so a row can drive the
/// value through as well as load it.
fn box_sort(ns: &str) -> String {
    format!(
        "enum {ns}.Box
  sort T = ?
  entity box(v: T)
end
"
    )
}

fn int_of(v: &Value) -> i64 {
    match v {
        Value::Int(i) => *i,
        other => panic!("expected an Int64, got {other:?}"),
    }
}

// ── the arms: a caller generic in its own variable ───────────────────────────

/// CASE 1 of the ticket, DRIVEN. `via_bare` promises exactly what `idv` promises and its
/// body is exactly `idv(x)`; the value is carried through and asserted, so the row cannot
/// go green on a declaration that resolves to nothing. FAILS ON BACK-OUT at
/// `via_bare.return (op-return): expected ?t, got ?t`.
#[test]
fn threads_a_bare_type_variable_through_a_call() {
    let src = "namespace tv_bare
  import anthill.prelude.{Int64}
  operation idv(x: ?t) -> ?t = x
  operation via_bare(x: ?t) -> ?t = idv(x)
  operation run() -> Int64 = via_bare(7)
end
";
    let mut interp = interp_for(src);
    let got = interp.call("tv_bare.run", &[]).expect("run evaluates");
    assert_eq!(int_of(&got), 7, "the value must thread through too");
}

/// CASE 2 of the ticket, DRIVEN. The variable NESTED in a sort application — the form whose
/// diagnostic named the mechanism (`got Box[T = b.T]`, the projection standing in for the
/// caller's own variable). FAILS ON BACK-OUT at `via.return (op-return): expected
/// Box[T = ?t], got Box[T = b.T]`.
#[test]
fn threads_a_nested_type_variable_through_a_call() {
    let src = format!(
        "{}namespace tv_nested
  import anthill.prelude.{{Int64}}
  import tv_nested.{{Box}}
  operation id(b: Box[?t]) -> Box[?t] = b
  operation via(b: Box[?t]) -> Box[?t] = id(b)
  operation run() -> Int64 = via(box(v: 3)).v
end
",
        box_sort("tv_nested")
    );
    let mut interp = interp_for(&src);
    let got = interp.call("tv_nested.run", &[]).expect("run evaluates");
    assert_eq!(int_of(&got), 3);
}

/// WHY IT MATTERS BEYOND GENERICS FOR THEIR OWN SAKE — the shape `examples/guardians` is
/// built from: an information-flow label lives in a type parameter, and a LIBRARY operation
/// in the middle of a pipeline is itself label-preserving and delegates to another one.
/// That middle operation is what could not be written; the property composed through the
/// type checker but not through user-written library code.
///
/// FAILS ON BACK-OUT at `summarize.return (op-return): expected Text[L = ?l], got
/// Text[L = t.L]` — the middle operation alone. What that middle must still ENFORCE is the
/// next row; what it enforces with no body check in play is
/// `control_a_label_is_enforced_through_a_body_less_middle`.
#[test]
fn threads_a_label_through_a_label_preserving_library_operation() {
    loads_clean(&label_program(
        "flow_ok",
        "  operation upcase(t: Text[L = ?l]) -> Text[L = ?l]
  operation summarize(t: Text[L = ?l]) -> Text[L = ?l] = upcase(t)",
    ));
}

/// The other half of the row above, and an ARM rather than a control because the middle
/// operation it needs is itself the arm: threading the label must not WEAKEN it. `send`
/// takes `Public` only, so an `Untrusted` text through the now-loadable middle is still
/// refused, and a `Public` one still passes. FAILS ON BACK-OUT — `summarize`'s own return
/// error joins the sink's, so the refusal is no longer the SOLE error and the permitted
/// flow no longer loads clean. What the fix must not do is buy the middle operation by
/// erasing what it carries; that is what these two assertions say and why they are worth
/// a row of their own. The back-out-independent form of the same claim is
/// `control_a_label_is_enforced_through_a_body_less_middle`.
#[test]
fn a_threaded_label_is_still_enforced_at_the_sink() {
    let err = sole_error(&label_program(
        "flow_leak",
        "  operation upcase(t: Text[L = ?l]) -> Text[L = ?l]
  operation summarize(t: Text[L = ?l]) -> Text[L = ?l] = upcase(t)
  operation send(body: Text[L = Public]) -> Unit
  operation leak(t: Text[L = Untrusted]) -> Unit = send(summarize(t))",
    ));
    assert!(
        err.contains("type mismatch in send.body (op-arg)")
            && err.contains("expected Text[L = Public]")
            && err.contains("got Text[L = Untrusted]"),
        "{err}"
    );
    loads_clean(&label_program(
        "flow_pub",
        "  operation upcase(t: Text[L = ?l]) -> Text[L = ?l]
  operation summarize(t: Text[L = ?l]) -> Text[L = ?l] = upcase(t)
  operation send(body: Text[L = Public]) -> Unit
  operation ok(t: Text[L = Public]) -> Unit = send(summarize(t))",
    ));
}

/// Passes either way BY DESIGN, and it is the row that keeps the arm above honest: the SAME
/// two flows through a BODY-LESS label-preserving middle, which never reaches the body check
/// at all. So "the label is enforced at the sink" is pinned independently of anything this
/// ticket changed — if the arm above ever went green by weakening the label rather than by
/// threading it, this row would say so.
#[test]
fn control_a_label_is_enforced_through_a_body_less_middle() {
    let err = sole_error(&label_program(
        "flow_spec_leak",
        "  operation summarize(t: Text[L = ?l]) -> Text[L = ?l]
  operation send(body: Text[L = Public]) -> Unit
  operation leak(t: Text[L = Untrusted]) -> Unit = send(summarize(t))",
    ));
    assert!(
        err.contains("type mismatch in send.body (op-arg)")
            && err.contains("expected Text[L = Public]")
            && err.contains("got Text[L = Untrusted]"),
        "{err}"
    );
    loads_clean(&label_program(
        "flow_spec_pub",
        "  operation summarize(t: Text[L = ?l]) -> Text[L = ?l]
  operation send(body: Text[L = Public]) -> Unit
  operation ok(t: Text[L = Public]) -> Unit = send(summarize(t))",
    ));
}

fn label_program(ns: &str, body: &str) -> String {
    format!(
        "enum {ns}.Trust
  entity Untrusted
  entity Public
end
enum {ns}.Text
  import anthill.prelude.{{String}}
  sort L = ?
  entity text(raw: String)
end
namespace {ns}
  import anthill.prelude.{{String, Unit}}
  import {ns}.Trust.{{Untrusted, Public}}
  import {ns}.{{Text}}
{body}
end
"
    )
}

// ── the soundness the skolemization buys ─────────────────────────────────────

/// FAILS ON BACK-OUT THE OTHER WAY: without the fix this LOADS CLEAN. `leaky` declares it
/// takes any `?t` and its body hands that value to an `Int64` parameter — the body pinned
/// the caller's universally-quantified variable, which is exactly what WI-392's rigid
/// forbids for a declared `[T]` and what the third family was escaping. The return type is
/// `Int64` on both sides, so nothing downstream re-asked the question.
#[test]
fn refuses_a_body_that_pins_the_callers_own_variable() {
    let err = sole_error(
        "namespace tv_pin
  import anthill.prelude.{Int64}
  operation sink(n: Int64) -> Int64
  operation leaky(x: ?t) -> Int64 = sink(x)
end
",
    );
    assert!(
        err.contains("type mismatch in sink.n (op-arg)")
            && err.contains("expected Int64")
            && err.contains("got ?t"),
        "{err}"
    );
}

/// Passes either way BY DESIGN — it pins the obvious over-correction. Two variables the
/// author wrote APART must stay apart: skolemizing them must give two distinct rigids, not
/// one. Before the fix this was refused because `types_compatible` refuses every variable
/// pair; after, because a rigid equals only itself.
#[test]
fn refuses_returning_a_different_variable() {
    let err = sole_error(
        "namespace tv_swap
  operation swap(a: ?u, b: ?v) -> ?u = b
end
",
    );
    assert!(
        err.contains("type mismatch in swap.return (op-return)")
            && err.contains("expected ?u")
            && err.contains("got ?v"),
        "{err}"
    );
}

// ── the controls ─────────────────────────────────────────────────────────────

/// THE TICKET'S OWN CONTROL, and the row that makes the two failures mean something: the
/// IDENTICAL delegation with a GROUND caller. So the failure was about the caller's
/// polymorphism — not about delegation, not arity, not the sort. Passes either way.
#[test]
fn control_a_ground_caller_delegates_the_same_way() {
    let src = format!(
        "{}namespace tv_ground
  import anthill.prelude.{{Int64}}
  import tv_ground.{{Box}}
  operation id(b: Box[?t]) -> Box[?t]
  operation via_ground(b: Box[T = Int64]) -> Box[T = Int64] = id(b)
end
",
        box_sort("tv_ground")
    );
    loads_clean(&src);
}

/// Passes either way, and for a reason worth naming: before the fix it passed only because
/// the declared return and the body's type were literally ONE `TermId` (the parser shares a
/// named variable across an operation's signature), so `types_compatible`'s identity
/// fast-path answered before its missing variable arm could. Anything that made the body
/// COMPUTE the type — the arm rows above — fell off that path.
#[test]
fn control_a_direct_identity_body_loads() {
    loads_clean(
        "namespace tv_direct
  operation via_id(x: ?t) -> ?t = x
end
",
    );
}

/// THE ANONYMOUS SLOT IS NOT A NAMED VARIABLE, and this is the accept the fix's anonymous
/// exclusion protects: `?` names nothing and ties nothing, so it stays the unwritten slot
/// §"Expansion during unification" describes and keeps taking
/// `UnwrittenFill::Projection`'s `b.T` — which is what a `-> b.T` return then resolves
/// against. Both spellings, omitted and written `?`, must agree.
///
/// SAID HONESTLY: this row does NOT discriminate the exclusion. Rigidifying anonymous
/// variables too leaves it green (the return projects the same receiver, so both sides move
/// together) and leaves all 194 corpus files unchanged. The exclusion is kept on the WI-1059
/// argument — a fresh var in place of the projection cost 27 stdlib load errors when that
/// ticket measured it — not on a fixture. What this row does pin is that the projection path
/// still works at all under the fix.
#[test]
fn control_an_anonymous_slot_still_takes_the_projection() {
    let src = format!(
        "{}namespace tv_anon
  import tv_anon.{{Box}}
  operation peel(b: Box) -> b.T
  operation peel_anon(b: Box[T = ?]) -> b.T
  operation via(b: Box) -> b.T = peel(b)
  operation via_anon(b: Box[T = ?]) -> b.T = peel_anon(b)
end
",
        box_sort("tv_anon")
    );
    loads_clean(&src);
}

/// The ticket's minimal reproduction file, loaded as the file. It carries both arms and the
/// ground control in one program, which is how the defect was reported; the rows above are
/// what keep a back-out's blast radius readable.
#[test]
fn the_measurement_file_loads() {
    let path = super::common::workspace_root()
        .join("docs/measurements/op-type-var-does-not-thread.anthill");
    let src = std::fs::read_to_string(&path).expect("measurement file readable");
    loads_clean(&src);
}

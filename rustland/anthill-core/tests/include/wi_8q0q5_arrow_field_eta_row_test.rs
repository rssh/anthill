//! WI-20260828-8Q0Q5 — an ARROW-typed ENTITY FIELD fed a BARE OPERATION NAME must
//! bind the arrow's EFFECT ROW.
//!
//! A constructor field declared `fn: (Int64) -> Int64 @ {R}` names a row PARAMETER.
//! Supplying a named operation there should bind `R` to that operation's own declared
//! row, exactly as supplying it to an operation PARAMETER of the same type does. It
//! did not: the row escaped the construction unbound and surfaced at the constructing
//! operation as `undeclared effect ?_`.
//!
//! ROOT CAUSE. The constructor-argument hint push-down looks `entity_field_types` up
//! only when some argument is a CALL, a TUPLE, a SORT NAME or a CONSTRUCTOR
//! APPLICATION. A bare name is none of those, so no hint was computed, the argument
//! was typed with NO expected type, and `check_bare_ref` had no arrow to eta-lift
//! against — the operation's declared row never met the field's row parameter. The
//! hint IS the child's expected type (`push_visit(work, arg, env, hint, fuel)`), which
//! is why the operation-parameter path was always fine. `arrow_slot_arg_hint` is the
//! fifth hint kind, gated on the argument being a bare operation name AND the field
//! being callable by head.
//!
//! WHY THE SUITE WAS BLIND. The stdlib never writes this shape: its combinators are
//! built from INSIDE `Iterable.map` / `FiniteCollection.map`, whose `f` is an
//! operation PARAMETER carrying its row from the call site. The shape only appears
//! when a free operation constructs a combinator by hand — which is what surfaced it,
//! while probing why `mapped(xs, inc)` did not type-check outside the stdlib.
//!
//! CONTAINMENT, argued AND measured. Widening the `field_types` gate means more builds
//! compute the table, so the four older hints could in principle newly fire. They cannot:
//! each one's first statement is a gate on the ARGUMENT's shape — a call
//! (`nested_call_arg_hint`), a sort name (`type_slot_arg_hint`), a constructor
//! application (`variant_slot_arg_hint`, `variant_field_expected_from_ctor`) — and a bare
//! name is none of those. Measured alongside: with the gate neutralised, the only verdict
//! in this file that changes is the defect row's.
//!
//! WHAT THIS FILE DOES NOT PIN, because it is a SEPARATE pre-existing hole: a bare
//! operation name supplied to a NON-callable field (`entity plain(v: Int64)` fed
//! `plain(inc)`) loads CLEAN, and it does so identically with this change and with it
//! backed out — so it is neither caused nor fixed here. Filed on its own; a row asserting
//! today's acceptance would pin laxity as intended behaviour and go red on its repair.
//!
//! HOW EACH ROW EARNS ITS PLACE. `entity_field_binds_the_ops_row` is the only row that
//! FAILS when `arrow_slot_arg_hint` is backed out (measured). The three rows after it
//! pass either way BY DESIGN and are what make the first one an experiment about the
//! FIELD PATH rather than about eta-lift or about arrows: each changes exactly one
//! thing and was already green. The last row is the over-widening guard.

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;

/// Load stdlib + `extra` in ONE `load_all` and return the errors (empty when clean).
/// The whole-KB passes — op-body type checking among them — belong to `load_all`, so
/// a second incremental `load` would not be the loader's verdict on this source.
fn errors_for(extra: &str) -> Vec<String> {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => Vec::new(),
        Err(errs) => errs.iter().map(|e| e.to_string()).collect(),
    }
}

/// The carrier every row below shares: ONE arrow field whose row is a sort parameter,
/// and a consumer that declares exactly that row. `{ARG}` is the only text that varies.
const CARRIER: &str = r#"
namespace wi8q0q5.{NS}
  import anthill.prelude.{Int64, Function, EffectsRuntime}

  sort Holder
    import anthill.prelude.{Int64, Function, EffectsRuntime}
    effects R = ?
    entity held(fn: (Int64) -> Int64 @ {R})
    operation run(h: Holder) -> Int64 effects R =
      match h
        case held(f) -> f(1)
  end

  operation inc(x: Int64) -> Int64 = x + 1
{BODY}
end
"#;

fn load_body(ns: &str, body: &str) -> Vec<String> {
    errors_for(&CARRIER.replace("{NS}", ns).replace("{BODY}", body))
}

/// THE DEFECT. A bare operation name in the arrow field: `R` must bind to `inc`'s own
/// (pure) row, so the constructing operation is pure and its `effects` clause — which
/// says nothing, i.e. `{}` — holds.
///
/// BACKED OUT (drop `arrow_slot_arg_hint` from the two hint chains, or drop
/// `has_op_name_field` from the `field_types` gate): this row FAILS with
/// `type mismatch in probe.effects (op-effects): expected declared: [], got undeclared
/// effect: ?_`. It is the ONLY row in this file that does.
#[test]
fn entity_field_binds_the_ops_row() {
    let errs = load_body(
        "defect",
        "  operation probe() -> Int64 = Holder.run(held(inc))",
    );
    assert!(
        errs.is_empty(),
        "a bare operation name in an arrow-typed FIELD must bind the field's row \
         parameter to the operation's own row; got: {errs:?}"
    );
}

/// CONTROL — the same eta-lifted operation into an OPERATION PARAMETER arrow slot
/// carrying the same row parameter. Passes either way BY DESIGN: that path already
/// pushed its declared parameter type down as the argument's expected type. It is what
/// makes the row above an experiment about the FIELD path and not about eta-lift.
#[test]
fn operation_parameter_arrow_slot_was_always_fine() {
    let errs = load_body(
        "param",
        "  operation take[Q](f: (Int64) -> Int64 @ {Q}) -> Int64 effects Q = f(1)\n  \
         operation probe() -> Int64 = take(inc)",
    );
    assert!(
        errs.is_empty(),
        "the operation-parameter control must be green either way; got: {errs:?}"
    );
}

/// CONTROL — an INLINE LAMBDA in the very same FIELD slot. Passes either way BY
/// DESIGN: a lambda is typed from its own text and never needed the hint. It is what
/// makes the defect row an experiment about the bare-NAME reading and not about arrows
/// or about entity fields in general.
#[test]
fn an_inline_lambda_in_the_same_field_was_always_fine() {
    let errs = load_body(
        "lambda",
        "  operation probe() -> Int64 = Holder.run(held(lambda x -> x + 1))",
    );
    assert!(
        errs.is_empty(),
        "the lambda control must be green either way; got: {errs:?}"
    );
}

/// CONTROL — the workaround that existed before the fix: route the construction
/// through an operation whose declared RETURN pins the row. Passes either way BY
/// DESIGN, and is kept so the fix cannot silently take the workaround away with it.
#[test]
fn a_declared_return_still_pins_the_row() {
    let errs = load_body(
        "pinned",
        "  operation mk() -> Holder[R = {}] = held(inc)\n  \
         operation probe() -> Int64 = Holder.run(mk())",
    );
    assert!(
        errs.is_empty(),
        "pinning the row at a declared return must keep working; got: {errs:?}"
    );
}

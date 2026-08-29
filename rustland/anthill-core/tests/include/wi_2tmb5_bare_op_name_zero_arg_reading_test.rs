//! WI-20260828-2TMB5 — a BARE NON-NULLARY OPERATION NAME may not take the
//! ZERO-ARG-CALL reading.
//!
//! THE DEFECT. `check_bare_ref` gives a bare operation name two readings: the ETA lift
//! (the operation as a function value) and the ZERO-ARG CALL (the operation's return
//! type). The eta arm fires only where an ARROW is expected; everything else fell
//! through to the return type — and that fall-through was never gated on the operation
//! actually being NULLARY. So `entity plain(v: Int64)` fed `plain(inc)`, where `inc(x:
//! Int64) -> Int64`, typed `inc` as `Int64`, which is exactly the declared field type:
//! the WI-385 field validation had nothing to object to and the program loaded CLEAN.
//! The APPLIED spelling of the same reading, `plain(inc())`, is an arity error. The
//! bare one skipped the arity check by never being routed through a call.
//!
//! THE HINT IS NOT THE HOLE, which is worth stating because WI-8Q0Q5 had just widened
//! the constructor-argument hint push-down for the neighbouring arrow-field case.
//! `arrow_slot_arg_hint` is gated on `type_head_is_callable`, and `Int64` is not
//! callable, so no hint is computed and the argument is typed with `expected = None` —
//! MEASURED. A repair that only refused a bare name against a KNOWN non-arrow expected
//! type would not have touched the ticket's own program.
//!
//! THE FIX is at the arm itself: a NON-NULLARY bare name reaching the zero-arg-call
//! reading denotes NOTHING and is refused there, naming the operation. Non-nullary is the
//! whole gate — a nullary name keeps both readings and the existing arrow-slot rule
//! (WI-700's `eta_shadows_return_type`) keeps arbitrating them.
//!
//! LIFTING INSTEAD WAS THE FIRST CUT, AND IT WAS UNSOUND. Reaching this arm means there is
//! no arrow to lift AGAINST — the WI-275 arm above returns whenever `expected` is an arrow
//! and the operation has a function-value form. The first cut lifted anyway, pinning the
//! dictionary against the operation's own arrow, which pins nothing:
//! `attach_eta_dispatch_dict` reads the expected arrow for BOTH the requirement dictionary
//! and the argument-spread labels. `via_option(some(sub2))` then returned **-7** where its
//! arrow-slot twin returned 7 — see
//! [`the_polymorphic_slot_is_refused_and_the_arrow_slot_still_runs`], which holds that
//! measurement. On main the same program is a load error, so the lift was not a capability;
//! it was a correct refusal turned into a wrong answer.
//!
//! THE THIRD VISIT TO THIS FALL-THROUGH. WI-1063 found it laundering an existential
//! return (`takes_pure(mk)` clean where `takes_pure(mk())` was refused); WI-1083 found
//! it laundering a ∀ (a bare `idp[A](x: A) -> A` typing as a flexible `?A` that unifies
//! with anything). Both repaired the arm ABOVE so that fewer references reached this
//! one. This repairs the arm ITSELF.
//!
//! WHAT NOTHING HERE COVERS, said rather than credited to a neighbour: the repair reads
//! the operation record through `lookup_operation_info_full`, a DIFFERENT reader of the
//! `OperationInfo` facts from the `lookup_operation_return_type` whose arm it guards — it
//! decodes a whole signature, through a cache tier the other has not got. The two
//! disagreeing is what the third arm of the gate refuses, and no fixture in this workspace
//! produces that disagreement, so that arm is written and never driven. It is a loud error
//! rather than a fall-through precisely because it cannot be tested: a silent default to
//! either reading would be the fail-open this ticket is about, minted fresh.
//!
//! TWO NEIGHBOURING TESTS MOVED WITH THIS, both repairs rather than concessions.
//! `wi1078`'s `the_bare_nullary_name_and_the_eta_lift_open_it_too` wrote an
//! `apply_it(f: Function[…])` slot in a fixture whose preamble never imported `Function`,
//! so the "eta slot" was not an arrow and the row was passing on the zero-arg-call
//! reading's refusal; the import is added and it now measures the lift it names.
//! `wi836`'s `a_callback_slot_nested_in_a_sort_application_still_withholds` needed an argument
//! typed `List[T = Int64]` against a `List[T = Function[…]]` slot, and got its `Int64` from
//! the very reading removed here — the literal `1` reaches the identical comparison owing
//! nothing to the bare-name path, and was measured under a head-only-degraded
//! `type_contains_callable` to confirm it still detects what that row exists to detect.
//!
//! THE POPULATION, CENSUSED rather than guessed. With a probe on the zero-arg-call arm,
//! the WHOLE workspace reaches it with a non-nullary operation exactly FIVE
//! times, and every one is a row below: `is_big` under an unknown dot head, `sub2` into
//! a `List`/`Option` field ×2, `widen_named` into an eta slot, and `as_term` — the one
//! body-less case. That is why this file's rows are these rows.

use crate::common::{interp_for, try_load_kb_with};

/// The load errors of `src` (empty when it loads clean).
fn errs(src: &str) -> Vec<String> {
    try_load_kb_with(src).err().unwrap_or_default()
}

/// Assert `src` is refused by a diagnostic containing every needle. Asserting on the
/// MESSAGE, not merely on the refusal: the defect was a check that reported NOTHING, and
/// a count-only assertion would pass on a fix that rejected the program for an unrelated
/// reason.
fn assert_refused_with(src: &str, needles: &[&str], why: &str) {
    let es = errs(src);
    assert!(!es.is_empty(), "must NOT load: {why}");
    assert!(
        es.iter().any(|e| needles.iter().all(|n| e.contains(n))),
        "{why}; got: {es:?}",
    );
}

/// The ticket's own program, to the token. One entity with ONE non-callable field, one
/// unary operation, and the constructor fed the operation's bare name.
const PLAIN: &str = r#"
namespace wi2tmb5.field
  import anthill.prelude.{Int64, String}
  sort Plain
    import anthill.prelude.{Int64, String}
    entity plain(v: Int64)
  end
  operation inc(x: Int64) -> Int64 = x + 1
  operation probe() -> Plain = plain(ARG)
end
"#;

fn plain(arg: &str) -> String {
    PLAIN.replace("ARG", arg)
}

/// THE DEFECT, positional spelling. An operation name is not an `Int64` by any relation,
/// and the eta arrow `Int64 -> Int64` is not the declared field type either.
///
/// BACKED OUT (delete the non-nullary arm from `check_bare_ref`, so control falls to the
/// zero-arg-call reading): this row FAILS — the program loads with NO errors at all,
/// which is the ticket's measurement.
#[test]
fn a_bare_op_name_in_a_non_callable_field_is_refused() {
    assert_refused_with(
        &plain("inc"),
        &["inc", "no function type to lift it against"],
        "a bare operation name in an Int64 field must be refused at the reference",
    );
}

/// THE DEFECT, NAMED-ARG spelling. The same hole reached down the OTHER of the two hint
/// chains (`named_hints` beside `pos_hints`), and a repair wired into only one of them
/// would leave this green-and-wrong. Measured lax before the fix, exactly as the
/// positional row was.
///
/// BACKED OUT: FAILS, same as the row above — the program loads clean.
#[test]
fn the_named_arg_spelling_is_refused_too() {
    assert_refused_with(
        &plain("v: inc"),
        &["inc", "no function type to lift it against"],
        "the named-argument spelling must be refused identically",
    );
}

/// THE DEFECT IS NOT THE FIELD PATH — the ticket framed it as a constructor-field hole,
/// and the census says an ordinary OPERATION PARAMETER has it too. This row is why the
/// repair sits in `check_bare_ref` rather than in the constructor hint chain: one arm
/// serves both positions.
///
/// BACKED OUT: FAILS — `take(inc)` loads clean with `v: Int64`.
#[test]
fn a_non_callable_operation_parameter_has_the_same_hole() {
    assert_refused_with(
        r#"
namespace wi2tmb5.param
  import anthill.prelude.Int64
  operation inc(x: Int64) -> Int64 = x + 1
  operation take(v: Int64) -> Int64 = v
  operation probe() -> Int64 = take(inc)
end
"#,
        &["inc", "no function type to lift it against"],
        "a bare operation name in a non-callable operation PARAMETER must be refused",
    );
}

/// A BODY-LESS operation has NEITHER reading: `operation_as_function_value` refuses to
/// eta-lift it (the typer's accepted set must stay a subset of the evaluator's — a
/// builtin has no `Value::OpRef` form), and the zero-arg-call reading is now gone too.
/// It used to be caught only where the return type HAPPENED not to conform:
/// `my_map([1,2,3], as_term)` was refused because `Term` is not a `Function`, and would
/// have loaded clean had `as_term` returned one. Now the reference itself is the error.
///
/// BACKED OUT: this row FAILS on the MESSAGE, not on the refusal — the program is still
/// rejected, but by the accidental `Term`-is-not-a-`Function` mismatch downstream rather
/// than by anything naming `as_term`. That difference is the whole point of asserting the
/// operation's name here.
#[test]
fn a_body_less_builtin_in_an_arrow_slot_names_itself() {
    assert_refused_with(
        r#"
namespace wi2tmb5.builtin
  import anthill.prelude.{List, Int64, Function}
  import anthill.reflect.{Term, as_term}
  operation my_map(xs: List[T = Int64], f: Function[Int64, Term]) -> List[T = Term] =
    match xs
      case nil() -> nil()
      case cons(h, t) -> cons(f(h), my_map(t, f))
  operation go() -> List[T = Term] = my_map([1, 2, 3], as_term)
end
"#,
        &["as_term", "carries no body"],
        "a body-less builtin in an arrow slot must be refused AT THE REFERENCE, naming \
         the operation",
    );
}

/// The same body-less operation where NOTHING is expected — a polymorphic field. This is
/// the row the old behaviour was silently WRONG on rather than accidentally right: with
/// no expected type there was no downstream mismatch to catch it, so `some(as_term)`
/// loaded clean carrying the type `Option[T = Term]` for a value that has no runtime form
/// at all.
///
/// BACKED OUT: FAILS — the program loads with no errors.
#[test]
fn a_body_less_builtin_with_no_expected_type_is_refused() {
    assert_refused_with(
        r#"
namespace wi2tmb5.builtinbare
  import anthill.prelude.{Option, Int64, some}
  import anthill.reflect.{Term, as_term}
  operation go() -> Option[T = Term] = some(as_term)
end
"#,
        &["as_term", "carries no body"],
        "a body-less builtin with no expected type must be refused, not typed as its \
         return type",
    );
}

/// THE ROW THAT DECIDED THE SHAPE OF THE FIX, and it is DRIVEN. This ticket's first cut
/// did the opposite of the refusal above: with no arrow to lift against it lifted anyway
/// and pinned the dispatch dictionary against the operation's OWN arrow. That looked like a
/// capability and was a soundness hole — `attach_eta_dispatch_dict` reads the expected
/// arrow to pin BOTH the requirement dictionary and the argument-spread labels
/// (`function_slot_spread_labels`, WI-1087), and an arrow unified with ITSELF pins neither.
///
/// The two halves are the same operation, the same declared slot and the same applied
/// tuple, differing only in whether the callback arrives through an ARROW parameter or
/// through a POLYMORPHIC one. THEY MUST AGREE, and that is the whole row. Under the first
/// cut they did not: `direct` returned 7 and `via_option` returned **-7**, the labels having
/// gone unpinned so eval spread `(acc: 3, x: 10)` by source order.
///
/// WI-20260828-5NSZY MADE THE SECOND HALF WORK RATHER THAN REFUSING IT, which is why this
/// row now drives both. When 2TMB5 shipped, the arrow the author had written one level out
/// (`Option[T = Function[…]]`) could not reach the name — an op-call argument that is a
/// constructor application was handed no expected type unless its parameter type named an
/// ENTITY — so the honest answer was to refuse. 5NSZY delivers the arrow instead, through
/// `ctor_arg_unlocks_an_arrow_for_a_bare_name` plus `arrow_field_expected_from_ctor`, and
/// the reference then takes the ordinary WI-275 path with its dictionary and labels pinned
/// from the slot. Both halves return 7.
///
/// THE POINT IS THE AGREEMENT, not the number. `7` and `-7` are the two orderings of the
/// same subtraction, so a row asserting only `direct` would pass under the first cut, and a
/// row asserting only `via_option` would pass on a fix that spread positionally in BOTH.
/// Only the pair separates "the labels are pinned" from "the labels happen to match source
/// order", which is why the tuple is written `(acc: 3, x: 10)` — in the OTHER order from the
/// parameter list, so source order gives the wrong answer.
///
/// BACKED OUT (2TMB5's gate): both halves still return 7 — that gate is not what makes this
/// work, and this row is a control for it rather than a measurement of it. BACKED OUT
/// (5NSZY's two hints, either one): `via_option` is REFUSED at the reference, naming `sub2`.
/// Under the abandoned first cut of 2TMB5: `via_option` returns -7.
#[test]
fn the_arrow_slot_and_the_polymorphic_slot_agree() {
    const DIRECT: &str = r#"
namespace wi2tmb5.arrowslot
  import anthill.prelude.{Int64, Function}
  operation sub2(x: Int64, acc: Int64) -> Int64 = x - acc
  operation direct(g: Function[A = (x: Int64, acc: Int64), B = Int64]) -> Int64 =
    g((acc: 3, x: 10))
  operation drive() -> Int64 = direct(sub2)
end
"#;
    const VIA: &str = r#"
namespace wi2tmb5.polyslot
  import anthill.prelude.{Option, Int64, Function, some, none}
  operation sub2(x: Int64, acc: Int64) -> Int64 = x - acc
  operation via_option(o: Option[T = Function[A = (x: Int64, acc: Int64), B = Int64]])
      -> Int64 =
    match o
      case none() -> 0
      case some(g) -> g((acc: 3, x: 10))
  operation drive() -> Int64 = via_option(some(sub2))
end
"#;
    // SEPARATE PROGRAMS on purpose: a load error anywhere in a file is reported for every
    // operation in it, so one namespace holding both halves cannot say which half failed.
    for (src, op, which) in [
        (DIRECT, "wi2tmb5.arrowslot.drive", "the ARROW slot"),
        (VIA, "wi2tmb5.polyslot.drive", "the POLYMORPHIC slot"),
    ] {
        match interp_for(src).call(op, &[]).unwrap_or_else(|e| panic!("call {op}: {e:?}")) {
            anthill_core::eval::Value::Int(i) => assert_eq!(
                i, 7,
                "{which} must spread `(acc: 3, x: 10)` into `sub2(x, acc)` BY LABEL; \
                 -7 means the labels went unpinned and eval used source order",
            ),
            other => panic!("call {op}: expected Int, got {other:?}"),
        }
    }
}

/// CONTROL — a NULLARY operation keeps the zero-arg-call reading. Passes either way BY
/// DESIGN, and it is the boundary the fix must not cross: `total()` in an `Int64` slot
/// denotes its RESULT, which is the reading the whole language relies on
/// (`operation main() -> Int64 = total` is a call, not a function value). The gate is
/// `operation_is_nullary`, so this row is the direct control on it.
#[test]
fn a_nullary_bare_name_still_denotes_its_result() {
    let src = r#"
namespace wi2tmb5.nullary
  import anthill.prelude.Int64
  operation total() -> Int64 = 42
  operation drive() -> Int64 = total
end
"#;
    match interp_for(src)
        .call("wi2tmb5.nullary.drive", &[])
        .expect("call drive")
    {
        anthill_core::eval::Value::Int(i) => assert_eq!(i, 42),
        other => panic!("expected Int, got {other:?}"),
    }
}

/// CONTROL — the INLINE LAMBDA twin of the headline row. Passes either way BY DESIGN: a
/// lambda is typed from its own text and never took the zero-arg-call reading. It is
/// kept because it is the message the headline row now MATCHES — the fix is "hand the
/// existing field check the type the author wrote", and this row is the existing check
/// working, so a regression in it would mean the two spellings had drifted apart again.
#[test]
fn the_inline_lambda_twin_was_always_refused() {
    assert_refused_with(
        // The IDENTITY lambda, not `lambda x -> x + 1`: with a non-callable field there
        // is no arrow to hint the binder from, so `+` on an unpinned `x` reports the
        // `Additive` ambiguity FIRST and the field check never runs. That is a real and
        // separate diagnostic — it would make this control measure symbol resolution
        // rather than the field check it is here for.
        &plain("lambda x -> x"),
        &["plain.v", "expected Int64, got"],
        "a lambda in an Int64 field was refused before this ticket and must stay so",
    );
}

/// CONTROL — the WELL-TYPED program the headline row is the negative of. Passes either
/// way BY DESIGN. Without it, every row above is satisfied by a fix that simply refuses
/// `plain(...)`, and nothing here would notice.
#[test]
fn a_well_typed_field_value_still_loads() {
    assert!(
        errs(&plain("7")).is_empty(),
        "an Int64 in an Int64 field must still load",
    );
}

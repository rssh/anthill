//! WI-1059 — an UNWRITTEN sort parameter is RIGID inside the operation body.
//!
//! `s: Stream[T = Int64]` is `s: Stream[T = Int64, E = ?]`, and `?` is a NEW variable per
//! instantiation, so the operation is universally quantified over `E`: its BODY may only do
//! what holds for EVERY row. Before this ticket the body saw a FLEXIBLE variable that
//! satisfied any demand, and the two halves composed into an unsound program — each looking
//! correct alone, which is why neither was ever reported.
//!
//! `docs/kernel-language.md` §"Expansion during unification" states the rule; this file
//! drives it.
//!
//! REFERENCE: WI-1056 (which measured all four spellings and whose own false control is
//! recorded at `parameterized_compatible_view`); WI-942 (the previous widening of the
//! rigidifier, to the enclosing sort's params); WI-1016 (both carriers must key alike).

use crate::wi1012_static_supplier_tie_test::refusal;

/// The ticket's program, as source. `feed` is declared with `param`, and its body hands the
/// stream straight to `takes_pure`, which accepts only the empty row.
fn streamed(param: &str, op: &str) -> String {
    format!(
        "namespace test.wi1059.erow\n\
         \x20 import anthill.prelude.{{Int64, Stream}}\n\
         \x20 operation takes_pure(s: Stream[T = Int64, E = {{}}]) -> Int64\n\
         \x20 operation {op}(s: {param}) -> Int64 = takes_pure(s)\n\
         end\n",
    )
}

/// THE HEADLINE — the unwritten row may not be assumed empty.
///
/// The refusal names `s.E`, the projection the unwritten slot is filled with: that is the
/// language's own name for "the row of THIS stream, whatever it is", and it is rigid by the
/// mechanism already in place (WI-400 ζ — a neutral never equals a concrete type). Asserted
/// on the exact rendering rather than on a bare `"E"`, which an unrelated mismatch on the
/// ELEMENT type would also satisfy.
///
/// CONTROL: on main this program LOADS, and so does the caller that exploits it
/// (`an_effectful_stream_cannot_reach_a_pure_slot`).
#[test]
fn an_unwritten_row_is_rigid_in_the_body() {
    let msg = refusal(&streamed("Stream[T = Int64]", "feed"));
    assert!(
        msg.contains("E = s.E") && msg.contains("E = {}"),
        "the refusal must name the row it cannot assume and the row it was handed to: {msg}",
    );
}

/// THE SECOND LEAK, and the case that proves the CHECK rather than the skolemizer: here `E`
/// IS in `rec.type_params` and IS rigidified already — yet the program loaded anyway.
///
/// The ticket read that as "the subtype check accepts a RIGID row against a written `{}`".
/// It does not: `subtype_effect_rows` refuses one correctly, at `bind_row_tail` (WI-336, a
/// rigid tail is not bindable). The check was never REACHED — `resolved_type_is_ground`
/// called every `Term::Var` non-ground, skolems included, and `validate_arg_against_param`
/// returns `Ok` on a non-ground pair without checking anything. So this case is fixed by
/// [`type_value_is_ground`] alone, and needs nothing from the skolemizer.
///
/// CONTROL: on main this loads DESPITE being rigidified. It is also the one row of this file
/// that fails when ONLY the rigid-is-ground line is backed out — the other two refusals
/// additionally need the unwritten slot to be materialized.
#[test]
fn an_op_type_param_row_is_rigid_in_the_body() {
    let msg = refusal(&streamed("Stream[T = Int64, E = E]", "feed[E]"));
    assert!(
        msg.contains("E = ?E") && msg.contains("E = {}"),
        "the refusal must name the skolem it cannot assume and the row it was handed to: \
         {msg}",
    );
}

/// The composed program the two halves add up to: `feed` claims any row, `caller` hands it
/// `{Error}`. The REFUSAL belongs at `feed`, not at `caller` — asserted, because "it is
/// refused somewhere" would also pass if the rule had been put in the wrong place, and
/// refusing at the caller would make every legitimate row-polymorphic signature unusable.
///
/// CONTROL: on main BOTH lines load and an effectful stream reaches an operation that
/// declared it wanted none.
#[test]
fn an_effectful_stream_cannot_reach_a_pure_slot() {
    let src = "namespace test.wi1059.exploit\n\
        \x20 import anthill.prelude.{Int64, Stream, Error}\n\
        \x20 operation takes_pure(s: Stream[T = Int64, E = {}]) -> Int64\n\
        \x20 operation feed(s: Stream[T = Int64]) -> Int64 = takes_pure(s)\n\
        \x20 operation caller(s: Stream[T = Int64, E = {Error}]) -> Int64 = feed(s)\n\
        end\n";
    let msg = refusal(src);
    assert!(
        msg.contains("takes_pure.s") && !msg.contains("feed.s"),
        "the refusal belongs at `feed`'s body — the call on takes_pure — and NOT at the \
         caller that hands `feed` an effectful stream: {msg}",
    );
}

/// THE POSITIVE CONTROL: an author who MEANS the empty row writes it, and that still loads.
/// Passes both with and without this ticket's change, by design — it is here so the refusals
/// above cannot be satisfied by a check that simply rejects every row.
#[test]
fn a_written_empty_row_still_loads() {
    crate::common::load_kb_with(&streamed("Stream[T = Int64, E = {}]", "feed"));
}

/// THE OTHER POSITIVE CONTROL, and the one that keeps this ticket from being "reject every
/// unwritten parameter": a body that genuinely holds for EVERY instantiation still loads,
/// under all four spellings. `sink` leaves its OWN row unwritten and names its element as an
/// operation type parameter, so it accepts any of both — and at a CALL SITE an unwritten
/// parameter is FLEXIBLE again and binds from the argument, which is exactly the asymmetry
/// the rule rests on. Same variable, two positions.
///
/// `sink[X](s: Stream[T = X])`, NOT `sink(s: Stream[T = Int64])` — the first draft wrote the
/// latter and the bare-`Stream` row failed, correctly: a bare reference leaves `T` unwritten
/// too, so `feed(s: Stream)` claims any ELEMENT type and may no more hand it to an
/// `Int64`-demanding slot than it may assume a row. The four spellings are one type only in
/// `E`; in `T` the bare one says strictly less.
///
/// CONTROL, and it is NOT the both-ways-green non-regression a first draft claimed: back the
/// materialization out and the BARE row fails with `expected a type for 'X', got
/// unconstrained`. A bare argument carries no slot for `sink`'s `X` to bind to, so
/// materializing the parameter is what gives the inference something to solve — the same
/// mechanism read from its accepting side. The other three rows pass either way.
#[test]
fn a_body_that_holds_for_every_row_still_loads() {
    for (param, op) in [
        ("Stream[T = Int64, E = E]", "feed[E]"),
        ("Stream", "feed"),
        ("Stream[T = Int64, E = ?]", "feed"),
        ("Stream[T = Int64]", "feed"),
    ] {
        crate::common::load_kb_with(&format!(
            "namespace test.wi1059.polymorphic\n\
             \x20 import anthill.prelude.{{Int64, Stream}}\n\
             \x20 operation sink[X](s: Stream[T = X]) -> Int64\n\
             \x20 operation {op}(s: {param}) -> Int64 = sink(s)\n\
             end\n",
        ));
    }
}

//! WI-1083 — a TYPE-PARAMETERIZED OPERATION IS A FUNCTION VALUE, because its type is now a
//! ∀ over an arrow rather than an arrow it does not fit in.
//!
//! `operation_as_function_value` refused to eta-lift any operation declaring `[A]`, on the
//! stated grounds that "its arrow would carry unfreshened type-param vars that alias across
//! multiple eta-lifts of the same op". True of an ARROW, which has nowhere to write a binder.
//! `TypeExtractor.PolyType(binders, body)` has one, so the binders say exactly which variables
//! to freshen, `check_bare_ref` freshens them at the reference (§5.6 — a type parameter is
//! "the CALLER's to instantiate"), and the clause is gone.
//!
//! ## REFUSING THE LIFT DID NOT REFUSE THE PROGRAM — that is what the clause hid
//!
//! With the lift refused, control fell through to `check_bare_ref`'s zero-arg-call reading,
//! which types a bare `idp[A](x: A) -> A` as its declared return `?A` — a bare flexible
//! variable that unifies with ANY expected type. So the gate did not keep these operations out
//! of function-typed slots; it let them in **untyped**. Two consequences, both measured here
//! against the back-out (re-adding `if !op.type_params.is_empty() { return None; }`):
//!
//! | | with the gate (back-out) | delivered |
//! |---|---|---|
//! | a type-parameterized member of a `requires`-carrying sort, passed as a value and RUN | loads clean, then **traps at eval** — `DeferToRequirement: requirement param `__req_eq` not bound in caller frame` | runs, returns `"hi"` |
//! | a 2-parameter type-parameterized operation in a 1-parameter arrow slot | **loads clean** | refused, naming both arities |
//!
//! The first is the headline and it is a broken invariant, not a missing feature:
//! `operation_as_function_value`'s own doc opens by stating that it lifts only what the
//! runtime can run, "keeping the typer's accepted set a subset of the evaluator's". The
//! fallback reading typed the reference without ever reaching `attach_eta_dispatch_dict`, so
//! no dispatch dictionary was captured on the `OpRef` and the operation's `__req_*` was
//! unbound when the HOF applied it.
//!
//! ## WHAT THIS TICKET DID NOT CLOSE, and WI-1084 did
//!
//! As delivered, a RESULT-type and an EFFECT-ROW disagreement were still not refused for a
//! type-parameterized operation while both were refused for the monomorphic twin — pinned
//! here as two known-gap rows. WI-1084 found the root and it was NOT the WI-385 groundness
//! discipline this header first blamed: `unify_types` had no `arrow` ↔ `Function[A, B, E]`
//! arm at all, so the pair fell to the subtype fallback, which decomposes but cannot BIND,
//! and answered `false` with ZERO bindings whether the pair agreed or not. Nothing pinned
//! `A`, so the groundness gate downstream had nothing to compare. TWO fixes were needed —
//! the missing arm, and `validate_arrow_param_result` resolving the RESULT through σ before
//! testing it for groundness — each measured separately at
//! `kb::typing::wi1084_arrow_function_unify_tests`, whose header carries the three-level
//! back-out table. [`a_result_type_disagreement_is_refused`] now holds the refusal.
//!
//! [`an_effect_row_disagreement_is_refused`] needed a THIRD and independent fix on top of
//! those two: `validate_callback_effect_row` discarded the row check for any `Function[A, B,
//! E]` slot, because such a parameter registers no binder PLACES and the alignment guard
//! bailed on the length mismatch. All three landed on WI-1084.
//!
//! ## WHO GENERALIZES, AND WHEN — the question WI-1079 handed over
//!
//! The binder list IS WI-1078's bound set, read positively. That scan already answers "which
//! variables does this signature bind" over four sources (a parameter type, a `requires`
//! clause, the operation's own `[A]`, and — WI-1082 — the declaring sort's canonical
//! parameter); WI-1078 reads it negatively to decide which RETURN variables are existential.
//! `signature_bound_vars` is now its own function with both callers, so a ∀ cannot quantify a
//! variable WI-1078 would open, nor open one the ∀ quantifies. That is what makes this
//! SUBSUME the rule rather than contradict it: `mplus(a: LogicalStream[?A], b:
//! LogicalStream[?A]) -> LogicalStream[?A]` declares no brackets at all, and its `?A` is a
//! binder here for exactly the reason it is bound there.
//!
//! GENERALIZATION HAPPENS AT THE LIFT, not at load and not at instantiation:
//! `generalize_eta_arrow` runs inside `operation_as_function_value`, which is where an
//! operation first becomes a VALUE. Nothing is stored on `OperationInfo` — the ticket
//! predicted no new field there and there is none.
//!
//! A CONSEQUENCE WIDER THAN THE GATE, because the set counts the declaring sort's parameter
//! too: a member of a PARAMETERIZED sort now lifts to a ∀ whether or not it declares `[A]`.
//! `SortedSet.insert` is the corpus case, it eta-lifted before this ticket, and its behaviour
//! is unchanged — but only because the dictionary pin reads the ∀'s body un-freshened. The
//! third back-out row below is that measurement, and it is not one of this file's rows.
//!
//! ## What fails when each piece is backed out — DRIVEN, one revert each, whole crate
//!
//! | revert | cost |
//! |---|---|
//! | the gate re-added (`if !op.type_params.is_empty() { return None; }`) | **6**, and NOTHING outside this ticket's own files: [`a_requires_carrying_member_runs_as_a_function_value`] (loads, then traps at eval), [`a_member_naming_its_own_sort_still_resolves_its_dictionary`], [`an_arity_disagreement_is_refused`], [`two_element_types_in_one_program`] (on its `EtaOpRef` half — the VALUES stay right), and both `kb::typing::wi1083_poly_type_tests` rows (the lift returns `None`, so there is no ∀ to inspect) |
//! | `generalize_eta_arrow` returns its arrow unwrapped | **2** — the two `wi1083_poly_type_tests` rows ALONE. Every integration row above survives, and that is the honest shape of this ticket: with one reference per operation per program there is nothing for the freshening to separate, so the ∀ is only observable at its own site. Reaching it from a program needs let-polymorphism (a bare reference that eta-lifts with NO expectation), which is not delivered here |
//! | `attach_eta_dispatch_dict` pins on an INSTANTIATION instead of `poly_type_body`'s un-freshened body | **1**, and not one of this file's: `wi844_sorted_set_driver_test::an_etad_op_takes_its_ordering_from_the_expected_arrow`. `SortedSet.insert` names its own sort's parameters, which the ∀ now quantifies, and the dictionary's dependencies are keyed by those same canonical variables — so a pin made on fresh ones leaves the requirement "unsatisfiable". Every row in THIS file passes under that revert, including the one written to try to catch it |
//! | `instantiate_poly_type` walks with `walk_type_deep_value` instead of the shared σ walk | **1** — `kb::typing::wi1083_poly_type_tests::no_declared_binder_survives_into_an_instantiation`, which fails with `leaked [452, 453]`. That walk's `NamedTuple` arm answers "unchanged", so a binder in a Node-carried parameter LIST was never freshened and the ticket's headline property held only for ONE-parameter operations. Found by review; nothing else in the workspace notices |
//!
//! That the first revert costs nothing OUTSIDE these files is itself a measurement: the gate
//! was guarding no behaviour the corpus or the suite relied on. The third revert is the
//! opposite lesson — the widest consequence of this change (that a member of a PARAMETERIZED
//! sort now lifts to a ∀ whether or not it declares `[A]`) is caught only by a pre-existing
//! test, on a stdlib operation, at a value.
//!
//! Rows that pass BOTH ways, by design, and say so at their sites:
//! [`an_arity_disagreement_is_refused_for_a_monomorphic_operation`]. [`two_element_types_in_one_program`] is half and half — its values pass either way
//! (the `?A` fallback already unified with anything, and eval mints an `OpRef` by arity), its
//! classification assertion does not.
//!
//! REFERENCE: WI-1079 (where the shape was decided, and the three variable forms this builds
//! on), WI-1078 (the bound set this consumes), WI-1063 (the ∃ opening, whose once-per-lift
//! limit is NOT moved here — see `operation_as_function_value`), WI-420 (the eta dispatch
//! dict), WI-700 (why a nullary op eta-lifts), WI-791 (arrow arity),
//! `docs/kernel-language.md` §5.4 and §5.6.

use crate::wi1012_static_supplier_tie_test::refusal;
use anthill_core::kb::typing::CallClass;

/// `idp[A]` at two element types in one program, through two references.
const TWO_TYPES: &str = "namespace test.wi1083.two\n\
    \x20 import anthill.prelude.{Int64, String, Function}\n\
    \x20 operation idp[A](x: A) -> A = x\n\
    \x20 operation callInt(f: Function[A = Int64, B = Int64, E = {}], v: Int64) -> Int64 = f(v)\n\
    \x20 operation callStr(f: Function[A = String, B = String, E = {}], v: String) -> Int64 \
       = String.length(f(v))\n\
    \x20 operation atInt() -> Int64 = callInt(idp, 3)\n\
    \x20 operation atStr() -> Int64 = callStr(idp, \"abcd\")\n\
    end\n";

fn int_result(src: &str, op: &str) -> i64 {
    // Fresh interpreter per call — a reused one poisons later calls after a trap.
    let mut interp = crate::common::interp_for(src);
    match interp
        .call(op, &[])
        .unwrap_or_else(|e| panic!("call {op}: {e:?}"))
    {
        anthill_core::eval::Value::Int(i) => i,
        other => panic!("call {op}: expected Int, got {other:?}"),
    }
}

/// THE HEADLINE. `Bag.tagged[D]` is type-parameterized AND sits on a sort with a `requires`,
/// so running it needs the dispatch dictionary `attach_eta_dispatch_dict` captures on the
/// `OpRef` at the eta site. Under the gate the lift never happened, the reference took the
/// `?A` return-type reading, no dictionary was attached — and the program LOADED and then
/// died inside the callee with `__req_eq` unbound.
///
/// Driven to a VALUE, not to a load: "it loads" is exactly what it did before, and is the
/// property that hid the defect.
///
/// CONTROL: with the gate re-added this loads clean and traps
/// `DeferToRequirement: requirement param `__req_eq` not bound in caller frame (running
/// `test.wi1083.req.Bag.tagged`, requires-chain owner `test.wi1083.req.Bag`; frame binds [])`.
#[test]
fn a_requires_carrying_member_runs_as_a_function_value() {
    let src = "namespace test.wi1083.req\n\
        \x20 import anthill.prelude.{Int64, String, Bool, Function, Eq}\n\
        \x20 sort Bag\n\
        \x20   requires anthill.prelude.Eq[T = Int64]\n\
        \x20   sort T = ?\n\
        \x20   operation tagged[D](probe: Int64, d: D) -> D = if eq(probe, probe) then d else d\n\
        \x20 end\n\
        \x20 import test.wi1083.req.Bag.{tagged}\n\
        \x20 operation callit(f: Function[A = (a: Int64, b: String), B = String, E = {}]) \
         -> String = f(1, \"hi\")\n\
        \x20 operation use_it() -> String = callit(tagged)\n\
        end\n";
    let mut interp = crate::common::interp_for(src);
    match interp.call("test.wi1083.req.use_it", &[]) {
        Ok(anthill_core::eval::Value::Str(s)) => assert_eq!(
            &*s, "hi",
            "the eta'd member must RUN and return its argument",
        ),
        Ok(other) => panic!("expected Str(\"hi\"), got {other:?}"),
        Err(e) => panic!(
            "a type-parameterized member of a `requires`-carrying sort must run as a function \
             value, not trap — the typer's accepted set is a subset of the evaluator's: {e:?}",
        ),
    }
}

/// THE DECLARING SORT'S PARAMETER IS A BINDER TOO. `signature_bound_vars` includes the sort's
/// canonical parameter (WI-1082 put it there), so an eta of a member that NAMES its own sort
/// quantifies it — here on top of the member's own `[D]`, and with the sort's `requires` keyed
/// on that same parameter (`requires Eq[T = T]`), which is the configuration where a mishandled
/// binder would show up as an unresolvable dictionary rather than as a type error.
///
/// Driven to a VALUE for the same reason as the row above: a dictionary that resolves to
/// nothing shows up at eval, not at load.
///
/// CONTROL: fails under the gate back-out, so it measures the deletion in this configuration.
/// It does NOT measure `poly_type_body` — MEASURED, it passes with that read replaced by an
/// instantiation. The row that measures THAT is
/// `wi844_sorted_set_driver_test::an_etad_op_takes_its_ordering_from_the_expected_arrow`, on the
/// stdlib's own `SortedSet.insert`, and it is named at `poly_type_body` itself.
#[test]
fn a_member_naming_its_own_sort_still_resolves_its_dictionary() {
    let src = "namespace test.wi1083.self\n\
        \x20 import anthill.prelude.{Int64, String, Bool, Function, Eq}\n\
        \x20 sort Holder\n\
        \x20   requires anthill.prelude.Eq[T = T]\n\
        \x20   sort T = ?\n\
        \x20   entity Holder(seed: T)\n\
        \x20   operation relabel[D](h: Holder, d: D) -> D = if eq(h.seed, h.seed) then d else d\n\
        \x20 end\n\
        \x20 import test.wi1083.self.Holder.{relabel}\n\
        \x20 operation callit(f: (Holder[T = Int64], String) -> String, h: Holder[T = Int64]) \
         -> String = f(h, \"ok\")\n\
        \x20 operation use_it() -> String = callit(relabel, Holder(seed: 1))\n\
        end\n";
    let mut interp = crate::common::interp_for(src);
    match interp.call("test.wi1083.self.use_it", &[]) {
        Ok(anthill_core::eval::Value::Str(s)) => assert_eq!(&*s, "ok"),
        Ok(other) => panic!("expected Str(\"ok\"), got {other:?}"),
        Err(e) => panic!("the eta'd member must run with its dictionary attached: {e:?}"),
    }
}

/// TWO INSTANTIATIONS IN ONE PROGRAM, values asserted — the ticket's acceptance. `idp` serves
/// `Int64` at one reference and `String` at another; nothing ties the two, which is what a
/// single shared type-param variable would have done.
///
/// CONTROL: the VALUES are right under the back-out too — the `?A` reading unifies with
/// anything, and eval mints an `OpRef` for an arity-≥1 bare reference regardless. What the
/// back-out does NOT do is CLASSIFY the reference, so the second half of this row (the program
/// carries one `EtaOpRef` per reference) is the half that measures the change; it counts 0
/// there. Both halves are here because the value assertion alone would be vacuous.
#[test]
fn two_element_types_in_one_program() {
    assert_eq!(int_result(TWO_TYPES, "test.wi1083.two.atInt"), 3);
    assert_eq!(int_result(TWO_TYPES, "test.wi1083.two.atStr"), 4);

    let kb = crate::common::load_kb_with(TWO_TYPES);
    let mut etas = 0usize;
    for (_, body) in kb.op_bodies_iter() {
        anthill_core::kb::node_occurrence::visit_classifications(body, &mut |_, c| {
            if matches!(c, CallClass::EtaOpRef { .. }) {
                etas += 1;
            }
        });
    }
    assert_eq!(
        etas, 2,
        "each reference to `idp` must be classified as an eta lift — under the back-out the \
         lift is refused and the reference falls through to the zero-arg-call reading, which \
         classifies nothing",
    );
}

/// A 2-parameter operation does not belong in a 1-parameter arrow slot, and a `[A]` on it
/// never made that less true. With the eta refused, the reference typed as the bare variable
/// `?A` and the whole disagreement was invisible.
///
/// CONTROL: [`an_arity_disagreement_is_refused_for_a_monomorphic_operation`] below is the same
/// program without the `[A]`, refused BOTH ways — so this row measures the type parameter and
/// not the arity check.
#[test]
fn an_arity_disagreement_is_refused() {
    let msg = refusal(
        "namespace test.wi1083.arity\n\
         \x20 import anthill.prelude.{Int64}\n\
         \x20 operation two[A](x: A, y: A) -> A = x\n\
         \x20 operation callit(f: (v: Int64) -> Int64) -> Int64 = f(3)\n\
         \x20 operation use_it() -> Int64 = callit(two)\n\
         end\n",
    );
    assert!(
        msg.contains("1-parameter") && msg.contains("2-parameter"),
        "the refusal must name both arities: {msg}",
    );
}

/// The monomorphic twin of the row above — refused before this ticket and after it. Here to
/// fix what the row above is measuring, not to measure anything itself.
#[test]
fn an_arity_disagreement_is_refused_for_a_monomorphic_operation() {
    let msg = refusal(
        "namespace test.wi1083.aritym\n\
         \x20 import anthill.prelude.{Int64}\n\
         \x20 operation twom(x: Int64, y: Int64) -> Int64 = x\n\
         \x20 operation callit(f: (v: Int64) -> Int64) -> Int64 = f(3)\n\
         \x20 operation use_it() -> Int64 = callit(twom)\n\
         end\n",
    );
    assert!(msg.contains("1-parameter") && msg.contains("2-parameter"), "{msg}");
}

/// A RESULT-TYPE DISAGREEMENT IS REFUSED — closed by WI-1084, and this row was a
/// known-gap pin until it was. `∀A. (x: A) -> A` cannot be `Int64 -> String`: the parameter
/// pins `A := Int64` and the result then contradicts `String`. It is visible only THROUGH
/// the shared variable, which is why it needed two fixes — unification had no
/// `arrow` ↔ `Function[A, B, E]` arm to make the binding with, and
/// `validate_arrow_param_result` then tested the result for groundness without resolving it
/// through σ.
///
/// CONTROL: on WI-1083 as delivered this LOADED, and `use_it()` — declared `-> String` —
/// returned `Int(3)`. Its monomorphic twin was refused throughout, which is what said the
/// polymorphic verdict was wrong rather than the rule being lax.
#[test]
fn a_result_type_disagreement_is_refused() {
    let msg = refusal(
        "namespace test.wi1083.res\n\
         \x20 import anthill.prelude.{Int64, String, Function}\n\
         \x20 operation idp[A](x: A) -> A = x\n\
         \x20 operation callit(f: Function[A = Int64, B = String, E = {}]) -> String = f(3)\n\
         \x20 operation use_it() -> String = callit(idp)\n\
         end\n",
    );
    assert!(
        msg.contains("callit.f") && msg.contains("String"),
        "the disagreement is refused at the argument, naming the slot and the contradicted \
         result: {msg}",
    );
    // THE MONOMORPHIC TWIN, kept beside it: the identical mismatch with no type parameter,
    // refused before this cluster and after it. Without it this row passes under any
    // regression that refuses `Function`-typed callbacks MORE broadly — which is the reading
    // the twin exists to exclude, and which the WI-1084 rewrite briefly dropped.
    let mono = refusal(
        "namespace test.wi1083.resm\n\
         \x20 import anthill.prelude.{Int64, String, Function}\n\
         \x20 operation idm(x: Int64) -> Int64 = x\n\
         \x20 operation callit(f: Function[A = Int64, B = String, E = {}]) -> String = f(3)\n\
         \x20 operation use_it() -> String = callit(idm)\n\
         end\n",
    );
    assert!(mono.contains("callit.f"), "the monomorphic twin stays refused: {mono}");
}

/// AN EFFECT-ROW DISAGREEMENT IS REFUSED — the effect-row half, closed by WI-1084, and it
/// is worth its own row because an effect leak is what WI-1063 / WI-1078 exist about.
/// `bang[A](x: A) -> A effects {Error}` in a slot declaring `E = {}` used to load.
///
/// It needed a THIRD fix beyond the two the result-type row needed:
/// `validate_callback_effect_row` discarded the row check entirely for any `Function[A, B,
/// E]` slot, because such a parameter registers NO argument places and the binder-alignment
/// guard bailed on the length mismatch. There is nothing to align when neither side names a
/// place, and `{Error}` versus `{}` is decidable without one.
///
/// CONTROL: on WI-1083 as delivered this LOADED, and the raising variant below TRAPPED
/// `Raised { payload: Str("boom") }` at runtime — out of a `use_it() -> Int64` that declares
/// no effects, through a slot that declares `E = {}`. Its monomorphic twin was refused
/// throughout.
#[test]
fn an_effect_row_disagreement_is_refused() {
    let msg = refusal(
        "namespace test.wi1083.eff\n\
         \x20 import anthill.prelude.{Int64, Function, Error}\n\
         \x20 operation bang[A](x: A) -> A effects {Error} = x\n\
         \x20 operation callit(f: Function[A = Int64, B = Int64, E = {}]) -> Int64 = f(3)\n\
         \x20 operation use_it() -> Int64 = callit(bang)\n\
         end\n",
    );
    assert!(
        msg.contains("closed row does not admit") && msg.contains("Error"),
        "the refusal must name the effect the closed row does not admit: {msg}",
    );
    // The same program with a body that ACTUALLY raises — the one that reached a runtime
    // `Raised` through two declarations that both promised purity. Refused at LOAD now.
    let raising = refusal(
        "namespace test.wi1083.effr\n\
         \x20 import anthill.prelude.{Int64, String, Function, Error}\n\
         \x20 operation bang[A](x: A) -> A effects {Error[T = String]} = Error.raise(\"boom\")\n\
         \x20 operation callit(f: Function[A = Int64, B = Int64, E = {}]) -> Int64 = f(3)\n\
         \x20 operation use_it() -> Int64 = callit(bang)\n\
         end\n",
    );
    assert!(
        raising.contains("closed row does not admit") && raising.contains("Error[T = String]"),
        "{raising}",
    );
    // The monomorphic twin, for the reason given on the result-type row above.
    let mono = refusal(
        "namespace test.wi1083.effm\n\
         \x20 import anthill.prelude.{Int64, Function, Error}\n\
         \x20 operation bangm(x: Int64) -> Int64 effects {Error} = x\n\
         \x20 operation callit(f: Function[A = Int64, B = Int64, E = {}]) -> Int64 = f(3)\n\
         \x20 operation use_it() -> Int64 = callit(bangm)\n\
         end\n",
    );
    assert!(mono.contains("callit.f"), "the monomorphic twin stays refused: {mono}");
}

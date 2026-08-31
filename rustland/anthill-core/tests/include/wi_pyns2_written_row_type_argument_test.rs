//! WI-20260831-PYNS2 — A WRITTEN ROW TYPE-ARGUMENT ON A PARAMETER MUST REACH THE CALL'S
//! EFFECT INSTANTIATION, NOT ONLY THE DECLARED ROW.
//!
//! ```text
//! operation ask(s: Spec[E = {Error}], p: String) -> Out
//!   effects {s.E, Error} = Spec.go(s, p)
//! ```
//!
//! The DECLARED side eliminated `s.E` correctly — the refusal's own
//! `expected declared: [Error, Error]` proves the written binding was read. The BODY's
//! call incurred the spec op's `{E, Error}` with `E` UNBOUND, so an unresolved row var
//! surfaced as `got undeclared effect: ?_`. One parameter, one written binding, read on
//! one side and not the other.
//!
//! ## THE TICKET'S SCOPE WAS WIDER THAN THE DEFECT, and that census is the main result
//!
//! "Today that spelling cannot be used at all" is measured FALSE. WHICH RECEIVER SHAPE the
//! called operation has decides it, and only one of three was broken:
//!
//! | receiver shape | before | after |
//! |---|---|---|
//! | self-receiver spec op (`go(self: Spec, …)`) | WORKS | unchanged |
//! | carrier-param (`go(self: C, …)`), some sort `provides Spec` | WORKS | unchanged |
//! | carrier-param, NO sort provides the spec YET | `?_` | WORKS |
//!
//! The self-receiver shape never needed anything: `self: Spec` unifies with the argument's
//! `Spec[E = {Error}]`, and ordinary argument unification binds `Spec.E`. The CARRIER-PARAM
//! shape (`sort C = ?` beside `go(self: C, …)` — guardians' `Llm.complete`, the stdlib's
//! `Iterable`) binds `C` from the receiver and leaves `Spec.E` to WI-609's REFLEXIVE arm of
//! `carrier_param_receiver`: the receiver's carrier IS the op's own spec, so the receiver's
//! own type-args ARE the spec's params. That arm sat under `carrier_is_abstract_spec`, and
//! INSTRUMENTED, the leg that declined was the PROVIDER one — `spec=Spec carrier=Spec
//! has_ctors=false has_providers=false`. It is a leg this arm has already answered, since
//! the carrier IS the sort declaring the operation; the fix asks the reflexive question
//! above that predicate, and the reasoning is at the site.
//!
//! A spec nobody implements YET is exactly the state a program is in while it is being
//! written, which is why the ticket's own minimal fixture hit this and guardians did not.
//! MEASURED ON GUARDIANS: `ask(m: Llm[E = {}], p: Prompt) effects {m.E, Error} =
//! Llm.complete(m, p)` — the ticket's motivating "I take a pure model" spelling — loads,
//! and its `E = {External}` twin under a row omitting `External` is refused BY NAME. `Llm`
//! has two carriers, so it is the `a_provided_spec_reads_the_written_row` row of the table,
//! which is the one measured unchanged across the back-out.
//!
//! ## The second half of the fix, which the first half made necessary
//!
//! `statically_pinned_carrier` filtered its carrier param with `!carrier_is_abstract_spec`,
//! using the PROVIDER leg as its stand-in for "is this an abstract spec value?". Once the
//! reflexive arm stopped needing a provider, a spec nothing provides reached that filter,
//! answered "concrete", and was reported as a statically pinned CARRIER — the very mis-pin
//! its WI-608 leg exists to prevent, in that leg's own words. It takes the spec symbol now
//! and excludes a reflexive carrier outright. Measured benign either way (a spec with no
//! providers has no competing supplier to mis-pin TO, so both readers agreed), which is why
//! no test here reds on it — it is stated so the invariant is asked rather than argued.
//! (/code-review)
//!
//! ## What fails when it is backed out
//!
//! ```text
//!   back-out                                            reds
//!   the reflexive arm put back UNDER                    a_written_row_type_argument_… (both rows)
//!   `carrier_is_abstract_spec` (the pre-ticket code)    a_label_the_declared_row_omits_… (both halves)
//!                                                       a_bodyless_op_on_an_unimplemented_… (first half)
//! ```
//!
//! THE CONTROLS PASS BOTH WAYS BY DESIGN, and each dates a different half of the census:
//! `a_self_receiver_spec_op_reads_the_written_row` (the shape that always worked),
//! `a_provided_spec_reads_the_written_row` (the shape a carrier already fixed — which is
//! what says this ticket changed the PROVIDER leg and not the reading of a written type
//! argument), `a_carrier_with_its_own_constructors_is_not_read_as_the_spec` (the leg the fix
//! keeps), and the self-receiver half of `a_bodyless_op_on_an_unimplemented_…`.
//!
//! ## THE WIDENING THAT WAS BUILT, MEASURED, AND DECLINED
//!
//! Dropping the reflexive arm's remaining `!sort_has_constructors` leg as well makes
//! `a_carrier_with_its_own_constructors_…`'s shape load, with the same by-name refusal, and
//! leaves the FULL SUITE GREEN (measured: 6227 / 0, against 6232 / 0 for what shipped). It is declined on what the flag it sets MEANS, not on a
//! measured red: an empty view marked `transitive` makes the call DEFER to eval's
//! value-directed dispatch, returning above `dispatch_spec_op_cached` and with it above
//! `MissingRequiresForSpecOp` and WI-1027's supplier-tie refusal. Every neighbour that sets
//! that flag (WI-598/601/608/609) reserves it for a value with no representation of its
//! own, and `sort_has_constructors` is the canonical data-sort-vs-spec predicate. Widening
//! it would move a CONCRETE sort onto that path — where, unlike the provider-less spec, a
//! competing supplier CAN exist — to silence one diagnostic at the cost of three. The
//! hazard first written down here (a `Box[T = Box[T = Int64]]` whose `Box.wrap(x: T)`
//! receiver is an ELEMENT, not a carrier) was BUILT AND DID NOT FIRE: both variants answer
//! `expected Box[T = Int64], got Box[T = Box[T = Int64]]`, so it is recorded as not-driven
//! rather than as the reason.

use crate::common::{assert_refused_naming, try_load_kb_with_files};

/// The load diagnostics for the stdlib plus these sources, empty when it loads.
fn load_errors(srcs: &[&str]) -> Vec<String> {
    try_load_kb_with_files(srcs).err().unwrap_or_default()
}

const OUT: &str = r#"
namespace test.pyns2.out
  import anthill.prelude.{String}
  sort Out
    entity out(v: String)
  end
end
"#;

/// THE TICKET'S SPEC, verbatim in shape: a CARRIER-PARAM receiver (`self: C`) over a row
/// parameter, and NO sort provides it. The default body keeps the fixture self-contained —
/// what is under test is the call's effect instantiation, not dispatch.
const SPEC: &str = r#"
namespace test.pyns2.spec
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.pyns2.out.{Out}
  import test.pyns2.out.Out.{out}
  sort Spec
    sort C = ?
    effects E = ?
    operation go(self: C, p: String) -> Out
      effects {E, Error} = out(v: p)
  end
end
"#;

/// THE CONTROL SPEC: identical but for the receiver, which is the SPEC SORT itself. Binds
/// `Spec2.E` by ordinary argument unification and was never affected.
const SPEC_SELF: &str = r#"
namespace test.pyns2.selfrecv
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.pyns2.out.{Out}
  import test.pyns2.out.Out.{out}
  sort Spec2
    effects E = ?
    operation go(self: Spec2, p: String) -> Out
      effects {E, Error} = out(v: p)
  end
end
"#;

/// THE CONTROL SPEC that dates the defect to the PROVIDER leg: the same carrier-param shape
/// as `SPEC`, with one carrier providing it. Loaded clean before this ticket.
const SPEC_PROVIDED: &str = r#"
namespace test.pyns2.provided
  import anthill.prelude.{Error, String, External, EffectsRuntime}
  import test.pyns2.out.{Out}
  import test.pyns2.out.Out.{out}
  sort Spec3
    sort C = ?
    effects E = ?
    operation go(self: C, p: String) -> Out
      effects {E, Error} = out(v: p)
  end
  sort Carrier3
    entity carrier3(t: String)
    operation go(self: Carrier3, p: String) -> Out
      effects {External, Error} = out(v: p)
    provides Spec3[E = {External}]
  end
end
"#;

/// A sort with ITS OWN CONSTRUCTORS that also declares a carrier param — the shape the
/// reflexive arm's surviving `sort_has_constructors` leg keeps out.
const SPEC_CONCRETE: &str = r#"
namespace test.pyns2.concrete
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.pyns2.out.{Out}
  import test.pyns2.out.Out.{out}
  sort Spec4
    entity spec4(t: String)
    sort C = ?
    effects E = ?
    operation go(self: C, p: String) -> Out
      effects {E, Error} = out(v: p)
  end
end
"#;

fn caller(ns: &str, spec_ns: &str, spec: &str, binding: &str, declared: &str) -> String {
    format!(
        r#"
namespace test.pyns2.{ns}
  import anthill.prelude.{{Error, String, External, EffectsRuntime}}
  import test.pyns2.out.{{Out}}
  import test.pyns2.{spec_ns}.{{{spec}}}
  operation ask(s: {spec}[{binding}], p: String) -> Out
    effects {declared} = {spec}.go(s, p)
end
"#
    )
}

fn expect_loads(what: &str, srcs: &[&str]) {
    let errs = load_errors(srcs);
    assert!(errs.is_empty(), "{what} must load; got: {errs:#?}");
}

/// THE TICKET'S ACCEPTANCE, first two clauses: the written row REACHES the call, at a
/// non-empty row and at the empty one.
///
/// BACKED OUT (the reflexive arm returned to UNDER `carrier_is_abstract_spec`): both rows
/// red, with `expected declared: [Error, Error], got undeclared effect: ?_` and
/// `expected declared: [Error], got undeclared effect: ?_`.
#[test]
fn a_written_row_type_argument_reaches_the_calls_effect_instantiation() {
    let bound = caller("c1", "spec", "Spec", "E = {Error}", "{s.E, Error}");
    expect_loads(
        "a written row type-argument projected into the declared row",
        &[OUT, SPEC, &bound],
    );
    // The EMPTY row is the ticket's own control for "the fix binds the row rather than
    // special-casing a non-empty one". It failed IDENTICALLY before, so within this file it
    // is coverage and not a control — what it rules out is a repair keyed on the row having
    // a label in it.
    let empty = caller("c2", "spec", "Spec", "E = {}", "{s.E, Error}");
    expect_loads("an EMPTY written row type-argument", &[OUT, SPEC, &empty]);
}

/// THE TICKET'S THIRD ACCEPTANCE CLAUSE, and the one that says the row was BOUND rather
/// than SILENCED: a declared row that omits what the receiver's row admits must still be
/// refused, NAMING the label.
///
/// BOTH HALVES ARE ASSERTED. Before this ticket a refusal DID come out here — it read
/// `?_`, a message naming no label at all, which is what made the defect unreadable. So an
/// assertion on "some refusal" passes on the broken tree; the negative half is what
/// separates them.
#[test]
fn a_label_the_declared_row_omits_is_refused_by_its_own_name() {
    let src = caller("c3", "spec", "Spec", "E = {External}", "{Error}");
    let errs = load_errors(&[OUT, SPEC, &src]);
    assert_refused_naming(
        &errs,
        &["undeclared effect: External"],
        "a written `E = {External}` incurred through the call must be refused BY NAME \
         against a declared row that omits it",
    );
    assert!(
        !errs.iter().any(|e| e.contains("undeclared effect: ?")),
        "no refusal may name an unresolved row var — that is the defect, not the verdict; \
         got: {errs:#?}"
    );
    // And the row the receiver DOES admit is accepted, so the refusal above is about the
    // omission and not about `External` being unreachable through a projection at all.
    let ok = caller("c4", "spec", "Spec", "E = {External}", "{s.E, Error}");
    expect_loads(
        "a declared row that projects the receiver's `External`",
        &[OUT, SPEC, &ok],
    );
}

/// CONTROL — the SELF-RECEIVER shape, which passes BOTH WAYS.
///
/// `go(self: Spec2, …)` unifies its parameter with the argument's `Spec2[E = {…}]`, so
/// ordinary argument unification binds `Spec2.E` and no carrier classification is involved.
/// This is what says the ticket's "a written row type-argument does not reach the call's
/// effect instantiation" was a claim about ONE receiver shape.
#[test]
fn a_self_receiver_spec_op_reads_the_written_row() {
    let ok = caller("c5", "selfrecv", "Spec2", "E = {Error}", "{s.E, Error}");
    expect_loads(
        "a self-receiver spec op at a written row",
        &[OUT, SPEC_SELF, &ok],
    );
    let bad = caller("c6", "selfrecv", "Spec2", "E = {External}", "{Error}");
    assert_refused_naming(
        &load_errors(&[OUT, SPEC_SELF, &bad]),
        &["undeclared effect: External"],
        "the self-receiver shape must refuse the omitted label BY NAME — it did so before \
         this ticket too",
    );
}

/// CONTROL — the CARRIER-PARAM shape WITH a provider, which passes BOTH WAYS and is what
/// dates the defect to `carrier_is_abstract_spec`'s PROVIDER leg rather than to the written
/// type argument.
///
/// Same `sort C = ?` + `go(self: C, …)` as `SPEC`; the only difference is that one sort
/// `provides Spec3`. It loaded clean before this ticket and still does — as does the
/// guardians `Llm` shape the ticket set out to enable, whose spec has two carriers.
#[test]
fn a_provided_spec_reads_the_written_row() {
    let ok = caller("c7", "provided", "Spec3", "E = {Error}", "{s.E, Error}");
    expect_loads(
        "a carrier-param spec op with a provider, at a written row",
        &[OUT, SPEC_PROVIDED, &ok],
    );
    let bad = caller("c8", "provided", "Spec3", "E = {External}", "{Error}");
    assert_refused_naming(
        &load_errors(&[OUT, SPEC_PROVIDED, &bad]),
        &["undeclared effect: External"],
        "the provided shape must refuse the omitted label BY NAME — it did so before this \
         ticket too",
    );
}

/// THE LEG THE FIX KEEPS, pinned because it is the one thing measured here and DECLINED.
///
/// The reflexive arm still asks `!sort_has_constructors`, so a sort with a representation
/// of its own is not read as an abstract spec value and its row still leaks `?_` in this
/// shape. Dropping that leg makes this load, with the same by-name refusal, and leaves the
/// whole suite green — so this is not a can't, it is a won't: the empty view the arm returns
/// is marked `transitive`, and that flag makes the call DEFER to eval, returning above
/// `dispatch_spec_op_cached`, `MissingRequiresForSpecOp` and WI-1027's supplier-tie
/// refusal. Its every neighbour reserves that for a value with NO representation of its
/// own. Widening it here would silence one diagnostic by skipping three.
///
/// PINNED AS THE CURRENT ANSWER, NOT ENDORSED. The shape below is a legal program with an
/// unreadable message, and what it needs is a way to tell a carrier receiver from an element
/// receiver on a concrete sort — a classification question, not this one.
#[test]
fn a_carrier_with_its_own_constructors_is_not_read_as_the_spec() {
    let src = caller("c9", "concrete", "Spec4", "E = {Error}", "{s.E, Error}");
    let errs = load_errors(&[OUT, SPEC_CONCRETE, &src]);
    assert!(
        errs.iter().any(|e| e.contains("undeclared effect: ?")),
        "a sort with its own constructors is deliberately NOT read through the reflexive \
         arm, so its row still leaks; got: {errs:#?}"
    );
}

/// THE BODY-LESS HALF, and the finding that made this test exist.
///
/// Every other fixture here gives `go` a DEFAULT BODY, which takes `check_apply`'s
/// runnable-body early return and never reaches dispatch at all. /code-review pointed out
/// that the newly-admitted population — a spec NOTHING provides — is exactly where the
/// body-less shape's classification feeds the WI-496/598 eval deferral, and measured that
/// backing this ticket out gives TWO diagnostics where the fix gives none:
///
/// ```text
///   backed out:  undeclared effect: ?_
///                missing `requires Spec5[E = …]` on enclosing sort
///                        …covering ABSTRACT TYPE PARAMETER
///   with fix:    (loads)
/// ```
///
/// THE SECOND IS A CONSEQUENCE OF THE FIRST, not an independent guard that this ticket
/// deletes, and the control that settles it is the SELF-RECEIVER twin below: the same
/// body-less op, the same unimplemented spec, the same written row — a shape this ticket
/// does not touch — LOADS CLEAN, and does so on the BACKED-OUT tree too (measured). The
/// refusal's own words say what it was about: `E` was an *abstract type parameter*, and
/// writing `E = {Error}` at the use site is precisely what stops it being one. So the
/// carrier-param shape now answers as its sibling always did.
///
/// A DEFERRAL VARIANT WAS BUILT AND BACKED OUT over this. Making the reflexive arm's
/// `transitive` flag ask WI-325's witness question (`spec_has_any_providers ||
/// !spec_warrants_abstract_check`) so a provider-less spec DISPATCHES instead of deferring
/// changed no row in this file — including this one — because a spec with no providers has
/// no candidate to be refused over. Removed rather than kept: a branch that fires nowhere.
const SPEC_BODYLESS: &str = r#"
namespace test.pyns2.bodyless
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.pyns2.out.{Out}
  sort Spec5
    sort C = ?
    effects E = ?
    operation go(self: C, p: String) -> Out
      effects {E, Error}
  end
end
"#;

/// The SELF-RECEIVER twin of `SPEC_BODYLESS` — the control, untouched by this ticket.
const SPEC_SELF_BODYLESS: &str = r#"
namespace test.pyns2.selfbodyless
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.pyns2.out.{Out}
  sort Spec6
    effects E = ?
    operation go(self: Spec6, p: String) -> Out
      effects {E, Error}
  end
end
"#;

#[test]
fn a_bodyless_op_on_an_unimplemented_spec_agrees_with_its_self_receiver_twin() {
    let carrier_param = caller("cA", "bodyless", "Spec5", "E = {Error}", "{s.E, Error}");
    expect_loads(
        "a body-less carrier-param spec op on a spec nothing provides, at a written row",
        &[OUT, SPEC_BODYLESS, &carrier_param],
    );
    // THE CONTROL, and it passes BOTH WAYS — measured on the backed-out tree, where the
    // carrier-param half above reports `?_` and the missing-`requires` refusal. That is
    // what says the refusal was about the UNPINNED row and not about the missing provider.
    let self_recv = caller("cB", "selfbodyless", "Spec6", "E = {Error}", "{s.E, Error}");
    expect_loads(
        "the self-receiver twin — same unimplemented spec, same written row",
        &[OUT, SPEC_SELF_BODYLESS, &self_recv],
    );
}

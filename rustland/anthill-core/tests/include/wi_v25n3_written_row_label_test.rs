//! WI-20260831-V25N3 — AN EFFECT LABEL WRITTEN IN A ROW TYPE-ARGUMENT IS JUDGED WHERE IT
//! IS WRITTEN, AT EVERY POSITION A ROW CAN BE WRITTEN IN.
//!
//! WI-20260831-RSRP5 established the rule and closed two of the three routes by which a
//! concrete row reaches a projection: a carrier's `provides Spec[E = {…}]` binding, and a
//! sort's bound alias `effects E = K`. The third — a row written as a TYPE ARGUMENT in a
//! signature — had no gate at all, so `docs/kernel-language.md` §5.5's "a row element is
//! judged once, AT ITS ORIGIN" (which is what lets a projection `s.E` be exempt) was
//! FALSE for that origin:
//!
//! ```text
//! operation ask(s: Spec[E = {Beep}], p: String) -> Out          -- loaded clean
//!   effects {s.E, Error} = Spec.go(s, p)
//! operation ask(s: Spec[E = {Modify[Thing]}], p: String) -> Out -- loaded clean
//!   effects {s.E, Error} = Spec.go(s, p)
//! ```
//!
//! Both labels are refused in an operation's own row and in a `provides` binding.
//!
//! ## THE WORK IS THE CENSUS, NOT THE GATE
//!
//! The judging half is RSRP5's, unchanged (`effect_element_labels` +
//! `classify_modify_target` + `registered_effect_kinds`). What this ticket had to
//! establish is WHERE a row can be written, and the answer was measured — by walking
//! every live fact head, the const-type table and every op/const body of a corpus that
//! writes a row at each candidate position, and asking where the binding LANDED — rather
//! than taken from the ticket's two examples (WI-20260830-APXSS).
//!
//! Nineteen positions are drivable and each is pinned by a fixture below; one is refused
//! before a row can be judged. They bottom out in three SOURCES:
//!
//! | # | position | source | fixture |
//! |---|---|---|---|
//! |  1 | operation PARAMETER type | site | `a_row_type_argument_on_a_parameter_…` |
//! |  2 | operation RETURN type | site | census |
//! |  3 | ENTITY FIELD type (sort-nested) | site | census |
//! |  4 | ENTITY FIELD type (free-standing, §6.3) | site | census |
//! |  5 | `sort S = Spec[…]` alias | site | census |
//! |  6 | `sort S = List[T = Spec[…]]` — nested in an alias | site | census |
//! |  7 | a sort's own `sort S = …` member | site | census |
//! |  8 | a `const`'s declared type | site | census |
//! |  9 | a body `let x: Spec[…]` annotation | site | census |
//! | 10 | a typed LAMBDA binder | site | census |
//! | 11 | nested in another instantiation (`List[T = Spec[…]]`) | site | census |
//! | 12 | an ARROW parameter type | site | census |
//! | 13 | a TUPLE component | site | census |
//! | 14 | nested inside a `provides` binding | site | `a_row_nested_inside_a_provides_…` |
//! | 15 | a sort's `requires Spec[…]` | spec clause | census |
//! | 16 | a sort's `requires B: Spec[…]` (named binder) | spec clause | census |
//! | 17 | a carrier's `provides Spec[…]` | spec clause | RSRP5's own tests |
//! | 18 | a `provides X :- Spec[…]` condition | spec clause | census |
//! | 19 | an operation's `requires` / `requires b: …` | contract clause | census |
//! | 20 | an operation TYPE-PARAM DEFAULT | — | refused by construction, own test |
//!
//! **Source: site.** [`crate::kb::ParameterizedSite`] — WI-835's registry of every
//! written parameterized type, recorded AT THE TYPE LOWERINGS so a new type position
//! cannot escape by being added elsewhere. Reused rather than re-enumerated: WI-835
//! solved this exact scope problem, and its own doc records that enumerating positions is
//! what produced the mismatch it closed.
//!
//! **Source: spec clause.** `sort_inst_to_value` is the one `TypeExpr::Parameterized`
//! lowering that records NO site — it assembles a `reflect.SortView` instead — and its
//! outputs are exactly `SortProvidesInfo`, `SortRequiresInfo` and
//! `ProvidesConditionInfo`. So the boundary is not a judgement call. (Its NESTED bindings
//! do record, through `sort_binding_to_value`, which is why row 14 arrives as a site.)
//!
//! **Source: contract clause.** An op-scoped `requires` list is OVERLOADED — it carries
//! spec requirements beside VALUE preconditions (`requires plus: Monoid[T], neq(b, 0)`)
//! — so the loader converts each item with the GOAL converter and no type lowering runs
//! at all. Measured: with the first two sources alone, rows 19's two spellings were the
//! only positions of the census still loading clean.
//!
//! THE TWO FACT SOURCES HAVE NO BATCH BOUNDARY of their own — only the site registry is
//! drained per load — so each clause fact is CLAIMED ONCE PER KB
//! (`claim_row_binding_clause`). Without it a `load_all` into a live KB of a clean file into a
//! KB already holding an offending clause re-reported that clause, failing a batch over a
//! file it was never given.
//!
//! AND THE CLAIM IS DROPPED WHEN THE LOADER RE-PRESENTS THE FACT
//! (`note_metadata_fact_presented`, WI-20260901-EA6KS): an assert DEDUPS, so re-loading
//! the very file that WROTE the clause lands on the id already claimed, and that lost the
//! refusal outright — the same unchanged file came back `Ok` with zero errors. Both
//! directions are pinned by `a_later_load_re_reports_a_re_presented_clause_…`, each named
//! there as the other's control, because either alone is satisfiable by a walk that
//! judges everything or nothing. It counts PRODUCERS of the two fact sources, not clause
//! keywords: `SortProvidesInfo` has two loader producers and only one of them went through
//! the metadata entry point. FOUR of the five, not four of four — a provision's `:-
//! Spec[…]` condition is the fifth, re-judged by a mechanism of its own (a per-scope
//! clause index) and driven by `a_check_less_load_claims_the_clauses_it_wrote` instead.
//!
//! AND THE ENTRY POINT THAT RUNS NO CHECK HANDS ON NOTHING (`a_check_less_load_entry_point_…`,
//! `a_check_less_load_claims_the_clauses_it_wrote`, `…_claims_a_row_it_derived_too`): a
//! `run_typer: false` load stops above every check, so leaving either of the two
//! registries a check reads changed hands the next batch a refusal about a file it was
//! never given — measured for both. The SITE half is a restore (`restore_load_check_marks`).
//! The CLAUSE half is a run of THIS CHECK'S OWN WALK that claims and judges nothing
//! (`typing::RowBindingRun::ClaimOnly`, WI-20260901-47VWX), because the population is
//! everything the check would judge and not everything the loader wrote: two earlier
//! shapes keyed on a producer — restore what the load un-claimed (WI-20260901-EA6KS),
//! then also claim what its declaration walk presented — and each was a writer census the
//! next writer escaped, the last being `derive_forwarded_provisions`, which is not in the
//! loader at all.
//!
//! A FACT-SOURCED REFUSAL CARRIES NO SPAN, and the two candidate lookups were built and
//! measured answering `None` rather than argued away: `functor_span` keys off a converted
//! `Term::Fn` functor (an APPLIED name, not a declaration) and `rule_head_span` is empty
//! for a loader-emitted metadata fact. Those refusals name the owner and the clause
//! keyword; a SITE-sourced one carries `path:line:col`.
//!
//! ## What fails when it is backed out — MEASURED, one back-out at a time
//!
//! ```text
//!   back-out                                   reds
//!   ────────────────────────────────────────── ─────────────────────────────────────────
//!   source 1 (`sites` emptied)                 a_row_type_argument_… (both)
//!                                              a_row_nested_inside_a_provides_…
//!                                              a_denoted_element_…
//!                                              a_type_parameter_binding_… (refusal half)
//!                                              a_nullary_ambient_place_… (refusal half)
//!                                              census: the 12 rows marked `site`
//!                                              RSRP5: ALL SIX GREEN
//!   source 2 (spec-clause loop emptied)        RSRP5's three route-A tests
//!                                              census rows 15, 16, 18
//!                                              a_row_nested_inside_a_provides_… GREEN
//!   source 3 (contract-clause loop emptied)    census row 19, both spellings — and
//!                                              NOTHING ELSE
//!   the site carrier widening (ground-only)    a_denoted_element_… — and nothing else
//!   the `is_sort_param_symbol` exemption       EIGHT tests across both files: every
//!     (`if false && …`)                        "must load" one, in both directions.
//!                                              The prelude stops loading.
//!   the dedup key's `origin` (blanked)         two_clause_kinds_on_one_owner_… — and
//!                                              NOTHING else. RSRP5's own slot-axis test
//!                                              stays green, because `param` is still in
//!                                              the key: two axes, two tests.
//!   `claim_row_binding_clause` (always `true`) a_later_load_re_reports_… (its UNRELATED
//!                                              batch goes to 4) AND all three check-less
//!                                              tests, whose whole point is that a batch
//!                                              skips what it did not present. "And
//!                                              nothing else" stood here until
//!                                              WI-20260901-47VWX added them and
//!                                              /code-review noticed the row had not
//!                                              moved; re-measured, 4 reds.
//!   `note_metadata_fact_presented` (inert)     a_later_load_re_reports_… (its
//!                                              RE-PRESENTED batch goes to 0),
//!                                              …_claims_the_clauses_it_wrote (its batch
//!                                              4 goes 5 → 1) and …_claims_a_row_it_
//!                                              derived_too (its batch 4 goes 1 → 0).
//!                                              Its call sites back out separately, one
//!                                              route each: see that test's own table.
//!                                              THE ONE SURVIVOR IS THE CONDITION ROUTE,
//!                                              and it is not a hole in the drop: a
//!                                              `ProvidesConditionInfo` head carries a
//!                                              per-scope CLAUSE INDEX
//!                                              (`provides_clause_seen`, never reset per
//!                                              load), so a re-presented file mints a
//!                                              structurally NEW fact with a fresh
//!                                              RuleId rather than dedup-hitting — it
//!                                              needs no un-claiming to be judged again.
//!   `restore_load_check_marks`'s truncate      a_check_less_load_entry_point_… (site
//!                                              half) — and nothing else
//!   `claim_written_row_bindings` (call removed) a_check_less_load_entry_point_… (clause
//!                                              half, 2), a_check_less_load_claims_the_
//!                                              clauses_it_wrote (5) and …_claims_a_row_
//!                                              it_derived_too (2) — and nothing else,
//!                                              measured over the whole workspace.
//!                                              Three populations, one line.
//! ```
//!
//! TWO ROWS EARN THEIR PLACE BY WHAT THEY LEAVE GREEN. Source 2's back-out leaves
//! `a_row_nested_inside_a_provides_binding_is_judged` passing, which is what says a row
//! nested inside a `provides` clause arrives as a SITE and not through the provision walk
//! — the distinction the whole three-source split rests on. And source 1's back-out
//! leaves every RSRP5 test passing, which is what says this ticket added an origin rather
//! than changing the rule.
//!
//! `an_operation_bracket_parameter_in_a_row_binding_names_no_kind` is the exemption's own
//! fixture, in eight lines, so the reason it exists is readable without reading a prelude
//! combinator. It passes both ways for sources 1 and 2 by design — a type parameter in
//! scope lowers to a `Term::Var` there, so those sources never ask — and is load-bearing
//! for source 3 alone.
//!
//! TWO TESTS ARE MIXED, not pure controls, and their names say only half of what they do:
//! `a_type_parameter_binding_in_a_signature_is_not_read_as_an_effect_row` and
//! `a_nullary_ambient_place_in_a_row_type_argument_still_loads` each pair a must-LOAD half
//! (the control) with a must-REFUSE half (coverage), because a control for a refusal's
//! WIDTH is only worth having beside the refusal it bounds.
//!
//! ONE PURE CONTROL: `a_registered_kind_in_a_row_type_argument_still_loads` passes under
//! every back-out above except the exemption's, and that is the point — it is what says
//! the refusals are about the LABEL, not about writing a row at a signature at all.

use crate::common::try_load_kb_with_files;

/// The load diagnostics for the stdlib plus these sources, empty when it loads.
fn load_errors(srcs: &[&str]) -> Vec<String> {
    try_load_kb_with_files(srcs).err().unwrap_or_default()
}

fn expect_refused(what: &str, needles: &[&str], srcs: &[&str]) {
    let errs = load_errors(srcs);
    for needle in needles {
        assert!(
            errs.iter().any(|e| e.contains(needle)),
            "{what}: expected a refusal containing `{needle}`; got: {errs:#?}"
        );
    }
}

fn expect_loads(what: &str, srcs: &[&str]) {
    let errs = load_errors(srcs);
    assert!(errs.is_empty(), "{what} must load; got: {errs:#?}");
}

const OUT: &str = r#"
namespace test.v25n3.out
  import anthill.prelude.{String}
  sort Out
    entity out(v: String)
  end
end
"#;

/// The ticket's spec, verbatim in shape: a row parameter, a carrier-param receiver, and
/// no carrier — the shape WI-20260831-PYNS2 made loadable, and the one the ticket's two
/// fixtures are written against.
const SPEC: &str = r#"
namespace test.v25n3.spec
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  sort Spec
    sort C = ?
    effects E = ?
    operation go(self: C, p: String) -> Out
      effects {E, Error} = out(v: p)
  end
end
"#;

/// THE TICKET'S FIRST FIXTURE — an UNREGISTERED kind written in a parameter's row
/// type-argument.
///
/// The refusal must name the SLOT AS WRITTEN (`Spec`'s `E`), not just the label: an
/// author who wrote two row parameters cannot fix the right one otherwise, and the same
/// label may be lawful in the other.
///
/// BACKED OUT (source 1 skipped): red. Its `provides` twin — RSRP5's
/// `a_provision_row_binding_may_not_name_an_unregistered_kind_in_either_spelling` — stays
/// green, which is what dates this as the SIGNATURE origin rather than the rule.
#[test]
fn a_row_type_argument_on_a_parameter_may_not_name_an_unregistered_kind() {
    let src = r#"
namespace test.v25n3.reg
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.spec.{Spec}
  sort Beep
    entity beep
  end
  operation ask(s: Spec[E = {Beep}], p: String) -> Out
    effects {s.E, Error} = Spec.go(s, p)
end
"#;
    expect_refused(
        "an unregistered kind in a parameter's row type-argument",
        &[
            "is not a REGISTERED effect kind",
            "effect-row parameter `E`",
            "test.v25n3.spec.Spec",
        ],
        &[OUT, SPEC, src],
    );
}

/// THE TICKET'S SECOND FIXTURE — a TYPE-targeted `Modify` in the same position.
///
/// BACKED OUT (source 1 skipped): red.
#[test]
fn a_row_type_argument_on_a_parameter_may_not_name_a_type_targeted_modify() {
    let src = r#"
namespace test.v25n3.mt
  import anthill.prelude.{Error, String, Modify, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.spec.{Spec}
  sort Thing
    entity thing(v: String)
  end
  operation ask(s: Spec[E = {Modify[Thing]}], p: String) -> Out
    effects {s.E, Error} = Spec.go(s, p)
end
"#;
    expect_refused(
        "a type-targeted `Modify` in a parameter's row type-argument",
        &["whose target is a TYPE", "effect-row parameter `E`"],
        &[OUT, SPEC, src],
    );
}

/// THE BENIGN CONTROL — a row naming a REGISTERED kind must still load, in exactly the
/// position the two tests above refuse.
///
/// THE ONE PURE CONTROL IN THIS FILE. It passes under every back-out except the
/// type-parameter exemption's (which stops the prelude loading and reds everything), by
/// design: it is what says the refusals are about the LABEL and not about writing a row
/// at a signature at all.
#[test]
fn a_registered_kind_in_a_row_type_argument_still_loads() {
    let src = r#"
namespace test.v25n3.ok
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.spec.{Spec}
  operation ask(s: Spec[E = {Error}], p: String) -> Out
    effects {s.E, Error} = Spec.go(s, p)
end
"#;
    expect_loads(
        "a registered kind in a parameter's row type-argument",
        &[OUT, SPEC, src],
    );
}

/// THE FALSE-POSITIVE CONTROL, AT THE NEW SITE — RSRP5's
/// `a_type_parameter_binding_is_not_read_as_an_effect_row` re-driven where this ticket
/// added a source.
///
/// `Spec[C = Int64]` binds a TYPE parameter. `Int64` is neither a registered effect kind
/// nor a place, so a source that judged EVERY binding would refuse it — the exact failure
/// a value-shape filter and a naive "judge all bindings" both produce. It must load, and
/// the row binding beside it must still be judged (asserted by the `E = {Boop}` half).
///
/// A MIXED TEST, not a pure control. The must-LOAD half passes under every back-out in
/// this file and guards a future widening of `effect_row_params_of_spec`, the only thing
/// that could make it red; the must-REFUSE half beside it is source-1 coverage and reds
/// with that source. They are together because a control for a refusal's WIDTH is only
/// worth having beside the refusal it bounds.
#[test]
fn a_type_parameter_binding_in_a_signature_is_not_read_as_an_effect_row() {
    let good = r#"
namespace test.v25n3.tp
  import anthill.prelude.{Error, String, Int64, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  import test.v25n3.spec.{Spec}
  operation ask(s: Spec[C = Int64, E = {Error}], p: String) -> Out
    effects {Error} = out(v: p)
end
"#;
    let bad = r#"
namespace test.v25n3.tp2
  import anthill.prelude.{Error, String, Int64, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  import test.v25n3.spec.{Spec}
  sort Boop
    entity boop
  end
  operation ask2(s: Spec[C = Int64, E = {Boop}], p: String) -> Out
    effects {Error} = out(v: p)
end
"#;
    expect_loads(
        "a TYPE-parameter binding beside a lawful row binding, at a signature",
        &[OUT, SPEC, good],
    );
    expect_refused(
        "the row binding beside a TYPE-parameter binding is still judged",
        &[
            "is not a REGISTERED effect kind",
            "effect-row parameter `E`",
        ],
        &[OUT, SPEC, bad],
    );
}

/// A LAWFUL `Modify` PLACE IN A ROW TYPE-ARGUMENT STILL LOADS — the control that keeps
/// the type-target refusal from being read as "a row type-argument may not mention
/// `Modify`", and that dates the repair the diagnostic offers.
///
/// §5.6's one place-form available where there is no parameter list is a NULLARY
/// CONSTRUCTOR naming an ambient resource, which is what the message tells the author to
/// write. A MIXED TEST (see the header): its second half is source-1 coverage.
/// MEASURED: the sort-nested `entity clock` under `fact Modifiable[T = Clock]` loads. The FREE-STANDING spelling does NOT (`entity clock` at namespace level is its
/// own sort, WI-926, so `is_ambient_resource_name` excludes it as an EPONYMOUS
/// constructor — WI-20260823-4GBQV's own rule), and that half is asserted too, because a
/// message advising a form that does not work is the defect /code-review found in this
/// diagnostic's RSRP5 ancestor.
#[test]
fn a_nullary_ambient_place_in_a_row_type_argument_still_loads() {
    let place = r#"
namespace test.v25n3.pl
  import anthill.prelude.{Error, String, Modify, Modifiable, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  import test.v25n3.spec.{Spec}
  sort Clock
    entity clock
  end
  fact Modifiable[T = Clock]
  import test.v25n3.pl.Clock.{clock}
  operation ask(s: Spec[E = {Modify[clock]}], p: String) -> Out
    effects {Error} = out(v: p)
end
"#;
    let eponymous = r#"
namespace test.v25n3.ep
  import anthill.prelude.{Error, String, Modify, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  import test.v25n3.spec.{Spec}
  entity clockep
  operation ask(s: Spec[E = {Modify[clockep]}], p: String) -> Out
    effects {Error} = out(v: p)
end
"#;
    expect_loads(
        "a `Modify` over a sort-nested nullary ambient constructor, in a row type-argument",
        &[OUT, SPEC, place],
    );
    expect_refused(
        "a `Modify` over a FREE-STANDING (eponymous) nullary entity",
        &["whose target is a TYPE"],
        &[OUT, SPEC, eponymous],
    );
}

/// A ROW NESTED INSIDE A `provides` BINDING — a hole in route A itself, found by this
/// ticket's census and closed by it.
///
/// `provides Box[T = Spec[E = {Beep}]]` binds `Box`'s TYPE parameter `T`, so RSRP5's
/// provision walk — which filters to the provided spec's OWN row parameters — never
/// looked inside. MEASURED loading clean before. It arrives as a SITE: the outer
/// `provides` is `sort_inst_to_value`'s, but its nested binding value goes through
/// `sort_binding_to_value`, which records.
///
/// BACKED OUT (source 1 skipped): red. Backing out source 2 leaves it GREEN, which is
/// what says this row is the SITE source's and not the provision walk's.
#[test]
fn a_row_nested_inside_a_provides_binding_is_judged() {
    let src = r#"
namespace test.v25n3.nest
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.spec.{Spec}
  sort BeepN
    entity beepn
  end
  sort BoxN
    sort T = ?
  end
  sort CN
    import test.v25n3.nest.{BeepN}
    entity cn(t: String)
    provides BoxN[T = Spec[E = {BeepN}]]
  end
end
"#;
    expect_refused(
        "a row nested inside a provides binding",
        &[
            "is not a REGISTERED effect kind",
            "effect-row parameter `E`",
        ],
        &[OUT, SPEC, src],
    );
}

/// A DENOTED ELEMENT DOES NOT HIDE ITS NEIGHBOURS — the fixture the
/// [`crate::kb::ParameterizedSite`] carrier widening exists for.
///
/// One `denoted` element poisons the whole row to a `Value::Node`, and the site registry
/// recorded GROUND bindings only — so `Spec[E = {Beep, Modify[clock]}]` dropped its entire
/// `E` binding and the unregistered `Beep` beside the LAWFUL place went unjudged.
/// MEASURED loading clean, while the identical row in a `provides` clause was refused.
///
/// BACKED OUT (the recorded bindings narrowed back to `TypeChild::Ground`): red, and
/// `a_row_type_argument_…_unregistered_kind` stays green — the two differ only by the
/// lawful `Modify` beside the bad label.
#[test]
fn a_denoted_element_does_not_hide_a_bad_label_beside_it() {
    let src = r#"
namespace test.v25n3.den
  import anthill.prelude.{Error, String, Modify, Modifiable, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  import test.v25n3.spec.{Spec}
  sort BeepD
    entity beepd
  end
  sort ClockD
    entity clockd
  end
  fact Modifiable[T = ClockD]
  import test.v25n3.den.ClockD.{clockd}
  operation ask(s: Spec[E = {BeepD, Modify[clockd]}], p: String) -> Out
    effects {Error} = out(v: p)
end
"#;
    expect_refused(
        "an unregistered kind beside a lawful denoted place",
        &["is not a REGISTERED effect kind", "BeepD"],
        &[OUT, SPEC, src],
    );
}

/// AN OPERATION'S BRACKET PARAMETER NAMES NO KIND — §5.5's "a row variable the checker
/// has opened", driven on a minimal program.
///
/// A SORT parameter carries a `SortAlias(P, Var)` fact, so the label walk follows it to a
/// variable and asks nothing. An OPERATION's bracket parameter carries no such fact — its
/// variable lives in the op's own record — so through the CONTRACT-CLAUSE source (whose
/// items the GOAL converter builds, where a type parameter stays a `Ref`) it arrives as an
/// ordinary sort reference and would be refused for not being a registered kind.
///
/// NOT HYPOTHETICAL: without the exemption the prelude's own `map[…, EffS, …] requires
/// Iterable[C = Sc, Element = S, E = EffS]` is refused, so EVERY program that loads the
/// prelude fails. This fixture is the same shape in eight lines.
#[test]
fn an_operation_bracket_parameter_in_a_row_binding_names_no_kind() {
    let src = r#"
namespace test.v25n3.opp
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  import test.v25n3.spec.{Spec}
  operation ask[Eff](p: String) -> Out
    requires Spec[E = Eff]
    effects {Error} = out(v: p)
end
"#;
    expect_loads(
        "an operation bracket parameter bound to a spec's row parameter",
        &[OUT, SPEC, src],
    );
}

/// AN OPERATION TYPE-PARAMETER DEFAULT — the one census position NOT covered, with its
/// reason MEASURED rather than assumed.
///
/// `operation f[T = Spec[E = {Beep}]](…)` is refused BEFORE any row can be judged: a
/// default on an operation's bracket parameter is a load error in its own right, because
/// nothing reads it. So the position exists in the grammar and carries no program for a
/// row-label gate to have a verdict about.
///
/// Asserted here rather than left as prose so the exemption expires loudly: if that
/// refusal is ever lifted, this test reds and the position needs covering.
#[test]
fn an_operation_type_parameter_default_is_refused_before_a_row_is_judged() {
    let src = r#"
namespace test.v25n3.dflt
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  import test.v25n3.spec.{Spec}
  sort BeepDf
    entity beepdf
  end
  operation ask[T = Spec[E = {BeepDf}]](p: String) -> Out
    effects {Error} = out(v: p)
end
"#;
    let err = anthill_core::parse::parse(src).expect_err("a bracket-param default is refused");
    let rendered = format!("{err:?}");
    assert!(
        rendered.contains("carries a default") && rendered.contains("which nothing reads"),
        "expected the bracket-param-default refusal; got: {rendered}"
    );
}

/// ONE POSITION, ONE FIXTURE, ONE REFUSAL — the census this ticket's work actually was.
///
/// Every row writes the SAME unregistered label into the SAME spec's SAME row parameter,
/// so the only thing that varies is WHERE it is written. The count is asserted per row
/// (not summed) because a summed count is satisfied by one position firing twice, which
/// is exactly the failure a census is supposed to catch.
///
/// EACH ROW NAMES ITS SOURCE, and the three back-outs in this file's header are per
/// source, so a row's failure says which loop lost it.
#[test]
fn every_type_position_a_row_can_be_written_in_is_judged() {
    // (label, source, program). The label is the census row from this file's header.
    let cases: &[(&str, &str, String)] = &[
        (
            "02 operation RETURN type",
            "site",
            // A BODY-LESS spec op, so the row is written at the RETURN and NOWHERE
            // ELSE. The first cut wrote `mk(s: Spec[E = {B}]) -> Spec[E = {B}]` and
            // reported TWICE — two written positions, two refusals, correct behaviour
            // and a useless census row. Caught by the exactly-once assertion below,
            // which is what that assertion is for. (/code-review)
            fixture(
                "r02",
                "sort Holder2\n    import test.v25n3.c.r02.{B}\n    sort C = ?\n    operation mk(self: C) -> Spec[E = {B}]\n      effects {Error}\n  end",
            ),
        ),
        (
            "03 ENTITY FIELD type (sort-nested)",
            "site",
            fixture(
                "r03",
                "sort Holder\n    import test.v25n3.c.r03.{B}\n    entity holder(s: Spec[E = {B}])\n  end",
            ),
        ),
        (
            "04 ENTITY FIELD type (free-standing, §6.3)",
            "site",
            fixture("r04", "entity holder4(s: Spec[E = {B}])"),
        ),
        (
            "05 `sort S = Spec[…]` alias",
            "site",
            fixture("r05", "sort Alias5 = Spec[E = {B}]"),
        ),
        (
            "06 nested in an alias",
            "site",
            fixture("r06", "sort Alias6 = List[T = Spec[E = {B}]]"),
        ),
        (
            "07 a sort's own `sort S = …` member",
            "site",
            fixture(
                "r07",
                "sort Wrap7\n    import test.v25n3.c.r07.{B}\n    sort S = Spec[E = {B}]\n    entity w7(t: String)\n  end",
            ),
        ),
        (
            "08 a `const`'s declared type",
            "site",
            fixture("r08", "const k8: Spec[E = {B}] = ?"),
        ),
        (
            "09 a body `let` annotation",
            "site",
            fixture(
                "r09",
                "operation ask9(s: Spec[E = {Error}], p: String) -> Out\n    effects {Error} =\n      let t: Spec[E = {B}] = s\n      out(v: p)",
            ),
        ),
        (
            "10 a typed LAMBDA binder",
            "site",
            fixture(
                "r10",
                "operation ask10(p: String) -> Out\n    effects {Error} =\n      let f = lambda (x: Spec[E = {B}]) -> out(v: p)\n      out(v: p)",
            ),
        ),
        (
            "11 nested in another instantiation",
            "site",
            fixture(
                "r11",
                "operation ask11(ss: List[T = Spec[E = {B}]], p: String) -> Out\n    effects {Error} = out(v: p)",
            ),
        ),
        (
            "12 an ARROW parameter type",
            "site",
            fixture(
                "r12",
                "operation ask12(f: (Spec[E = {B}]) -> Out, p: String) -> Out\n    effects {Error} = out(v: p)",
            ),
        ),
        (
            "13 a TUPLE component",
            "site",
            fixture(
                "r13",
                "operation ask13(pr: (Spec[E = {B}], String), p: String) -> Out\n    effects {Error} = out(v: p)",
            ),
        ),
        (
            "15 a sort's `requires Spec[…]`",
            "spec clause",
            fixture(
                "r15",
                "sort Needs15\n    import test.v25n3.c.r15.{B}\n    requires Spec[E = {B}]\n    entity n15(t: String)\n  end",
            ),
        ),
        (
            "16 a sort's `requires B: Spec[…]` (named binder)",
            "spec clause",
            fixture(
                "r16",
                "sort Needs16\n    import test.v25n3.c.r16.{B}\n    requires S16: Spec[E = {B}]\n    entity n16(t: String)\n  end",
            ),
        ),
        (
            "18 a `provides X :- Spec[…]` condition",
            "spec clause",
            fixture(
                "r18",
                "sort Other18\n    sort C = ?\n  end\n  sort C18\n    import test.v25n3.c.r18.{B}\n    entity c18(t: String)\n    provides Other18[C = String] :- Spec[E = {B}]\n  end",
            ),
        ),
        (
            "19 an operation's `requires`",
            "contract clause",
            fixture(
                "r19",
                "operation ask19(p: String) -> Out\n    requires Spec[E = {B}]\n    effects {Error} = out(v: p)",
            ),
        ),
        (
            "19 an operation's `requires b: …` (named binder)",
            "contract clause",
            fixture(
                "r19b",
                "operation ask19b(p: String) -> Out\n    requires s19: Spec[E = {B}]\n    effects {Error} = out(v: p)",
            ),
        ),
    ];
    let mut wrong: Vec<String> = Vec::new();
    for (label, source, program) in cases {
        let errs = load_errors(&[OUT, SPEC, program]);
        let hits = errs
            .iter()
            .filter(|e| e.contains("is not a REGISTERED effect kind"))
            .count();
        // EXACTLY ONE, not at-least-one (/code-review). Each program writes the label
        // ONCE, so a count of 2 means two sources both claimed it — the overlap the
        // three-source split exists to avoid, and the thing a presence-only assertion
        // cannot see. A count of 0 means the position is judged by nothing.
        if hits != 1 {
            wrong.push(format!("[{source}] {label}: {hits} refusal(s)"));
            eprintln!("CENSUS MISS [{source}] {label} ({hits} hits)\n  errors: {errs:#?}");
        }
    }
    assert!(
        wrong.is_empty(),
        "each position must be judged EXACTLY ONCE; these were not: {wrong:#?}"
    );
}

/// One census program: the shared preamble plus `item`, writing the unregistered label
/// `B` into `Spec`'s row parameter. Each case gets its OWN namespace so a bad label in
/// one cannot be reported for another.
fn fixture(ns: &str, item: &str) -> String {
    format!(
        r#"
namespace test.v25n3.c.{ns}
  import anthill.prelude.{{Error, String, List, EffectsRuntime}}
  import test.v25n3.out.{{Out}}
  import test.v25n3.out.Out.{{out}}
  import test.v25n3.spec.{{Spec}}
  sort B
    entity b
  end
  {item}
end
"#
    )
}

/// TWO CLAUSE KINDS ON ONE OWNER, TWO REFUSALS — the dedup key's own axis.
///
/// The first cut keyed on the OWNER SYMBOL, so a sort writing the same bad label in
/// `provides Spec[E = {Beep}]` AND `requires Spec[E = {Beep}]` reported ONCE, naming only
/// the `provides` — MEASURED — and an author who fixed that met the other on the next
/// load. Same collapse for one operation writing it under `requires` and `ensures`. The
/// key is the rendered ORIGIN now, which is exactly as fine as the message.
///
/// This is RSRP5's `each_bad_row_parameter_is_reported_against_its_own_slot` on the other
/// axis: that one separates two SLOTS of one clause, this one two CLAUSES of one owner.
///
/// BACKED OUT (the key's `origin` replaced by the owner symbol): both halves red at 1
/// refusal instead of 2. (/code-review)
#[test]
fn two_clause_kinds_on_one_owner_are_each_reported() {
    let sort_level = r#"
namespace test.v25n3.two
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.spec.{Spec}
  sort BeepT
    entity beept
  end
  sort Both
    import test.v25n3.two.{BeepT}
    entity both(t: String)
    requires Spec[E = {BeepT}]
    provides Spec[E = {BeepT}]
  end
end
"#;
    let op_level = r#"
namespace test.v25n3.twob
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  import test.v25n3.spec.{Spec}
  sort BeepU
    entity beepu
  end
  operation ask(p: String) -> Out
    requires Spec[E = {BeepU}]
    ensures Spec[E = {BeepU}]
    effects {Error} = out(v: p)
end
"#;
    for (what, src, kinds) in [
        (
            "a sort's `requires` beside its `provides`",
            sort_level,
            ["provides", "requires"],
        ),
        (
            "an operation's `requires` beside its `ensures`",
            op_level,
            ["`requires` clause", "`ensures` clause"],
        ),
    ] {
        let errs = load_errors(&[OUT, SPEC, src]);
        let rows: Vec<&String> = errs
            .iter()
            .filter(|e| e.contains("is not a REGISTERED effect kind"))
            .collect();
        assert_eq!(
            rows.len(),
            2,
            "{what}: one refusal per clause; got: {errs:#?}"
        );
        for kind in kinds {
            assert!(
                rows.iter().any(|e| e.contains(kind)),
                "{what}: expected one naming `{kind}`; got: {rows:#?}"
            );
        }
    }
}

/// A CHECK-LESS LOAD RECORDS NO LOAD-CHECK WORK.
///
/// `LoadOptions { run_typer: false }` stops the phase before the typer, so none of the
/// checks below that line run over what it loaded. (It was `load::load` — a separate
/// single-file entry point — until WI-20260901-Q68AK folded the partial shape into an
/// option on the one pipeline; the rule and both measurements are unchanged, and the
/// registries are settled at the same place.) Two registries the walk
/// writes are read only by a check, and leaving either changed hands the NEXT batch work
/// it did not do: measured, a `load_all` into a live KB of one unrelated clean sort failed with
/// refusals naming a file it was never given. Both halves are asserted here because they
/// are two registries with one rule, and they came from opposite directions
/// (/code-review).
///
/// ```text
///   half                          back-out                       unrelated batch reports
///   ───────────────────────────── ────────────────────────────── ───────────────────────
///   judged_row_binding_clauses    `claim_written_row_bindings`,   2  (was 0)
///                                 the call removed
///   parameterized_type_sites      `restore_load_check_marks`'s    1  (was 0)
///                                 truncate line
/// ```
///
/// THIS ARM'S OFFENDER IS LOADED IN BATCH 1 FIRST, so every clause its check-less load
/// presents is a DEDUP HIT on a RuleId that was already claimed. That is one of THREE
/// populations, and it used to be the only one the repair addressed — a snapshot of
/// `judged_row_binding_clauses`, restored at the return, which put back exactly the
/// claims the presentation had dropped. The other two are clauses the check-less load
/// CREATES: one it wrote (`a_check_less_load_claims_the_clauses_it_wrote`) and one it
/// derived (`…_claims_a_row_it_derived_too`), whose fresh RuleIds no snapshot could hold.
/// All three are settled by one `ClaimOnly` run of this check's own walk
/// (WI-20260901-47VWX), which is why the snapshot went: a clause whose claim the load
/// dropped is a clause the walk re-claims, so restoring it first was measured changing no
/// row of the workspace suite.
///
/// THE TWO HALVES HAVE DIFFERENT HISTORIES, and saying so is the point. The claim half is
/// a regression introduced by WI-20260901-EA6KS itself — the walk now DROPS claims and
/// only the check re-adds them — and backing that drop out takes its row to 0. The site
/// half is PRE-EXISTING, measured identical with the drop backed out: `load`'s sites
/// simply waited in a push-only registry until the next batch drained them. It is fixed
/// beside the other because otherwise the same check's source 1 and source 2 answer "what
/// does `load` mean" two different ways.
///
/// NOT A SUPPRESSION: this entry point ran no checks before or after, so nothing that was
/// reported stops being reported. What stops is charging it to the wrong batch — which is
/// the rule `a_later_load_re_reports_…` states for the other producers.
#[test]
fn a_check_less_load_entry_point_records_no_load_check_work() {
    use anthill_core::kb::load::{self, NullResolver};
    use anthill_core::kb::KnowledgeBase;
    use anthill_core::parse;

    // The CLAUSE half: two spec clauses, both offending — the `judged_row_binding_clauses`
    // route, which `load` un-claims and never re-claims.
    let clauses = r#"
namespace test.v25n3.solo
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.spec.{Spec}
  sort BeepS
    entity beeps
  end
  sort CS
    import test.v25n3.solo.{BeepS}
    entity cs(t: String)
    requires Spec[E = {BeepS}]
    provides Spec[E = {BeepS}]
  end
end
"#;
    // The SITE half: a row written as a type argument in a signature — source 1, whose
    // registry `load` fills and no check of its own drains.
    let site = r#"
namespace test.v25n3.solo2
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  import test.v25n3.spec.{Spec}
  sort BeepT2
    entity beept2
  end
  operation askS(s: Spec[E = {BeepT2}], p: String) -> Out
    effects {Error} = out(v: p)
end
"#;
    let unrelated = r#"
namespace test.v25n3.solo3
  import anthill.prelude.{String}
  sort LaterS
    entity laters(t: String)
  end
end
"#;
    let judged = |errs: &[String]| {
        errs.iter()
            .filter(|e| e.contains("is not a REGISTERED effect kind"))
            .count()
    };
    let errs_of = |r: Result<load::LoadResult, Vec<load::LoadError>>| -> Vec<String> {
        match r {
            Ok(_) => vec![],
            Err(e) => e.iter().map(|x| x.to_string()).collect(),
        }
    };

    for (half, offender, expected_in_batch_one) in
        [("clause", clauses, 2usize), ("site", site, 0usize)]
    {
        let dir = crate::common::stdlib_dir();
        let mut parsed: Vec<_> = crate::common::collect_anthill_files(&dir)
            .iter()
            .map(|p| {
                parse::parse(&std::fs::read_to_string(p).expect("read stdlib"))
                    .expect("parse stdlib")
            })
            .collect();
        for extra in [OUT, SPEC] {
            parsed.push(parse::parse(extra).expect("parse extra"));
        }
        // The CLAUSE half loads its offender in batch 1 too, so the claim it needs to
        // leave behind exists to be dropped; the SITE half must NOT, because a site is
        // judged in the batch that wrote it and the question is what a later batch
        // inherits from `load` alone.
        if expected_in_batch_one > 0 {
            parsed.push(parse::parse(offender).expect("parse offender"));
        }
        let refs: Vec<_> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        let first = errs_of(load::load_all(&mut kb, &refs, &NullResolver));
        assert_eq!(
            judged(&first),
            expected_in_batch_one,
            "{half}: batch 1 baseline; got: {first:#?}"
        );

        let solo = parse::parse(offender).expect("parse offender");
        let mid = errs_of(load::load_all_with(
            &mut kb,
            &[&solo],
            &NullResolver,
            load::LoadOptions {
                run_typer: false,
                ..Default::default()
            },
        ));
        assert_eq!(
            judged(&mid),
            0,
            "{half}: a partial load runs no load check, so it reports none of these itself; \
             got: {mid:#?}"
        );

        let later = parse::parse(unrelated).expect("parse later");
        let third = errs_of(load::load_all(&mut kb, &[&later], &NullResolver));
        assert_eq!(
            judged(&third),
            0,
            "{half}: a batch of one unrelated sort must not inherit the partial load's work; \
             got: {third:#?}"
        );
    }
}

/// A LATER LOAD RE-REPORTS A RE-PRESENTED CLAUSE, AND ONLY THAT ONE.
///
/// Two of the three sources walk the WHOLE KB — only the site registry is drained per
/// load — so the walk needs a per-fact boundary of its own, and it has two questions to
/// answer with one, which is why BOTH directions are asserted here and each is the
/// other's control:
///
/// * A BATCH THAT PRESENTS NOTHING must report nothing. Without
///   `claim_row_binding_clause`, a `load_all` into a live KB of a clean unrelated file into a KB
///   that already holds an offending clause re-reported it — a batch failing over a file
///   it was never given (WI-20260831-V25N3, measured).
/// * A BATCH THAT RE-PRESENTS THE FILE must report it again. The claim alone gets this
///   WRONG, and shipped wrong: an assert DEDUPS, so re-loading the very file that wrote
///   the clause lands on the RuleId already claimed, and the same unchanged file came
///   back `Ok` with zero errors — a load-blocking refusal lost
///   (WI-20260901-EA6KS, measured). `note_metadata_fact_presented` is the repair.
///
/// A pass with EITHER direction alone is trivially available — claim nothing, or claim
/// everything — so neither assertion means anything without the other, and the first
/// shipped without the second.
///
/// FOUR CLAUSE ROUTES — one per producer of the facts sources 2 and 3 read THAT THIS
/// REPAIR IS LOAD-BEARING FOR, which is not the same as one per producer. There are five:
/// `SortProvidesInfo` has two loader producers, `SortRequiresInfo` and `OperationInfo` one
/// each, and `ProvidesConditionInfo` is the fifth. The fifth is deliberately absent here,
/// and WI-20260901-47VWX is what measured why: a condition head carries a per-scope CLAUSE
/// INDEX (`provides_clause_seen`, never reset per load), so a re-presented file mints a
/// structurally NEW fact with a fresh RuleId instead of dedup-hitting the claimed one — it
/// is judged again whether or not anything un-claims it. Putting it in this fixture would
/// make the table below read "every refusal but one" and credit the drop with a row it
/// does not carry. It IS driven, by `a_check_less_load_claims_the_clauses_it_wrote`, whose
/// question the index does not answer. Backed out ONE AT A TIME:
///
/// ```text
///   back-out                                           what the RE-PRESENTED batch loses
///   ────────────────────────────────────────────────── ────────────────────────────────
///   `claim_row_binding_clause` (always `true`)         nothing — it fails EARLIER, on
///                                                      the UNRELATED batch, which goes
///                                                      from 0 to 4. The other direction.
///   `note_metadata_fact_presented` (body emptied)      every refusal
///   … its `assert_metadata_fact_carrier` call alone    the sort's `provides`, and the
///                                                      `fact Spec[…]` provider with it
///   … its `assert_metadata_fact`/`_value` calls alone  the operation's `requires`
///   … its `resolve_requires_bindings` call alone       the sort's `requires`
///   `maybe_emit_fact_provides_info` back on            the `fact Spec[…]` provider
///     `assert_fact_carrier`                            alone
/// ```
///
/// The whole-repair row is measured against the WORKSPACE suite, not just this binary:
/// 6249 pass and this one test fails.
///
/// THE FOURTH ROUTE IS WHY THIS COUNTS PRODUCERS AND NOT CLAUSE KINDS. `SortProvidesInfo`
/// has two loader producers, not one — `load_provides_clause` for the `provides` keyword
/// and `maybe_emit_fact_provides_info` for a `fact Spec[…]` provider declaration — and
/// only the first went through the metadata entry point, so the first cut of this repair
/// covered three routes and left the fourth exactly as broken as it found it (measured;
/// /code-review). A per-KEYWORD census would not have found it.
///
/// The sort-level `requires` is the one that needs the `resolve_requires_bindings` site:
/// its fact is asserted by the item walk and then RETRACTED and re-asserted by that pass
/// onto a dedup hit against the earlier batch's live completed head, so the loader's own
/// presentation lands on a transient id and the surviving one carries the old claim.
#[test]
fn a_later_load_re_reports_a_re_presented_clause_and_not_an_unrelated_one() {
    use anthill_core::kb::load::{self, NullResolver};
    use anthill_core::kb::KnowledgeBase;
    use anthill_core::parse;

    // ONE FILE, FOUR ROUTES: a sort's `requires` (the retract-and-re-assert route), its
    // `provides` (a plain metadata-carrier assert), an operation's `requires` (the
    // `OperationInfo` fact) and a `fact Spec[…]` provider declaration
    // (`maybe_emit_fact_provides_info`, the fourth `SortProvidesInfo` producer and the
    // one that was still bypassing the metadata entry point).
    //
    // `DI` IS A SECOND CARRIER ON PURPOSE. The dedup key is the rendered ORIGIN, and a
    // `fact Spec[C = CI, …]` renders as `CI provides Spec` — the same string the sort's
    // own `provides` clause renders as — so writing both on ONE carrier collapses them to
    // a single refusal and the route goes invisible whether or not it works.
    let bad = r#"
namespace test.v25n3.inc
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  import test.v25n3.spec.{Spec}
  sort BeepI
    entity beepi
  end
  sort CI
    import test.v25n3.inc.{BeepI}
    entity ci(t: String)
    requires Spec[E = {BeepI}]
    provides Spec[E = {BeepI}]
  end
  sort DI
    entity di(t: String)
  end
  fact Spec[C = DI, E = {BeepI}]
  operation askI(p: String) -> Out
    requires Spec[E = {BeepI}]
    effects {Error} = out(v: p)
end
"#;
    let unrelated = r#"
namespace test.v25n3.inc2
  import anthill.prelude.{String}
  sort Later
    entity later(t: String)
  end
end
"#;
    let dir = crate::common::stdlib_dir();
    let mut parsed: Vec<_> = crate::common::collect_anthill_files(&dir)
        .iter()
        .map(|p| {
            parse::parse(&std::fs::read_to_string(p).expect("read stdlib")).expect("parse stdlib")
        })
        .collect();
    for extra in [OUT, SPEC, bad] {
        parsed.push(parse::parse(extra).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    let first: Vec<String> = match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => vec![],
        Err(e) => e.iter().map(|x| x.to_string()).collect(),
    };
    // Only the row-label refusals are counted: the fixture's `provides Spec[…]` is
    // deliberately unbacked, and this test is about WHICH BATCH judges a clause, not
    // about what else that clause owes.
    let rows = |errs: &[String]| {
        let mut out: Vec<String> = errs
            .iter()
            .filter(|e| e.contains("is not a REGISTERED effect kind"))
            .cloned()
            .collect();
        out.sort();
        out
    };
    let judged = |errs: &[String]| rows(errs).len();
    assert_eq!(
        judged(&first),
        4,
        "the batch that WRITES the clauses must refuse all four; got: {first:#?}"
    );

    let later = parse::parse(unrelated).expect("parse later");
    let second: Vec<String> = match load::load_all(&mut kb, &[&later], &NullResolver) {
        Ok(_) => vec![],
        Err(e) => e.iter().map(|x| x.to_string()).collect(),
    };
    assert_eq!(
        judged(&second),
        0,
        "a later batch must not re-report a clause it was never given; got: {second:#?}"
    );

    let again = parse::parse(bad).expect("parse re-presented");
    let third: Vec<String> = match load::load_all(&mut kb, &[&again], &NullResolver) {
        Ok(_) => vec![],
        Err(e) => e.iter().map(|x| x.to_string()).collect(),
    };
    // THE SAME DIAGNOSTIC, not merely the same COUNT: a re-presented clause must read
    // identically to the first batch's refusal, since the two are the same clause of the
    // same file. Comparing the rendered messages is what catches a repair that judges the
    // right number of clauses through the wrong origins.
    assert_eq!(
        rows(&third),
        rows(&first),
        "a RE-PRESENTED file must be refused again, on every route, word for word"
    );
}

/// A CHECK-LESS LOAD CLAIMS THE CLAUSES IT WROTE, NOT ONLY THE ONES IT UN-CLAIMED.
///
/// `a_check_less_load_entry_point_records_no_load_check_work` above loads the offender in
/// batch 1 FIRST, so every clause the partial load presents is a dedup hit on a RuleId
/// already claimed — and restoring the pre-load snapshot puts those claims back. This is
/// the other population: a file the partial load is the FIRST to see. Its clause facts get
/// FRESH RuleIds that were never in any snapshot, so a restore leaves them UNCLAIMED, and
/// the next full `load_all` walks the whole KB, judges them and fails — naming a file it
/// was never handed. One symptom, two mechanisms, and the snapshot addresses exactly one
/// (WI-20260901-47VWX; found by /code-review reading WI-20260821-P85Z7's diff).
///
/// MEASURED, with `typing::claim_written_row_bindings`'s call at the check-less return
/// removed: the third batch — ONE clean unrelated sort — reports 5 refusals, one per
/// clause producer, about `test.v47vwx.inc`. With the repair it reports 0.
///
/// ```text
///   back-out                                        this test             elsewhere
///   ─────────────────────────────────────────────── ───────────────────── ────────────
///   `claim_written_row_bindings` (call removed)      the UNRELATED arm, 5  a_check_less_
///                                                                          load_entry_
///                                                                          point_… (2),
///                                                                          …_derived_
///                                                                          too (2)
/// ```
///
/// ONE LINE, THREE POPULATIONS, and that is why the row above names its neighbours:
/// removing the call takes `a_check_less_load_entry_point_…`'s clause half to 2 as well,
/// and `…_claims_a_row_it_derived_too` to 2. That first arm loads its offender in batch 1
/// first, so its clauses are DEDUP HITS on already-claimed ids — the population
/// WI-20260901-EA6KS's snapshot-and-restore addressed. This test is a population it could
/// not reach: a clause the check-less load WROTE.
///
/// THE FOURTH BATCH IS THE CONTROL, and without it the repair is satisfiable by claiming
/// everything forever: re-presenting the SAME file to a full `load_all` must be refused
/// again on all five routes, because `note_metadata_fact_presented` drops the claims at
/// the loader's metadata entry points. It is the `a_later_load_re_reports_…` rule, asked
/// of a file whose claims came from a check-less load rather than from a check. (FOUR of
/// the five come back through that drop; the condition route comes back because its head
/// carries a per-scope clause index that makes the re-presented fact a NEW one — see the
/// module header's back-out table, where backing the drop out takes this batch to 1 and
/// not to 0.)
///
/// FIVE PRODUCERS, ONE FILE — `a_later_load_re_reports_…`'s fixture plus the one it does
/// not carry. `SortProvidesInfo` has two loader producers (`load_provides_clause` and
/// `maybe_emit_fact_provides_info`), `SortRequiresInfo` arrives through
/// `resolve_requires_bindings`' retract-and-re-assert, `OperationInfo` through the
/// op-scoped `requires`, and `ProvidesConditionInfo` — `EI`'s `provides OtherI[…] :-
/// Spec[E = {BeepI}]` — through the third head `all_spec_clause_views` reads. That fifth
/// one was missing here and /code-review found it: the four-producer census this fixture
/// was copied from is a census of `a_later_load_re_reports_…`'s ROUTES, not of the
/// check's SOURCES, and the two are not the same list.
///
/// AND FIVE IS STILL NOT THE DEFINITION OF THE SCOPE. A repair keyed on this census
/// passed and still leaked — see `…_claims_a_row_it_derived_too` for a producer that is
/// not in the loader at all. The shipped claim is keyed on the check's own walk, so these
/// five are a fixture for the symptom rather than a boundary; that is exactly why the
/// enumeration being one short did not become a bug.
#[test]
fn a_check_less_load_claims_the_clauses_it_wrote() {
    use anthill_core::kb::load::{self, NullResolver};
    use anthill_core::kb::KnowledgeBase;
    use anthill_core::parse;

    // `DI` is a second carrier for the `fact Spec[…]` route on purpose — see
    // `a_later_load_re_reports_…`, whose fixture this is: the dedup key is the rendered
    // ORIGIN, so a `fact Spec[C = CI, …]` on the sort that already writes `provides`
    // collapses to one refusal and the route goes invisible either way.
    let bad = r#"
namespace test.v47vwx.inc
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  import test.v25n3.spec.{Spec}
  sort BeepI
    entity beepi
  end
  sort CI
    import test.v47vwx.inc.{BeepI}
    entity ci(t: String)
    requires Spec[E = {BeepI}]
    provides Spec[E = {BeepI}]
  end
  sort DI
    entity di(t: String)
  end
  sort OtherI
    sort C = ?
  end
  sort EI
    import test.v47vwx.inc.{BeepI, OtherI}
    entity ei(t: String)
    provides OtherI[C = String] :- Spec[E = {BeepI}]
  end
  fact Spec[C = DI, E = {BeepI}]
  operation askI(p: String) -> Out
    requires Spec[E = {BeepI}]
    effects {Error} = out(v: p)
end
"#;
    let unrelated = r#"
namespace test.v47vwx.inc2
  import anthill.prelude.{String}
  sort LaterZ
    entity laterz(t: String)
  end
end
"#;
    // Only the row-label refusals are counted: the fixture's `provides Spec[…]` is
    // deliberately unbacked, and this test is about WHICH BATCH judges a clause.
    let rows = |errs: &[String]| {
        let mut out: Vec<String> = errs
            .iter()
            .filter(|e| e.contains("is not a REGISTERED effect kind"))
            .cloned()
            .collect();
        out.sort();
        out
    };
    let judged = |errs: &[String]| rows(errs).len();
    let errs_of = |r: Result<load::LoadResult, Vec<load::LoadError>>| -> Vec<String> {
        match r {
            Ok(_) => vec![],
            Err(e) => e.iter().map(|x| x.to_string()).collect(),
        }
    };

    // Batch 1: the stdlib and the spec, WITHOUT the offender — that is the whole
    // difference from the test above, and it is what makes batch 2's clauses fresh.
    let dir = crate::common::stdlib_dir();
    let mut parsed: Vec<_> = crate::common::collect_anthill_files(&dir)
        .iter()
        .map(|p| {
            parse::parse(&std::fs::read_to_string(p).expect("read stdlib")).expect("parse stdlib")
        })
        .collect();
    for extra in [OUT, SPEC] {
        parsed.push(parse::parse(extra).expect("parse extra"));
    }
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    let first = errs_of(load::load_all(&mut kb, &refs, &NullResolver));
    assert_eq!(
        judged(&first),
        0,
        "batch 1 has no offending clause to judge; got: {first:#?}"
    );

    // Batch 2: the offender, CHECK-LESS. It runs none of these checks itself.
    let solo = parse::parse(bad).expect("parse offender");
    let mid = errs_of(load::load_all_with(
        &mut kb,
        &[&solo],
        &NullResolver,
        load::LoadOptions {
            run_typer: false,
            ..Default::default()
        },
    ));
    assert_eq!(
        judged(&mid),
        0,
        "a check-less load runs no load check, so it reports none of these itself; \
         got: {mid:#?}"
    );

    // Batch 3: one clean unrelated sort. It must inherit nothing.
    let later = parse::parse(unrelated).expect("parse later");
    let third = errs_of(load::load_all(&mut kb, &[&later], &NullResolver));
    assert_eq!(
        judged(&third),
        0,
        "a batch of one unrelated sort must not be handed the check-less load's clauses; \
         got: {third:#?}"
    );

    // Batch 4: the SAME file, in full. A claim is not an erasure.
    let again = parse::parse(bad).expect("parse re-presented");
    let fourth = errs_of(load::load_all(&mut kb, &[&again], &NullResolver));
    assert_eq!(
        judged(&fourth),
        5,
        "re-presenting the file to a full load must refuse all five clauses; \
         got: {fourth:#?}"
    );
    for owner in [
        "test.v47vwx.inc.CI provides",
        "test.v47vwx.inc.CI requires",
        "test.v47vwx.inc.DI provides",
        "test.v47vwx.inc.EI provides",
        "test.v47vwx.inc.askI",
    ] {
        assert!(
            rows(&fourth).iter().any(|e| e.contains(owner)),
            "each of the four clause producers must be refused; missing `{owner}` in \
             {fourth:#?}"
        );
    }
}

/// AND A ROW IT DID NOT WRITE BUT *DERIVED* — the producer that decides how the claim is
/// keyed.
///
/// `derive_forwarded_provisions` materializes `carrier provides <lower floor>` for a
/// carrier providing a forwarding spec (058 §3.8), asserting a `SortProvidesInfo` row
/// through `assert_fact_carrier` — NOT through a metadata entry point, and ABOVE the
/// `run_typer: false` stop. So a check-less load creates a clause fact through a route
/// the loader's declaration walk never touches, and any repair keyed on what that walk
/// PRESENTED leaves it unclaimed.
///
/// THAT IS NOT HYPOTHETICAL — IT IS WHAT THIS TICKET SHIPPED FIRST AND MEASURED WRONG. A
/// presentation-keyed claim (record every `note_metadata_fact_presented` id, claim them
/// at the return) took the four-producer test above to green and left THIS fixture
/// leaking: batch 3, one clean unrelated sort, reported
/// ``test.v47vwx.fwd.CF provides test.v47vwx.fwd.SpecLo`` — a file it was never given.
/// A census of the loader's own writers could not have found it, because the writer is
/// not in the loader. Keying the claim on the CHECK'S OWN WALK
/// (`typing::RowBindingRun::ClaimOnly`) is what makes the producer irrelevant.
///
/// ```text
///   back-out                                        this test            the 5-producer test
///   ─────────────────────────────────────────────── ──────────────────── ──────────────────
///   `claim_written_row_bindings` (call removed)      the UNRELATED arm,   its UNRELATED
///                                                    2 — BOTH rows        arm, 5
///   the presentation-keyed repair, in its place      the UNRELATED arm,   green
///                                                    1 — SpecLo alone
/// ```
///
/// THE TWO ROWS DIFFER BY EXACTLY ONE ENTRY, and that is the whole measurement. Remove
/// the claim entirely and BOTH the written row and the derived one leak. Put the
/// presentation-keyed repair in its place and the written row is claimed while the
/// DERIVED one still leaks — one row, and it is the one no census of the loader's writers
/// would have predicted. (The first draft of this table recorded `1 (SpecLo)` in both
/// rows: the second row's figure, carried across rather than measured. /code-review
/// caught it and the back-out was re-run — a control table whose number is wrong is worse
/// than no table.)
///
/// THE FOURTH BATCH RECORDS WHAT THE CLAIM COSTS, and it is a real cost stated rather
/// than hidden: re-presenting the file to a full load refuses the WRITTEN clause again
/// (`note_metadata_fact_presented` drops that claim at the assert) but NOT the derived
/// one, whose claim nothing drops. THE REASON IS NOT A DEDUP HIT — this doc said so and
/// was wrong (/code-review): `forwarded_rows_to_derive` returns "every (carrier,
/// forwarded floor) row NOT ALREADY PRESENT", so on the second load the row is filtered
/// out and `assert_forwarded_provides` is never reached at all. There is no assertion to
/// hang a presentation on, which matters to anyone who later tries to recover this
/// refusal: the fix would be at the deriver's filter, not at an entry point. The author
/// still meets a refusal naming `BeepF`, at the clause they actually wrote, which is the
/// one they can fix.
#[test]
fn a_check_less_load_claims_a_row_it_derived_too() {
    use anthill_core::kb::load::{self, NullResolver};
    use anthill_core::kb::KnowledgeBase;
    use anthill_core::parse;

    // `SpecHi provides SpecLo[C = C, E = E]` is the forwarder — the `Ord provides
    // WeakOrd[T = T]` shape 058 §3.8 names. `CF` writes the bad label ONCE, on the upper
    // floor; the lower floor's row is derived at the same bindings, and carries it.
    let fwd = r#"
namespace test.v47vwx.fwd
  import anthill.prelude.{Error, String, EffectsRuntime}
  import test.v25n3.out.{Out}
  import test.v25n3.out.Out.{out}
  sort SpecLo
    sort C = ?
    effects E = ?
    operation lo(self: C, p: String) -> Out
      effects {E, Error} = out(v: p)
  end
  sort SpecHi
    import test.v47vwx.fwd.{SpecLo}
    sort C = ?
    effects E = ?
    provides SpecLo[C = C, E = E]
    operation hi(self: C, p: String) -> Out
      effects {E, Error} = out(v: p)
  end
  sort BeepF
    entity beepf
  end
  sort CF
    import test.v47vwx.fwd.{BeepF, SpecHi}
    entity cf(t: String)
    provides SpecHi[E = {BeepF}]
  end
end
"#;
    let unrelated = r#"
namespace test.v47vwx.fwd2
  import anthill.prelude.{String}
  sort LaterF
    entity laterf(t: String)
  end
end
"#;
    // The ORIGIN phrase only — `owner keyword spec` — which is what says WHICH row was
    // judged. The rest of the message is the shared explanation.
    let rows = |errs: &[String]| {
        let mut out: Vec<String> = errs
            .iter()
            .filter(|e| e.contains("is not a REGISTERED effect kind"))
            .map(|e| e[..e.find(" binds ").unwrap_or(0)].to_string())
            .collect();
        out.sort();
        out
    };
    let errs_of = |r: Result<load::LoadResult, Vec<load::LoadError>>| -> Vec<String> {
        match r {
            Ok(_) => vec![],
            Err(e) => e.iter().map(|x| x.to_string()).collect(),
        }
    };
    let base = || {
        let dir = crate::common::stdlib_dir();
        let mut parsed: Vec<_> = crate::common::collect_anthill_files(&dir)
            .iter()
            .map(|p| parse::parse(&std::fs::read_to_string(p).expect("read")).expect("parse"))
            .collect();
        for extra in [OUT, SPEC] {
            parsed.push(parse::parse(extra).expect("parse extra"));
        }
        parsed
    };
    let written = "`test.v47vwx.fwd.CF provides test.v47vwx.fwd.SpecHi`";
    let derived = "`test.v47vwx.fwd.CF provides test.v47vwx.fwd.SpecLo`";

    // A BATCH THAT IS GIVEN THE FILE REFUSES BOTH ROWS. Without this the test cannot
    // tell "the derived row is claimed" from "the derived row is never judged at all",
    // and the whole fixture would be measuring nothing.
    {
        let mut parsed = base();
        parsed.push(parse::parse(fwd).expect("parse fwd"));
        let refs: Vec<_> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        let e = errs_of(load::load_all(&mut kb, &refs, &NullResolver));
        // A SET, NOT A SEQUENCE: `rows` sorts, so the pair's ORDER here means nothing and
        // the expected side is sorted to say so. Written as `vec![written, derived]` it
        // read as judgement order and passed on an alphabetical accident — `SpecHi` <
        // `SpecLo` — so renaming the floors to 058 §3.8's own `Ord`/`WeakOrd` would have
        // reddened it for a reason that is not about this rule (/code-review).
        let mut both = vec![written.to_string(), derived.to_string()];
        both.sort();
        assert_eq!(
            rows(&e),
            both,
            "a full load of the file refuses the written row AND the derived one; got: {e:#?}"
        );
    }

    let parsed = base();
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    let first = errs_of(load::load_all(&mut kb, &refs, &NullResolver));
    assert!(
        rows(&first).is_empty(),
        "batch 1 has nothing to judge; got: {first:#?}"
    );

    let solo = parse::parse(fwd).expect("parse fwd");
    let mid = errs_of(load::load_all_with(
        &mut kb,
        &[&solo],
        &NullResolver,
        load::LoadOptions {
            run_typer: false,
            ..Default::default()
        },
    ));
    assert!(
        rows(&mid).is_empty(),
        "a check-less load reports none of these itself; got: {mid:#?}"
    );

    let later = parse::parse(unrelated).expect("parse later");
    let third = errs_of(load::load_all(&mut kb, &[&later], &NullResolver));
    assert!(
        rows(&third).is_empty(),
        "a batch of one unrelated sort must not be handed the DERIVED row either; \
         got: {third:#?}"
    );

    let again = parse::parse(fwd).expect("parse again");
    let fourth = errs_of(load::load_all(&mut kb, &[&again], &NullResolver));
    assert_eq!(
        rows(&fourth),
        vec![written.to_string()],
        "re-presenting the file refuses the clause the author WROTE; the derived row's \
         claim is dropped by nothing, and this records that; got: {fourth:#?}"
    );
}

//! WI-842 (proposal 058 §4.9, phase 3a) — the BRACKET-LESS provider readers go loud
//! on a second candidate instead of taking the first.
//!
//! §4.9's audit: exactly one consumer of provider facts can raise a use-site
//! ambiguity (`resolve_inner` → `pick_most_specific`, reachable only from
//! `check_apply` — the sites that HAVE a call-site bracket). Every other consumer
//! selects by FIRST MATCH with no ambiguity arm, and the code names today's LOAD-time
//! coherence refusal as its license — the very refusal phase 3b deletes. So these
//! reads must be hardened BEFORE coexistence lands, or 3b delivers silent first-match.
//!
//! WHAT THIS FILE PINS, one test per leg:
//!
//!   * VALUE-DIRECTED DISPATCH (`eval.rs`'s `own .or_else(fact) .or_else(witness)`
//!     chain, now `typing::spec_op_suppliers_for_carrier`). MEASURED before the fix,
//!     on the `Leaf` + `RIVAL` program this file then used: it answered `Ok(Int(1))` —
//!     the carrier's own member — and the rule-body twin answered `described(leaf(), 1)`
//!     DEFINITELY while denying `described(leaf(), 7)`, i.e. it committed to one
//!     provider and denied the other's answer with no diagnostic from anywhere.
//!     **WI-861 moved both tie pins onto [`TWIG`]**, because 058 §3.2's rung 2a makes a
//!     carrier's own provision its default and that pair is no longer a tie at all —
//!     the answer it now gives is asserted in `wi861_rung2a_default_dispatch_test`. The
//!     historical measurement above is about the shape, not about today's fixture.
//!   * CARRIER-KEYED PROVIDER VIEWS (`provider_spec_view_bindings`, ~12 call sites:
//!     type conformance, member projection, carrier-param classification). MEASURED
//!     before the fix: the SAME program loaded clean or was refused depending on which
//!     of two provisions was WRITTEN FIRST.
//!
//! Two legs live elsewhere, and are not restated here:
//!
//!   * the `eq` family is WI-837's (the semantic-eq dispatch index, which refuses at
//!     LOAD because equality dispatches from unification where no selection can ever
//!     be written) — `wi837_witness_eq_dispatch_test.rs`:
//!     `two_witness_eq_providers_are_refused_by_the_index_build`,
//!     `a_fact_bound_eq_beside_a_witness_eq_is_refused`,
//!     `an_own_eq_beside_a_fact_bound_eq_is_refused`;
//!   * the OTHER half of §4.9's rule — an EXISTENCE read stays boolean over two
//!     providers while a SELECTING read sees both — is asked of the two readers
//!     directly, in `typing.rs`'s `wi842_bracketless_reader_tests` (they are
//!     `pub(crate)`, and the point is the readers' answers rather than what a surface
//!     does with them).

use anthill_core::eval::{EvalError, Value};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId};
use smallvec::SmallVec;

/// Spec `Desc` with a base instance at `Leaf` and a conditional one at `Wrap[E]` —
/// the shape shared with WI-817 / WI-822 / WI-855.
const INSTANCES: &str = crate::common::DESC_INSTANCES;

/// The SECOND provider of `Desc[T = Leaf]`, beside `Leaf`'s own `describe`.
///
/// It LOADS CLEAN because `Rival` is CONCRETE, which exempts it from the witness rule
/// as a manifest backend, so no `(Desc, Leaf)` group ever reaches two candidates —
/// the only way to put two providers in front of a bracket-less read while phase 3b
/// is still unwritten.
///
/// WI-855 measured a second reason that WI-859 then retired: `Leaf`'s own provision
/// used to be a coherence candidate of NEITHER kind (it binds no op, and its provider
/// IS its carrier). It is now the SELF-PROVIDER candidate, so with an ABSTRACT rival
/// the group holds two — and still loads, since both are nameable (058 tier 3). The
/// concrete spelling here is what keeps this fixture a group of one either way.
const RIVAL: &str = r#"
  sort Rival
    entity rival
    provides Desc[T = Leaf]
    operation describe(x: Leaf) -> Int64 = 7
  end
"#;

/// `Holder.probe`'s requirement is OP-SCOPED, so (WI-562) its `Desc.describe(x)` call
/// is served by VALUE DIRECTION rather than by a caller dictionary — the read this
/// ticket hardens. Entered from the HOST (or from a rule body), so no typer-classified
/// call site resolves `Desc[Leaf]`: a classified one is `pick_most_specific`'s job and
/// is already loud (`DispatchAmbiguous` at load), which is exactly why the bracket-less
/// route needs its own check.
const HOLDER: &str = r#"
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 requires Desc[HT] = Desc.describe(x)
  end
"#;

fn program(ns: &str, extra: &str, tail: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64}}
  import anthill.prelude.PartialEq.{{eq}}
{INSTANCES}{extra}{HOLDER}{tail}
end
"#
    )
}

/// WI-861 — A CARRIER THAT PROVIDES NOTHING ITSELF, with two witnesses. The fixture the
/// two tie pins moved onto, and the move is forced rather than cosmetic: 058 §3.2's rung
/// 2a makes a carrier's OWN provision its default, so `Leaf` beside `RIVAL` is no longer
/// a tie at all — it RESOLVES to `Leaf`, which is asserted in
/// `wi861_rung2a_default_dispatch_test::a_value_directed_tie_takes_the_carriers_own_
/// supplier`. `Twig` has no provision of its own and neither witness is marked, so
/// nothing answers and §4.9's rule — go loud on the second candidate, never first-match —
/// is still what these two tests measure.
///
/// The two witnesses disagree (3 vs 5), so a first-match regression shows as a VALUE
/// rather than as a missing error.
const TWIG: &str = r#"
  sort Twig
    entity twig
  end

  sort TwigA
    provides Desc[T = Twig]
    operation describe(x: Twig) -> Int64 = 3
  end

  sort TwigB
    provides Desc[T = Twig]
    operation describe(x: Twig) -> Int64 = 5
  end
"#;

/// Call `Holder.probe(<ctor>())` from the host — the entry with no call site at all.
fn probe_entity(ns: &str, extra: &str, ctor: &str) -> Result<Value, EvalError> {
    let src = program(ns, extra, "");
    let kb = crate::common::load_kb_with(&src);
    let sym = kb.resolve_symbol(&format!("{ns}.{ctor}"));
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    let recv = Value::Entity {
        functor: sym,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    };
    interp.call(&format!("{ns}.Holder.probe"), &[recv])
}

fn probe_leaf(ns: &str, extra: &str) -> Result<Value, EvalError> {
    probe_entity(ns, extra, "Leaf.leaf")
}

/// THE PIN. Two providers, one bracket-less read from a host entry: a NAMED diagnostic
/// listing both candidates, never the first match.
///
/// WI-861 moved it onto [`TWIG`] — see that constant for why the `Leaf` + `RIVAL` pair
/// stopped being a tie, and where the answer it now gives is asserted.
///
/// **WI-1091 MOVED WHICH QUESTION IS ASKED, and the diagnostic with it.** `Holder.probe`'s
/// requirement is OP-SCOPED, and WI-1091 widened the placement so a body call licensed by
/// its enclosing operation's own `requires` reads THAT dictionary rather than being served
/// by value-direction. So the runtime no longer gets as far as "which SUPPLIER of
/// `describe` for `Twig`?" — it fails one step earlier, building the `Desc[Twig]`
/// dictionary the licence names, and reports `AmbiguousRequirement` naming the requirement
/// and both providers. §4.9's rule is what this row measures and it is unchanged: go loud
/// on the second candidate, never first-match.
///
/// WHAT MOVED WITH IT, and where it is still measured — this row used to be the eval face
/// of `AmbiguousSpecOpDispatch`, including its BY-ROUTE candidate rendering and its
/// `NameableWitness` repair. None of that is lost:
///   * the eval face itself — `wi1012_static_supplier_tie_test::a_tie_on_an_abstract_
///     carrier_is_still_refused_at_the_call`, whose abstract-`Shape` receiver reaches
///     value-direction with no op-scoped `requires` in the way;
///   * the one message body across both faces — `wi1012 both_faces_render_one_message_body`;
///   * the `NameableWitness` repair and its sentence — `wi1027` route 3, `wi1035`, `wi1043`.
///
/// WHAT AN AUTHOR LOSES, stated rather than left to be noticed: `AmbiguousSpecOpDispatch`
/// carries a `repair` (`SupplierTieRepair::NameableWitness` — "route the call through an
/// operation that can write `[Spec = Witness]`") and `AmbiguousRequirement` has no such
/// field, so on THIS route the message now names both providers and not what to write.
/// The repair sentence is still measured on the LOAD face (wi1027 route 3, wi1035,
/// wi1043) and the eval face keeps it wherever a supplier tie is still what fails
/// (wi1012's abstract-carrier row). Restoring it here means giving
/// `AmbiguousRequirement` a repair of its own, which is a diagnostics change with its
/// own shape — not this ticket's, and recorded here so it is a decision rather than an
/// omission.
///
/// BACKED OUT (WI-1091's widening reverted): `AmbiguousSpecOpDispatch` naming `TwigA` and
/// `TwigB` by supply route. `Ok(Int(1))` / `Ok(Int(7))` are the pre-WI-842 defect this
/// still guards on either placement — a first match, with the loser silently denied.
#[test]
fn a_two_provider_value_directed_dispatch_names_both_candidates() {
    let ns = "wi842.vd.tie";
    let err = probe_entity(ns, TWIG, "Twig.twig").unwrap_err();
    let EvalError::AmbiguousRequirement {
        op,
        requirement,
        candidates,
    } = &err
    else {
        panic!(
            "expected AmbiguousRequirement; got {err:?} — `Ok(Int(3))` here is the \
             pre-WI-842 behaviour (first match), and `Ok(Int(5))` would be the same \
             defect with the other winner"
        )
    };
    assert!(
        op.ends_with("Holder.probe"),
        "the error must name the operation whose requirement could not be built; got `{op}`"
    );
    assert!(
        requirement.contains("Desc") && requirement.contains("Twig"),
        "the error must name the REQUIREMENT that tied (`Desc[T = Twig]`); got `{requirement}`"
    );
    assert_eq!(
        candidates.len(),
        2,
        "exactly the two providers expected; got {candidates:?}"
    );
    for want in ["TwigA", "TwigB"] {
        assert!(
            candidates.iter().any(|c| c.contains(want)),
            "`{want}` must be named as a provider; got {candidates:?}"
        );
    }
    let rendered = err.to_string();
    for want in ["Twig", "TwigA", "TwigB"] {
        assert!(
            rendered.contains(want),
            "the rendered diagnostic must mention `{want}`: {rendered}"
        );
    }
}

/// ABSENCE CONTROL — the identical program with ONE provider still dispatches and
/// computes its answer. Without it the pin above would pass just as well if the whole
/// shape had stopped working; with it, the only difference is the second provision.
#[test]
fn the_same_program_with_one_provider_still_dispatches() {
    let got = probe_leaf("wi842.vd.untied", "");
    assert!(
        matches!(got, Ok(Value::Int(1))),
        "expected Leaf's own `describe` (1) by value-directed dispatch; got {got:?}"
    );
}

/// …AND THE PAIR THAT USED TO BE THE HEADLINE, kept HERE with its new verdict rather
/// than deleted with the fixture (WI-861, and the review that caught `RIVAL` going
/// unused: an orphaned fixture is the shape a lost control takes).
///
/// `Leaf` PROVIDES `Desc` itself and `RIVAL` is a nameable witness beside it. That was
/// this file's `AmbiguousSpecOpDispatch` pin; 058 §3.6 infers a default from a carrier's
/// own provision and §3.2's rung 2a takes it, so the same value-directed read now
/// ANSWERS — and answers `1`, the carrier's own member, not `Rival`'s 7.
///
/// It is NOT a return to first-match, which is this file's subject: the difference is
/// visible one fixture over, where the marked witness wins
/// (`wi861_rung2a_default_dispatch_test::a_value_directed_tie_takes_the_marked_witness`),
/// and where a witness-only tie still refuses (the pin above).
#[test]
fn a_self_providing_carrier_now_answers_where_it_used_to_tie() {
    let got = probe_leaf("wi842.vd.defaulted", RIVAL);
    assert!(
        matches!(got, Ok(Value::Int(1))),
        "the carrier's own provision is its default (058 §3.6), so the value-directed \
         read takes `Leaf.describe` (1) and `Rival` (7) stays opt-in; got {got:?}"
    );
}

/// A rule-body atom reaches the same read (its op-call operand runs through the
/// SLD→eval bridge, WI-625 gap 1), and there the tie DELAYS instead of answering.
///
/// Stated exactly, because the bridge's contract decides the shape of this leg: an
/// eval error inside a bridged body RESIDUALIZES rather than aborting the enclosing
/// rule (WI-483 — a rule's validity may not depend on a callee's body), so the NAMED
/// diagnostic is what an eval entry sees (the test above) while the rule reports by
/// NOT ANSWERING. That is still the §4.9 fix: MEASURED with first-match restored, the
/// two-provider program answered `described(leaf(), 1)` DEFINITELY and refuted
/// `described(leaf(), 7)` — indistinguishable from the one-provider program, with the
/// second provider silently ignored.
///
/// WI-861 moved the TIED arm onto [`TWIG`] for the reason that constant states: `Leaf` +
/// `RIVAL` now resolves by rung 2a. The UNTIED arm keeps `Leaf`, so the pair still
/// differs by exactly one thing — whether anything answers the dispatch.
#[test]
fn a_rule_body_delays_on_the_tie_instead_of_first_matching() {
    const RULE: &str = r#"
  rule described(?x, ?y)
    :- eq(?y, Holder.probe(?x))
"#;
    // ONE provider: the rule answers, and answers 1 (not 7).
    let (definite_1, definite_7) =
        rule_answers("wi842.vd.rule.untied", "", RULE, "Leaf.leaf", (1, 7));
    assert_eq!(
        (definite_1, definite_7),
        (1, 0),
        "with one provider the rule must fire for the provider's answer (1) and refute 7"
    );
    // TWO providers: neither answer is DEFINITE. A definite 3 (or 5) here is a
    // first-match commitment — the defect this ticket closes.
    let (tied_3, tied_5) = rule_answers("wi842.vd.rule.tie", TWIG, RULE, "Twig.twig", (3, 5));
    assert_eq!(
        (tied_3, tied_5),
        (0, 0),
        "with two providers the rule may not DECIDE either answer: the dispatch is \
         ambiguous, so the goal delays (a residual, non-definite solution)"
    );
}

/// `described(<ctor>(), n)` for the two candidate answers — the count of DEFINITE
/// solutions of each. Ground queries on purpose: an unbound query var triggers the
/// caller-var delay pre-check and the body never runs (the WI-483 pattern).
fn rule_answers(
    ns: &str,
    extra: &str,
    rule: &str,
    ctor: &str,
    answers: (i64, i64),
) -> (usize, usize) {
    let mut kb = crate::common::load_kb_with(&program(ns, extra, rule));
    let functor = kb.resolve_symbol(&format!("{ns}.described"));
    let leaf_ctor = kb.resolve_symbol(&format!("{ns}.{ctor}"));
    let leaf: TermId = kb.alloc(Term::Fn {
        functor: leaf_ctor,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let mut definite_for = |answer: i64| {
        let a = kb.alloc(Term::Const(Literal::Int(answer)));
        let goal = kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::from_slice(&[leaf, a]),
            named_args: SmallVec::new(),
        });
        let cfg = ResolveConfig {
            max_solutions: 10,
            ..ResolveConfig::default()
        };
        kb.resolve(&[goal], &cfg)
            .iter()
            .filter(|s| s.is_definite())
            .count()
    };
    (definite_for(answers.0), definite_for(answers.1))
}

// ── `provider_spec_view_bindings`: the carrier-keyed provider view ──────────────

/// Two provisions of one spec for one carrier AT THE SAME APPLICATION (`Self = C`)
/// that disagree about another param. `first`/`second` decide the SOURCE ORDER.
fn two_provision_program(ns: &str, first: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  import anthill.prelude.PartialEq.{{eq}}
  sort Iter
    sort Self = ?
    sort Element = ?
  end
  sort C
    entity c
    provides Iter[Self = C, Element = {first}]
    provides Iter[Self = C, Element = {second}]
  end
  sort Use
    operation takes(i: Iter[Self = C, Element = String]) -> Int64 = 1
    operation go(n: Int64) -> Int64 = Use.takes(c())
  end
end
"#
    )
}

/// THE SECOND PIN. Whichever order the two provisions are written in, the program is
/// refused by the SAME named diagnostic.
///
/// MEASURED before the fix, and the measurement is the whole point: with
/// `Element = String` written first the program LOADED CLEAN; with `Element = Int64`
/// first the identical program was refused with `expected Iter[Element = String,
/// Self = C], got C`. The reader took the first matching provision, so the program's
/// MEANING was decided by provision order and the losing binding was invisible.
#[test]
fn conflicting_provisions_are_refused_in_either_order() {
    for (ns, first, second) in [
        ("wi842.view.intfirst", "Int64", "String"),
        ("wi842.view.strfirst", "String", "Int64"),
    ] {
        let errs = crate::common::try_load_kb_with(&two_provision_program(ns, first, second))
            .err()
            .unwrap_or_else(|| {
                panic!(
                    "`{ns}` must be REFUSED: `C` provides `Iter` twice at one application \
                     with `Element` bound two ways, and every reader of the provider view \
                     takes the first — so admitting it makes the program mean whichever \
                     provision was written first"
                )
            });
        let text = errs.join("\n");
        for want in ["conflicting provisions", "Element", "Int64", "String"] {
            assert!(
                text.contains(want),
                "`{ns}`: the refusal must name the conflict and both bindings (`{want}` \
                 missing) — a bare type mismatch is the pre-WI-842 report, which named \
                 neither the second provision nor the order-dependence:\n{text}"
            );
        }
    }
}

/// THE CONTROL THAT BOUNDS THAT RULE — a carrier may provide one spec MANY times at
/// DIFFERENT APPLICATIONS, and must still load.
///
/// This is not hypothetical: `sort Console` holds `fact Effect[T = ConsoleOutput]`,
/// `[T = ConsoleError]` and `[T = ConsoleInput]` (`prelude/console.anthill:35-37`), and
/// a first cut of the check above refused the STDLIB. The distinction is the spec's
/// CARRIER PARAM: differing there means different instances; agreeing there while
/// differing elsewhere means two answers for one instance.
#[test]
fn several_applications_of_one_spec_on_one_carrier_still_load() {
    let src = r#"
namespace wi842.view.apps
  import anthill.prelude.{Int64, String}
  sort Iter
    sort Self = ?
    sort Element = ?
  end
  sort A
    entity a
  end
  sort B
    entity b
  end
  sort C
    entity c
    provides Iter[Self = A, Element = Int64]
    provides Iter[Self = B, Element = String]
  end
end
"#;
    crate::common::try_load_kb_with(src).unwrap_or_else(|errs| {
        panic!(
            "two provisions differing in the spec's CARRIER PARAM are two instances, \
             not a conflict — this is the stdlib's own `Console provides Effect` shape:\n{}",
            errs.join("\n")
        )
    });
}

/// The blind spot §4.9 recorded, retired: "a first `SortProvidesInfo` fact that binds
/// no `eq` hides a second that does". With conflicts refused, the reader MERGES the
/// provisions of one application instead of returning the first, so a param the first
/// provision omits is read from the second.
///
/// Observable as a load verdict: `takes` demands `Element = Int64`, which only the
/// SECOND provision binds. Under first-match the program was refused.
#[test]
fn a_provision_binding_a_param_the_first_omits_is_no_longer_hidden() {
    let src = r#"
namespace wi842.view.merge
  import anthill.prelude.{Int64}
  sort Iter
    sort Self = ?
    sort Element = ?
  end
  sort C
    entity c
    provides Iter[Self = C]
    provides Iter[Self = C, Element = Int64]
  end
  sort Use
    operation takes(i: Iter[Self = C, Element = Int64]) -> Int64 = 1
    operation go(n: Int64) -> Int64 = Use.takes(c())
  end
end
"#;
    crate::common::try_load_kb_with(src).unwrap_or_else(|errs| {
        panic!(
            "the two provisions AGREE (one binds `Element`, the other omits it), so the \
             carrier's view is their merge — reading only the first hides the binding \
             the author wrote:\n{}",
            errs.join("\n")
        )
    });
}

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
//!     on the program below: the two-provider program answered `Ok(Int(1))` — the
//!     carrier's own member — and the rule-body twin answered `described(leaf(), 1)`
//!     DEFINITELY while denying `described(leaf(), 7)`, i.e. it committed to one
//!     provider and denied the other's answer with no diagnostic from anywhere.
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
    fact Desc[T = Leaf]
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
{INSTANCES}{extra}{HOLDER}{tail}
end
"#
    )
}

/// Call `Holder.probe(leaf())` from the host — the entry with no call site at all.
fn probe_leaf(ns: &str, extra: &str) -> Result<Value, EvalError> {
    let src = program(ns, extra, "");
    let kb = crate::common::load_kb_with(&src);
    let leaf_sym = kb.resolve_symbol(&format!("{ns}.Leaf.leaf"));
    let mut interp = anthill_core::eval::Interpreter::new(kb);
    anthill_core::eval::builtins::register_standard_builtins(&mut interp)
        .expect("register standard eval builtins");
    let leaf = Value::Entity {
        functor: leaf_sym,
        pos: Vec::new().into(),
        named: Vec::new().into(),
    };
    interp.call(&format!("{ns}.Holder.probe"), &[leaf])
}

/// THE PIN. Two providers, one bracket-less value-directed dispatch: a NAMED
/// diagnostic listing both candidates BY SUPPLY ROUTE, never the first match.
#[test]
fn a_two_provider_value_directed_dispatch_names_both_candidates() {
    let ns = "wi842.vd.tie";
    let err = probe_leaf(ns, RIVAL).unwrap_err();
    let EvalError::AmbiguousSpecOpDispatch { op, carrier, candidates, repair } = &err else {
        panic!(
            "expected AmbiguousSpecOpDispatch; got {err:?} — `Ok(Int(1))` here is the \
             pre-WI-842 behaviour (first match: the carrier's own member), and \
             `Ok(Int(7))` would be the same defect with the other winner"
        )
    };
    assert!(op.ends_with("Desc.describe"), "the error must name the spec op; got `{op}`");
    assert!(carrier.ends_with("Leaf"), "the error must name the carrier; got `{carrier}`");
    assert_eq!(candidates.len(), 2, "exactly the two suppliers expected; got {candidates:?}");
    // Rendered BY ROUTE: the two are written in different syntaxes (a member of the
    // carrier vs a witness sort's `fact`), and only the route says which text to delete.
    assert!(
        candidates.iter().any(|c| c.contains("own member") && c.ends_with("Leaf.describe'")),
        "one candidate is the carrier's OWN member; got {candidates:?}"
    );
    assert!(
        candidates.iter().any(|c| c.contains("witness sort") && c.contains("Rival")),
        "the other is the WITNESS sort; got {candidates:?}"
    );
    let rendered = err.to_string();
    for want in ["Desc.describe", "Leaf", "Rival"] {
        assert!(rendered.contains(want), "the rendered diagnostic must mention `{want}`: {rendered}");
    }
    // WI-1012 — THE REPAIR THIS TIE HAS, and the control the message had been missing.
    // `Rival` is a WITNESS sort: a nameable provider distinct from the carrier, and
    // `Desc.describe` is BODY-LESS, so it has the `Dispatch` requirement slot a
    // `[Desc = Rival]` bracket binds (`callee_requirement_slots`). No such bracket can
    // be written HERE — that is what "bracket-less read" means and why this refuses —
    // but routing the call through an operation that can write one IS a repair, and it
    // is the ONE tie shape the corpus drives. Asserted because a shared message is
    // exactly where it can be lost: WI-1012's first cut told this author "no bracket
    // names any of them", which is true only of a DEFAULTED op's tie.
    assert_eq!(
        *repair,
        anthill_core::kb::typing::SupplierTieRepair::NameableWitness,
        "a witness rival on a body-less op is nameable at a bracket-capable call",
    );
    assert!(
        rendered.contains("route the call through an operation that can write \
                           `[Spec = Witness]`"),
        "the witness repair must survive into the rendered message: {rendered}",
    );
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
#[test]
fn a_rule_body_delays_on_the_tie_instead_of_first_matching() {
    const RULE: &str = r#"
  rule described(?x, ?y)
    :- eq(?y, Holder.probe(?x))
"#;
    // ONE provider: the rule answers, and answers 1 (not 7).
    let (definite_1, definite_7) = rule_answers("wi842.vd.rule.untied", "", RULE);
    assert_eq!(
        (definite_1, definite_7),
        (1, 0),
        "with one provider the rule must fire for the provider's answer (1) and refute 7"
    );
    // TWO providers: neither answer is DEFINITE. A definite 1 (or 7) here is a
    // first-match commitment — the defect this ticket closes.
    let (tied_1, tied_7) = rule_answers("wi842.vd.rule.tie", RIVAL, RULE);
    assert_eq!(
        (tied_1, tied_7),
        (0, 0),
        "with two providers the rule may not DECIDE either answer: the dispatch is \
         ambiguous, so the goal delays (a residual, non-definite solution)"
    );
}

/// `described(leaf(), n)` for n = 1 and 7 — the count of DEFINITE solutions of each.
/// Ground queries on purpose: an unbound query var triggers the caller-var delay
/// pre-check and the body never runs (the WI-483 pattern).
fn rule_answers(ns: &str, extra: &str, rule: &str) -> (usize, usize) {
    let mut kb = crate::common::load_kb_with(&program(ns, extra, rule));
    let functor = kb.resolve_symbol(&format!("{ns}.described"));
    let leaf_ctor = kb.resolve_symbol(&format!("{ns}.Leaf.leaf"));
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
        let cfg = ResolveConfig { max_solutions: 10, ..ResolveConfig::default() };
        kb.resolve(&[goal], &cfg).iter().filter(|s| s.is_definite()).count()
    };
    (definite_for(1), definite_for(7))
}

// ── `provider_spec_view_bindings`: the carrier-keyed provider view ──────────────

/// Two provisions of one spec for one carrier AT THE SAME APPLICATION (`Self = C`)
/// that disagree about another param. `first`/`second` decide the SOURCE ORDER.
fn two_provision_program(ns: &str, first: &str, second: &str) -> String {
    format!(
        r#"
namespace {ns}
  import anthill.prelude.{{Int64, String}}
  sort Iter
    sort Self = ?
    sort Element = ?
  end
  sort C
    entity c
    fact Iter[Self = C, Element = {first}]
    fact Iter[Self = C, Element = {second}]
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
    fact Iter[Self = A, Element = Int64]
    fact Iter[Self = B, Element = String]
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
    fact Iter[Self = C]
    fact Iter[Self = C, Element = Int64]
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

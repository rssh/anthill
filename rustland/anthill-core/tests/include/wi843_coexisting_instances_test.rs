//! WI-843 (proposal 058 §4.1 tier 3, §4.3, §5.1, §9 phase 3b) — COHERENCE: two
//! providers of one `(spec, carrier)` COEXIST, and what is refused is an
//! UNSELECTED dispatch against them.
//!
//! WHAT MOVED. Two independent refusals fired on §1's program: the per-call
//! `DispatchAmbiguous` and the LOAD-TIME `AmbiguousWitness`. The second did not
//! depend on any call — delete every caller and the load still failed with "keep
//! exactly one", so what Anthill rejected was the pair of DECLARATIONS and the
//! question of which monoid a call wanted was never reached. That refusal is gone
//! (`AmbiguousWitness` DELETED, not gated), and the first one grew the payload a
//! use-site diagnostic needs: the candidates, and the bracket that picks one.
//!
//! THE GATE IS NAMEABILITY (§4.3), and it is why two of the three load-time
//! diagnostics survive. A witness sort has a name, so a use site can select it; an
//! instance fact has none, so a tier-3 message listing one would offer a candidate
//! the author cannot spell. Two facts therefore stay `AmbiguousInstanceFact` and a
//! MIXED pair stays `MixedProviderKinds` (WI-838) — the cross-kind case being the
//! trap this ticket was warned about, since merely deleting the witness check
//! would have inherited WI-838's blind spot as the coexistence rule.
//!
//! NOTHING BECAME SILENTLY *FIRST-MATCHED* — which is a narrower claim than the
//! ticket's "nothing may become silently dispatched", and the difference is
//! measured. Phase 3a (WI-842) was a PREREQUISITE rather than cleanup precisely so
//! the first-match half would hold: every bracket-less provider reader that SELECTS
//! was made loud first, and the two whose ambiguity is unnameable (the sem-eq index,
//! the carrier-keyed provision reader) still refuse at LOAD.
//!
//! But a review found the wider claim FALSE, and the last three tests in this file
//! are the honest boundary. Two providers in one group whose heads differ in
//! SPECIFICITY are not a tie at all — tier 2's pre-existing rule picks the more
//! specific one and the call runs silently, in a program the deleted refusal used to
//! reject. And `AmbiguousEqDispatch` refuses two `eq` TARGETS, not two provisions, so
//! a bare co-provision is admitted. Both are pinned as behaviour rather than left to
//! be rediscovered; see 058 §4.1.
//!
//! Reference: docs/proposals/058-modular-instances.md §4.1, §4.3, §5.1, §5.2,
//! §9 phase 3b.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId};
use smallvec::SmallVec;

/// §1's program, minus the caller — the shape whose load failure was the whole
/// point of the ticket ("delete `sort Use` and the load STILL fails").
const TWO_MONOIDS: &str = r#"
  sort Monoid
    sort T = ?
    operation combine(a: T, b: T) -> T
    operation unit() -> T
  end
  sort AddM
    fact Monoid[T = Int64]
    operation combine(a: Int64, b: Int64) -> Int64 = add(a, b)
    operation unit() -> Int64 = 0
  end
  sort MulM
    fact Monoid[T = Int64]
    operation combine(a: Int64, b: Int64) -> Int64 = mul(a, b)
    operation unit() -> Int64 = 1
  end
"#;

/// A `fold` over `Monoid`, on the SORT-LEVEL `requires` route. §4.2 spells the
/// example with an OP-scoped `requires`, which phase 3b cannot use: an op-scoped
/// requirement is served by value-directed dispatch, which never sees a selection, so
/// WI-841 REFUSES one there whenever two or more providers answer — exactly the
/// situation this ticket creates. The sort-level twin is the same selection through
/// the channel that can carry it.
///
/// STILL TRUE AFTER WI-822 LEG 1, which gave the op-scoped chain frame slots: the
/// slots exist and the call site fills them, but a body reads them only where
/// value-direction cannot serve the call, and `fold`'s `Monoid.combine` over an
/// abstract element is served by it. See `wi841_call_site_selection_test`'s
/// `an_op_scoped_selection_that_could_differ_is_refused_not_ignored`, and WI-1091,
/// which owns lifting it.
const FOLDER: &str = r#"
  sort Folder
    sort FT = ?
    requires Monoid[T = FT]
    operation fold(xs: List[T = FT]) -> FT =
      match xs
        case nil() -> Monoid.unit()
        case cons(h, t) -> Monoid.combine(h, Folder.fold(t))
  end
"#;

const LIST_234: &str = "cons(head: 2, tail: cons(head: 3, tail: cons(head: 4, tail: nil())))";

fn program(ns: &str, body: &str) -> String {
    program_with(ns, TWO_MONOIDS, body)
}

/// The same program over a chosen set of monoid declarations — the single-provider
/// control needs `TWO_MONOIDS` minus `MulM`, and spelling the preamble twice to get
/// it is how the two drift.
fn program_with(ns: &str, monoids: &str, body: &str) -> String {
    format!("\nnamespace {ns}\n  import anthill.prelude.{{Int64, List}}\n{monoids}{body}\nend\n")
}

/// `TWO_MONOIDS` with the multiplicative one dropped.
fn one_monoid() -> String {
    let cut = TWO_MONOIDS
        .find("  sort MulM")
        .expect("TWO_MONOIDS declares MulM");
    TWO_MONOIDS[..cut].to_string()
}

fn load_errs(src: &str) -> Vec<String> {
    crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_else(|| panic!("expected load errors, but this loaded clean:\n{src}"))
}

fn loads_clean(src: &str, why: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("{why}; got load errors: {errs:?}");
    }
}

/// A FRESH interpreter per call — a trapped call poisons later calls on a shared
/// one. `interp_for` panics on a dirty load, so a value assertion also asserts the
/// program loads.
fn eval_int(src: &str, entry: &str, why: &str) -> i64 {
    let mut interp = crate::common::interp_for(src);
    match interp.call(entry, &[Value::Int(0)]) {
        Ok(Value::Int(n)) => n,
        other => panic!("{why}; got {other:?}"),
    }
}

// ── Positive control ─────────────────────────────────────────────────

/// The harness reports breakage: an unknown sort must still fail to load, so every
/// `loads_clean` below is a real assertion and not a broken oracle.
#[test]
fn positive_control_a_broken_program_is_refused() {
    let src = program(
        "wi843.control",
        "  sort Bad\n    operation bad(x: NoSuchSort) -> Int64 = 0\n  end",
    );
    // `load_errs` itself panics unless the load returned `Err`, so calling it IS the
    // control; asserting non-emptiness after it would be unreachable-if-false.
    load_errs(&src);
}

// ── §9 phase 3b acceptance ───────────────────────────────────────────

/// THE HEADLINE. `Int64` carries both the additive and the multiplicative monoid,
/// in ONE program, with no call site anywhere — the exact configuration §1 measured
/// as `ambiguous witness: … (keep exactly one)`.
#[test]
fn two_witnesses_for_one_carrier_coexist() {
    loads_clean(
        &program("wi843.coexist", ""),
        "two witness sorts for one (spec, carrier) are NAMEABLE, so they coexist \
         (058 §4.1 tier 3) — the load-time refusal moved to the use site",
    );
}

/// …and each is SELECTABLE, to a different number. 0+2+3+4 = 9 beside 1×2×3×4 = 24,
/// in one program, over one carrier — the value test phase 2 could not run because
/// `AddM` and `MulM` could not then coexist.
///
/// Both entries fold the SAME list through the SAME operation; only the bracket
/// differs. One answer twice would mean the selection reached nothing.
#[test]
fn each_coexisting_monoid_is_selectable_to_its_own_value() {
    let src = program(
        "wi843.fold",
        &format!(
            "{FOLDER}  sort Driver\n    \
             operation added(n: Int64) -> Int64 = Folder.fold[Monoid = AddM]({LIST_234})\n    \
             operation mulled(n: Int64) -> Int64 = Folder.fold[Monoid = MulM]({LIST_234})\n  end"
        ),
    );
    assert_eq!(
        eval_int(
            &src,
            "wi843.fold.Driver.added",
            "the additive monoid, selected"
        ),
        9,
        "0 + 2 + 3 + 4",
    );
    assert_eq!(
        eval_int(
            &src,
            "wi843.fold.Driver.mulled",
            "the multiplicative monoid, selected"
        ),
        24,
        "1 × 2 × 3 × 4 — the same fold over the same list, differing only in the \
         bracket, so 9 twice would mean the selection decided nothing",
    );
}

/// THE REFUSAL MOVED, it did not vanish: §1's `Use.go`, unbracketed, is an error —
/// and it is an error AT THAT CALL, naming both candidates and the bracket.
///
/// The three assertions are separate on purpose. That the load fails proves nothing
/// by itself (the same program failed before this ticket, twice over); that the
/// message names `AddM` and `MulM` is what makes a use-site diagnostic actionable;
/// and the absence of the declaration-level wording is what says the refusal MOVED
/// rather than doubled.
#[test]
fn an_unselected_dispatch_is_refused_at_the_call_that_is_ambiguous() {
    let src = program(
        "wi843.unselected",
        "  sort Use\n    operation go(a: Int64, b: Int64) -> Int64 = Monoid.combine(a, b)\n  end",
    );
    let errs = load_errs(&src);
    let tier3: Vec<&String> = errs
        .iter()
        .filter(|e| e.contains("ambiguous dispatch of"))
        .collect();
    assert_eq!(
        tier3.len(),
        1,
        "the ONE call that is actually ambiguous must raise ONE tier-3 error; \
         all errors: {errs:?}"
    );
    let text = tier3[0];
    assert!(
        text.contains("wi843.unselected.Monoid.combine")
            && text.contains("wi843.unselected.AddM")
            && text.contains("wi843.unselected.MulM")
            && text.contains("[Monoid = "),
        "the diagnostic must name the dispatched op, BOTH candidates, and the \
         bracket that picks one: {text}"
    );
    // The bracket key is the spec's SHORT name — a QUALIFIED key is refused rather
    // than resolved (§4.2), so advice spelling `[wi843.unselected.Monoid = …]`
    // would not load.
    assert!(
        !text.contains("[wi843.unselected.Monoid ="),
        "the suggested key must be the bare short name, not the qualified spec: {text}"
    );
    assert!(
        !errs.iter().any(|e| e.contains("keep exactly one")),
        "the refusal MOVED to the use site; a surviving declaration-level \
         'keep exactly one' would mean it merely doubled: {errs:?}"
    );
}

/// …and writing the bracket makes that very program load and run. The control for
/// the test above: the refusal is about the SELECTION being absent, not about the
/// two declarations.
#[test]
fn selecting_at_the_unselected_call_makes_it_load_and_run() {
    let src = program(
        "wi843.selected",
        "  sort Use\n    operation go(n: Int64) -> Int64 = Monoid.combine[Monoid = AddM](2, 3)\n  end",
    );
    assert_eq!(
        eval_int(&src, "wi843.selected.Use.go", "the pinned §1 call"),
        5
    );
}

/// THE MESSAGE MUST NOT SUGGEST A BRACKET IT WOULD ITSELF REFUSE. §4.4 check 3
/// refuses an explicit witness on a CONCRETE provider (there the VALUE decides), so
/// a tie among concrete providers has no bracket repair — and a tier-3 diagnostic
/// offering one would send the author from this refusal straight into a second.
///
/// MEASURED, which is why the branch exists: `Zeroable.zero[Zeroable = Pebble]()` on
/// exactly this program is `expected no explicit witness — this dispatch is
/// value-directed`. The receiver-less nullary op is the shape that gets here — no
/// argument value can direct it, so neither tier answers.
///
/// WI-822 LEG 1 CHANGED WHAT THE THIRD ANSWER IS, and this fixture had to move by one
/// line to keep driving the wording. `Holder.probe` used to be written `requires
/// Zeroable[HT]`, and that op-scoped clause is now a real frame slot the tie DEFERS to
/// — the program loads and computes 5 (`wi822_op_scoped_supply_test::
/// receiverless_spec_op_op_scoped_rejected_sort_level_correct` is where that is
/// asserted, and it is the same program). So the `requires` is dropped here: with no
/// chain to defer to there is still no third answer, the tie still refuses, and the
/// WORDING — which is all this test ever asserted — is still driven. Restoring the
/// clause would silently turn this into a load-clean program and the `load_errs`
/// oracle would report it, which is how the move was found.
#[test]
fn a_tie_among_concrete_providers_does_not_suggest_a_bracket() {
    let src = r#"
namespace wi843.concretetie
  import anthill.prelude.{Int64, Bool}
  sort Zeroable
    sort T = ?
    operation zero() -> T
    operation describe(x: T) -> Int64
  end
  sort Leaf
    entity leaf
    fact Zeroable[T = Leaf]
    operation zero() -> Leaf = leaf()
    operation describe(x: Leaf) -> Int64 = 1
  end
  sort Pebble
    entity pebble
    fact Zeroable[T = Pebble]
    operation zero() -> Pebble = pebble()
    operation describe(x: Pebble) -> Int64 = 5
  end
  sort Holder
    sort HT = ?
    operation probe(x: HT) -> Int64 =
      Zeroable.describe(Zeroable.zero())
  end
  sort Driver
    operation drive(n: Int64) -> Int64 = Holder.probe(pebble())
  end
end
"#;
    let errs = load_errs(src);
    let text = errs.join("\n");
    assert!(
        text.contains("ambiguous dispatch of") && text.contains("CONCRETE provider"),
        "a tie among concrete providers must still be named, and must say WHY no \
         selection is available: {text}"
    );
    assert!(
        !text.contains("[Zeroable ="),
        "the bracket must not be suggested where §4.4 check 3 refuses it: {text}"
    );

    // The CONTROL that this absence is the branch firing — rather than the bracket
    // never being suggested at all — is the sibling
    // `an_unselected_dispatch_is_refused_at_the_call_that_is_ambiguous`, which asserts
    // `[Monoid = ` IS offered on a nameable tie.
}

/// NOTHING BECAME SILENTLY DISPATCHED ON THE ROUTE THAT HAS NO USE SITE. A rule-body
/// atom is never typer-classified (§4.9), so tier 3 cannot fire for it — the
/// bracket-less read is all there is, and WI-842 made it loud.
///
/// This row exists because WI-842 could not build its own version of it. Its fixture
/// had to reach a bracket-less read through a CONCRETE rival plus a carrier's own
/// provision, since "an abstract witness pair loads clean" was exactly what phase 3b
/// had not yet delivered. That pair is now expressible, and it is the shape this
/// ticket newly admits — so it is asserted here rather than assumed to inherit 3a's
/// coverage.
///
/// The verdict is DELAY, not an error surfaced to the query: an eval error inside a
/// bridged body residualizes rather than aborting the enclosing rule (WI-483), so the
/// rule reports by NOT ANSWERING. What must not happen is a DEFINITE answer — that is
/// first-match with the loser silently denied.
#[test]
fn a_rule_body_over_two_coexisting_witnesses_does_not_first_match() {
    // The requirement is OP-SCOPED, so `Monoid.combine(a, b)` inside `probe` is served
    // by VALUE DIRECTION rather than by a caller's dictionary (WI-562) — the
    // bracket-less read. A typer-classified call would be `pick_most_specific`'s job
    // and is already loud at load, which is the other test above.
    const TAIL: &str = r#"  sort Holder
    sort HT = ?
    operation probe(a: HT, b: HT) -> HT requires Monoid[T = HT] = Monoid.combine(a, b)
  end
  rule combined(?y)
    :- eq(?y, Holder.probe(2, 3))"#;
    // 5 = AddM, 6 = MulM.
    let tied = definite_answers("wi843.rulebody", &program("wi843.rulebody", TAIL));
    let one = definite_answers(
        "wi843.rulebody1",
        &program_with("wi843.rulebody1", &one_monoid(), TAIL),
    );
    assert_eq!(
        one,
        (1, 0),
        "CONTROL: with ONE provider the rule must answer 5 DEFINITELY and refute 6 — \
         otherwise the tie assertion below measures a rule that never fires",
    );
    assert_eq!(
        tied,
        (0, 0),
        "a rule body has no bracket to write (§4.2 leaves rule bodies out of \
         selection), so a tie there must DELAY — deciding either answer would be the \
         silent first-match phase 3a exists to prevent",
    );
}

/// `combined(n)` for n = 5 and 6 — the count of DEFINITE solutions of each. Ground
/// queries on purpose: an unbound query var trips the caller-var delay pre-check and
/// the body never runs (the WI-483 pattern), which would make both counts 0 for a
/// reason that has nothing to do with providers.
fn definite_answers(ns: &str, src: &str) -> (usize, usize) {
    let mut kb = crate::common::load_kb_with(src);
    let functor = kb.resolve_symbol(&format!("{ns}.combined"));
    let mut definite_for = |kb: &mut anthill_core::kb::KnowledgeBase, answer: i64| {
        let a: TermId = kb.alloc(Term::Const(Literal::Int(answer)));
        let goal = kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::from_slice(&[a]),
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
    (definite_for(&mut kb, 5), definite_for(&mut kb, 6))
}

// ── The nameability gate (§4.3) ──────────────────────────────────────

/// Two INSTANCE FACTS keep the LOAD refusal. A fact has no name, so tier 3 has
/// nothing to offer at a use site — and this is not a leftover: the same program
/// shape with witnesses now loads (the test above), so the two rows differ ONLY in
/// whether the candidates can be spelled.
#[test]
fn two_instance_facts_still_refuse_at_load() {
    let src = r#"
namespace wi843.twofacts
  import anthill.prelude.Int64
  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end
  sort Tag
    entity tag(n: Int64)
  end
  operation combineA(x: Tag, y: Tag) -> Tag = tag(n: 1)
  operation combineB(x: Tag, y: Tag) -> Tag = tag(n: 2)
  fact Combiner[T = Tag, combine = combineA]
  fact Combiner[T = Tag, combine = combineB]
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter()
            .any(|e| e.contains("ambiguous instance: 2 distinct instance facts")),
        "an instance fact has no NAME, so its group keeps the load refusal: {errs:?}"
    );
}

/// A MIXED pair keeps the LOAD refusal too — the WI-838 trap, stated as a test.
/// This group holds a nameable candidate (`WitCombiner`) AND an unnameable one, and
/// the rule is per-GROUP: one unspellable candidate is enough, because a tier-3
/// message would have to list it.
#[test]
fn a_mixed_fact_and_witness_pair_still_refuses_at_load() {
    let src = r#"
namespace wi843.mixed
  import anthill.prelude.Int64
  sort Combiner
    sort T = ?
    operation combine(x: T, y: T) -> T
  end
  sort Tag
    entity tag(n: Int64)
  end
  operation tagCombine(x: Tag, y: Tag) -> Tag = tag(n: 99)
  fact Combiner[T = Tag, combine = tagCombine]
  sort WitCombiner
    fact Combiner[T = Tag]
    operation combine(x: Tag, y: Tag) -> Tag = tag(n: 5)
  end
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter().any(|e| e.contains("ambiguous provider kinds")),
        "a group holding an UNNAMEABLE candidate keeps the load refusal even though \
         its other candidate is a named witness: {errs:?}"
    );
}

/// THE `Eq` FAMILY IS UNTOUCHED (§6), and by MECHANISM: two `PartialEq` providers
/// for one carrier stay a LOAD error, refused by WI-837's index build. Semantic
/// equality dispatches from UNIFICATION, so there is no call site at which to write
/// a bracket — tier 3 has nowhere to fire and coexistence simply does not apply.
///
/// This row is the one that would have rotted silently: the program was ALSO
/// refused by `AmbiguousWitness` until this ticket, so asserting only "the load
/// fails" would keep passing on the strength of a diagnostic that no longer exists.
/// The identity is asserted.
#[test]
fn two_eq_providers_still_refuse_at_load_by_the_index_build() {
    let src = r#"
namespace wi843.twoeq
  import anthill.prelude.{Int64, Bool, PartialEq}
  sort Coin
    entity coin(n: Int64)
  end
  sort CoinEqA
    fact PartialEq[T = Coin]
    operation eq(a: Coin, b: Coin) -> Bool = true
  end
  sort CoinEqB
    fact PartialEq[T = Coin]
    operation eq(a: Coin, b: Coin) -> Bool = false
  end
end
"#;
    let errs = load_errs(src);
    assert!(
        errs.iter()
            .any(|e| e.contains("ambiguous semantic equality")),
        "two `eq` suppliers for one carrier must be refused by the sem-eq INDEX \
         BUILD (WI-837), the check phase 3b does NOT delete — `eq` dispatches from \
         unification, with no site to select at: {errs:?}"
    );
}

// ── What tier 3 does NOT reach (found by review, each driven) ────────

/// A TIE IN A SUB-GOAL IS NOT A TIE AT THIS CALL, and the message must not pretend
/// otherwise. `PrettyW` provides `Pretty[PT = E]` conditionally on `Show[ST = E]`;
/// the outer goal has ONE provider and the tie is in the `:-` subgoal.
///
/// The first cut stamped the tie with the DISPATCHED goal's spec — filled in two
/// frames above the level that tied — and so said "2 instances provide `Pretty` …
/// write `[Pretty = ShowA]`". Both halves were false, and both were driven:
/// `[Pretty = ShowA]` is *"ShowA does not provide Pretty"*, and the honest key
/// `[Show = ShowA]` is *"unknown type-param 'Show'"* — because §4.5 step 0
/// deliberately keeps a bracket out of sub-resolutions. So NO bracket repairs this
/// shape, and the diagnostic has to say that instead of inventing one.
///
/// Newly reachable: `ShowA`/`ShowB` are one `(Show, Int64)` group, which the deleted
/// load refusal used to reject outright.
#[test]
fn a_subgoal_tie_names_the_subgoal_spec_and_offers_no_bracket() {
    let src = r#"
namespace wi843.subtie
  import anthill.prelude.{Int64}
  sort Show
    sort ST = ?
    operation show(x: ST) -> Int64
  end
  sort ShowA
    fact Show[ST = Int64]
    operation show(x: Int64) -> Int64 = 1
  end
  sort ShowB
    fact Show[ST = Int64]
    operation show(x: Int64) -> Int64 = 2
  end
  sort Pretty
    sort PT = ?
    operation pretty(x: PT) -> Int64
  end
  sort PrettyW
    sort E = ?
    requires Show[ST = E]
    fact Pretty[PT = E]
    operation pretty(x: E) -> Int64 = Show.show(x)
  end
  sort Driver
    operation go(n: Int64) -> Int64 = Pretty.pretty(n)
  end
end
"#;
    let errs = load_errs(src);
    let text = errs.join("\n");
    assert!(
        text.contains("ambiguous dispatch of") && text.contains("SUB-GOAL"),
        "a subgoal tie must be reported AS a subgoal tie: {text}"
    );
    // The tie is over `Show`'s providers, so `Show` is the spec named — naming
    // `Pretty` beside ShowA/ShowB is the false statement this test exists for.
    assert!(
        text.contains("provide `wi843.subtie.Show`")
            && text.contains("wi843.subtie.ShowA")
            && text.contains("wi843.subtie.ShowB"),
        "the spec named must be the one whose providers tied, not the dispatched \
         goal's: {text}"
    );
    assert!(
        !text.contains("provide `wi843.subtie.Pretty`"),
        "ShowA/ShowB do not provide Pretty — saying so is the defect: {text}"
    );
    // Neither spelling exists, so neither may be advertised (both driven).
    assert!(
        !text.contains("[Pretty = ") && !text.contains("[Show = "),
        "no call-site bracket reaches a sub-resolution (§4.5), so none may be \
         suggested: {text}"
    );
}

/// A WIDENING THIS TICKET DID NOT INTEND, recorded as behaviour rather than left to
/// be discovered: two providers in ONE `(spec, carrier)` group whose heads differ in
/// SPECIFICITY are no longer a tie at all. `pick_most_specific` picks the ground one
/// and the call runs, with no diagnostic anywhere.
///
/// That is tier 2's pre-existing rule — WI-841's `selection_overrides_the_search…`
/// depends on it, and §4.1 calls tier 2 "today's rule, unchanged" — reaching a case
/// the deleted load refusal used to make unreachable. §4.1 tier 3 reads as though two
/// providers and no selection is always loud; it is not, when one is strictly more
/// specific. CONTROL: the mixed-kind twin of this program is refused
/// `ambiguous provider kinds … for carrier 'anthill.prelude.List'`, proving both
/// provisions are in ONE group and so were refused before WI-843.
///
/// Pinned, not fixed: making it loud would contradict WI-841's committed acceptance
/// and amounts to a new coherence rule. Recorded in 058 §4.1 and as ticket feedback.
#[test]
fn a_specificity_ordered_pair_silently_takes_the_more_specific() {
    let src = r#"
namespace wi843.specpair
  import anthill.prelude.{Int64, List}
  sort Monoid
    sort T = ?
    operation tag(x: T) -> Int64
  end
  sort GroundListM
    fact Monoid[T = List[T = Int64]]
    operation tag(x: List[T = Int64]) -> Int64 = 111
  end
  sort AnyListM
    sort E = ?
    fact Monoid[T = List[T = E]]
    operation tag(x: List[T = E]) -> Int64 = 222
  end
  sort Driver
    operation go(n: Int64) -> Int64 = Monoid.tag(cons(head: 1, tail: nil()))
  end
end
"#;
    assert_eq!(
        eval_int(
            &src,
            "wi843.specpair.Driver.go",
            "specificity decides, silently"
        ),
        111,
        "the GROUND provider wins by `pick_most_specific`; 222 would mean the \
         parametric one did, and a load error would mean tier 3 grew to cover \
         specificity-ordered pairs (a deliberate change, not a fix)",
    );
}

/// AND THE `Eq` SCOPE, stated exactly. `AmbiguousEqDispatch` refuses two distinct
/// `eq` TARGETS; a second provision that supplies no `eq` contributes no candidate
/// and is not refused. That pair loads, and equality answers by the ONE supplier
/// there is — not structurally, which is what §6 actually promises.
///
/// The deleted spec-generic refusal used to reject this incidentally, by counting
/// PROVISIONS rather than dictionaries. Asserted so the narrower scope is a stated
/// property rather than a gap someone rediscovers.
#[test]
fn a_bare_co_provision_of_partial_eq_is_not_an_eq_ambiguity() {
    let src = r#"
namespace wi843.bareeq
  import anthill.prelude.{Int64, Bool, PartialEq}
  sort Coin
    entity coin(n: Int64)
  end
  sort CoinEqA
    provides PartialEq[T = Coin]
    operation eq(a: Coin, b: Coin) -> Bool = true
  end
  sort CoinEqB
    provides PartialEq[T = Coin]
  end
end
"#;
    loads_clean(
        src,
        "one `eq` supplier beside a provision that supplies none is ONE dictionary, \
         not an ambiguity — the pair coexists (058 tier 3)",
    );
}

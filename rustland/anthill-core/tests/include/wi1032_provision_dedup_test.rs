//! WI-1032 — two provisions that say the same thing are ONE dispatch candidate.
//!
//! WI-1027 recorded a bad rendering rather than fixing it: with the carrier ALSO
//! self-providing the spec, a route-1-vs-route-2 supplier conflict reached
//! `DispatchOutcome::Ambiguous` and printed `2 instances provide Desc (Leaf, Leaf)` —
//! one carrier named twice — with `TieRepair::ValueDirected`, whose repair ("pin the
//! carrier through the call's receiver") cannot apply because the carrier IS pinned.
//! That is the exact rendering WI-1012 gave the supplier tie its own variant to avoid.
//!
//! DRIVING IT FOUND A SECOND, WORSE DEFECT FROM THE SAME CAUSE, and it is the reason
//! this is a fix rather than a rewording. Drop the fact's op binding — `sort Leaf {
//! provides Desc[T = Leaf]; operation describe … }` beside a bare namespace-level
//! `fact Desc[T = Leaf]` — and there is no conflict at all: ONE dictionary written in
//! two places. MEASURED: it was REFUSED at the call, with the same `(Leaf, Leaf)`
//! message. A program with a single implementation, rejected.
//!
//! WHICH COHERENCE CELL THAT IS — stated because the first cut of this file said
//! (1 fact, 0 witnesses, 1 self-provider) and review MEASURED otherwise. `Provider::Fact`
//! is recorded only when the provision BINDS an op (`binding_op_symbol` demands a
//! `SymbolKind::Operation` value) and a bare `fact Desc[T = Leaf]` binds a SORT, so both
//! provisions classify as `SelfProvider(Leaf)`, `record` collapses them, and the group
//! holds ONE — cell (0, 0, 1), which the size gate skips. WI-859's arm never sees this
//! shape, so nothing here falsifies its licence; the fixture that IS in (1, 0, 1) is
//! `a_supplier_conflict_behind_a_self_provision_reports_by_route` below, which genuinely
//! has a conflict — exactly what the licence covers.
//!
//! THE CAUSE IS ONE MISSING DEDUP, and the rule was already written down one layer over.
//! `Provider::SelfProvider`'s doc says it: "Two self-provisions of one spec by one carrier
//! are therefore ONE candidate, which is right: they name one member set, and a
//! disagreement between their BINDINGS is `ConflictingProvisionBindings`'s (WI-842), not a
//! second dictionary." The LOAD grouping applied it; `collect_provides_candidates` built
//! two structurally IDENTICAL `Candidate`s and `pick_most_specific` refused to choose.
//!
//! WHY DEDUP IS NOT FIRST-MATCH, the distinction the whole 058 §4.9 hardening turns on:
//! a `Candidate` is `(impl_sort, resolved_head_bindings, impl_subst, head_specificity)`,
//! and every downstream product — the resolved tree node, the subgoals
//! `requires_chain(impl_sort)` instantiates through `impl_subst` — is a function of
//! exactly those. Two EQUAL candidates therefore resolve identically, so picking either
//! is picking the same thing. Candidates differing in ANY field are all kept, and
//! `pick_most_specific` still refuses among them: `a_specificity_ordered_pair_silently_
//! takes_the_more_specific` (wi843) and `a_two_provider_value_directed_dispatch_names_
//! both_candidates` (wi842) are the controls, and both stay green.
//!
//! AND IT FIXES THE RENDERING BY ROUTING, not by rewording. The op-binding leg is the
//! reason: the candidate loop `continue`s on any binding that is not a spec TYPE param,
//! so a `fact Desc[T = Leaf, describe = otherDescribe]` differs from a bare
//! `provides Desc[T = Leaf]` in NOTHING `Candidate` records. Deduping collapses that
//! pair too — which is right, because as *provisions* they agree — and the genuine
//! conflict then reaches the reader that can see it: WI-1027's supplier tie, which names
//! both texts BY SUPPLY ROUTE (`the carrier's own member 'Leaf.describe'` vs `an
//! instance fact binding describe = otherDescribe`) and offers `KeepOne`.
//!
//! THE COLLECTOR'S DEDUP IS NOT THE WHOLE FIX, and the first cut of this file claimed it
//! was — "no remaining driver, so a dedup in `render_instance_tie` would be untested
//! code". REVIEW BUILT THE DRIVER. The shape I tried (one provision binding a second type
//! param, the other omitting it) does not tie, because the ground binding raises
//! `head_specificity` and tier 2 picks it. But two provisions binding DIFFERENT extra
//! params — `provides Desc[T = Leaf, A = Int64]` beside `fact Desc[T = Leaf, B = Int64]` —
//! both score +1, tie at equal specificity, and differ in `resolved_head_bindings`, so the
//! collector cannot collapse them. MEASURED with the collector dedup already in place:
//! `2 instances provide Desc (Leaf, Leaf) … Pin the carrier through the call's receiver` —
//! the defect verbatim.
//!
//! So `render_instance_tie` now dedups the rendered names BY CANONICAL PROVIDER, and when
//! that leaves one name the repair is `TieRepair::OneProviderTwoProvisions` — because no
//! bracket separates a provider from itself, and `ValueDirected`'s "pin the carrier" is
//! advice for a carrier already pinned. Driven by
//! `one_carrier_two_disagreeing_provisions_names_it_once`.
//!
//! WHAT FAILS IF THIS IS BACKED OUT (back out = push every candidate unconditionally) —
//! MEASURED:
//!
//! | test | backed out |
//! |---|---|
//! | `agreeing_provisions_are_one_dictionary_and_still_dispatch` | **FAILS** (refused) |
//! | `a_supplier_conflict_behind_a_self_provision_reports_by_route` | **FAILS** (`Leaf, Leaf`) |
//! | `identical_facts_in_two_namespaces_are_one_candidate` | **FAILS** (refused) |
//! | `two_identical_namespace_facts_still_dispatch` | ok — **by design** |
//! | `a_specificity_ordered_pair_still_takes_the_more_specific` | ok — **by design** |
//! | `one_carrier_two_disagreeing_provisions_names_it_once` | ok (the RENDERER's row) |
//!
//! Two of those are the controls a dedup must not consume: an already-working shape
//! (byte-identical facts in ONE namespace hash-cons to a single fact, so they never made
//! two candidates), and tier-2 specificity, which must keep choosing rather than be
//! collapsed into. The last row has its own back-out: revert `render_instance_tie`'s name
//! dedup and it FAILS, while the four above stay green — two independent changes, two
//! independent controls.
//!
//! AND IT IS THE CONTROL FOR "DEDUP IS NOT FIRST-MATCH", the file's central claim, which
//! review found nothing else discriminated: replace the collector's field-wise equality
//! with an `impl_sort`-only compare — literal first-match within a carrier — and the four
//! rows above ALL still pass, because every one of their candidate pairs shares a carrier
//! whose `sort_ops_lookup` answers the same op either way. That fixture's two candidates
//! differ ONLY in `resolved_head_bindings`, so an `impl_sort`-only compare collapses them,
//! the tie disappears and the program loads clean — which is what its assertion catches.
//!
//! REFERENCE: WI-1027; WI-859; WI-1012; WI-843; `docs/design/058-implementation.md` §15.

use crate::wi1012_static_supplier_tie_test::refusal;

/// A body-less `Desc.describe`, a concrete `Leaf` owning it, and whatever `tail` adds at
/// namespace level. `leaf_extra` writes the carrier's own provision when present.
fn program(ns: &str, leaf_extra: &str, tail: &str) -> String {
    format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
{leaf_extra}    operation describe(x: Leaf) -> Int64 = 7
  end
{tail}
  operation probe() -> Int64 = Desc.describe(leaf())
end
"#
    )
}

const SELF_PROVISION: &str = "    provides Desc[T = Leaf]\n";

/// THE HEADLINE, and the defect that made this a fix rather than a rewording. The
/// carrier's own provision beside a bare namespace fact for the same carrier is ONE
/// dictionary written twice — WI-859's admitted cell — and there is exactly one
/// implementation in the program.
///
/// MEASURED before the dedup: REFUSED, `2 instances provide test…Desc (test…Leaf,
/// test…Leaf) … Pin the carrier through the call's receiver or its expected result type`.
/// The carrier was already pinned; nothing the author could write would have helped.
#[test]
fn agreeing_provisions_are_one_dictionary_and_still_dispatch() {
    let ns = "test.wi1032.agree";
    let src = program(ns, SELF_PROVISION, "\n  fact Desc[T = Leaf]\n");
    assert_eq!(
        crate::wi1010_defaulted_op_instance_fact_test::probe(ns, &src),
        7,
        "the two provisions AGREE — same carrier, same bindings, neither supplying an op \
         — so they are one candidate and the call must dispatch to `Leaf.describe`",
    );
}

/// THE RENDERING WI-1027 RECORDED, now routed to the reader that can see the conflict.
/// The same pair with the fact BINDING a different operation IS a genuine conflict; as
/// PROVISIONS the two still agree (an op binding is not a type-param binding, so it never
/// reaches `Candidate`), so they collapse to one candidate and the tie surfaces where it
/// belongs — at WI-1027's supplier guard, named by supply route.
///
/// MEASURED before the dedup: `2 instances provide … (Leaf, Leaf)` with
/// `TieRepair::ValueDirected`. Both halves of that are asserted against below, since a
/// rewording that kept the wrong repair would satisfy a `contains` check on the names.
#[test]
fn a_supplier_conflict_behind_a_self_provision_reports_by_route() {
    let ns = "test.wi1032.conflict";
    let msg = refusal(&program(
        ns,
        SELF_PROVISION,
        "\n  operation otherDescribe(x: Leaf) -> Int64 = 9\n\n  \
         fact Desc[T = Leaf, describe = otherDescribe]\n",
    ));
    assert!(
        msg.contains(&format!("the carrier's own member '{ns}.Leaf.describe'"))
            && msg.contains(&format!("an instance fact binding `describe = {ns}.otherDescribe`")),
        "the conflict must be named by SUPPLY ROUTE — which text to delete: {msg}",
    );
    assert_eq!(
        msg.matches(&format!("{ns}.Leaf`")).count(),
        1,
        "the carrier is named ONCE; `(Leaf, Leaf)` was the defect: {msg}",
    );
    assert!(
        !msg.contains("instances provide"),
        "this is a SUPPLIER tie, not a provider tie — the provisions agree: {msg}",
    );
    assert!(
        !msg.contains("Pin the carrier through the call's receiver"),
        "`TieRepair::ValueDirected` advises pinning a carrier that is already pinned — \
         the repair WI-1012 gave this tie its own variant to avoid: {msg}",
    );
}

/// CONTROL — the shape that ALREADY worked, so the dedup cannot be credited for it. Two
/// byte-identical facts IN ONE NAMESPACE hash-cons to a single fact, so they never
/// reached the collector as two candidates; this pins that the fix did not change them.
///
/// "In one namespace" is load-bearing and was missing from the first cut of this doc —
/// review MEASURED that the SAME two facts written in two different namespaces are TWO
/// `SortProvidesInfo` facts, and that shape did NOT already work. It is the test below.
#[test]
fn two_identical_namespace_facts_still_dispatch() {
    let ns = "test.wi1032.identical";
    let src = program(ns, "", "\n  fact Desc[T = Leaf]\n\n  fact Desc[T = Leaf]\n");
    assert_eq!(
        crate::wi1010_defaulted_op_instance_fact_test::probe(ns, &src),
        7,
        "identical facts are one fact before dispatch ever sees them",
    );
}

/// THE SHAPE THE FIRST CUT MISSED, found by review MEASURING the control above rather
/// than believing it. Hash-consing collapses two identical facts only within ONE file's
/// namespace; the same `fact Desc[T = Leaf]` written in a SECOND namespace that imports
/// the sorts is a distinct fact, so the collector really did see two candidates and the
/// call really was refused.
///
/// This is the retroactive-instance shape WI-431 exists to support — a downstream
/// namespace asserting an instance for a sort it did not declare — so it is the spelling a
/// real program is most likely to hit, and the one the ticket's own blast-radius statement
/// understated.
#[test]
fn identical_facts_in_two_namespaces_are_one_candidate() {
    let base = "test.wi1032.xns.base";
    let other = "test.wi1032.xns.other";
    let src = format!(
        r#"namespace {base}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    operation describe(x: Leaf) -> Int64 = 7
  end

  fact Desc[T = Leaf]

  operation probe() -> Int64 = Desc.describe(leaf())
end

namespace {other}
  import {base}.{{Desc, Leaf}}

  fact Desc[T = Leaf]
end
"#
    );
    assert_eq!(
        crate::wi1010_defaulted_op_instance_fact_test::probe(base, &src),
        7,
        "the second namespace asserts the SAME instance — one dictionary, two files — so \
         it must not turn a working call into `2 instances provide … (Leaf, Leaf)`",
    );
}

/// CONTROL — the answer a dedup must NOT consume: two candidates that differ, resolved by
/// tier-2 SPECIFICITY rather than collapsed. Two provisions of one spec for one carrier
/// differing in whether they bind a second TYPE param have different
/// `resolved_head_bindings`, so the collector keeps both and `pick_most_specific` takes
/// the ground one.
///
/// This is also the shape whose absence of a tie is why `render_instance_tie` did NOT get
/// a defensive name-dedup: it was the remaining candidate driver for a duplicate name, and
/// it does not tie. MEASURED — answers 7, no diagnostic.
#[test]
fn a_specificity_ordered_pair_still_takes_the_more_specific() {
    let ns = "test.wi1032.specificity";
    let src = format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Iter
    sort Self = ?
    sort Element = ?
    operation nxt(i: Self) -> Element
  end

  sort C
    import anthill.prelude.Int64
    entity c
    fact Iter[Self = C]
    fact Iter[Self = C, Element = Int64]
    operation nxt(i: C) -> Int64 = 7
  end

  operation probe() -> Int64 = Iter.nxt(c())
end
"#
    );
    assert_eq!(
        crate::wi1010_defaulted_op_instance_fact_test::probe(ns, &src),
        7,
        "the two provisions differ in a TYPE-param binding, so they stay two candidates \
         and tier 2 picks the ground one — collapsing them would be first-match",
    );
}

/// THE RENDERER'S OWN DEFECT, which the collector's dedup does NOT reach — built by review
/// after this file claimed no driver existed.
///
/// Two provisions of ONE carrier binding DIFFERENT extra type params. Both score +1 in
/// `match_candidate_against_goal` (the goal leaves `A` and `B` unresolved, and
/// `dispatch_values_match` accepts a var against a concrete value), so they tie at equal
/// specificity — and they differ in `resolved_head_bindings`, so the collector keeps both.
/// MEASURED with the collector dedup in place: `2 instances provide Desc (…Leaf, …Leaf)`
/// with `TieRepair::ValueDirected`.
///
/// It is ALSO this file's control for "dedup is not first-match": an `impl_sort`-only
/// compare in the collector would swallow this pair and the program would load clean.
#[test]
fn one_carrier_two_disagreeing_provisions_names_it_once() {
    let ns = "test.wi1032.twoprovisions";
    let msg = refusal(&format!(
        r#"namespace {ns}
  import anthill.prelude.Int64

  sort Desc
    sort T = ?
    sort A = ?
    sort B = ?
    operation describe(x: T) -> Int64
  end

  sort Leaf
    import anthill.prelude.Int64
    entity leaf
    provides Desc[T = Leaf, A = Int64]
    operation describe(x: Leaf) -> Int64 = 7
  end

  fact Desc[T = Leaf, B = Int64]

  operation probe() -> Int64 = Desc.describe(leaf())
end
"#
    ));
    assert_eq!(
        msg.matches(&format!("{ns}.Leaf")).count(),
        1,
        "ONE provider, named once — `(Leaf, Leaf)` was the defect: {msg}",
    );
    assert!(
        msg.contains("1 instances provide"),
        "the count is of distinct PROVIDERS, so it must follow the deduped list: {msg}",
    );
    assert!(
        !msg.contains("Pin the carrier through the call's receiver"),
        "`ValueDirected` advises pinning a carrier that is already pinned: {msg}",
    );
    assert!(
        msg.contains("ONE provider reached through several provisions")
            && msg.contains("write the provisions as ONE"),
        "the repair must be the one that applies — make them one provision: {msg}",
    );
}

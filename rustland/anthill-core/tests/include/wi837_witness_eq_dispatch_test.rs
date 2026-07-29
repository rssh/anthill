//! WI-837 (proposal 058 §4.9) — a WI-450 WITNESS-supplied `eq` must key the
//! semantic-equality dispatch index, and a SECOND `eq` for one carrier must be a
//! LOAD error raised by the index build itself.
//!
//! ```anthill
//! sort Pebble
//!   entity pebble(n: Int64)
//! end
//! sort PebbleEq
//!   provides PartialEq[T = Pebble]
//!   operation eq(a: Pebble, b: Pebble) -> Bool = true    -- deliberately NON-structural
//! end
//! ```
//!
//! Before this ticket the index build consulted only the carrier's OWN `eq`
//! (WI-616) and a CARRIER-KEYED instance fact (WI-625 gap 2). A witness provision's
//! `sort_ref` is the WITNESS (`PebbleEq`), not the carrier, so it was invisible to
//! both — and semantic eq/neq reads *only* that index (`sem_eq_dispatch_target`),
//! never the `witness_provision` route the other dispatch paths use. The witness's
//! `eq` was therefore ignored and equality silently answered STRUCTURALLY.
//!
//! That silent degradation is also a SOUNDNESS GATE for 058 phase 3b, which deletes
//! the spec-generic `AmbiguousWitness` refusal — today the only thing stopping two
//! `PartialEq` witnesses for one carrier. §4.9's hardening refuses a second
//! candidate AT THE INDEX BUILD, but no witness ever reached the index, so the pair
//! would have coexisted with no diagnostic from either check. Hence the ambiguity
//! test below asserts the DIAGNOSTIC IDENTITY, not merely that the load fails:
//! `AmbiguousWitness` refuses that program today, so a failure-only assertion would
//! pass with nothing implemented.

use anthill_core::eval::Value;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

/// The witness's `eq` answers `true` for ANY two pebbles — structurally distinct
/// operands (`pebble(1)` vs `pebble(2)` — the reflexivity shortcut settles
/// identical ones before dispatch is ever consulted) are EQUAL iff the witness ran.
const WITNESS_SRC: &str = r#"namespace test.wi837
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Pebble
    entity pebble(n: Int64)
  end

  sort PebbleEq
    provides PartialEq[T = Pebble]
    operation eq(a: Pebble, b: Pebble) -> Bool = true
  end

  rule peq(?x, ?y) :- eq(?x, ?y)
  rule pneq(?x, ?y) :- neq(?x, ?y)
end
"#;

/// `ctor_qn(f1: v1, …)` as a term. Every carrier in this file is a one- or
/// two-field entity, so the tests differ only in the qualified name and the values.
fn entity_term(kb: &mut KnowledgeBase, ctor_qn: &str, fields: &[(&str, i64)]) -> TermId {
    let functor = kb.try_resolve_symbol(ctor_qn).unwrap_or_else(|| panic!("{ctor_qn}"));
    let named = fields
        .iter()
        .map(|&(name, v)| {
            let sym = kb.intern(name);
            let val = kb.alloc(Term::Const(Literal::Int(v)));
            (sym, val)
        })
        .collect::<Vec<_>>();
    kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&named),
    })
}

/// Solutions of `pred_qn(x, y)` — each carrier's `eq` answers true for ANY pair, so
/// ONE solution means the index dispatched and NONE means it answered structurally.
fn solutions(kb: &mut KnowledgeBase, pred_qn: &str, x: TermId, y: TermId) -> usize {
    let functor = kb.try_resolve_symbol(pred_qn).unwrap_or_else(|| panic!("{pred_qn}"));
    let goal = kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::from_slice(&[x, y]),
        named_args: SmallVec::new(),
    });
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// Load `src` and count solutions of `pred_qn` over two distinct `ctor_qn` values.
fn eq_solutions(src: &str, pred_qn: &str, ctor_qn: &str, fields: &[&str]) -> usize {
    let mut kb = crate::common::load_kb_with(src);
    let mk = |kb: &mut KnowledgeBase, base: i64| {
        let vals: Vec<(&str, i64)> =
            fields.iter().enumerate().map(|(i, &f)| (f, base + i as i64)).collect();
        entity_term(kb, ctor_qn, &vals)
    };
    let (x, y) = (mk(&mut kb, 1), mk(&mut kb, 100));
    solutions(&mut kb, pred_qn, x, y)
}

/// Assert `src` fails to load with a diagnostic containing every needle. Asserting
/// the diagnostic IDENTITY, not merely that the load fails, is load-bearing here:
/// the spec-generic `AmbiguousWitness` / `MixedProviderKinds` refuse some of these
/// programs already, so a failure-only assertion would pass with nothing implemented.
fn assert_refused(src: &str, needles: &[&str], why: &str) {
    let errs = crate::common::try_load_kb_with(src).err().unwrap_or_default();
    assert!(
        errs.iter().any(|e| needles.iter().all(|n| e.contains(n))),
        "{why}; expected one diagnostic containing all of {needles:?}, got:\n{}",
        errs.join("\n"),
    );
}

fn pebble_term(kb: &mut KnowledgeBase, n: i64) -> TermId {
    entity_term(kb, "test.wi837.Pebble.pebble", &[("n", n)])
}

/// Solutions of `test.wi837.<pred>(pebble(a), pebble(b))` — the RESOLVER's
/// `eq`/`neq` builtin as a rule-body goal.
fn resolver_solutions(kb: &mut KnowledgeBase, pred: &str, a: i64, b: i64) -> usize {
    let (x, y) = (pebble_term(kb, a), pebble_term(kb, b));
    solutions(kb, &format!("test.wi837.{pred}"), x, y)
}

// ── The witness's `eq` reaches BOTH backends ─────────────────────────────────

/// RESOLVER — `eq(pebble(1), pebble(2))` over structurally DISTINCT operands
/// dispatches to `PebbleEq.eq`, which answers `true`. A structural verdict (the
/// pre-WI-837 answer) is 0 solutions.
#[test]
fn witness_eq_dispatches_at_the_resolver() {
    let mut kb = crate::common::load_kb_with(WITNESS_SRC);
    assert_eq!(
        resolver_solutions(&mut kb, "peq", 1, 2),
        1,
        "eq(pebble(1), pebble(2)) must dispatch to the witness PebbleEq.eq (always true); \
         0 solutions means the index never saw the witness and equality answered structurally"
    );
}

/// RESOLVER — the negation follows the same dispatch: `neq` of two pebbles the
/// witness calls equal must FAIL. Pins that the witness's verdict is what is
/// negated, rather than `neq` keeping an independent structural answer.
#[test]
fn witness_eq_dispatch_drives_neq_at_the_resolver() {
    let mut kb = crate::common::load_kb_with(WITNESS_SRC);
    assert_eq!(
        resolver_solutions(&mut kb, "pneq", 1, 2),
        0,
        "neq(pebble(1), pebble(2)) must be FALSE — the witness calls them equal"
    );
}

/// INTERPRETER — the eval-side twin, through the `PartialEq.eq` builtin
/// (`semantic_equal`, which probes the same index). Both backends must agree, or a
/// program answers differently by backend.
#[test]
fn witness_eq_dispatches_at_the_interpreter() {
    let mut i = crate::common::interp_for(WITNESS_SRC);
    let a = Value::term(pebble_term(i.kb_mut(), 1));
    let b = Value::term(pebble_term(i.kb_mut(), 2));
    let got = i
        .call("anthill.prelude.PartialEq.eq", &[a, b])
        .expect("PartialEq.eq")
        .as_bool()
        .expect("PartialEq.eq returns a Bool");
    assert!(
        got,
        "eval `eq(pebble(1), pebble(2))` must dispatch to the witness PebbleEq.eq (always true); \
         false is the structural answer the index used to give"
    );
}

/// CONTROL — the witness's `eq` is reached because of the PROVISION, not because
/// any `eq` member anywhere keys every carrier. `PebbleEq provides PartialEq[T =
/// Pebble]` names `Pebble`; an unrelated carrier keeps structural equality.
#[test]
fn an_unprovided_carrier_keeps_structural_equality() {
    let src = r#"namespace test.wi837.control
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Pebble
    entity pebble(n: Int64)
  end
  sort Stone
    entity stone(n: Int64)
  end

  sort PebbleEq
    provides PartialEq[T = Pebble]
    operation eq(a: Pebble, b: Pebble) -> Bool = true
  end

  rule seq(?x, ?y) :- eq(?x, ?y)
end
"#;
    assert_eq!(
        eq_solutions(src, "test.wi837.control.seq", "test.wi837.control.Stone.stone", &["n"]),
        0,
        "Stone has no eq provider — it must keep structural equality, not inherit PebbleEq's"
    );
}

// ── The index build refuses a second candidate ───────────────────────────────

/// Two `PartialEq` WITNESSES for one carrier are refused BY THE INDEX BUILD, naming
/// both providers. Asserted on the diagnostic IDENTITY (`ambiguous semantic
/// equality`, plus both witness sort names) rather than on failure: the
/// spec-generic `AmbiguousWitness` also refuses this program today, so a
/// failure-only assertion would pass with nothing implemented — and it is exactly
/// that check 058 phase 3b deletes.
#[test]
fn two_witness_eq_providers_are_refused_by_the_index_build() {
    let src = r#"namespace test.wi837.twowitness
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Pebble
    entity pebble(n: Int64)
  end

  sort PebbleEqA
    provides PartialEq[T = Pebble]
    operation eq(a: Pebble, b: Pebble) -> Bool = true
  end
  sort PebbleEqB
    provides PartialEq[T = Pebble]
    operation eq(a: Pebble, b: Pebble) -> Bool = false
  end
end
"#;
    assert_refused(
        src,
        &["ambiguous semantic equality", "Pebble", "PebbleEqA", "PebbleEqB"],
        "two PartialEq witnesses for Pebble must be refused BY THE INDEX BUILD, naming both \
         providers (not only by the spec-generic AmbiguousWitness, which phase 3b deletes)",
    );
}

/// The MIXED shape the index sees but no per-kind check does: an instance fact's
/// `eq` binding beside a WITNESS's `eq` member. WI-838's cross-kind grouping is
/// scoped to op-BINDING facts and abstract witnesses; here both supply `eq` for one
/// carrier, and the index can key only one — so the refusal must come from the
/// index build, naming the fact's op and the witness sort.
#[test]
fn a_fact_bound_eq_beside_a_witness_eq_is_refused() {
    let src = r#"namespace test.wi837.mixed
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Pebble
    entity pebble(n: Int64)
  end

  operation pebbleEq(a: Pebble, b: Pebble) -> Bool = true

  fact PartialEq[T = Pebble, eq = pebbleEq]

  sort PebbleEqW
    provides PartialEq[T = Pebble]
    operation eq(a: Pebble, b: Pebble) -> Bool = false
  end
end
"#;
    assert_refused(
        src,
        &["ambiguous semantic equality", "pebbleEq", "PebbleEqW"],
        "an instance-fact `eq` binding beside a witness `eq` member is two dictionaries for one \
         index entry and must be refused, naming both",
    );
}

/// A carrier's OWN `eq` member beside a retroactive fact binding a DIFFERENT `eq`
/// is the same conflict in the two pre-existing routes — it loaded clean before
/// WI-837 and the carrier's own member silently won by `or_else` precedence.
#[test]
fn an_own_eq_beside_a_fact_bound_eq_is_refused() {
    let src = r#"namespace test.wi837.ownplusfact
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Pebble
    entity pebble(n: Int64)
    provides PartialEq[T = Pebble]
    operation eq(a: Pebble, b: Pebble) -> Bool = true
  end

  operation otherEq(a: Pebble, b: Pebble) -> Bool = false

  fact PartialEq[T = Pebble, eq = otherEq]
end
"#;
    assert_refused(
        src,
        &["ambiguous semantic equality", "otherEq", "Pebble.eq"],
        "a carrier's own `eq` beside a fact binding a different `eq` must be refused, naming both",
    );
}

/// SIBLING BLIND SPOT (same audit) — a first `SortProvidesInfo` fact for
/// `(Pebble, PartialEq)` that binds NO `eq` used to HIDE a later one that does:
/// the carrier-keyed reader `provider_spec_view_bindings` returns at its first
/// (spec, carrier) match, so the type-only `provides PartialEq[T = Pebble]` block
/// answered for the whole carrier and the index silently degraded to structural
/// equality. Collecting every supplier rather than the first retires it here; the
/// reader itself is still first-match for its ~15 other call sites, which is 058
/// phase 3a's scope, not this ticket's.
#[test]
fn a_type_only_provision_does_not_hide_a_later_eq_binding() {
    let src = r#"namespace test.wi837.hidden
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Pebble
    entity pebble(n: Int64)
    provides PartialEq[T = Pebble]
  end

  operation pebbleEq(a: Pebble, b: Pebble) -> Bool = true

  fact PartialEq[T = Pebble, eq = pebbleEq]

  rule peq(?x, ?y) :- eq(?x, ?y)
end
"#;
    assert_eq!(
        eq_solutions(src, "test.wi837.hidden.peq", "test.wi837.hidden.Pebble.pebble", &["n"]),
        1,
        "the type-only `provides PartialEq[T = Pebble]` must not hide the later \
         `fact PartialEq[T = Pebble, eq = pebbleEq]` — 0 solutions is the structural answer"
    );
}

// ── The pre-existing routes are unchanged ────────────────────────────────────

/// CONTROL — ONE witness is not an ambiguity: the single-candidate program above
/// loads clean. Without this, the two refusal tests could be passing because the
/// witness route now over-refuses.
#[test]
fn a_single_witness_eq_loads_clean() {
    if let Err(errs) = crate::common::try_load_kb_with(WITNESS_SRC) {
        panic!("a lone PartialEq witness for Pebble must load clean; got:\n{}", errs.join("\n"));
    }
}

/// CONTROL — the carrier's OWN `eq` still keys the index and still wins as the sole
/// candidate when the carrier's provision binds no op (`provides PartialEq[T = C]`
/// is type-only, so it supplies nothing and cannot collide with the member).
#[test]
fn a_carrier_own_eq_still_dispatches() {
    let src = r#"namespace test.wi837.own
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Pebble
    entity pebble(n: Int64)
    provides PartialEq[T = Pebble]
    operation eq(a: Pebble, b: Pebble) -> Bool = true
  end

  rule peq(?x, ?y) :- eq(?x, ?y)
end
"#;
    assert_eq!(
        eq_solutions(src, "test.wi837.own.peq", "test.wi837.own.Pebble.pebble", &["n"]),
        1,
        "the carrier's own `eq` member must still key the index (WI-616 route unchanged)"
    );
}

// ── The index's DOMAIN, pinned (a pre-existing gap, not this ticket's) ────────

/// WI-837 shares ONE predicate between the eq index build and WI-664's lawful-Eq
/// boundary classifier — but the two enumerate DIFFERENT sort universes, and this
/// pair of tests pins that so the shared predicate is not misread as a shared
/// domain. The index build derives its carriers from `SortInfo` facts, which only a
/// `sort … end` block emits; a NAMESPACE-LEVEL entity is its own carrier with no
/// `SortInfo`, so its `eq` supplier never keys the index and equality stays
/// STRUCTURAL. Measured on both arms of one otherwise-identical program.
///
/// PRE-EXISTING and independent of the witness route: the index build has always
/// walked the `SortInfo`-derived sort list, so the WI-625 gap-2 instance-fact route
/// used here degrades identically. Recorded rather than fixed — widening the domain
/// would newly key every free-standing entity and is its own increment (WI-856).
const NS_ENTITY_SRC: &str = r#"namespace test.wi837.nsent
  import anthill.prelude.{Int64, Bool, PartialEq}

  entity binding(n: Int64, note: Int64)

  operation bindEq(a: binding, b: binding) -> Bool = true

  fact PartialEq[T = binding, eq = bindEq]

  rule beq(?x, ?y) :- eq(?x, ?y)
end
"#;

/// The same program with the entity wrapped in a `sort`.
const SORT_ENTITY_SRC: &str = r#"namespace test.wi837.sortent
  import anthill.prelude.{Int64, Bool, PartialEq}

  sort Binding
    entity binding(n: Int64, note: Int64)
  end

  operation bindEq(a: Binding, b: Binding) -> Bool = true

  fact PartialEq[T = Binding, eq = bindEq]

  rule beq(?x, ?y) :- eq(?x, ?y)
end
"#;

#[test]
fn a_sort_wrapped_entity_carrier_keys_the_index() {
    assert_eq!(
        eq_solutions(SORT_ENTITY_SRC, "test.wi837.sortent.beq", "test.wi837.sortent.Binding.binding", &["n", "note"]),
        1,
        "the control arm: a `sort`-wrapped carrier's instance-fact `eq` dispatches"
    );
}

#[test]
fn a_namespace_level_entity_carrier_does_not_key_the_index() {
    assert_eq!(
        eq_solutions(NS_ENTITY_SRC, "test.wi837.nsent.beq", "test.wi837.nsent.binding", &["n", "note"]),
        0,
        "PINS A KNOWN GAP (WI-856), not a desired behaviour: a namespace-level entity emits no \
         `SortInfo`, so the index build never enumerates it and its `eq` supplier is ignored. \
         If this starts returning 1 the gap was closed — update the doc on `is_eq_boundary` \
         (kb/eq_derive.rs), which cites this asymmetry, and delete this test's premise"
    );
}

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
//!
//! WI-856 continues in the same file (last section) because it closes the DOMAIN gap
//! WI-837 measured and pinned here: the index build enumerated `SortInfo` sorts only,
//! so a NAMESPACE-LEVEL entity carrier — its own carrier, emitting no `SortInfo` —
//! never keyed the index at all, whatever route supplied its `eq`.

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
  import anthill.prelude.PartialEq.{neq, eq}

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
pub(crate) fn entity_term(kb: &mut KnowledgeBase, ctor_qn: &str, fields: &[(&str, i64)]) -> TermId {
    let functor = kb
        .try_resolve_symbol(ctor_qn)
        .unwrap_or_else(|| panic!("{ctor_qn}"));
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
pub(crate) fn solutions(kb: &mut KnowledgeBase, pred_qn: &str, x: TermId, y: TermId) -> usize {
    let functor = kb
        .try_resolve_symbol(pred_qn)
        .unwrap_or_else(|| panic!("{pred_qn}"));
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
        let vals: Vec<(&str, i64)> = fields
            .iter()
            .enumerate()
            .map(|(i, &f)| (f, base + i as i64))
            .collect();
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
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.iter().any(|e| needles.iter().all(|n| e.contains(n))),
        "{why}; expected one diagnostic containing all of {needles:?}, got:\n{}",
        errs.join("\n"),
    );
}

/// The positive twin of [`assert_refused`] — `src` loads with NO diagnostic. Every
/// refusal test in this file needs one: without it a refusal can be passing because
/// the check over-refuses the one-supplier shape too. `common::load_kb_with` is not a
/// substitute — it panics with a generic "load failed with N errors" and drops the
/// per-test rationale, which is the whole content of a control.
pub(crate) fn assert_loads_clean(src: &str, why: &str) {
    if let Err(errs) = crate::common::try_load_kb_with(src) {
        panic!("{why}; got:\n{}", errs.join("\n"));
    }
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
  import anthill.prelude.PartialEq.{eq}

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
        eq_solutions(
            src,
            "test.wi837.control.seq",
            "test.wi837.control.Stone.stone",
            &["n"]
        ),
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
        &[
            "ambiguous semantic equality",
            "carrier 'test.wi837.twowitness.Pebble'",
            "PebbleEqA",
            "PebbleEqB",
        ],
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
  import anthill.prelude.PartialEq.{eq}

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
        eq_solutions(
            src,
            "test.wi837.hidden.peq",
            "test.wi837.hidden.Pebble.pebble",
            &["n"]
        ),
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
    assert_loads_clean(
        WITNESS_SRC,
        "a lone PartialEq witness for Pebble must load clean",
    );
}

/// CONTROL — the carrier's OWN `eq` still keys the index and still wins as the sole
/// candidate when the carrier's provision binds no op (`provides PartialEq[T = C]`
/// is type-only, so it supplies nothing and cannot collide with the member).
#[test]
fn a_carrier_own_eq_still_dispatches() {
    let src = r#"namespace test.wi837.own
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq}

  sort Pebble
    entity pebble(n: Int64)
    provides PartialEq[T = Pebble]
    operation eq(a: Pebble, b: Pebble) -> Bool = true
  end

  rule peq(?x, ?y) :- eq(?x, ?y)
end
"#;
    assert_eq!(
        eq_solutions(
            src,
            "test.wi837.own.peq",
            "test.wi837.own.Pebble.pebble",
            &["n"]
        ),
        1,
        "the carrier's own `eq` member must still key the index (WI-616 route unchanged)"
    );
}

/// A WITNESS that BINDS `eq` in its provision rather than declaring a member —
/// `sort W provides PartialEq[T = C, eq = f]` — supplies it too. Both spellings load
/// today and the two kinds are independent choices of SYNTAX, not of meaning, so a
/// supplier walk that read only the usual leg per kind dropped this one on a silent
/// `continue`: the written `eq = pebbleEq` never keyed the index, equality answered
/// structurally, and nothing anywhere said so. (Found in review of this ticket, and a
/// `continue` that hides a written declaration is exactly what CLAUDE.md's
/// "loud error over silent skip" principle forbids.)
#[test]
fn a_witness_that_binds_eq_supplies_it_too() {
    let src = r#"namespace test.wi837.wbind
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq}

  sort Pebble
    entity pebble(n: Int64)
  end

  operation pebbleEq(a: Pebble, b: Pebble) -> Bool = true

  sort PebbleEqW
    provides PartialEq[T = Pebble, eq = pebbleEq]
  end

  rule peq(?x, ?y) :- eq(?x, ?y)
end
"#;
    assert_eq!(
        eq_solutions(
            src,
            "test.wi837.wbind.peq",
            "test.wi837.wbind.Pebble.pebble",
            &["n"]
        ),
        1,
        "a witness provision that BINDS `eq` must key the index just as one declaring an \
         `eq` member does — 0 solutions means the binding was silently dropped"
    );
}

// ── The index's DOMAIN (WI-856) ──────────────────────────────────────────────

/// WI-837 shares ONE predicate between the eq index build and WI-664's lawful-Eq
/// boundary classifier; WI-856 shares the composite half of the DOMAIN too, and this
/// pair of tests measures it on both arms of one otherwise-identical program. The
/// index build used to derive its carriers from `SortInfo` facts alone, which only a
/// `sort … end` block emits; a NAMESPACE-LEVEL entity is its own carrier with no
/// `SortInfo`, so its `eq` supplier never keyed the index and equality silently
/// answered STRUCTURALLY — while the classifier, which walks the entity registry,
/// reached that same entity and treated it as a lawful-Eq boundary.
///
/// The gap was PRE-EXISTING and route-independent: the `SortInfo` walk fed the index
/// from the start, so the WI-625 gap-2 instance-fact route used here degraded exactly
/// as the WI-616 own-member and WI-837 witness routes did.
const NS_ENTITY_SRC: &str = r#"namespace test.wi837.nsent
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq}

  entity binding(n: Int64, note: Int64)

  operation bindEq(a: binding, b: binding) -> Bool = true

  fact PartialEq[T = binding, eq = bindEq]

  rule beq(?x, ?y) :- eq(?x, ?y)
end
"#;

/// The same program with the entity wrapped in a `sort`.
const SORT_ENTITY_SRC: &str = r#"namespace test.wi837.sortent
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq}

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
        eq_solutions(
            SORT_ENTITY_SRC,
            "test.wi837.sortent.beq",
            "test.wi837.sortent.Binding.binding",
            &["n", "note"]
        ),
        1,
        "the control arm: a `sort`-wrapped carrier's instance-fact `eq` dispatches"
    );
}

#[test]
fn a_namespace_level_entity_carrier_keys_the_index() {
    assert_eq!(
        eq_solutions(
            NS_ENTITY_SRC,
            "test.wi837.nsent.beq",
            "test.wi837.nsent.binding",
            &["n", "note"]
        ),
        1,
        "a namespace-level entity emits no `SortInfo`, so the index build must reach it through \
         the composite-carrier walk it now shares with WI-664's classifier; 0 solutions means \
         the domain re-narrowed to `SortInfo` and the written `fact PartialEq[T = binding, \
         eq = bindEq]` is being silently ignored again (WI-856)"
    );
}

/// The WITNESS route to the same carrier — and the measurement that REFUTES this
/// ticket's premise that all three supply routes "degrade identically" for a
/// namespace-level entity and are all restored by widening the index's DOMAIN. They
/// are not: the witness route was broken a SECOND time, one owner earlier.
/// `provision_carrier_sort` (kb/typing.rs) read `T = binding` and required
/// `SymbolKind::Sort`, so a free-standing ENTITY carrier answered `None` and the
/// caller filed the provision as a self-provider keyed on the WITNESS — the widened
/// domain then enumerated `binding` and correctly found nothing there. Both owners
/// had to move; measured 0 → 1 on this arm alone.
#[test]
fn a_witness_supplies_eq_for_a_namespace_level_entity_carrier() {
    let src = r#"namespace test.wi856.nswitness
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq}

  entity binding(n: Int64, note: Int64)

  sort BindingEqW
    provides PartialEq[T = binding]
    operation eq(a: binding, b: binding) -> Bool = true
  end

  rule beq(?x, ?y) :- eq(?x, ?y)
end
"#;
    assert_eq!(
        eq_solutions(
            src,
            "test.wi856.nswitness.beq",
            "test.wi856.nswitness.binding",
            &["n", "note"]
        ),
        1,
        "a WITNESS sort supplying `eq` for a namespace-level entity carrier must dispatch; \
         0 solutions means the provision's carrier is being read as the witness sort again \
         and the written `operation eq` is silently ignored"
    );
}

/// CONTROL for the widening above — a sort-NESTED entity is NOT admitted as a carrier
/// in its own right. `T = pebble` names a VARIANT, whose type is the parent sort, so
/// the provision is not a witness for it and the parent keeps structural equality.
/// Without this, the free-standing widening could have admitted every constructor,
/// minting a second carrier bucket that keys the same constructor — where a rival
/// `eq` would hide from the per-carrier ambiguity check instead of colliding with it.
#[test]
fn a_variant_named_as_a_carrier_is_not_a_witness_carrier() {
    let src = r#"namespace test.wi856.variant
  import anthill.prelude.{Int64, Bool, PartialEq}
  import anthill.prelude.PartialEq.{eq}

  sort Pebble
    entity pebble(n: Int64)
  end

  sort PebbleEqW
    provides PartialEq[T = pebble]
    operation eq(a: Pebble, b: Pebble) -> Bool = true
  end

  rule peq(?x, ?y) :- eq(?x, ?y)
end
"#;
    assert_eq!(
        eq_solutions(
            src,
            "test.wi856.variant.peq",
            "test.wi856.variant.Pebble.pebble",
            &["n"]
        ),
        0,
        "a sort-nested variant is not a carrier — `T = pebble` must not key `pebble`'s \
         constructor for dispatch behind the `Pebble` carrier's back"
    );
}

/// The refusal half of the same widening: a namespace-level entity that is newly
/// index-keyed must also be newly REFUSABLE. Asserted on the diagnostic IDENTITY
/// (`AmbiguousEqDispatch`, naming both ops) rather than on failure — the program
/// below loaded CLEAN before WI-856, so a failure-only assertion would have been the
/// whole content of the change and would still pass if the second candidate were
/// dropped by some other check instead.
#[test]
fn two_eq_suppliers_for_a_namespace_level_entity_are_refused() {
    let src = r#"namespace test.wi856.nsambig
  import anthill.prelude.{Int64, Bool, PartialEq}

  entity binding(n: Int64, note: Int64)

  operation bindEqA(a: binding, b: binding) -> Bool = true
  operation bindEqB(a: binding, b: binding) -> Bool = false

  fact PartialEq[T = binding, eq = bindEqA]

  sort BindingEqW
    provides PartialEq[T = binding, eq = bindEqB]
  end
end
"#;
    assert_refused(
        src,
        &[
            "ambiguous semantic equality",
            "carrier 'test.wi856.nsambig.binding'",
            "bindEqA",
            "bindEqB",
        ],
        "a namespace-level entity carrier with two `eq` suppliers must be refused by the index \
         build just as a `sort`-wrapped one is — it loaded clean while the domain excluded it",
    );
}

/// CONTROL for the refusal above — ONE supplier for the same namespace-level carrier
/// still loads clean, so the refusal is the SECOND candidate talking and not the
/// widened domain over-refusing every free-standing entity.
#[test]
fn a_single_eq_supplier_for_a_namespace_level_entity_loads_clean() {
    assert_loads_clean(
        NS_ENTITY_SRC,
        "one `eq` supplier for a namespace-level entity must load clean",
    );
}

// ── The `eq_derive` half of the shared predicate ──────────────────────────────

/// The reason `eq_derive::is_eq_boundary` was rewired to the shared owner, exercised
/// rather than merely asserted in prose. WI-664 derives `NonEq` FIELD-WISE for a
/// composite that reaches an IEEE `Float`, UNLESS the composite is a lawful-Eq
/// BOUNDARY — a carrier whose `eq` is dispatched. A WITNESS-supplied `eq` is such a
/// boundary; before WI-837 the classifier knew only the own-member and instance-fact
/// routes, so a Float-containing composite with a witness `eq` would be derived
/// `NonEq` and its own `provides Eq` would then be refused by the WI-658 `Eq` ⊥
/// `NonEq` check.
///
/// This is the test that fails if a future change re-narrows `is_eq_boundary` to the
/// two old routes — the index-build tests above would all stay green, which is
/// exactly the silent falsification the shared owner exists to prevent.
#[test]
fn a_witness_supplied_eq_is_a_lawful_eq_boundary() {
    let src = r#"namespace test.wi837.boundary
  import anthill.prelude.{Float, Bool, Eq, PartialEq}

  sort W
    entity w(v: Float)
    provides Eq[T = W]
  end

  sort WEq
    provides PartialEq[T = W]
    operation eq(a: W, b: W) -> Bool = true
  end
end
"#;
    assert_loads_clean(
        src,
        "a Float-containing composite whose `eq` comes from a WITNESS is a lawful-Eq \
         boundary: it must NOT be field-wise-derived `NonEq` and must not then conflict \
         with its own `provides Eq`",
    );
}

/// CONTROL for the test above — WITHOUT any `eq` supplier the same composite IS
/// field-wise-derived `NonEq`, so `provides Eq[W]` conflicts. Without this, the
/// boundary test could pass because the derivation never fires at all.
#[test]
fn a_float_composite_with_no_eq_supplier_still_derives_noneq() {
    let src = r#"namespace test.wi837.noboundary
  import anthill.prelude.{Float, Bool, Eq, PartialEq}

  sort W
    entity w(v: Float)
    provides Eq[T = W]
  end
end
"#;
    let errs = crate::common::try_load_kb_with(src)
        .err()
        .unwrap_or_default();
    assert!(
        errs.iter()
            .any(|e| e.contains("provides both") && e.contains("NonEq")),
        "with no `eq` supplier the Float-containing W must be derived `NonEq` and conflict \
         with its own `provides Eq` — otherwise the boundary test above proves nothing; got:\n{}",
        errs.join("\n")
    );
}

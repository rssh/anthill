//! WI-1019 — the native-carrier structural view: the SHAPE is the equality.
//!
//! `Value::OpRef` and the requirement dictionary used to view as
//! `ViewHead::Opaque`, which made an `OpRef` measure as not equal to ITSELF and
//! gave two distinct ones one `goal_fingerprint`. WI-1014 patched the first with
//! a bespoke `Value::native_carrier_eq`; it could not touch the second, because a
//! payload-free head has nothing to key on.
//!
//! `OpRef` now presents a structural head under its own declared sort, so
//! equality and the key read the SAME view and cannot disagree.
//! `Value::FactRef` stays `Opaque` on purpose — see the last section.
//!
//! WI-1045 — the dictionary reached the same place by a shorter road: it is an
//! ORDINARY `Value::Entity` in the `Dictionary(sub₀ … subₙ₋₁, impl: S)` shape,
//! so it reads through the `Entity` view arms and has no arm of its own. The
//! dictionary tests below are unchanged in what they CLAIM; what changed is that
//! there is no second carrier left for the claim to be false of.
//!
//! Reference: docs/design/requirement-dictionaries.md §2.4.1, proposal 005.
//!
//! CONTROLS, MEASURED — each row is a back-out applied to `term_view.rs` and the
//! tests that then FAIL. Nothing here passes both with and without the change.
//!
//! | back-out | fails |
//! |---|---|
//! | `Value::head`'s `OpRef` arm → `Opaque` | `an_opref_is_equal_to_itself_and_keys_by_its_op`, `an_opref_key_is_payload_bearing`, `the_named_spec_op_half_…`, `two_oprefs_differing_only_in_their_dictionary_…` |
//! | `Value::head`'s `Entity` arm → `Opaque` | `a_dictionary_views_as_its_impl_and_sub_dictionaries`, `two_dictionaries_over_different_impls_are_not_equal`, `two_oprefs_differing_only_in_their_dictionary_…` (and most of the suite — after WI-1045 a dictionary IS an entity, so this back-out is no longer narrow) |
//! | drop `dict` from `opref_shape` | `two_oprefs_differing_only_in_their_dictionary_are_distinct` |
//! | drop `named` from `opref_shape` | `the_named_spec_op_half_is_part_of_the_identity` |
//! | delete the `(Opaque, Opaque)` arm | `kb::tests::a_factref_is_an_identity_not_a_shape` (unit) |
//!
//! The last row is the one that shows the two halves are INDEPENDENT: deleting
//! the opaque-equality arm leaves every test above green, because neither an
//! `OpRef` nor a dictionary reaches it.

use smallvec::SmallVec;

use anthill_core::eval::{Interpreter, Value};
use anthill_core::intern::Symbol;
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::term_view::{goal_fingerprint, views_structurally_equal, TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;

fn interp() -> Interpreter {
    crate::common::interp_for("namespace test.wi1019.empty\nend\n")
}

fn resolve(interp: &Interpreter, qn: &str) -> Symbol {
    interp
        .kb()
        .try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol {qn} not found in KB"))
}

/// Equality and the KEY, asked of the same pair. Every test below asserts both,
/// because the defect WI-1019 fixes is precisely that they answered differently:
/// the stopgap made `a == a` true while `key(a) == key(b)` stayed true for
/// distinct `a`/`b`.
fn eq_and_key<A: TermView, B: TermView>(kb: &KnowledgeBase, a: &A, b: &B) -> (bool, bool) {
    let s = Substitution::new();
    (
        views_structurally_equal(kb, a, b),
        goal_fingerprint(kb, a, &s) == goal_fingerprint(kb, b, &s),
    )
}

// ── OpRef: two symbols and a dictionary ──────────────────────────────────────

/// An `OpRef` is equal to itself AND keys distinctly from a different op.
///
/// The KEY asserts are the half WI-1014's stopgap could not reach: it repaired
/// equality with a bespoke compare while the head stayed payload-free, so two
/// `OpRef`s naming DIFFERENT ops went on sharing one `goal_fingerprint`. Asking
/// both questions of the same pair is what makes that visible.
///
/// CONTROL: back-out row 1 (see the module table).
#[test]
fn an_opref_is_equal_to_itself_and_keys_by_its_op() {
    let interp = interp();
    let kb = interp.kb();
    let a = resolve(&interp, "anthill.prelude.Int64");
    let b = resolve(&interp, "anthill.prelude.Bool");
    let mk = |op| Value::OpRef {
        op,
        dict: None,
        named: None,
    };

    let (eq, same_key) = eq_and_key(kb, &mk(a), &mk(a));
    assert!(eq, "an op-as-value is equal to itself");
    assert!(same_key, "and keys the same as itself");

    let (eq, same_key) = eq_and_key(kb, &mk(a), &mk(b));
    assert!(!eq, "two different ops are not equal");
    assert!(!same_key, "AND they no longer share one fingerprint");
}

/// The `named` half is identity, not decoration (WI-857).
///
/// CONTROL: back-out row 4 — dropping `"named"` from `opref_shape` fails THIS
/// test and only this test, so it is what pins the field.
#[test]
fn the_named_spec_op_half_is_part_of_the_identity() {
    let interp = interp();
    let kb = interp.kb();
    let a = resolve(&interp, "anthill.prelude.Int64");
    let b = resolve(&interp, "anthill.prelude.Bool");

    let (eq, same_key) = eq_and_key(
        kb,
        &Value::OpRef {
            op: a,
            dict: None,
            named: None,
        },
        &Value::OpRef {
            op: a,
            dict: None,
            named: Some(b),
        },
    );
    assert!(!eq, "the NAMED spec-op half is part of the identity");
    assert!(!same_key, "and it reaches the key too");
}

/// THE dict TRAP. Two `OpRef`s agreeing on `op` and `named` but carrying
/// DIFFERENT dictionaries dispatch under different requirement environments, so
/// they are different values. A representation dropping `dict` would merge them
/// — and this feeds `value_fact_dedup`, where merging DROPS A FACT (WI-815).
///
/// CONTROL: back-out row 3 — dropping `"dict"` from `opref_shape` fails THIS
/// test and only this test.
#[test]
fn two_oprefs_differing_only_in_their_dictionary_are_distinct() {
    let interp = interp();
    let int64 = resolve(&interp, "anthill.prelude.Int64");
    let bool_sym = resolve(&interp, "anthill.prelude.Bool");
    let op = resolve(&interp, "anthill.prelude.Option");

    let d_int = crate::common::dict(&interp, int64, []);
    let d_bool = crate::common::dict(&interp, bool_sym, []);
    let with = |d| Value::OpRef {
        op,
        dict: Some(std::rc::Rc::new(d)),
        named: None,
    };

    let kb = interp.kb();
    let (eq, same_key) = eq_and_key(kb, &with(d_int.clone()), &with(d_bool));
    assert!(!eq, "different dispatch environments are different values");
    assert!(!same_key, "and the key sees the difference");

    // And an OpRef WITH a dict is still equal to itself — the arity-3 shape is
    // not merely "distinct from everything", which `assert!(!…)` alone allows.
    let (eq, same_key) = eq_and_key(kb, &with(d_int.clone()), &with(d_int.clone()));
    assert!(
        eq && same_key,
        "an OpRef carrying a dict is equal to itself"
    );

    // A present `dict` and an absent one differ by ARITY, the conditional-key
    // shape (`Expr::Proof` precedent) — no `Option` wrapper is synthesized.
    let (eq, same_key) = eq_and_key(
        kb,
        &with(d_int),
        &Value::OpRef {
            op,
            dict: None,
            named: None,
        },
    );
    assert!(!eq && !same_key, "a captured dict is not the same as none");
}

// ── Dictionary: the accessor set IS the shape ────────────────────────────────

/// A dictionary views as `(impl, [subs])` — exactly what `impl` / `arity` / `sub`
/// read — and compares by CONTENT.
///
/// CONTROL: back-out row 2 (see the module table).
///
/// WI-1045 — this reads a `Value::Entity` now. That is the delivery, not a
/// weakening: the head it asserts is the one the σ-side producer already built,
/// so this test now pins that BOTH sides announce it.
#[test]
fn a_dictionary_views_as_its_impl_and_sub_dictionaries() {
    let interp = interp();
    let int64 = resolve(&interp, "anthill.prelude.Int64");
    let bool_sym = resolve(&interp, "anthill.prelude.Bool");

    let mk = |i: &Interpreter, functor, sub: Option<Symbol>| {
        let mut subs: SmallVec<[_; 1]> = SmallVec::new();
        if let Some(s) = sub {
            subs.push(crate::common::dict(i, s, []));
        }
        crate::common::dict(&i, functor, subs).into_value()
    };

    let parent = mk(&interp, int64, Some(bool_sym));
    let twin = mk(&interp, int64, Some(bool_sym));
    let childless = mk(&interp, int64, None);
    let other_sub = mk(&interp, int64, Some(int64));

    // The head is the declared sort, arity = sub count, one named key (`impl`).
    let dict_sym = resolve(&interp, "anthill.realization.runtime.Dictionary");
    let kb = interp.kb();
    match parent.head(kb) {
        ViewHead::Functor {
            functor,
            pos_arity,
            named_arity,
        } => {
            assert_eq!(functor, Some(dict_sym), "views under its own declared sort");
            assert_eq!(pos_arity, 1, "one sub-dictionary, positionally");
            assert_eq!(named_arity, 1, "and `impl`");
        }
        other => panic!("expected a Functor head, got {other:?}"),
    }

    // CONTENT equality: two SEPARATELY ALLOCATED slots holding the same tree are
    // the same dictionary. This is the claim slot-identity comparison got wrong.
    let (eq, same_key) = eq_and_key(kb, &parent, &twin);
    assert!(eq, "two dictionaries with the same (impl, subs) are equal");
    assert!(same_key, "and share a key");

    let (eq, same_key) = eq_and_key(kb, &parent, &childless);
    assert!(!eq && !same_key, "a sub-dictionary is part of the identity");

    let (eq, same_key) = eq_and_key(kb, &parent, &other_sub);
    assert!(!eq && !same_key, "and so is WHICH sub-dictionary it is");
}

/// The cross-interpreter FALSE POSITIVE the stopgap had, closed — and since
/// WI-1045, INEXPRESSIBLE.
///
/// `native_carrier_eq` compared dictionaries with `ha.raw() == hb.raw()` while the
/// handle's own doc said "Identity is `(arena, raw)`". It dropped the arena half,
/// so the FIRST slot of two different interpreters' arenas — both raw 0, different
/// impls — compared EQUAL. That is the direction that merges facts, and a fresh
/// interpreter per call is the normal pattern, so it was reachable.
///
/// WI-1019 answered it with content comparison, which has no arena half to drop.
/// WI-1045 removed the arena, so there is no longer a slot index for anything to
/// compare by: the subject is now simply two dictionaries built in two
/// interpreters, which is the shape that used to collide.
#[test]
fn two_dictionaries_over_different_impls_are_not_equal() {
    let a = interp();
    let b = interp();
    let int64 = resolve(&a, "anthill.prelude.Int64");
    let bool_sym = resolve(&b, "anthill.prelude.Bool");

    // Built in two SEPARATE interpreters — the pattern that shared a `raw`.
    let da = crate::common::dict(&a, int64, []).into_value();
    let db = crate::common::dict(&b, bool_sym, []).into_value();

    let (eq, same_key) = eq_and_key(a.kb(), &da, &db);
    assert!(!eq, "different impls are not the same dictionary");
    assert!(!same_key, "and do not share a key");

    // The other direction, which a raw-only compare also got wrong: two
    // dictionaries built in DIFFERENT interpreters over the SAME impl ARE equal.
    // With one representation there is no identity left for them to differ in.
    let db_int = crate::common::dict(&b, int64, []).into_value();
    let (eq, same_key) = eq_and_key(a.kb(), &da, &db_int);
    assert!(
        eq && same_key,
        "one dictionary built on two sides is one value — the whole point of \
         retiring the arena (requirement-channel.md §9)"
    );
}

// ── The blast radius, asserted ───────────────────────────────────────────────

/// An `OpRef` key is now payload-BEARING, which is what changes downstream:
/// `is_opaque_free` gates fact dedup, so facts holding an `OpRef` start being
/// deduped where they previously could not be, and `is_cacheable` stops
/// excluding such goals from the query cache. That is the POINT of the ticket,
/// so it is asserted rather than left to be discovered.
///
/// The opposite half — an opaque carrier's key REFUSING to be dedup-eligible, so
/// it degrades to no-dedup instead of merging two rows — is pinned on `FactRef`
/// by `a_factref_is_an_identity_not_a_shape` (`kb/mod.rs` unit tests), where its
/// crate-private constructor lives.
///
/// CONTROL: back-out row 1 — the key becomes the single `Opaque` token.
#[test]
fn an_opref_key_is_payload_bearing() {
    let interp = interp();
    let op = resolve(&interp, "anthill.prelude.Int64");
    let key = goal_fingerprint(
        interp.kb(),
        &Value::OpRef {
            op,
            dict: None,
            named: None,
        },
        &Substitution::new(),
    );
    assert!(
        key.is_opaque_free(),
        "an OpRef head now carries its own payload"
    );
}

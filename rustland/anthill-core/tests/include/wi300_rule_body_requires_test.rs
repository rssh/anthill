//! WI-300 — rule-body `requires(X)` requirement guards (guard tier).
//!
//! A rule-body `requires(PartialEq[T])` desugars (converter) to
//! `find_dictionary(PartialEq[T])`, the spec instance whole, which the typer sweep
//! rewrites into `find_dictionary(<spec>, <op>, ?x, ?y)` using the body's `eq(?x, ?y)`
//! call as the witness whose carrier types decide the instance. At resolution the guard
//! checks `provides PartialEq` — the spec it names, not `Eq` — at the current binding,
//! by a provision written or DERIVED (`Derived`, `Partial` below):
//!   * ground carrier WITH a provider     → the rule fires;
//!   * ground carrier with NO provider     → the rule does not fire (even though the
//!     structural `eq` would succeed — the guard is what blocks it);
//!   * under-determined carrier            → SUSPEND (no definite solution).
//! Body `eq` is `BuiltinTag::Eq` (structural), so the fire/don't-fire/suspend outcome
//! is governed ENTIRELY by the `requires` guard.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

use crate::common::load_kb_with as load_with;

/// Like [`load_with`] but returns the load errors instead of panicking.
use crate::common::try_load_kb_with as try_load_with;

const SRC: &str = r#"
    namespace test.wi300
      import anthill.prelude.{Int64, Float, PartialEq, Eq}
      -- WI-1089: `eq` is imported by name. `import anthill.prelude.Int64` binds
      -- `Int64` and nothing else, so the bare body call needs its own import.
      import anthill.prelude.PartialEq.eq
      import anthill.prelude.PartialEq.{eq}
      -- A carrier that DECLARES it provides Eq …
      sort Witheq
        entity we(v: Int64)
      end
      -- … and one that does not. Its field is typed by `Opaque`, a sort that provides
      -- nothing, so `Noeq` derives no equality either: typed `Int64` it would, and
      -- the guard would admit it (`Derived` below; WI-20260831-QF5JT).
      sort Opaque
      end
      sort Noeq
        entity ne(v: Opaque)
      end
      -- Three carriers that WRITE no provision, differing from `Noeq` in their fields
      -- only. A composite whose `eq` nothing supplies DERIVES its equality from its
      -- fields: `Eq` if every field is, `NonEq` if one reaches a `Float`, `PartialEq`
      -- with either (kernel-language §8.3, "Closed by the load that defines the
      -- carrier"; `eq_derive::derive_total_eq`, and `derive_conditional_eq`, which
      -- derives the same rows for a sort the first pass leaves). `Int64` provides
      -- `Eq` — the host bindings say so, and they always load — so `Derived` provides
      -- it as well; a second field typed `Opaque` withholds it from `Mixed`; `Partial`
      -- gets `PartialEq` and `NonEq` but no `Eq`.
      sort Derived
        entity de(v: Int64)
      end
      sort Mixed
        entity mx(v: Int64, o: Opaque)
      end
      sort Partial
        entity pt(f: Float)
      end
      namespace Witheq
        provides PartialEq[T = Witheq]
        provides Eq[T = Witheq]
      end

      -- Fires only when the argument type provides PartialEq; the inner `eq` is the
      -- structural builtin, so the guard alone decides fire / don't-fire.
      rule related(?x, ?y) :- requires(PartialEq[T]), eq(?x, ?y)
    end
"#;

/// `ctor(v: n)` — an entity term of one field `v` (`we`, `ne`, `de`).
fn mk(kb: &mut KnowledgeBase, ctor: &str, n: i64) -> TermId {
    mk_fields(kb, ctor, &["v"], Literal::Int(n))
}

/// `ctor(f₁: value, …)` — every named field holding `value`. The resolver does not
/// type a query term, so an `Opaque` field takes an integer as `ne`'s does. `fields`
/// must be in DECLARED order: that is the order the loader canonicalizes named
/// arguments into, and a term in another order is a different term, which the
/// blocking rows would count as a block.
fn mk_fields(kb: &mut KnowledgeBase, ctor: &str, fields: &[&str], value: Literal) -> TermId {
    let functor = kb
        .try_resolve_symbol(ctor)
        .unwrap_or_else(|| panic!("ctor {ctor} not in KB"));
    let v = kb.alloc(Term::Const(value));
    let named: Vec<_> = fields.iter().map(|f| (kb.intern(f), v)).collect();
    kb.alloc(Term::Fn {
        functor,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&named),
    })
}

/// An unbound global query variable as a term.
fn fresh(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

fn related_solutions(
    kb: &mut KnowledgeBase,
    a: TermId,
    b: TermId,
) -> Vec<anthill_core::kb::resolve::Solution> {
    let related = kb
        .try_resolve_symbol("test.wi300.related")
        .expect("test.wi300.related not in KB");
    let goal = kb.alloc(Term::Fn {
        functor: related,
        pos_args: SmallVec::from_slice(&[a, b]),
        named_args: SmallVec::new(),
    });
    kb.resolve(&[goal], &ResolveConfig::default())
}

fn definite_count(kb: &mut KnowledgeBase, a: TermId, b: TermId) -> usize {
    related_solutions(kb, a, b)
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

#[test]
fn guard_fires_when_carrier_provides_eq() {
    let mut kb = load_with(SRC);
    let a = mk(&mut kb, "test.wi300.Witheq.we", 7);
    let b = mk(&mut kb, "test.wi300.Witheq.we", 7);
    assert_eq!(
        definite_count(&mut kb, a, b),
        1,
        "Witheq provides Eq and we(7) == we(7): the rule must fire"
    );
}

#[test]
fn guard_fires_but_eq_fails_for_unequal_values() {
    let mut kb = load_with(SRC);
    let a = mk(&mut kb, "test.wi300.Witheq.we", 7);
    let b = mk(&mut kb, "test.wi300.Witheq.we", 8);
    assert_eq!(
        definite_count(&mut kb, a, b),
        0,
        "guard fires (Witheq provides Eq) but we(7) != we(8): no solution"
    );
}

#[test]
fn guard_blocks_when_carrier_has_no_provider() {
    // The distinguishing case: `eq(ne(7), ne(7))` is structurally TRUE, but Noeq
    // declares no `provides PartialEq[T = Noeq]` and derives none, so the guard does
    // not fire — the rule yields nothing. Without the guard (plain `eq`) this would be
    // a solution.
    let mut kb = load_with(SRC);
    // No answer at all, not merely no definite one: a SUSPENDED guard leaves a residual
    // answer (measured, one, over two unbound arguments), so `definite_count` alone
    // would not tell a block from a suspension.
    let a = mk(&mut kb, "test.wi300.Noeq.ne", 7);
    let b = mk(&mut kb, "test.wi300.Noeq.ne", 7);
    let sols = related_solutions(&mut kb, a, b);
    assert!(
        sols.is_empty(),
        "Noeq provides no PartialEq: the guard must block the rule despite eq \
         succeeding, and leave no residual answer — got {} answer(s)",
        sols.len()
    );
}

/// Does a sort of [`SRC`] provide the prelude spec `spec`, by a row written or derived?
fn provides(kb: &KnowledgeBase, sort: &str, spec: &str) -> bool {
    let carrier = kb
        .try_resolve_symbol(&format!("test.wi300.{sort}"))
        .unwrap_or_else(|| panic!("sort {sort} not in KB"));
    let spec = kb
        .try_resolve_symbol(&format!("anthill.prelude.{spec}"))
        .unwrap_or_else(|| panic!("{spec} not in KB"));
    kb.sort_provides(carrier, spec)
}

/// WI-20260831-QF5JT — A CARRIER THAT WRITES NO PROVISION STILL PASSES THE GUARD WHEN
/// ITS FIELDS GIVE IT EQUALITY. `Derived(v: Int64)` derives `PartialEq` and `Eq` from
/// its field (`eq_derive`, both passes; the fixture's comment), and the guard reads the
/// provision relation, derived rows included. This is the behaviour that was filed as
/// the guard "not discriminating by carrier" once the host bindings loaded: the
/// fixture's carrier was `Noeq(v: Int64)`, and `Int64` provides `Eq` only in the
/// bindings.
///
/// FAILS when the derivation is backed out for this file's sorts, MEASURED: skip
/// `test.wi300` sorts in BOTH `derive_total_eq` and `derive_conditional_eq`'s
/// candidates (the conditional pass derives the same rows, with no conditions, for a
/// sort the total pass leaves) and `Derived` provides nothing — the row fails there,
/// and a probe of the same shape found the guard answering 0. With the total pass
/// alone skipped it still provides, and the row passes.
#[test]
fn a_carrier_whose_fields_provide_eq_derives_it_and_passes_the_guard() {
    let mut kb = load_with(SRC);
    assert_eq!(
        ["PartialEq", "Eq", "NonEq"].map(|spec| provides(&kb, "Derived", spec)),
        [true, true, false],
        "`Derived(v: Int64)` writes no provision and must derive the TOTAL equality"
    );
    let a = mk(&mut kb, "test.wi300.Derived.de", 7);
    let b = mk(&mut kb, "test.wi300.Derived.de", 7);
    assert_eq!(
        definite_count(&mut kb, a, b),
        1,
        "a derived PartialEq must satisfy the guard as a written one does"
    );
}

/// The guard asks for the spec it NAMES. `Partial(f: Float)` derives `PartialEq` and
/// `NonEq` and no `Eq`, and `requires(PartialEq[T])` admits it — so the guard reads
/// `PartialEq`, as the header says, not the `Eq` it once said.
///
/// FAILS when the guard asks `Eq` where the goal names `PartialEq`, MEASURED (that
/// substitution at `builtin_find_dictionary`'s spec read), and is the only row that
/// does: every other carrier here that passes provides `Eq` as well. Passes under both
/// derivation back-outs above, which leave the Partial half alone. That half cannot be
/// backed out under this row: a derived `NonEq` without its `PartialEq` is refused at
/// load ("provides NonEq, which requires PartialEq"), MEASURED.
#[test]
fn a_partial_composite_passes_a_partial_eq_guard() {
    let mut kb = load_with(SRC);
    assert_eq!(
        ["PartialEq", "Eq", "NonEq"].map(|spec| provides(&kb, "Partial", spec)),
        [true, false, true],
        "`Partial(f: Float)` must derive the PARTIAL equality"
    );
    let a = mk_fields(&mut kb, "test.wi300.Partial.pt", &["f"], Literal::Float(1.5.into()));
    let b = mk_fields(&mut kb, "test.wi300.Partial.pt", &["f"], Literal::Float(1.5.into()));
    assert_eq!(
        definite_count(&mut kb, a, b),
        1,
        "a carrier with a partial equality provides PartialEq and must pass its guard"
    );
}

/// The CONTROL beside them: a carrier holding the same `Int64` field and one `Opaque`
/// field derives nothing — `Eq` needs EVERY field — and the guard BLOCKS it: no answer
/// at all, so not a suspension either (which would leave a residual one). This row is
/// what tells an `Int64` field from the reason `Derived` is admitted; `Noeq`, whose only
/// field is `Opaque`, cannot.
///
/// FAILS under an any-field derivation, MEASURED: let a `test.wi300` composite stay
/// derivable while ONE of its fields has equality, in both passes, and `Mixed` provides
/// `PartialEq` and `Eq` while `Noeq` still provides nothing. Passes under the plain
/// derivation back-out, by design. It is also the row a guard that grounded its witness
/// to a FIELD's carrier would fail (QF5JT's first hypothesis); no such mutation was
/// built.
#[test]
fn one_field_without_eq_withholds_the_derivation_and_the_guard_blocks() {
    let mut kb = load_with(SRC);
    assert_eq!(
        ["PartialEq", "Eq"].map(|spec| provides(&kb, "Mixed", spec)),
        [false, false],
        "`Mixed(v: Int64, o: Opaque)` has a field with no equality and derives none"
    );
    let a = mk_fields(&mut kb, "test.wi300.Mixed.mx", &["v", "o"], Literal::Int(7));
    let b = mk_fields(&mut kb, "test.wi300.Mixed.mx", &["v", "o"], Literal::Int(7));
    let sols = related_solutions(&mut kb, a, b);
    assert!(
        sols.is_empty(),
        "Mixed provides no PartialEq: the guard must block the rule despite eq \
         succeeding, and leave no residual answer — got {} answer(s)",
        sols.len()
    );
}

#[test]
fn guard_suspends_on_under_determined_carrier() {
    // Both arguments unbound → the carrier type is under-determined → the guard
    // SUSPENDS (never NAF-decides). No DEFINITE solution is produced.
    let mut kb = load_with(SRC);
    let a = fresh(&mut kb, "a");
    let b = fresh(&mut kb, "b");
    assert_eq!(
        definite_count(&mut kb, a, b),
        0,
        "under-determined carrier must suspend, yielding no definite solution"
    );
}

#[test]
fn ungroundable_requires_is_a_loud_error() {
    // `requires(PartialEq[T])` with NO body call to any of Eq's operations cannot be
    // grounded — the guard would never be decidable. That is reported as a hard
    // error (loud, not a silent skip), not left to fail quietly at resolution.
    let src = r#"
        namespace test.wi300.bad
          import anthill.prelude.{Int64, PartialEq, Eq}
          import anthill.prelude.PartialEq.eq
          sort Thing
            entity thing(v: Int64)
          end
          rule solo(?x) :- requires(PartialEq[T])
        end
    "#;
    let errs = try_load_with(src)
        .err()
        .expect("ungroundable requires must fail to load");
    assert!(
        errs.iter().any(|e| e.contains("ground the requirement")),
        "expected a grounding error, got: {errs:?}"
    );
}

#[test]
fn two_equal_requires_on_same_spec_is_a_loud_error() {
    // TWO `requires` ON ONE SPEC ARE NO LONGER AN ERROR BY THEMSELVES —
    // WI-20260909-96ZTM binds one dictionary per `require`, attributed by its own written
    // bracket (`wi_96ztm…::the_two_dictionaries_are_attributed_to_their_own_carriers`).
    // The old reason — "the guard tier strips the spec's type-args, so it cannot
    // attribute which type-parameter each `requires` names" — went with
    // WI-20260909-51W18's un-strip.
    //
    // WHAT IS STILL REFUSED IS TWO **EQUAL** ONES, and this fixture is one: `A` and `B`
    // here are FREE names, not head-introduced type variables, so neither denotes
    // anything, both requires lower to a bare `PartialEq`, and nothing distinguishes
    // them.
    //
    // AND THE FIXTURE SAYS SO OUT LOUD NOW. The two leading errors are
    // WI-20260909-51W18's: a bracket binding naming neither a sort nor one of the spec's
    // own type parameters is REPORTED rather than silently dropped — which is what makes
    // visible that this clause's `[A]`/`[B]` never distinguished anything.
    let src = r#"
        namespace test.wi300.dup
          import anthill.prelude.{Int64, PartialEq, Eq}
          import anthill.prelude.PartialEq.eq
          import anthill.prelude.PartialEq.{eq}
          sort Thing
            entity thing(v: Int64)
          end
          namespace Thing
            provides PartialEq[T = Thing]
            provides Eq[T = Thing]
          end
          rule twin(?a, ?b, ?c) :- requires(PartialEq[A]), requires(PartialEq[B]), eq(?a, ?b), eq(?b, ?c)
        end
    "#;
    let errs = try_load_with(src)
        .err()
        .expect("two requires on the same spec must fail to load");
    assert!(
        errs.iter().any(|e| e.contains("name a different instance")),
        "expected an equal-requires refusal, got: {errs:?}"
    );
    assert!(
        errs.iter()
            .any(|e| e.contains("`A` in it names neither a sort"))
            && errs
                .iter()
                .any(|e| e.contains("`B` in it names neither a sort")),
        "expected both free names to be reported in their own right, got: {errs:?}"
    );
}

//! WI-300 — a rule's requirement as a guard of the clause.
//!
//! WI-300 delivered the rule-body `requires(PartialEq[T])`, a check-only guard whose
//! carrier the body's `eq(?x, ?y)` call witnessed; proposal 060.1 §5 removed it, and the
//! guard is the head introducer's, `rule related[A](?x: A, ?y: A) :- PartialEq[T = A]`,
//! read as `find_dictionary(PartialEq[T = A], PartialEq, A, out: ?d, carrier_type: true)` at
//! the carrier the introducer names. At resolution the guard checks `provides PartialEq` —
//! the spec it names, not `Eq` — by a provision written or DERIVED (`Derived`, `Partial`
//! below). A query is typed where it is read (proposal 073 §6.2), so the guard is passed the
//! dictionary the query's own types build, and nothing is read from a value when it runs:
//!   * a carrier WITH a provider     → the rule fires;
//!   * a carrier with NO provider     → the query is refused where it is read (even though
//!     the structural `eq` would succeed — the guard is what refuses it);
//!   * a carrier the query leaves open → refused too, naming `A`.
//! Body `eq` is `BuiltinTag::Eq` (structural), so the outcome is governed ENTIRELY by the
//! guard. (Before 073 §6.2 the guard read the carrier from the goal's values, a goal built
//! by hand: no provider failed the goal, and an open carrier suspended it.)

use anthill_core::kb::resolve::{ResolveConfig, Solution};
use anthill_core::kb::KnowledgeBase;

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
      rule related[A](?x: A, ?y: A) :- PartialEq[T = A], eq(?x, ?y)
      -- A guard no call reads decides as well.
      rule solo[A](?x: A) :- PartialEq[T = A]
    end
"#;

/// The query `pattern`, typed where it is read: `Err` with its refusals, or its solutions.
fn ask(kb: &mut KnowledgeBase, pattern: &str) -> Result<Vec<Solution>, Vec<String>> {
    let refusals = crate::common::query_pattern_refusals(kb, pattern);
    if !refusals.is_empty() {
        return Err(refusals);
    }
    let goal = crate::common::query_pattern_term(kb, pattern);
    Ok(kb.resolve(&[goal], &ResolveConfig::default()))
}

/// The definite solutions of `pattern`, which must not be refused.
fn definite_count(kb: &mut KnowledgeBase, pattern: &str) -> usize {
    ask(kb, pattern)
        .unwrap_or_else(|e| panic!("`{pattern}` is refused: {e:?}"))
        .iter()
        .filter(|s| s.is_definite())
        .count()
}

/// `pattern` is refused where it is read, naming `PartialEq` and `tokens`.
fn refused(kb: &mut KnowledgeBase, pattern: &str, tokens: &[&str]) {
    let errs = ask(kb, pattern).err().unwrap_or_else(|| panic!("`{pattern}` must be refused"));
    let mut want = vec!["PartialEq"];
    want.extend_from_slice(tokens);
    crate::common::assert_refused_naming(&errs, &want, pattern);
}

/// `related(<a>, <b>)` over [`SRC`]'s constructors, written as `Witheq.we(v: 7)`.
fn related(a: &str, b: &str) -> String {
    format!("test.wi300.related(test.wi300.{a}, test.wi300.{b})")
}

#[test]
fn guard_fires_when_carrier_provides_eq() {
    let mut kb = load_with(SRC);
    assert_eq!(
        definite_count(&mut kb, &related("Witheq.we(v: 7)", "Witheq.we(v: 7)")),
        1,
        "Witheq provides Eq and we(7) == we(7): the rule must fire"
    );
}

#[test]
fn guard_fires_but_eq_fails_for_unequal_values() {
    let mut kb = load_with(SRC);
    assert_eq!(
        definite_count(&mut kb, &related("Witheq.we(v: 7)", "Witheq.we(v: 8)")),
        0,
        "guard fires (Witheq provides Eq) but we(7) != we(8): no solution"
    );
}

#[test]
fn guard_refuses_a_carrier_with_no_provider() {
    // The distinguishing case: `eq(ne(7), ne(7))` is structurally TRUE, but Noeq
    // declares no `provides PartialEq[T = Noeq]` and derives none, so the query is refused
    // where it is read, as a rule body's goal at `Noeq` is at load. Without the guard
    // (plain `eq`) this would be a solution.
    let mut kb = load_with(SRC);
    refused(&mut kb, &related("Noeq.ne(v: 7)", "Noeq.ne(v: 7)"), &["Noeq"]);
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
    assert_eq!(
        definite_count(&mut kb, &related("Derived.de(v: 7)", "Derived.de(v: 7)")),
        1,
        "a derived PartialEq must satisfy the guard as a written one does"
    );
}

/// The guard asks for the spec it NAMES. `Partial(f: Float)` derives `PartialEq` and
/// `NonEq` and no `Eq`, and the guard `PartialEq[T = A]` admits it — so the guard reads
/// `PartialEq`, as the header says, not the `Eq` it once said.
///
/// FAILED when the guard asked `Eq` where the goal named `PartialEq`, MEASURED (that
/// substitution at `builtin_find_dictionary`'s spec read) while the guard was
/// `requires(PartialEq[T])`, and was the only row that did: every other carrier here that
/// passes provides `Eq` as well. The introducer's guard reads the instance whole
/// (`carrier_type: true`), and that substitution was not measured on it. Passes under both
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
    assert_eq!(
        definite_count(&mut kb, &related("Partial.pt(f: 1.5)", "Partial.pt(f: 1.5)")),
        1,
        "a carrier with a partial equality provides PartialEq and must pass its guard"
    );
}

/// The CONTROL beside them: a carrier holding the same `Int64` field and one `Opaque`
/// field derives nothing — `Eq` needs EVERY field — and the query at it is refused, as at
/// `Noeq`. This row is
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
    refused(&mut kb, &related("Mixed.mx(v: 7, o: 7)", "Mixed.mx(v: 7, o: 7)"), &["Mixed"]);
}

#[test]
fn a_query_leaving_the_carrier_open_is_refused() {
    // Both arguments unbound: the query fixes no carrier, and no caller can pass the
    // guard a dictionary, so the query is refused where it is read, naming `A` (073 §6.2).
    // It suspended while the guard read the carrier from the values when it ran.
    let mut kb = load_with(SRC);
    refused(&mut kb, "test.wi300.related(?a, ?b)", &["`related`'s `A`"]);
}

/// A GUARD NO CALL READS STILL DECIDES. WI-300's `requires(PartialEq[T])` with no body
/// call was refused, "cannot … ground the requirement": its carrier came from the call. The
/// introducer names the carrier, so `solo[A](?x: A) :- PartialEq[T = A]` loads and holds at
/// `Witheq` alone, as an operation's unread `requires` line does.
#[test]
fn a_guard_no_call_reads_still_decides() {
    let mut kb = load_with(SRC);
    let answers = ask(&mut kb, "test.wi300.solo(test.wi300.Witheq.we(v: 7))").expect("typed at `Witheq`");
    assert!(answers.len() == 1 && answers[0].is_definite(), "{} answer(s)", answers.len());
    refused(&mut kb, "test.wi300.solo(test.wi300.Noeq.ne(v: 7))", &["Noeq"]);
}

/// TWO EQUAL GUARDS ARE TWO REQUIREMENTS, as an operation's two equal `requires` lines are
/// two slots (proposal 060.1 §8.5), and the call both cover reads the first: `twin` holds at
/// `Witheq` and not at `Noeq`. WI-300 refused two equal `requires(…)`, "name a different
/// instance"; that row's spelling, `requires(PartialEq[A]), requires(PartialEq[B])` over
/// free names, is the guards over names nothing introduces now, each refused as the
/// unresolved name it is.
#[test]
fn two_equal_guards_are_two_requirements() {
    let src = r#"
        namespace test.wi300.dup
          import anthill.prelude.{Int64, PartialEq, Eq}
          import anthill.prelude.PartialEq.{eq}
          sort Thing
            entity thing(v: Int64)
          end
          sort Opaque
          end
          sort Noeq
            entity ne(v: Opaque)
          end
          namespace Thing
            provides PartialEq[T = Thing]
            provides Eq[T = Thing]
          end
          rule twin[A](?a: A, ?b: A, ?c: A) :- PartialEq[T = A], PartialEq[T = A], eq(?a, ?b), eq(?b, ?c)
        end
    "#;
    let mut kb = load_with(src);
    let thing = "test.wi300.dup.Thing.thing(v: 7)";
    let answers = ask(&mut kb, &format!("test.wi300.dup.twin({thing}, {thing}, {thing})")).expect("typed at `Thing`");
    assert!(answers.len() == 1 && answers[0].is_definite(), "{} answer(s)", answers.len());
    let ne = "test.wi300.dup.Noeq.ne(v: 7)";
    refused(&mut kb, &format!("test.wi300.dup.twin({ne}, {ne}, {ne})"), &["Noeq"]);
    let free = r#"
        namespace test.wi300.free
          import anthill.prelude.{Int64, PartialEq}
          import anthill.prelude.PartialEq.{eq}
          rule twin(?a, ?b, ?c) :- PartialEq[A], PartialEq[B], eq(?a, ?b), eq(?b, ?c)
        end
    "#;
    let errs = try_load_with(free).err().expect("guards over free names must fail to load");
    assert!(
        errs.iter().any(|e| e.contains("unresolved name 'A'"))
            && errs.iter().any(|e| e.contains("unresolved name 'B'")),
        "expected both free names reported, got: {errs:?}"
    );
}

//! WI-898 — an equation-introduced functor has its OWN kind, so it never enters
//! WI-714's relation machinery. The rule lives in `docs/kernel-language.md`
//! §"What an introduced name denotes"; the mechanism is
//! `load::scan_rule_goal` + `intern::SymbolKind::EquationFunctor`.
//!
//! WHAT REGRESSED AND WHAT THIS PINS. WI-894 gave a rule-introduced functor a scoped
//! symbol, borrowing `SymbolKind::Goal` — the kind WI-714 reserves for a RELATION
//! REFERENCE. An equation's clauses are indexed under the `eq`/`unify` CONNECTIVE, so
//! the relation reader found zero clauses and reported `unresolved name` about a name
//! that resolved. The shape it fired on is the one WI-894's own docs recommend
//! (`import anthill.prelude.Bool.{ite}`), so the recommended spelling had the WORSE
//! diagnostic of the two.
//!
//! These tests deliberately assert MESSAGE CONTENT, which
//! `wi894_rule_functor_scope_test::an_imported_functor_with_no_redex_is_also_refused`
//! deliberately does NOT (it pins refusal + the named functor, and says so). The two
//! are a matched pair: that file owns "this shape is refused", this one owns "and here
//! is what the refusal says".
//!
//! THE CONTROL, per the repo principle. Backed out to pre-WI-898 (one `Goal` kind for
//! both head shapes), these FAIL: `an_equation_head_and_a_predicate_head_get_different_kinds`
//! (`eqn898` reads `Goal`), all three rows of `a_no_redex_call_is_refused_without_claiming_
//! the_name_is_unresolved` (the message is the "unresolved" one), `an_untagged_defining_
//! equation_is_diagnosed_as_inert_not_unmatched` (no such diagnostic exists), and
//! `a_bare_unimported_equation_functor_gets_the_owning_sort_hint` (the remedy scan is
//! Operation-only, so the terse "unknown functor" is emitted).
//!
//! The other two pin defects found DURING the work, and each passes against pre-WI-898
//! while failing against the cut that introduced it:
//! `a_name_in_both_head_shapes_is_a_relation_in_either_source_order` fails in ONE of its
//! two orders against a STAMPED kind, and
//! `the_receiver_remedy_is_withheld_when_any_owner_is_an_equation_functor` fails against
//! an `any`-shaped `dot_dispatchable`. Neither is evidence about the main fix — that is
//! what the five rows above are for.
//!
//! STDLIB LOADS: NINE — one per `#[test]`, plus the extra cells of the three tests that
//! drive a claim across several programs (two source orders, three citation spellings,
//! two owner shapes), each of which is worthless without its siblings. See
//! `wi884_sibling_backing_test`'s header.

use anthill_core::intern::SymbolKind;

/// THE KIND SPLIT AT THE SYMBOL LEVEL, on one load, so a regression names itself as a
/// classification rather than only as a message surprise. The two head shapes sit side
/// by side in one sort and must land on two kinds — including `bool.anthill`'s own
/// `ite`, the ticket's worked example, which is why the stdlib symbol is asserted too.
#[test]
fn an_equation_head_and_a_predicate_head_get_different_kinds() {
    const SRC: &str = r#"
namespace wi898.kinds
  sort S
    import anthill.prelude.{Int64, Bool}
    rule { eqn898(?x) = ?x [simp] }
    rule pred898(?x) :- Int64.gt(?x, 0)
  end
end
"#;
    let kb = crate::common::load_kb_with(SRC);
    for (qn, want, why) in [
        (
            "wi898.kinds.S.eqn898",
            SymbolKind::EquationFunctor,
            "an equation's LHS names a function defined by rewriting — it owns no \
             clauses, so it is not a relation",
        ),
        (
            "wi898.kinds.S.pred898",
            SymbolKind::Goal,
            "a predicate head owns its clauses, so it stays the WI-714 relation kind",
        ),
        (
            "anthill.prelude.Bool.ite",
            SymbolKind::EquationFunctor,
            "the ticket's worked example: `ite` is two `[simp]` equations, not a relation",
        ),
    ] {
        let sym = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("`{qn}` must be a defined symbol"));
        assert_eq!(kb.kind_of(sym), Some(want), "`{qn}`: {why}");
    }
}

/// A NAME WRITTEN IN BOTH SHAPES IS A RELATION, WHICHEVER RULE COMES FIRST. Pass 3
/// visits rules in source order and the MINT records the first shape it sees, so a
/// stamped classification is source-order dependent — MEASURED, against a first cut
/// that stamped it: the same two rules swapped answered `EquationFunctor` and `Goal`.
///
/// So the claim is deliberately made about [`KnowledgeBase::cites_a_relation`] and NOT
/// about `kind_of`: the kind still records which head shape minted the name (order and
/// all), while whether the name DENOTES a relation is derived from the clause index,
/// where a predicate clause is present in either order. Asserting the kind here would
/// pin the stamp back into place and forbid the fix.
///
/// The two orders are asserted TOGETHER because either alone passes against the defect;
/// that is the same trap `wi894_rule_functor_scope_test::each_sort_uses_its_own_rules`
/// records for its inverted pair.
#[test]
fn a_name_in_both_head_shapes_is_a_relation_in_either_source_order() {
    const EQUATION_FIRST: &str = r#"
namespace wi898.mixeda
  sort S
    import anthill.prelude.{Int64, Bool}
    rule { both898(?x) = ?x [simp] }
    rule both898(?x) :- Int64.gt(?x, 0)
  end
end
"#;
    const PREDICATE_FIRST: &str = r#"
namespace wi898.mixedb
  sort S
    import anthill.prelude.{Int64, Bool}
    rule both898(?x) :- Int64.gt(?x, 0)
    rule { both898(?x) = ?x [simp] }
  end
end
"#;
    for (order, src, qn) in [
        ("equation first", EQUATION_FIRST, "wi898.mixeda.S.both898"),
        ("predicate first", PREDICATE_FIRST, "wi898.mixedb.S.both898"),
    ] {
        let kb = crate::common::load_kb_with(src);
        let sym = kb
            .try_resolve_symbol(qn)
            .unwrap_or_else(|| panic!("{order}: `{qn}` must be a defined symbol"));
        assert!(
            kb.cites_a_relation(sym),
            "{order}: a PREDICATE clause is indexed under the name, so the relational \
             reading is real — and which rule is written first must not decide it",
        );
    }
}

/// THE TICKET'S OWN MEASUREMENT, across every citation spelling. All three are refused
/// (that is WI-884's limit, unchanged), and NONE may claim the name is unresolved —
/// which is the whole defect. The imported spelling is the one that regressed; the
/// other two, MEASURED, had the identical misdiagnosis, and they are driven here so
/// the fix is not pinned on one route into the same reader.
///
/// The BARE DOTTED row is a regression guard for a defect this fix itself introduced
/// and review caught: dropping `EquationFunctor` from the loader's dotted rule-citation
/// rung sent `Bool.ite` down the `field_access` PROJECTION path instead, where it drew
/// the old "expected resolved name, got unresolved" — twice, once for each segment.
#[test]
fn a_no_redex_call_is_refused_without_claiming_the_name_is_unresolved() {
    const IMPORTED: &str = r#"
namespace wi898.imported
  sort S
    import anthill.prelude.{Int64, Bool}
    import anthill.prelude.Bool.{ite}
    operation pickMax(a: Int64, b: Int64) -> Int64 = ite(Int64.gte(a, b), a, b)
  end
end
"#;
    const QUALIFIED: &str = r#"
namespace wi898.qualified
  sort S
    import anthill.prelude.{Int64, Bool}
    operation pickMax(a: Int64, b: Int64) -> Int64 = Bool.ite(Int64.gte(a, b), a, b)
  end
end
"#;
    const BARE_DOTTED: &str = r#"
namespace wi898.dotted
  sort S
    import anthill.prelude.{Int64, Bool}
    operation nameIt(a: Int64) -> Int64 = Bool.ite
  end
end
"#;
    for (spelling, src) in [
        ("imported", IMPORTED),
        ("qualified", QUALIFIED),
        ("bare dotted", BARE_DOTTED),
    ] {
        let Err(errs) = crate::common::try_load_kb_with(src) else {
            panic!("{spelling}: a computed condition has no `[simp]` redex — this must not load");
        };
        let joined = errs.join("\n");
        assert!(
            !joined.contains("unresolved"),
            "{spelling}: `ite` RESOLVES — the pre-WI-898 message called it unresolved \
             because a `Goal` functor was routed into WI-714's relation reader, which \
             found no clauses. Got {joined}",
        );
        assert!(
            joined.contains("defined by equations") && joined.contains("`[simp]`"),
            "{spelling}: the refusal must say what `ite` IS and why the citation did not \
             reduce. Got {joined}",
        );
    }
}

/// THE OTHER HALF OF THE CENSUS, and the reason the counts are carried at all: an
/// UNTAGGED defining equation is a different bug with a different repair (§5.3 —
/// `[simp]` is the enablement). A message that named only "no clause matched" would
/// send this author looking at patterns that are fine.
#[test]
fn an_untagged_defining_equation_is_diagnosed_as_inert_not_unmatched() {
    const SRC: &str = r#"
namespace wi898.inert
  sort S
    import anthill.prelude.{Int64, Bool}
    rule { inert898(?x) = ?x }
    operation drive(n: Int64) -> Int64 = inert898(n)
  end
end
"#;
    let Err(errs) = crate::common::try_load_kb_with(SRC) else {
        panic!("an untagged equation never fires, so this call cannot reduce and must not load");
    };
    let joined = errs.join("\n");
    assert!(
        joined.contains("is tagged `[simp]`") && joined.contains("never fires"),
        "the refusal must name the MISSING TAG, not blame the arguments. Got {joined}",
    );
}

/// WI-565's REMEDY, now reachable for an equation functor — the half of WI-898 that is
/// about the OTHER spelling. A bare un-imported `ite` used to get the terse "unknown
/// functor" because the remedy scan filtered on `SymbolKind::Operation` and an
/// equation functor was invisible to it.
///
/// The receiver clause is asserted ABSENT, deliberately: `receiver.ite(…)` is dot
/// DISPATCH, which selects a member operation, and `ite` is not one — so offering it
/// would be a remedy that fails the same way the call did. The qualified spelling that
/// IS offered is the one `wi884_sibling_backing_test::ite_reduces_under_both_spellings`
/// drives working.
#[test]
fn a_bare_unimported_equation_functor_gets_the_owning_sort_hint() {
    const SRC: &str = r#"
namespace wi898.hint
  sort S
    import anthill.prelude.{Int64, Bool}
    operation viaBare(n: Int64) -> Int64 = ite(true, 1, 2)
  end
end
"#;
    let Err(errs) = crate::common::try_load_kb_with(SRC) else {
        panic!("a bare `ite` with no import reaches no rules — it must be refused");
    };
    let joined = errs.join("\n");
    assert!(
        joined.contains("`ite` is a member of sort Bool") && joined.contains("`Bool.ite(…)`"),
        "WI-565's hint exists for exactly this confusion and must now see an equation \
         functor. Got {joined}",
    );
    assert!(
        !joined.contains("receiver"),
        "dot dispatch selects a member OPERATION; `ite` is not one, so the receiver \
         spelling must not be offered. Got {joined}",
    );
}

/// …AND WITHHELD ACROSS A MIXED OWNER SET, which is where the first cut of that rule
/// leaked. The message names its owning sorts JOINTLY, so one remedy has to hold for
/// EVERY one of them — a name that is an `operation` on one sort and an equation
/// functor on another must not advertise `receiver.mix898(…)`, or an author holding
/// the second sort follows it into the same failure. MEASURED against an `any`-shaped
/// first cut, which offered it.
#[test]
fn the_receiver_remedy_is_withheld_when_any_owner_is_an_equation_functor() {
    const SRC: &str = r#"
namespace wi898.mixed
  sort Opful
    import anthill.prelude.{Int64, Bool}
    operation mix898(a: Int64) -> Int64 = a
  end
  sort Eqful
    import anthill.prelude.{Int64, Bool}
    rule { mix898(?x) = ?x [simp] }
  end
  sort User
    import anthill.prelude.{Int64, Bool}
    operation drive(n: Int64) -> Int64 = mix898(n)
  end
end
"#;
    let Err(errs) = crate::common::try_load_kb_with(SRC) else {
        panic!("a bare `mix898` is in scope in neither owning sort — it must be refused");
    };
    let joined = errs.join("\n");
    assert!(
        joined.contains("member of sorts Eqful, Opful"),
        "both owners must be named — the equation functor is a member too. Got {joined}",
    );
    assert!(
        !joined.contains("receiver"),
        "`Eqful.mix898` is an equation functor, so the receiver spelling does not answer \
         for every sort named and must be withheld. Got {joined}",
    );
}

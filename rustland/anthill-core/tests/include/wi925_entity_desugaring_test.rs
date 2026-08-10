//! WI-925 / §6.3 — a free-standing `entity E` IS a single-constructor sort, so
//! it must ANSWER as one.
//!
//! §6.3 states `entity Account(id: AccountId)` and
//! `sort Account { entity Account(id: AccountId) }` are one declaration. WI-926
//! made them agree on the things a reader resolves — one symbol, the field schema,
//! the fact-head functor. Two things still differed, and both are what the wrapping
//! is *for*:
//!
//!   * an entity's SORT. The wrapping exists so that every entity has one, but the
//!     belongs-to relation answered nothing for the wrapped case, so a fact headed
//!     by a free-standing entity was filed under no sort at all. It is now TOTAL:
//!     such an entity's sort is ITSELF.
//!   * the name's CATEGORIES. One name that both is a sort and constructs could
//!     record only one `SymbolKind`, so which it got depended on source order.
//!     A name now carries a SET.
//!
//! Measured on the two spellings of one declaration, at runtime:
//!
//! ```text
//! entity E(a: String)              → ERR "row has no trigger sort and no sort hint"
//! sort E { entity E(a: String) }   → Ok(stored)
//! ```

use anthill_core::eval::value::Value;
use anthill_core::intern::SymbolKind;
use anthill_core::kb::load::{self, FileSourceResolver};
use anthill_core::kb::term::{Literal, Term};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use smallvec::SmallVec;

fn load_src(source: &str) -> KnowledgeBase {
    let parsed = parse::parse(source).expect("test source should parse");
    let mut kb = KnowledgeBase::new();
    let resolver = FileSourceResolver::new(vec![std::path::PathBuf::from("../../stdlib")]);
    load::load_all(&mut kb, &[&parsed], &resolver).expect("source should load");
    kb
}

/// The SAME declaration in both §6.3 spellings, plus a multi-variant sort that
/// neither spelling touches (the negative control below).
fn src(e_decl: &str) -> String {
    format!(
        r#"
namespace test.wi925
  import anthill.prelude.{{String}}

{e_decl}

  sort Status
    entity Open
    entity Closed
  end

  fact E(a: "x")
end
"#
    )
}

const SUGAR: &str = "  entity E(a: String)";
const DESUGARED: &str = "  sort E\n    entity E(a: String)\n  end";

/// An `E(a: "runtime")` row, built through the documented entity-term funnel
/// (`make_entity_term`, WI-299) — the same one the real runtime writer
/// (`persistence::term_ser`) goes through, so the row is canonicalized the way a
/// written row is rather than hand-assembled.
fn row(kb: &mut KnowledgeBase) -> Value {
    let e = kb.try_resolve_symbol("test.wi925.E").expect("E resolves");
    let a = kb.intern("a");
    let v = kb.alloc(Term::Const(Literal::String("runtime".into())));
    Value::term(kb.make_entity_term(e, SmallVec::new(), SmallVec::from_slice(&[(a, v)])))
}

// ── Subjects: the two spellings must agree ──────────────────────

#[test]
fn the_sugar_and_the_desugaring_agree_on_which_sort_they_belong_to() {
    // §6.3's equivalence, asked the way every caller asks it. Deliberately NOT
    // `sort_kind`: that is one index's private answer, and WI-925 fixed this by
    // making the accessor total rather than by registering a second index for the
    // sugar (which would then have to be kept in agreement with the first).
    for decl in [SUGAR, DESUGARED] {
        let kb = load_src(&src(decl));
        let e = kb.try_resolve_symbol("test.wi925.E").expect("E resolves");
        assert_eq!(
            kb.sort_of_head(e),
            Some(e),
            "§6.3: a free-standing entity IS a single-constructor sort, so it is \
             filed under ITSELF in BOTH spellings — including the sugar",
        );
    }
}

/// The relation is TOTAL — which is the whole point of the wrapping. §6.3 wraps
/// `entity E` into `sort E { entity E }` so that an entity HAS a sort; if the
/// relation stayed partial for exactly the wrapped case, the wrapping would buy
/// nothing. The sort IS the entity (WI-926: one symbol), so the edge is REFLEXIVE.
#[test]
fn every_entity_has_a_sort_including_the_wrapped_one() {
    for decl in [SUGAR, DESUGARED] {
        let kb = load_src(&src(decl));
        let e = kb.try_resolve_symbol("test.wi925.E").expect("E resolves");
        assert_eq!(
            kb.sort_of_constructor(e),
            Some(e),
            "the wrapping gives E a sort, and that sort is E itself",
        );
        // The inverse direction agrees: a single-constructor sort's one
        // constructor is itself.
        assert!(
            kb.constructors_of_sort(e).contains(&e),
            "E is its own constructor"
        );
    }
}

/// CONTROL — the STRICT view is where the fixpoint is cut, ONCE, so that the
/// several walkers which climb `parent(parent(…))` terminate. They were written
/// when "a parent is a sort, never a constructor" made the chain acyclic by
/// construction; WI-926 made one name both. Without this cut the suite
/// stack-overflows (measured, in `sort_provides_admissibly` /
/// `sort_sym_compatible`) — so this is not a stylistic preference.
#[test]
fn control_the_strict_parent_view_cuts_the_fixpoint() {
    for decl in [SUGAR, DESUGARED] {
        let kb = load_src(&src(decl));
        let e = kb.try_resolve_symbol("test.wi925.E").expect("E resolves");
        assert_eq!(
            kb.strict_parent_sort(e),
            None,
            "a chain-climbing walker sees no step from a name that is its own sort",
        );
    }
}

/// CONTROL — a differently-named variant is unaffected in BOTH views: it has a
/// strict parent, and that parent is not itself.
#[test]
fn control_a_named_variant_has_a_strict_parent() {
    let kb = load_src(&src(SUGAR));
    let status = kb
        .try_resolve_symbol("test.wi925.Status")
        .expect("Status resolves");
    let open = kb
        .try_resolve_symbol("test.wi925.Status.Open")
        .expect("Open resolves");
    assert_eq!(kb.sort_of_constructor(open), Some(status));
    assert_eq!(kb.strict_parent_sort(open), Some(status));
}

#[test]
fn a_free_standing_entity_row_has_a_trigger_sort() {
    // The consequence that made the missing edge load-bearing: a row has to be
    // filed under SOME sort, and for this shape that sort is the entity itself.
    for decl in [SUGAR, DESUGARED] {
        let mut kb = load_src(&src(decl));
        let e = kb.try_resolve_symbol("test.wi925.E").expect("E resolves");
        let r = row(&mut kb);
        assert_eq!(
            kb.fact_trigger_sort(&r),
            Some(e),
            "an `E(…)` row belongs to sort E — it is its own type (WI-926)",
        );
    }
}

#[test]
fn a_free_standing_entity_row_can_be_asserted_at_runtime() {
    // THE DRIVEN CALL SITE. `assert_checked_persistent` turns a missing trigger
    // sort into a loud backend error, so before WI-925 the sugar spelling could
    // not take a runtime row its own desugaring accepted.
    for decl in [SUGAR, DESUGARED] {
        let mut kb = load_src(&src(decl));
        let e = kb.try_resolve_symbol("test.wi925.E").expect("E resolves");
        assert_eq!(
            kb.rules_by_functor(e).len(),
            1,
            "the source `fact E(a: \"x\")` is the only row before the runtime write",
        );

        let r = row(&mut kb);
        let stored = kb
            .assert_checked_persistent(r, None)
            .unwrap_or_else(|e| panic!("a row of a free-standing entity must assert: {e:?}"));
        assert!(
            stored.is_some(),
            "no guard is declared here, so the row stores"
        );

        // The runtime row lands under the SAME functor as the source-loaded one —
        // a free-standing entity's two write paths agree on where its rows live.
        assert_eq!(
            kb.rules_by_functor(e).len(),
            2,
            "the runtime row joined the source row"
        );
    }
}

// ── Controls: what must NOT have changed ────────────────────────

/// NEGATIVE CONTROL — the registration is scoped to the free-standing/eponymous
/// shape and did not blanket-register every entity as a sort. A differently-named
/// sort-body variant stays a CONSTRUCTOR: no `sort_kind` of its own, and its rows
/// trigger on the PARENT. (`parse_test::load_sort_with_operation` pins the same
/// `sort_kind == None` from the other side.)
#[test]
fn control_a_sort_body_variant_is_a_constructor_not_a_sort() {
    let kb = load_src(&src(SUGAR));
    let status = kb
        .try_resolve_symbol("test.wi925.Status")
        .expect("Status resolves");
    let open = kb
        .try_resolve_symbol("test.wi925.Status.Open")
        .expect("Open resolves");

    // THE claim: the `Sort` role was NOT blanket-applied to every entity. This is
    // what the `!is_sort_scope` guard decides, so it is what must be asserted —
    // `sort_kind` would pass either way, since this change writes no `register_sort`.
    assert!(
        !kb.has_kind(open, SymbolKind::Sort),
        "a sort-body variant is a constructor of its sort, not a sort itself",
    );
    assert!(kb.has_kind(open, SymbolKind::Entity), "it does construct");
    assert_eq!(
        kb.strict_parent_sort(open),
        Some(status),
        "a differently-named variant IS the child of its sort",
    );
}

/// THE §6.3 EQUIVALENCE, stated on the categories themselves: one written name
/// plays BOTH roles, and both spellings record the same SET.
///
/// A symbol used to carry a single `SymbolKind`, so whichever role was recorded
/// first was the only one kept, and the two spellings disagreed (WI-926 measured
/// the flip). That is not a category; it is an accident of what was written first.
#[test]
fn both_spellings_record_the_same_set_of_categories() {
    use anthill_core::intern::SymbolKind;
    for decl in [SUGAR, DESUGARED] {
        let kb = load_src(&src(decl));
        let e = kb.try_resolve_symbol("test.wi925.E").expect("E resolves");
        assert!(
            kb.has_kind(e, SymbolKind::Sort),
            "it IS a single-constructor sort"
        );
        assert!(kb.has_kind(e, SymbolKind::Entity), "and it constructs");
    }
}

/// THE SHAPE THIS TEST WAS WRITTEN ON IS NOW REFUSED — 059 R1 / WI-997. A sort and
/// a same-named namespace-level `entity` are two declarations of one type, which
/// §6.3 already called two spellings of one declaration, so R1 names both spans and
/// refuses. Pinned here rather than deleted, because this file is where the shape
/// was introduced and a silent disappearance would read as coverage that moved.
///
/// WHAT THE ORIGINAL TEST MEASURED, AND WHERE IT LIVES NOW. It drove the property a
/// category SET exists to provide — membership does not depend on which declaration
/// came first — on the one pair that could then exhibit it. That pair is illegal;
/// the pair that remains is 059 R2's `namespace X` beside `sort X`, and
/// `wi979_declaration_order_test::both_orders_record_the_same_categories` drives it
/// in BOTH orders. The underlying hazard is still covered here too: of the three
/// arms that can produce an entity's symbol, TWO reuse an existing one and never
/// reach `define`, and the EPONYMOUS reuse arm is exercised by
/// `sugar_and_desugaring_agree_on_categories` above, whose `DESUGARED` spelling
/// takes exactly that arm.
#[test]
fn a_sort_and_a_same_named_entity_are_refused_by_059_r1() {
    const SORT_FIRST: &str = r#"
namespace test.wi925ord
  import anthill.prelude.{String}
  sort Colour
    entity Red
  end
  entity Colour(x: String)
end
"#;
    let parsed = parse::parse(SORT_FIRST).expect("test source should parse");
    let mut kb = KnowledgeBase::new();
    let resolver = FileSourceResolver::new(vec![std::path::PathBuf::from("../../stdlib")]);
    let errs = match load::load_all(&mut kb, &[&parsed], &resolver) {
        Err(e) => e,
        Ok(_) => panic!("059 R1 must refuse a sort and a same-named entity in one scope"),
    };
    let joined = errs
        .iter()
        .map(|e| e.to_string())
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        joined.contains("type 'Colour' is declared more than once")
            && joined.contains("`sort` at")
            && joined.contains("`entity` at"),
        "the refusal must name BOTH declarations; got:\n{joined}",
    );
}

/// CONTROL — the ORDER within the set still records which keyword was written,
/// which is the one thing `kind_of` may legitimately report (a diagnostic, or
/// reflect's `kind` string). Membership is order-free; the head is not.
///
/// Passes with and without the fix (`primary_kind` reproduces the old single
/// `kind` field exactly, since `define` was first-writer-wins) — it documents the
/// intended reading rather than measuring the change.
#[test]
fn control_the_head_of_the_set_is_the_written_keyword() {
    use anthill_core::intern::SymbolKind;
    let sugar = load_src(&src(SUGAR));
    let desugared = load_src(&src(DESUGARED));
    let sym = |kb: &KnowledgeBase| kb.try_resolve_symbol("test.wi925.E").expect("E resolves");

    assert_eq!(
        sugar.kind_of(sym(&sugar)),
        Some(SymbolKind::Entity),
        "`entity E` wrote `entity`"
    );
    assert_eq!(
        desugared.kind_of(sym(&desugared)),
        Some(SymbolKind::Sort),
        "`sort E` wrote `sort`"
    );
}

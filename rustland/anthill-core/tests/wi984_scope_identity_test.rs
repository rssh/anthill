//! WI-984 — SCOPE-HOOD IS A TYPE, AND THE OWNER PROJECTION IS TOTAL.
//!
//! Rustland's scope key was a bare `u32`: the raw `TermId` of the owner's nullary
//! name term. Two things followed, and the ticket is both of them.
//!
//! 1. A scope, an arbitrary term and an arbitrary index were ONE TYPE, so "this
//!    raw is a scope" was a promise each caller carried. That half is a COMPILE
//!    error now, not a runtime test — see the `compile_fail` blocks on
//!    `intern::ScopeId`, which is where they can actually run.
//!
//! 2. Recovering the owner FROM that key was a QUERY — fetch the term, match a
//!    nullary `Term::Fn`, answer `Option` — and the query was NOT TOTAL, because
//!    `KnowledgeBase::alloc` canonicalizes a CONSTRUCTOR symbol's nullary `Fn` to
//!    a `Term::Ref` (WI-511). Every scope owned by a constructor answered `None`.
//!    MEASURED over a stdlib load: 227 of 2602 resolved symbols. They are one
//!    population — an entity's FIELDS are declared in the CONSTRUCTOR's scope, and
//!    constructors are precisely the symbols whose name term is a `Ref`. This file
//!    drives that half.
//!
//! WHICH TESTS FAIL WHEN THE CHANGE IS BACKED OUT, MEASURED by restoring the
//! `Term::Fn`-only match: `a_field_names_its_declaring_constructor` (reads `None`)
//! and `the_scope_builtin_answers_for_a_constructor_owned_scope` (yields zero
//! solutions).
//!
//! WHAT PASSES EITHER WAY, BY DESIGN: `an_operation_names_its_declaring_sort` —
//! its scope owner is a SORT, never a constructor, so the old query answered it
//! too. It is here as the contrast that says the first test measures
//! constructor-hood and not merely "the loader records scopes". Also passing
//! either way: `intern.rs`'s resolution unit tests and the whole loader suite —
//! the scope KEY changed representation, but its mint and its readers changed
//! together, so no resolution answer moves.
//!
//! NOT IN THE POPULATION, checked rather than assumed: §6.3's eponymous
//! constructor. `sort Project { entity Project(…) }` collapses onto one symbol
//! (WI-926), but that symbol is NOT marked a constructor (measured), so its scope
//! term stayed an `Fn` and its members answered before this change as well.

mod common;

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, Var};
use anthill_core::kb::KnowledgeBase;
use smallvec::SmallVec;

const SOURCE: &str = r#"
namespace wi984
  sort Tank
    entity Full(litres: Int64)
    operation fill(t: Tank) -> Tank
  end
end
"#;

fn scope_qn(kb: &KnowledgeBase, member_qn: &str) -> Option<String> {
    let sym = kb
        .try_resolve_symbol(member_qn)
        .unwrap_or_else(|| panic!("{member_qn} must resolve"));
    kb.declaring_scope_symbol(sym)
        .map(|s| kb.qualified_name_of(s).to_string())
}

/// THE DEFECT. A field is declared in its CONSTRUCTOR's scope, and a constructor
/// is exactly the symbol whose nullary name term `alloc` stores as a `Term::Ref` —
/// so a field could never name its own declaring scope. Reads `None` when the
/// change is backed out.
#[test]
fn a_field_names_its_declaring_constructor() {
    let kb = common::load_kb_with(SOURCE);
    assert!(
        kb.is_constructor_symbol(kb.try_resolve_symbol("wi984.Tank.Full").unwrap()),
        "precondition: the declaring scope's owner is a CONSTRUCTOR — the property \
         the old term-matching query could not see past",
    );
    assert_eq!(
        scope_qn(&kb, "wi984.Tank.Full.litres").as_deref(),
        Some("wi984.Tank.Full"),
    );
}

/// THE CONTRAST, and it passes either way by design: an operation's scope owner is
/// a SORT, which is not a constructor, so its name term was a nullary `Fn` and the
/// old query answered it. Without this row the test above could be read as
/// asserting that the loader records scopes at all.
#[test]
fn an_operation_names_its_declaring_sort() {
    let kb = common::load_kb_with(SOURCE);
    assert!(
        !kb.is_constructor_symbol(kb.try_resolve_symbol("wi984.Tank").unwrap()),
        "precondition: this scope's owner is NOT a constructor",
    );
    assert_eq!(scope_qn(&kb, "wi984.Tank.fill").as_deref(), Some("wi984.Tank"));
}

/// `scope(?sym, ?owner)` — the LANGUAGE-level reader of the same projection, which
/// failed on exactly the same symbols. Driven through resolution rather than the
/// Rust accessor, so the two cannot drift apart on what they answer. Yields zero
/// solutions when the change is backed out.
#[test]
fn the_scope_builtin_answers_for_a_constructor_owned_scope() {
    let mut kb = common::load_kb_with(SOURCE);
    let field = kb.try_resolve_symbol("wi984.Tank.Full.litres").expect("field symbol");
    let owner = kb.try_resolve_symbol("wi984.Tank.Full").expect("owner symbol");

    let scope_sym = kb.resolve_symbol("anthill.reflect.scope");
    let field_ref = kb.alloc(Term::Ref(field));
    let r = kb.intern("r");
    let r_vid = kb.fresh_var(r);
    let r_var = kb.alloc(Term::Var(Var::Global(r_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: scope_sym,
        pos_args: SmallVec::from_slice(&[field_ref, r_var]),
        named_args: SmallVec::new(),
    });

    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(solutions.len(), 1, "`scope` must answer for a field symbol");
    let answer = kb.reify(r_var, &solutions[0].subst).expect_term();
    assert_eq!(
        kb.name_term_sym(answer),
        owner,
        "…and the answer is the declaring constructor",
    );
}

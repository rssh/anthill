//! A PARAMETERIZED standalone `provides` block loads.
//!
//! `provides Stack[T = Int64] language rust … end` is the form the grammar's own
//! doc comment documents (`tree-sitter-anthill/grammar.js`), and nothing in the
//! repo — no stdlib file, no fixture, no test — exercised it. That gap let the
//! sort/domain-as-`Symbol` change ship a loader ABORT for it: the block's spec
//! lowers to a SortView APPLICATION (`SortView(Stack, T = Int64)`), not a bare
//! name, and the new domain derivation unwrapped it as one.
//!
//! Two things are pinned here:
//!
//!   * the DOMAIN of the block's inner clauses is the BASE sort (`Stack`) — a
//!     clause belongs to the sort, not to one instantiation of it;
//!   * so is the SCOPE the block's body resolves in.
//!
//! THE SECOND ONE USED TO SAY THE OPPOSITE — "the SCOPE is the full applied term,
//! so `Stack[T = Int64]` and `Stack[T = String]` stay distinct identities" —
//! and WI-984 retired it. That identity was VACUOUS: nothing is ever declared
//! into an applied term's scope and no parent link reaches one, so BOTH
//! instantiations resolved against an empty scope with no parents, while the bare
//! `provides Stack` beside them resolved against `Stack`'s real scope. Keying
//! scopes on the owning SYMBOL made the phantom unrepresentable.
//!
//! The rows below stopped short of finding that: with only `language`/`artifact`
//! clauses, no name is ever resolved inside the block, so nothing asks what the
//! scope is. `*_resolves_a_spec_scoped_name` adds a body that does.
//!
//! The unparameterized block is kept beside each as the control: it took the same
//! code path before and after, so if IT breaks the cause is not the spec shape.

use anthill_core::kb::KnowledgeBase;

use crate::common::{load_kb_with, try_load_kb_with};
use anthill_core::intern::Symbol;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Literal, Term};
use smallvec::SmallVec;

/// Load `source` over the full stdlib, returning the load errors as strings.
/// The stdlib is REQUIRED, not incidental: the `Implementation` fact this block
/// emits names `anthill.realization.CarrierBinding`, so a prelude-only KB aborts
/// in `resolve_symbol` before reaching anything under test.
/// Deliberately NOT `load_kb_with` (which panics on error): the point of these
/// tests is what the loader DOES with the input, so a failure must be readable.
fn load_errors(source: &str) -> Vec<String> {
    try_load_kb_with(source).err().unwrap_or_default()
}

const PARAMETERIZED: &str = r#"
namespace test.pb
  sort Stack
    entity mk(x: Int64)
  end

  provides Stack[T = Int64]
    language rust
    artifact "src/stack.rs"
  end
end
"#;

const UNPARAMETERIZED: &str = r#"
namespace test.pb
  sort Stack
    entity mk(x: Int64)
  end

  provides Stack
    language rust
    artifact "src/stack.rs"
  end
end
"#;

#[test]
fn parameterized_provides_block_loads() {
    // Before the fix this did not FAIL — it panicked the process, so there was no
    // error list to assert on at all.
    assert!(
        load_errors(PARAMETERIZED).is_empty(),
        "parameterized provides block should load: {:?}",
        load_errors(PARAMETERIZED)
    );
}

#[test]
fn unparameterized_provides_block_loads() {
    assert!(
        load_errors(UNPARAMETERIZED).is_empty(),
        "unparameterized provides block should load: {:?}",
        load_errors(UNPARAMETERIZED)
    );
}

/// The `Implementation` fact is emitted for a non-`anthill` language, and its
/// domain is the BASE sort — the same domain the unparameterized block yields.
/// This is the assertion that would have caught the abort as a *wrong answer*
/// rather than as a crash: if the domain were derived from the applied term it
/// would differ between the two blocks.
#[test]
fn both_spec_shapes_file_the_implementation_fact_under_the_base_sort() {
    let domain_of = |source: &str| -> Vec<String> {
        let mut kb: KnowledgeBase = crate::common::load_kb_with(source);
        // WI-922: found by HEAD FUNCTOR. These clauses used to be filed under a
        // raw intern of `anthill.realization.Implementation` as their clause
        // KEY, so the key doubled as the functor question; they now carry the
        // `Fact` kind like every other metadata fact, and the functor index is
        // what selects them. Note `try_resolve_symbol`, not `intern` — the head
        // functor is the RESOLVED symbol, a different one.
        let impl_sym = kb.try_resolve_symbol("anthill.realization.Implementation")
            .expect("resolve anthill.realization.Implementation");
        // Filtered to this file's namespace: the Rust host bindings loaded
        // alongside emit their own `Implementation` facts (Int64, String, …).
        kb.rules_by_functor(impl_sym)
            .iter()
            .map(|&rid| kb.qualified_name_of(kb.rule_domain(rid)).to_string())
            .filter(|d| d.starts_with("test.pb"))
            .collect()
    };
    let param = domain_of(PARAMETERIZED);
    assert_eq!(param.len(), 1, "expected one Implementation fact, got {param:?}");
    assert_eq!(param, domain_of(UNPARAMETERIZED), "domain must not depend on the spec shape");
    assert!(param[0].ends_with("Stack"), "domain should be the base sort, got {param:?}");
}

// ── WI-984: the block's BODY resolves in the spec's scope ────────────────────

/// `is_full` is declared inside `Stack` and reachable ONLY through the block's
/// scope. If that scope is the applied term's empty phantom, `is_full` falls
/// through to a bare intern that heads no clause and the goal yields ZERO
/// solutions — so a passing row is evidence about the scope, not about the parse.
fn with_body(spec: &str) -> String {
    format!(
        r#"
namespace test.pbody
  sort Stack
    sort T = ?
    rule is_full(?s) :- eq(?s, ?s)
  end

  provides {spec} language anthill
    rule stack_provided(?x) :- is_full(?x)
  end
end
"#
    )
}

/// `stack_provided(7)` — one solution iff the body resolved `is_full` to the
/// clause `Stack` declares.
fn solutions_for_stack_provided(kb: &mut KnowledgeBase) -> usize {
    // A standalone `provides` block's head functor is bare-interned rather than
    // given a qualified definition (pre-existing, and the same for both
    // spellings), so it is reached by the name the loader actually minted.
    let goal_sym: Symbol = kb
        .lookup_symbol("stack_provided")
        .expect("the provides block's rule head must exist");
    let seven = kb.alloc(Term::Const(Literal::Int(7)));
    let goal = kb.alloc(Term::Fn {
        functor: goal_sym,
        pos_args: SmallVec::from_elem(seven, 1),
        named_args: SmallVec::new(),
    });
    kb.resolve(&[goal], &ResolveConfig::default()).len()
}

/// THE CONTROL — passes before and after WI-984: the bare form always had
/// `Stack`'s real scope.
#[test]
fn unparameterized_provides_body_resolves_a_spec_scoped_name() {
    let mut kb = load_kb_with(&with_body("Stack"));
    assert_eq!(solutions_for_stack_provided(&mut kb), 1);
}

/// Aborts the load (`name_term_sym: … is not a name term`) when WI-984's scope
/// change is backed out — the applied term is not a name and cannot own a scope.
#[test]
fn parameterized_provides_body_resolves_a_spec_scoped_name() {
    let mut kb = load_kb_with(&with_body("Stack[T = Int64]"));
    assert_eq!(
        solutions_for_stack_provided(&mut kb),
        1,
        "an instantiated spec resolves in the same scope its bare spelling does",
    );
}

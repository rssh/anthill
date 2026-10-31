//! A `@[simp]` or `@[unfold]` tag stands on an equation and nowhere else (kernel-language.md
//! §5.3).
//!
//! THE RULE. The tag makes an equation run; on an operation, a predicate rule, a denial, a fact,
//! a constraint, a sort, an entity or a const it does nothing, and it is a load error there. A
//! declaration's `@[…]` is written after it (§5.8), so a tag set in front of a rule is the
//! declaration before it's — the case the refusal is for.
//!
//! BEFORE (measured 2026-10-31 on 34886564): every one of these loaded clean, and the tag was
//! dropped. `operation g(x: Int64) -> Int64 = x` followed by `@[simp] rule g(?x) <=> 20` gave
//! the operation the tag and left the equation untagged, so `g(1)` ran the body, 1, with no
//! diagnostic.
//!
//! EVERY ROW HAS ITS OWN SOURCE. CONTROLS at each row.

use anthill_core::kb::load::LoadError;

use crate::common::{run_int64, unrendered_load_errors_of};

/// `test.<name>`, holding `body`.
fn ns(name: &str, body: &str) -> String {
    format!(
        "namespace test.{name}\n  import anthill.prelude.{{Int64}}\n  \
         import anthill.prelude.PartialEq.{{eq}}\n  fact a(1)\n{body}\nend\n"
    )
}

/// The load of `body` is refused with ONE error, the tag's, naming `declaration` and `tag`.
#[track_caller]
fn assert_refused_on(name: &str, body: &str, tag: &str, declaration: &str) {
    let errors = unrendered_load_errors_of(&ns(name, body));
    let peeled: Vec<&LoadError> = errors.iter().map(LoadError::peel).collect();
    assert!(
        matches!(
            peeled.as_slice(),
            [LoadError::RewriteTagOffEquation { tag: t, declaration: d, .. }]
                if t == tag && *d == declaration
        ),
        "{name}: expected the one refusal of `@[{tag}]` on {declaration}, got {errors:?}"
    );
}

/// EVERY DECLARATION THAT IS NOT AN EQUATION refuses the tag, naming what it stands on. FAILS
/// with the refusal backed out (`refuse_rewrite_tags` pushing nothing): each loads clean.
#[test]
fn a_rewrite_tag_off_an_equation_is_refused() {
    for (name, body, tag, declaration) in [
        (
            "rt.op",
            "  operation g(x: Int64) -> Int64 = x @[simp]",
            "simp",
            "an operation",
        ),
        (
            "rt.pred",
            "  rule p(?x) :- a(?x) @[simp]",
            "simp",
            "a predicate rule",
        ),
        (
            "rt.unfold",
            "  rule p(?x) :- a(?x) @[unfold]",
            "unfold",
            "a predicate rule",
        ),
        ("rt.denial", "  rule ⊥ :- a(2) @[simp]", "simp", "a denial"),
        (
            "rt.identity",
            "  operation pick(x: Int64) -> Int64 = x\n  rule pick(?x) === 7 :- a(?x) @[simp]",
            "simp",
            "a structural identity test (`===`)",
        ),
        ("rt.fact", "  fact b(1) @[simp]", "simp", "a fact"),
        (
            "rt.constraint",
            "  constraint c: eq(?x, 1) :- a(?x) @[simp]",
            "simp",
            "a constraint",
        ),
        ("rt.sort", "  sort S = ? @[simp]", "simp", "a sort"),
        (
            "rt.sortbody",
            "  sort W\n    operation h() -> Int64 = 1\n  end @[simp]",
            "simp",
            "a sort",
        ),
        ("rt.entity", "  entity box(v: Int64) @[simp]", "simp", "an entity"),
        ("rt.const", "  const k: Int64 = 3 @[simp]", "simp", "a const"),
    ] {
        assert_refused_on(name, body, tag, declaration);
    }
}

/// A TAG SET IN FRONT OF A RULE is the operation's before it, and refused there. It loaded, and
/// `g(1)` ran the body (1) with the equation it was meant for inert. FAILS with the refusal
/// backed out: the load is clean.
#[test]
fn a_tag_set_in_front_of_a_rule_is_refused_on_the_declaration_before() {
    assert_refused_on(
        "rt.front",
        "  operation g(x: Int64) -> Int64 = x\n  @[simp] rule g(?x) <=> 20\n  \
         operation run() -> Int64 = g(1)",
        "simp",
        "an operation",
    );
}

/// AN EQUATION TAKES THE TAG, bodyless, guarded, with another key beside it and in its `fact`
/// spelling, and runs: `g(1)` rewrites to 20 where the guarded `g(?x) = 10 :- a(2)` does not
/// hold, and `fact h(?x) <=> 30 @[simp]` rewrites `h(1)`. Passes either way by design: it is
/// the control that the refusal leaves an equation's tag alone.
#[test]
fn an_equation_takes_the_tag() {
    let src = ns(
        "rt.equation",
        "  operation g(x: Int64) -> Int64 = x\n  \
         rule g(?x) = 10 :- a(2) @[simp]\n  \
         rule g(?x) <=> 20 @[unfold, simp]\n  \
         operation run() -> Int64 = g(1)",
    );
    assert_eq!(run_int64(&src, "test.rt.equation.run"), Ok(20));
    let src = ns(
        "rt.factequation",
        "  operation h(x: Int64) -> Int64 = x\n  \
         fact h(?x) <=> 30 @[simp]\n  \
         operation run() -> Int64 = h(1)",
    );
    assert_eq!(run_int64(&src, "test.rt.factequation.run"), Ok(30));
}

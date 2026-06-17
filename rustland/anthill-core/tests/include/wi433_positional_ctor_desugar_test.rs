//! WI-433: positional constructor pattern vs NAMED-field sort.
//!
//! A positional constructor term (`Verified(?)`) and a named one
//! (`Verified(at: …)`) must share ONE in-KB shape: a stored fact's named args
//! (sorted by field) never unify with a positional pattern via the discrim tree,
//! so `WorkItem(id: ?dep, status: Verified(?))` loaded clean yet silently
//! NEVER matched the named `Verified(at: …)` facts — `all_deps_verified`
//! rejected every dependent (found driving heimdall WI-005, commit 9fa0da6).
//!
//! Fix direction (b), DESUGAR: positional args map to the declared fields NOT
//! already given by name, in declaration order ("positional application is sugar
//! for names", kernel spec §5.2; generalizes the `some(x)` → `some(value: x)`
//! canonicalization). More positional args than unfilled fields is a LOUD load
//! error. Reflect `anthill.reflect.*` Expr meta-ctors (`ho_apply`, `match_expr`,
//! …) keep their positional reflect shape. Match-expression patterns do NOT
//! share the gap — eval's `match_constructor_pattern` already maps positional
//! sub-patterns to leading field indices.

use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::resolve::ResolveConfig;
use smallvec::SmallVec;

fn config() -> ResolveConfig {
    ResolveConfig { max_solutions: 10, ..ResolveConfig::default() }
}

fn var(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

/// Resolve `functor(?x)` and return the solution count.
fn resolve_unary(kb: &mut KnowledgeBase, functor: &str) -> usize {
    let f = kb.resolve_symbol(functor);
    let x = var(kb, "x");
    let q = kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_elem(x, 1),
        named_args: SmallVec::new(),
    });
    kb.resolve(&[q], &config()).len()
}

/// The exact 9fa0da6 pre-fix shape: a positional `Verified(?)` sub-pattern in a
/// rule body matches the named `Verified(at: …)` facts.
#[test]
fn positional_subpattern_matches_named_fact() {
    let src = r#"
namespace test.wi433.match
  import anthill.prelude.String
  sort Status
    import anthill.prelude.String
    entity Verified(at: String)
    entity Opened
  end
  sort Item
    import anthill.prelude.String
    import test.wi433.match.Status
    entity WorkItem(id: String, status: Status)
  end
  rule has_verified(?id) :- WorkItem(id: ?id, status: Verified(?))
  fact WorkItem(id: "a", status: Verified(at: "now"))
  fact WorkItem(id: "b", status: Opened)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        resolve_unary(&mut kb, "test.wi433.match.has_verified"),
        1,
        "positional Verified(?) must match the one named Verified(at:) fact",
    );
}

/// Symmetric direction: a positional FACT matches a named rule pattern.
#[test]
fn positional_fact_matches_named_pattern() {
    let src = r#"
namespace test.wi433.fact
  import anthill.prelude.String
  sort Status
    import anthill.prelude.String
    entity Verified(at: String)
  end
  sort Item
    import anthill.prelude.String
    import test.wi433.fact.Status
    entity WorkItem(id: String, status: Status)
  end
  rule done(?id) :- WorkItem(id: ?id, status: Verified(at: ?))
  fact WorkItem(id: "a", status: Verified("now"))
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        resolve_unary(&mut kb, "test.wi433.fact.done"),
        1,
        "positional Verified(\"now\") fact must match named Verified(at: ?) pattern",
    );
}

/// MIXED order: positional args fill the fields NOT given by name (declaration
/// order), matching the materializer's rank-among-not-named read. `pair(b: B, A)`
/// and `pair(A, b: B)` both denote the same `pair(a: A, b: B)`.
#[test]
fn mixed_positional_named_fills_unnamed_fields() {
    let src = r#"
namespace test.wi433.mixed
  import anthill.prelude.String
  sort P
    import anthill.prelude.String
    entity duo(a: String, b: String)
  end
  rule both(?id) :-
    duo(a: ?id, b: "y"),
    duo(?id, b: "y"),
    duo(b: "y", ?id)
  fact duo(a: "x", b: "y")
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    // All three sub-goals (named, positional-prefix, named-prefix) denote
    // pair(a: "x", b: "y") and unify with the single fact, binding ?id = "x".
    assert_eq!(
        resolve_unary(&mut kb, "test.wi433.mixed.both"),
        1,
        "all three positional/named orderings must match the one fact",
    );
}

/// LOUD: more positional args than the sort's fields is a hard load error
/// naming the declared fields (never a silent never-match).
#[test]
fn over_arity_positional_is_loud_load_error() {
    let src = r#"
namespace test.wi433.arity
  import anthill.prelude.String
  sort Status
    import anthill.prelude.String
    entity Verified(at: String)
  end
  fact Verified("now", "extra")
end
"#;
    match crate::common::try_load_kb_with(src) {
        Ok(_) => panic!("Verified(\"now\", \"extra\") (2 args, 1 field) must fail to load"),
        Err(errs) => assert!(
            errs.iter().any(|e| e.contains("Verified") && e.contains("at")),
            "the arity error must name the constructor and its declared field; got: {errs:?}",
        ),
    }
}

#[test]
fn nullary_entity_unaffected() {
    // A bare nullary variant (`Opened`) and the all-fresh partial pattern are
    // untouched: `!new_pos.is_empty()` gates the desugar off for zero positional.
    let src = r#"
namespace test.wi433.nullary
  import anthill.prelude.String
  sort Status
    import anthill.prelude.String
    entity Verified(at: String)
    entity Opened
  end
  sort Item
    import anthill.prelude.String
    import test.wi433.nullary.Status
    entity WorkItem(id: String, status: Status)
  end
  rule is_open(?id) :- WorkItem(id: ?id, status: Opened)
  fact WorkItem(id: "a", status: Opened)
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(resolve_unary(&mut kb, "test.wi433.nullary.is_open"), 1);
}

#[test]
fn zero_field_variant_given_positional_is_loud_error() {
    // A 0-field variant given a positional arg has zero unfilled fields → loud
    // over-arity error (never a silent never-match).
    let src = r#"
namespace test.wi433.zerofield
  sort Status
    entity Opened
  end
  fact Opened("oops")
end
"#;
    match crate::common::try_load_kb_with(src) {
        Ok(_) => panic!("Opened(\"oops\") on a 0-field variant must fail to load"),
        Err(errs) => assert!(
            errs.iter().any(|e| e.contains("Opened")),
            "the error must name the over-applied variant; got: {errs:?}",
        ),
    }
}

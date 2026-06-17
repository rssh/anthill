//! WI-499: positional-ctor desugar (WI-433) + partial-named-arg expansion are
//! load-order-INDEPENDENT.
//!
//! Both the WI-433 desugar (positional → named) and the pre-existing
//! partial-named-arg expansion gate on `kb.entity_field_names(functor)`. That
//! registry used to be populated in `load_entity` during the source-order load
//! pass, so a positional constructor whose entity is declared TEXTUALLY AFTER
//! the referencing fact/rule saw `entity_field_names = None` at convert time —
//! the positional term stayed positional and silently never unified with the
//! canonical named form (the WI-433 never-match, just reordered), and the
//! over-arity loud error was silently skipped.
//!
//! Fix: register entity field NAMES in `scan_definitions` pass-1, before ANY
//! term conversion, so both transforms (and the over-arity loud check) are
//! order-independent.

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

/// The exact WI-499 probe: a positional `Verified(?)` rule pattern must match a
/// NAMED `Verified(at: …)` fact (the genuine WI-433 shape mismatch — two
/// positional arity-1 terms would unify trivially), with the rule and fact
/// placed TEXTUALLY BEFORE `sort Status` declares `entity Verified(at: String)`.
/// Pre-fix the desugar saw `entity_field_names = None` at convert time → the
/// positional pattern stayed positional and never matched the named fact (0);
/// the desugar must now fire regardless of declaration order → 1.
#[test]
fn forward_referenced_entity_still_desugars() {
    let src = r#"
namespace test.wi499.forward
  import anthill.prelude.String
  rule has_verified(?id) :- WorkItem(id: ?id, status: Verified(?))
  fact WorkItem(id: "a", status: Verified(at: "now"))
  fact WorkItem(id: "b", status: Opened)
  sort Status
    import anthill.prelude.String
    entity Verified(at: String)
    entity Opened
  end
  sort Item
    import anthill.prelude.String
    import test.wi499.forward.Status
    entity WorkItem(id: String, status: Status)
  end
end
"#;
    let mut kb = crate::common::load_kb_with(src);
    assert_eq!(
        resolve_unary(&mut kb, "test.wi499.forward.has_verified"),
        1,
        "forward-referenced positional Verified(?) must still desugar to match the named Verified(at:) fact",
    );
}

/// The over-arity LOUD check must also fire regardless of order: a positional
/// fact with more args than the (forward-declared) entity's fields is a hard
/// load error, not a silent skip.
#[test]
fn forward_referenced_over_arity_is_loud() {
    let src = r#"
namespace test.wi499.arity
  import anthill.prelude.String
  fact Verified("now", "extra")
  sort Status
    import anthill.prelude.String
    entity Verified(at: String)
  end
end
"#;
    match crate::common::try_load_kb_with(src) {
        Ok(_) => panic!("forward-ref Verified(\"now\", \"extra\") (2 args, 1 field) must fail to load"),
        Err(errs) => assert!(
            errs.iter().any(|e| e.contains("Verified") && e.contains("at")),
            "the arity error must name the constructor and its declared field; got: {errs:?}",
        ),
    }
}

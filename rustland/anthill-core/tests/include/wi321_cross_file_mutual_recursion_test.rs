//! WI-321: cross-file mutually-recursive sort declarations are a SUPPORTED
//! loader pattern, and this pins the load-bearing invariant.
//!
//! `scan_definitions` defines ALL names across ALL files (sub-pass 1) before it
//! resolves ANY `requires`/`import` (sub-pass 2). So two files whose entities
//! reference each other's sorts both load: each file's pass-1 ignores the
//! other's content, so both sort names exist before either file's imports
//! resolve. This is the same "collect all top-level names, then resolve bodies"
//! technique SML/Haskell use for mutual recursion — not an accident.
//!
//! The cycle here is genuine and structural, in both directions:
//!   test.wi321.tree :  Node.leaf   : Leaf            (tree -> leaf)
//!   test.wi321.leaf :  Leaf.parent : Option[T = Tree] (leaf -> tree)
//! plus a mutual `import` cycle (tree imports leaf.Leaf, leaf imports tree.Tree).
//!
//! If a future single-pass / streaming loader refactor broke the pass-1-first
//! ordering (each file fully processed before the next), one direction's import
//! would resolve against a not-yet-defined name and load would fail loudly —
//! `UnresolvedImport` for the selective `import …Leaf`/`…Tree`, plus
//! `UnresolvedName` for the bare imported sort used in the field-type position —
//! failing this test.

use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::resolve::ResolveConfig;
use smallvec::SmallVec;

/// File A — the `Tree` namespace. References `Leaf` (file B) in `Node.leaf` and
/// in the fact; imports the `Tree` consumer's counterpart from file B.
const TREE_SRC: &str = r#"
namespace test.wi321.tree
  import anthill.prelude.String
  import anthill.prelude.Option.{none}
  import test.wi321.leaf.Leaf

  sort Tree
    entity Node(name: String, leaf: Leaf)
  end

  rule tree_tip(?tip) :- Node(name: ?, leaf: Leaf(name: ?tip, parent: ?))

  fact Node(name: "root", leaf: Leaf(name: "tip", parent: none))
end
"#;

/// File B — the `Leaf` namespace. References `Tree` (file A) in `Leaf.parent`;
/// imports `Tree` from file A. Closes the mutual cycle.
const LEAF_SRC: &str = r#"
namespace test.wi321.leaf
  import anthill.prelude.String
  import anthill.prelude.Option
  import test.wi321.tree.Tree

  sort Leaf
    entity Leaf(name: String, parent: Option[T = Tree])
  end
end
"#;

fn config() -> ResolveConfig {
    ResolveConfig { max_solutions: 10, ..ResolveConfig::default() }
}

fn var(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

fn count_unary(kb: &mut KnowledgeBase, functor: &str) -> usize {
    let f = kb.resolve_symbol(functor);
    let x = var(kb, "x");
    let q = kb.alloc(Term::Fn {
        functor: f,
        pos_args: SmallVec::from_elem(x, 1),
        named_args: SmallVec::new(),
    });
    kb.resolve(&[q], &config()).len()
}

/// The core invariant: two files with a mutual structural cycle both load, and
/// the cross-file references are usable — a rule in file A that pattern-matches
/// file B's `Leaf` constructor resolves against the fact.
#[test]
fn cross_file_mutual_structural_recursion_loads_and_resolves() {
    let mut kb = crate::common::try_load_kb_with_files(&[TREE_SRC, LEAF_SRC])
        .unwrap_or_else(|errs| panic!("cross-file mutual recursion must load; got: {errs:?}"));
    assert_eq!(
        count_unary(&mut kb, "test.wi321.tree.tree_tip"),
        1,
        "the rule must match the fact built from the cross-file Leaf constructor",
    );
}

/// Robustness: the result must NOT depend on which file is scanned first — the
/// pass-1-defines-all-names-first invariant makes load order irrelevant. Pin
/// the reversed order too so a future order-sensitive refactor is caught.
#[test]
fn cross_file_mutual_recursion_is_load_order_independent() {
    crate::common::try_load_kb_with_files(&[LEAF_SRC, TREE_SRC])
        .unwrap_or_else(|errs| panic!("reversed file order must also load; got: {errs:?}"));
}

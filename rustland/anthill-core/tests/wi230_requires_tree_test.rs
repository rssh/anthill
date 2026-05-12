//! WI-230 — tree-structured `requires` declaration with substitution
//! composition.
//!
//! Three acceptance points:
//! 1. Tree shape mirrors the declared `requires` hierarchy.
//! 2. Substitution composition: a leaf in Wi222Outer's tree carries
//!    `T = Wi222Outer.T` directly, not `T = Ordered.T` (root-scoped).
//! 3. `flatten_requires_tree` reproduces the same set of entries that
//!    `requires_chain` returns (consistency between tree and flat views).

mod common;

use anthill_core::kb::term::Term;
use anthill_core::kb::typing::{
    flatten_requires_tree, requires_chain, requires_tree, RequiresNode, RequiresEntry,
};
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::parse;

use common::collect_stdlib_and_rust_bindings;

fn load_with(source: &str) -> KnowledgeBase {
    let mut files = collect_stdlib_and_rust_bindings();
    files.sort();
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src = std::fs::read_to_string(p).expect("read stdlib file");
            parse::parse(&src).expect("parse stdlib file")
        })
        .collect();
    parsed.push(parse::parse(source).expect("parse user source"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load::load_all(&mut kb, &refs, &NullResolver).expect("load");
    kb
}

#[test]
fn tree_shape_mirrors_declared_requires_hierarchy() {
    // A two-level requires chain:
    //   Wi230Outer requires Wi230Middle[T]
    //   Wi230Middle requires Wi230Leaf[T]
    // requires_tree(Wi230Outer) should yield:
    //   [ Middle-node with sub_requires = [ Leaf-node with sub_requires = [] ] ]
    let src = r#"
namespace test.wi230.tree_shape
  export Wi230Outer, Wi230Middle, Wi230Leaf
  sort Wi230Leaf
    sort T = ?
  end
  sort Wi230Middle
    sort T = ?
    requires Wi230Leaf[T = T]
  end
  sort Wi230Outer
    sort T = ?
    requires Wi230Middle[T = T]
  end
end
"#;
    let mut kb = load_with(src);

    let outer = kb
        .try_resolve_symbol("test.wi230.tree_shape.Wi230Outer")
        .expect("Outer");
    let middle = kb
        .try_resolve_symbol("test.wi230.tree_shape.Wi230Middle")
        .expect("Middle");
    let leaf = kb
        .try_resolve_symbol("test.wi230.tree_shape.Wi230Leaf")
        .expect("Leaf");

    let tree = requires_tree(&mut kb, outer);
    assert_eq!(tree.len(), 1, "Outer has one direct require (Middle)");
    let middle_node = &tree[0];
    assert_eq!(middle_node.entry.required_sort, middle);

    assert_eq!(
        middle_node.sub_requires.len(),
        1,
        "Middle has one direct require (Leaf)"
    );
    let leaf_node = &middle_node.sub_requires[0];
    assert_eq!(leaf_node.entry.required_sort, leaf);
    assert_eq!(
        leaf_node.sub_requires.len(),
        0,
        "Leaf has no requires; sub_requires must be empty"
    );
}

#[test]
fn substitution_composes_through_chain_to_root_scope() {
    // Wi230Outer requires Wi230Middle[T], Wi230Middle requires Wi230Leaf[T].
    // Each `T` here refers to the declaring sort's own type-param. The
    // tree's leaf entry must carry `T = Ref(Wi230Outer.T)` after
    // composition — NOT `T = Ref(Wi230Middle.T)` (the declared form).
    let src = r#"
namespace test.wi230.subst_compose
  export Wi230Outer, Wi230Middle, Wi230Leaf
  sort Wi230Leaf
    sort T = ?
  end
  sort Wi230Middle
    sort T = ?
    requires Wi230Leaf[T = T]
  end
  sort Wi230Outer
    sort T = ?
    requires Wi230Middle[T = T]
  end
end
"#;
    let mut kb = load_with(src);

    let outer_t_sym = kb
        .try_resolve_symbol("test.wi230.subst_compose.Wi230Outer.T")
        .expect("Outer.T");
    let middle_t_sym = kb
        .try_resolve_symbol("test.wi230.subst_compose.Wi230Middle.T")
        .expect("Middle.T");
    let outer = kb
        .try_resolve_symbol("test.wi230.subst_compose.Wi230Outer")
        .expect("Outer");

    let tree = requires_tree(&mut kb, outer);

    // Helper — find the T-binding value in a spec's SortView. The
    // loader represents a bare name reference as either `Term::Ref(s)`
    // or nullary `Term::Fn(s, [], [])`; both shapes mean "Ref(s)" for
    // substitution purposes.
    fn extract_t_binding(kb: &KnowledgeBase, node: &RequiresNode) -> Option<anthill_core::intern::Symbol> {
        let term = kb.get_term(node.entry.spec);
        let named_args = match term {
            Term::Fn { named_args, .. } => named_args,
            _ => return None,
        };
        for (k, v) in named_args {
            if kb.resolve_sym(*k) != "T" {
                continue;
            }
            match kb.get_term(*v) {
                Term::Ref(s) => return Some(*s),
                Term::Fn { functor, pos_args, named_args }
                    if pos_args.is_empty() && named_args.is_empty() =>
                {
                    return Some(*functor);
                }
                _ => return None,
            }
        }
        None
    }

    // Middle's entry's T-binding should be Ref(Outer.T) — declared
    // directly by Outer's requires clause.
    let middle_node = &tree[0];
    let middle_t = extract_t_binding(&kb, middle_node).expect("Middle's T binding");
    assert_eq!(
        middle_t, outer_t_sym,
        "Middle-node's T should be Outer.T (declared by Outer's requires clause)"
    );

    // Leaf's entry's T-binding should ALSO be Ref(Outer.T) after
    // substitution composition — NOT Ref(Middle.T) (which is what
    // Middle's raw SortRequiresInfo declares).
    let leaf_node = &middle_node.sub_requires[0];
    let leaf_t = extract_t_binding(&kb, leaf_node).expect("Leaf's T binding");
    assert_ne!(
        leaf_t, middle_t_sym,
        "Leaf's T must NOT be Middle.T (would mean no substitution composition)"
    );
    assert_eq!(
        leaf_t, outer_t_sym,
        "Leaf's T must be Outer.T after composition: Outer→Middle→Leaf maps T through to Outer.T"
    );
}

#[test]
fn requires_chain_flatten_matches_required_sorts() {
    // requires_chain (substituted) and flatten_requires_tree(tree) must
    // produce the same sequence of required_sort symbols. The bindings
    // may differ from the pre-WI-230 declared form (substitution is
    // now applied) but the required_sort sequence is invariant.
    let src = r#"
namespace test.wi230.flatten
  export Wi230Outer, Wi230Middle, Wi230Leaf
  sort Wi230Leaf
    sort T = ?
  end
  sort Wi230Middle
    sort T = ?
    requires Wi230Leaf[T = T]
  end
  sort Wi230Outer
    sort T = ?
    requires Wi230Middle[T = T]
  end
end
"#;
    let mut kb = load_with(src);

    let outer = kb
        .try_resolve_symbol("test.wi230.flatten.Wi230Outer")
        .expect("Outer");

    let tree = requires_tree(&mut kb, outer);
    let flat_from_tree: Vec<_> = flatten_requires_tree(&tree)
        .into_iter()
        .map(|e| e.required_sort)
        .collect();
    let flat_via_chain: Vec<RequiresEntry> = requires_chain(&mut kb, outer);
    let flat_chain_sorts: Vec<_> = flat_via_chain.iter().map(|e| e.required_sort).collect();

    assert_eq!(
        flat_from_tree, flat_chain_sorts,
        "flatten_requires_tree(requires_tree(s)) must match requires_chain(s) in required_sort order"
    );

    // Pre-order traversal yields Middle then Leaf for Outer's chain.
    let middle = kb
        .try_resolve_symbol("test.wi230.flatten.Wi230Middle")
        .expect("Middle");
    let leaf = kb
        .try_resolve_symbol("test.wi230.flatten.Wi230Leaf")
        .expect("Leaf");
    assert_eq!(flat_from_tree, vec![middle, leaf]);
}

//! WI-515: the loader no longer asserts a same-functor entity "schema fact".
//!
//! `load_entity` used to assert, per entity, a fact whose head was the
//! entity's own functor with the FIELD TYPES in the data slots —
//! `edge(from: <Node type-term>, to: <Node type-term>)` under sort `Entity`.
//! A fact carrying type terms in data slots unifies with any fully-var query
//! over the constructor: the self-referential constraint
//! `no ?p -: edge(from: ?p, to: ?p)` matched it (`?p = Node` binds
//! consistently because both fields share a type) and was spuriously violated
//! on self-loop-free data, and every var-quantified `resolve` / `KB.execute`
//! pattern query saw a phantom declaration row. The declaration-side record
//! lives in the `entity_field_types` registry + the `EntityInfo` facts; the
//! reflect readers now consume the registry (`read_entity_fields`,
//! `find_entity_schema`), so the same-functor fact is gone.

use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, Var};
use smallvec::SmallVec;

use crate::common::{load_kb_with, try_load_kb_with};

/// `edge` has both fields of the SAME type (`Node`) — the shape whose schema
/// fact used to satisfy a fully-var self-referential pattern.
const GRAPH: &str = r#"
namespace test.wi515
  sort Node
    entity a
    entity b
  end
  sort Rel
    entity edge(from: Node, to: Node)
  end
"#;

/// The ticket's acceptance case: a fully-var self-referential constraint over
/// self-loop-free data HOLDS (it used to be spuriously violated by the schema
/// fact — the only 'self-loop' in the KB was `edge(from: Node, to: Node)`).
#[test]
fn fully_var_self_referential_constraint_holds_without_self_loop() {
    let kb = try_load_kb_with(&format!(
        "{GRAPH}\n  constraint no_self_loop: no ?p -: edge(from: ?p, to: ?p)\n  fact edge(from: a, to: b)\nend\n"
    ))
    .unwrap_or_else(|errs| panic!("self-loop-free data must satisfy the constraint, got: {errs:?}"));
    assert_eq!(kb.guard_count(), 1, "the constraint should register one guard");
}

/// The exclusion half stays honest: a REAL self-loop data fact violates the
/// same constraint and blocks the load.
#[test]
fn fully_var_self_referential_constraint_violated_by_real_self_loop() {
    match try_load_kb_with(&format!(
        "{GRAPH}\n  constraint no_self_loop: no ?p -: edge(from: ?p, to: ?p)\n  fact edge(from: a, to: b)\n  fact edge(from: b, to: b)\nend\n"
    )) {
        Ok(_) => panic!("a real self-loop must violate the constraint, but load succeeded"),
        Err(errs) => assert!(
            errs.iter().any(|e| e.contains("no_self_loop")),
            "the violation should name the constraint, got: {errs:?}"
        ),
    }
}

/// A fully-var query over the constructor returns ONLY data facts — no phantom
/// `edge(from: Node, to: Node)` declaration row (`kb_query_test` documents the
/// workaround this used to force: a concrete discriminator in every query).
#[test]
fn var_query_over_entity_functor_returns_only_data_facts() {
    let mut kb = load_kb_with(&format!("{GRAPH}\n  fact edge(from: a, to: b)\nend\n"));

    let edge = kb
        .try_resolve_symbol("test.wi515.Rel.edge")
        .expect("edge constructor symbol");
    let from_key = kb.intern("from");
    let to_key = kb.intern("to");
    let qa = kb.intern("qa");
    let qb = kb.intern("qb");
    let va = kb.fresh_var(qa);
    let vb = kb.fresh_var(qb);
    let va_t = kb.alloc(Term::Var(Var::Global(va)));
    let vb_t = kb.alloc(Term::Var(Var::Global(vb)));
    let goal = kb.alloc(Term::Fn {
        functor: edge,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(from_key, va_t), (to_key, vb_t)]),
    });

    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert_eq!(
        solutions.len(),
        1,
        "only the data fact edge(a, b) should match a fully-var query"
    );
    // ?from binds to the entity `a` itself — not to the field TYPE `Node`
    // the phantom declaration row used to supply. Compare the bound head
    // symbol structurally (a nullary constructor rides as `Ref`/`Ident`/`Fn`).
    let a_sym = kb
        .try_resolve_symbol("test.wi515.Node.a")
        .expect("entity a symbol");
    let node_sym = kb
        .try_resolve_symbol("test.wi515.Node")
        .expect("Node sort symbol");
    let bound_tid = kb.reify(va_t, &solutions[0].subst).expect_term();
    let bound_sym = match kb.get_term(bound_tid) {
        Term::Ref(s) | Term::Ident(s) => *s,
        Term::Fn { functor, .. } => *functor,
        other => panic!("expected an entity binding for ?from, got {other:?}"),
    };
    assert_ne!(bound_sym, node_sym, "?from must not bind to the field TYPE Node");
    assert_eq!(bound_sym, a_sym, "?from must bind to the entity a");
}

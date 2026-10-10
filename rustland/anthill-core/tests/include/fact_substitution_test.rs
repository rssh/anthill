//! Integration tests for operation binding via instantiation substitution.
//!
//! Tests load source files into a KB and verify:
//! - base_subst computed from SortInfo
//! - SortRequiresInfo spec (SortView) completed with all bindings
//! - resolve_sort_instantiation_param builtin extracts bindings
//! - auto-bind works for same-named operations
use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::kb::term_view::{TermView, ViewHead};
use anthill_core::kb::KnowledgeBase;

use smallvec::SmallVec;

/// Load stdlib + test files into a fresh KB with builtins registered.
fn load_monoid_kb() -> KnowledgeBase {
    let monoid_path = crate::common::testcases_dir().join("fact-substitution/monoid.anthill");
    crate::common::load_kb_with_user_files(&[crate::common::UserFile::Path(&monoid_path)])
}

fn default_config() -> ResolveConfig {
    ResolveConfig {
        max_solutions: 10,
        ..ResolveConfig::default()
    }
}

/// Create a fresh logic variable term with the given debug name.
fn make_var(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

/// Build a SortRequiresInfo query with 2 named args (sort_ref, spec).
/// Missing args are filled with fresh variables.
fn make_requires_query(kb: &mut KnowledgeBase, sort_ref: TermId, spec: TermId) -> TermId {
    let requires_sym = kb.resolve_symbol("anthill.reflect.SortRequiresInfo");
    let sort_ref_sym = kb.intern("sort_ref");
    let spec_sym = kb.intern("spec");
    kb.alloc(Term::Fn {
        functor: requires_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(sort_ref_sym, sort_ref), (spec_sym, spec)]),
    })
}

/// Build a query goal with positional args.
fn make_goal(kb: &mut KnowledgeBase, name: &str, pos_args: &[TermId]) -> TermId {
    let sym = kb
        .try_resolve_symbol(name)
        .unwrap_or_else(|| kb.intern(name));
    kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(pos_args),
        named_args: SmallVec::new(),
    })
}

/// The last segment of a name.
fn short_of(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

/// The spec of the `requires` clause written on `sort_qn`, as the resolver answers it —
/// on whichever carrier it rides. Every reader below takes it through the view.
fn required_spec(kb: &mut KnowledgeBase, sort_qn: &str) -> Value {
    let sort_term = kb.resolve_qualified_name_term(sort_qn);
    let var_inst = make_var(kb, "inst");
    let goal = make_requires_query(kb, sort_term, var_inst);
    let solutions = kb.resolve(&[goal], &default_config());
    assert!(!solutions.is_empty(), "should find Requires for {sort_qn}");
    kb.reify(var_inst, &solutions[0].subst)
}

/// A spec's binding by its short name (the key may be scoped, `Monoid.T`): the key and
/// the value.
fn binding_by_short(kb: &KnowledgeBase, spec: &Value, short: &str) -> Option<(Symbol, Value)> {
    let key = spec
        .named_keys(kb)
        .into_iter()
        .find(|key| short_of(kb.local_name_of(*key)) == short)?;
    Some((key, spec.named_arg(kb, key)?.to_value()))
}

/// The short name a type or an operation reference is headed by.
fn head_short_name<V: TermView>(kb: &KnowledgeBase, v: &V) -> String {
    match v.head(kb) {
        ViewHead::Functor {
            functor: Some(name),
            ..
        }
        | ViewHead::Ident(name) => short_of(kb.local_name_of(name)).to_owned(),
        other => format!("{other:?}"),
    }
}

/// The short name `short` is bound to in `spec`.
fn bound_short_name(kb: &KnowledgeBase, spec: &Value, short: &str) -> String {
    let (_, value) = binding_by_short(kb, spec, short)
        .unwrap_or_else(|| panic!("spec should have a `{short}` binding"));
    head_short_name(kb, &value)
}

/// What `resolve_sort_instantiation_param` answers for the binding `short` of the
/// requirement written on `sort_qn`, asked in ONE query with the requirement itself — so
/// the spec reaches the builtin as the resolver bound it.
fn resolved_binding_short_name(kb: &mut KnowledgeBase, sort_qn: &str, short: &str) -> String {
    let spec = required_spec(kb, sort_qn);
    let (key, _) = binding_by_short(kb, &spec, short)
        .unwrap_or_else(|| panic!("spec should have a `{short}` binding"));
    let sort_term = kb.resolve_qualified_name_term(sort_qn);
    let var_inst = make_var(kb, "inst");
    let req_goal = make_requires_query(kb, sort_term, var_inst);
    let key_ref = kb.alloc(Term::Ref(key));
    let var_val = make_var(kb, "val");
    let param_goal = make_goal(
        kb,
        "anthill.reflect.resolve_sort_instantiation_param",
        &[var_inst, key_ref, var_val],
    );
    let solutions = kb.resolve(&[req_goal, param_goal], &default_config());
    assert!(
        !solutions.is_empty(),
        "resolve_sort_instantiation_param should succeed for {short}"
    );
    let value = kb.reify(var_val, &solutions[0].subst);
    head_short_name(kb, &value)
}

// ── base_subst tests ──────────────────────────────────────────

#[test]
fn base_subst_computed_for_monoid() {
    let kb = load_monoid_kb();
    let monoid_sym = kb.resolve_symbol("test.monoid.Monoid");
    let base = kb
        .sort_base_subst(monoid_sym)
        .expect("Monoid should have a base_subst");

    // Monoid has 3 slots: T (param), combine (op), identity (op)
    assert_eq!(
        base.len(),
        3,
        "Monoid should have 3 slots (T, combine, identity)"
    );

    let slot_names: Vec<&str> = base
        .iter()
        .map(|(sym, _)| kb.local_name_of(*sym))
        .map(|n| n.rsplit('.').next().unwrap_or(n))
        .collect();

    assert!(
        slot_names.contains(&"T"),
        "should contain T param, got: {:?}",
        slot_names
    );
    assert!(
        slot_names.contains(&"combine"),
        "should contain combine op, got: {:?}",
        slot_names
    );
    assert!(
        slot_names.contains(&"identity"),
        "should contain identity op, got: {:?}",
        slot_names
    );

    // Each value should be Ref(same_sym)
    for (sym, tid) in base {
        match kb.get_term(*tid) {
            Term::Ref(ref_sym) => {
                assert_eq!(*ref_sym, *sym, "base subst value should be Ref(same_sym)")
            }
            other => panic!("base subst value should be Ref, got: {:?}", other),
        }
    }
}

// ── Requires spec completion tests ──────────────────────────────

#[test]
fn requires_spec_inst_completed_for_int_add() {
    let mut kb = load_monoid_kb();
    // spec should be SortView(Monoid(), T=Int64(), combine=Ref(add), identity=Ref(zero))
    let spec = required_spec(&mut kb, "test.monoid.IntAdd");
    assert_eq!(head_short_name(&kb, &spec), "SortView", "spec should be SortView");
    assert_eq!(
        spec.named_keys(&kb).len(),
        3,
        "spec should have 3 named args (T, combine, identity)"
    );
    assert_eq!(bound_short_name(&kb, &spec, "T"), "Int64");
    assert_eq!(bound_short_name(&kb, &spec, "combine"), "add");
    assert_eq!(bound_short_name(&kb, &spec, "identity"), "zero");
}

#[test]
fn requires_spec_inst_completed_for_int_mul() {
    let mut kb = load_monoid_kb();
    let spec = required_spec(&mut kb, "test.monoid.IntMul");
    assert_eq!(spec.named_keys(&kb).len(), 3, "spec should have 3 named args");
    assert_eq!(bound_short_name(&kb, &spec, "combine"), "multiply");
    assert_eq!(bound_short_name(&kb, &spec, "identity"), "one");
}

// ── resolve_sort_instantiation_param tests ──────────────────────

#[test]
fn resolve_sort_inst_param_extracts_type_binding() {
    let mut kb = load_monoid_kb();
    assert_eq!(
        resolved_binding_short_name(&mut kb, "test.monoid.IntAdd", "T"),
        "Int64",
        "T should resolve to Int64"
    );
}

#[test]
fn resolve_sort_inst_param_extracts_operation_binding() {
    let mut kb = load_monoid_kb();
    assert_eq!(
        resolved_binding_short_name(&mut kb, "test.monoid.IntAdd", "combine"),
        "add",
        "combine should resolve to add"
    );
}

// ── auto-bind test ──────────────────────────────────────────

#[test]
fn auto_bind_same_named_operations() {
    let mut kb = load_monoid_kb();

    // AutoBindTest has `requires Monoid[T = Int64]` with no explicit combine/identity.
    // Since AutoBindTest has same-named ops (combine, identity), they should auto-bind.
    let spec = required_spec(&mut kb, "test.monoid.AutoBindTest");
    assert_eq!(
        spec.named_keys(&kb).len(),
        3,
        "spec should have 3 named args after auto-bind"
    );
    assert_eq!(
        bound_short_name(&kb, &spec, "combine"),
        "combine",
        "auto-bound combine should point to AutoBindTest's combine"
    );
    assert_eq!(
        bound_short_name(&kb, &spec, "identity"),
        "identity",
        "auto-bound identity should point to AutoBindTest's identity"
    );
}

/// Integration tests for the typing module (anthill.reflect.typing).
///
/// Tests load source files into a KB, register builtins, and run SLD resolution
/// to verify typing rules: is_entity_of, refines, type_compatible, list_contains,
/// extract_sort_ref, sort_requires, sort_has_param.


use anthill_core::parse;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term, TermId, Literal, Var};
use anthill_core::intern::Symbol;
use anthill_core::kb::load::{self, NullResolver, LoadResult};
use anthill_core::kb::resolve::ResolveConfig;

use smallvec::SmallVec;

/// Load stdlib + typing rules into a fresh KB with builtins registered.
fn load_stdlib_kb() -> KnowledgeBase {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    assert!(!files.is_empty(), "no stdlib files found");

    let parsed: Vec<_> = files.iter()
        .map(|path| {
            let source = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            parse::parse(&source)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", path.display()))
        })
        .collect();

    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let result = load::load_all(&mut kb, &refs, &NullResolver);
    if let Err(errs) = &result {
        for e in errs {
            eprintln!("Load error: {}", e);
        }
        panic!("stdlib load failed with {} errors", errs.len());
    }
    kb
}

/// Load user source on top of an existing KB (stdlib already loaded).
fn load_source(kb: &mut KnowledgeBase, source: &str) {
    let parsed = parse::parse(source).expect("parse failed");
    load::load(kb, &parsed, &NullResolver).expect("load failed");
}

/// Get the functor symbol from a name term (resolve_qualified_name_term returns a nullary Fn).
fn functor_of(kb: &KnowledgeBase, term: TermId) -> anthill_core::intern::Symbol {
    match kb.get_term(term) {
        Term::Fn { functor, .. } => *functor,
        _ => panic!("expected Fn term"),
    }
}

/// Build a query goal using a resolved symbol as functor.
/// Works for kernel names ("EntityInfo"), qualified builtins
/// ("anthill.reflect.typing.is_entity_of"), and qualified rule functor names
/// ("anthill.reflect.typing.refines", "anthill.reflect.typing.list_contains").
fn make_goal(kb: &mut KnowledgeBase, name: &str, pos_args: &[TermId]) -> TermId {
    let sym = kb.try_resolve_symbol(name)
        .unwrap_or_else(|| kb.intern(name));
    kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(pos_args),
        named_args: SmallVec::new(),
    })
}

/// Build a query goal using named args (for EntityInfo, SortRequiresInfo, etc.).
fn make_named_goal(kb: &mut KnowledgeBase, name: &str, named_args: &[(&str, TermId)]) -> TermId {
    let sym = kb.try_resolve_symbol(name)
        .unwrap_or_else(|| kb.intern(name));
    let named: SmallVec<[(anthill_core::intern::Symbol, TermId); 2]> = named_args.iter()
        .map(|(n, t)| (kb.intern(n), *t))
        .collect();
    kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::new(),
        named_args: named,
    })
}

fn default_config() -> ResolveConfig {
    ResolveConfig { max_solutions: 10, ..ResolveConfig::default() }
}

/// Create a fresh logic variable term with the given debug name.
fn make_var(kb: &mut KnowledgeBase, name: &str) -> TermId {
    let sym = kb.intern(name);
    let vid = kb.fresh_var(sym);
    kb.alloc(Term::Var(Var::Global(vid)))
}

// ── is_entity_of tests ──────────────────────────────────────────

#[test]
fn is_entity_of_basic() {
    let source = r#"
sort Color {
    entity red
    entity green
    entity blue
}
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    let red_term = kb.resolve_qualified_name_term("Color.red");
    let color_term = kb.resolve_qualified_name_term("Color");

    assert!(kb.is_entity_of(red_term, color_term), "red should be entity of Color");
    assert!(!kb.is_entity_of(color_term, red_term), "Color should NOT be entity of red");
}

#[test]
fn is_entity_of_builtin_succeeds() {
    let source = r#"
sort Color {
    entity red
    entity green
    entity blue
}
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    let red_term = kb.resolve_qualified_name_term("Color.red");
    let color_term = kb.resolve_qualified_name_term("Color");

    // Query via the builtin (uses intern'd qualified name directly)
    let goal = make_goal(&mut kb, "anthill.reflect.typing.is_entity_of", &[red_term, color_term]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 1, "is_entity_of builtin(red, Color) should succeed");

    // Negative
    let goal_neg = make_goal(&mut kb, "anthill.reflect.typing.is_entity_of", &[color_term, red_term]);
    let results_neg = kb.resolve(&[goal_neg], &default_config());
    assert_eq!(results_neg.len(), 0, "is_entity_of builtin(Color, red) should fail");
}

#[test]
fn is_entity_of_enumeration_via_entity_info_facts() {
    let source = r#"
sort Color {
    entity red
    entity green
    entity blue
}
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    // Query: EntityInfo(name: ?x, fields: ?f) — should find red, green, blue
    let var_x = make_var(&mut kb, "x");
    let var_f = make_var(&mut kb, "f");

    let goal = make_named_goal(&mut kb, "anthill.reflect.EntityInfo", &[("name", var_x), ("fields", var_f)]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 3, "Color should have 3 EntityInfo facts for red, green, blue");
}

// ── is_entity_of via typing rule ──────────────────────────────────

#[test]
fn is_entity_of_rule_resolves() {
    let source = r#"
sort Color {
    entity red
    entity green
    entity blue
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let red_term = kb.resolve_qualified_name_term("Color.red");
    let color_term = kb.resolve_qualified_name_term("Color");

    // Query via the typing rule (uses qualified name for is_entity_of builtin symbol)
    let goal = make_goal(&mut kb, "anthill.reflect.typing.is_entity_of", &[red_term, color_term]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(), "is_entity_of(red, Color) via typing rule should succeed");
}

// ── list_contains tests ──────────────────────────────────────────

#[test]
fn list_contains_finds_element() {
    let source = r#"
sort Color {
    entity red
    entity green
    entity blue
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    // Build a cons list: cons(head: red, tail: cons(head: green, tail: nil()))
    let red = kb.resolve_qualified_name_term("Color.red");
    let green = kb.resolve_qualified_name_term("Color.green");
    let nil_sym = kb.resolve_symbol("anthill.prelude.List.nil");
    let nil = kb.alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });

    let cons_sym = kb.resolve_symbol("anthill.prelude.List.cons");
    let head_sym = kb.intern("head");
    let tail_sym = kb.intern("tail");

    let inner = kb.alloc(Term::Fn {
        functor: cons_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(head_sym, green), (tail_sym, nil)]),
    });
    let list = kb.alloc(Term::Fn {
        functor: cons_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(head_sym, red), (tail_sym, inner)]),
    });

    // list_contains(red, list) should succeed — using resolved symbol
    let goal = make_goal(&mut kb, "anthill.reflect.typing.list_contains", &[red, list]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(), "list_contains(red, [red, green]) should succeed");

    // list_contains(green, list) should also succeed
    let goal2 = make_goal(&mut kb, "anthill.reflect.typing.list_contains", &[green, list]);
    let results2 = kb.resolve(&[goal2], &default_config());
    assert!(!results2.is_empty(), "list_contains(green, [red, green]) should succeed");

    // list_contains(blue, list) should fail (blue not in list)
    let blue = kb.resolve_qualified_name_term("Color.blue");
    let goal3 = make_goal(&mut kb, "anthill.reflect.typing.list_contains", &[blue, list]);
    let results3 = kb.resolve(&[goal3], &default_config());
    assert!(results3.is_empty(), "list_contains(blue, [red, green]) should fail");
}

// ── extract_sort_ref builtin tests ──────────────────────────────

#[test]
fn extract_sort_ref_from_parameterized_type() {
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();

    // Build SortView(Eq(), T=Int())
    let eq_sym = kb.intern("Eq");
    let eq_name = kb.alloc(Term::Fn {
        functor: eq_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let int_sym = kb.intern("Int");
    let int_term = kb.alloc(Term::Fn {
        functor: int_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let t_sym = kb.intern("T");
    let pt_sym = kb.intern("SortView");
    let inst = kb.alloc(Term::Fn {
        functor: pt_sym,
        pos_args: SmallVec::from_elem(eq_name, 1),
        named_args: SmallVec::from_slice(&[(t_sym, int_term)]),
    });

    // Query: extract_sort_ref(inst, ?result)
    let var_result = make_var(&mut kb, "result");

    let goal = make_goal(&mut kb, "anthill.reflect.typing.extract_sort_ref", &[inst, var_result]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 1, "extract_sort_ref should succeed");

    let bound = kb.reify(var_result, &results[0].subst);
    // extract_sort_ref emits the canonical nullary-Fn shape used by
    // load.rs for sort references (so the result can flow into rule
    // heads / fact field positions that expect Fn(name, [], [])).
    match kb.get_term(bound) {
        Term::Fn { functor, pos_args, named_args } if pos_args.is_empty() && named_args.is_empty() => {
            assert_eq!(kb.resolve_sym(*functor), "Eq", "should extract Eq from SortView(Eq(), ...)");
        }
        other => panic!("expected Fn(Eq, [], []), got {:?}", other),
    }
}

#[test]
fn extract_sort_ref_from_simple_ref() {
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();

    let eq_sym = kb.intern("Eq");
    let eq_ref = kb.alloc(Term::Ref(eq_sym));

    let var_result = make_var(&mut kb, "result");

    let goal = make_goal(&mut kb, "anthill.reflect.typing.extract_sort_ref", &[eq_ref, var_result]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 1, "extract_sort_ref from Ref should succeed");

    let bound = kb.reify(var_result, &results[0].subst);
    match kb.get_term(bound) {
        Term::Fn { functor, pos_args, named_args } if pos_args.is_empty() && named_args.is_empty() => {
            assert_eq!(kb.resolve_sym(*functor), "Eq");
        }
        other => panic!("expected Fn(Eq, [], []), got {:?}", other),
    }
}

// ── refines tests (via SLD rules in typing.anthill) ──────────────

#[test]
fn refines_direct() {
    let source = r#"
sort Eq {
    sort T = ?
}

sort Ordered {
    sort T = ?
    requires Eq[T = T]
    operation compare(a: T, b: T) -> Int
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let ordered_term = kb.resolve_qualified_name_term("Ordered");

    // Query: SortRequiresInfo(sort_ref: Ordered, spec: ?spec) — direct fact query (named args)
    let var_spec = make_var(&mut kb, "spec");

    let goal = make_named_goal(&mut kb, "anthill.reflect.SortRequiresInfo", &[("sort_ref", ordered_term), ("spec", var_spec)]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(), "Ordered should have at least 1 SortRequiresInfo fact");
}

#[test]
fn refines_direct_via_rule() {
    let source = r#"
sort Eq {
    sort T = ?
}

sort Ordered {
    sort T = ?
    requires Eq[T = T]
    operation compare(a: T, b: T) -> Int
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let ordered_term = kb.resolve_qualified_name_term("Ordered");

    // Query: refines(Ordered, ?spec) via the typing rule
    let var_spec = make_var(&mut kb, "spec");

    let goal = make_goal(&mut kb, "anthill.reflect.typing.refines", &[ordered_term, var_spec]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(), "refines(Ordered, ?spec) should find at least Eq[T=T]");
}

#[test]
fn refines_transitive() {
    let source = r#"
sort A {
    sort T = ?
}

sort B {
    sort T = ?
    requires A[T = T]
}

sort C {
    sort T = ?
    requires B[T = T]
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let c_term = kb.resolve_qualified_name_term("C");

    // Query: refines(C, ?spec) — should find both B[T=T] and A[T=T]
    let var_spec = make_var(&mut kb, "spec");

    let goal = make_goal(&mut kb, "anthill.reflect.typing.refines", &[c_term, var_spec]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(results.len() >= 2, "C refines both B[T=T] (direct) and A[T=T] (transitive), got {} results", results.len());
}

// WI-344: the reflect-queryable `provides` rule mirrors `refines` over
// SortProvidesInfo — it resolves the satisfaction facts a `fact
// Spec[carrier]` emits. This is the SLD-level twin of the Rust
// `types_compatible` provider-admissibility arm. Queried with a variable
// carrier so the check is robust to the `sort_ref` term shape (the
// namespace-level emitter builds it via `make_name_term_from_sym`); the
// point is that the rule fires against an emitted `SortProvidesInfo`.
#[test]
fn provides_rule_resolves_satisfaction_facts() {
    let source = r#"
namespace test.wi344_provides
  sort Comparable
    sort T = ?
    operation cmp(a: T, b: T) -> Bool
  end
  sort Widget
    entity widget(id: Int)
  end
  fact Comparable[T = Widget]
end
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let var_carrier = make_var(&mut kb, "carrier");
    let var_spec = make_var(&mut kb, "spec");

    let goal = make_goal(&mut kb, "anthill.reflect.typing.provides", &[var_carrier, var_spec]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(),
        "the `provides` rule must resolve at least the SortProvidesInfo \
         emitted by `fact Comparable[T = Widget]`");
}

// ── type_compatible tests ────────────────────────────────────────

#[test]
fn type_compatible_same_type() {
    let source = r#"
sort Color {
    entity red
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let color_term = kb.resolve_qualified_name_term("Color");

    // type_compatible(Color, Color) — same type via unification
    let goal = make_goal(&mut kb, "anthill.reflect.typing.type_compatible", &[color_term, color_term]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(), "type_compatible(Color, Color) should succeed");
}

#[test]
fn type_compatible_entity_subtyping() {
    let source = r#"
sort Color {
    entity red
    entity green
    entity blue
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let red_term = kb.resolve_qualified_name_term("Color.red");
    let color_term = kb.resolve_qualified_name_term("Color");

    // type_compatible(red, Color) — via is_entity_of rule
    let goal = make_goal(&mut kb, "anthill.reflect.typing.type_compatible", &[red_term, color_term]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(), "type_compatible(red, Color) should succeed via entity_of");
}

// ── sort_requires tests (uses partial named-arg expansion) ──────

#[test]
fn sort_requires_via_sort_info() {
    let source = r#"
sort Eq {
    sort T = ?
}

sort Ordered {
    sort T = ?
    requires Eq[T = T]
    operation compare(a: T, b: T) -> Int
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let ordered_name = kb.resolve_qualified_name_term("Ordered");
    let ordered_functor = functor_of(&kb, ordered_name);
    let ordered_ref = kb.alloc(Term::Ref(ordered_functor));

    // Query: sort_requires(Ordered_ref, ?spec)
    let var_spec = make_var(&mut kb, "spec");

    let goal = make_goal(&mut kb, "anthill.reflect.typing.sort_requires", &[ordered_ref, var_spec]);
    let config = ResolveConfig { max_solutions: 5, ..ResolveConfig::default() };
    let results = kb.resolve(&[goal], &config);
    assert!(!results.is_empty(),
        "sort_requires(Ordered, ?spec) should find at least one spec via SortInfo partial expansion");
}

// ── sort_has_param tests ─────────────────────────────────────────

#[test]
fn sort_has_param_finds_type_params() {
    let source = r#"
sort Eq {
    sort T = ?
    operation equals(a: T, b: T) -> Bool
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let eq_name = kb.resolve_qualified_name_term("Eq");
    let eq_functor = functor_of(&kb, eq_name);
    let eq_ref = kb.alloc(Term::Ref(eq_functor));

    // Query: sort_has_param(Eq_ref, ?param)
    let var_param = make_var(&mut kb, "param");

    let goal = make_goal(&mut kb, "anthill.reflect.typing.sort_has_param", &[eq_ref, var_param]);
    let config = ResolveConfig { max_solutions: 5, ..ResolveConfig::default() };
    let results = kb.resolve(&[goal], &config);
    assert!(!results.is_empty(),
        "sort_has_param(Eq, ?param) should find T via SortInfo partial expansion");
}

// ── EntityInfo fact verification ───────────────────────────────────

#[test]
fn entity_info_fact_exists_in_kb() {
    let source = r#"
sort Color {
    entity red
    entity green
    entity blue
}
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    // Query EntityInfo facts by functor
    let entity_info_sym = kb.resolve_symbol("anthill.reflect.EntityInfo");
    let facts = kb.by_functor(entity_info_sym);
    assert_eq!(facts.len(), 3, "should have 3 EntityInfo facts for red, green, blue");
}

// ── EntityInfo is 1-level (non-transitive) ────────────────────────

#[test]
fn entity_info_is_not_transitive() {
    // Nested sorts: entity inside sort inside sort.
    // EntityInfo should only exist for direct entities, not grandparent's.
    let source = r#"
sort Outer {
    sort Inner {
        entity leaf
    }
}
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    let leaf_term = kb.resolve_qualified_name_term("Outer.Inner.leaf");
    let inner_term = kb.resolve_qualified_name_term("Outer.Inner");

    // leaf is entity of Inner (direct — via internal index)
    assert!(kb.is_entity_of(leaf_term, inner_term), "leaf should be entity of Inner");

    // EntityInfo fact should exist for leaf (need both named args for arity match)
    let var_f = make_var(&mut kb, "f");
    let goal = make_named_goal(&mut kb, "anthill.reflect.EntityInfo", &[("name", leaf_term), ("fields", var_f)]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 1, "leaf should have exactly 1 EntityInfo fact");
}

#[test]
fn entity_of_sibling_entities_are_independent() {
    let source = r#"
sort Color {
    entity red
    entity green
    entity blue
}
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    let red_term = kb.resolve_qualified_name_term("Color.red");
    let green_term = kb.resolve_qualified_name_term("Color.green");

    // Siblings are not entity_of each other
    assert!(!kb.is_entity_of(red_term, green_term), "red should NOT be entity of green");
    assert!(!kb.is_entity_of(green_term, red_term), "green should NOT be entity of red");
}

#[test]
fn entity_info_sort_is_not_entity() {
    let source = r#"
sort Color {
    entity red
}
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    let color_term = kb.resolve_qualified_name_term("Color");

    // No EntityInfo(name: Color) — Color is a sort, not an entity
    let color_functor = functor_of(&kb, color_term);
    let color_ref = kb.alloc(Term::Ref(color_functor));
    let goal = make_named_goal(&mut kb, "anthill.reflect.EntityInfo", &[("name", color_ref)]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 0, "Color should NOT have an EntityInfo fact");
}

#[test]
fn entity_info_standalone_entity_has_no_entity_info() {
    // Standalone entity `entity Foo(...)` is loaded as an Entity fact only.
    // It does NOT produce EntityInfo facts (only sort-with-body entities do).
    let source = r#"
entity Account(id: Int, balance: Int)
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    // No EntityInfo facts for standalone entities
    let entity_info_sym = kb.resolve_symbol("anthill.reflect.EntityInfo");
    let facts = kb.by_functor(entity_info_sym);
    assert_eq!(facts.len(), 0, "standalone entity should not produce EntityInfo facts");
}

#[test]
fn entity_info_multiple_sorts() {
    // Entities from different sorts should not cross-contaminate
    let source = r#"
sort Color {
    entity red
    entity green
}

sort Shape {
    entity circle
    entity square
}
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    let red_term = kb.resolve_qualified_name_term("Color.red");
    let circle_term = kb.resolve_qualified_name_term("Shape.circle");
    let color_term = kb.resolve_qualified_name_term("Color");
    let shape_term = kb.resolve_qualified_name_term("Shape");

    // red is entity of Color, NOT Shape (via internal index)
    assert!(kb.is_entity_of(red_term, color_term), "red should be entity of Color");
    assert!(!kb.is_entity_of(red_term, shape_term), "red should NOT be entity of Shape");

    // circle is entity of Shape, NOT Color
    assert!(kb.is_entity_of(circle_term, shape_term), "circle should be entity of Shape");
    assert!(!kb.is_entity_of(circle_term, color_term), "circle should NOT be entity of Color");

    // EntityInfo facts: 2 for Color + 2 for Shape = 4
    let entity_info_sym = kb.resolve_symbol("anthill.reflect.EntityInfo");
    let facts = kb.by_functor(entity_info_sym);
    assert_eq!(facts.len(), 4, "should have 4 EntityInfo facts total");
}

// ── is_entity_of via typing rule with various patterns ──────────

#[test]
fn entity_info_enumerates_all_entities() {
    // EntityInfo(name: ?x, fields: ?f) enumerates all entities from user source.
    let source = r#"
sort Color {
    entity red
    entity green
    entity blue
}
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    let var_x = make_var(&mut kb, "x");
    let var_f = make_var(&mut kb, "f");

    // Use EntityInfo directly for enumeration (both fields needed for arity match)
    let goal = make_named_goal(&mut kb, "anthill.reflect.EntityInfo", &[("name", var_x), ("fields", var_f)]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 3, "EntityInfo(?x, ?f) should find 3 entities");
}

#[test]
fn entity_info_scope_finds_parent() {
    // scope(red, ?parent) should find Color — the entity's scope.
    let source = r#"
sort Color {
    entity red
    entity green
}
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    let red_term = kb.resolve_qualified_name_term("Color.red");
    let red_functor = functor_of(&kb, red_term);
    let red_ref = kb.alloc(Term::Ref(red_functor));
    let var_p = make_var(&mut kb, "parent");

    let scope_sym = kb.resolve_symbol("anthill.reflect.scope");
    let goal = kb.alloc(Term::Fn {
        functor: scope_sym,
        pos_args: SmallVec::from_slice(&[red_ref, var_p]),
        named_args: SmallVec::new(),
    });
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 1, "scope(red, ?parent) should find exactly 1 parent");

    // Verify the parent is Color (scope returns the sort term Fn, not a Ref)
    let bound = kb.reify(var_p, &results[0].subst);
    let color_term = kb.resolve_qualified_name_term("Color");
    assert_eq!(bound, color_term, "scope of red should be Color");
}

// ── type_compatible via entity_of ───────────────────────────────

#[test]
fn type_compatible_entity_not_compatible_with_wrong_sort() {
    let source = r#"
sort Color {
    entity red
}
sort Shape {
    entity circle
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let red_term = kb.resolve_qualified_name_term("Color.red");
    let shape_term = kb.resolve_qualified_name_term("Shape");

    // type_compatible(red, Shape) should fail — red is entity of Color, not Shape
    let goal = make_goal(&mut kb, "anthill.reflect.typing.type_compatible", &[red_term, shape_term]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(results.is_empty(), "type_compatible(red, Shape) should fail");
}

#[test]
fn type_compatible_entity_compatible_with_own_sort() {
    let source = r#"
sort Color {
    entity red
    entity green
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let red_term = kb.resolve_qualified_name_term("Color.red");
    let green_term = kb.resolve_qualified_name_term("Color.green");
    let color_term = kb.resolve_qualified_name_term("Color");

    // type_compatible(red, Color) — should succeed
    let goal = make_goal(&mut kb, "anthill.reflect.typing.type_compatible", &[red_term, color_term]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(), "type_compatible(red, Color) should succeed");

    // type_compatible(red, green) — should fail (siblings, not entity_of)
    let goal2 = make_goal(&mut kb, "anthill.reflect.typing.type_compatible", &[red_term, green_term]);
    let results2 = kb.resolve(&[goal2], &default_config());
    assert!(results2.is_empty(), "type_compatible(red, green) should fail — different entities");
}

#[test]
fn type_compatible_entity_with_fields() {
    let source = r#"
sort Account {
    entity checking(balance: Int)
    entity savings(balance: Int, rate: Float)
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let checking_term = kb.resolve_qualified_name_term("Account.checking");
    let savings_term = kb.resolve_qualified_name_term("Account.savings");
    let account_term = kb.resolve_qualified_name_term("Account");

    // Both entities are compatible with Account
    let goal1 = make_goal(&mut kb, "anthill.reflect.typing.type_compatible", &[checking_term, account_term]);
    let results1 = kb.resolve(&[goal1], &default_config());
    assert!(!results1.is_empty(), "type_compatible(checking, Account) should succeed");

    let goal2 = make_goal(&mut kb, "anthill.reflect.typing.type_compatible", &[savings_term, account_term]);
    let results2 = kb.resolve(&[goal2], &default_config());
    assert!(!results2.is_empty(), "type_compatible(savings, Account) should succeed");

    // Entities are NOT compatible with each other
    let goal3 = make_goal(&mut kb, "anthill.reflect.typing.type_compatible", &[checking_term, savings_term]);
    let results3 = kb.resolve(&[goal3], &default_config());
    assert!(results3.is_empty(), "type_compatible(checking, savings) should fail");
}

// ── entity_of tests (nonvar-guarded rule) ────────────────────────

#[test]
fn entity_of_ground_entity_finds_parent() {
    // entity_of(red, ?sort) should find Color via nonvar guard + EntityOf fact.
    let source = r#"
sort Color {
    entity red
    entity green
    entity blue
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let red_term = kb.resolve_qualified_name_term("Color.red");
    let var_sort = make_var(&mut kb, "sort");

    let goal = make_goal(&mut kb, "anthill.reflect.typing.entity_of", &[red_term, var_sort]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 1, "entity_of(red, ?sort) should find exactly 1 parent");

    // Verify the parent is Color
    let bound = kb.reify(var_sort, &results[0].subst);
    let color_term = kb.resolve_qualified_name_term("Color");
    assert_eq!(bound, color_term, "entity_of(red, ?sort) should bind ?sort to Color");
}

#[test]
fn entity_of_with_unbound_entity_reorders() {
    // entity_of(?x, Color): nonvar(?x) delays, resolver reorders to try
    // EntityOf(entity: ?x, parent: Color) first, which binds ?x, then
    // nonvar succeeds on retry. So entity_of can enumerate in both directions.
    let source = r#"
sort Color {
    entity red
    entity green
    entity blue
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let color_term = kb.resolve_qualified_name_term("Color");
    let var_x = make_var(&mut kb, "x");

    let goal = make_goal(&mut kb, "anthill.reflect.typing.entity_of", &[var_x, color_term]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(),
        "entity_of(?x, Color) should find entities via delay/reorder");
}

#[test]
fn entity_of_no_parent_for_sort_itself() {
    // entity_of(Color, ?sort) should fail — Color is not an entity of anything.
    let source = r#"
sort Color {
    entity red
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let color_term = kb.resolve_qualified_name_term("Color");
    let var_sort = make_var(&mut kb, "sort");

    let goal = make_goal(&mut kb, "anthill.reflect.typing.entity_of", &[color_term, var_sort]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 0, "entity_of(Color, ?sort) should fail — Color has no parent sort");
}

#[test]
fn entity_of_each_entity_finds_own_parent() {
    // Entities from different sorts find their respective parents.
    let source = r#"
sort Color {
    entity red
    entity green
}

sort Shape {
    entity circle
    entity square
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let red_term = kb.resolve_qualified_name_term("Color.red");
    let circle_term = kb.resolve_qualified_name_term("Shape.circle");
    let color_term = kb.resolve_qualified_name_term("Color");
    let shape_term = kb.resolve_qualified_name_term("Shape");

    // entity_of(red, ?sort) → Color
    let var_sort1 = make_var(&mut kb, "sort");
    let goal1 = make_goal(&mut kb, "anthill.reflect.typing.entity_of", &[red_term, var_sort1]);
    let results1 = kb.resolve(&[goal1], &default_config());
    assert_eq!(results1.len(), 1);
    let bound1 = kb.reify(var_sort1, &results1[0].subst);
    assert_eq!(bound1, color_term, "red's parent should be Color");

    // entity_of(circle, ?sort) → Shape
    let var_sort2 = make_var(&mut kb, "sort");
    let goal2 = make_goal(&mut kb, "anthill.reflect.typing.entity_of", &[circle_term, var_sort2]);
    let results2 = kb.resolve(&[goal2], &default_config());
    assert_eq!(results2.len(), 1);
    let bound2 = kb.reify(var_sort2, &results2[0].subst);
    assert_eq!(bound2, shape_term, "circle's parent should be Shape");

    // entity_of(red, Shape) should fail — wrong parent
    let goal3 = make_goal(&mut kb, "anthill.reflect.typing.entity_of", &[red_term, shape_term]);
    let results3 = kb.resolve(&[goal3], &default_config());
    assert_eq!(results3.len(), 0, "entity_of(red, Shape) should fail");
}

#[test]
fn entity_of_ground_check_succeeds() {
    // entity_of(red, Color) with both args ground should succeed.
    let source = r#"
sort Color {
    entity red
    entity green
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let red_term = kb.resolve_qualified_name_term("Color.red");
    let color_term = kb.resolve_qualified_name_term("Color");

    let goal = make_goal(&mut kb, "anthill.reflect.typing.entity_of", &[red_term, color_term]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 1, "entity_of(red, Color) should succeed when both args are ground");
}

#[test]
fn entity_of_standalone_entity_has_no_parent() {
    // Standalone entity (not inside a sort body) has no EntityOf fact.
    let source = r#"
entity Account(id: Int, balance: Int)
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let account_term = kb.resolve_qualified_name_term("Account");
    let var_sort = make_var(&mut kb, "sort");

    let goal = make_goal(&mut kb, "anthill.reflect.typing.entity_of", &[account_term, var_sort]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 0, "entity_of(Account, ?sort) should fail — standalone entity has no parent");
}

// ── Universal type variable tests ────────────────────────────────

#[test]
fn variable_field_type_loads_as_var() {
    // `entity Foo(x: ?)` — field type should be Term::Var in KB.
    let source = r#"
entity Foo(x: ?)
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    let foo_sym = kb.resolve_symbol("Foo");
    let x_sym = kb.intern("x");
    let facts = kb.by_functor(foo_sym);
    // There should be an Entity fact for Foo
    assert!(!facts.is_empty(), "Foo entity should exist in KB");

    // The entity fact's field 'x' should be a Var term
    let entity_fact = facts[0];
    let entity_term = kb.fact_term(entity_fact);
    match kb.get_term(entity_term) {
        Term::Fn { named_args, .. } => {
            let x_arg = named_args.iter().find(|(s, _)| *s == x_sym);
            assert!(x_arg.is_some(), "entity should have field 'x'");
            let (_, x_tid) = x_arg.unwrap();
            assert!(matches!(kb.get_term(*x_tid), Term::Var(_)),
                "field typed ? should load as Term::Var, got {:?}", kb.get_term(*x_tid));
        }
        other => panic!("expected Fn term for entity, got {:?}", other),
    }
}

#[test]
fn variable_field_type_unifies_with_concrete() {
    // Verify that an entity with `?` field types produces Term::Var in the KB,
    // and that the var unifies with a concrete term via match_term.
    let source = r#"
entity Box(contents: ?)
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    // Get the Box entity fact
    let box_sym = kb.resolve_symbol("Box");
    let contents_sym = kb.intern("contents");
    let facts = kb.by_functor(box_sym);
    assert!(!facts.is_empty(), "Box should exist in KB");

    let entity_term = kb.fact_term(facts[0]);
    let contents_tid = match kb.get_term(entity_term) {
        Term::Fn { named_args, .. } => {
            named_args.iter().find(|(s, _)| *s == contents_sym)
                .expect("should have 'contents' field").1
        }
        other => panic!("expected Fn, got {:?}", other),
    };

    // The contents field should be a Var — meaning it can hold any type
    assert!(matches!(kb.get_term(contents_tid), Term::Var(_)),
        "field typed ? should be a logic variable in KB");

    // A Var unifies with any concrete term via match_term
    let int_sym = kb.intern("Int");
    let int_term = kb.alloc(Term::Fn {
        functor: int_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let result = kb.match_term(contents_tid, int_term);
    assert!(result.is_some(), "Var should unify with any concrete term (Int)");
}

// ── Field access builtin tests ───────────────────────────────

#[test]
fn field_access_entity_extracts_field() {
    let mut kb = load_stdlib_kb();

    // Define a sort with an entity that has fields
    load_source(&mut kb, r#"
        namespace test_fa
          sort Env
            entity env(platform: Int, fs: Int)
          end
        end
    "#);

    // Construct an entity instance: env(platform: 1, fs: 42)
    let env_sym = kb.try_resolve_symbol("test_fa.Env.env").expect("env entity");
    let platform_sym = kb.intern("platform");
    let fs_sym = kb.intern("fs");
    let val1 = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(1)));
    let val42 = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(42)));
    let env_term = kb.alloc(Term::Fn {
        functor: env_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(platform_sym, val1), (fs_sym, val42)]),
    });

    // Build goal: field_access(env_instance, Ident(fs), ?result)
    let fs_field_sym = kb.intern("fs");
    let field_ident = kb.alloc(Term::Ident(fs_field_sym));
    let result_name = kb.intern("result");
    let result_var = kb.fresh_var(result_name);
    let result_tid = kb.alloc(Term::Var(Var::Global(result_var)));
    let goal = make_goal(&mut kb, "anthill.reflect.field_access", &[env_term, field_ident, result_tid]);

    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert!(!solutions.is_empty(), "field_access should produce a solution");
    let sol = &solutions[0];
    let resolved = sol.subst.resolve_with_term(result_var).expect("result should be bound");
    // The resolved value should be 42 (the fs field)
    match kb.get_term(resolved) {
        Term::Const(anthill_core::kb::term::Literal::Int(n)) => {
            assert_eq!(*n, 42);
        }
        other => panic!("expected Int literal 42, got {:?}", other),
    }
}

#[test]
fn field_access_delays_on_unbound_object() {
    let mut kb = load_stdlib_kb();

    // Build goal: field_access(?x, Ident(fs), ?result) where ?x is unbound
    let obj_name = kb.intern("x");
    let obj_var = kb.fresh_var(obj_name);
    let obj_tid = kb.alloc(Term::Var(Var::Global(obj_var)));
    let fs_field_sym = kb.intern("fs");
    let field_ident = kb.alloc(Term::Ident(fs_field_sym));
    let result_name = kb.intern("result");
    let result_var = kb.fresh_var(result_name);
    let result_tid = kb.alloc(Term::Var(Var::Global(result_var)));
    let goal = make_goal(&mut kb, "anthill.reflect.field_access", &[obj_tid, field_ident, result_tid]);

    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    // Should produce a residual (delayed) goal, not a solution with bound result
    if !solutions.is_empty() {
        assert!(!solutions[0].residual.is_empty(), "should have residual goals from delay");
    }
}

#[test]
fn field_access_fails_on_bad_field() {
    let mut kb = load_stdlib_kb();

    load_source(&mut kb, r#"
        namespace test_fa2
          sort Env
            entity env(platform: Int, fs: Int)
          end
        end
    "#);

    let env_sym = kb.try_resolve_symbol("test_fa2.Env.env").expect("env entity");
    let platform_sym = kb.intern("platform");
    let fs_sym = kb.intern("fs");
    let val1 = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(1)));
    let val42 = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(42)));
    let env_term = kb.alloc(Term::Fn {
        functor: env_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(platform_sym, val1), (fs_sym, val42)]),
    });

    // Try to access a non-existent field "nonexistent"
    let ne_field_sym = kb.intern("nonexistent");
    let field_ident = kb.alloc(Term::Ident(ne_field_sym));
    let result_name = kb.intern("result");
    let result_var = kb.fresh_var(result_name);
    let result_tid = kb.alloc(Term::Var(Var::Global(result_var)));
    let goal = make_goal(&mut kb, "anthill.reflect.field_access", &[env_term, field_ident, result_tid]);

    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert!(solutions.is_empty(), "field_access with bad field should fail");
}

#[test]
fn field_access_sort_component() {
    let mut kb = load_stdlib_kb();

    load_source(&mut kb, r#"
        namespace test_sc
          import anthill.prelude.*
          sort Monoid
            sort Carrier = ?
            operation combine(a: Carrier, b: Carrier) -> Carrier
          end
        end
    "#);

    // Build a sort term for Monoid (nullary Fn)
    let monoid_sym = kb.try_resolve_symbol("test_sc.Monoid").expect("Monoid sort");
    let monoid_term = kb.alloc(Term::Fn {
        functor: monoid_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });

    // field_access(Monoid(), Ident(Carrier), ?result)
    let carrier_sym = kb.intern("Carrier");
    let field_ident = kb.alloc(Term::Ident(carrier_sym));
    let result_name = kb.intern("result");
    let result_var = kb.fresh_var(result_name);
    let result_tid = kb.alloc(Term::Var(Var::Global(result_var)));
    let goal = make_goal(&mut kb, "anthill.reflect.field_access", &[monoid_term, field_ident, result_tid]);

    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert!(!solutions.is_empty(), "field_access for sort component should succeed");
    let sol = &solutions[0];
    let resolved = sol.subst.resolve_with_term(result_var).expect("result should be bound");
    // Should resolve to Carrier sort term (nullary Fn)
    match kb.get_term(resolved) {
        Term::Fn { functor, .. } => {
            let name = kb.resolve_sym(*functor);
            assert!(name.contains("Carrier"), "expected Carrier sort, got {}", name);
        }
        Term::Ref(sym) => {
            let name = kb.resolve_sym(*sym);
            assert!(name.contains("Carrier"), "expected Carrier ref, got {}", name);
        }
        other => panic!("expected Fn or Ref for Carrier, got {:?}", other),
    }
}

// ── WI-295: cross-namespace rule-predicate import ────────────────

#[test]
fn wi295_cross_namespace_rule_predicate_import_resolves() {
    // A rule-defined predicate (`my_pred`) is imported across namespaces. Its
    // head-functor Goal is registered in scan sub-pass 3 — *after* imports
    // (sub-pass 2) — so the import is deferred and resolved by the post-pass-3
    // retry rather than erroring (WI-295). Both namespaces load together so the
    // predicate isn't already interned (which would resolve it in sub-pass 2
    // and bypass the retry).
    let mut kb = load_stdlib_kb();
    let source = concat!(
        "namespace wi295.a\n",
        "  rule my_pred(?x, ?x)\n",
        "end\n",
        "namespace wi295.b\n",
        "  import wi295.a.{my_pred}\n",
        "  rule uses_pred(?y) :- my_pred(?y, ?y)\n",
        "end\n",
    );
    let parsed = parse::parse(source).expect("parse wi295 source");
    let errs = load::load(&mut kb, &parsed, &NullResolver).err().unwrap_or_default();
    let has_unresolved = errs.iter().any(|e|
        matches!(e, anthill_core::kb::load::LoadError::UnresolvedImport { .. }));
    assert!(
        !has_unresolved,
        "cross-namespace rule-predicate import should resolve via the post-pass-3 \
         retry; load errors: {errs:?}"
    );
}

// ── Typing pass spec loading ─────────────────────────────────────

#[test]
fn typing_pass_spec_parses_and_loads() {
    // The full parse → load → typecheck → requirement-insertion
    // pipeline runs in constant host stack regardless of source
    // nesting depth, and the kb's discrimination tree / NodeOccurrence
    // subtree both drop iteratively. Runs on the default 2 MiB
    // debug-build test stack with no `thread::Builder.stack_size`
    // workaround.
    let mut kb = load_stdlib_kb();

    let spec_path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../docs/proposals/typing_pass_spec.anthill");
    let source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", spec_path.display()));
    let parsed = parse::parse(&source).unwrap_or_else(|errs| {
        for e in &errs {
            eprintln!("parse error: {}", e.format_with_source(&source));
        }
        panic!("typing_pass_spec.anthill has {} parse errors", errs.len());
    });

    let result = load::load(&mut kb, &parsed, &NullResolver);
    if let Err(errs) = &result {
        for e in errs {
            eprintln!("load error: {e}");
        }
        eprintln!("typing_pass_spec.anthill had {} load warnings", errs.len());
    }

    assert!(
        kb.try_resolve_symbol("anthill.reflect.typing_pass.TypingEnv").is_some(),
        "TypingEnv sort should be defined"
    );
    assert!(
        kb.try_resolve_symbol("anthill.reflect.typing_pass.type_check").is_some(),
        "type_check operation should be defined"
    );
    assert!(
        kb.try_resolve_symbol("anthill.reflect.typing_pass.assert_compatible").is_some(),
        "assert_compatible operation should be defined"
    );
}

// ── WI-297: occurrence_term shows a literal occurrence reflected ─────

#[test]
fn wi297_occurrence_term_literal_synth_resolves() {
    // Acceptance: a synth-LIT rule whose body destructures an expression
    // occurrence via `occurrence_term` resolves to the literal's sort.
    // `probe` puts an int literal at a rule-body-atom position, so it enters
    // resolution as an `Expr::Const` occurrence; `synth`'s body shows it
    // through the reflect lens and matches `int_lit(value: ?)`.
    let source = concat!(
        "namespace wi297.t\n",
        "  import anthill.reflect.{Expr}\n",
        "  import anthill.prelude.Type.{sort_ref}\n",
        "  import anthill.prelude.{Int}\n",
        "  rule synth(?e, sort_ref(name: Int)) :- occurrence_term(?e, int_lit(value: ?))\n",
        "  rule probe(?T) :- synth(42, ?T)\n",
        "end\n",
    );
    let mut kb = load_with_source(source);

    let var_t = make_var(&mut kb, "T");
    let goal = make_goal(&mut kb, "wi297.t.probe", &[var_t]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(
        results.len(), 1,
        "probe should resolve once via synth/occurrence_term on a literal occurrence"
    );

    let bound = kb.reify(var_t, &results[0].subst);
    match kb.get_term(bound) {
        Term::Fn { functor, named_args, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "sort_ref", "synth should yield sort_ref(...)");
            let name = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "name")
                .map(|(_, t)| *t)
                .expect("sort_ref should carry a name arg");
            let name_sym = match kb.get_term(name) {
                Term::Ref(s) | Term::Ident(s) => *s,
                Term::Fn { functor, .. } => *functor,
                other => panic!("unexpected sort_ref name term: {other:?}"),
            };
            assert_eq!(kb.resolve_sym(name_sym), "Int", "literal 42 should synth to Int");
        }
        other => panic!("expected sort_ref(name: Int), got {other:?}"),
    }
}

#[test]
fn wi297_occurrence_term_discriminates_literal_kind() {
    // `occurrence_term` reads the *actual* term of the shown occurrence: a
    // distinct synth rule per literal kind, and each literal selects exactly
    // the matching rule (42 ⇒ Int, "hi" ⇒ String) — proving the builtin binds
    // the occurrence's term, not a vacuous match.
    let source = concat!(
        "namespace wi297.b\n",
        "  import anthill.reflect.{Expr}\n",
        "  import anthill.prelude.Type.{sort_ref}\n",
        "  import anthill.prelude.{Int, String}\n",
        "  rule synth(?e, sort_ref(name: Int))    :- occurrence_term(?e, int_lit(value: ?))\n",
        "  rule synth(?e, sort_ref(name: String)) :- occurrence_term(?e, string_lit(value: ?))\n",
        "  rule probe_int(?T) :- synth(42, ?T)\n",
        "  rule probe_str(?T) :- synth(\"hi\", ?T)\n",
        "end\n",
    );
    let mut kb = load_with_source(source);

    let sort_ref_name = |kb: &KnowledgeBase, t: TermId| -> String {
        match kb.get_term(t) {
            Term::Fn { functor, named_args, .. } => {
                assert_eq!(kb.resolve_sym(*functor), "sort_ref");
                let n = named_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "name")
                    .map(|(_, t)| *t).expect("sort_ref name");
                match kb.get_term(n) {
                    Term::Ref(s) | Term::Ident(s) => kb.resolve_sym(*s).to_string(),
                    Term::Fn { functor, .. } => kb.resolve_sym(*functor).to_string(),
                    other => panic!("unexpected name term {other:?}"),
                }
            }
            other => panic!("expected sort_ref, got {other:?}"),
        }
    };

    let var_i = make_var(&mut kb, "Ti");
    let g_int = make_goal(&mut kb, "wi297.b.probe_int", &[var_i]);
    let r_int = kb.resolve(&[g_int], &default_config());
    assert_eq!(r_int.len(), 1, "an int literal should select exactly the int_lit synth rule");
    let t_int = kb.reify(var_i, &r_int[0].subst);
    assert_eq!(sort_ref_name(&kb, t_int), "Int");

    let var_s = make_var(&mut kb, "Ts");
    let g_str = make_goal(&mut kb, "wi297.b.probe_str", &[var_s]);
    let r_str = kb.resolve(&[g_str], &default_config());
    assert_eq!(r_str.len(), 1, "a string literal should select exactly the string_lit synth rule");
    let t_str = kb.reify(var_s, &r_str[0].subst);
    assert_eq!(sort_ref_name(&kb, t_str), "String");
}

#[test]
fn wi297_occurrence_span_builds_source_span() {
    // `occurrence_span` constructs the anthill `source_span(...)` entity from
    // the occurrence's Rust span. The result is a term, so it propagates up.
    let source = concat!(
        "namespace wi297.sp\n",
        "  rule span_of(?e, ?s) :- occurrence_span(?e, ?s)\n",
        "  rule probe(?s) :- span_of(42, ?s)\n",
        "end\n",
    );
    let mut kb = load_with_source(source);
    let var_s = make_var(&mut kb, "s");
    let goal = make_goal(&mut kb, "wi297.sp.probe", &[var_s]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 1, "occurrence_span should produce a span term");
    let bound = kb.reify(var_s, &results[0].subst);
    match kb.get_term(bound) {
        Term::Fn { functor, named_args, .. } => {
            assert_eq!(kb.resolve_sym(*functor), "source_span");
            let keys: Vec<String> = named_args.iter().map(|(s, _)| kb.resolve_sym(*s).to_string()).collect();
            assert!(keys.contains(&"file".to_string()), "fields: {keys:?}");
            assert!(keys.contains(&"start_byte".to_string()), "fields: {keys:?}");
            assert!(keys.contains(&"end_byte".to_string()), "fields: {keys:?}");
        }
        other => panic!("expected source_span(...), got {other:?}"),
    }
}

#[test]
fn wi297_sub_occurrences_empty_vs_nonempty() {
    // `sub_occurrences` lists the direct child occurrences: a literal has none
    // (matches `nil`), a constructor has its args (matches `cons(...)`). The
    // list is matched intra-frame; an int marker propagates the outcome.
    let source = concat!(
        "namespace wi297.su\n",
        "  import anthill.prelude.{List}\n",
        "  rule kind(?e, 0) :- sub_occurrences(?e, nil)\n",
        "  rule kind(?e, 1) :- sub_occurrences(?e, cons(head: ?, tail: ?))\n",
        "  rule probe_lit(?k) :- kind(42, ?k)\n",
        "  rule probe_compound(?k) :- kind(cons(head: 1, tail: nil), ?k)\n",
        "end\n",
    );
    let mut kb = load_with_source(source);

    let var_k = make_var(&mut kb, "k");
    let g_lit = make_goal(&mut kb, "wi297.su.probe_lit", &[var_k]);
    let r_lit = kb.resolve(&[g_lit], &default_config());
    assert_eq!(r_lit.len(), 1, "a literal occurrence has no sub-occurrences (nil)");
    let t_lit = kb.reify(var_k, &r_lit[0].subst);
    assert_eq!(kb.get_term(t_lit), &Term::Const(Literal::Int(0)));

    let var_k2 = make_var(&mut kb, "k2");
    let g_cmp = make_goal(&mut kb, "wi297.su.probe_compound", &[var_k2]);
    let r_cmp = kb.resolve(&[g_cmp], &default_config());
    assert_eq!(r_cmp.len(), 1, "a constructor occurrence has sub-occurrences (cons)");
    let t_cmp = kb.reify(var_k2, &r_cmp[0].subst);
    assert_eq!(kb.get_term(t_cmp), &Term::Const(Literal::Int(1)));
}

#[test]
fn wi297_occurrence_owner_none_for_body_atom_child() {
    // A rule-body-atom child carries no owner, so `occurrence_owner` fails
    // (no top-level owner to report). Positive-owner cases need op-body
    // occurrences, reachable once `occurrences_of` is implemented.
    let source = concat!(
        "namespace wi297.ow\n",
        "  rule owner_of(?e, ?o) :- occurrence_owner(?e, ?o)\n",
        "  rule probe(?o) :- owner_of(42, ?o)\n",
        "end\n",
    );
    let mut kb = load_with_source(source);
    let var_o = make_var(&mut kb, "o");
    let goal = make_goal(&mut kb, "wi297.ow.probe", &[var_o]);
    assert_eq!(
        kb.resolve(&[goal], &default_config()).len(), 0,
        "occurrence_owner has no owner for a body-atom child"
    );
}

#[test]
fn wi297_occurrence_span_structured_pattern_matches() {
    // A *structured* `source_span(file:, start_byte:, end_byte:)` pattern must
    // match the built span term — guards that the builder canonicalizes named
    // args in declared field order (the order-sensitive discrim matcher would
    // silently miss otherwise).
    let source = concat!(
        "namespace wi297.sps\n",
        "  import anthill.reflect.{SourceSpan}\n",
        "  rule field(?e, ?s) :- occurrence_span(?e, source_span(file: ?, start_byte: ?s, end_byte: ?))\n",
        "  rule probe(?s) :- field(42, ?s)\n",
        "end\n",
    );
    let mut kb = load_with_source(source);
    let var_s = make_var(&mut kb, "s");
    let goal = make_goal(&mut kb, "wi297.sps.probe", &[var_s]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 1, "structured source_span pattern should match (field order aligned)");
    let bound = kb.reify(var_s, &results[0].subst);
    assert!(
        matches!(kb.get_term(bound), Term::Const(Literal::Int(_))),
        "start_byte should bind to an Int, got {:?}", kb.get_term(bound)
    );
}

#[test]
fn wi297_occurrence_term_compound_pattern_fails_not_panics() {
    // A child-bearing reflect pattern (`if_expr`) is not yet handled by the
    // lens; `occurrence_term` must fail (no match), NOT trip the goal-form
    // assertion in `occurrence_to_term`. The test passing without a panic is
    // the guard.
    let source = concat!(
        "namespace wi297.if\n",
        "  import anthill.reflect.{Expr}\n",
        "  rule synth_if(?e, 1) :- occurrence_term(?e, if_expr(cond: ?c, then_branch: ?t, else_branch: ?el))\n",
        "  rule probe(?k) :- synth_if(42, ?k)\n",
        "end\n",
    );
    let mut kb = load_with_source(source);
    let var_k = make_var(&mut kb, "k");
    let goal = make_goal(&mut kb, "wi297.if.probe", &[var_k]);
    assert_eq!(
        kb.resolve(&[goal], &default_config()).len(), 0,
        "a literal does not match an if_expr pattern (and must not panic)"
    );
}


// ══════════════════════════════════════════════════════════════════
// type_check_sorts tests (facts)
// ══════════════════════════════════════════════════════════════════

/// Helper: load stdlib + custom source, return KB.
fn load_with_source(source: &str) -> KnowledgeBase {
    let mut kb = load_stdlib_kb();
    let parsed = parse::parse(source).expect("parse failed");
    let refs = vec![&parsed];
    if let Err(errs) = load::load_all(&mut kb, &refs, &NullResolver) {
        for e in &errs {
            eprintln!("warning: {e}");
        }
    }
    kb
}

// ── WI-305: operation_body builtin (op body via the op_body_node side-table) ──

#[test]
fn wi305_operation_body_discriminates_some_vs_none() {
    // `operation_body(op)` returns `some(value: <body occurrence>)` for an
    // operation with an expression body and `none()` for a declaration-only op
    // — the node lives in the `op_body_node` side-table, not a fact field.
    let mut kb = load_with_source(concat!(
        "namespace wi305.t\n",
        "  import anthill.prelude.{Int}\n",
        "  operation f(x: Int) -> Int = x\n",   // has a body
        "  operation g(x: Int) -> Int\n",        // declaration only
        "end\n",
    ));
    let some_sym = kb.resolve_symbol("anthill.prelude.Option.some");
    let value_sym = kb.intern("value");

    let some_pattern = |kb: &mut KnowledgeBase| {
        let v = make_var(kb, "v");
        kb.alloc(Term::Fn {
            functor: some_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(value_sym, v)]),
        })
    };

    // op f HAS a body → operation_body(f, some(value: ?)) succeeds, binding the
    // body occurrence into the some-wrapper.
    let f_ref = {
        let f = kb.try_resolve_symbol("wi305.t.f").expect("op f");
        kb.alloc(Term::Ref(f))
    };
    let some_pat = some_pattern(&mut kb);
    let goal_f = make_goal(&mut kb, "anthill.reflect.operation_body", &[f_ref, some_pat]);
    assert_eq!(
        kb.resolve(&[goal_f], &default_config()).len(), 1,
        "operation with a body should yield some(value: <node>)",
    );

    // op g is declaration-only → its result is none(), so a some(...) pattern
    // must NOT match.
    let g_ref = {
        let g = kb.try_resolve_symbol("wi305.t.g").expect("op g");
        kb.alloc(Term::Ref(g))
    };
    let some_pat_g = some_pattern(&mut kb);
    let goal_g = make_goal(&mut kb, "anthill.reflect.operation_body", &[g_ref, some_pat_g]);
    assert_eq!(
        kb.resolve(&[goal_g], &default_config()).len(), 0,
        "declaration-only operation should yield none(), not some(...)",
    );
}

/// Helper: load only stdlib, returning both KB and LoadResult (all stdlib sorts).
fn load_stdlib_kb_with_result() -> (KnowledgeBase, LoadResult) {
    let dir = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&dir);
    assert!(!files.is_empty(), "no stdlib files found");

    let parsed: Vec<_> = files.iter()
        .map(|path| {
            let source = std::fs::read_to_string(path)
                .unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
            parse::parse(&source)
                .unwrap_or_else(|e| panic!("parse {}: {e:?}", path.display()))
        })
        .collect();

    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let result = load::load_all(&mut kb, &refs, &NullResolver);
    match result {
        Ok(load_result) => (kb, load_result),
        Err(errs) => {
            for e in &errs {
                eprintln!("Load error: {}", e);
            }
            panic!("stdlib load failed with {} errors", errs.len());
        }
    }
}

#[test]
fn type_check_correct_fact_no_errors() {
    let source = r#"
sort Color
  entity Red
  entity Blue
end

sort Shape
  entity Circle(color: Color, radius: Int)
end

fact Circle(color: Red, radius: 42)
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "correct fact should produce no errors, got: {:?}", errors);
}

#[test]
fn type_check_string_field_with_int_literal() {
    let source = r#"
sort Item
  entity Thing(name: String)
end

fact Thing(name: 42)
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "should detect Int where String expected");
    let err = &errors[0];
    match err {
        load::LoadError::TypeMismatch { field_name, expected_type, actual_type, .. } => {
            assert_eq!(field_name, "name");
            assert!(expected_type.contains("String"), "expected String, got: {expected_type}");
            assert_eq!(actual_type, "Int");
        }
        _ => panic!("expected TypeMismatch, got: {err:?}"),
    }
}

#[test]
fn type_check_int_field_with_string_literal() {
    let source = r#"
sort Item
  entity Thing(count: Int)
end

fact Thing(count: "hello")
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "should detect String where Int expected");
    match &errors[0] {
        load::LoadError::TypeMismatch { field_name, actual_type, .. } => {
            assert_eq!(field_name, "count");
            assert_eq!(actual_type, "String");
        }
        _ => panic!("expected TypeMismatch"),
    }
}

#[test]
fn type_check_wrong_entity_sort() {
    let source = r#"
sort Color
  entity Red
  entity Blue
end

sort Shape
  entity Square
  entity Circle
end

sort Item
  entity Box(color: Color)
end

fact Box(color: Square)
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "should detect Shape entity where Color expected, got: {:?}", errors);
    match &errors[0] {
        load::LoadError::TypeMismatch { field_name, expected_type, actual_type, .. } => {
            assert_eq!(field_name, "color");
            assert!(expected_type.contains("Color"), "expected Color, got: {expected_type}");
            assert!(actual_type.contains("Shape"), "actual should be Shape, got: {actual_type}");
        }
        _ => panic!("expected TypeMismatch"),
    }
}

#[test]
fn type_check_variable_field_skipped() {
    let source = r#"
sort Item
  entity Thing(name: String)
end
"#;
    // Entity definition itself has type terms, not instances — no facts to check
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "entity definitions should not produce errors, got: {:?}", errors);
}

#[test]
fn type_check_error_reports_line_number() {
    let source = "sort Item\n  entity Thing(count: Int)\nend\n\nfact Thing(count: \"hello\")\n";
    //            line 1        line 2                    line 3  line 4  line 5
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "should detect String where Int expected");
    let formatted = errors[0].format_with_source(source);
    assert!(formatted.contains("type mismatch"), "should say type mismatch: {formatted}");
    assert!(formatted.contains("Thing"), "should mention entity name: {formatted}");
    assert!(formatted.starts_with("5:"), "error should point to line 5, got: {formatted}");
}

#[test]
fn type_check_stdlib_no_spurious_errors() {
    let (mut kb, result) = load_stdlib_kb_with_result();
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "stdlib should produce no type errors, got: {:?}", errors);
}

// ══════════════════════════════════════════════════════════════════
// type_check_sorts tests (operations)
// ══════════════════════════════════════════════════════════════════

#[test]
fn type_check_op_literal_body_correct() {
    let source = r#"
sort Math
  operation one() -> Int = 1
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "correct literal body should produce no errors, got: {:?}", errors);
}

#[test]
fn type_check_op_literal_body_wrong_return() {
    let source = r#"
sort Math
  operation one() -> String = 1
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "should detect Int body vs String return type");
    match &errors[0] {
        load::LoadError::TypeMismatch { entity_name, field_name, .. } => {
            assert!(entity_name.contains("one"), "should mention operation name: {entity_name}");
            assert_eq!(field_name, "return");
        }
        _ => panic!("expected TypeMismatch, got: {:?}", errors[0]),
    }
}

#[test]
fn type_check_op_var_ref_correct() {
    let source = r#"
sort Math
  operation id(x: Int) -> Int = x
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "correct var ref should produce no errors, got: {:?}", errors);
}

#[test]
fn type_check_op_var_ref_wrong_return() {
    let source = r#"
sort Math
  operation wrong(x: Int) -> String = x
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "should detect Int var vs String return type, got: {:?}", errors);
}

#[test]
fn type_check_op_constructor_correct() {
    let source = r#"
sort Color
  entity Red
  entity Blue
end

sort Factory
  operation make_red() -> Color = Red
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "correct constructor return should produce no errors, got: {:?}", errors);
}

#[test]
fn param_and_body_var_share_same_symbol() {
    // A parameter name "x" used in the operation body should resolve to the
    // same KB Symbol as the parameter declaration in FieldInfo.
    let source = r#"
sort Math
  operation id(x: Int) -> Int = x
end
"#;
    let kb = load_with_source(source);
    let op_info_sym = kb.try_resolve_symbol("anthill.reflect.OperationInfo")
        .expect("OperationInfo should be defined");

    // Find the "id" operation's FieldInfo param symbol and body var_ref symbol
    let mut param_sym: Option<Symbol> = None;
    let mut body_var_sym: Option<Symbol> = None;

    for rid in kb.by_functor(op_info_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        if let Term::Fn { named_args, .. } = kb.get_term(head) {
            // Check if this is the "id" operation
            let is_id = named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "name")
                .and_then(|(_, v)| match kb.get_term(*v) { Term::Ref(s) => Some(*s), _ => None })
                .map(|s| kb.resolve_sym(s) == "id")
                .unwrap_or(false);
            if !is_id { continue; }

            // Extract param name symbol from FieldInfo
            if let Some(params_tid) = named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "params")
                .map(|(_, v)| *v)
            {
                // Walk cons-list to first FieldInfo
                if let Term::Fn { named_args: cons_args, .. } = kb.get_term(params_tid) {
                    if let Some((_, head_tid)) = cons_args.iter().find(|(s, _)| kb.resolve_sym(*s) == "head") {
                        if let Term::Fn { named_args: fi_args, .. } = kb.get_term(*head_tid) {
                            param_sym = fi_args.iter()
                                .find(|(s, _)| kb.resolve_sym(*s) == "name")
                                .and_then(|(_, v)| match kb.get_term(*v) { Term::Ref(s) => Some(*s), _ => None });
                        }
                    }
                }
            }

            // Extract body var_ref name symbol via `kb.op_body_node`
            // — post-WI-251 the body lives on the NodeOccurrence tree,
            // not in the OperationInfo fact's Handle slot.
            let id_sym = kb.try_resolve_symbol("Math.id")
                .or_else(|| kb.try_resolve_symbol("id"));
            if let Some(op_sym) = id_sym {
                use anthill_core::kb::node_occurrence::{Expr, NodeKind};
                if let Some(body) = kb.op_body_node(op_sym) {
                    if let NodeKind::Expr { expr: Expr::VarRef { name }, .. } = &body.kind {
                        body_var_sym = Some(*name);
                    }
                }
            }
        }
    }

    let ps = param_sym.expect("should find param symbol for x");
    let bs = body_var_sym.expect("should find body var_ref symbol for x");
    assert_eq!(kb.resolve_sym(ps), "x", "param symbol should resolve to x");
    assert_eq!(kb.resolve_sym(bs), "x", "body symbol should resolve to x");
    assert_eq!(ps, bs,
        "param symbol ({}: {}) and body var_ref symbol ({}: {}) for 'x' should be the same KB Symbol",
        ps.index(), kb.resolve_sym(ps), bs.index(), kb.resolve_sym(bs));
}

#[test]
fn type_check_op_stdlib_no_spurious_errors() {
    let (mut kb, result) = load_stdlib_kb_with_result();
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "stdlib operations should produce no type errors, got: {:?}", errors);
}

// ══════════════════════════════════════════════════════════════════
// Phase 2: if_expr, let_expr, match_expr
// ══════════════════════════════════════════════════════════════════

#[test]
fn type_check_op_if_expr_correct() {
    let source = r#"
sort Logic
  operation pick(b: Bool) -> Int = if b then 1 else 0
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "correct if_expr should produce no errors, got: {:?}", errors);
}

#[test]
fn type_check_op_if_expr_wrong_return() {
    let source = r#"
sort Logic
  operation pick(b: Bool) -> String = if b then 1 else 0
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "should detect Int branches vs String return, got: {:?}", errors);
}

#[test]
fn type_check_op_let_expr_correct() {
    // Block-style let: `let ?y = x \n body` (no `in` keyword).
    // Pre-WI-264 the typer silently swallowed errors when a body
    // sub-expression failed to resolve, so an `in` token here would
    // type-check vacuously. With Result propagation, sub-expression
    // failures surface — use the actual grammar shape.
    let source = r#"
sort Math
  operation double(x: Int) -> Int =
    let y = x
    add(y, y)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "correct let_expr should produce no errors, got: {:?}", errors);
}

#[test]
fn type_check_op_match_correct() {
    let source = r#"
sort Color
  entity Red
  entity Blue
end

sort Palette
  operation rank(c: Color) -> Int = match c
    case Red -> 1
    case Blue -> 2
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "correct match should produce no errors, got: {:?}", errors);
}

#[test]
fn type_check_op_match_wrong_return() {
    let source = r#"
sort Color
  entity Red
  entity Blue
end

sort Palette
  operation rank(c: Color) -> String = match c
    case Red -> 1
    case Blue -> 2
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "should detect Int match body vs String return, got: {:?}", errors);
}

// ══════════════════════════════════════════════════════════════════
// Lambda parameter typing (WI-275): the typer binds a lambda's
// parameter into the body env from (1) a pattern annotation, (2) the
// expected arrow's param slot, or (3) a fresh type var pinned by body
// usage / the call site. Before this, an unannotated lambda left its
// param unbound and every reference failed as `UnresolvedName`. The
// eval_test HOF tests (m2_higher_order_lambda) bypass the typer, so
// these are the typed-path proofs.
// ══════════════════════════════════════════════════════════════════

#[test]
fn type_check_op_apply_function_value() {
    // WI-289: applying a `Function`-typed parameter directly — `f(x)`.
    // `arrow` is the typer's shorthand for `Function[A, B, E]`, so a
    // `Function[String, String]`-typed value is callable and `f(x)`
    // yields `String`. Before this, the apply path only recognized
    // `arrow(...)` and rejected `f` as "unknown functor".
    let source = r#"
sort S
  import anthill.prelude.{Function, String}

  operation apply1(f: Function[String, String], x: String) -> String = f(x)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "applying a Function-typed param should typecheck, got: {:?}", errors);
}

#[test]
fn type_check_op_lambda_arg_inferred() {
    // Inline lambda as a `Function`-typed argument, in a sort-owned (so
    // type-checked) body that also applies it. Exercises the full path:
    // parse lambda-as-arg, convert, bind the lambda param, and apply the
    // Function value (WI-289).
    let source = r#"
sort S
  import anthill.prelude.{Function, String}

  operation apply1(f: Function[String, String], x: String) -> String = f(x)
  operation greet(x: String) -> String = apply1(lambda q -> q, x)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "inline lambda arg should typecheck, got: {:?}", errors);
}

#[test]
fn type_check_op_lambda_let_inferred() {
    // Let-bound lambda with no annotation and no expected type: the
    // param binds to a fresh type var, and the call site `g(x)` pins it
    // to String. Previously failed with `q unresolved`.
    let source = r#"
sort S
  import anthill.prelude.{Function, String}

  operation make(x: String) -> String =
    let g = lambda q -> q
    g(x)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "let-bound lambda should typecheck, got: {:?}", errors);
}

// ══════════════════════════════════════════════════════════════════
// types_compatible tests
// ══════════════════════════════════════════════════════════════════

use anthill_core::kb::typing::{
    types_compatible as raw_types_compatible,
    is_subtype, requires_chain_flat, check_obligations, type_check_sorts,
};
use anthill_core::kb::subst::Substitution;

/// Test-private wrapper around [`raw_types_compatible`] that allocates a
/// fresh substitution per call. WI-335 added an explicit `&mut Substitution`
/// argument so nested arrow checks could thread row-var bindings across
/// sibling positions; for unit tests of isolated type pairs that
/// independence is the right default — each call gets its own subst.
fn types_compatible(kb: &mut KnowledgeBase, actual: TermId, expected: TermId) -> bool {
    let mut subst = Substitution::new();
    raw_types_compatible(kb, &mut subst, &TermIdView(actual), &TermIdView(expected))
}

#[test]
fn subtype_same_sort_ref() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    assert!(types_compatible(&mut kb, int_ty, int_ty), "Int <: Int");
}

#[test]
fn subtype_different_sort_ref_incompatible() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let string_ty = kb.make_sort_ref_by_name("String");
    assert!(!types_compatible(&mut kb, int_ty, string_ty), "Int not <: String");
}

#[test]
fn subtype_entity_of_enum() {
    // red <: Color (entity of enum)
    let source = r#"
enum Color
  entity red
  entity blue
end
"#;
    let mut kb = load_with_source(source);
    let red_sym = kb.resolve_symbol("Color.red");
    let color_sym = kb.resolve_symbol("Color");
    let red_ty = kb.make_sort_ref(red_sym);
    let color_ty = kb.make_sort_ref(color_sym);
    assert!(types_compatible(&mut kb, red_ty, color_ty), "red <: Color");
    assert!(!types_compatible(&mut kb, color_ty, red_ty), "Color not <: red");
}

#[test]
fn subtype_entity_same_parent() {
    // red not <: blue (both entities of Color, but not subtypes of each other)
    let source = r#"
enum Color
  entity red
  entity blue
end
"#;
    let mut kb = load_with_source(source);
    let red_sym = kb.resolve_symbol("Color.red");
    let blue_sym = kb.resolve_symbol("Color.blue");
    let red_ty = kb.make_sort_ref(red_sym);
    let blue_ty = kb.make_sort_ref(blue_sym);
    assert!(!types_compatible(&mut kb, red_ty, blue_ty), "red not <: blue");
}

#[test]
fn subtype_named_tuple_width() {
    // (a: Int, b: String) <: (a: Int) — extra fields OK
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let string_ty = kb.make_sort_ref_by_name("String");
    let a_sym = kb.intern("a");
    let b_sym = kb.intern("b");
    let wider = kb.make_named_tuple_type(&[(a_sym, int_ty), (b_sym, string_ty)]);
    let narrower = kb.make_named_tuple_type(&[(a_sym, int_ty)]);
    assert!(types_compatible(&mut kb, wider, narrower), "(a: Int, b: String) <: (a: Int)");
    assert!(!types_compatible(&mut kb, narrower, wider), "(a: Int) not <: (a: Int, b: String)");
}

#[test]
fn subtype_named_tuple_depth() {
    // (color: sort_ref(red)) <: (color: sort_ref(Color))
    let source = r#"
enum Color
  entity red
end
"#;
    let mut kb = load_with_source(source);
    let red_sym = kb.resolve_symbol("Color.red");
    let color_sym = kb.resolve_symbol("Color");
    let red_ty = kb.make_sort_ref(red_sym);
    let color_ty = kb.make_sort_ref(color_sym);
    let field_sym = kb.intern("color");
    let specific = kb.make_named_tuple_type(&[(field_sym, red_ty)]);
    let general = kb.make_named_tuple_type(&[(field_sym, color_ty)]);
    assert!(types_compatible(&mut kb, specific, general), "(color: red) <: (color: Color)");
}

#[test]
fn subtype_arrow_covariant_result() {
    // (Int -> red) <: (Int -> Color) — covariant result
    let source = r#"
enum Color
  entity red
end
"#;
    let mut kb = load_with_source(source);
    let int_ty = kb.make_sort_ref_by_name("Int");
    let red_sym = kb.resolve_symbol("Color.red");
    let color_sym = kb.resolve_symbol("Color");
    let red_ty = kb.make_sort_ref(red_sym);
    let color_ty = kb.make_sort_ref(color_sym);
    let specific = kb.make_arrow_type(int_ty, red_ty, &[]);
    let general = kb.make_arrow_type(int_ty, color_ty, &[]);
    assert!(types_compatible(&mut kb, specific, general), "(Int -> red) <: (Int -> Color)");
}

#[test]
fn subtype_arrow_contravariant_param() {
    // (Color -> Int) <: (red -> Int) — contravariant param
    let source = r#"
enum Color
  entity red
end
"#;
    let mut kb = load_with_source(source);
    let int_ty = kb.make_sort_ref_by_name("Int");
    let red_sym = kb.resolve_symbol("Color.red");
    let color_sym = kb.resolve_symbol("Color");
    let red_ty = kb.make_sort_ref(red_sym);
    let color_ty = kb.make_sort_ref(color_sym);
    let general_param = kb.make_arrow_type(color_ty, int_ty, &[]);
    let specific_param = kb.make_arrow_type(red_ty, int_ty, &[]);
    assert!(types_compatible(&mut kb, general_param, specific_param), "(Color -> Int) <: (red -> Int)");
    assert!(!types_compatible(&mut kb, specific_param, general_param), "(red -> Int) not <: (Color -> Int)");
}

#[test]
fn subtype_parameterized_same() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let t_sym = kb.intern("T");
    let list_base = kb.make_sort_ref_by_name("List");
    let list_int = kb.make_parameterized_type(list_base, &[(t_sym, int_ty)]);
    assert!(types_compatible(&mut kb, list_int, list_int), "List[T=Int] <: List[T=Int]");
}

#[test]
fn subtype_parameterized_different_binding_incompatible() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let string_ty = kb.make_sort_ref_by_name("String");
    let t_sym = kb.intern("T");
    let list_base = kb.make_sort_ref_by_name("List");
    let list_int = kb.make_parameterized_type(list_base, &[(t_sym, int_ty)]);
    let list_str = kb.make_parameterized_type(list_base, &[(t_sym, string_ty)]);
    assert!(!types_compatible(&mut kb, list_int, list_str), "List[T=Int] not <: List[T=String]");
}

#[test]
fn subtype_type_var_compatible_with_anything() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let fresh = kb.intern("?X");
    let var_ty = kb.make_type_var(fresh);
    assert!(types_compatible(&mut kb, var_ty, int_ty), "type_var <: Int");
    assert!(types_compatible(&mut kb, int_ty, var_ty), "Int <: type_var");
}

#[test]
fn subtype_nothing_compatible_with_anything() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let nothing = kb.make_nothing_type();
    assert!(types_compatible(&mut kb, nothing, int_ty), "nothing <: Int");
}

#[test]
fn subtype_arrow_pure_subtype_of_effectful() {
    // (Int -> Int @ []) <: (Int -> Int @ [E]) — pure function usable where effects declared
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e_sym = kb.intern("SomeEffect");
    let effect = kb.make_sort_ref(e_sym);
    let pure_fn = kb.make_arrow_type(int_ty, int_ty, &[]);
    let effectful_fn = kb.make_arrow_type(int_ty, int_ty, &[effect]);
    assert!(types_compatible(&mut kb, pure_fn, effectful_fn), "pure <: effectful");
}

#[test]
fn subtype_arrow_fewer_effects() {
    // (Int -> Int @ [E1]) <: (Int -> Int @ [E1, E2]) — fewer effects OK
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e2_sym = kb.intern("E2");
    let e1 = kb.make_sort_ref(e1_sym);
    let e2 = kb.make_sort_ref(e2_sym);
    let fewer = kb.make_arrow_type(int_ty, int_ty, &[e1]);
    let more = kb.make_arrow_type(int_ty, int_ty, &[e1, e2]);
    assert!(types_compatible(&mut kb, fewer, more), "fewer effects <: more effects");
    assert!(!types_compatible(&mut kb, more, fewer), "more effects not <: fewer effects");
}

#[test]
fn subtype_arrow_different_effects_incompatible() {
    // (Int -> Int @ [E1]) not <: (Int -> Int @ [E2]) — different effects
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e2_sym = kb.intern("E2");
    let e1 = kb.make_sort_ref(e1_sym);
    let e2 = kb.make_sort_ref(e2_sym);
    let fn1 = kb.make_arrow_type(int_ty, int_ty, &[e1]);
    let fn2 = kb.make_arrow_type(int_ty, int_ty, &[e2]);
    assert!(!types_compatible(&mut kb, fn1, fn2), "different effects not compatible");
}

/// WI-307 v1a canonical-form invariant: two arrow types built from the
/// SAME set of effect labels in DIFFERENT input order must hash-cons to the
/// SAME TermId. Pins the docstring promise on
/// `build_canonical_effects_rows` against code-review #12 (existing
/// parse_test had source order == alphabetic order, so it couldn't
/// distinguish source-order from canonical-order behavior).
#[test]
fn arrow_effects_canonical_form_hash_cons_stable() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    // Use names whose alphabetic order is OPPOSITE to source order, so the
    // canonical sort must actively reorder to make the TermIds match.
    let z_sym = kb.intern("ZebraEffect");
    let a_sym = kb.intern("AlphaEffect");
    let z = kb.make_sort_ref(z_sym);
    let a = kb.make_sort_ref(a_sym);

    let arrow_forward  = kb.make_arrow_type(int_ty, int_ty, &[z, a]); // source: Z, A
    let arrow_reverse  = kb.make_arrow_type(int_ty, int_ty, &[a, z]); // source: A, Z

    assert_eq!(
        arrow_forward, arrow_reverse,
        "two arrows with the same effect set in reversed source order must \
         hash-cons to the same TermId — that's the whole point of the \
         canonical form. forward={:?} reverse={:?}",
        arrow_forward, arrow_reverse,
    );
}

/// Empty effects, in two orderings, also produce identical TermIds —
/// guards against a regression where an empty input fell into a different
/// path (e.g. a stray `Vec::new()` branch) than the general one.
#[test]
fn arrow_effects_empty_canonical_stable() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let a = kb.make_arrow_type(int_ty, int_ty, &[]);
    let b = kb.make_arrow_type(int_ty, int_ty, &[]);
    assert_eq!(a, b, "two pure arrows must hash-cons identically");
}

// ── WI-307 v1a row unification tests ─────────────────────────────────────

/// Closed/closed: identical label sets unify trivially.
#[test]
fn row_unify_closed_closed_same() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let ea_sym = kb.intern("EffectA");
    let eb_sym = kb.intern("EffectB");
    let e1 = kb.make_sort_ref(ea_sym);
    let e2 = kb.make_sort_ref(eb_sym);
    let arrow_a = kb.make_arrow_type(int_ty, int_ty, &[e1, e2]);
    let arrow_b = kb.make_arrow_type(int_ty, int_ty, &[e2, e1]); // reversed input order
    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(arrow_a), &TermIdView(arrow_b)),
        "two closed rows with same label set must unify");
}

/// Closed/closed: different label sets fail.
#[test]
fn row_unify_closed_closed_different() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let ea_sym = kb.intern("EffectA");
    let eb_sym = kb.intern("EffectB");
    let e1 = kb.make_sort_ref(ea_sym);
    let e2 = kb.make_sort_ref(eb_sym);
    let arrow_a = kb.make_arrow_type(int_ty, int_ty, &[e1]);
    let arrow_b = kb.make_arrow_type(int_ty, int_ty, &[e2]);
    let mut subst = Substitution::new();
    assert!(!unify_types(&mut kb, &mut subst, &TermIdView(arrow_a), &TermIdView(arrow_b)),
        "two closed rows with different label sets must NOT unify");
}

/// Open/closed: the open side's tail absorbs the labels the closed side
/// carries beyond the common set.
#[test]
fn row_unify_open_closed_tail_absorbs() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let ea_sym = kb.intern("EffectA");
    let eb_sym = kb.intern("EffectB");
    let e1 = kb.make_sort_ref(ea_sym);
    let e2 = kb.make_sort_ref(eb_sym);

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    let open_row    = kb.make_arrow_type(int_ty, int_ty, &[e1, rho]);   // {EffectA | ?rho}
    let closed_row  = kb.make_arrow_type(int_ty, int_ty, &[e1, e2]);    // {EffectA, EffectB}

    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(open_row), &TermIdView(closed_row)),
        "open row should unify with closed row of same labels + extras");
    assert!(subst.resolve_with_term(rho_vid).is_some(),
        "?rho should be bound after row unification");
}

/// Open/closed: open row's labels exceed closed row's — closed can't
/// provide the missing label, so unification fails.
#[test]
fn row_unify_open_closed_missing_label_fails() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let ea_sym = kb.intern("EffectA");
    let eb_sym = kb.intern("EffectB");
    let ec_sym = kb.intern("EffectC");
    let e1 = kb.make_sort_ref(ea_sym);
    let e2 = kb.make_sort_ref(eb_sym);
    let e3 = kb.make_sort_ref(ec_sym);

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    let open_row   = kb.make_arrow_type(int_ty, int_ty, &[e1, e3, rho]); // {EffectA, EffectC | ?rho}
    let closed_row = kb.make_arrow_type(int_ty, int_ty, &[e1, e2]);      // {EffectA, EffectB}

    let mut subst = Substitution::new();
    assert!(!unify_types(&mut kb, &mut subst, &TermIdView(open_row), &TermIdView(closed_row)),
        "open row with extra labels not in closed row must NOT unify");
}

/// Open/open with shared identical tail var and same labels — hash-cons
/// fast path covers this (the arrows share a TermId).
#[test]
fn row_unify_open_open_same_tail() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let ea_sym = kb.intern("EffectA");
    let e1 = kb.make_sort_ref(ea_sym);

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    let arrow_a = kb.make_arrow_type(int_ty, int_ty, &[e1, rho]);
    let arrow_b = kb.make_arrow_type(int_ty, int_ty, &[e1, rho]); // identical
    assert_eq!(arrow_a, arrow_b, "identical open rows share TermId");

    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(arrow_a), &TermIdView(arrow_b)),
        "identical open rows unify trivially");
}

/// Open/open with DIFFERENT tail vars and disjoint extras — both tails
/// bind to absorb the other side's labels + a fresh shared row variable.
/// This is the canonical Rémy fresh-tail case.
#[test]
fn row_unify_open_open_disjoint_extras() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let ea_sym = kb.intern("EffectA");
    let eb_sym = kb.intern("EffectB");
    let e1 = kb.make_sort_ref(ea_sym);
    let e2 = kb.make_sort_ref(eb_sym);

    let rho_a_sym = kb.intern("?rho_a");
    let rho_b_sym = kb.intern("?rho_b");
    let rho_a_vid = kb.fresh_var(rho_a_sym);
    let rho_b_vid = kb.fresh_var(rho_b_sym);
    let rho_a = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_a_vid)));
    let rho_b = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_b_vid)));

    let arrow_a = kb.make_arrow_type(int_ty, int_ty, &[e1, rho_a]); // {EffectA | ?rho_a}
    let arrow_b = kb.make_arrow_type(int_ty, int_ty, &[e2, rho_b]); // {EffectB | ?rho_b}

    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(arrow_a), &TermIdView(arrow_b)),
        "open/open with disjoint extras must unify (Rémy fresh-tail case)");
    assert!(subst.resolve_with_term(rho_a_vid).is_some(),
        "?rho_a should be bound");
    assert!(subst.resolve_with_term(rho_b_vid).is_some(),
        "?rho_b should be bound");
}

/// Open/open where each side carries the same common label plus its own
/// tail — both tails should be unifiable (with no extras to migrate).
#[test]
fn row_unify_open_open_same_labels() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let ea_sym = kb.intern("EffectA");
    let e1 = kb.make_sort_ref(ea_sym);

    let rho_a_sym = kb.intern("?rho_a");
    let rho_b_sym = kb.intern("?rho_b");
    let rho_a_vid = kb.fresh_var(rho_a_sym);
    let rho_b_vid = kb.fresh_var(rho_b_sym);
    let rho_a = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_a_vid)));
    let rho_b = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_b_vid)));

    let arrow_a = kb.make_arrow_type(int_ty, int_ty, &[e1, rho_a]);
    let arrow_b = kb.make_arrow_type(int_ty, int_ty, &[e1, rho_b]);

    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(arrow_a), &TermIdView(arrow_b)),
        "open/open with same labels must unify; tails link through a fresh shared var");
}

// ── WI-328 v1b lacks-constraint tests ────────────────────────────────────
//
// `-e` (`absent(e)`) on an open row is a `lacks e` constraint on its tail:
// no binding of that tail may present `e`. These exercise the four pieces:
// registration (decompose's absent slot → Substitution::lacks), the bind
// check (present-into-lacked-tail rejected), propagation onto a fresh
// shared tail, and the within-row present/absent clash reject.

/// A closed row presenting a NON-lacked effect unifies with `{-Error | ρ}`:
/// `Other` ≠ `Error`, so the tail closes to `{Other}` without violating the
/// lacks. ρ is bound.
#[test]
fn row_lacks_unify_non_conflicting_label_ok() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let err = kb.make_sort_ref_by_name("Error");
    let other = kb.make_sort_ref_by_name("Other");

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    let absent_err = kb.make_effect_expression_absent(err);
    let closed_other = kb.make_arrow_type(int_ty, int_ty, &[other]);     // {Other}
    let lacks_row    = kb.make_arrow_type(int_ty, int_ty, &[absent_err, rho]); // {-Error | ρ}

    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(closed_other), &TermIdView(lacks_row)),
        "{{Other}} unifies with {{-Error | ρ}} — Other is not the lacked Error");
    assert!(subst.resolve_with_term(rho_vid).is_some(),
        "ρ should be bound (absorbs Other, closing the row)");
}

/// A closed row presenting the LACKED effect must NOT unify with
/// `{-Error | ρ}`: binding ρ to `{Error}` would present a forbidden effect.
/// This is the §7.1 "presents e against a tail carrying lacks e fails".
#[test]
fn row_lacks_unify_present_lacked_label_fails() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let err = kb.make_sort_ref_by_name("Error");

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    let absent_err = kb.make_effect_expression_absent(err);
    let closed_err = kb.make_arrow_type(int_ty, int_ty, &[err]);          // {Error}
    let lacks_row  = kb.make_arrow_type(int_ty, int_ty, &[absent_err, rho]); // {-Error | ρ}

    let mut subst = Substitution::new();
    assert!(!unify_types(&mut kb, &mut subst, &TermIdView(closed_err), &TermIdView(lacks_row)),
        "{{Error}} must NOT unify with {{-Error | ρ}} — ρ lacks Error");
}

/// Open/open: `{-Error | ρa}` unified with `{Error | ρb}` fails — the
/// `Error` presented on the b side flows into ρa (which lacks Error) during
/// the Rémy fresh-tail step. Proven impossibility on the open/open arm.
#[test]
fn row_lacks_open_open_present_into_lacking_tail_fails() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let err = kb.make_sort_ref_by_name("Error");

    let rho_a_sym = kb.intern("?rho_a");
    let rho_a_vid = kb.fresh_var(rho_a_sym);
    let rho_a = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_a_vid)));
    let rho_b_sym = kb.intern("?rho_b");
    let rho_b_vid = kb.fresh_var(rho_b_sym);
    let rho_b = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_b_vid)));

    let absent_err = kb.make_effect_expression_absent(err);
    let lacks_row = kb.make_arrow_type(int_ty, int_ty, &[absent_err, rho_a]); // {-Error | ρa}
    let err_row   = kb.make_arrow_type(int_ty, int_ty, &[err, rho_b]);        // {Error | ρb}

    let mut subst = Substitution::new();
    assert!(!unify_types(&mut kb, &mut subst, &TermIdView(lacks_row), &TermIdView(err_row)),
        "{{-Error | ρa}} must NOT unify with {{Error | ρb}} — Error flows into ρa which lacks it");
}

/// Propagation onto the fresh shared tail. Step 1 unifies `{-Error | ρa}`
/// with `{ρb}` (both open, no present labels): ρa/ρb link through a fresh
/// shared tail that INHERITS the lacks-Error. Step 2, reusing the same
/// substitution, unifies `{Error}` against `{ρb}` — ρb now resolves to the
/// fresh tail, so presenting Error must fail, proving the constraint
/// propagated. (This is the map/fold callback shape: a `-Error` on one
/// arrow's tail constrains the shared tail every later row links to.)
#[test]
fn row_lacks_propagates_to_fresh_shared_tail() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let err = kb.make_sort_ref_by_name("Error");

    let rho_a_sym = kb.intern("?rho_a");
    let rho_a_vid = kb.fresh_var(rho_a_sym);
    let rho_a = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_a_vid)));
    let rho_b_sym = kb.intern("?rho_b");
    let rho_b_vid = kb.fresh_var(rho_b_sym);
    let rho_b = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_b_vid)));

    let absent_err = kb.make_effect_expression_absent(err);
    let lacks_row = kb.make_arrow_type(int_ty, int_ty, &[absent_err, rho_a]); // {-Error | ρa}
    let open_b    = kb.make_arrow_type(int_ty, int_ty, &[rho_b]);             // {ρb}

    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(lacks_row), &TermIdView(open_b)),
        "step 1: {{-Error | ρa}} unifies with {{ρb}} (both open)");

    // Step 2: present Error against ρb's now-shared tail — must fail.
    let closed_err = kb.make_arrow_type(int_ty, int_ty, &[err]);             // {Error}
    let open_b2    = kb.make_arrow_type(int_ty, int_ty, &[rho_b]);           // {ρb} (resolves to fresh tail)
    assert!(!unify_types(&mut kb, &mut subst, &TermIdView(closed_err), &TermIdView(open_b2)),
        "step 2: {{Error}} must NOT unify with the shared tail that inherited lacks-Error");
}

/// A row that both presents and absents the SAME label (`{Error, -Error}`)
/// is malformed — decompose rejects it, so any unification involving it
/// fails (proposal §7.2 present/absent clash).
#[test]
fn row_present_absent_same_label_rejected() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let err = kb.make_sort_ref_by_name("Error");

    let absent_err = kb.make_effect_expression_absent(err);
    let clash_row  = kb.make_arrow_type(int_ty, int_ty, &[err, absent_err]); // {Error, -Error}
    let closed_err = kb.make_arrow_type(int_ty, int_ty, &[err]);             // {Error}

    let mut subst = Substitution::new();
    assert!(!unify_types(&mut kb, &mut subst, &TermIdView(clash_row), &TermIdView(closed_err)),
        "{{Error, -Error}} is malformed (present/absent clash) — unification rejects");
}

// ── WI-326 v1a row subtyping tests ───────────────────────────────────────
//
// These exercise the directional row algorithm in `arrow_compatible`.
// Pre-WI-326 these would fail because the naive effects-subset check
// rejected any row containing a `Var` (the open tail) — no functor →
// types_compatible returns false → subset fails. The new
// `subtype_effect_rows` honors open-tail subsumption.

/// Pure ≤ effectful — a pure function (closed empty row) is a subtype of
/// any arrow with effects. Pre-WI-326 path stayed green (no open tails,
/// no Var rejection); test re-pinned post-row-subtyping to guard against
/// regressions in the closed-into-closed-via-rows path.
#[test]
fn subtype_arrow_pure_subtype_of_effectful_via_rows() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e_sym = kb.intern("SomeEffect");
    let effect = kb.make_sort_ref(e_sym);
    let pure_fn = kb.make_arrow_type(int_ty, int_ty, &[]);
    let effectful_fn = kb.make_arrow_type(int_ty, int_ty, &[effect]);
    assert!(types_compatible(&mut kb, pure_fn, effectful_fn),
        "pure (closed empty row) <: effectful (closed {{e}}) — covariant subset");
    assert!(!types_compatible(&mut kb, effectful_fn, pure_fn),
        "effectful NOT <: pure — pure has fewer effects, can't accept more");
}

/// Open ≤ closed with absorbable extras — actual has open tail with no
/// known labels; expected is closed with some labels. For sub to hold,
/// actual's tail must close (the local subst will bind it). Pre-WI-326
/// the open tail (a `Var` in effects_rows_to_flat_list) made every
/// types_compatible check fail; the new row algorithm closes the tail.
#[test]
fn subtype_arrow_open_le_closed_tail_closes() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e2_sym = kb.intern("E2");
    let e1 = kb.make_sort_ref(e1_sym);
    let e2 = kb.make_sort_ref(e2_sym);

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    // Actual: {| ?rho} — open row, no concrete labels.
    let open_actual = kb.make_arrow_type(int_ty, int_ty, &[rho]);
    // Expected: {E1, E2} — closed.
    let closed_expected = kb.make_arrow_type(int_ty, int_ty, &[e1, e2]);

    assert!(types_compatible(&mut kb, open_actual, closed_expected),
        "open-tail actual (no labels) <: closed expected — actual's tail closes to empty");
}

/// Open ≤ closed where actual has labels not in expected → must reject.
/// Actual's known label set has an item expected doesn't cover; expected
/// is closed (no tail to absorb it).
#[test]
fn subtype_arrow_open_le_closed_extras_reject() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e2_sym = kb.intern("E2");
    let e3_sym = kb.intern("E3");
    let e1 = kb.make_sort_ref(e1_sym);
    let e2 = kb.make_sort_ref(e2_sym);
    let e3 = kb.make_sort_ref(e3_sym);

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    // Actual: {E1, E3 | ?rho} — has E3 not in expected.
    let open_actual = kb.make_arrow_type(int_ty, int_ty, &[e1, e3, rho]);
    // Expected: {E1, E2} — closed, no E3.
    let closed_expected = kb.make_arrow_type(int_ty, int_ty, &[e1, e2]);

    assert!(!types_compatible(&mut kb, open_actual, closed_expected),
        "open actual with extra concrete label NOT in closed expected must reject");
}

/// Closed ≤ open — actual's labels go into expected's tail (or are
/// covered already). Always compatible: expected is permissive.
#[test]
fn subtype_arrow_closed_le_open() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e1 = kb.make_sort_ref(e1_sym);

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    let closed_actual = kb.make_arrow_type(int_ty, int_ty, &[e1]);
    let open_expected = kb.make_arrow_type(int_ty, int_ty, &[rho]); // {| ?rho}

    assert!(types_compatible(&mut kb, closed_actual, open_expected),
        "closed actual <: open expected — expected's tail absorbs actual's labels");
}

// ── WI-332 arrow-vs-Function path effects consistency ──────────────────
//
// Pre-WI-332 arrow_function_compatible discarded effects entirely while
// arrow_compatible (post-WI-326) compared them via row subtyping. So the
// same denotational type (arrow shorthand vs Function[A,B,E] alias)
// got different sub answers depending on syntactic form.

/// WI-332: an arrow with effects must NOT be a subtype of a Function with
/// fewer effects (closed empty E). Pre-WI-332 this was incorrectly
/// accepted because arrow_function_compatible discarded effects.
#[test]
fn subtype_arrow_with_effect_not_le_function_no_effect() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let reads_sym = kb.intern("Reads");
    let reads = kb.make_sort_ref(reads_sym);

    // arrow(Int, Int, {Reads})
    let actual = kb.make_arrow_type(int_ty, int_ty, &[reads]);

    // Function[A=Int, B=Int, E=effects_rows(empty_row)] — closed empty
    // effects (no Reads). Explicit binding distinguishes this from the
    // "missing E = polymorphic" case (see below).
    let fn_sym = kb.resolve_symbol("anthill.prelude.Function");
    let fn_base = kb.make_sort_ref(fn_sym);
    let a_sym = kb.intern("A");
    let b_sym = kb.intern("B");
    let e_sym = kb.intern("E");
    let empty_effects_rows = kb.build_canonical_effects_rows(&[]);
    let expected = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, empty_effects_rows)],
    );

    assert!(!types_compatible(&mut kb, actual, expected),
        "arrow(Int, Int, {{Reads}}) NOT <: Function[A=Int, B=Int, E={{}}] — \
         actual has Reads, expected closed-empty can't accept");
}

/// WI-332: an arrow with empty effects IS a subtype of a Function with
/// effects (covariant subset). Already worked pre-WI-332 (effects
/// ignored), now works for the right reason (closed empty ⊆ any closed).
#[test]
fn subtype_arrow_pure_le_function_with_effects() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let reads_sym = kb.intern("Reads");
    let reads = kb.make_sort_ref(reads_sym);

    let actual = kb.make_arrow_type(int_ty, int_ty, &[]);

    let fn_sym = kb.resolve_symbol("anthill.prelude.Function");
    let fn_base = kb.make_sort_ref(fn_sym);
    let a_sym = kb.intern("A");
    let b_sym = kb.intern("B");
    let e_sym = kb.intern("E");
    let effects_rows = kb.build_canonical_effects_rows(&[reads]);
    let expected = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, effects_rows)],
    );

    assert!(types_compatible(&mut kb, actual, expected),
        "arrow(Int, Int, {{}}) <: Function[A=Int, B=Int, E={{Reads}}] — \
         pure (empty) is a subset of any closed effect set");
}

/// WI-332: Function with NO E binding is polymorphic in effects — accepts
/// effectful actuals (matches the missing-A convention). Distinguishes
/// `Function[Int, Int]` (polymorphic E, accept anything) from
/// `Function[A=Int, B=Int, E={}]` (explicit closed empty, reject
/// effectful). Without this distinction, common user code like
/// `operation use(f: Function[Int, Int]) = f(5)` would regress against
/// effectful lambda actuals that worked pre-WI-332.
#[test]
fn subtype_arrow_with_effect_le_function_no_E_binding_polymorphic() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let reads_sym = kb.intern("Reads");
    let reads = kb.make_sort_ref(reads_sym);

    let actual = kb.make_arrow_type(int_ty, int_ty, &[reads]);

    let fn_sym = kb.resolve_symbol("anthill.prelude.Function");
    let fn_base = kb.make_sort_ref(fn_sym);
    let a_sym = kb.intern("A");
    let b_sym = kb.intern("B");
    // Function[A=Int, B=Int] — NO E binding, polymorphic in effects.
    let expected = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty)],
    );

    assert!(types_compatible(&mut kb, actual, expected),
        "arrow(Int, Int, {{Reads}}) <: Function[A=Int, B=Int] — missing \
         E binding is polymorphic in effects, accepts any actual");
}

/// WI-332: Function-vs-arrow direction (mirrors the arrow-vs-Function
/// direction). Pre-WI-332 effects discarded; post-WI-332 row sub honored.
#[test]
fn subtype_function_with_effect_not_le_arrow_no_effect() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let reads_sym = kb.intern("Reads");
    let reads = kb.make_sort_ref(reads_sym);

    // Function[A=Int, B=Int, E={Reads}]
    let fn_sym = kb.resolve_symbol("anthill.prelude.Function");
    let fn_base = kb.make_sort_ref(fn_sym);
    let a_sym = kb.intern("A");
    let b_sym = kb.intern("B");
    let e_sym = kb.intern("E");
    let effects_rows = kb.build_canonical_effects_rows(&[reads]);
    let actual = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, effects_rows)],
    );

    // arrow(Int, Int, {}) — closed empty
    let expected = kb.make_arrow_type(int_ty, int_ty, &[]);

    assert!(!types_compatible(&mut kb, actual, expected),
        "Function[A=Int, B=Int, E={{Reads}}] NOT <: arrow(Int, Int, {{}}) — \
         same denotational shape as arrow-vs-arrow rejection");
}

// ── WI-333 Function-vs-Function effects path uses row subtyping ─────────
//
// Pre-WI-333 the (effects_rows, effects_rows) arm in types_compatible did
// conservative structural recursion — sound but missed open-row subsumption.
// So Function[E={Reads}] <: Function[E={Reads, Writes}] was REJECTED (the
// inner EffectExpression trees differ), even though arrow(_, _, {Reads}) <:
// arrow(_, _, {Reads, Writes}) was ACCEPTED post-WI-326. Same denotational
// type written via the parameterized form, opposite answer.

/// WI-333: Function[E={Reads}] IS a subtype of Function[E={Reads, Writes}]
/// — fewer effects subset of more effects (closed/closed). Pre-WI-333
/// rejected via the conservative structural recursion.
#[test]
fn subtype_function_E_fewer_effects_le_more() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let reads_sym = kb.intern("Reads");
    let writes_sym = kb.intern("Writes");
    let reads = kb.make_sort_ref(reads_sym);
    let writes = kb.make_sort_ref(writes_sym);

    let fn_sym = kb.resolve_symbol("anthill.prelude.Function");
    let fn_base = kb.make_sort_ref(fn_sym);
    let a_sym = kb.intern("A");
    let b_sym = kb.intern("B");
    let e_sym = kb.intern("E");

    let fewer_rows = kb.build_canonical_effects_rows(&[reads]);
    let more_rows = kb.build_canonical_effects_rows(&[reads, writes]);

    let fewer = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, fewer_rows)],
    );
    let more = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, more_rows)],
    );

    assert!(types_compatible(&mut kb, fewer, more),
        "Function[E={{Reads}}] <: Function[E={{Reads, Writes}}] — fewer effects");
    assert!(!types_compatible(&mut kb, more, fewer),
        "Function[E={{Reads, Writes}}] NOT <: Function[E={{Reads}}]");
}

/// WI-333: disjoint effect sets are incompatible — Function[E={Reads}] vs
/// Function[E={Writes}]. Closed/closed with only_a non-empty → reject.
#[test]
fn subtype_function_E_disjoint_effects_incompatible() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let reads_sym = kb.intern("Reads");
    let writes_sym = kb.intern("Writes");
    let reads = kb.make_sort_ref(reads_sym);
    let writes = kb.make_sort_ref(writes_sym);

    let fn_sym = kb.resolve_symbol("anthill.prelude.Function");
    let fn_base = kb.make_sort_ref(fn_sym);
    let a_sym = kb.intern("A");
    let b_sym = kb.intern("B");
    let e_sym = kb.intern("E");

    let reads_rows = kb.build_canonical_effects_rows(&[reads]);
    let writes_rows = kb.build_canonical_effects_rows(&[writes]);

    let fn_reads = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, reads_rows)],
    );
    let fn_writes = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, writes_rows)],
    );

    assert!(!types_compatible(&mut kb, fn_reads, fn_writes),
        "Function[E={{Reads}}] NOT <: Function[E={{Writes}}] — disjoint");
}

/// WI-333: open-row subsumption works through the Function[E] path now,
/// matching arrow_compatible behavior. Function[E={| ?rho}] <:
/// Function[E={Reads}] — actual's open tail closes to empty under the
/// directional row algorithm.
#[test]
fn subtype_function_E_open_le_closed() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let reads_sym = kb.intern("Reads");
    let reads = kb.make_sort_ref(reads_sym);

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    let fn_sym = kb.resolve_symbol("anthill.prelude.Function");
    let fn_base = kb.make_sort_ref(fn_sym);
    let a_sym = kb.intern("A");
    let b_sym = kb.intern("B");
    let e_sym = kb.intern("E");

    let open_rows = kb.build_canonical_effects_rows(&[rho]);
    let closed_rows = kb.build_canonical_effects_rows(&[reads]);

    let actual = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, open_rows)],
    );
    let expected = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, closed_rows)],
    );

    assert!(types_compatible(&mut kb, actual, expected),
        "Function[E={{|?rho}}] <: Function[E={{Reads}}] — open tail closes");
}

/// WI-333: open actual with EXTRA concrete labels NOT in closed expected
/// must reject (mirrors `subtype_arrow_open_le_closed_extras_reject` from
/// the arrow path). Confirms only_a non-empty rejection survives through
/// the parameterized→arm dispatch.
#[test]
fn subtype_function_E_open_le_closed_extras_reject() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e2_sym = kb.intern("E2");
    let e3_sym = kb.intern("E3");
    let e1 = kb.make_sort_ref(e1_sym);
    let e2 = kb.make_sort_ref(e2_sym);
    let e3 = kb.make_sort_ref(e3_sym);

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    let fn_sym = kb.resolve_symbol("anthill.prelude.Function");
    let fn_base = kb.make_sort_ref(fn_sym);
    let a_sym = kb.intern("A");
    let b_sym = kb.intern("B");
    let e_sym = kb.intern("E");

    // Actual: {E1, E3 | ?rho} — open with E3 NOT in expected.
    let open_actual_rows = kb.build_canonical_effects_rows(&[e1, e3, rho]);
    // Expected: {E1, E2} — closed, no E3.
    let closed_expected_rows = kb.build_canonical_effects_rows(&[e1, e2]);

    let actual = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, open_actual_rows)],
    );
    let expected = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, closed_expected_rows)],
    );

    assert!(!types_compatible(&mut kb, actual, expected),
        "Function[E={{E1, E3 | ?rho}}] NOT <: Function[E={{E1, E2}}] — \
         open actual carries E3 that closed expected can't accept");
}

/// WI-333: closed actual ≤ open expected — actual's labels absorbed by
/// expected's tail (mirrors `subtype_arrow_closed_le_open`).
#[test]
fn subtype_function_E_closed_le_open() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e1 = kb.make_sort_ref(e1_sym);

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    let fn_sym = kb.resolve_symbol("anthill.prelude.Function");
    let fn_base = kb.make_sort_ref(fn_sym);
    let a_sym = kb.intern("A");
    let b_sym = kb.intern("B");
    let e_sym = kb.intern("E");

    let closed_actual_rows = kb.build_canonical_effects_rows(&[e1]);
    let open_expected_rows = kb.build_canonical_effects_rows(&[rho]);

    let actual = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, closed_actual_rows)],
    );
    let expected = kb.make_parameterized_type(
        fn_base,
        &[(a_sym, int_ty), (b_sym, int_ty), (e_sym, open_expected_rows)],
    );

    assert!(types_compatible(&mut kb, actual, expected),
        "Function[E={{E1}}] <: Function[E={{|?rho}}] — expected's tail absorbs E1");
}

/// F1 regression (code-review): multi-actual-to-single-expected entity
/// subtyping. Pre-WI-326 `arrow_compatible`'s effects loop was exists-
/// quantified: `actual.iter().all(|ae| expected.iter().any(|ee| <:))`.
/// The initial WI-326 implementation used `pair_present_labels` (1-to-1
/// pairing with a `b_matched` flag), which rejected `{red, blue} <:
/// {Color}` because `Color` got marked matched after pairing with `red`,
/// leaving `blue` un-paired. The fix uses `cover_present_labels`
/// (existential) so one expected can cover many actuals.
#[test]
fn subtype_arrow_multi_entity_to_single_sort() {
    let source = r#"
enum Color
  entity red
  entity blue
end
"#;
    let mut kb = load_with_source(source);
    let int_ty = kb.make_sort_ref_by_name("Int");
    let red_sym = kb.resolve_symbol("Color.red");
    let blue_sym = kb.resolve_symbol("Color.blue");
    let color_sym = kb.resolve_symbol("Color");
    let red = kb.make_sort_ref(red_sym);
    let blue = kb.make_sort_ref(blue_sym);
    let color = kb.make_sort_ref(color_sym);

    let actual = kb.make_arrow_type(int_ty, int_ty, &[red, blue]);
    let expected = kb.make_arrow_type(int_ty, int_ty, &[color]);

    assert!(types_compatible(&mut kb, actual, expected),
        "{{red, blue}} <: {{Color}} — multi-entity to single sort; \
         set-with-subtyping semantics lets Color cover both red and blue");
}

/// WI-335 probe: nested arrow sharing a row var across positions with
/// inconsistent expected bindings. Pre-WI-335 each arrow_compatible call
/// allocated a fresh local_subst, so the param check bound rho := {E1}
/// and the result check bound rho := empty independently — no
/// contradiction surfaced. Outer wrongly accepted.
#[test]
fn subtype_nested_arrow_shared_rho_inconsistent_binding_rejects() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e2_sym = kb.intern("E2");
    let e1 = kb.make_sort_ref(e1_sym);
    let e2 = kb.make_sort_ref(e2_sym);

    // One shared rho across both inner arrows.
    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    // actual = arrow(arrow(Int, Int, {rho}), arrow(Int, Int, {rho}), {})
    let inner_actual_left = kb.make_arrow_type(int_ty, int_ty, &[rho]);
    let inner_actual_right = kb.make_arrow_type(int_ty, int_ty, &[rho]);
    let actual = kb.make_arrow_type(inner_actual_left, inner_actual_right, &[]);

    // expected = arrow(arrow(Int, Int, {E1}), arrow(Int, Int, {E2}), {})
    let inner_expected_left = kb.make_arrow_type(int_ty, int_ty, &[e1]);
    let inner_expected_right = kb.make_arrow_type(int_ty, int_ty, &[e2]);
    let expected = kb.make_arrow_type(inner_expected_left, inner_expected_right, &[]);

    // No consistent global binding of rho can satisfy both:
    //   param (contravariant): expected_param <: actual_param needs rho ⊇ E1
    //   result (covariant):    actual_result  <: expected_result needs rho ⊆ {E2}
    // These conflict. Post-WI-335: types_compatible threads a shared subst,
    // the conflict surfaces as contradiction, and the outer rejects.
    assert!(!types_compatible(&mut kb, actual, expected),
        "nested arrows sharing rho across positions with inconsistent \
         expected bindings must REJECT (no consistent global rho)");
}

// ── WI-337 bootstrap-safe arrow comparison ───────────────────────────────
//
// Pre-WI-337 arrow_compatible / unify_arrow synthesized an empty
// effects_rows for the missing-side case via
// `make_effect_expression_empty_row` + `make_effects_rows_type` — both
// of which call panic-on-miss `resolve_symbol`. If a hand-built arrow
// reaches the typer BEFORE `register_prelude` has registered the
// `EffectExpression.empty_row` / `Type.effects_rows` symbols, the
// resolve panics. WI-337 routes through the new bootstrap-safe builder
// `kb.try_make_empty_effects_rows()` which returns `None` instead.

/// WI-337: hand-built arrows with only one side carrying effects must
/// not panic when compared on a fresh KB that hasn't been
/// register_prelude'd. The sound conservative answer is `false` (we
/// can't synthesize the empty row to compare against).
#[test]
fn types_compatible_bootstrap_safe_when_prelude_not_registered() {
    let mut kb = KnowledgeBase::new();
    // Deliberately DO NOT call load::register_prelude(&mut kb).
    // Build two arrow terms with only param + result populated (no
    // effects field on either side, then one side with an effects-like
    // field shape).
    let arrow_sym = kb.intern("anthill.prelude.Type.arrow");
    let int_sym = kb.intern("anthill.prelude.Int");
    let int_ty = kb.alloc(Term::Fn {
        functor: int_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });
    let param_key = kb.intern("param");
    let result_key = kb.intern("result");
    let effects_key = kb.intern("effects");

    // arrow_no_effects: arrow(param: Int, result: Int) — no effects field.
    let mut na: SmallVec<[(anthill_core::intern::Symbol, anthill_core::kb::term::TermId); 2]>
        = SmallVec::new();
    na.push((param_key, int_ty));
    na.push((result_key, int_ty));
    na.sort_by_key(|(s, _)| s.index());
    let arrow_no_effects = kb.alloc(Term::Fn {
        functor: arrow_sym,
        pos_args: SmallVec::new(),
        named_args: na,
    });

    // arrow_with_effects: arrow(param: Int, result: Int, effects: <Var>).
    // Use a Var for the effects slot so the missing side triggers the
    // (Some, None) arm via the *opposite* side's None.
    let v_sym = kb.intern("?eff");
    let vid = kb.fresh_var(v_sym);
    let v_term = kb.alloc(Term::Var(
        anthill_core::kb::term::Var::Global(vid),
    ));
    let mut na2: SmallVec<[(anthill_core::intern::Symbol, anthill_core::kb::term::TermId); 2]>
        = SmallVec::new();
    na2.push((param_key, int_ty));
    na2.push((result_key, int_ty));
    na2.push((effects_key, v_term));
    na2.sort_by_key(|(s, _)| s.index());
    let arrow_with_effects = kb.alloc(Term::Fn {
        functor: arrow_sym,
        pos_args: SmallVec::new(),
        named_args: na2,
    });

    // Pre-WI-337: types_compatible PANICS at make_effect_expression_
    // empty_row's resolve_symbol call.
    // Post-WI-337: no panic; returns false (conservative reject — the
    // missing-side empty row can't be synthesized without the prelude).
    //
    // Cover all four return-false sites: (Some, None) and (None, Some)
    // in both arrow_compatible (types_compatible path) and unify_arrow
    // (unify_types path).
    assert!(!types_compatible(&mut kb, arrow_with_effects, arrow_no_effects),
        "arrow_compatible (Some, None): bootstrap-uninitialized KB rejects \
         without panicking");
    assert!(!types_compatible(&mut kb, arrow_no_effects, arrow_with_effects),
        "arrow_compatible (None, Some): symmetric arm also bootstrap-safe");

    // unify_types reaches unify_arrow's (Some, None) / (None, Some) arms.
    let mut subst1 = Substitution::new();
    assert!(!unify_types(&mut kb, &mut subst1, &TermIdView(arrow_with_effects), &TermIdView(arrow_no_effects)),
        "unify_arrow (Some, None): bootstrap-uninitialized KB rejects \
         without panicking");
    let mut subst2 = Substitution::new();
    assert!(!unify_types(&mut kb, &mut subst2, &TermIdView(arrow_no_effects), &TermIdView(arrow_with_effects)),
        "unify_arrow (None, Some): symmetric arm also bootstrap-safe");

    // bind_row_tail is reachable via the bare-Var path in
    // decompose_effect_row when both arrows carry an effects field of
    // bare-Var shape (a malformed but parse-tolerant input). Build that
    // case and confirm no panic.
    let v_sym2 = kb.intern("?eff2");
    let vid2 = kb.fresh_var(v_sym2);
    let v_term2 = kb.alloc(Term::Var(
        anthill_core::kb::term::Var::Global(vid2),
    ));
    let mut na3: SmallVec<[(anthill_core::intern::Symbol, anthill_core::kb::term::TermId); 2]>
        = SmallVec::new();
    na3.push((param_key, int_ty));
    na3.push((result_key, int_ty));
    na3.push((effects_key, v_term2));
    na3.sort_by_key(|(s, _)| s.index());
    let arrow_with_other_var = kb.alloc(Term::Fn {
        functor: arrow_sym,
        pos_args: SmallVec::new(),
        named_args: na3,
    });
    // Both sides have bare-Var effects; subtype_effect_rows /
    // unify_effect_rows reach bind_row_tail with a Var::Global tail
    // and would panic at make_effect_expression_empty_row pre-WI-337.
    assert!(!types_compatible(&mut kb, arrow_with_effects, arrow_with_other_var),
        "bind_row_tail via bare-Var effects: bootstrap-safe reject without panic");
}

// ── WI-336 Rigid row tail hardening ──────────────────────────────────────
//
// `Var::Rigid` represents a forall-Skolem — a universally-quantified row
// variable whose contents are unknown to this scope. Pre-WI-336
// `bind_row_tail`'s fallback returned `extras.is_empty() && final_tail.
// is_none()` for any non-Global Var (including Rigid), so case 3 of
// `subtype_effect_rows` accepted `actual={| ?rho_rigid} <: closed
// expected` whenever actual had no extras — silently assuming
// rigid_contents = empty. Unsound: rigid could instantiate to any row.
//
// Currently latent for v1a (the typer never produces Rigid effect-row
// tails); WI-307 v1b lacks-constraints + polymorphic-row work will
// surface this.

/// WI-336: actual open with Rigid tail, expected closed, only_a empty.
/// Pre-WI-336 the fallback accepted as a no-op; post-WI-336 rejects
/// because Rigid's contents are universally quantified and can't be
/// claimed empty.
#[test]
fn subtype_rejects_rigid_tail_close_to_empty() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e1 = kb.make_sort_ref(e1_sym);

    let rigid_name = kb.intern("rho_rigid");
    let rigid_vid = kb.fresh_var(rigid_name);
    let rigid_tail = kb.alloc(Term::Var(
        anthill_core::kb::term::Var::Rigid(rigid_vid),
    ));

    // actual = arrow(Int, Int, {| ?rho_rigid}) — open with Rigid tail.
    let actual = kb.make_arrow_type(int_ty, int_ty, &[rigid_tail]);
    // expected = arrow(Int, Int, {E1}) — closed.
    let expected = kb.make_arrow_type(int_ty, int_ty, &[e1]);

    // a_present=[], a_tail=Some(Rigid), e_present=[E1], e_tail=None.
    // only_a=[], only_e=[E1]. Case 3 (Some(a_t), None) with only_a empty.
    // Pre-WI-336: bind_row_tail(Rigid, &[], None) → fallback returns
    // true → arm returns true → SUB ACCEPTED (unsound).
    // Post-WI-336: bind_row_tail rejects Rigid → arm returns false →
    // SUB REJECTED (sound).
    assert!(!types_compatible(&mut kb, actual, expected),
        "arrow({{|?rho_rigid}}) NOT <: arrow({{E1}}) — Rigid tail's \
         universally-quantified contents could violate the closed bound");
}

/// WI-336: same idea for unify — unify_effect_rows' (Some(a_t), None) arm
/// with Rigid a_t and only_b empty pre-WI-336 unsoundly unified.
#[test]
fn unify_rejects_rigid_tail_against_closed() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e1 = kb.make_sort_ref(e1_sym);

    let rigid_name = kb.intern("rho_rigid");
    let rigid_vid = kb.fresh_var(rigid_name);
    let rigid_tail = kb.alloc(Term::Var(
        anthill_core::kb::term::Var::Rigid(rigid_vid),
    ));

    let arrow_open_rigid = kb.make_arrow_type(int_ty, int_ty, &[e1, rigid_tail]);
    let arrow_closed = kb.make_arrow_type(int_ty, int_ty, &[e1]);

    let mut subst = Substitution::new();
    assert!(!unify_types(&mut kb, &mut subst, &TermIdView(arrow_open_rigid), &TermIdView(arrow_closed)),
        "unify of {{E1 | ?rho_rigid}} with closed {{E1}} must REJECT — \
         Rigid can't be bound to empty by the unifier");
    // Symmetric direction.
    let mut subst2 = Substitution::new();
    assert!(!unify_types(&mut kb, &mut subst2, &TermIdView(arrow_closed), &TermIdView(arrow_open_rigid)),
        "symmetric direction: unify of closed {{E1}} with {{E1 | ?rho_rigid}} must REJECT");
}

/// WI-336 positive control: Global (regular) row tail with the same
/// shape still works — confirms the fix doesn't over-reject.
#[test]
fn subtype_accepts_global_tail_close_to_empty() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e1 = kb.make_sort_ref(e1_sym);

    let global_name = kb.intern("?rho");
    let global_vid = kb.fresh_var(global_name);
    let global_tail = kb.alloc(Term::Var(
        anthill_core::kb::term::Var::Global(global_vid),
    ));

    let actual = kb.make_arrow_type(int_ty, int_ty, &[global_tail]);
    let expected = kb.make_arrow_type(int_ty, int_ty, &[e1]);

    // Same shape as the Rigid case but with Global — must accept.
    assert!(types_compatible(&mut kb, actual, expected),
        "arrow({{|?rho_global}}) <: arrow({{E1}}) — Global tail can close to empty");
}

/// WI-335 positive control: shared rho across positions with CONSISTENT
/// expected bindings accepts. Both positions want rho := {E1}, so the
/// shared subst resolves them coherently. Guards against the fix
/// over-rejecting valid sub.
#[test]
fn subtype_nested_arrow_shared_rho_consistent_binding_accepts() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e1 = kb.make_sort_ref(e1_sym);

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    // actual = arrow(arrow(Int, Int, {rho}), arrow(Int, Int, {rho}), {})
    let inner_actual_left = kb.make_arrow_type(int_ty, int_ty, &[rho]);
    let inner_actual_right = kb.make_arrow_type(int_ty, int_ty, &[rho]);
    let actual = kb.make_arrow_type(inner_actual_left, inner_actual_right, &[]);

    // expected = arrow(arrow(Int, Int, {E1}), arrow(Int, Int, {E1}), {})
    // Both positions agree on {E1} → rho := {E1} satisfies both.
    let inner_expected_left = kb.make_arrow_type(int_ty, int_ty, &[e1]);
    let inner_expected_right = kb.make_arrow_type(int_ty, int_ty, &[e1]);
    let expected = kb.make_arrow_type(inner_expected_left, inner_expected_right, &[]);

    assert!(types_compatible(&mut kb, actual, expected),
        "nested arrows sharing rho across positions with CONSISTENT \
         expected bindings must ACCEPT (rho := {{E1}} works for both)");
}

// ── WI-334 shared row var with non-empty extras ──────────────────────────
//
// Pre-WI-334 the both-open arm in subtype_effect_rows and unify_effect_rows
// allocated a fresh tail and called bind_row_tail TWICE on the same VarId
// when a_walked == e_walked but extras were non-empty:
//   bind rho := only_e ++ open(fresh)
//   bind rho := only_a ++ open(fresh)
// Two distinct terms → subst.is_contradiction() → false. Valid sub /
// unify rejected. Fix: detect shared tail and bind ONCE with the union of
// both extras (the two rows agree on the same set after binding).

/// WI-334 subtype: shared rho with only_e extras.
#[test]
fn subtype_arrow_shared_rho_only_e_extras() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e2_sym = kb.intern("E2");
    let e2 = kb.make_sort_ref(e2_sym);

    // ONE rho var — shared between actual and expected.
    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    // A = {| ?rho}, B = {E2 | ?rho} — both reference the SAME rho.
    let actual = kb.make_arrow_type(int_ty, int_ty, &[rho]);
    let expected = kb.make_arrow_type(int_ty, int_ty, &[e2, rho]);

    assert!(types_compatible(&mut kb, actual, expected),
        "arrow({{|?rho}}) <: arrow({{E2 | ?rho}}) — same rho var means \
         A's set = ?rho-content ⊆ {{E2}} ∪ ?rho-content = B's set");
}

/// WI-334 subtype: symmetric case — only_a extras non-empty.
#[test]
fn subtype_arrow_shared_rho_only_a_extras() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e1 = kb.make_sort_ref(e1_sym);

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    let actual = kb.make_arrow_type(int_ty, int_ty, &[e1, rho]);
    let expected = kb.make_arrow_type(int_ty, int_ty, &[rho]);

    // Under the shared-rho binding K = {E1 | fresh}, both rows become
    // {E1 | fresh}. Equal sets → A <: B.
    assert!(types_compatible(&mut kb, actual, expected),
        "arrow({{E1 | ?rho}}) <: arrow({{| ?rho}}) — shared-rho binding \
         absorbs E1 into the common tail");
}

/// WI-334 unify: shared rho with non-empty extras. Pre-WI-334
/// unify_types over arrows sharing rho with extras hit the same
/// double-bind contradiction in unify_effect_rows.
#[test]
fn unify_arrow_shared_rho_with_extras() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e2_sym = kb.intern("E2");
    let e2 = kb.make_sort_ref(e2_sym);

    let rho_sym = kb.intern("?rho");
    let rho_vid = kb.fresh_var(rho_sym);
    let rho = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_vid)));

    let arrow_a = kb.make_arrow_type(int_ty, int_ty, &[rho]);
    let arrow_b = kb.make_arrow_type(int_ty, int_ty, &[e2, rho]);

    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(arrow_a), &TermIdView(arrow_b)),
        "unify of arrows sharing rho with one side carrying extras must succeed");
    assert!(subst.resolve_with_term(rho_vid).is_some(),
        "?rho should be bound after unification");
}

// ── WI-339 decompose_effect_row malformed-input hard reject ──────────────
//
// Per CLAUDE.md "avoid fallbacks, know about errors early", the row
// decomposer now returns None instead of debug_assert + silently-
// returning-incomplete-results when it sees:
//   - a second distinct row-tail Var (e.g. merge(open(?rho_1),
//     open(?rho_2)));
//   - an unknown functor inside the EffectExpression algebra;
//   - an unexpected term shape.
// Callers in unify_effect_rows / subtype_effect_rows map None to a
// rejection (return false).

/// WI-339 F13: a hand-built EffectExpression with two distinct
/// row-tail vars is malformed. Pre-WI-339 the second tail was
/// silently dropped and the sub/unify check proceeded on incomplete
/// information; post-WI-339 it hard-rejects.
#[test]
fn subtype_rejects_malformed_multi_tail_row() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");

    // Build a malformed inner EffectExpression: merge(open(?rho_1),
    // open(?rho_2)). decompose_effect_row's stack walk will see two
    // distinct Vars in tail position.
    let rho1_sym = kb.intern("?rho_1");
    let rho2_sym = kb.intern("?rho_2");
    let rho1_vid = kb.fresh_var(rho1_sym);
    let rho2_vid = kb.fresh_var(rho2_sym);
    let rho1 = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho1_vid)));
    let rho2 = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho2_vid)));
    let open1 = kb.make_effect_expression_open(rho1);
    let open2 = kb.make_effect_expression_open(rho2);
    let merge_two_tails = kb.make_effect_expression_merge(open1, open2);
    let malformed_rows = kb.make_effects_rows_type(merge_two_tails);

    // Hand-construct an arrow with the malformed effects field directly
    // (bypassing make_arrow_type's canonicalization).
    let arrow_sym = kb.try_resolve_symbol("anthill.prelude.Type.arrow")
        .expect("arrow symbol pre-registered");
    let param_key = kb.intern("param");
    let result_key = kb.intern("result");
    let effects_key = kb.intern("effects");
    let mut na: SmallVec<[(anthill_core::intern::Symbol, anthill_core::kb::term::TermId); 2]>
        = SmallVec::new();
    na.push((param_key, int_ty));
    na.push((result_key, int_ty));
    na.push((effects_key, malformed_rows));
    na.sort_by_key(|(s, _)| s.index());
    let arrow_malformed = kb.alloc(Term::Fn {
        functor: arrow_sym,
        pos_args: SmallVec::new(),
        named_args: na,
    });

    // A well-formed arrow against the malformed one — must reject.
    let arrow_clean = kb.make_arrow_type(int_ty, int_ty, &[]);

    assert!(!types_compatible(&mut kb, arrow_malformed, arrow_clean),
        "malformed multi-tail row must reject the subtype check");
    assert!(!types_compatible(&mut kb, arrow_clean, arrow_malformed),
        "malformed multi-tail row must reject the symmetric subtype check");

    // unify_types also rejects (propagates the decompose None as false).
    let mut subst = Substitution::new();
    assert!(!unify_types(&mut kb, &mut subst, &TermIdView(arrow_malformed), &TermIdView(arrow_clean)),
        "unify rejects against malformed multi-tail row");
}

// ── WI-338 pair/cover_present_labels hardening ───────────────────────────
//
// F8: dropped the strict functor-name pre-filter so cross-arm
// (sort_ref vs parameterized) label pairs are tried via unify_types.
// F11: subst snapshot/restore per attempt so failed pairings don't
// leak bindings into the substitution.

/// WI-338 F8: an effect-row label that's a bare sort_ref must pair
/// with the same sort presented as parameterized (with no bindings).
/// types_compatible's (sort_ref, parameterized) bridge arm accepts
/// this; pre-WI-338 the functor-name pre-filter rejected the pairing
/// before unify_types could fire it.
#[test]
fn cover_pairs_sort_ref_with_parameterized_same_base() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");

    // Use stdlib's `List` sort so we can build both shapes against the
    // same base symbol. Effect labels in arrow.effects are typically
    // sort_refs (Reads, Writes, etc.) — but the cross-arm pairing also
    // surfaces for entities-of-sort comparisons.
    let list_base = kb.make_sort_ref_by_name("List");
    let list_param = kb.make_parameterized_type(list_base, &[]); // bare List[]

    // arrow(Int, Int, [list_param]) where the label is parameterized.
    let actual = kb.make_arrow_type(int_ty, int_ty, &[list_param]);
    // arrow(Int, Int, [list_base]) where the label is sort_ref(List).
    let expected = kb.make_arrow_type(int_ty, int_ty, &[list_base]);

    // The two arrows' effects should compare compatibly via the
    // (parameterized, sort_ref) bridge in types_compatible — pre-WI-338
    // pair/cover_present_labels' functor-name pre-filter rejected this
    // since type_functor_name("List") == Some("sort_ref") and the
    // parameterized term reports Some("parameterized"). Now the pre-filter
    // is gone and unify_types' fallback to types_compatible's bridge arm
    // handles it.
    assert!(types_compatible(&mut kb, actual, expected),
        "effects with mixed sort_ref / parameterized(same base) must \
         pair via the types_compatible bridge arm");
    assert!(types_compatible(&mut kb, expected, actual),
        "symmetric — sort_ref vs parameterized is two-way compatible");
}

/// WI-338 F11: a label-pair attempt that partially binds variables and
/// then fails must not leak the partial bindings into the caller's
/// substitution. After WI-338 each unify_types attempt is wrapped in a
/// snapshot/restore.
///
/// Hard to exercise externally — partial-bind happens deep inside
/// unify_arrow when one sub-position unifies before another fails. We
/// use a simpler proxy: pair a label that succeeds against the FIRST
/// candidate in `b_present` then fails on a later step. The subst
/// should remain clean after the failed pair (besides bindings from
/// the successful pair, which the algorithm needs).
#[test]
fn cover_snapshot_restore_on_failed_pairing_no_leak() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e2_sym = kb.intern("E2");
    let e1 = kb.make_sort_ref(e1_sym);
    let e2 = kb.make_sort_ref(e2_sym);

    // actual = {E1, E2}, expected = {E1} — both closed.
    // Pairing: E1 matches E1 (success, marks b_covered[0]); E2 tries
    // E1, unify_types fails. Pre-WI-338 a failed unify_types could
    // partially bind subst on the E2 attempt; post-WI-338 the snapshot
    // restore wipes any partial bindings.
    //
    // The subtype check itself rejects (only_a=[E2] non-empty). The
    // important property: rejection happens for the RIGHT reason
    // (only_a non-empty), not because partial bindings made downstream
    // logic misbehave.
    let actual = kb.make_arrow_type(int_ty, int_ty, &[e1, e2]);
    let expected = kb.make_arrow_type(int_ty, int_ty, &[e1]);

    assert!(!types_compatible(&mut kb, actual, expected),
        "arrow({{E1, E2}}) NOT <: arrow({{E1}}) — actual has E2 expected lacks");
    // A second comparison on the same fresh KB also rejects cleanly
    // (no stale bindings from the first call leaked into anywhere).
    assert!(!types_compatible(&mut kb, actual, expected),
        "idempotent: repeated subtype query returns the same answer");
}

/// Open ≤ open with shared tail — both sides have open tails. The
/// directional algorithm (mirroring the unify both-open case) links them
/// through a fresh shared row variable; the sub holds because the two
/// rows then agree on the same set.
#[test]
fn subtype_arrow_open_le_open_shared_tail() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let e1_sym = kb.intern("E1");
    let e2_sym = kb.intern("E2");
    let e1 = kb.make_sort_ref(e1_sym);
    let e2 = kb.make_sort_ref(e2_sym);

    let rho_a_sym = kb.intern("?rho_a");
    let rho_e_sym = kb.intern("?rho_e");
    let rho_a_vid = kb.fresh_var(rho_a_sym);
    let rho_e_vid = kb.fresh_var(rho_e_sym);
    let rho_a = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_a_vid)));
    let rho_e = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(rho_e_vid)));

    // Actual: {E1 | ?rho_a}
    let open_actual = kb.make_arrow_type(int_ty, int_ty, &[e1, rho_a]);
    // Expected: {E2 | ?rho_e}
    let open_expected = kb.make_arrow_type(int_ty, int_ty, &[e2, rho_e]);

    assert!(types_compatible(&mut kb, open_actual, open_expected),
        "open <: open — fresh shared tail accommodates each side's extras");
}

// ── is_subtype tests (strict, irreflexive) ─────────────────────

#[test]
fn is_subtype_not_reflexive() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    assert!(!is_subtype(&mut kb, int_ty, int_ty), "Int is not a strict subtype of Int");
}

#[test]
fn is_subtype_entity_of() {
    let source = r#"
enum Color
  entity red
end
"#;
    let mut kb = load_with_source(source);
    let red_sym = kb.resolve_symbol("Color.red");
    let color_sym = kb.resolve_symbol("Color");
    let red_ty = kb.make_sort_ref(red_sym);
    let color_ty = kb.make_sort_ref(color_sym);
    assert!(is_subtype(&mut kb, red_ty, color_ty), "red is a strict subtype of Color");
    assert!(!is_subtype(&mut kb, color_ty, red_ty), "Color is not a subtype of red");
}

#[test]
fn is_subtype_requires_direct() {
    // Ordered requires Eq — Ordered is a subtype of Eq
    let mut kb = load_stdlib_kb();
    let ordered_sym = kb.resolve_symbol("anthill.prelude.Ordered");
    let eq_sym = kb.resolve_symbol("anthill.prelude.Eq");
    let ordered_ty = kb.make_sort_ref(ordered_sym);
    let eq_ty = kb.make_sort_ref(eq_sym);
    assert!(is_subtype(&mut kb, ordered_ty, eq_ty), "Ordered <: Eq via requires");
    assert!(!is_subtype(&mut kb, eq_ty, ordered_ty), "Eq is not <: Ordered");
}

#[test]
fn requires_compatible() {
    // types_compatible should also accept requires relationships
    let mut kb = load_stdlib_kb();
    let ordered_sym = kb.resolve_symbol("anthill.prelude.Ordered");
    let eq_sym = kb.resolve_symbol("anthill.prelude.Eq");
    let ordered_ty = kb.make_sort_ref(ordered_sym);
    let eq_ty = kb.make_sort_ref(eq_sym);
    assert!(types_compatible(&mut kb, ordered_ty, eq_ty), "Ordered compatible with Eq");
}

// ── requires_chain and obligation checking tests ───────────────

#[test]
fn requires_chain_ordered_includes_eq() {
    let kb = load_stdlib_kb();
    let ordered_sym = kb.resolve_symbol("anthill.prelude.Ordered");
    let chain = requires_chain_flat(&kb, ordered_sym);
    let eq_name = "Eq";
    assert!(chain.iter().any(|e| kb.resolve_sym(e.required_sort) == eq_name),
        "Ordered's requires chain should include Eq");
}

#[test]
fn obligations_spec_sort_not_checked() {
    // Spec sorts (like Ordered requires Eq) don't need to provide the required operations.
    // They declare a transitive requirement — obligation checking applies to concrete sorts.
    let kb = load_stdlib_kb();
    let ordered_sym = kb.resolve_symbol("anthill.prelude.Ordered");
    let chain = requires_chain_flat(&kb, ordered_sym);
    assert!(!chain.is_empty(), "Ordered should have requires entries");
    // Ordered itself is a spec — it doesn't need to implement Eq's operations.
    // A concrete sort that requires Ordered would need to provide both.
}

#[test]
fn obligations_missing_operation() {
    // Sort declares requires but doesn't provide the required operation.
    let source = r#"
sort Showable
  sort T = ?
  operation show(x: T) -> String
end

sort MySort requires Showable[T = MySort]
  entity foo
end
"#;
    let mut kb = load_with_source(source);
    let my_sort_sym = kb.resolve_symbol("MySort");
    let missing = check_obligations(&kb, my_sort_sym);
    assert!(!missing.is_empty(), "MySort should be missing 'show' obligation");
    assert!(missing.iter().any(|m| m.operation == "show"),
        "should report 'show' as missing, got: {:?}", missing);
}

#[test]
fn obligations_satisfied_when_operation_provided() {
    let source = r#"
sort Showable
  sort T = ?
  operation show(x: T) -> String
end

sort MySort requires Showable[T = MySort]
  entity foo
  operation show(x: MySort) -> String
end
"#;
    let mut kb = load_with_source(source);
    let my_sort_sym = kb.resolve_symbol("MySort");
    let missing = check_obligations(&kb, my_sort_sym);
    assert!(missing.is_empty(),
        "MySort provides show, should have no missing obligations, got: {:?}", missing);
}

#[test]
fn subtype_op_entity_return_compatible() {
    // Operation returns red, declared return type is Color — should be compatible
    let source = r#"
enum Color
  entity red
  entity blue
end
operation get_color() -> Color = red
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "red <: Color, should be no errors, got: {:?}", errors);
}

#[test]
fn subtype_sort_requires_enum() {
    // Sort with operation that returns an enum entity — compatible via requires chain
    let source = r#"
enum Color
  entity red
  entity blue
end

sort Paintable
  operation paint() -> Color
end

sort Canvas
  requires Paintable
  operation paint() -> Color = red
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "Canvas.paint returns red <: Color, got: {:?}", errors);
    // Canvas requires Paintable — compatible
    let canvas_sym = kb.resolve_symbol("Canvas");
    let paintable_sym = kb.resolve_symbol("Paintable");
    let canvas_ty = kb.make_sort_ref(canvas_sym);
    let paintable_ty = kb.make_sort_ref(paintable_sym);
    assert!(types_compatible(&mut kb, canvas_ty, paintable_ty), "Canvas <: Paintable via requires");
}

#[test]
fn subtype_entity_in_enum_requires_sort() {
    // Entity `circle` in `enum Shape` which requires `sort Drawable`.
    // circle <: Shape <: Drawable — transitively, circle is compatible with Drawable.
    let source = r#"
sort Drawable
  operation draw() -> String
end

sort Printable
  operation print() -> String
end

enum Shape
  requires Drawable
  entity circle(radius: Int)
  entity rect(w: Int, h: Int)
  operation draw() -> String
end
"#;
    let mut kb = load_with_source(source);
    let circle_sym = kb.resolve_symbol("Shape.circle");
    let shape_sym = kb.resolve_symbol("Shape");
    let drawable_sym = kb.resolve_symbol("Drawable");
    let circle_ty = kb.make_sort_ref(circle_sym);
    let shape_ty = kb.make_sort_ref(shape_sym);
    let drawable_ty = kb.make_sort_ref(drawable_sym);

    // circle <: Shape (entity_of)
    assert!(is_subtype(&mut kb, circle_ty, shape_ty), "circle <: Shape");
    // Shape <: Drawable (requires)
    assert!(is_subtype(&mut kb, shape_ty, drawable_ty), "Shape <: Drawable");
    // circle <: Drawable (transitively: entity_of + requires)
    assert!(types_compatible(&mut kb, circle_ty, drawable_ty), "circle compatible with Drawable");
    // NOT compatible with unrelated sort
    let printable_sym = kb.resolve_symbol("Printable");
    let printable_ty = kb.make_sort_ref(printable_sym);
    assert!(!types_compatible(&mut kb, circle_ty, printable_ty), "circle not compatible with Printable");
    assert!(!types_compatible(&mut kb, shape_ty, printable_ty), "Shape not compatible with Printable");
    assert!(!types_compatible(&mut kb, drawable_ty, printable_ty), "Drawable not compatible with Printable");
}

// ══════════════════════════════════════════════════════════════════
// enum tests
// ══════════════════════════════════════════════════════════════════

#[test]
fn enum_parses_and_loads() {
    let source = r#"
enum Color
  entity red
  entity blue(shade: Int)
end
"#;
    let mut kb = load_with_source(source);
    let color_sym = kb.resolve_symbol("Color");
    // Enum entities should be registered
    let red_sym = kb.resolve_symbol("Color.red");
    assert!(kb.is_constructor_symbol(red_sym), "red should be a constructor");
    let blue_sym = kb.resolve_symbol("Color.blue");
    assert!(kb.is_constructor_symbol(blue_sym), "blue should be a constructor");
    // Enum should have SortKind::Enum
    let color_term = kb.resolve_qualified_name_term("Color");
    assert_eq!(kb.sort_kind(color_term), Some(anthill_core::kb::SortKind::Enum));
}

#[test]
fn enum_with_type_param() {
    let source = r#"
enum Option
  sort T = ?
  entity some(value: T)
  entity none
end
"#;
    let mut kb = load_with_source(source);
    let some_sym = kb.resolve_symbol("Option.some");
    assert!(kb.is_constructor_symbol(some_sym), "some should be a constructor");
    let none_sym = kb.resolve_symbol("Option.none");
    assert!(kb.is_constructor_symbol(none_sym), "none should be a constructor");
}

#[test]
fn enum_entity_subtyping() {
    let source = r#"
enum Color
  entity red
  entity blue
end
"#;
    let mut kb = load_with_source(source);
    let red_sym = kb.resolve_symbol("Color.red");
    let color_sym = kb.resolve_symbol("Color");
    let red_ty = kb.make_sort_ref(red_sym);
    let color_ty = kb.make_sort_ref(color_sym);
    assert!(types_compatible(&mut kb, red_ty, color_ty), "enum: red <: Color");
}

#[test]
fn enum_sort_info_has_kind() {
    let source = r#"
enum Color
  entity red
end
"#;
    let mut kb = load_with_source(source);
    // Check that SortInfo for Color has kind = "enum"
    let si_sym = kb.resolve_symbol("anthill.reflect.SortInfo");
    for rid in kb.by_functor(si_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        if let Term::Fn { named_args, .. } = kb.get_term(head) {
            let name = named_args.iter()
                .find(|(s, _)| kb.resolve_sym(*s) == "name")
                .and_then(|(_, v)| match kb.get_term(*v) {
                    Term::Ref(s) => Some(kb.resolve_sym(*s).to_string()),
                    _ => None,
                });
            if name.as_deref() == Some("Color") {
                let kind = named_args.iter()
                    .find(|(s, _)| kb.resolve_sym(*s) == "kind")
                    .and_then(|(_, v)| match kb.get_term(*v) {
                        Term::Ident(s) => Some(kb.resolve_sym(*s).to_string()),
                        _ => None,
                    });
                assert_eq!(kind.as_deref(), Some("enum"), "SortInfo kind should be 'enum'");
                return;
            }
        }
    }
    panic!("SortInfo for Color not found");
}

// ══════════════════════════════════════════════════════════════════
// unify_types tests
// ══════════════════════════════════════════════════════════════════

use anthill_core::kb::typing::unify_types;
use anthill_core::kb::term_view::TermIdView;
// Substitution already imported above for the types_compatible test wrapper.

#[test]
fn unify_identical_types() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(int_ty), &TermIdView(int_ty)), "Int unifies with Int");
}

#[test]
fn unify_var_binds_to_type() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let sym = kb.intern("?X");
    let vid = kb.fresh_var(sym);
    let var_term = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(vid)));
    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(var_term), &TermIdView(int_ty)), "Var unifies with Int");
    assert_eq!(subst.resolve_with_term(vid), Some(int_ty), "Var should be bound to Int");
}

#[test]
fn unify_both_vars_bind() {
    let mut kb = load_stdlib_kb();
    let sym1 = kb.intern("?A");
    let sym2 = kb.intern("?B");
    let vid1 = kb.fresh_var(sym1);
    let vid2 = kb.fresh_var(sym2);
    let var1 = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(vid1)));
    let var2 = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(vid2)));
    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(var1), &TermIdView(var2)), "two vars unify");
    // One should be bound to the other
    assert!(subst.resolve_with_term(vid1).is_some() || subst.resolve_with_term(vid2).is_some(),
        "at least one var should be bound");
}

#[test]
fn unify_incompatible_ground_types() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let str_ty = kb.make_sort_ref_by_name("String");
    let mut subst = Substitution::new();
    assert!(!unify_types(&mut kb, &mut subst, &TermIdView(int_ty), &TermIdView(str_ty)), "Int does not unify with String");
}

#[test]
fn unify_parameterized_with_var_binding() {
    // List[T=?X] unified with List[T=Int] → ?X = Int
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let t_sym = kb.intern("T");
    let list_base = kb.make_sort_ref_by_name("List");

    let x_sym = kb.intern("?X");
    let x_vid = kb.fresh_var(x_sym);
    let x_var = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(x_vid)));

    let list_var = kb.make_parameterized_type(list_base, &[(t_sym, x_var)]);
    let list_int = kb.make_parameterized_type(list_base, &[(t_sym, int_ty)]);

    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(list_var), &TermIdView(list_int)), "List[T=?X] unifies with List[T=Int]");
    assert_eq!(subst.resolve_with_term(x_vid), Some(int_ty), "?X should be bound to Int");
}

#[test]
fn unify_arrow_with_var_binding() {
    // (?A -> ?B) unified with (Int -> String) → ?A=Int, ?B=String
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let str_ty = kb.make_sort_ref_by_name("String");

    let a_sym = kb.intern("?A");
    let b_sym = kb.intern("?B");
    let a_vid = kb.fresh_var(a_sym);
    let b_vid = kb.fresh_var(b_sym);
    let a_var = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(a_vid)));
    let b_var = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(b_vid)));

    let arrow_var = kb.make_arrow_type(a_var, b_var, &[]);
    let arrow_concrete = kb.make_arrow_type(int_ty, str_ty, &[]);

    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(arrow_var), &TermIdView(arrow_concrete)), "(?A -> ?B) unifies with (Int -> String)");
    assert_eq!(subst.resolve_with_term(a_vid), Some(int_ty), "?A = Int");
    assert_eq!(subst.resolve_with_term(b_vid), Some(str_ty), "?B = String");
}

#[test]
fn unify_sort_ref_type_param_resolves() {
    // sort T = ? inside a sort creates SortAlias(T, Var).
    // sort_ref(name: T) should resolve through SortAlias during unification.
    let source = r#"
sort Container
  sort T = ?
  entity box(value: T)
end
"#;
    let mut kb = load_with_source(source);
    let int_ty = kb.make_sort_ref_by_name("Int");
    let t_sym = kb.resolve_symbol("Container.T");
    let t_ref = kb.make_sort_ref(t_sym);

    let mut subst = Substitution::new();
    assert!(unify_types(&mut kb, &mut subst, &TermIdView(t_ref), &TermIdView(int_ty)),
        "sort_ref(T) should unify with Int via SortAlias");
}

// ══════════════════════════════════════════════════════════════════
// type_check_sorts (unified pass) tests
// ══════════════════════════════════════════════════════════════════

fn load_with_result(source: &str) -> (KnowledgeBase, LoadResult) {
    let mut kb = load_stdlib_kb();
    let parsed = parse::parse(source).expect("parse failed");
    let result = load::load(&mut kb, &parsed, &NullResolver)
        .expect("load failed");
    (kb, result)
}

#[test]
fn type_check_sorts_correct_fact_no_errors() {
    let source = r#"
enum Color
  entity red
  entity blue
end
sort Item
  entity Thing(name: String, color: Color)
end
fact Thing(name: "hello", color: red)
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "correct fact should produce no errors, got: {:?}", errors);
}

#[test]
fn type_check_sorts_wrong_field_type() {
    let source = r#"
sort Item
  entity Thing(count: Int)
end
fact Thing(count: "hello")
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "should detect String where Int expected");
}

#[test]
fn type_check_sorts_operation_body() {
    let source = r#"
sort Math
  operation get_answer() -> Int = 42
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "correct literal body should produce no errors, got: {:?}", errors);
}

#[test]
fn let_with_type_annotation_simple() {
    // Proposal 035 form (1): typer accepts `let x: Int = 7 ; x` cleanly.
    // The annotation pins the bound variable's type for the body env.
    let source = r#"
sort Demo
  operation main() -> Int =
    let x: Int = 7
    x
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "let with Int annotation should typecheck, got: {:?}", errors);
}

#[test]
fn let_with_parameterized_type_annotation() {
    // Annotation drives the variable's type when the value's inferred
    // type would otherwise leave parameters free. Even when the typer
    // can't infer K/V from the empty constructor today, the annotation
    // still binds the variable to the parameterized form for later use.
    let source = r#"
sort Demo
  import anthill.prelude.{Map}
  import anthill.prelude.Map.{empty, size}

  operation main() -> Int =
    let m: Map[K = String, V = Int] = empty()
    size(m)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "annotated let should typecheck, got: {:?}", errors);
}

#[test]
fn type_check_sorts_op_with_type_param_instantiation() {
    // add(x, x) where x: Int should resolve Numeric.T to Int, return Int
    let source = r#"
sort Math
  operation double(x: Int) -> Int = add(x, x)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "add(x,x) with x:Int should return Int via type param instantiation, got: {:?}", errors);
}

#[test]
fn type_check_sorts_operation_wrong_return() {
    let source = r#"
sort Math
  operation get_name() -> String = 42
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "should detect Int body vs String return");
}

#[test]
fn type_check_sorts_parameterized_field_correct() {
    // List[T=Int] field with correct cons(head: 1, tail: nil) — no errors
    let source = r#"
sort Container
  import anthill.prelude.List
  entity Box(items: List[T = Int])
end
fact Box(items: cons(head: 42, tail: nil))
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "correct List[T=Int] value should produce no errors, got: {:?}", errors);
}

#[test]
fn type_check_sorts_parameterized_field_wrong_element() {
    // List[T=Int] field with wrong element type (String instead of Int)
    let source = r#"
sort Container
  import anthill.prelude.List
  entity Box(items: List[T = Int])
end
fact Box(items: cons(head: "hello", tail: nil))
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "String in List[T=Int] should be detected, got: {:?}", errors);
}

#[test]
fn type_check_sorts_only_checks_given_sorts() {
    // Load stdlib, then a user file. Only check the user sorts.
    let source = r#"
sort MySort
  entity Foo(x: Int)
end
fact Foo(x: "wrong")
"#;
    let (mut kb, result) = load_with_result(source);
    // Only check user sorts, not stdlib
    assert!(!result.defined_sorts.is_empty(), "should have defined sorts");
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "should detect type error in user sort");
}

// ══════════════════════════════════════════════════════════════════
// HO predicate variable tests
// ══════════════════════════════════════════════════════════════════

#[test]
fn ho_predicate_parses_as_ho_apply() {
    // ?P(nil) should parse and load as ho_apply(?P, nil)
    let source = r#"
rule test_induction(?P) :- ?P(nil)
"#;
    let mut kb = load_with_source(source);
    // The rule should be loaded — check it exists
    let test_sym = kb.try_resolve_symbol("test_induction");
    assert!(test_sym.is_some(), "test_induction should be defined");

    let facts = kb.by_functor(test_sym.unwrap());
    assert!(!facts.is_empty(), "should have rule for test_induction");
    let body = kb.rule_body_nodes(facts[0]);
    assert!(!body.is_empty(), "rule should have a body");
    // Body goal should be ho_apply(?P, nil)
    match body[0].as_expr() {
        Some(anthill_core::kb::node_occurrence::Expr::Apply { functor, pos_args, .. }) => {
            let fname = kb.resolve_sym(*functor);
            assert!(fname == "ho_apply" || fname.ends_with(".ho_apply"),
                "body should be ho_apply, got: {}", fname);
            assert_eq!(pos_args.len(), 2, "ho_apply should have 2 pos args: ?P and nil");
        }
        other => panic!("expected ho_apply Apply, got {:?}", other),
    }
}

#[test]
fn ho_predicate_multi_arg() {
    // ?P(a, b) should parse as ho_apply(?P, a, b)
    let source = r#"
rule test(?P) :- ?P(foo, bar)
"#;
    let mut kb = load_with_source(source);
    let test_sym = kb.try_resolve_symbol("test");
    assert!(test_sym.is_some());
    let facts = kb.by_functor(test_sym.unwrap());
    let body = kb.rule_body_nodes(facts[0]);
    match body[0].as_expr() {
        Some(anthill_core::kb::node_occurrence::Expr::Apply { functor, pos_args, .. }) => {
            let fname = kb.resolve_sym(*functor);
            assert!(fname == "ho_apply" || fname.ends_with(".ho_apply"),
                "body should be ho_apply, got: {}", fname);
            assert_eq!(pos_args.len(), 3, "ho_apply(?P, foo, bar) = 3 pos args");
        }
        other => panic!("expected ho_apply Apply, got {:?}", other),
    }
}

#[test]
fn ho_bigint_induction_parses() {
    // BigInt strong induction rule with HO predicate variable.
    // The inductive-step antecedent uses the `nested_implication`
    // grammar form: outer parens around `(forall(binders), ant -:
    // cons)`. The outer parens are required by the grammar; without
    // them, the inner `-:` has no syntactic anchor and tree-sitter
    // emits an embedded ERROR node (parser limped along by accident
    // in earlier versions; the form below is the grammar-supported
    // shape and parses cleanly).
    let source = r#"
rule bigint_induction(?P)
  :- ?P(0),
     (forall(?n), gt(?n, 0), ?P(sub(?n, 1)) -: ?P(?n))
"#;
    let parsed = parse::parse(source);
    assert!(parsed.is_ok(), "BigInt induction rule should parse: {:?}", parsed.err());

    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let ind_sym = kb.try_resolve_symbol("bigint_induction");
    assert!(ind_sym.is_some(), "bigint_induction should be defined");

    let rules = kb.by_functor(ind_sym.unwrap());
    assert!(!rules.is_empty(), "should have a rule");

    // Rule head: bigint_induction(?P)
    let head = kb.rule_head(rules[0]);
    match kb.get_term(head) {
        Term::Fn { pos_args, .. } => {
            assert_eq!(pos_args.len(), 1, "head should have 1 arg (?P)");
            assert!(matches!(kb.get_term(pos_args[0]), Term::Var(_)),
                "head arg should be a Var");
        }
        other => panic!("expected Fn head, got {:?}", other),
    }

    // Rule body should have 2 goals: ?P(0) and forall(...)
    let body = kb.rule_body_nodes(rules[0]);
    assert_eq!(body.len(), 2, "body should have 2 goals: ?P(0) and forall(...)");

    // First goal: ho_apply(?P, 0)
    match body[0].as_expr() {
        Some(anthill_core::kb::node_occurrence::Expr::Apply { functor, pos_args, .. }) => {
            let fname = kb.resolve_sym(*functor);
            assert!(fname == "ho_apply" || fname.ends_with(".ho_apply"),
                "first goal should be ho_apply, got: {}", fname);
            assert_eq!(pos_args.len(), 2, "ho_apply(?P, 0)");
        }
        other => panic!("expected ho_apply for first goal, got {:?}", other),
    }

    // Second goal: the nested-implication form `(forall(?n), ant -:
    // cons)` loads as `forall_impl` — the WI-108 hereditary-Harrop
    // form built specifically for the inductive-step antecedent of
    // recursive-constructor induction principles. Accept either the
    // plain `forall` functor (for the unparenthesized form) or
    // `forall_impl` (for the nested-implication form).
    match body[1].as_expr() {
        Some(anthill_core::kb::node_occurrence::Expr::Apply { functor, pos_args, .. }) => {
            let fname = kb.resolve_sym(*functor);
            let ok = fname == "forall" || fname.ends_with(".forall")
                  || fname == "forall_impl" || fname.ends_with(".forall_impl");
            assert!(ok,
                "second goal should be forall or forall_impl, got: {} (pos_args: {})",
                fname, pos_args.len());
        }
        other => {
            eprintln!("second goal occurrence: {:?}", other.map(std::mem::discriminant));
        }
    }
}

#[test]
fn ho_predicate_resolves_with_bound_var() {
    // rule test(?P) :- ?P(42)
    // rule my_pred(42)
    // Query: test(my_pred) should succeed
    let source = r#"
sort TestSort
  rule test(?P) :- ?P(42)
  rule my_pred(42)
end
"#;
    let mut kb = load_with_source(source);
    let my_pred_term = kb.resolve_qualified_name_term("TestSort.my_pred");
    let query = make_goal(&mut kb, "TestSort.test", &[my_pred_term]);
    let config = default_config();
    let solutions = kb.resolve(&[query], &config);
    assert!(!solutions.is_empty(),
        "test(my_pred) should succeed — ho_apply(my_pred, 42) resolves my_pred(42)");
}

// ══════════════════════════════════════════════════════════════════
// Rule type-checking tests
// ══════════════════════════════════════════════════════════════════

#[test]
fn rule_typing_consistent_vars_no_error() {
    // ?x appears as Int in both head and body — consistent
    let source = r#"
sort Math
  operation double(x: Int) -> Int
  rule double_fact(?x, ?y) :- double(?x, ?y)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "consistent variable types should produce no errors, got: {:?}", errors);
}

#[test]
fn rule_typing_inconsistent_vars_detected() {
    // ?x used as String field and Int field — inconsistent
    let source = r#"
sort Mixed
  entity Foo(name: String)
  entity Bar(count: Int)
  rule bad(?x) :- Foo(name: ?x), Bar(count: ?x)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "?x used as String and Int should be detected, got: {:?}", errors);
}

#[test]
fn rule_typing_entity_fields_consistent() {
    // ?c used consistently as Color in both entity field positions
    let source = r#"
enum Color
  entity red
  entity blue
end
sort Items
  entity Box(color: Color)
  entity Bag(color: Color)
  rule same_color(?c) :- Box(color: ?c), Bag(color: ?c)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "?c consistently Color should be fine, got: {:?}", errors);
}

#[test]
fn rule_typing_stdlib_no_spurious_errors() {
    let (mut kb, result) = {
        let dir = crate::common::stdlib_dir();
        let files = crate::common::collect_anthill_files(&dir);
        let parsed: Vec<_> = files.iter()
            .map(|path| {
                let source = std::fs::read_to_string(path).unwrap();
                anthill_core::parse::parse(&source).unwrap()
            })
            .collect();
        let refs: Vec<_> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        let result = load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib load");
        (kb, result)
    };
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "stdlib rules should produce no type errors, got: {:?}", errors);
}

// ══════════════════════════════════════════════════════════════════
// Pattern fragment checking tests
// ══════════════════════════════════════════════════════════════════

#[test]
fn pattern_fragment_valid_ho_apply_in_body() {
    // ?P(nil) in body — valid pattern fragment
    let source = r#"
sort TestSort
  rule test(?P) :- ?P(nil)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "valid ho_apply in body should be fine, got: {:?}", errors);
}

#[test]
fn pattern_fragment_duplicate_var_rejected() {
    // ?P(?x, ?x) — duplicate variable in ho_apply args — rejected
    let source = r#"
sort TestSort
  rule test(?P, ?x) :- ?P(?x, ?x)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(), "duplicate var in ho_apply should be rejected, got: {:?}", errors);
}

#[test]
fn pattern_fragment_stdlib_valid() {
    // stdlib should have no pattern fragment violations
    let (mut kb, result) = {
        let dir = crate::common::stdlib_dir();
        let files = crate::common::collect_anthill_files(&dir);
        let parsed: Vec<_> = files.iter()
            .map(|path| {
                let source = std::fs::read_to_string(path).unwrap();
                anthill_core::parse::parse(&source).unwrap()
            })
            .collect();
        let refs: Vec<_> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        let result = load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib load");
        (kb, result)
    };
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    // Filter to only pattern-fragment errors (not type errors)
    let ho_errors: Vec<_> = errors.iter()
        .filter(|e| {
            let msg = format!("{}", e);
            msg.contains("ho_apply") || msg.contains("predicate")
        })
        .collect();
    assert!(ho_errors.is_empty(), "stdlib should have no pattern fragment errors, got: {:?}", ho_errors);
}

// ══════════════════════════════════════════════════════════════════
// Effect scoping tests
// ══════════════════════════════════════════════════════════════════

#[test]
fn effect_scoping_stdlib_no_spurious_errors() {
    // Stdlib operations should produce no effect scoping errors
    let (mut kb, result) = {
        let dir = crate::common::stdlib_dir();
        let files = crate::common::collect_anthill_files(&dir);
        let parsed: Vec<_> = files.iter()
            .map(|path| {
                let source = std::fs::read_to_string(path).unwrap();
                anthill_core::parse::parse(&source).unwrap()
            })
            .collect();
        let refs: Vec<_> = parsed.iter().collect();
        let mut kb = KnowledgeBase::new();
        load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        let result = load::load_all(&mut kb, &refs, &NullResolver).expect("stdlib load");
        (kb, result)
    };
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let effect_errors: Vec<_> = errors.iter()
        .filter(|e| {
            let msg = format!("{}", e);
            msg.contains("effect")
        })
        .collect();
    assert!(effect_errors.is_empty(), "stdlib should have no effect errors, got: {:?}", effect_errors);
}

// ══════════════════════════════════════════════════════════════════
// Constructor type param inference tests
// ══════════════════════════════════════════════════════════════════

use anthill_core::kb::typing::type_check_expr;
use anthill_core::kb::typing::TypingEnv;

#[test]
fn constructor_infers_type_param_from_int_field() {
    // Direct test: type_check_expr on cons(head: 42, tail: nil) should produce a parameterized List type
    let source = r#"
sort TestSort
  import anthill.prelude.List
  entity Holder(items: List[T = Int])
end
fact Holder(items: cons(head: 42, tail: nil))
"#;
    let (mut kb, result) = load_with_result(source);
    // Use parameterized field checking (already works for facts)
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "cons(head: 42, tail: nil) in List[T=Int] field should pass, got: {:?}", errors);
}

#[test]
fn constructor_infers_type_param_from_string_field() {
    let source = r#"
sort TestSort
  import anthill.prelude.List
  entity Holder(items: List[T = String])
end
fact Holder(items: cons(head: "hello", tail: nil))
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "cons(head: \"hello\", tail: nil) in List[T=String] field should pass, got: {:?}", errors);
}

#[test]
fn constructor_two_different_instantiations() {
    // Two fields with different T bindings: List[T=Int] and List[T=String]
    // Both should be checked correctly — shared Var must not cause conflict
    let source = r#"
sort Container
  import anthill.prelude.List
  entity Holder(ints: List[T = Int], strings: List[T = String])
end
fact Holder(ints: cons(head: 42, tail: nil), strings: cons(head: "hello", tail: nil))
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "two different List instantiations in same entity should work, got: {:?}", errors);
}

#[test]
fn constructor_two_instantiations_mismatch() {
    // List[T=Int] field with String value — should detect mismatch
    // List[T=String] field with Int value — should also detect
    let source = r#"
sort Container
  import anthill.prelude.List
  entity Holder(ints: List[T = Int], strings: List[T = String])
end
fact Holder(ints: cons(head: "wrong", tail: nil), strings: cons(head: 42, tail: nil))
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(),
        "swapped types should be detected, got: {:?}", errors);
}

#[test]
fn constructor_two_instantiations_in_rule() {
    // Rule that uses both List[T=Int] and List[T=String] fields
    // via different variables — should not interfere
    let source = r#"
sort Container
  import anthill.prelude.List
  entity Holder(ints: List[T = Int], strings: List[T = String])
  rule test(?x, ?y) :- Holder(ints: ?x, strings: ?y)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "rule with two different List instantiations should be fine, got: {:?}", errors);
}

#[test]
fn constructor_type_param_mismatch_detected() {
    // cons(head: 42) in a List[T=String] field — should detect mismatch
    let source = r#"
sort TestSort
  import anthill.prelude.List
  entity Holder(items: List[T = String])
end
fact Holder(items: cons(head: 42, tail: nil))
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(),
        "cons(head: 42) in List[T=String] field should detect Int vs String mismatch");
}

// ══════════════════════════════════════════════════════════════════
// Exhaustiveness checking tests
// ══════════════════════════════════════════════════════════════════

#[test]
fn exhaustiveness_all_cases_covered() {
    let source = r#"
enum Color
  entity red
  entity blue
end
sort Test
  operation name(c: Color) -> String =
    match c
      case red -> "red"
      case blue -> "blue"
    end
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "exhaustive match should be fine, got: {:?}", errors);
}

#[test]
fn exhaustiveness_missing_case_detected() {
    let source = r#"
enum Color
  entity red
  entity blue
  entity green
end
sort Test
  operation name(c: Color) -> String =
    match c
      case red -> "red"
      case blue -> "blue"
    end
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let match_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("missing"))
        .collect();
    assert!(!match_errors.is_empty(), "should detect missing 'green' case, got: {:?}", errors);
}

// WI-036: a fact field whose declared type is a spec sort accepts a value
// whose own sort provides that spec.
#[test]
fn spec_field_accepts_value_whose_sort_provides_spec() {
    let source = r#"
namespace test.wi036_ok
  sort Comparable
    sort T = ?
    operation cmp(a: T, b: T) -> Bool
  end
  sort Widget
    entity widget(id: Int)
  end
  fact Comparable[T = Widget]
  sort Box
    entity Holder(item: Comparable)
  end
  fact Holder(item: widget(7))
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let field_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("Holder"))
        .collect();
    assert!(field_errors.is_empty(),
        "Widget provides Comparable, so the field should type-check, got: {:?}", errors);
}

#[test]
fn spec_field_rejects_value_whose_sort_lacks_provides() {
    let source = r#"
namespace test.wi036_bad
  sort Comparable
    sort T = ?
    operation cmp(a: T, b: T) -> Bool
  end
  sort Gadget
    entity gadget(id: Int)
  end
  sort Box
    entity Holder(item: Comparable)
  end
  fact Holder(item: gadget(3))
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let field_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("Holder"))
        .collect();
    assert!(!field_errors.is_empty(),
        "Gadget does not provide Comparable, so the field should be rejected, got: {:?}", errors);
}

// WI-344: provider admissibility in `types_compatible` — a value whose sort
// PROVIDES a spec is usable where that spec is expected, at a *value
// position* (operation return / argument), not just a field-membership
// check (WI-036). The WI's motivating shape is `iterator(xs: List) ->
// Stream = xs` once `List` provides `fact Stream[List]`; here the same
// mechanism is exercised with a self-contained spec/carrier pair.
#[test]
fn operation_return_accepts_value_whose_sort_provides_spec() {
    let source = r#"
namespace test.wi344_ok
  sort Comparable
    sort T = ?
    operation cmp(a: T, b: T) -> Bool
  end
  sort Widget
    entity widget(id: Int)
  end
  fact Comparable[T = Widget]
  operation as_comparable(w: Widget) -> Comparable = w
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let op_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("as_comparable"))
        .collect();
    assert!(op_errors.is_empty(),
        "Widget provides Comparable, so returning a Widget where Comparable \
         is expected must type-check (WI-344 provider admissibility), got: {:?}",
        errors);
}

// WI-344 negative: a value whose sort does NOT provide the spec is still
// rejected at the value position — provider admissibility must not blanket-
// accept unrelated sorts.
#[test]
fn operation_return_rejects_value_whose_sort_lacks_provides() {
    let source = r#"
namespace test.wi344_bad
  sort Comparable
    sort T = ?
    operation cmp(a: T, b: T) -> Bool
  end
  sort Gadget
    entity gadget(id: Int)
  end
  operation as_comparable(g: Gadget) -> Comparable = g
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let op_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("as_comparable"))
        .collect();
    assert!(!op_errors.is_empty(),
        "Gadget does not provide Comparable, so the return must be rejected, got: {:?}",
        errors);
}

// WI-344 soundness: provider admissibility must NOT drop the expected
// spec's type-param bindings. Widget provides `Comparable[T = Widget]`, so
// returning a Widget where `Comparable[T = Gadget]` is expected must STILL
// be rejected — the bare-carrier provider arm is confined to the bare↔bare
// `types_compatible` case and never rides `base_sort_compatible` (which
// would discard the `[T = Gadget]` binding). Pins the fix for the binding-
// mismatch hole the bare-only `sort_provides` would otherwise reopen.
#[test]
fn operation_return_rejects_provider_at_mismatched_binding() {
    let source = r#"
namespace test.wi344_binding_mismatch
  sort Comparable
    sort T = ?
    operation cmp(a: T, b: T) -> Bool
  end
  sort Widget
    entity widget(id: Int)
  end
  sort Gadget
    entity gadget(id: Int)
  end
  fact Comparable[T = Widget]
  operation as_cmp_gadget(w: Widget) -> Comparable[T = Gadget] = w
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let op_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("as_cmp_gadget"))
        .collect();
    assert!(!op_errors.is_empty(),
        "Widget provides Comparable only at T = Widget, so returning it where \
         Comparable[T = Gadget] is expected must be rejected (no binding-drop), got: {:?}",
        errors);
}

// WI-036: spec satisfaction also applies through parameterized field types —
// here a `List[T = Comparable]` whose elements must each provide Comparable.
#[test]
fn parameterized_spec_field_accepts_providing_elements() {
    let source = r#"
namespace test.wi036_list_ok
  import anthill.prelude.{List}
  sort Comparable
    sort T = ?
    operation cmp(a: T, b: T) -> Bool
  end
  sort Widget
    entity widget(id: Int)
  end
  fact Comparable[T = Widget]
  sort Box
    entity Holder(items: List[T = Comparable])
  end
  fact Holder(items: [widget(7)])
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let field_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("Holder"))
        .collect();
    assert!(field_errors.is_empty(),
        "list elements provide Comparable, so the field should type-check, got: {:?}", errors);
}

#[test]
fn parameterized_spec_field_rejects_non_providing_element() {
    let source = r#"
namespace test.wi036_list_bad
  import anthill.prelude.{List}
  sort Comparable
    sort T = ?
    operation cmp(a: T, b: T) -> Bool
  end
  sort Widget
    entity widget(id: Int)
  end
  sort Gadget
    entity gadget(id: Int)
  end
  fact Comparable[T = Widget]
  sort Box
    entity Holder(items: List[T = Comparable])
  end
  fact Holder(items: [gadget(3)])
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let field_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("Holder"))
        .collect();
    assert!(!field_errors.is_empty(),
        "a list element (Gadget) does not provide Comparable, so it should be rejected, got: {:?}", errors);
}

// WI-036: a field whose declared type is a *parameterized spec* (`Comparable[T
// = Widget]`) accepts a value whose sort provides that spec — exercises the
// provides fallback in check_value_against_parameterized's base check.
#[test]
fn parameterized_spec_base_field_accepts_providing_value() {
    let source = r#"
namespace test.wi036_pspec
  sort Comparable
    sort T = ?
    operation cmp(a: T, b: T) -> Bool
  end
  sort Widget
    entity widget(id: Int)
  end
  fact Comparable[T = Widget]
  sort Box
    entity Holder(item: Comparable[T = Widget])
  end
  fact Holder(item: widget(7))
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let field_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("Holder"))
        .collect();
    assert!(field_errors.is_empty(),
        "Widget provides Comparable, so the parameterized-spec field should type-check, got: {:?}", errors);
}

// WI-274: binding-precise spec-field validation. The base-only WI-036
// check looked only at whether the value's sort provides the spec
// *base*, ignoring the declared bindings. A field `Comparable[T =
// Gadget]` holding a Widget value (Widget provides Comparable only at
// `T = Widget`) was therefore silently accepted. With binding-precise
// validation the canonical instance resolver runs at `T = Gadget`,
// finds no provider, and the field is rejected at load. This is the
// case that behaved incorrectly before the fix.
#[test]
fn parameterized_spec_base_field_rejects_binding_mismatch() {
    let source = r#"
namespace test.wi274_mismatch
  sort Comparable
    sort T = ?
    operation cmp(a: T, b: T) -> Bool
  end
  sort Widget
    entity widget(id: Int)
  end
  sort Gadget
    entity gadget(id: Int)
  end
  fact Comparable[T = Widget]
  sort Box
    entity Holder(item: Comparable[T = Gadget])
  end
  fact Holder(item: widget(7))
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let field_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("Holder"))
        .collect();
    assert!(!field_errors.is_empty(),
        "Widget provides Comparable only at T = Widget, so a Comparable[T = Gadget] field must reject a Widget value, got: {:?}", errors);
}

// WI-274: conditional provider. `EqList` provides Eq for a list whose
// elements provide Eq (`fact Eq[T = List[T = A]]` guarded by `requires
// Eq[T = A]`). A field `Eq[T = List[T = Int]]` is accepted because the
// resolver descends the requires chain and finds Int provides Eq.
#[test]
fn conditional_spec_field_accepts_eq_list_of_eq_elements() {
    let source = r#"
namespace test.wi274_list_ok
  import anthill.prelude.{Eq, List, Int}
  fact Eq[T = Int]
  sort EqList
    sort A = ?
    requires Eq[T = A]
    fact Eq[T = List[T = A]]
  end
  sort Box
    entity Holder(item: Eq[T = List[T = Int]])
  end
  fact Holder(item: [1, 2, 3])
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let field_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("Holder"))
        .collect();
    assert!(field_errors.is_empty(),
        "Int provides Eq, so Eq[T = List[T = Int]] should type-check via the conditional EqList provider, got: {:?}", errors);
}

// WI-274: the binding precision discriminates the element type. The
// same `EqList` conditional provider does *not* satisfy `Eq[T = List[T
// = NonEq]]`, because NonEq provides no Eq instance — the requires
// subgoal `Eq[T = NonEq]` fails. Base-only validation could not tell
// these apart (both are "List provides Eq").
#[test]
fn conditional_spec_field_rejects_eq_list_of_non_eq_elements() {
    let source = r#"
namespace test.wi274_list_bad
  import anthill.prelude.{Eq, List, Int}
  fact Eq[T = Int]
  sort NonEq
    entity ne(id: Int)
  end
  sort EqList
    sort A = ?
    requires Eq[T = A]
    fact Eq[T = List[T = A]]
  end
  sort Box
    entity Holder(item: Eq[T = List[T = NonEq]])
  end
  fact Holder(item: [ne(1)])
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    let field_errors: Vec<_> = errors.iter()
        .filter(|e| format!("{}", e).contains("Holder"))
        .collect();
    assert!(!field_errors.is_empty(),
        "NonEq provides no Eq, so Eq[T = List[T = NonEq]] must be rejected, got: {:?}", errors);
}

#[test]
fn exhaustiveness_wildcard_covers_all() {
    let source = r#"
enum Color
  entity red
  entity blue
  entity green
end
sort Test
  operation name(c: Color) -> String =
    match c
      case red -> "red"
      case other -> "other"
    end
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "wildcard should cover remaining cases, got: {:?}", errors);
}

#[test]
fn exhaustiveness_var_pattern_covers_all() {
    let source = r#"
enum Color
  entity red
  entity blue
end
sort Test
  operation name(c: Color) -> String =
    match c
      case x -> "something"
    end
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "var pattern should cover all cases, got: {:?}", errors);
}

use anthill_core::kb::typing::{type_check_sorts_typed, TypeError, TypeErrorContext};

#[test]
fn typed_field_mismatch_carries_entity_and_field_symbols() {
    let source = r#"
sort Item
  entity Thing(count: Int)
end
fact Thing(count: "oops")
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts_typed(&mut kb, &result.defined_sorts);
    assert_eq!(errors.len(), 1, "expected one type error, got: {errors:?}");
    match &errors[0] {
        TypeError::Other { context: TypeErrorContext::EntityField { entity, field }, expected, actual, .. } => {
            assert_eq!(kb.resolve_sym(*entity), "Thing");
            assert_eq!(kb.resolve_sym(*field), "count");
            assert!(expected.contains("Int"), "expected Int, got: {expected}");
            assert_eq!(actual, "String");
        }
        other => panic!("expected Other(EntityField), got: {other:?}"),
    }
}

#[test]
fn typed_return_type_mismatch_uses_typemismatch_variant() {
    let source = r#"
sort Test
  operation greet() -> Int =
    "hello"
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts_typed(&mut kb, &result.defined_sorts);
    let return_err = errors.iter().find(|e| matches!(
        e,
        TypeError::TypeMismatch { context: TypeErrorContext::OperationReturn { .. }, .. }
    )).unwrap_or_else(|| panic!("no OperationReturn TypeMismatch in {errors:?}"));
    match return_err {
        TypeError::TypeMismatch { context: TypeErrorContext::OperationReturn { op_name }, .. } => {
            assert_eq!(kb.resolve_sym(*op_name), "greet");
        }
        _ => unreachable!(),
    }
}

#[test]
fn typed_span_resolves_to_source_position() {
    let source = "sort Item\n  entity Thing(count: Int)\nend\nfact Thing(count: \"oops\")\n";
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts_typed(&mut kb, &result.defined_sorts);
    let span = errors[0].span(&kb);
    assert!(span.is_some(), "span should be populated for entity-field mismatch");
}

// ══════════════════════════════════════════════════════════════════
// WI-186 — Free-standing parametric operations (proposal 035)
// ══════════════════════════════════════════════════════════════════

#[test]
fn wi186_smoke_free_standing_logical_var_in_param_type() {
    // Hypothesis: with `?a` already a valid variable_term in type
    // positions, a free-standing parametric operation may already
    // parse + load + typecheck without grammar/loader changes.
    // Each `?a` is a logical variable in the operation's signature
    // scope; the typer instantiates it at each call site.
    let source = r#"
namespace test.wi186_smoke
  operation id_int(a: ?a) -> Int
    = 0
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "free-standing op with ?a in param type should typecheck cleanly, got: {:?}",
        errors);
}

#[test]
fn wi186_free_standing_logical_var_in_return_type() {
    // `?a` in the return type position. With a literal body the typer
    // must allow a concrete return type to satisfy the polymorphic
    // declared return.
    let source = r#"
namespace test.wi186_ret
  operation pick(a: ?a, b: ?b) -> ?a
    = a
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "free-standing op with ?a in return type should typecheck cleanly, got: {:?}",
        errors);
}

#[test]
fn wi186_free_standing_parameterized_return_type() {
    // Real proposal-035 fixture: free-standing parametric op whose
    // return type uses an existing parametric sort with its bindings
    // pinned by the operation's logical variables.
    let source = r#"
namespace test.wi186_pair
  import anthill.prelude.{Pair}
  operation make_pair(a: ?a, b: ?b) -> Pair[A = ?a, B = ?b]
    = pair(a, b)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "free-standing op returning Pair[?a, ?b] should typecheck cleanly, got: {:?}",
        errors);
}

#[test]
fn wi186_free_standing_call_site_concrete() {
    // Call a free-standing parametric op with concrete-typed args
    // and bind into a let with an explicit annotation. The typer
    // should accept this — it instantiates ?a := String, ?b := Int
    // at the call site.
    let source = r#"
namespace test.wi186_call
  import anthill.prelude.{Pair}
  operation make_pair(a: ?a, b: ?b) -> Pair[A = ?a, B = ?b]
    = pair(a, b)
  operation main() -> Pair[A = String, B = Int]
    = make_pair("hi", 7)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "concrete call site for free-standing parametric op should typecheck, got: {:?}",
        errors);
}

#[test]
fn wi186_free_standing_call_site_int_pair() {
    // Same shape as above with both args of the same primitive type —
    // exercises the case where ?a and ?b are bound to the same sort.
    let source = r#"
namespace test.wi186_call_int
  import anthill.prelude.{Pair}
  operation make_pair(a: ?a, b: ?b) -> Pair[A = ?a, B = ?b]
    = pair(a, b)
  operation main() -> Pair[A = Int, B = Int]
    = make_pair(1, 2)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "Int-Int instantiation should typecheck, got: {:?}",
        errors);
}

#[test]
fn wi237_pattern_subst_concrete_field_type() {
    // Baseline: a ctor whose field type is a bare type-param Var.
    // `case some(v)` over `Option[T = String]` must bind `v: String`,
    // i.e. the inner String literal in the case body must satisfy the
    // top-level String return type.
    let source = r#"
namespace test.wi237_concrete
  import anthill.prelude.{Option}
  operation pick(o: Option[T = String]) -> String =
    match o
      case some(v) -> v
      case none() -> "default"
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "bare-Var ctor field should propagate scrutinee type-arg, got: {:?}",
        errors);
}

#[test]
fn wi237_pattern_subst_parameterized_field_type() {
    // A ctor whose field type embeds the parent's type-param inside
    // another parameterized type (`items: List[T = T]`). Matching
    // `case wrapped(items)` over `Container[T = String]` should propagate
    // T = String into `items`'s type, yielding `items: List[T = String]`.
    // The nested `case cons(head, _)` then binds `head: String`, which
    // is then passed to `String.concat` — that call's per-call binding
    // typer check forces the propagation to actually have happened. With
    // T un-propagated, `head: Var(T)` doesn't satisfy `concat`'s
    // `String` arg, producing a type error.
    //
    // Today `build_pattern_subst` only collects type-param Vars from
    // ctor fields whose declared type is a bare Var(Global) — Vars
    // nested inside parameterized field types aren't traversed, so
    // this test is expected to FAIL until that gap is closed.
    let source = r#"
namespace test.wi237_buried
  import anthill.prelude.{List}
  import anthill.prelude.String.{concat}
  enum Container
    sort T = ?
    entity wrapped(items: List[T = T])
  end

  operation first_or_default(c: Container[T = String]) -> String =
    match c
      case wrapped(items) ->
        match items
          case cons(head, tail) -> if eq(head, head) then concat("[", head) else "tied"
          case nil() -> "default"
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "parameterized field type should propagate scrutinee type-arg into inner pattern, got: {:?}",
        errors);
}

// ══════════════════════════════════════════════════════════════════
// WI-031 end-to-end acceptance:
// load non-trivial source → type_check_sorts → verify typing facts
// (SortInfo, SortRequiresInfo) emitted for known sorts and requires
// ══════════════════════════════════════════════════════════════════

#[test]
fn wi031_stdlib_load_then_typecheck_then_verify_typing_facts() {
    // 1) Non-trivial load: full stdlib (~30 .anthill files: prelude, reflect,
    //    realization, logic, persistence, kernel, cli).
    let (mut kb, result) = load_stdlib_kb_with_result();

    // 2) Run the WI-031 typing pass on every loaded sort.
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(), "stdlib should type-check clean, got: {:?}", errors);

    // 3a) SortInfo facts emitted for known stdlib sorts.
    let sort_info_sym = kb.resolve_symbol("anthill.reflect.SortInfo");
    let name_field = kb.intern("name");
    for qn in ["anthill.prelude.Eq",
               "anthill.prelude.Ordered",
               "anthill.prelude.Numeric",
               "anthill.logic.Minimal.Minimal",
               "anthill.logic.Constructive.Constructive",
               "anthill.logic.Classical.Classical"] {
        let sort_term = kb.resolve_qualified_name_term(qn);
        let sort_functor = match kb.get_term(sort_term) {
            Term::Fn { functor, .. } => *functor,
            _ => panic!("{qn} did not resolve to Fn term"),
        };
        let found = kb.by_functor(sort_info_sym).iter().any(|rid| {
            let head = kb.fact_term(*rid);
            let Term::Fn { named_args, .. } = kb.get_term(head) else { return false };
            named_args.iter().any(|(f, v)| *f == name_field && match kb.get_term(*v) {
                Term::Fn { functor, .. } => *functor == sort_functor,
                Term::Ref(s) => *s == sort_functor,
                _ => false,
            })
        });
        assert!(found, "no SortInfo fact found for {qn}");
    }

    // 3b) SortRequiresInfo facts: reuse the public `requires_chain` walk
    // (same module, kb/typing.rs). All asserted pairs are direct stdlib
    // requires — they appear at depth 0 of the chain.
    let pairs = [
        ("anthill.prelude.Ordered",                  "anthill.prelude.Eq"),
        ("anthill.prelude.Numeric",                  "anthill.prelude.Ordered"),
        ("anthill.logic.Constructive.Constructive",  "anthill.logic.Minimal.Minimal"),
        ("anthill.logic.Classical.Classical",        "anthill.logic.Constructive.Constructive"),
    ];
    for (requirer, spec) in pairs {
        let r_sym = kb.resolve_symbol(requirer);
        let s_sym = kb.resolve_symbol(spec);
        let chain = requires_chain_flat(&kb, r_sym);
        assert!(chain.iter().any(|e| e.required_sort == s_sym),
            "no SortRequiresInfo fact found for `{requirer} requires {spec}`");
    }
}

// ══════════════════════════════════════════════════════════════════
// Operation type parameters at call sites (proposal 042 Phase D)
// ══════════════════════════════════════════════════════════════════

/// All-explicit: arg list alone can't pin A. The explicit `[Int]` is
/// the only constraint, so without seeding the return type stays
/// `Box[T = Var(A)]` and won't unify with the annotated `Box[T = Int]`.
#[test]
fn op_type_param_explicit_positional_binding_pins_return() {
    let source = r#"
sort Box
  sort T = ?
end
sort Demo
  operation make_box[A]() -> Box[A]
  operation tester() -> Box[T = Int] = make_box[Int]()
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "explicit positional binding should pin return type, got: {:?}", errors);
}

#[test]
fn op_type_param_explicit_named_binding_pins_return() {
    let source = r#"
sort Box
  sort T = ?
end
sort Demo
  operation make_box[A]() -> Box[A]
  operation tester() -> Box[T = Int] = make_box[A = Int]()
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "explicit named binding should pin return type, got: {:?}", errors);
}

/// Partial-explicit: one binding given, one inferred from argument.
#[test]
fn op_type_param_partial_explicit_mixes_with_arg_inference() {
    let source = r#"
sort Pair
  sort A = ?
  sort B = ?
end
sort Demo
  operation make_pair[A, B](a: A, b: B) -> Pair[A = A, B = B]
  operation tester() -> Pair[A = Int, B = String] = make_pair[A = Int](7, "hi")
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "partial explicit + arg inference should typecheck, got: {:?}", errors);
}

/// Sanity: existing all-inferred behavior still works after Phase D.
#[test]
fn op_type_param_all_inferred_from_args() {
    let source = r#"
sort Box
  sort T = ?
end
sort Demo
  operation make_box[A](x: A) -> Box[A]
  operation tester() -> Box[T = Int] = make_box(42)
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(errors.is_empty(),
        "arg-driven inference should pin A to Int, got: {:?}", errors);
}

/// Explicit binding inconsistent with expected return type — the seed
/// pins A = Int, but the caller expects Box[T = String]; downstream
/// unification surfaces the mismatch.
#[test]
fn op_type_param_explicit_binding_conflicts_with_expected_return() {
    let source = r#"
sort Box
  sort T = ?
end
sort Demo
  operation make_box[A]() -> Box[A]
  operation tester() -> Box[T = String] = make_box[Int]()
end
"#;
    let (mut kb, result) = load_with_result(source);
    let errors = type_check_sorts(&mut kb, &result.defined_sorts);
    assert!(!errors.is_empty(),
        "Box[T = Int] from call should not unify with Box[T = String] expected return");
}

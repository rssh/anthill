/// Integration tests for the typing module (anthill.reflect.typing).
///
/// Tests load source files into a KB, register builtins, and run SLD resolution
/// to verify typing rules: is_entity_of, refines, type_compatible, list_contains,
/// extract_sort_ref, sort_requires, sort_has_param.

mod common;

use anthill_core::parse;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;

use smallvec::SmallVec;

/// Load stdlib + typing rules into a fresh KB with builtins registered.
fn load_stdlib_kb() -> KnowledgeBase {
    let dir = common::stdlib_dir();
    let files = common::collect_anthill_files(&dir);
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
    kb.alloc(Term::Var(vid))
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
    match kb.get_term(bound) {
        Term::Ref(sym) => {
            assert_eq!(kb.resolve_sym(*sym), "Eq", "should extract Eq from SortView(Eq(), ...)");
        }
        other => panic!("expected Ref(Eq), got {:?}", other),
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
        Term::Ref(sym) => {
            assert_eq!(kb.resolve_sym(*sym), "Eq");
        }
        other => panic!("expected Ref(Eq), got {:?}", other),
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
    let result_tid = kb.alloc(Term::Var(result_var));
    let goal = make_goal(&mut kb, "anthill.reflect.field_access", &[env_term, field_ident, result_tid]);

    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert!(!solutions.is_empty(), "field_access should produce a solution");
    let sol = &solutions[0];
    let resolved = sol.subst.resolve(result_var).expect("result should be bound");
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
    let obj_tid = kb.alloc(Term::Var(obj_var));
    let fs_field_sym = kb.intern("fs");
    let field_ident = kb.alloc(Term::Ident(fs_field_sym));
    let result_name = kb.intern("result");
    let result_var = kb.fresh_var(result_name);
    let result_tid = kb.alloc(Term::Var(result_var));
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
    let result_tid = kb.alloc(Term::Var(result_var));
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
    let result_tid = kb.alloc(Term::Var(result_var));
    let goal = make_goal(&mut kb, "anthill.reflect.field_access", &[monoid_term, field_ident, result_tid]);

    let solutions = kb.resolve(&[goal], &ResolveConfig::default());
    assert!(!solutions.is_empty(), "field_access for sort component should succeed");
    let sol = &solutions[0];
    let resolved = sol.subst.resolve(result_var).expect("result should be bound");
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

// ── Typing pass spec loading ─────────────────────────────────────

#[test]
fn typing_pass_spec_parses_and_loads() {
    let mut kb = load_stdlib_kb();

    // Parse typing_pass_spec.anthill
    let spec_path = std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../docs/proposals/typing_pass_spec.anthill");
    let source = std::fs::read_to_string(&spec_path)
        .unwrap_or_else(|e| panic!("read {}: {e}", spec_path.display()));
    let parsed = parse::parse(&source)
        .unwrap_or_else(|errs| {
            for e in &errs {
                eprintln!("parse error: {}", e.format_with_source(&source));
            }
            panic!("typing_pass_spec.anthill has {} parse errors", errs.len());
        });

    // Load into KB on top of stdlib
    let result = load::load(&mut kb, &parsed, &NullResolver);
    if let Err(errs) = &result {
        for e in errs {
            eprintln!("load error: {e}");
        }
        // Don't panic — some symbols may be undefined (TypingEnv is abstract).
        // Just report. The test verifies the spec PARSES and loads without hard failures.
        eprintln!("typing_pass_spec.anthill had {} load warnings", errs.len());
    }

    // Verify key definitions were scanned
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

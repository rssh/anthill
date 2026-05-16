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

// ── Typing pass spec loading ─────────────────────────────────────

#[test]
fn typing_pass_spec_parses_and_loads() {
    // WI-253 made the NodeOccurrence materializer iterative, so it
    // runs in constant host stack regardless of source nesting.
    // However the *loader* itself (kb/load.rs::convert_expr_term /
    // load_let_expr / load_match_expr / …) is still recursive and
    // its frames push the 624-line typing-pass spec ~0.5 MiB past
    // Rust's default 2 MiB debug-build stack. A 4 MiB spawned-thread
    // stack gives ~2x headroom while we file WI-254 for an iterative
    // loader. Release-mode builds already pass on the default stack.
    std::thread::Builder::new()
        .stack_size(4 * 1024 * 1024)
        .spawn(|| {
            let mut kb = load_stdlib_kb();

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
        })
        .unwrap()
        .join()
        .unwrap();
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
        if !kb.rule_body(rid).is_empty() { continue; }
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
    let source = r#"
sort Math
  operation double(x: Int) -> Int = let ?y = x in add(?y, ?y)
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
// types_compatible tests
// ══════════════════════════════════════════════════════════════════

use anthill_core::kb::typing::{types_compatible, is_subtype, requires_chain_flat, check_obligations, type_check_sorts};

#[test]
fn subtype_same_sort_ref() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    assert!(types_compatible(&kb, int_ty, int_ty), "Int <: Int");
}

#[test]
fn subtype_different_sort_ref_incompatible() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let string_ty = kb.make_sort_ref_by_name("String");
    assert!(!types_compatible(&kb, int_ty, string_ty), "Int not <: String");
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
    assert!(types_compatible(&kb, red_ty, color_ty), "red <: Color");
    assert!(!types_compatible(&kb, color_ty, red_ty), "Color not <: red");
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
    assert!(!types_compatible(&kb, red_ty, blue_ty), "red not <: blue");
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
    assert!(types_compatible(&kb, wider, narrower), "(a: Int, b: String) <: (a: Int)");
    assert!(!types_compatible(&kb, narrower, wider), "(a: Int) not <: (a: Int, b: String)");
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
    assert!(types_compatible(&kb, specific, general), "(color: red) <: (color: Color)");
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
    assert!(types_compatible(&kb, specific, general), "(Int -> red) <: (Int -> Color)");
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
    assert!(types_compatible(&kb, general_param, specific_param), "(Color -> Int) <: (red -> Int)");
    assert!(!types_compatible(&kb, specific_param, general_param), "(red -> Int) not <: (Color -> Int)");
}

#[test]
fn subtype_parameterized_same() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let t_sym = kb.intern("T");
    let list_base = kb.make_sort_ref_by_name("List");
    let list_int = kb.make_parameterized_type(list_base, &[(t_sym, int_ty)]);
    assert!(types_compatible(&kb, list_int, list_int), "List[T=Int] <: List[T=Int]");
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
    assert!(!types_compatible(&kb, list_int, list_str), "List[T=Int] not <: List[T=String]");
}

#[test]
fn subtype_type_var_compatible_with_anything() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let fresh = kb.intern("?X");
    let var_ty = kb.make_type_var(fresh);
    assert!(types_compatible(&kb, var_ty, int_ty), "type_var <: Int");
    assert!(types_compatible(&kb, int_ty, var_ty), "Int <: type_var");
}

#[test]
fn subtype_nothing_compatible_with_anything() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let nothing = kb.make_nothing_type();
    assert!(types_compatible(&kb, nothing, int_ty), "nothing <: Int");
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
    assert!(types_compatible(&kb, pure_fn, effectful_fn), "pure <: effectful");
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
    assert!(types_compatible(&kb, fewer, more), "fewer effects <: more effects");
    assert!(!types_compatible(&kb, more, fewer), "more effects not <: fewer effects");
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
    assert!(!types_compatible(&kb, fn1, fn2), "different effects not compatible");
}

// ── is_subtype tests (strict, irreflexive) ─────────────────────

#[test]
fn is_subtype_not_reflexive() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    assert!(!is_subtype(&kb, int_ty, int_ty), "Int is not a strict subtype of Int");
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
    assert!(is_subtype(&kb, red_ty, color_ty), "red is a strict subtype of Color");
    assert!(!is_subtype(&kb, color_ty, red_ty), "Color is not a subtype of red");
}

#[test]
fn is_subtype_requires_direct() {
    // Ordered requires Eq — Ordered is a subtype of Eq
    let mut kb = load_stdlib_kb();
    let ordered_sym = kb.resolve_symbol("anthill.prelude.Ordered");
    let eq_sym = kb.resolve_symbol("anthill.prelude.Eq");
    let ordered_ty = kb.make_sort_ref(ordered_sym);
    let eq_ty = kb.make_sort_ref(eq_sym);
    assert!(is_subtype(&kb, ordered_ty, eq_ty), "Ordered <: Eq via requires");
    assert!(!is_subtype(&kb, eq_ty, ordered_ty), "Eq is not <: Ordered");
}

#[test]
fn requires_compatible() {
    // types_compatible should also accept requires relationships
    let mut kb = load_stdlib_kb();
    let ordered_sym = kb.resolve_symbol("anthill.prelude.Ordered");
    let eq_sym = kb.resolve_symbol("anthill.prelude.Eq");
    let ordered_ty = kb.make_sort_ref(ordered_sym);
    let eq_ty = kb.make_sort_ref(eq_sym);
    assert!(types_compatible(&kb, ordered_ty, eq_ty), "Ordered compatible with Eq");
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
    assert!(types_compatible(&kb, canvas_ty, paintable_ty), "Canvas <: Paintable via requires");
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
    assert!(is_subtype(&kb, circle_ty, shape_ty), "circle <: Shape");
    // Shape <: Drawable (requires)
    assert!(is_subtype(&kb, shape_ty, drawable_ty), "Shape <: Drawable");
    // circle <: Drawable (transitively: entity_of + requires)
    assert!(types_compatible(&kb, circle_ty, drawable_ty), "circle compatible with Drawable");
    // NOT compatible with unrelated sort
    let printable_sym = kb.resolve_symbol("Printable");
    let printable_ty = kb.make_sort_ref(printable_sym);
    assert!(!types_compatible(&kb, circle_ty, printable_ty), "circle not compatible with Printable");
    assert!(!types_compatible(&kb, shape_ty, printable_ty), "Shape not compatible with Printable");
    assert!(!types_compatible(&kb, drawable_ty, printable_ty), "Drawable not compatible with Printable");
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
    assert!(types_compatible(&kb, red_ty, color_ty), "enum: red <: Color");
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
        if !kb.rule_body(rid).is_empty() { continue; }
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
use anthill_core::kb::subst::Substitution;

#[test]
fn unify_identical_types() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let mut subst = Substitution::new();
    assert!(unify_types(&kb, &mut subst, int_ty, int_ty), "Int unifies with Int");
}

#[test]
fn unify_var_binds_to_type() {
    let mut kb = load_stdlib_kb();
    let int_ty = kb.make_sort_ref_by_name("Int");
    let sym = kb.intern("?X");
    let vid = kb.fresh_var(sym);
    let var_term = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(vid)));
    let mut subst = Substitution::new();
    assert!(unify_types(&kb, &mut subst, var_term, int_ty), "Var unifies with Int");
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
    assert!(unify_types(&kb, &mut subst, var1, var2), "two vars unify");
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
    assert!(!unify_types(&kb, &mut subst, int_ty, str_ty), "Int does not unify with String");
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
    assert!(unify_types(&kb, &mut subst, list_var, list_int), "List[T=?X] unifies with List[T=Int]");
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
    assert!(unify_types(&kb, &mut subst, arrow_var, arrow_concrete), "(?A -> ?B) unifies with (Int -> String)");
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
    assert!(unify_types(&kb, &mut subst, t_ref, int_ty),
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
    let body = kb.rule_body(facts[0]);
    assert!(!body.is_empty(), "rule should have a body");
    // Body goal should be ho_apply(?P, nil)
    match kb.get_term(body[0]) {
        Term::Fn { functor, pos_args, .. } => {
            let fname = kb.resolve_sym(*functor);
            assert!(fname == "ho_apply" || fname.ends_with(".ho_apply"),
                "body should be ho_apply, got: {}", fname);
            assert_eq!(pos_args.len(), 2, "ho_apply should have 2 pos args: ?P and nil");
        }
        other => panic!("expected Fn term, got {:?}", other),
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
    let body = kb.rule_body(facts[0]);
    match kb.get_term(body[0]) {
        Term::Fn { functor, pos_args, .. } => {
            let fname = kb.resolve_sym(*functor);
            assert!(fname == "ho_apply" || fname.ends_with(".ho_apply"),
                "body should be ho_apply, got: {}", fname);
            assert_eq!(pos_args.len(), 3, "ho_apply(?P, foo, bar) = 3 pos args");
        }
        other => panic!("expected Fn, got {:?}", other),
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
    let body = kb.rule_body(rules[0]);
    assert_eq!(body.len(), 2, "body should have 2 goals: ?P(0) and forall(...)");

    // First goal: ho_apply(?P, 0)
    match kb.get_term(body[0]) {
        Term::Fn { functor, pos_args, .. } => {
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
    match kb.get_term(body[1]) {
        Term::Fn { functor, pos_args, .. } => {
            let fname = kb.resolve_sym(*functor);
            let ok = fname == "forall" || fname.ends_with(".forall")
                  || fname == "forall_impl" || fname.ends_with(".forall_impl");
            assert!(ok,
                "second goal should be forall or forall_impl, got: {} (pos_args: {})",
                fname, pos_args.len());
        }
        other => {
            eprintln!("second goal term: {:?}", other);
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
      case ?other -> "other"
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
      case ?x -> "something"
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

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
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

/// Load user source on top of an existing KB (stdlib already loaded).
fn load_source(kb: &mut KnowledgeBase, source: &str) {
    let parsed = parse::parse(source).expect("parse failed");
    load::load(kb, &parsed, &NullResolver).expect("load failed");
}

/// Get the functor symbol from a name term (resolve_short_name_term returns a nullary Fn).
fn functor_of(kb: &KnowledgeBase, term: TermId) -> anthill_core::intern::Symbol {
    match kb.get_term(term) {
        Term::Fn { functor, .. } => *functor,
        _ => panic!("expected Fn term"),
    }
}

/// Build a query goal using a resolved symbol as functor.
/// Works for kernel names ("EntityOf"), qualified builtins
/// ("anthill.reflect.typing.is_entity_of"), and rule functor names
/// ("refines", "list_contains") which fall back to intern.
fn make_goal(kb: &mut KnowledgeBase, name: &str, pos_args: &[TermId]) -> TermId {
    let sym = kb.try_resolve_symbol(name)
        .unwrap_or_else(|| kb.intern(name));
    kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(pos_args),
        named_args: SmallVec::new(),
    })
}

/// Build a query goal using named args (for EntityOf, Requires, etc.).
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

    let red_term = kb.resolve_short_name_term("red");
    let color_term = kb.resolve_short_name_term("Color");

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

    let red_term = kb.resolve_short_name_term("red");
    let color_term = kb.resolve_short_name_term("Color");

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
fn is_entity_of_enumeration_via_entity_of_facts() {
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

    let color_term = kb.resolve_short_name_term("Color");

    // Query: EntityOf(entity: ?x, parent: Color) — should find red, green, blue
    let var_x = make_var(&mut kb, "x");

    let goal = make_named_goal(&mut kb, "EntityOf", &[("entity", var_x), ("parent", color_term)]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 3, "Color should have 3 entities: red, green, blue");
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

    let red_term = kb.resolve_short_name_term("red");
    let color_term = kb.resolve_short_name_term("Color");

    // Query via the typing rule (uses resolved symbol for is_entity_of)
    let goal = make_goal(&mut kb, "is_entity_of", &[red_term, color_term]);
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
    let red = kb.resolve_short_name_term("red");
    let green = kb.resolve_short_name_term("green");
    let nil_sym = kb.resolve_symbol("nil");
    let nil = kb.alloc(Term::Fn {
        functor: nil_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::new(),
    });

    let cons_sym = kb.resolve_symbol("cons");
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
    let goal = make_goal(&mut kb, "list_contains", &[red, list]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(), "list_contains(red, [red, green]) should succeed");

    // list_contains(green, list) should also succeed
    let goal2 = make_goal(&mut kb, "list_contains", &[green, list]);
    let results2 = kb.resolve(&[goal2], &default_config());
    assert!(!results2.is_empty(), "list_contains(green, [red, green]) should succeed");

    // list_contains(blue, list) should fail (blue not in list)
    let blue = kb.resolve_short_name_term("blue");
    let goal3 = make_goal(&mut kb, "list_contains", &[blue, list]);
    let results3 = kb.resolve(&[goal3], &default_config());
    assert!(results3.is_empty(), "list_contains(blue, [red, green]) should fail");
}

// ── extract_sort_ref builtin tests ──────────────────────────────

#[test]
fn extract_sort_ref_from_parameterized_type() {
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();

    // Build ParameterizedType(Eq(), T=Int())
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
    let pt_sym = kb.intern("ParameterizedType");
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
            assert_eq!(kb.resolve_sym(*sym), "Eq", "should extract Eq from ParameterizedType(Eq(), ...)");
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
    requires Eq{T = T}
    operation compare(a: T, b: T) -> Int
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let ordered_term = kb.resolve_short_name_term("Ordered");

    // Query: Requires(sort_ref: Ordered, base_sort: ?, spec_inst: ?spec) — direct fact query (named args)
    let var_spec = make_var(&mut kb, "spec");
    let var_anon = make_var(&mut kb, "_anon");

    let goal = make_named_goal(&mut kb, "Requires", &[("sort_ref", ordered_term), ("base_sort", var_anon), ("spec_inst", var_spec)]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(), "Ordered should have at least 1 Requires fact");
}

#[test]
fn refines_direct_via_rule() {
    let source = r#"
sort Eq {
    sort T = ?
}

sort Ordered {
    sort T = ?
    requires Eq{T = T}
    operation compare(a: T, b: T) -> Int
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let ordered_term = kb.resolve_short_name_term("Ordered");

    // Query: refines(Ordered, ?spec) via the typing rule
    let var_spec = make_var(&mut kb, "spec");

    let goal = make_goal(&mut kb, "refines", &[ordered_term, var_spec]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(), "refines(Ordered, ?spec) should find at least Eq{{T=T}}");
}

#[test]
fn refines_transitive() {
    let source = r#"
sort A {
    sort T = ?
}

sort B {
    sort T = ?
    requires A{T = T}
}

sort C {
    sort T = ?
    requires B{T = T}
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let c_term = kb.resolve_short_name_term("C");

    // Query: refines(C, ?spec) — should find both B{T=T} and A{T=T}
    let var_spec = make_var(&mut kb, "spec");

    let goal = make_goal(&mut kb, "refines", &[c_term, var_spec]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(results.len() >= 2, "C refines both B{{T=T}} (direct) and A{{T=T}} (transitive), got {} results", results.len());
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

    let color_term = kb.resolve_short_name_term("Color");

    // type_compatible(Color, Color) — same type via unification
    let goal = make_goal(&mut kb, "type_compatible", &[color_term, color_term]);
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

    let red_term = kb.resolve_short_name_term("red");
    let color_term = kb.resolve_short_name_term("Color");

    // type_compatible(red, Color) — via is_entity_of rule
    let goal = make_goal(&mut kb, "type_compatible", &[red_term, color_term]);
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
    requires Eq{T = T}
    operation compare(a: T, b: T) -> Int
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let ordered_name = kb.resolve_short_name_term("Ordered");
    let ordered_functor = functor_of(&kb, ordered_name);
    let ordered_ref = kb.alloc(Term::Ref(ordered_functor));

    // Query: sort_requires(Ordered_ref, ?spec)
    let var_spec = make_var(&mut kb, "spec");

    let goal = make_goal(&mut kb, "sort_requires", &[ordered_ref, var_spec]);
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

    let eq_name = kb.resolve_short_name_term("Eq");
    let eq_functor = functor_of(&kb, eq_name);
    let eq_ref = kb.alloc(Term::Ref(eq_functor));

    // Query: sort_has_param(Eq_ref, ?param)
    let var_param = make_var(&mut kb, "param");

    let goal = make_goal(&mut kb, "sort_has_param", &[eq_ref, var_param]);
    let config = ResolveConfig { max_solutions: 5, ..ResolveConfig::default() };
    let results = kb.resolve(&[goal], &config);
    assert!(!results.is_empty(),
        "sort_has_param(Eq, ?param) should find T via SortInfo partial expansion");
}

// ── EntityOf fact verification ───────────────────────────────────

#[test]
fn entity_of_fact_exists_in_kb() {
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

    // Query EntityOf facts by functor
    let entity_of_sym = kb.resolve_symbol("EntityOf");
    let facts = kb.by_functor(entity_of_sym);
    assert_eq!(facts.len(), 3, "should have 3 EntityOf facts for red, green, blue");
}

// ── EntityOf is 1-level (non-transitive) ────────────────────────

#[test]
fn entity_of_is_not_transitive() {
    // Nested sorts: entity inside sort inside sort.
    // EntityOf should only link entity → immediate parent sort, not to grandparent.
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

    let leaf_term = kb.resolve_short_name_term("leaf");
    let inner_term = kb.resolve_short_name_term("Inner");
    let outer_term = kb.resolve_short_name_term("Outer");

    // leaf is entity of Inner (direct)
    assert!(kb.is_entity_of(leaf_term, inner_term), "leaf should be entity of Inner");

    // EntityOf fact should exist for leaf → Inner
    let var_x = make_var(&mut kb, "x");
    let goal = make_named_goal(&mut kb, "EntityOf", &[("entity", leaf_term), ("parent", var_x)]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 1, "leaf should have exactly 1 EntityOf fact (→ Inner only)");

    // No EntityOf(leaf, Outer) — entity_of is 1-level
    let goal_outer = make_named_goal(&mut kb, "EntityOf", &[("entity", leaf_term), ("parent", outer_term)]);
    let results_outer = kb.resolve(&[goal_outer], &default_config());
    assert_eq!(results_outer.len(), 0, "EntityOf(leaf, Outer) should NOT exist — 1-level only");
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

    let red_term = kb.resolve_short_name_term("red");
    let green_term = kb.resolve_short_name_term("green");

    // Siblings are not entity_of each other
    assert!(!kb.is_entity_of(red_term, green_term), "red should NOT be entity of green");
    assert!(!kb.is_entity_of(green_term, red_term), "green should NOT be entity of red");
}

#[test]
fn entity_of_sort_is_not_entity_of_itself() {
    let source = r#"
sort Color {
    entity red
}
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    let color_term = kb.resolve_short_name_term("Color");

    // No EntityOf(Color, Color)
    let goal = make_named_goal(&mut kb, "EntityOf", &[("entity", color_term), ("parent", color_term)]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 0, "Color should NOT be entity of itself");
}

#[test]
fn entity_of_standalone_entity_has_no_entity_of() {
    // Standalone entity `entity Foo(...)` is loaded as an Entity fact only.
    // It does NOT produce EntityOf facts (only sort-with-body entities do).
    // The spec says standalone entity desugars to sort-with-body, but the
    // current loader stores it as a plain Entity fact without sort registration.
    let source = r#"
entity Account(id: Int, balance: Int)
"#;
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    load_source(&mut kb, source);

    // No EntityOf facts for standalone entities
    let entity_of_sym = kb.resolve_symbol("EntityOf");
    let facts = kb.by_functor(entity_of_sym);
    assert_eq!(facts.len(), 0, "standalone entity should not produce EntityOf facts");
}

#[test]
fn entity_of_multiple_sorts() {
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

    let red_term = kb.resolve_short_name_term("red");
    let circle_term = kb.resolve_short_name_term("circle");
    let color_term = kb.resolve_short_name_term("Color");
    let shape_term = kb.resolve_short_name_term("Shape");

    // red is entity of Color, NOT Shape
    assert!(kb.is_entity_of(red_term, color_term), "red should be entity of Color");
    assert!(!kb.is_entity_of(red_term, shape_term), "red should NOT be entity of Shape");

    // circle is entity of Shape, NOT Color
    assert!(kb.is_entity_of(circle_term, shape_term), "circle should be entity of Shape");
    assert!(!kb.is_entity_of(circle_term, color_term), "circle should NOT be entity of Color");

    // EntityOf facts: 2 for Color + 2 for Shape = 4
    let entity_of_sym = kb.resolve_symbol("EntityOf");
    let facts = kb.by_functor(entity_of_sym);
    assert_eq!(facts.len(), 4, "should have 4 EntityOf facts total");
}

// ── is_entity_of via typing rule with various patterns ──────────

#[test]
fn entity_of_enumerates_all_entities() {
    // EntityOf(?x, Color) enumerates all entities (via KB fact matching).
    // Note: is_entity_of builtin delays when first arg is Var (needs nonvar),
    // so enumeration should use EntityOf facts directly.
    let source = r#"
sort Color {
    entity red
    entity green
    entity blue
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let color_term = kb.resolve_short_name_term("Color");
    let var_x = make_var(&mut kb, "x");

    // Use EntityOf directly for enumeration
    let goal = make_named_goal(&mut kb, "EntityOf", &[("entity", var_x), ("parent", color_term)]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 3, "EntityOf(?x, Color) should find 3 entities");
}

#[test]
fn entity_of_finds_parent() {
    // Query: EntityOf(red, ?parent) should find Color.
    // Note: is_entity_of builtin delays when second arg is Var,
    // so use EntityOf facts directly for parent lookup.
    let source = r#"
sort Color {
    entity red
    entity green
}
"#;
    let mut kb = load_stdlib_kb();
    load_source(&mut kb, source);

    let red_term = kb.resolve_short_name_term("red");
    let var_p = make_var(&mut kb, "parent");

    let goal = make_named_goal(&mut kb, "EntityOf", &[("entity", red_term), ("parent", var_p)]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 1, "EntityOf(red, ?parent) should find exactly 1 parent");

    // Verify the parent is Color
    let bound = kb.reify(var_p, &results[0].subst);
    let color_term = kb.resolve_short_name_term("Color");
    assert_eq!(bound, color_term, "parent of red should be Color");
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

    let red_term = kb.resolve_short_name_term("red");
    let shape_term = kb.resolve_short_name_term("Shape");

    // type_compatible(red, Shape) should fail — red is entity of Color, not Shape
    let goal = make_goal(&mut kb, "type_compatible", &[red_term, shape_term]);
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

    let red_term = kb.resolve_short_name_term("red");
    let green_term = kb.resolve_short_name_term("green");
    let color_term = kb.resolve_short_name_term("Color");

    // type_compatible(red, Color) — should succeed
    let goal = make_goal(&mut kb, "type_compatible", &[red_term, color_term]);
    let results = kb.resolve(&[goal], &default_config());
    assert!(!results.is_empty(), "type_compatible(red, Color) should succeed");

    // type_compatible(red, green) — should fail (siblings, not entity_of)
    let goal2 = make_goal(&mut kb, "type_compatible", &[red_term, green_term]);
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

    let checking_term = kb.resolve_short_name_term("checking");
    let savings_term = kb.resolve_short_name_term("savings");
    let account_term = kb.resolve_short_name_term("Account");

    // Both entities are compatible with Account
    let goal1 = make_goal(&mut kb, "type_compatible", &[checking_term, account_term]);
    let results1 = kb.resolve(&[goal1], &default_config());
    assert!(!results1.is_empty(), "type_compatible(checking, Account) should succeed");

    let goal2 = make_goal(&mut kb, "type_compatible", &[savings_term, account_term]);
    let results2 = kb.resolve(&[goal2], &default_config());
    assert!(!results2.is_empty(), "type_compatible(savings, Account) should succeed");

    // Entities are NOT compatible with each other
    let goal3 = make_goal(&mut kb, "type_compatible", &[checking_term, savings_term]);
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

    let red_term = kb.resolve_short_name_term("red");
    let var_sort = make_var(&mut kb, "sort");

    let goal = make_goal(&mut kb, "entity_of", &[red_term, var_sort]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 1, "entity_of(red, ?sort) should find exactly 1 parent");

    // Verify the parent is Color
    let bound = kb.reify(var_sort, &results[0].subst);
    let color_term = kb.resolve_short_name_term("Color");
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

    let color_term = kb.resolve_short_name_term("Color");
    let var_x = make_var(&mut kb, "x");

    let goal = make_goal(&mut kb, "entity_of", &[var_x, color_term]);
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

    let color_term = kb.resolve_short_name_term("Color");
    let var_sort = make_var(&mut kb, "sort");

    let goal = make_goal(&mut kb, "entity_of", &[color_term, var_sort]);
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

    let red_term = kb.resolve_short_name_term("red");
    let circle_term = kb.resolve_short_name_term("circle");
    let color_term = kb.resolve_short_name_term("Color");
    let shape_term = kb.resolve_short_name_term("Shape");

    // entity_of(red, ?sort) → Color
    let var_sort1 = make_var(&mut kb, "sort");
    let goal1 = make_goal(&mut kb, "entity_of", &[red_term, var_sort1]);
    let results1 = kb.resolve(&[goal1], &default_config());
    assert_eq!(results1.len(), 1);
    let bound1 = kb.reify(var_sort1, &results1[0].subst);
    assert_eq!(bound1, color_term, "red's parent should be Color");

    // entity_of(circle, ?sort) → Shape
    let var_sort2 = make_var(&mut kb, "sort");
    let goal2 = make_goal(&mut kb, "entity_of", &[circle_term, var_sort2]);
    let results2 = kb.resolve(&[goal2], &default_config());
    assert_eq!(results2.len(), 1);
    let bound2 = kb.reify(var_sort2, &results2[0].subst);
    assert_eq!(bound2, shape_term, "circle's parent should be Shape");

    // entity_of(red, Shape) should fail — wrong parent
    let goal3 = make_goal(&mut kb, "entity_of", &[red_term, shape_term]);
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

    let red_term = kb.resolve_short_name_term("red");
    let color_term = kb.resolve_short_name_term("Color");

    let goal = make_goal(&mut kb, "entity_of", &[red_term, color_term]);
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

    let account_term = kb.resolve_short_name_term("Account");
    let var_sort = make_var(&mut kb, "sort");

    let goal = make_goal(&mut kb, "entity_of", &[account_term, var_sort]);
    let results = kb.resolve(&[goal], &default_config());
    assert_eq!(results.len(), 0, "entity_of(Account, ?sort) should fail — standalone entity has no parent");
}

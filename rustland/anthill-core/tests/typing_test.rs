/// Integration tests for the typing module (anthill.reflect.typing).
///
/// Tests load source files into a KB, register builtins, and run SLD resolution
/// to verify typing rules: is_entity_of, refines, type_compatible, list_contains,
/// extract_sort_ref, sort_requires, sort_has_param.

use std::path::PathBuf;

use anthill_core::parse;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;

use smallvec::SmallVec;

/// Collect all .anthill files under a directory, recursively.
fn collect_anthill_files(dir: &std::path::Path) -> Vec<PathBuf> {
    let mut files = Vec::new();
    if dir.is_dir() {
        for entry in std::fs::read_dir(dir).expect("read dir") {
            let entry = entry.expect("read dir entry");
            let path = entry.path();
            if path.is_dir() {
                files.extend(collect_anthill_files(&path));
            } else if path.extension().is_some_and(|e| e == "anthill") {
                files.push(path);
            }
        }
    }
    files.sort();
    files
}

fn stdlib_dir() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../stdlib/anthill")
}

/// Load stdlib + typing rules into a fresh KB with builtins registered.
fn load_stdlib_kb() -> KnowledgeBase {
    let dir = stdlib_dir();
    let files = collect_anthill_files(&dir);
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

/// Get the functor symbol from a name term (resolve_name_term returns a nullary Fn).
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

fn default_config() -> ResolveConfig {
    ResolveConfig { max_solutions: 10, ..ResolveConfig::default() }
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

    let red_term = kb.resolve_name_term("red");
    let color_term = kb.resolve_name_term("Color");

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

    let red_term = kb.resolve_name_term("red");
    let color_term = kb.resolve_name_term("Color");

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

    let color_term = kb.resolve_name_term("Color");

    // Query: EntityOf(?x, Color) — should find red, green, blue
    let x_sym = kb.intern("x");
    let vx = kb.fresh_var(x_sym);
    let var_x = kb.alloc(Term::Var(vx));

    let goal = make_goal(&mut kb, "EntityOf", &[var_x, color_term]);
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

    let red_term = kb.resolve_name_term("red");
    let color_term = kb.resolve_name_term("Color");

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
    let red = kb.resolve_name_term("red");
    let green = kb.resolve_name_term("green");
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
    let blue = kb.resolve_name_term("blue");
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
    let r_sym = kb.intern("result");
    let vr = kb.fresh_var(r_sym);
    let var_result = kb.alloc(Term::Var(vr));

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

    let r_sym = kb.intern("result");
    let vr = kb.fresh_var(r_sym);
    let var_result = kb.alloc(Term::Var(vr));

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

    let ordered_term = kb.resolve_name_term("Ordered");

    // Query: Requires(Ordered_ref, ?, ?spec) — direct fact query (3 pos args now)
    let spec_sym = kb.intern("spec");
    let vspec = kb.fresh_var(spec_sym);
    let var_spec = kb.alloc(Term::Var(vspec));

    let anon1 = kb.intern("?");
    let v_anon = kb.fresh_var(anon1);
    let var_anon = kb.alloc(Term::Var(v_anon));

    let goal = make_goal(&mut kb, "Requires", &[ordered_term, var_anon, var_spec]);
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

    let ordered_term = kb.resolve_name_term("Ordered");

    // Query: refines(Ordered, ?spec) via the typing rule
    let spec_sym = kb.intern("spec");
    let vspec = kb.fresh_var(spec_sym);
    let var_spec = kb.alloc(Term::Var(vspec));

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

    let c_term = kb.resolve_name_term("C");

    // Query: refines(C, ?spec) — should find both B{T=T} and A{T=T}
    let spec_sym = kb.intern("spec");
    let vspec = kb.fresh_var(spec_sym);
    let var_spec = kb.alloc(Term::Var(vspec));

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

    let color_term = kb.resolve_name_term("Color");

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

    let red_term = kb.resolve_name_term("red");
    let color_term = kb.resolve_name_term("Color");

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

    let ordered_name = kb.resolve_name_term("Ordered");
    let ordered_functor = functor_of(&kb, ordered_name);
    let ordered_ref = kb.alloc(Term::Ref(ordered_functor));

    // Query: sort_requires(Ordered_ref, ?spec)
    let spec_sym = kb.intern("spec");
    let vspec = kb.fresh_var(spec_sym);
    let var_spec = kb.alloc(Term::Var(vspec));

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

    let eq_name = kb.resolve_name_term("Eq");
    let eq_functor = functor_of(&kb, eq_name);
    let eq_ref = kb.alloc(Term::Ref(eq_functor));

    // Query: sort_has_param(Eq_ref, ?param)
    let p_sym = kb.intern("param");
    let vp = kb.fresh_var(p_sym);
    let var_param = kb.alloc(Term::Var(vp));

    let goal = make_goal(&mut kb, "sort_has_param", &[eq_ref, var_param]);
    let config = ResolveConfig { max_solutions: 5, ..ResolveConfig::default() };
    let results = kb.resolve(&[goal], &config);
    assert!(!results.is_empty(),
        "sort_has_param(Eq, ?param) should find T via SortInfo partial expansion");
}

// ── EntityOf fact rename verification ────────────────────────────

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

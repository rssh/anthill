/// Integration tests for operation binding via instantiation substitution.
///
/// Tests load source files into a KB and verify:
/// - base_subst computed from SortInfo
/// - Requires spec (SortView) completed with all bindings
/// - resolve_sort_instantiation_param builtin extracts bindings
/// - auto-bind works for same-named operations

mod common;

use anthill_core::parse;
use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;

use smallvec::SmallVec;

/// Load stdlib + test files into a fresh KB with builtins registered.
fn load_monoid_kb() -> KnowledgeBase {
    let stdlib_dir = common::stdlib_dir();
    let mut files = common::collect_anthill_files(&stdlib_dir);

    let testcases_dir = common::testcases_dir();
    let monoid_path = testcases_dir.join("fact-substitution/monoid.anthill");
    files.push(monoid_path);

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
    }
    kb
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

/// Build a Requires query with 2 named args (sort_ref, spec).
/// Missing args are filled with fresh variables.
fn make_requires_query(
    kb: &mut KnowledgeBase,
    sort_ref: TermId,
    spec: TermId,
) -> TermId {
    let requires_sym = kb.resolve_symbol("Requires");
    let sort_ref_sym = kb.intern("sort_ref");
    let spec_sym = kb.intern("spec");
    kb.alloc(Term::Fn {
        functor: requires_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[
            (sort_ref_sym, sort_ref),
            (spec_sym, spec),
        ]),
    })
}

/// Build a query goal with positional args.
fn make_goal(kb: &mut KnowledgeBase, name: &str, pos_args: &[TermId]) -> TermId {
    let sym = kb.try_resolve_symbol(name)
        .unwrap_or_else(|| kb.intern(name));
    kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(pos_args),
        named_args: SmallVec::new(),
    })
}

/// Find a named arg key symbol by short name.
fn find_named_arg_sym_by_short(kb: &KnowledgeBase, named_args: &[(anthill_core::intern::Symbol, TermId)], short: &str) -> Option<anthill_core::intern::Symbol> {
    named_args.iter().find(|(sym, _)| {
        let name = kb.resolve_sym(*sym);
        let s = name.rsplit('.').next().unwrap_or(name);
        s == short
    }).map(|(sym, _)| *sym)
}

/// Find a named arg by its short name (last segment of qualified name).
fn find_named_arg_by_short(kb: &KnowledgeBase, named_args: &[(anthill_core::intern::Symbol, TermId)], short: &str) -> Option<TermId> {
    named_args.iter().find(|(sym, _)| {
        let name = kb.resolve_sym(*sym);
        let s = name.rsplit('.').next().unwrap_or(name);
        s == short
    }).map(|(_, tid)| *tid)
}

/// Extract the short name from a term (works for both Fn and Ref).
fn extract_short_name(kb: &KnowledgeBase, tid: TermId) -> String {
    match kb.get_term(tid) {
        Term::Ref(sym) => {
            let name = kb.resolve_sym(*sym);
            name.rsplit('.').next().unwrap_or(name).to_owned()
        }
        Term::Fn { functor, .. } => {
            let name = kb.resolve_sym(*functor);
            name.rsplit('.').next().unwrap_or(name).to_owned()
        }
        _ => format!("{:?}", kb.get_term(tid)),
    }
}

// ── base_subst tests ──────────────────────────────────────────

#[test]
fn base_subst_computed_for_monoid() {
    let kb = load_monoid_kb();
    let monoid_sym = kb.resolve_symbol("Monoid");
    let base = kb.sort_base_subst(monoid_sym)
        .expect("Monoid should have a base_subst");

    // Monoid has 3 slots: T (param), combine (op), identity (op)
    assert_eq!(base.len(), 3, "Monoid should have 3 slots (T, combine, identity)");

    let slot_names: Vec<&str> = base.iter()
        .map(|(sym, _)| kb.resolve_sym(*sym))
        .map(|n| n.rsplit('.').next().unwrap_or(n))
        .collect();

    assert!(slot_names.contains(&"T"), "should contain T param, got: {:?}", slot_names);
    assert!(slot_names.contains(&"combine"), "should contain combine op, got: {:?}", slot_names);
    assert!(slot_names.contains(&"identity"), "should contain identity op, got: {:?}", slot_names);

    // Each value should be Ref(same_sym)
    for (sym, tid) in base {
        match kb.get_term(*tid) {
            Term::Ref(ref_sym) => assert_eq!(*ref_sym, *sym, "base subst value should be Ref(same_sym)"),
            other => panic!("base subst value should be Ref, got: {:?}", other),
        }
    }
}

// ── Requires spec completion tests ──────────────────────────────

#[test]
fn requires_spec_inst_completed_for_int_add() {
    let mut kb = load_monoid_kb();

    let int_add_term = kb.resolve_short_name_term("IntAdd");
    let var_inst = make_var(&mut kb, "inst");
    let goal = make_requires_query(&mut kb, int_add_term, var_inst);

    let config = default_config();
    let solutions = kb.resolve(&[goal], &config);
    assert!(!solutions.is_empty(), "should find Requires for IntAdd");

    let sol = &solutions[0];
    let inst_tid = kb.reify(var_inst, &sol.subst);

    // spec should be SortView(Monoid(), T=Int(), combine=Ref(add), identity=Ref(zero))
    match kb.get_term(inst_tid).clone() {
        Term::Fn { ref functor, ref named_args, .. } => {
            let functor_name = kb.resolve_sym(*functor);
            assert!(
                functor_name == "SortView" || functor_name.ends_with(".SortView"),
                "spec should be SortView, got: {functor_name}"
            );
            // Should have all 3 bindings
            assert_eq!(named_args.len(), 3, "spec should have 3 named args (T, combine, identity), got {}", named_args.len());

            // Check T binding -> Int
            let t_tid = find_named_arg_by_short(&kb, &named_args, "T");
            assert!(t_tid.is_some(), "should have T binding");
            let t_short = extract_short_name(&kb, t_tid.unwrap());
            assert_eq!(t_short, "Int", "T should be bound to Int, got: {t_short}");

            // Check combine binding -> add
            let c_tid = find_named_arg_by_short(&kb, &named_args, "combine");
            assert!(c_tid.is_some(), "should have combine binding");
            let c_short = extract_short_name(&kb, c_tid.unwrap());
            assert_eq!(c_short, "add", "combine should be bound to add, got: {c_short}");

            // Check identity binding -> zero
            let i_tid = find_named_arg_by_short(&kb, &named_args, "identity");
            assert!(i_tid.is_some(), "should have identity binding");
            let i_short = extract_short_name(&kb, i_tid.unwrap());
            assert_eq!(i_short, "zero", "identity should be bound to zero, got: {i_short}");
        }
        _ => panic!("spec should be Fn term"),
    }
}

#[test]
fn requires_spec_inst_completed_for_int_mul() {
    let mut kb = load_monoid_kb();

    let int_mul_term = kb.resolve_short_name_term("IntMul");
    let var_inst = make_var(&mut kb, "inst");
    let goal = make_requires_query(&mut kb, int_mul_term, var_inst);

    let config = default_config();
    let solutions = kb.resolve(&[goal], &config);
    assert!(!solutions.is_empty(), "should find Requires for IntMul");

    let sol = &solutions[0];
    let inst_tid = kb.reify(var_inst, &sol.subst);

    match kb.get_term(inst_tid).clone() {
        Term::Fn { ref named_args, .. } => {
            assert_eq!(named_args.len(), 3, "spec should have 3 named args");

            // Check combine -> multiply
            let c_tid = find_named_arg_by_short(&kb, &named_args, "combine");
            assert!(c_tid.is_some(), "should have combine binding");
            let c_short = extract_short_name(&kb, c_tid.unwrap());
            assert_eq!(c_short, "multiply", "combine should be bound to multiply, got: {c_short}");

            // Check identity -> one
            let i_tid = find_named_arg_by_short(&kb, &named_args, "identity");
            assert!(i_tid.is_some(), "should have identity binding");
            let i_short = extract_short_name(&kb, i_tid.unwrap());
            assert_eq!(i_short, "one", "identity should be bound to one, got: {i_short}");
        }
        _ => panic!("spec should be Fn term"),
    }
}

// ── resolve_sort_instantiation_param tests ──────────────────────

#[test]
fn resolve_sort_inst_param_extracts_type_binding() {
    let mut kb = load_monoid_kb();

    // First get the spec for IntAdd
    let int_add_term = kb.resolve_short_name_term("IntAdd");
    let var_inst = make_var(&mut kb, "inst");
    let req_goal = make_requires_query(&mut kb, int_add_term, var_inst);

    let config = default_config();
    let solutions = kb.resolve(&[req_goal], &config);
    assert!(!solutions.is_empty());
    let inst_tid = kb.reify(var_inst, &solutions[0].subst);

    // Extract the T named arg key from the spec (it might be scoped as Monoid.T)
    let t_key_sym = match kb.get_term(inst_tid).clone() {
        Term::Fn { ref named_args, .. } => {
            find_named_arg_sym_by_short(&kb, named_args, "T")
                .expect("spec should have T")
        }
        _ => panic!("spec should be Fn"),
    };
    let t_ref = kb.alloc(Term::Ref(t_key_sym));
    let var_val = make_var(&mut kb, "val");
    let param_goal = make_goal(&mut kb, "resolve_sort_instantiation_param", &[inst_tid, t_ref, var_val]);

    let solutions2 = kb.resolve(&[param_goal], &config);
    assert!(!solutions2.is_empty(), "resolve_sort_instantiation_param should succeed for T");

    let val_tid = kb.reify(var_val, &solutions2[0].subst);
    match kb.get_term(val_tid) {
        Term::Fn { functor, .. } => {
            let name = kb.resolve_sym(*functor);
            assert!(name == "Int" || name.ends_with(".Int"), "T should resolve to Int, got: {name}");
        }
        other => panic!("T value should be Int(), got: {:?}", other),
    }
}

#[test]
fn resolve_sort_inst_param_extracts_operation_binding() {
    let mut kb = load_monoid_kb();

    // Get the spec for IntAdd
    let int_add_term = kb.resolve_short_name_term("IntAdd");
    let var_inst = make_var(&mut kb, "inst");
    let req_goal = make_requires_query(&mut kb, int_add_term, var_inst);

    let config = default_config();
    let solutions = kb.resolve(&[req_goal], &config);
    assert!(!solutions.is_empty());
    let inst_tid = kb.reify(var_inst, &solutions[0].subst);

    // Extract the combine named arg key from spec
    let combine_key_sym = match kb.get_term(inst_tid).clone() {
        Term::Fn { ref named_args, .. } => {
            find_named_arg_sym_by_short(&kb, named_args, "combine")
                .expect("spec should have combine")
        }
        _ => panic!("spec should be Fn"),
    };
    let combine_ref = kb.alloc(Term::Ref(combine_key_sym));
    let var_val = make_var(&mut kb, "val");
    let param_goal = make_goal(&mut kb, "resolve_sort_instantiation_param", &[inst_tid, combine_ref, var_val]);

    let solutions2 = kb.resolve(&[param_goal], &config);
    assert!(!solutions2.is_empty(), "resolve_sort_instantiation_param should succeed for combine");

    let val_tid = kb.reify(var_val, &solutions2[0].subst);
    let short = extract_short_name(&kb, val_tid);
    assert_eq!(short, "add", "combine should resolve to add, got: {short}");
}

// ── auto-bind test ──────────────────────────────────────────

#[test]
fn auto_bind_same_named_operations() {
    let mut kb = load_monoid_kb();

    // AutoBindTest has `requires Monoid{T = Int}` with no explicit combine/identity.
    // Since AutoBindTest has same-named ops (combine, identity), they should auto-bind.
    let auto_term = kb.resolve_short_name_term("AutoBindTest");
    let var_inst = make_var(&mut kb, "inst");
    let goal = make_requires_query(&mut kb, auto_term, var_inst);

    let config = default_config();
    let solutions = kb.resolve(&[goal], &config);
    assert!(!solutions.is_empty(), "should find Requires for AutoBindTest");

    let sol = &solutions[0];
    let inst_tid = kb.reify(var_inst, &sol.subst);

    match kb.get_term(inst_tid).clone() {
        Term::Fn { ref named_args, .. } => {
            // Should have all 3 bindings: T, combine, identity
            assert_eq!(named_args.len(), 3, "spec should have 3 named args after auto-bind");



            // Check combine was auto-bound
            let c_tid = find_named_arg_by_short(&kb, &named_args, "combine");
            assert!(c_tid.is_some(), "combine should be auto-bound");
            let c_short = extract_short_name(&kb, c_tid.unwrap());
            assert_eq!(c_short, "combine", "auto-bound combine should point to AutoBindTest's combine, got: {c_short}");

            // Check identity was auto-bound
            let i_tid = find_named_arg_by_short(&kb, &named_args, "identity");
            assert!(i_tid.is_some(), "identity should be auto-bound");
            let i_short = extract_short_name(&kb, i_tid.unwrap());
            assert_eq!(i_short, "identity", "auto-bound identity should point to AutoBindTest's identity, got: {i_short}");
        }
        _ => panic!("spec should be Fn term"),
    }
}

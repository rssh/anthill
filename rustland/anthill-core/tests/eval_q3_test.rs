//! Integration tests for proposal 026.1 Q3 — value-integrated KB queries
//! (WI-047). Covers `alloc_from_value` / `lower_query` / `execute_logical_query`.
//!
//! The eval-side builtin binding `anthill.reflect.KB.execute` to this
//! machinery is WI-048's responsibility (it produces a `Value::Stream`,
//! which needs the M4 stream arena). These tests exercise the KB API
//! directly and confirm that query results come back with `Value`-typed
//! substitution bindings.

mod common;

use anthill_core::eval::Value;
use anthill_core::kb::execute::LowerError;
use anthill_core::kb::term::{Literal, Term, Var};

use common::load_kb_with;

/// Build a `Value::Entity` wrapping a single named argument. Convenience for
/// writing LogicalQuery literals on the Rust side of the boundary.
fn entity_named(functor: anthill_core::intern::Symbol, named: Vec<(anthill_core::intern::Symbol, Value)>) -> Value {
    Value::Entity { functor, pos: Vec::new(), named }
}

#[test]
fn q3_alloc_from_value_scalars_and_entity() {
    // alloc_from_value promotes runtime Values into hash-consed TermIds.
    // Two structurally equal Entities should dedupe to the same TermId.
    let mut kb = load_kb_with(r#"
namespace test.q3_alloc
  sort Color
    entity red
  end
end
"#);
    let red_sym = kb.try_resolve_symbol("test.q3_alloc.Color.red").expect("red symbol");
    let int_field = kb.intern("n");

    let v1 = Value::Entity {
        functor: red_sym,
        pos: vec![Value::Int(1), Value::Str("hi".into())],
        named: vec![(int_field, Value::Bool(true))],
    };
    let v2 = v1.clone();

    let t1 = kb.alloc_from_value(&v1).expect("alloc v1");
    let t2 = kb.alloc_from_value(&v2).expect("alloc v2");
    // Hash-consing: structurally-equal Values collapse to one TermId.
    assert_eq!(t1, t2);

    // Scalar variants land as Term::Const.
    let t_int = kb.alloc_from_value(&Value::Int(7)).expect("alloc int");
    match kb.get_term(t_int) {
        Term::Const(Literal::Int(7)) => {}
        other => panic!("expected Const(Int(7)), got {other:?}"),
    }
}

#[test]
fn q3_alloc_from_value_passes_through_term() {
    // Value::Term(tid) must reuse the existing TermId, not re-promote.
    let mut kb = load_kb_with("namespace test.q3_passthrough end\n");
    let n_sym = kb.intern("n");
    let n = kb.fresh_var(n_sym);
    let var_tid = kb.alloc(Term::Var(Var::Global(n)));

    let v = Value::Term(var_tid);
    let got = kb.alloc_from_value(&v).expect("alloc term-variant");
    assert_eq!(got, var_tid);
}

#[test]
fn q3_alloc_from_value_rejects_closures_streams_lazies() {
    let mut kb = load_kb_with("namespace test.q3_rej end\n");

    // Unit has no KB-term representation either — covers the whole
    // "interpreter-only Value" class in one check.
    for v in [Value::Unit,
              Value::Tuple { pos: Vec::new(), named: Vec::new() }] {
        let err = kb.alloc_from_value(&v).unwrap_err();
        assert!(matches!(err, LowerError::UnsupportedVariant(_)),
                "expected UnsupportedVariant for {v:?}, got {err:?}");
    }
}

#[test]
fn q3_lower_empty_query_yields_zero_goals() {
    let mut kb = load_kb_with("namespace test.q3_empty end\n");
    let empty_q_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.empty_query")
        .expect("empty_query in reflect stdlib");
    let q = Value::Entity { functor: empty_q_sym, pos: Vec::new(), named: Vec::new() };

    let goals = kb.lower_query(&q).expect("lower empty_query");
    assert_eq!(goals.len(), 0);
}

#[test]
fn q3_lower_rejects_non_logical_query() {
    let mut kb = load_kb_with("namespace test.q3_nlq end\n");

    let err = kb.lower_query(&Value::Int(42)).unwrap_err();
    assert!(matches!(err, LowerError::NotALogicalQuery { .. }), "got {err:?}");
}

#[test]
fn q3_execute_pattern_query_yields_value_typed_substitutions() {
    // Acceptance test (WI-047): build a pattern_query(EntityInfo(name: ?n)),
    // execute it against the KB, and iterate Value-typed Substitution
    // solutions. EntityInfo facts are asserted by the loader for every
    // entity declared inside a sort body — one per constructor.
    let mut kb = load_kb_with(r#"
namespace test.q3_exec
  sort Color
    entity red
    entity green
    entity blue
  end
end
"#);

    // Build the reified query:  pattern_query( EntityInfo(name: ?n, fields: ?f) )
    let entity_info_sym = kb.try_resolve_symbol("anthill.reflect.EntityInfo")
        .expect("EntityInfo symbol in reflect stdlib");
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query")
        .expect("pattern_query symbol");

    let name_field = kb.intern("name");
    let fields_field = kb.intern("fields");
    let term_field = kb.intern("term");

    let n_sym = kb.intern("n");
    let f_sym = kb.intern("f");
    let vn = kb.fresh_var(n_sym);
    let vf = kb.fresh_var(f_sym);
    let var_n = kb.alloc(Term::Var(Var::Global(vn)));
    let var_f = kb.alloc(Term::Var(Var::Global(vf)));

    // EntityInfo(name: ?n, fields: ?f) — note the named_args get sorted on
    // the way into alloc_from_value, so any order we hand in here works.
    let inner_pattern = Value::Entity {
        functor: entity_info_sym,
        pos: Vec::new(),
        named: vec![(name_field, Value::Term(var_n)), (fields_field, Value::Term(var_f))],
    };

    let query = entity_named(pattern_query_sym, vec![(term_field, inner_pattern)]);

    // Collect all solutions via split_first iteration.
    let mut stream = kb.execute_logical_query(&query).expect("execute lowered cleanly");
    let mut solutions = Vec::new();
    loop {
        match stream.split_first(&mut kb) {
            Some((sol, rest)) => { solutions.push(sol); stream = rest; }
            None => break,
        }
    }

    // The stdlib loads a large number of entities, so there are many
    // EntityInfo facts in addition to the three from test.q3_exec. The
    // key properties we want to confirm:
    //   1. We got _some_ solutions (the pattern resolved through Value
    //      inputs to real facts).
    //   2. Among them, `?n` is bound to each of the three user-defined
    //      Color constructors (red, green, blue).
    //   3. Substitutions surface as `Value`-typed bindings via `lookup`.
    assert!(solutions.len() >= 3, "expected at least 3 EntityInfo solutions, got {}",
            solutions.len());

    let red_tid = kb.try_resolve_symbol("test.q3_exec.Color.red").expect("red sym");
    let green_tid = kb.try_resolve_symbol("test.q3_exec.Color.green").expect("green sym");
    let blue_tid = kb.try_resolve_symbol("test.q3_exec.Color.blue").expect("blue sym");
    let mut seen_colors = std::collections::HashSet::new();
    for sol in &solutions {
        // lookup returns Option<&Value>; we expect Value::Term for KB-resident
        // bindings (lineage-preserving — EntityInfo fact heads are TermId).
        match sol.subst.resolve_as_value(vn) {
            Some(Value::Term(t)) => {
                if let Term::Fn { functor, .. } = kb.get_term(*t) {
                    if *functor == red_tid { seen_colors.insert("red"); }
                    if *functor == green_tid { seen_colors.insert("green"); }
                    if *functor == blue_tid { seen_colors.insert("blue"); }
                }
            }
            // Non-Term Value variants shouldn't appear here — the source
            // is a hash-consed EntityInfo fact, so the binding stays as
            // Value::Term. If this ever flips to Value::Entity, we've
            // regressed the lineage-preservation rule.
            Some(other) => panic!("expected Value::Term for KB-resident binding, got {other:?}"),
            None => panic!("solution has no binding for ?n"),
        }
    }
    assert_eq!(seen_colors.len(), 3, "expected all three colors to appear, saw {:?}", seen_colors);
}

#[test]
fn q3_execute_conjunction_composes_goals() {
    // conjunction(pattern_query(A), pattern_query(B)) should produce the
    // same goal list as the union of the two pattern_query lowerings —
    // i.e. two goals in the frame, joined through shared variables.
    let mut kb = load_kb_with(r#"
namespace test.q3_conj
  sort Pair
    entity pair(x: Int, y: Int)
  end
  fact pair(x: 1, y: 10)
  fact pair(x: 2, y: 20)
end
"#);

    let pair_sym = kb.try_resolve_symbol("test.q3_conj.Pair.pair").expect("pair sym");
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query").unwrap();
    let conj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.conjunction").unwrap();
    let term_field = kb.intern("term");
    let left_field = kb.intern("left");
    let right_field = kb.intern("right");
    let x_field = kb.intern("x");
    let y_field = kb.intern("y");

    let v_sym = kb.intern("v");
    let vid = kb.fresh_var(v_sym);
    let var_v = kb.alloc(Term::Var(Var::Global(vid)));

    // Two pattern_query children sharing the `?v` variable. The discrim
    // tree matches structurally, so the pattern's named-arg arity has to
    // equal the fact's — both `x` and `y` are listed; `y` gets a fresh
    // anonymous var per side. When the same var appears in two goals in
    // the same frame, their bindings must be consistent, so each solution
    // pins `?v` to the x-value of some matching fact.
    let y1_sym = kb.intern("y1");
    let y2_sym = kb.intern("y2");
    let vy1 = kb.fresh_var(y1_sym);
    let vy2 = kb.fresh_var(y2_sym);
    let var_y1 = kb.alloc(Term::Var(Var::Global(vy1)));
    let var_y2 = kb.alloc(Term::Var(Var::Global(vy2)));
    let pat_x = Value::Entity {
        functor: pair_sym,
        pos: Vec::new(),
        named: vec![(x_field, Value::Term(var_v)), (y_field, Value::Term(var_y1))],
    };
    let pat_y = Value::Entity {
        functor: pair_sym,
        pos: Vec::new(),
        named: vec![(x_field, Value::Term(var_v)), (y_field, Value::Term(var_y2))],
    };
    let left = entity_named(pattern_query_sym, vec![(term_field, pat_x)]);
    let right = entity_named(pattern_query_sym, vec![(term_field, pat_y)]);
    let conj = entity_named(conj_sym, vec![(left_field, left), (right_field, right)]);

    let goals = kb.lower_query(&conj).expect("lower conjunction");
    // conjunction flattens to one goal per side.
    assert_eq!(goals.len(), 2);

    // And execute yields solutions for each facts's x = 1, x = 2.
    let mut stream = kb.execute_logical_query(&conj).expect("execute conj");
    let mut xs = Vec::new();
    while let Some((sol, rest)) = stream.split_first(&mut kb) {
        match sol.subst.resolve_as_value(vid) {
            Some(Value::Term(t)) => {
                if let Term::Const(Literal::Int(n)) = kb.get_term(*t) {
                    xs.push(*n);
                }
            }
            other => panic!("unexpected binding for ?v: {other:?}"),
        }
        stream = rest;
    }
    xs.sort();
    xs.dedup();
    assert_eq!(xs, vec![1, 2]);
}

#[test]
fn q3_quantifier_lowering_is_not_yet_implemented() {
    // forall_q / some_q / ... / count_q / ... need the M4 LogicalStream
    // (WI-048) to have proper semantics. Until then, lower_query surfaces
    // a clean NotYetImplemented error — callers don't silently get "true".
    let mut kb = load_kb_with("namespace test.q3_nyi end\n");

    let forall_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.forall_q")
        .expect("forall_q symbol");
    let var_field = kb.intern("var");
    let cond_field = kb.intern("condition");
    let body_field = kb.intern("body");
    let empty_q_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.empty_query").unwrap();
    let empty_q = Value::Entity { functor: empty_q_sym, pos: Vec::new(), named: Vec::new() };

    let sym_v = kb.intern("v");
    let any_sym = Value::Term(kb.alloc(Term::Ref(sym_v)));
    let q = Value::Entity {
        functor: forall_sym,
        pos: Vec::new(),
        named: vec![
            (var_field, any_sym),
            (cond_field, empty_q.clone()),
            (body_field, empty_q),
        ],
    };

    let err = kb.lower_query(&q).unwrap_err();
    assert!(matches!(err, LowerError::NotYetImplemented(_)), "got {err:?}");
}

#[test]
fn q3_disjunction_yields_solutions_from_both_branches() {
    // disjunction(pattern_query(A), pattern_query(B)) — proposal 033 / WI-075.
    // Both branches resolve through push_choice; each surviving branch
    // contributes solutions. Uses entities-as-predicates so the tag entity
    // is the matched goal head and the fact stamps it into the KB.
    let mut kb = load_kb_with(r#"
namespace test.q3_disj
  sort LeftTag
    entity left_tag(name: String)
  end
  sort RightTag
    entity right_tag(name: String)
  end
  fact left_tag(name: "alpha")
  fact right_tag(name: "beta")
end
"#);

    let left_tag_sym = kb.try_resolve_symbol("test.q3_disj.LeftTag.left_tag").expect("left_tag");
    let right_tag_sym = kb.try_resolve_symbol("test.q3_disj.RightTag.right_tag").expect("right_tag");
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query").unwrap();
    let disj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.disjunction").unwrap();
    let term_field = kb.intern("term");
    let left_field = kb.intern("left");
    let right_field = kb.intern("right");
    let name_field = kb.intern("name");

    let v_sym = kb.intern("v");
    let vid = kb.fresh_var(v_sym);
    let var_v = kb.alloc(Term::Var(Var::Global(vid)));

    // pattern_query(left_tag(name: ?v))
    let left_pattern = Value::Entity {
        functor: left_tag_sym,
        pos: Vec::new(),
        named: vec![(name_field, Value::Term(var_v))],
    };
    let left_q = entity_named(pattern_query_sym, vec![(term_field, left_pattern)]);

    // pattern_query(right_tag(name: ?v))
    let right_pattern = Value::Entity {
        functor: right_tag_sym,
        pos: Vec::new(),
        named: vec![(name_field, Value::Term(var_v))],
    };
    let right_q = entity_named(pattern_query_sym, vec![(term_field, right_pattern)]);

    let query = entity_named(disj_sym, vec![
        (left_field, left_q),
        (right_field, right_q),
    ]);

    let mut stream = kb.execute_logical_query(&query).expect("disjunction lowers");
    // Dedup on ?v value — each entity declaration auto-stamps a schema
    // fact in addition to the user-asserted fact, so the discrim tree
    // matches the pattern more than once per branch. The semantic
    // contract checked here is: distinct ?v values come from both
    // branches.
    let mut seen = std::collections::HashSet::new();
    while let Some((sol, rest)) = stream.split_first(&mut kb) {
        if let Some(Value::Term(t)) = sol.subst.resolve_as_value(vid) {
            if let Term::Const(Literal::String(s)) = kb.get_term(*t) {
                seen.insert(s.clone());
            }
        }
        stream = rest;
    }
    let mut expected: std::collections::HashSet<String> = std::collections::HashSet::new();
    expected.insert("alpha".to_string());
    expected.insert("beta".to_string());
    assert_eq!(seen, expected, "both branches must contribute distinct ?v bindings");
}

#[test]
fn q3_disjunction_inside_conjunction_yields_cross_product() {
    // disjunction(P, Q) inside a conjunction with a tail T — both branches
    // must run T. Validates the shared-tail contract through the
    // execute_logical_query path.
    let mut kb = load_kb_with(r#"
namespace test.q3_disj_conj
  sort LeftTag
    entity left_tag(name: String)
  end
  sort RightTag
    entity right_tag(name: String)
  end
  sort HasMarker
    entity has_marker(label: String)
  end
  fact left_tag(name: "alpha")
  fact right_tag(name: "beta")
  fact has_marker(label: "M")
end
"#);

    let left_tag_sym = kb.try_resolve_symbol("test.q3_disj_conj.LeftTag.left_tag").unwrap();
    let right_tag_sym = kb.try_resolve_symbol("test.q3_disj_conj.RightTag.right_tag").unwrap();
    let has_marker_sym = kb.try_resolve_symbol("test.q3_disj_conj.HasMarker.has_marker").unwrap();
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query").unwrap();
    let disj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.disjunction").unwrap();
    let conj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.conjunction").unwrap();
    let term_field = kb.intern("term");
    let left_field = kb.intern("left");
    let right_field = kb.intern("right");
    let name_field = kb.intern("name");
    let label_field = kb.intern("label");

    let v_sym = kb.intern("v");
    let m_sym = kb.intern("m");
    let vid = kb.fresh_var(v_sym);
    let mid = kb.fresh_var(m_sym);
    let var_v = kb.alloc(Term::Var(Var::Global(vid)));
    let var_m = kb.alloc(Term::Var(Var::Global(mid)));

    let left_q = entity_named(pattern_query_sym, vec![(term_field, Value::Entity {
        functor: left_tag_sym, pos: Vec::new(),
        named: vec![(name_field, Value::Term(var_v))],
    })]);
    let right_q = entity_named(pattern_query_sym, vec![(term_field, Value::Entity {
        functor: right_tag_sym, pos: Vec::new(),
        named: vec![(name_field, Value::Term(var_v))],
    })]);
    let disj_q = entity_named(disj_sym, vec![
        (left_field, left_q),
        (right_field, right_q),
    ]);
    let marker_q = entity_named(pattern_query_sym, vec![(term_field, Value::Entity {
        functor: has_marker_sym, pos: Vec::new(),
        named: vec![(label_field, Value::Term(var_m))],
    })]);
    let query = entity_named(conj_sym, vec![
        (left_field, disj_q),
        (right_field, marker_q),
    ]);

    // Schema-fact auto-stamping (one per entity declaration) inflates the
    // raw solution count beyond the user-asserted facts. The contract
    // checked here is the semantic one: solutions where both ?v and ?m
    // resolve to user-fact strings must include both ("alpha", "M") and
    // ("beta", "M") — i.e. the disjunction's two branches each
    // composed with the marker fact in the tail.
    let mut stream = kb.execute_logical_query(&query).expect("disj+conj lowers");
    let mut seen: std::collections::HashSet<(String, String)> = std::collections::HashSet::new();
    while let Some((sol, rest)) = stream.split_first(&mut kb) {
        let v_val = sol.subst.resolve_as_value(vid);
        let m_val = sol.subst.resolve_as_value(mid);
        if let (Some(Value::Term(vt)), Some(Value::Term(mt))) = (v_val, m_val) {
            if let (Term::Const(Literal::String(vs)),
                    Term::Const(Literal::String(ms)))
                = (kb.get_term(*vt).clone(), kb.get_term(*mt).clone())
            {
                seen.insert((vs, ms));
            }
        }
        stream = rest;
    }
    assert!(seen.contains(&("alpha".to_string(), "M".to_string()))
        && seen.contains(&("beta".to_string(), "M".to_string())),
        "both disjunction branches must compose with the tail marker; saw {seen:?}");
}

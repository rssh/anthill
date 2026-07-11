//! Integration tests for proposal 026.1 Q3 — value-integrated KB queries
//! (WI-047). Covers `alloc_from_value` / `lower_query` / `execute_logical_query`.
//!
//! The eval-side builtin binding `anthill.reflect.KB.execute` to this
//! machinery is WI-048's responsibility (it produces a `Value::Stream`,
//! which needs the M4 stream arena). These tests exercise the KB API
//! directly and confirm that query results come back with `Value`-typed
//! substitution bindings.


use anthill_core::eval::Value;
use anthill_core::kb::execute::LowerError;
use anthill_core::kb::term::{Literal, Term, TermId, Var, VarId};

use crate::common::load_kb_with;

/// Build a `Value::Entity` wrapping a single named argument. Convenience for
/// writing LogicalQuery literals on the Rust side of the boundary.
fn entity_named(functor: anthill_core::intern::Symbol, named: Vec<(anthill_core::intern::Symbol, Value)>) -> Value {
    Value::Entity { functor, pos: Vec::new().into(), named: named.into() }
}

#[test]
fn q3_alloc_from_value_scalars_and_entity() {
    // alloc_from_value promotes runtime Values into hash-consed TermIds.
    // Two structurally equal Entities should dedupe to the same TermId.
    // The entity declares three fields so the mixed positional+named build is
    // well-formed (WI-500 made alloc_from_value reject an over-arity ctor — a
    // positional arg with no field to fill — like the loader does).
    let mut kb = load_kb_with(r#"
namespace test.q3_alloc
  import anthill.prelude.{Int64, String, Bool}
  sort Color
    import anthill.prelude.{Int64, String, Bool}
    entity red(x: Int64, y: String, n: Bool)
  end
end
"#);
    let red_sym = kb.try_resolve_symbol("test.q3_alloc.Color.red").expect("red symbol");
    let int_field = kb.intern("n");

    // pos fills the unfilled `x`, `y` (in declaration order); `n` is named.
    let v1 = Value::Entity {
        functor: red_sym,
        pos: vec![Value::Int(1), Value::Str("hi".into())].into(),
        named: vec![(int_field, Value::Bool(true))].into(),
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
        other => panic!("expected Const(Int64(7)), got {other:?}"),
    }
}

#[test]
fn q3_alloc_from_value_passes_through_term() {
    // Value::Term(tid) must reuse the existing TermId, not re-promote.
    let mut kb = load_kb_with("namespace test.q3_passthrough end\n");
    let n_sym = kb.intern("n");
    let n = kb.fresh_var(n_sym);
    let var_tid = kb.alloc(Term::Var(Var::Global(n)));

    let v = Value::term(var_tid);
    let got = kb.alloc_from_value(&v).expect("alloc term-variant");
    assert_eq!(got, var_tid);
}

#[test]
fn q3_alloc_from_value_rejects_closures_streams_lazies() {
    let mut kb = load_kb_with("namespace test.q3_rej end\n");

    // Unit has no KB-term representation either — covers the whole
    // "interpreter-only Value" class in one check.
    for v in [Value::Unit,
              Value::Tuple { pos: Vec::new().into(), named: Vec::new().into() }] {
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
    let q = Value::Entity { functor: empty_q_sym, pos: Vec::new().into(), named: Vec::new().into() };

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
        pos: Vec::new().into(),
        named: vec![(name_field, Value::term(var_n)), (fields_field, Value::term(var_f))].into(),
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
            Some(Value::Term { id: t, .. }) => {
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
    entity pair(x: Int64, y: Int64)
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
        pos: Vec::new().into(),
        named: vec![(x_field, Value::term(var_v)), (y_field, Value::term(var_y1))].into(),
    };
    let pat_y = Value::Entity {
        functor: pair_sym,
        pos: Vec::new().into(),
        named: vec![(x_field, Value::term(var_v)), (y_field, Value::term(var_y2))].into(),
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
            Some(Value::Term { id: t, .. }) => {
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
    let empty_q = Value::Entity { functor: empty_q_sym, pos: Vec::new().into(), named: Vec::new().into() };

    let sym_v = kb.intern("v");
    let any_sym = Value::term(kb.alloc(Term::Ref(sym_v)));
    let q = Value::Entity {
        functor: forall_sym,
        pos: Vec::new().into(),
        named: vec![
            (var_field, any_sym),
            (cond_field, empty_q.clone()),
            (body_field, empty_q),
        ].into(),
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
        pos: Vec::new().into(),
        named: vec![(name_field, Value::term(var_v))].into(),
    };
    let left_q = entity_named(pattern_query_sym, vec![(term_field, left_pattern)]);

    // pattern_query(right_tag(name: ?v))
    let right_pattern = Value::Entity {
        functor: right_tag_sym,
        pos: Vec::new().into(),
        named: vec![(name_field, Value::term(var_v))].into(),
    };
    let right_q = entity_named(pattern_query_sym, vec![(term_field, right_pattern)]);

    let query = entity_named(disj_sym, vec![
        (left_field, left_q),
        (right_field, right_q),
    ]);

    let mut stream = kb.execute_logical_query(&query).expect("disjunction lowers");
    // Dedup on ?v value — order-insensitive robustness (WI-515 removed the
    // schema-fact auto-stamping that used to multiply matches per branch).
    // The semantic contract checked here is: distinct ?v values come from
    // both branches.
    let mut seen = std::collections::HashSet::new();
    while let Some((sol, rest)) = stream.split_first(&mut kb) {
        if let Some(Value::Term { id: t, .. }) = sol.subst.resolve_as_value(vid) {
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
        functor: left_tag_sym, pos: Vec::new().into(),
        named: vec![(name_field, Value::term(var_v))].into(),
    })]);
    let right_q = entity_named(pattern_query_sym, vec![(term_field, Value::Entity {
        functor: right_tag_sym, pos: Vec::new().into(),
        named: vec![(name_field, Value::term(var_v))].into(),
    })]);
    let disj_q = entity_named(disj_sym, vec![
        (left_field, left_q),
        (right_field, right_q),
    ]);
    let marker_q = entity_named(pattern_query_sym, vec![(term_field, Value::Entity {
        functor: has_marker_sym, pos: Vec::new().into(),
        named: vec![(label_field, Value::term(var_m))].into(),
    })]);
    let query = entity_named(conj_sym, vec![
        (left_field, disj_q),
        (right_field, marker_q),
    ]);

    // The contract checked here is the semantic one: solutions where both
    // ?v and ?m resolve to user-fact strings must include both ("alpha",
    // "M") and ("beta", "M") — i.e. the disjunction's two branches each
    // composed with the marker fact in the tail. (WI-515: the schema-fact
    // auto-stamping that used to inflate the raw count is gone.)
    let mut stream = kb.execute_logical_query(&query).expect("disj+conj lowers");
    let mut seen: std::collections::HashSet<(String, String)> = std::collections::HashSet::new();
    while let Some((sol, rest)) = stream.split_first(&mut kb) {
        let v_val = sol.subst.resolve_as_value(vid);
        let m_val = sol.subst.resolve_as_value(mid);
        if let (Some(Value::Term { id: vt, .. }), Some(Value::Term { id: mt, .. })) = (v_val, m_val) {
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

#[test]
fn q3_nested_disjunction_yields_three_branches() {
    // disjunction(disjunction(A, B), C) — verifies that the lowering
    // recurses correctly: the outer disjunction's left branch is itself
    // a disjunction, and all three leaves contribute solutions.
    let mut kb = load_kb_with(r#"
namespace test.q3_disj_nested
  sort A
    entity a_tag(name: String)
  end
  sort B
    entity b_tag(name: String)
  end
  sort C
    entity c_tag(name: String)
  end
  fact a_tag(name: "alpha")
  fact b_tag(name: "beta")
  fact c_tag(name: "gamma")
end
"#);

    let a_sym = kb.try_resolve_symbol("test.q3_disj_nested.A.a_tag").unwrap();
    let b_sym = kb.try_resolve_symbol("test.q3_disj_nested.B.b_tag").unwrap();
    let c_sym = kb.try_resolve_symbol("test.q3_disj_nested.C.c_tag").unwrap();
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query").unwrap();
    let disj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.disjunction").unwrap();
    let term_field = kb.intern("term");
    let left_field = kb.intern("left");
    let right_field = kb.intern("right");
    let name_field = kb.intern("name");

    let v_sym = kb.intern("v");
    let vid = kb.fresh_var(v_sym);
    let var_v = kb.alloc(Term::Var(Var::Global(vid)));

    let pq = |functor| Value::Entity {
        functor: pattern_query_sym,
        pos: Vec::new().into(),
        named: vec![(term_field, Value::Entity {
            functor, pos: Vec::new().into(),
            named: vec![(name_field, Value::term(var_v))].into(),
        })].into(),
    };
    let q_a = pq(a_sym);
    let q_b = pq(b_sym);
    let q_c = pq(c_sym);
    let inner = entity_named(disj_sym, vec![(left_field, q_a), (right_field, q_b)]);
    let outer = entity_named(disj_sym, vec![(left_field, inner), (right_field, q_c)]);

    let mut stream = kb.execute_logical_query(&outer).expect("nested disjunction lowers");
    let mut seen = std::collections::HashSet::new();
    while let Some((sol, rest)) = stream.split_first(&mut kb) {
        if let Some(Value::Term { id: t, .. }) = sol.subst.resolve_as_value(vid) {
            if let Term::Const(Literal::String(s)) = kb.get_term(*t) {
                seen.insert(s.clone());
            }
        }
        stream = rest;
    }
    let expected: std::collections::HashSet<String> =
        ["alpha", "beta", "gamma"].iter().map(|s| s.to_string()).collect();
    assert_eq!(seen, expected, "all three nested branches must contribute");
}

#[test]
fn q3_disjunction_multi_goal_branch_lifts_via_synthesized_rule() {
    // Multi-goal disjunction branches lift through a synthesized
    // conjunction-rule head (proposal 033 §M4 / WI-076). The left branch
    // is `conjunction(left_tag(?v), other_tag(?v))` — a 2-goal body that
    // needs a synthesized head; the right branch is a single-goal pattern.
    // The query succeeds when both halves of the conjunction match a
    // single ?v ("alpha"), or when the right branch matches alone.
    let mut kb = load_kb_with(r#"
namespace test.q3_disj_multi
  sort Tag
    entity left_tag(name: String)
    entity other_tag(name: String)
    entity right_tag(name: String)
  end
  fact left_tag(name: "alpha")
  fact other_tag(name: "alpha")
  fact right_tag(name: "beta")
end
"#);

    let left_sym = kb.try_resolve_symbol("test.q3_disj_multi.Tag.left_tag").unwrap();
    let other_sym = kb.try_resolve_symbol("test.q3_disj_multi.Tag.other_tag").unwrap();
    let right_sym = kb.try_resolve_symbol("test.q3_disj_multi.Tag.right_tag").unwrap();
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query").unwrap();
    let disj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.disjunction").unwrap();
    let conj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.conjunction").unwrap();
    let term_field = kb.intern("term");
    let left_field = kb.intern("left");
    let right_field = kb.intern("right");
    let name_field = kb.intern("name");

    let v_sym = kb.intern("v");
    let vid = kb.fresh_var(v_sym);
    let var_v = kb.alloc(Term::Var(Var::Global(vid)));

    let pq = |functor| Value::Entity {
        functor: pattern_query_sym,
        pos: Vec::new().into(),
        named: vec![(term_field, Value::Entity {
            functor, pos: Vec::new().into(),
            named: vec![(name_field, Value::term(var_v))].into(),
        })].into(),
    };
    let multi_left = entity_named(conj_sym, vec![
        (left_field, pq(left_sym)),
        (right_field, pq(other_sym)),
    ]);
    let query = entity_named(disj_sym, vec![
        (left_field, multi_left),
        (right_field, pq(right_sym)),
    ]);

    let mut stream = kb.execute_logical_query(&query).expect("multi-goal lifts cleanly");
    let mut seen = std::collections::HashSet::new();
    while let Some((sol, rest)) = stream.split_first(&mut kb) {
        if let Some(Value::Term { id: t, .. }) = sol.subst.resolve_as_value(vid) {
            if let Term::Const(Literal::String(s)) = kb.get_term(*t) {
                seen.insert(s.clone());
            }
        }
        stream = rest;
    }
    let expected: std::collections::HashSet<String> =
        ["alpha", "beta"].iter().map(|s| s.to_string()).collect();
    assert_eq!(seen, expected,
        "left branch (conj of left_tag+other_tag) yields alpha; right branch yields beta");
}

#[test]
fn q3_disjunction_empty_branch_is_not_yet_implemented() {
    // empty_query branches still surface NYI — the true/false collapse
    // is a semantic decision the caller likely didn't intend.
    let mut kb = load_kb_with("namespace test.q3_disj_empty end\n");
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query").unwrap();
    let empty_q_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.empty_query").unwrap();
    let disj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.disjunction").unwrap();
    let entity_info_sym = kb.try_resolve_symbol("anthill.reflect.EntityInfo").unwrap();
    let term_field = kb.intern("term");
    let left_field = kb.intern("left");
    let right_field = kb.intern("right");
    let name_field = kb.intern("name");

    let n_sym = kb.intern("n");
    let vn = kb.fresh_var(n_sym);
    let var_n = kb.alloc(Term::Var(Var::Global(vn)));
    let some_pattern = entity_named(pattern_query_sym, vec![(term_field, Value::Entity {
        functor: entity_info_sym, pos: Vec::new().into(),
        named: vec![(name_field, Value::term(var_n))].into(),
    })]);
    let empty_q = Value::Entity { functor: empty_q_sym, pos: Vec::new().into(), named: Vec::new().into() };
    let query = entity_named(disj_sym, vec![
        (left_field, empty_q),
        (right_field, some_pattern),
    ]);

    let err = kb.lower_query(&query).unwrap_err();
    assert!(matches!(err, LowerError::NotYetImplemented(_)),
        "empty disjunction branch must still NYI; got {err:?}");
}

#[test]
fn q3_negation_multi_goal_lifts_via_synthesized_rule() {
    // Multi-goal negation lifts through the same synthesizer — proposal
    // 033 §M4 / WI-076. A `negation(conjunction(p, q))` lowers to
    // `not(_synth_N(?vars))` where the synthesized rule says
    // `_synth_N(?vars) :- p_goal, q_goal`. Test: a conjunction that's
    // unsatisfiable (left_tag and right_tag for the same ?v don't both
    // match any single ?v) negated should succeed.
    let mut kb = load_kb_with(r#"
namespace test.q3_neg_multi
  sort Tag
    entity left_tag(name: String)
    entity right_tag(name: String)
    entity probe(name: String)
  end
  fact left_tag(name: "alpha")
  fact right_tag(name: "beta")
  fact probe(name: "p")
end
"#);

    let left_sym = kb.try_resolve_symbol("test.q3_neg_multi.Tag.left_tag").unwrap();
    let right_sym = kb.try_resolve_symbol("test.q3_neg_multi.Tag.right_tag").unwrap();
    let probe_sym = kb.try_resolve_symbol("test.q3_neg_multi.Tag.probe").unwrap();
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query").unwrap();
    let neg_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.negation").unwrap();
    let conj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.conjunction").unwrap();
    let term_field = kb.intern("term");
    let left_field = kb.intern("left");
    let right_field = kb.intern("right");
    let query_field = kb.intern("query");
    let name_field = kb.intern("name");

    // ?v shared across the negated conjunction (forces the contradiction);
    // ?p binds the probe tag so the outer query has something to ground out.
    let v_sym = kb.intern("v");
    let p_sym = kb.intern("p");
    let vid = kb.fresh_var(v_sym);
    let pid = kb.fresh_var(p_sym);
    let var_v = kb.alloc(Term::Var(Var::Global(vid)));
    let var_p = kb.alloc(Term::Var(Var::Global(pid)));

    let pq = |functor, var| Value::Entity {
        functor: pattern_query_sym, pos: Vec::new().into(),
        named: vec![(term_field, Value::Entity {
            functor, pos: Vec::new().into(),
            named: vec![(name_field, Value::term(var))].into(),
        })].into(),
    };
    // negation(conjunction(left_tag(?v), right_tag(?v))) — multi-goal inner
    let inner_conj = entity_named(conj_sym, vec![
        (left_field, pq(left_sym, var_v)),
        (right_field, pq(right_sym, var_v)),
    ]);
    let negated = entity_named(neg_sym, vec![(query_field, inner_conj)]);
    // conjunction(probe(?p), negation(...)) — gives the outer query a
    // fact-bound goal so we have something to assert about.
    let outer = entity_named(conj_sym, vec![
        (left_field, pq(probe_sym, var_p)),
        (right_field, negated),
    ]);

    let mut stream = kb.execute_logical_query(&outer).expect("multi-goal negation lifts");
    let mut probe_seen = std::collections::HashSet::new();
    while let Some((sol, rest)) = stream.split_first(&mut kb) {
        if let Some(Value::Term { id: t, .. }) = sol.subst.resolve_as_value(pid) {
            if let Term::Const(Literal::String(s)) = kb.get_term(*t) {
                probe_seen.insert(s.clone());
            }
        }
        stream = rest;
    }
    assert!(probe_seen.contains("p"),
        "negation succeeds (the conjunction has no shared-?v witness), so probe ground binding surfaces; saw {probe_seen:?}");
}

#[test]
fn q3_synth_rule_memoized_across_repeated_queries() {
    // WI-169: re-issuing the SAME multi-goal query must REUSE one synthesized
    // conjunction-rule, not append a fresh `_synth_N` (+ rule slot + symbol +
    // discrim entry) per execution. Each iteration opens FRESH query vars (as a
    // real long-running query consumer would), so the memo has to canonicalize
    // the body's De Bruijn form to register a hit. The acceptance contract is
    // ZERO growth after the first execution — not merely sub-linear.
    let mut kb = load_kb_with(r#"
namespace test.q3_synth_memo
  sort Tag
    entity left_tag(name: String)
    entity other_tag(name: String)
    entity right_tag(name: String)
  end
  fact left_tag(name: "alpha")
  fact other_tag(name: "alpha")
  fact right_tag(name: "beta")
end
"#);

    let left_sym = kb.try_resolve_symbol("test.q3_synth_memo.Tag.left_tag").unwrap();
    let other_sym = kb.try_resolve_symbol("test.q3_synth_memo.Tag.other_tag").unwrap();
    let right_sym = kb.try_resolve_symbol("test.q3_synth_memo.Tag.right_tag").unwrap();
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query").unwrap();
    let disj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.disjunction").unwrap();
    let conj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.conjunction").unwrap();
    let term_field = kb.intern("term");
    let left_field = kb.intern("left");
    let right_field = kb.intern("right");
    let name_field = kb.intern("name");

    // Build + execute the same query shape once, opening a FRESH `?v` each time
    // so the synth body carries different Globals per run. Returns the bound
    // `name` strings so the caller can confirm results stay stable.
    let run_once = |kb: &mut anthill_core::kb::KnowledgeBase| -> std::collections::HashSet<String> {
        let v_sym = kb.intern("v");
        let vid = kb.fresh_var(v_sym);
        let var_v = kb.alloc(Term::Var(Var::Global(vid)));
        let pq = |functor| Value::Entity {
            functor: pattern_query_sym,
            pos: Vec::new().into(),
            named: vec![(term_field, Value::Entity {
                functor, pos: Vec::new().into(),
                named: vec![(name_field, Value::term(var_v))].into(),
            })].into(),
        };
        // disjunction(conjunction(left_tag(?v), other_tag(?v)), right_tag(?v)) —
        // the left branch is a 2-goal body that lifts via `synthesize_conjunction_rule`.
        let multi_left = entity_named(conj_sym, vec![
            (left_field, pq(left_sym)),
            (right_field, pq(other_sym)),
        ]);
        let query = entity_named(disj_sym, vec![
            (left_field, multi_left),
            (right_field, pq(right_sym)),
        ]);
        let mut stream = kb.execute_logical_query(&query).expect("multi-goal lifts cleanly");
        let mut seen = std::collections::HashSet::new();
        while let Some((sol, rest)) = stream.split_first(kb) {
            if let Some(Value::Term { id: t, .. }) = sol.subst.resolve_as_value(vid) {
                if let Term::Const(Literal::String(s)) = kb.get_term(*t) {
                    seen.insert(s.clone());
                }
            }
            stream = rest;
        }
        seen
    };

    let expected: std::collections::HashSet<String> =
        ["alpha", "beta"].iter().map(|s| s.to_string()).collect();

    // First execution mints the synth rule.
    assert_eq!(run_once(&mut kb), expected, "sanity: first run yields alpha+beta");
    let after_first = kb.rule_count();

    // Re-issue the identical query shape with fresh vars; the synth rule must
    // be reused, so the rule count stays CONSTANT.
    for _ in 0..5 {
        assert_eq!(run_once(&mut kb), expected, "results stable across repeats");
        assert_eq!(kb.rule_count(), after_first,
            "WI-169: repeated multi-goal query must reuse one synth rule (zero growth)");
    }
}

#[test]
fn q3_synth_rule_distinguishes_variable_sharing() {
    // WI-169 (structural key): two multi-goal bodies that differ ONLY in
    // variable sharing — `conj(left(?v), other(?v))` vs `conj(left(?v),
    // other(?w))` — MUST synthesize distinct rules. A key that treats vars as
    // wildcards (as a discrimination key does — pattern vars are var-edges, not
    // concrete keys) would collapse them onto one rule and resolve the unshared
    // body with shared-var semantics. The structural key preserves sharing by
    // numbering each var by first-occurrence position, so this catches a
    // wildcard-collapse two ways: the rule count, and the differing results.
    let mut kb = load_kb_with(r#"
namespace test.q3_synth_share
  sort Tag
    entity left_tag(name: String)
    entity other_tag(name: String)
    entity right_tag(name: String)
  end
  fact left_tag(name: "alpha")
  fact other_tag(name: "beta")
  fact right_tag(name: "gamma")
end
"#);

    let left_sym = kb.try_resolve_symbol("test.q3_synth_share.Tag.left_tag").unwrap();
    let other_sym = kb.try_resolve_symbol("test.q3_synth_share.Tag.other_tag").unwrap();
    let right_sym = kb.try_resolve_symbol("test.q3_synth_share.Tag.right_tag").unwrap();
    let pattern_query_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.pattern_query").unwrap();
    let disj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.disjunction").unwrap();
    let conj_sym = kb.try_resolve_symbol("anthill.reflect.LogicalQuery.conjunction").unwrap();
    let term_field = kb.intern("term");
    let left_field = kb.intern("left");
    let right_field = kb.intern("right");
    let name_field = kb.intern("name");

    // disjunction(conjunction(left_tag(?a), other_tag(?b)), right_tag(?a)) —
    // the conjunction branch lifts via the synthesizer; `?a` (collected) is the
    // outer variable the right branch also binds. Returns the bound `?a` names.
    let run = |kb: &mut anthill_core::kb::KnowledgeBase, a: TermId, b: TermId, aid: VarId|
        -> std::collections::HashSet<String>
    {
        let pq = |functor, v| Value::Entity {
            functor: pattern_query_sym, pos: Vec::new().into(),
            named: vec![(term_field, Value::Entity {
                functor, pos: Vec::new().into(),
                named: vec![(name_field, Value::term(v))].into(),
            })].into(),
        };
        let conj = entity_named(conj_sym, vec![
            (left_field, pq(left_sym, a)),
            (right_field, pq(other_sym, b)),
        ]);
        let query = entity_named(disj_sym, vec![
            (left_field, conj),
            (right_field, pq(right_sym, a)),
        ]);
        let mut stream = kb.execute_logical_query(&query).expect("lowers cleanly");
        let mut seen = std::collections::HashSet::new();
        while let Some((sol, rest)) = stream.split_first(kb) {
            if let Some(Value::Term { id: t, .. }) = sol.subst.resolve_as_value(aid) {
                if let Term::Const(Literal::String(s)) = kb.get_term(*t) { seen.insert(s.clone()); }
            }
            stream = rest;
        }
        seen
    };

    // Shared: conj(left(?v), other(?v)) — needs one name in BOTH tags; alpha≠beta
    // so the conjunction branch is empty and only right_tag's gamma surfaces.
    let v_sym = kb.intern("v");
    let vid = kb.fresh_var(v_sym);
    let var_v = kb.alloc(Term::Var(Var::Global(vid)));
    let shared = run(&mut kb, var_v, var_v, vid);
    let after_shared = kb.rule_count();

    // Unshared: conj(left(?v2), other(?w)) — independent vars, so the
    // conjunction matches (left=alpha, other=beta) and ?v2 binds alpha.
    let v2_sym = kb.intern("v2");
    let w_sym = kb.intern("w");
    let v2id = kb.fresh_var(v2_sym);
    let wid = kb.fresh_var(w_sym);
    let var_v2 = kb.alloc(Term::Var(Var::Global(v2id)));
    let var_w = kb.alloc(Term::Var(Var::Global(wid)));
    let unshared = run(&mut kb, var_v2, var_w, v2id);
    let after_unshared = kb.rule_count();

    // The bodies differ only in sharing, so they must NOT share a synth rule:
    // exactly one new rule appears for the unshared body.
    assert_eq!(after_unshared, after_shared + 1,
        "different variable-sharing bodies must not collapse onto one synth rule");

    // …and the semantics differ accordingly.
    assert!(shared.contains("gamma") && !shared.contains("alpha"),
        "shared ?v: conj unsatisfiable (alpha≠beta), only right branch; saw {shared:?}");
    assert!(unshared.contains("alpha") && unshared.contains("gamma"),
        "unshared: conj matches left=alpha; saw {unshared:?}");
}

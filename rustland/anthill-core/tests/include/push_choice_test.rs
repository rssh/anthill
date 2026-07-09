//! Resolver primitives: push_choice and the derived `or` rule.
//!
//! Proposal 033 / WI-075. Verifies that `anthill.kernel.push_choice(?a, ?b)`
//! creates a binary choice point with shared frame tail, and that the
//! `or(?a, ?b) :- push_choice(?a, ?b)` rule lifts the primitive to a
//! regular rule head.


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::parse;
use smallvec::SmallVec;

/// Build a `Term::Ref(qualified_name_sym)` term — matches how entities
/// stored in args appear in the KB after loading.
fn ref_term(kb: &mut KnowledgeBase, qualified: &str) -> TermId {
    let sym = kb.try_resolve_symbol(qualified)
        .unwrap_or_else(|| panic!("symbol {qualified} not in KB"));
    kb.alloc(Term::Ref(sym))
}

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let parsed_extra = parse::parse(extra)
        .unwrap_or_else(|e| panic!("parse extra: {e:?}"));
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p).unwrap();
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parsed_extra);
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    match load::load_all(&mut kb, &refs, &NullResolver) {
        Ok(_) => {}
        Err(errs) => {
            for e in &errs { eprintln!("LOAD ERR: {}", e); }
            panic!("load failed with {} errors", errs.len());
        }
    }
    kb
}

#[test]
fn push_choice_yields_two_solutions_via_facts() {
    // Both branches dispatch to user-defined predicates whose facts unify
    // with the goal. Each branch yields one solution.
    let src = r#"
        namespace test.pc.both
          sort Branch
            entity b1
            entity b2
          end
          fact left_branch(b1)
          fact right_branch(b2)
          rule chooses(?x)
            :- push_choice(left_branch(?x), right_branch(?x))
        end
    "#;
    let mut kb = load_with(src);
    let chooses_sym = kb.try_resolve_symbol("test.pc.both.chooses").unwrap();
    let x_sym = kb.intern("_x");
    let x_vid = kb.fresh_var(x_sym);
    let x_term = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(x_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: chooses_sym,
        pos_args: SmallVec::from_slice(&[x_term]),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig::default();
    let solutions = kb.resolve(&[goal], &cfg);
    assert_eq!(solutions.len(), 2, "two branches × one fact each = 2 solutions");

    // Distinct bindings for ?x: one solution has ?x = b1, other has ?x = b2.
    let b1 = ref_term(&mut kb, "test.pc.both.Branch.b1");
    let b2 = ref_term(&mut kb, "test.pc.both.Branch.b2");
    let mut bindings: Vec<u32> = solutions.iter()
        .map(|sol| kb.reify(x_term, &sol.subst).expect_term().raw())
        .collect();
    bindings.sort();
    let mut expected = vec![b1.raw(), b2.raw()];
    expected.sort();
    assert_eq!(bindings, expected, "branches must bind ?x to b1 and b2");
}

#[test]
fn push_choice_yields_one_solution_when_only_one_branch_matches() {
    // First branch's predicate has no facts; second branch's predicate
    // has one fact. Resolver yields exactly one solution from the
    // second branch.
    let src = r#"
        namespace test.pc.one
          sort Branch
            entity b1
            entity b2
          end
          fact right_branch(b1)
          rule chooses(?x)
            :- push_choice(missing_branch(?x), right_branch(?x))
        end
    "#;
    let mut kb = load_with(src);
    let chooses_sym = kb.try_resolve_symbol("test.pc.one.chooses").unwrap();
    let x_sym = kb.intern("_x");
    let x_vid = kb.fresh_var(x_sym);
    let x_term = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(x_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: chooses_sym,
        pos_args: SmallVec::from_slice(&[x_term]),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig::default();
    let solutions = kb.resolve(&[goal], &cfg);
    assert_eq!(solutions.len(), 1, "only the second branch should succeed");
    let b1 = ref_term(&mut kb, "test.pc.one.Branch.b1");
    assert_eq!(kb.reify(x_term, &solutions[0].subst).expect_term(), b1);
}

#[test]
fn push_choice_yields_zero_solutions_when_both_branches_fail() {
    // Both branches' predicates have no matching facts.
    let src = r#"
        namespace test.pc.none
          sort Branch
            entity b1
          end
          rule chooses(?x)
            :- push_choice(missing_a(?x), missing_b(?x))
        end
    "#;
    let mut kb = load_with(src);
    let chooses_sym = kb.try_resolve_symbol("test.pc.none.chooses").unwrap();
    let x_sym = kb.intern("_x");
    let x_vid = kb.fresh_var(x_sym);
    let x_term = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(x_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: chooses_sym,
        pos_args: SmallVec::from_slice(&[x_term]),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig::default();
    let solutions = kb.resolve(&[goal], &cfg);
    assert_eq!(solutions.len(), 0, "both branches fail — no solutions");
}

#[test]
fn or_rule_succeeds_via_either_branch_with_facts() {
    // The derived `or` rule lifts push_choice to a regular head functor.
    let src = r#"
        namespace test.pc.or_rule
          sort Tag
            entity t1
            entity t2
          end
          fact left_tag(t1)
          fact right_tag(t2)
          rule tagged(?x)
            :- or(left_tag(?x), right_tag(?x))
        end
    "#;
    let mut kb = load_with(src);
    let tagged_sym = kb.try_resolve_symbol("test.pc.or_rule.tagged").unwrap();
    let x_sym = kb.intern("_x");
    let x_vid = kb.fresh_var(x_sym);
    let x_term = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(x_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: tagged_sym,
        pos_args: SmallVec::from_slice(&[x_term]),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig::default();
    let solutions = kb.resolve(&[goal], &cfg);
    assert_eq!(solutions.len(), 2, "or should yield one solution per succeeding branch");

    let t1 = ref_term(&mut kb, "test.pc.or_rule.Tag.t1");
    let t2 = ref_term(&mut kb, "test.pc.or_rule.Tag.t2");
    let mut bindings: Vec<u32> = solutions.iter()
        .map(|sol| kb.reify(x_term, &sol.subst).expect_term().raw())
        .collect();
    bindings.sort();
    let mut expected = vec![t1.raw(), t2.raw()];
    expected.sort();
    assert_eq!(bindings, expected, "or branches must bind ?x to t1 and t2");
}

#[test]
fn push_choice_shares_tail_with_both_branches() {
    // push_choice(a, b), c — both branches must run c.
    // c is a fact-based goal that binds ?y. Verifies the shared-tail
    // contract: both Continuation candidates inherit frame.goals[1..].
    let src = r#"
        namespace test.pc.tail
          sort Tag
            entity t1
            entity t2
          end
          sort Marker
            entity m1
          end
          fact left_tag(t1)
          fact right_tag(t2)
          fact has_marker(m1)
          rule tagged(?x, ?y)
            :- push_choice(left_tag(?x), right_tag(?x)), has_marker(?y)
        end
    "#;
    let mut kb = load_with(src);
    let tagged_sym = kb.try_resolve_symbol("test.pc.tail.tagged").unwrap();
    let x_sym = kb.intern("_x");
    let y_sym = kb.intern("_y");
    let x_vid = kb.fresh_var(x_sym);
    let y_vid = kb.fresh_var(y_sym);
    let x_term = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(x_vid)));
    let y_term = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(y_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: tagged_sym,
        pos_args: SmallVec::from_slice(&[x_term, y_term]),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig::default();
    let solutions = kb.resolve(&[goal], &cfg);
    assert_eq!(solutions.len(), 2, "two branches × shared tail = 2 solutions");

    let m1 = ref_term(&mut kb, "test.pc.tail.Marker.m1");
    for sol in &solutions {
        let y_reified = kb.reify(y_term, &sol.subst).expect_term();
        assert_eq!(y_reified, m1, "tail goal must run on each branch");
    }

    let t1 = ref_term(&mut kb, "test.pc.tail.Tag.t1");
    let t2 = ref_term(&mut kb, "test.pc.tail.Tag.t2");
    let mut x_bindings: Vec<u32> = solutions.iter()
        .map(|sol| kb.reify(x_term, &sol.subst).expect_term().raw())
        .collect();
    x_bindings.sort();
    let mut expected = vec![t1.raw(), t2.raw()];
    expected.sort();
    assert_eq!(x_bindings, expected, "two branches yield distinct ?x");
}

#[test]
fn or_rule_handles_nested_disjunction() {
    // or(or(p, q), r) — three branches, shared variable binds to three
    // distinct values. Validates that the Continuation candidates from an
    // outer push_choice can themselves trigger an inner push_choice (via
    // the `or` rule unfolding) and that all three leaf solutions surface.
    let src = r#"
        namespace test.pc.nested
          sort Tag
            entity ta
            entity tb
            entity tc
          end
          fact branch_a(ta)
          fact branch_b(tb)
          fact branch_c(tc)
          rule chooses(?x)
            :- or(or(branch_a(?x), branch_b(?x)), branch_c(?x))
        end
    "#;
    let mut kb = load_with(src);
    let chooses_sym = kb.try_resolve_symbol("test.pc.nested.chooses").unwrap();
    let x_sym = kb.intern("_x");
    let x_vid = kb.fresh_var(x_sym);
    let x_term = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(x_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: chooses_sym,
        pos_args: SmallVec::from_slice(&[x_term]),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig::default();
    let solutions = kb.resolve(&[goal], &cfg);
    assert_eq!(solutions.len(), 3, "nested or yields one solution per leaf branch");

    let ta = ref_term(&mut kb, "test.pc.nested.Tag.ta");
    let tb = ref_term(&mut kb, "test.pc.nested.Tag.tb");
    let tc = ref_term(&mut kb, "test.pc.nested.Tag.tc");
    let mut bindings: Vec<u32> = solutions.iter()
        .map(|sol| kb.reify(x_term, &sol.subst).expect_term().raw())
        .collect();
    bindings.sort();
    let mut expected = vec![ta.raw(), tb.raw(), tc.raw()];
    expected.sort();
    assert_eq!(bindings, expected, "all three branches must contribute");
}

#[test]
fn or_rule_isolates_substitutions_across_branches() {
    // Branches that bind a shared ?x to different values must not leak
    // bindings across each other. After branch A binds ?x = ta, branch B
    // must start from σ where ?x is unbound and bind it to tb (not stay
    // pinned to ta).
    let src = r#"
        namespace test.pc.isolate
          sort Tag
            entity ta
            entity tb
          end
          fact branch_a(ta)
          fact branch_b(tb)
          rule chooses(?x)
            :- or(branch_a(?x), branch_b(?x))
        end
    "#;
    let mut kb = load_with(src);
    let chooses_sym = kb.try_resolve_symbol("test.pc.isolate.chooses").unwrap();
    let x_sym = kb.intern("_x");
    let x_vid = kb.fresh_var(x_sym);
    let x_term = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(x_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: chooses_sym,
        pos_args: SmallVec::from_slice(&[x_term]),
        named_args: SmallVec::new(),
    });
    let cfg = ResolveConfig::default();
    let solutions = kb.resolve(&[goal], &cfg);
    assert_eq!(solutions.len(), 2);

    let ta = ref_term(&mut kb, "test.pc.isolate.Tag.ta");
    let tb = ref_term(&mut kb, "test.pc.isolate.Tag.tb");
    let bindings: std::collections::HashSet<u32> = solutions.iter()
        .map(|sol| kb.reify(x_term, &sol.subst).expect_term().raw())
        .collect();
    let expected: std::collections::HashSet<u32> = [ta.raw(), tb.raw()].into_iter().collect();
    assert_eq!(bindings, expected,
        "σ isolation: each branch must bind ?x to its own value, not leak across");
}

#[test]
fn wi580_relational_append_solves_first_arg() {
    // WI-580 §3.3: abstract-interpretation-on-suspend. Solve `append(?a, [3]) =
    // [1,3]` for the unground first arg — the <=> rules can't (they need a
    // ground-headed first arg); the body-unfold case-split does, converging to
    // the unique ?a = [1].
    let src = r#"
        namespace test.wi580ra
          import anthill.prelude.List.{append, cons, nil}
          rule solve(?a) :- eq(append(?a, cons(head: 3, tail: nil)), cons(head: 1, tail: cons(head: 3, tail: nil)))
        end
    "#;
    let mut kb = load_with(src);
    let solve_sym = kb.try_resolve_symbol("test.wi580ra.solve").unwrap();
    let s = kb.intern("_a");
    let a_vid = kb.fresh_var(s);
    let a_term = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(a_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: solve_sym,
        pos_args: SmallVec::from_slice(&[a_term]),
        named_args: SmallVec::new(),
    });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    let definite: Vec<_> = sols.iter().filter(|s| s.is_definite()).collect();
    assert_eq!(definite.len(), 1, "expected exactly one definite solution; got {} total", sols.len());

    // ?a must be [1] = cons(head:1, tail:nil). Compare hash-consed TermIds.
    let one = kb.alloc(Term::Const(anthill_core::kb::term::Literal::Int(1)));
    let conss = kb.try_resolve_symbol("anthill.prelude.List.cons").unwrap();
    let fields = kb.entity_field_names(conss).expect("cons fields").to_vec();
    let (heads, tails) = (fields[0], fields[1]);
    let nilt = {
        let nils = kb.try_resolve_symbol("anthill.prelude.List.nil").unwrap();
        kb.alloc(Term::Ref(nils))
    };
    let mut na = SmallVec::<[(anthill_core::intern::Symbol, anthill_core::kb::term::TermId); 2]>::new();
    na.push((heads, one));
    na.push((tails, nilt));
    na.sort_by_key(|(s, _)| s.index());
    let expected = kb.alloc(Term::Fn { functor: conss, pos_args: SmallVec::new(), named_args: na });

    let got = match kb.reify(a_term, &definite[0].subst) {
        anthill_core::eval::Value::Term { id, .. } => id,
        other => panic!("?a should reify to a ground term; got {other:?}"),
    };
    assert_eq!(got, expected, "?a should be [1] (cons(1,nil))");
}

#[test]
fn wi580_catchall_arm_declines_no_overgeneration() {
    // WI-580 §3.3 soundness: a body with a catch-all (`_`) arm is NOT disjoint —
    // case-splitting it would need "earlier arms didn't match" negation guards
    // (undecidable on an unground scrutinee). `folded_call_match` declines, so a
    // relational `eq(label(?n), "nonzero")` DELAYS (residual) instead of wrongly
    // enumerating a definite ?n (which would assert label(?n)="nonzero" for ALL
    // ?n, including ?n=0 where label(0)="zero").
    let src = r#"
        namespace test.wi580ca
          import anthill.prelude.{Int64, String}
          operation label(n: Int64) -> String =
            match n
              case 0 -> "zero"
              case _ -> "nonzero"
          rule q(?n) :- eq(label(?n), "nonzero")
        end
    "#;
    let mut kb = load_with(src);
    let q = kb.try_resolve_symbol("test.wi580ca.q").unwrap();
    let s = kb.intern("_n");
    let nvid = kb.fresh_var(s);
    let nt = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(nvid)));
    let goal = kb.alloc(Term::Fn { functor: q, pos_args: SmallVec::from_slice(&[nt]), named_args: SmallVec::new() });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert!(
        sols.iter().all(|s| !s.is_definite()),
        "a catch-all body must not over-generate a definite answer; got {} solution(s), some definite",
        sols.len(),
    );
}

#[test]
fn wi580_op_call_other_operand_declines() {
    // WI-580 §3.3 soundness: when the OTHER eq operand is itself an unevaluated
    // bodied op-call, the residual/OTHER `unify` would compare it structurally
    // and wrongly fail (dropping real solutions). `unfold_eq_operand` declines
    // when OTHER carries an op-call, so the goal DELAYS (residual) as before —
    // never a wrong definite answer.
    let src = r#"
        namespace test.wi580oc
          import anthill.prelude.List.{append, cons, nil}
          rule q(?a, ?b) :- eq(append(?a, cons(head: 3, tail: nil)), append(?b, cons(head: 4, tail: nil)))
        end
    "#;
    let mut kb = load_with(src);
    let q = kb.try_resolve_symbol("test.wi580oc.q").unwrap();
    let sa = kb.intern("_a");
    let sb = kb.intern("_b");
    let av = kb.fresh_var(sa);
    let bv = kb.fresh_var(sb);
    let at = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(av)));
    let bt = kb.alloc(Term::Var(anthill_core::kb::term::Var::Global(bv)));
    let goal = kb.alloc(Term::Fn { functor: q, pos_args: SmallVec::from_slice(&[at, bt]), named_args: SmallVec::new() });
    let sols = kb.resolve(&[goal], &ResolveConfig::default());
    assert!(
        sols.iter().all(|s| !s.is_definite()),
        "an op-call OTHER operand must decline the unfold and delay; got {} solution(s), some definite",
        sols.len(),
    );
}

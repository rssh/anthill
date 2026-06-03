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
          export Branch
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
        .map(|sol| kb.reify(x_term, &sol.subst).as_term().unwrap().raw())
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
          export Branch
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
    assert_eq!(kb.reify(x_term, &solutions[0].subst).as_term().unwrap(), b1);
}

#[test]
fn push_choice_yields_zero_solutions_when_both_branches_fail() {
    // Both branches' predicates have no matching facts.
    let src = r#"
        namespace test.pc.none
          export Branch
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
          export Tag
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
        .map(|sol| kb.reify(x_term, &sol.subst).as_term().unwrap().raw())
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
          export Tag, Marker
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
        let y_reified = kb.reify(y_term, &sol.subst).as_term().unwrap();
        assert_eq!(y_reified, m1, "tail goal must run on each branch");
    }

    let t1 = ref_term(&mut kb, "test.pc.tail.Tag.t1");
    let t2 = ref_term(&mut kb, "test.pc.tail.Tag.t2");
    let mut x_bindings: Vec<u32> = solutions.iter()
        .map(|sol| kb.reify(x_term, &sol.subst).as_term().unwrap().raw())
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
          export Tag
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
        .map(|sol| kb.reify(x_term, &sol.subst).as_term().unwrap().raw())
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
          export Tag
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
        .map(|sol| kb.reify(x_term, &sol.subst).as_term().unwrap().raw())
        .collect();
    let expected: std::collections::HashSet<u32> = [ta.raw(), tb.raw()].into_iter().collect();
    assert_eq!(bindings, expected,
        "σ isolation: each branch must bind ?x to its own value, not leak across");
}

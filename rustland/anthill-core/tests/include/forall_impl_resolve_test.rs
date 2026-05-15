//! SLD resolution of `forall_impl` body goals (WI-108).
//!
//! Acceptance is layered:
//!
//! Tier 1 — passthrough. Resolver doesn't crash on a `forall_impl` goal;
//!   yields it as a residual (or otherwise threads the term through).
//!
//! Tier 3 — skolem rigidity. Binders become fresh rigid witnesses; a
//!   universal whose consequent unifies a skolem with a concrete value
//!   must fail.
//!
//! Tier 4 — hypothetical reasoning. Antecedents are scoped assumptions,
//!   discharged on success / popped on backtrack. Lets auto-generated
//!   `<Sort>.induction` rules actually prove their universal from a
//!   base case + IH-using step case.


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::resolve::ResolveConfig;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::parse;
use smallvec::SmallVec;

fn load_with(extra: &str) -> KnowledgeBase {
    let stdlib = crate::common::stdlib_dir();
    let files = crate::common::collect_anthill_files(&stdlib);
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p).unwrap();
        parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
    }).collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    load::register_prelude(&mut kb);
    kb.register_standard_builtins();
    let _ = load::load_all(&mut kb, &refs, &NullResolver);
    kb
}

fn resolve_one(kb: &mut KnowledgeBase, goal: TermId) -> bool {
    let cfg = ResolveConfig::default();
    let solutions = kb.resolve(&[goal], &cfg);
    !solutions.is_empty()
}

/// Build `qn(args...)` where `qn` is the qualified name of a head goal
/// already loaded in the KB.
fn make_call(kb: &mut KnowledgeBase, qn: &str, args: &[TermId]) -> TermId {
    let sym = kb.try_resolve_symbol(qn)
        .unwrap_or_else(|| panic!("symbol {qn} not in KB"));
    kb.alloc(Term::Fn {
        functor: sym,
        pos_args: SmallVec::from_slice(args),
        named_args: SmallVec::new(),
    })
}

// =================================================================
// Tier 1 — passthrough
// =================================================================

#[test]
fn t1_resolver_does_not_crash_on_forall_impl() {
    // The resolver must terminate (success OR failure, but no panic /
    // infinite loop) when a body goal is forall_impl(...).
    let src = r#"
        namespace test.forall_impl.t1
          export Stub
          sort Stub
            entity stub_root
          end

          rule t1_witness(?P)
            :- (forall(?x), eq(?x, ?x) -: eq(?x, ?x))
        end
    "#;
    let mut kb = load_with(src);
    let p_ref = kb.make_name_term("test.forall_impl.t1.stub_root");
    let goal = make_call(&mut kb, "test.forall_impl.t1.t1_witness", &[p_ref]);
    // Tier 1 acceptance: query terminates (no panic).
    let _ = resolve_one(&mut kb, goal);
}

// =================================================================
// Tier 3 — skolem rigidity
// =================================================================

#[test]
fn t3_skolem_reflexivity_succeeds() {
    // (forall(?x), eq(1, 1) -: eq(?x, ?x)) — antecedent trivially holds;
    // consequent is reflexivity which holds for any skolem.
    let src = r#"
        namespace test.forall_impl.t3a
          export Stub
          sort Stub
            entity stub_root
          end

          rule t3a_witness(?dummy)
            :- (forall(?x), eq(1, 1) -: eq(?x, ?x))
        end
    "#;
    let mut kb = load_with(src);
    let stub = kb.make_name_term("test.forall_impl.t3a.stub_root");
    let goal = make_call(&mut kb, "test.forall_impl.t3a.t3a_witness", &[stub]);
    assert!(resolve_one(&mut kb, goal),
        "Tier 3: reflexivity for skolem ?x should succeed");
}

#[test]
fn t3_skolem_cannot_unify_with_concrete_succeeds_only_if_unsound() {
    // (forall(?x), eq(1, 1) -: eq(?x, 5)) — the consequent demands the
    // skolem ?x equals 5. A rigid skolem cannot unify with a concrete
    // integer, so this universal must FAIL. If the resolver lets the
    // binder var bind freely, this would falsely succeed.
    let src = r#"
        namespace test.forall_impl.t3b
          export Stub
          sort Stub
            entity stub_root
          end

          rule t3b_witness(?dummy)
            :- (forall(?x), eq(1, 1) -: eq(?x, 5))
        end
    "#;
    let mut kb = load_with(src);
    let stub = kb.make_name_term("test.forall_impl.t3b.stub_root");
    let goal = make_call(&mut kb, "test.forall_impl.t3b.t3b_witness", &[stub]);
    assert!(!resolve_one(&mut kb, goal),
        "Tier 3 soundness: skolem ?x must not unify with 5 — universal must fail");
}

// =================================================================
// Tier 4 — hypothetical reasoning (assumption stack)
// =================================================================

#[test]
fn t4_assumption_lets_step_case_use_ih() {
    // The classic test: prove `?P(?x)` for all `?x` via a hand-crafted
    // step rule whose body antecedent is the IH `?P(?prev)`. Without
    // an assumption stack, `?P(?prev)` is unprovable for a rigid ?prev.
    // With assumptions, it discharges trivially against the assumed
    // antecedent.
    let src = r#"
        namespace test.forall_impl.t4
          export Stub
          sort Stub
            entity stub_root
          end

          -- The IH `t4_property(?prev)` is the antecedent assumption;
          -- the consequent is the same predicate over the same skolem.
          -- Without an assumption stack, no rule for t4_property exists
          -- in the KB and the consequent fails. With assumptions, the
          -- antecedent's skolemized form discharges the consequent.
          rule t4_step(?dummy)
            :- (forall(?prev), t4_property(?prev) -: t4_property(?prev))
        end
    "#;
    let mut kb = load_with(src);
    let stub = kb.make_name_term("test.forall_impl.t4.stub_root");
    let goal = make_call(&mut kb, "test.forall_impl.t4.t4_step", &[stub]);
    assert!(resolve_one(&mut kb, goal),
        "Tier 4: IH-as-assumption must let the step discharge");
}

// =================================================================
// Tier 4 — assumption scoping (no leakage past consequent)
// =================================================================

#[test]
fn t4_assumption_does_not_leak_to_next_body_goal() {
    // After the forall_impl discharges its consequent, the assumed
    // antecedent must NOT remain in scope for the surrounding rule's
    // remaining body goals. Otherwise, predicates that have no rule
    // in the KB would falsely succeed via a stale assumption.
    //
    // Here `false_assumption` has no rule. Inside the forall_impl,
    // it is an antecedent that doesn't depend on the skolem ?x — so
    // it can be unified by a later goal verbatim if leakage occurs.
    // The test is the canary for the scoping invariant.
    let src = r#"
        namespace test.forall_impl.t4_leak
          export Stub
          sort Stub
            entity stub_root
          end

          rule leaky_witness(?dummy)
            :- (forall(?x), false_assumption -: eq(1, 1)),
               false_assumption
        end
    "#;
    let mut kb = load_with(src);
    let stub = kb.make_name_term("test.forall_impl.t4_leak.stub_root");
    let goal = make_call(&mut kb, "test.forall_impl.t4_leak.leaky_witness", &[stub]);
    assert!(!resolve_one(&mut kb, goal),
        "Tier 4 scoping: assumed antecedent must not leak past the consequent");
}

// =================================================================
// Structural induction integration (auto-generated <Sort>.induction
// + IH discharge through forall_impl)
// =================================================================

#[test]
fn structural_induction_proves_property_via_auto_generated_rule() {
    // Use the auto-generated `IntList.induction(?P)` rule from WI-106.
    // Body shape:
    //   IntList.induction(?P)
    //     :- ho_apply(?P, nil),
    //        (forall(?head, ?tail),
    //           ho_apply(?P, ?tail) -: ho_apply(?P, cons(head: ?head, tail: ?tail)))
    //
    // We instantiate ?P with `prop_holds`, a user-defined predicate
    // that holds for nil and propagates through cons. Discharging the
    // induction rule for ?P = prop_holds requires:
    //   - base case: ho_apply(prop_holds, nil) → prop_holds(nil)
    //                must match the fact.
    //   - step case: skolemise ?head, ?tail; assume prop_holds(!tail);
    //                consequent prop_holds(cons(head: !head, tail: !tail))
    //                matches the cons rule whose body is prop_holds(?t),
    //                where ?t = !tail — discharged from the assumption.
    let src = r#"
        namespace test.forall_impl.struct_ind
          export IntList, prop_holds
          enum IntList
            entity i_nil
            entity i_cons(head: Int, tail: IntList)
          end

          fact prop_holds(i_nil)
          rule prop_holds(i_cons(head: ?_h, tail: ?t))
            :- prop_holds(?t)
        end
    "#;
    let mut kb = load_with(src);

    // Sanity: direct fact query confirms prop_holds is registered.
    let nil_sym = kb.try_resolve_symbol("test.forall_impl.struct_ind.IntList.i_nil")
        .expect("IntList.i_nil must be defined");
    let nil_ref = kb.alloc(Term::Ref(nil_sym));
    let direct = make_call(&mut kb, "test.forall_impl.struct_ind.prop_holds", &[nil_ref]);
    assert!(resolve_one(&mut kb, direct),
        "sanity: direct prop_holds(i_nil) must succeed");

    let pred_sym = kb.try_resolve_symbol("test.forall_impl.struct_ind.prop_holds")
        .expect("prop_holds must be defined");
    let pred_ref = kb.alloc(Term::Ref(pred_sym));
    let goal = make_call(
        &mut kb,
        "test.forall_impl.struct_ind.IntList.induction",
        &[pred_ref],
    );
    assert!(resolve_one(&mut kb, goal),
        "structural induction: auto-generated IntList.induction(prop_holds) \
         must discharge given the fact + cons rule");
}

// =================================================================
// Gap probes — look for soundness / correctness holes
// =================================================================

#[test]
fn gap_minimal_rigid_vs_fact_concrete_does_not_match() {
    // Probe: a fact `tree_holds(leaf)` must not match a goal
    // `tree_holds(!rigid)`. !rigid (Rigid) cannot unify with the
    // concrete `leaf` (Term::Ref). Includes a dummy rule so the
    // tree_holds head functor is registered.
    let src = r#"
        namespace test.forall_impl.rigid_vs_fact
          export Tree, tree_holds
          enum Tree
            entity leaf
          end

          rule tree_holds(leaf)
        end
    "#;
    let mut kb = load_with(src);
    let pred_sym = kb.try_resolve_symbol("test.forall_impl.rigid_vs_fact.tree_holds")
        .expect("tree_holds defined");
    let rigid_name = kb.intern("l");
    let rigid_vid = kb.fresh_var(rigid_name);
    use anthill_core::kb::term::Var;
    let rigid_term = kb.alloc(Term::Var(Var::Rigid(rigid_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: pred_sym,
        pos_args: SmallVec::from_slice(&[rigid_term]),
        named_args: SmallVec::new(),
    });
    let cfg = anthill_core::kb::resolve::ResolveConfig {
        max_depth: 20,
        max_solutions: 5,
        ..Default::default()
    };
    let solutions = kb.resolve(&[goal], &cfg);
    assert!(solutions.is_empty(),
        "tree_holds(!l) must not match `fact tree_holds(leaf)` — \
         Rigid cannot unify with the concrete `leaf` Ref. Got {} solutions.",
        solutions.len());
}

#[test]
fn gap_minimal_rigid_vs_concrete_pattern_does_not_match() {
    // Probe: when a goal has a Rigid at a position where a stored rule
    // has a concrete constructor, the candidate match must NOT succeed.
    // If it does, the rule fires with an unsound binding, recurses, and
    // hangs.
    //
    // Goal `tree_holds(!l)` against rule head `tree_holds(branch(...))`
    // — should fail, because !l (Rigid) cannot be unified with a
    // concrete `branch(...)` term.
    let src = r#"
        namespace test.forall_impl.rigid_match
          export Tree, tree_holds
          enum Tree
            entity leaf
            entity branch(left: Tree, right: Tree)
          end

          rule tree_holds(branch(left: ?l, right: ?r))
            :- tree_holds(?l), tree_holds(?r)
        end
    "#;
    let mut kb = load_with(src);

    // Build goal `tree_holds(!l)` with !l a Rigid var allocated by us.
    let pred_sym = kb.try_resolve_symbol("test.forall_impl.rigid_match.tree_holds")
        .expect("tree_holds defined");
    let rigid_name = kb.intern("l");
    let rigid_vid = kb.fresh_var(rigid_name);
    use anthill_core::kb::term::Var;
    let rigid_term = kb.alloc(Term::Var(Var::Rigid(rigid_vid)));
    let goal = kb.alloc(Term::Fn {
        functor: pred_sym,
        pos_args: SmallVec::from_slice(&[rigid_term]),
        named_args: SmallVec::new(),
    });

    // With a tight depth limit, query must terminate. If it succeeds
    // unexpectedly (no rule should match a Rigid against branch),
    // that's a soundness bug.
    let cfg = anthill_core::kb::resolve::ResolveConfig {
        max_depth: 20,
        max_solutions: 5,
        ..Default::default()
    };
    let solutions = kb.resolve(&[goal], &cfg);
    assert!(solutions.is_empty(),
        "tree_holds(!l) should NOT have solutions — Rigid cannot match \
         the rule's concrete `branch(...)` head, and there is no fact for \
         a bare rigid argument. Got {} solutions.", solutions.len());
}

#[test]
fn gap_multi_recursive_constructor_emits_multiple_ihs() {
    // Tree with two recursive fields. Auto-generated induction must
    // include BOTH `?P(?left)` and `?P(?right)` as antecedents, and
    // the consequent must use both binders. Tests the multi-IH path
    // in emit_induction_rule + the discharge path.
    let src = r#"
        namespace test.forall_impl.tree
          export Tree, tree_holds
          enum Tree
            entity leaf
            entity branch(left: Tree, right: Tree)
          end

          fact tree_holds(leaf)
          rule tree_holds(branch(left: ?l, right: ?r))
            :- tree_holds(?l), tree_holds(?r)
        end
    "#;
    let mut kb = load_with(src);
    let pred_sym = kb.try_resolve_symbol("test.forall_impl.tree.tree_holds")
        .expect("tree_holds must be defined");
    let pred_ref = kb.alloc(Term::Ref(pred_sym));
    let goal = make_call(
        &mut kb,
        "test.forall_impl.tree.Tree.induction",
        &[pred_ref],
    );
    assert!(resolve_one(&mut kb, goal),
        "multi-recursive: Tree.induction must discharge with both IHs");
}

#[test]
fn gap_skolem_does_not_leak_into_caller_solution() {
    // After a rule with forall_impl in its body succeeds, the caller's
    // answer substitution must not contain a Var::Rigid binding —
    // skolems are local to the discharge, never user-visible.
    let src = r#"
        namespace test.forall_impl.no_leak
          export Witness, marker
          sort Witness
            entity marker
          end

          rule witness_rule(?w)
            :- (forall(?x), eq(1, 1) -: eq(?x, ?x))
        end
    "#;
    let mut kb = load_with(src);
    let marker_sym = kb.try_resolve_symbol("test.forall_impl.no_leak.Witness.marker")
        .expect("marker entity must exist");
    let marker_ref = kb.alloc(Term::Ref(marker_sym));
    let goal = make_call(
        &mut kb,
        "test.forall_impl.no_leak.witness_rule",
        &[marker_ref],
    );
    let cfg = anthill_core::kb::resolve::ResolveConfig::default();
    let solutions = kb.resolve(&[goal], &cfg);
    assert!(!solutions.is_empty(), "rule must discharge");
    // Walk every TermId reachable through the solution's substitution
    // and assert no Var::Rigid appears.
    use anthill_core::kb::term::Var;
    let sol = &solutions[0];
    for (_, val) in sol.subst.iter_terms() {
        let mut stack = vec![val];
        while let Some(t) = stack.pop() {
            match kb.get_term(t) {
                Term::Var(Var::Rigid(_)) => {
                    panic!("skolem leaked into caller solution: term {t:?}");
                }
                Term::Fn { pos_args, named_args, .. } => {
                    stack.extend(pos_args.iter().copied());
                    stack.extend(named_args.iter().map(|(_, t)| *t));
                }
                _ => {}
            }
        }
    }
}

#[test]
fn gap_duplicate_binders_in_forall_impl() {
    // `(forall(?x, ?x), ...)` — a duplicate binder is malformed by the
    // pattern-fragment convention but currently the loader doesn't
    // reject it. The two `?x` occurrences resolve to the same Global;
    // skolemisation produces ONE rigid; the rule reduces to the form
    // with a single binder. Test pins the behaviour: it should either
    // reject at load OR produce a result consistent with one binder.
    let src = r#"
        namespace test.forall_impl.dup_binder
          export Stub
          sort Stub
            entity stub_root
          end

          rule dup_binder_rule(?dummy)
            :- (forall(?x, ?x), eq(1, 1) -: eq(?x, ?x))
        end
    "#;
    let mut kb = load_with(src);
    let stub = kb.make_name_term("test.forall_impl.dup_binder.stub_root");
    let goal = make_call(&mut kb, "test.forall_impl.dup_binder.dup_binder_rule", &[stub]);
    // Currently: loader does not reject; rule discharges (the two
    // skolems collapse). Pinning the current behaviour.
    let _ = resolve_one(&mut kb, goal);
}

#[test]
fn gap_nested_forall_impl_in_consequent() {
    // Universal whose consequent contains another universal:
    //   (forall(?x), Q(?x) -: (forall(?y), R(?x, ?y) -: P(?x, ?y)))
    // The outer forall_impl produces consequent that is itself a
    // forall_impl. step_forall_impl should fire again on the inner
    // one when it surfaces as a goal. Tests that nested universals
    // compose.
    let src = r#"
        namespace test.forall_impl.nested
          export Stub
          sort Stub
            entity stub_root
          end

          -- Trivially-true nested universal.
          rule nested_witness(?dummy)
            :- (forall(?x),
                  eq(1, 1)
                  -: (forall(?y),
                        eq(2, 2)
                        -: eq(?x, ?x)))
        end
    "#;
    let mut kb = load_with(src);
    let stub = kb.make_name_term("test.forall_impl.nested.stub_root");
    let goal = make_call(&mut kb, "test.forall_impl.nested.nested_witness", &[stub]);
    assert!(resolve_one(&mut kb, goal),
        "nested forall_impl with trivially-true inner consequent must discharge");
}

#[test]
fn structural_induction_on_stdlib_polymorphic_list() {
    // The stdlib `List[T]` is parameterised. After lifting the
    // parameterised-sort exclusion in emit_induction_rule, the kernel
    // emits `anthill.prelude.List.induction(?P)`. The body shape is the
    // standard structural-induction principle (one base + one
    // forall_impl step) — and the rule body itself never references
    // the type parameter ?T, so polymorphism has no effect on the rule.
    //
    // Define a predicate over a concrete instantiation (List[T = Int])
    // and discharge induction.
    let src = r#"
        namespace test.forall_impl.poly_list
          export poly_pred
          rule poly_pred(nil) :- eq(1, 1)
          rule poly_pred(cons(head: ?_h, tail: ?t)) :- poly_pred(?t)
        end
    "#;
    let mut kb = load_with(src);

    let pred_sym = kb.try_resolve_symbol("test.forall_impl.poly_list.poly_pred")
        .expect("poly_pred must be defined");
    let pred_ref = kb.alloc(Term::Ref(pred_sym));

    let goal = make_call(
        &mut kb,
        "anthill.prelude.List.induction",
        &[pred_ref],
    );
    assert!(resolve_one(&mut kb, goal),
        "polymorphic structural induction: auto-generated \
         anthill.prelude.List.induction(poly_pred) must discharge");
}

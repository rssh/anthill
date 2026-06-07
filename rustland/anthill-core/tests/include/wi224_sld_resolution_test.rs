//! WI-224 — full SLD-based instance synthesis.
//!
//! Replaces the single-shot `find_unique_impl_op` with `resolve(goal,
//! scope) -> ResolutionResult` per `docs/design/operation-call-model.md`
//! §"Resolution". This file pins the acceptance criteria:
//!
//! 1. Leaf instance resolution (non-conditional `fact Spec[..]`).
//! 2. One-level conditional (`fact Eq[T = List[T = ?A]] :- Eq[T = ?A]`).
//! 3. Two-level conditional (`Eq[T = List[T = List[T = X]]]` — Example 8).
//! 4. Ambiguous diagnostic for multiple matching impls (no specificity).
//! 5. Cyclic diagnostic for ill-founded resolution (`A :- B; B :- A`).
//! 6. NoMatch diagnostic with helpful hint.
//! 7. Coherence at diamond join points (Example 3).


use anthill_core::kb::KnowledgeBase;
use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::typing::{
    resolve, sort_goal_from_subst, ResolutionScope, ResolvedRequiresNode, ResolutionResult, SortGoal,
    requires_chain_flat,
};
use anthill_core::kb::term::{Term, TermId, Var};
use anthill_core::parse;
use smallvec::SmallVec;

/// Load stdlib + rustland bindings + an extra source string.
fn load_with(extra: &str) -> KnowledgeBase {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files.iter().map(|p| {
        let src = std::fs::read_to_string(p)
            .unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
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

/// Build a goal `<spec>[<param> = <carrier>]` directly. Uses
/// `sort_goal_from_subst` to mirror the typer's call-site goal
/// construction (going through SortAlias → Var → subst).
fn goal_for(kb: &mut KnowledgeBase, spec_qn: &str, param_short: &str, carrier_qn: &str) -> SortGoal {
    let spec_sym = kb.try_resolve_symbol(spec_qn)
        .unwrap_or_else(|| panic!("{spec_qn} not registered"));
    let param_qn = format!("{spec_qn}.{param_short}");
    let param_sym = kb.try_resolve_symbol(&param_qn)
        .unwrap_or_else(|| panic!("{param_qn} not registered"));
    let alias_sym = kb.try_resolve_symbol("SortAlias").expect("SortAlias");
    let mut param_var = None;
    for rid in kb.rules_by_functor(alias_sym) {
        if !kb.is_fact(rid) { continue; }
        let head = kb.rule_head(rid);
        if let Term::Fn { pos_args, .. } = kb.get_term(head).clone() {
            if pos_args.len() < 2 { continue; }
            if let Term::Fn { functor, .. } = kb.get_term(pos_args[0]) {
                if *functor == param_sym {
                    if let Term::Var(Var::Global(v)) = kb.get_term(pos_args[1]) {
                        param_var = Some(*v);
                    }
                }
            }
        }
    }
    let param_var = param_var.unwrap_or_else(||
        panic!("{}'s SortAlias not found for {spec_qn}", param_short));
    let carrier_sym = kb.try_resolve_symbol(carrier_qn)
        .unwrap_or_else(|| panic!("{carrier_qn} not registered"));
    let carrier_term = kb.make_sort_ref(carrier_sym);
    let mut subst = Substitution::new();
    subst.bind_term(param_var, carrier_term);
    // WI-350: these SLD-resolution tests dispatch by binding (the carrier
    // here is the binding *value*, not a self-receiver carrier).
    sort_goal_from_subst(kb, &subst, spec_sym, None)
}

/// Build a parametric carrier value `Outer[Param = Inner]` (e.g.,
/// `List[T = Int64]`). Used to test conditional resolution where the
/// goal's binding value is itself a parametric type.
fn parametric_carrier(
    kb: &mut KnowledgeBase,
    outer_qn: &str,
    param_short: &str,
    inner_qn: &str,
) -> TermId {
    let outer_sym = kb.try_resolve_symbol(outer_qn)
        .unwrap_or_else(|| panic!("{outer_qn} not registered"));
    let inner_sym = kb.try_resolve_symbol(inner_qn)
        .unwrap_or_else(|| panic!("{inner_qn} not registered"));
    let inner_ref = kb.alloc(Term::Ref(inner_sym));
    let param_sym = kb.intern(param_short);
    kb.alloc(Term::Fn {
        functor: outer_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(param_sym, inner_ref)]),
    })
}

/// Empty scope (no available_requires). Substitution is unused by the
/// scope itself — the goal already carries the per-call values.
fn empty_scope<'a>(_subst: &'a Substitution) -> ResolutionScope<'a> {
    ResolutionScope { available_requires: &[] }
}

// ── (1) Leaf instance resolution ─────────────────────────────────

#[test]
fn leaf_resolution_picks_concrete_impl() {
    // Eq[T = Int64] resolves to the IntEq leaf — stdlib registers
    // `fact Eq[T = Int64]` in the rustland bindings.
    let mut kb = load_with("");
    let goal = goal_for(&mut kb, "anthill.prelude.Eq", "T", "anthill.prelude.Int64");
    let subst = Substitution::new();
    let scope = empty_scope(&subst);
    let result = resolve(&mut kb, &goal, &scope);
    match result {
        ResolutionResult::Resolved(ResolvedRequiresNode::Leaf { impl_sort, .. }) => {
            let impl_qn = kb.qualified_name_of(impl_sort).to_string();
            assert!(impl_qn.ends_with(".Int64") || impl_qn == "anthill.prelude.Int64"
                || impl_qn.ends_with("IntEq"),
                "expected an Int64-or-IntEq leaf; got {impl_qn}");
        }
        other => panic!("expected Resolved::Leaf for Eq[T=Int64]; got {other:?}"),
    }
}

// ── (2) One-level conditional ────────────────────────────────────

#[test]
fn one_level_conditional_resolves_via_subgoal() {
    // EqList provides Eq[List[T=A]] conditional on Eq[T=A]. Resolving
    // Eq[T = List[T = Int64]] must produce a Conditional node whose
    // sub_resolution is Eq[T = Int64]'s leaf impl.
    let src = r#"
        namespace test.wi224.one_level
          import anthill.prelude.{Eq, List, Int64}
          export EqList
          sort EqList
            sort A = ?
            requires Eq[T = A]
            fact Eq[T = List[T = A]]
          end
        end
    "#;
    let mut kb = load_with(src);

    // Build goal Eq[T = List[T = Int64]].
    let list_int = parametric_carrier(
        &mut kb, "anthill.prelude.List", "T", "anthill.prelude.Int64");
    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq").expect("Eq");
    let t_sym = kb.intern("T");
    let goal = SortGoal {
        spec_sort: eq_sym,
        bindings: SmallVec::from_slice(&[(t_sym, list_int)]),
        carrier: None,
    };
    let subst = Substitution::new();
    let scope = empty_scope(&subst);
    match resolve(&mut kb, &goal, &scope) {
        ResolutionResult::Resolved(ResolvedRequiresNode::Conditional { impl_sort, sub_resolutions, .. }) => {
            let impl_qn = kb.qualified_name_of(impl_sort).to_string();
            assert_eq!(impl_qn, "test.wi224.one_level.EqList",
                "expected EqList as the conditional impl; got {impl_qn}");
            assert_eq!(sub_resolutions.len(), 1,
                "EqList has one requires (`Eq[T=A]`); got {} sub_resolutions",
                sub_resolutions.len());
            match &sub_resolutions[0] {
                ResolvedRequiresNode::Leaf { impl_sort: inner, .. } => {
                    let inner_qn = kb.qualified_name_of(*inner).to_string();
                    assert!(inner_qn.contains("Int64"),
                        "expected inner subgoal to resolve to an Int64 leaf; got {inner_qn}");
                }
                other => panic!("inner sub_resolution should be a Leaf; got {other:?}"),
            }
        }
        other => panic!("expected Conditional resolution for Eq[List[Int64]]; got {other:?}"),
    }
}

// ── (3) Two-level conditional (Example 8) ────────────────────────

#[test]
fn two_level_conditional_chains_recursively() {
    // Eq[List[List[Int64]]] resolves through two EqList layers, each
    // descending to the inner type's Eq impl.
    let src = r#"
        namespace test.wi224.two_level
          import anthill.prelude.{Eq, List, Int64}
          export EqList
          sort EqList
            sort A = ?
            requires Eq[T = A]
            fact Eq[T = List[T = A]]
          end
        end
    "#;
    let mut kb = load_with(src);

    // Build the outer goal: Eq[T = List[T = List[T = Int64]]].
    let list_int = parametric_carrier(
        &mut kb, "anthill.prelude.List", "T", "anthill.prelude.Int64");
    let list_sym = kb.try_resolve_symbol("anthill.prelude.List").expect("List");
    let t_sym = kb.intern("T");
    let list_list_int = kb.alloc(Term::Fn {
        functor: list_sym,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(t_sym, list_int)]),
    });

    let eq_sym = kb.try_resolve_symbol("anthill.prelude.Eq").expect("Eq");
    let goal = SortGoal {
        spec_sort: eq_sym,
        bindings: SmallVec::from_slice(&[(t_sym, list_list_int)]),
        carrier: None,
    };
    let subst = Substitution::new();
    let scope = empty_scope(&subst);
    match resolve(&mut kb, &goal, &scope) {
        ResolutionResult::Resolved(ResolvedRequiresNode::Conditional {
            impl_sort, sub_resolutions, ..
        }) => {
            let impl_qn = kb.qualified_name_of(impl_sort).to_string();
            assert_eq!(impl_qn, "test.wi224.two_level.EqList");
            assert_eq!(sub_resolutions.len(), 1);
            // The middle layer must also be a Conditional EqList…
            match &sub_resolutions[0] {
                ResolvedRequiresNode::Conditional { impl_sort: mid, sub_resolutions: inner, .. } => {
                    let mid_qn = kb.qualified_name_of(*mid).to_string();
                    assert_eq!(mid_qn, "test.wi224.two_level.EqList",
                        "middle layer must be EqList; got {mid_qn}");
                    assert_eq!(inner.len(), 1);
                    // …whose inner sub_resolution bottoms out at an Int64 leaf.
                    match &inner[0] {
                        ResolvedRequiresNode::Leaf { impl_sort: leaf, .. } => {
                            let leaf_qn = kb.qualified_name_of(*leaf).to_string();
                            assert!(leaf_qn.contains("Int64"),
                                "expected the leaf to mention Int64; got {leaf_qn}");
                        }
                        other => panic!("inner-most must be Leaf; got {other:?}"),
                    }
                }
                other => panic!("middle resolution must be Conditional EqList; got {other:?}"),
            }
        }
        other => panic!("expected Conditional outer; got {other:?}"),
    }
}

// ── (4) Ambiguous diagnostic ─────────────────────────────────────

#[test]
fn ambiguous_when_two_impls_collide_without_specificity_order() {
    // Two impls each provide AmbSpec[T = AmbCarrier]; both heads are
    // equally-specific (same concrete binding). Resolution must
    // surface as Ambiguous with both carrier names in the diagnostic.
    let src = r#"
        namespace test.wi224.amb
          export AmbSpec, AmbCarrier, AmbA, AmbB
          sort AmbSpec
            sort T = ?
            operation amb_op(x: T) -> T
          end
          sort AmbCarrier
            entity amb_e
          end
          sort AmbA
            fact AmbSpec[T = AmbCarrier]
            operation amb_op(x: AmbCarrier) -> AmbCarrier = x
          end
          sort AmbB
            fact AmbSpec[T = AmbCarrier]
            operation amb_op(x: AmbCarrier) -> AmbCarrier = x
          end
        end
    "#;
    let mut kb = load_with(src);
    let goal = goal_for(&mut kb, "test.wi224.amb.AmbSpec", "T", "test.wi224.amb.AmbCarrier");
    let subst = Substitution::new();
    let scope = empty_scope(&subst);
    match resolve(&mut kb, &goal, &scope) {
        ResolutionResult::Ambiguous { candidate_impl_qns, .. } => {
            assert!(candidate_impl_qns.iter().any(|q| q.ends_with("AmbA")),
                "AmbA should appear in candidates: {candidate_impl_qns:?}");
            assert!(candidate_impl_qns.iter().any(|q| q.ends_with("AmbB")),
                "AmbB should appear in candidates: {candidate_impl_qns:?}");
            assert_eq!(candidate_impl_qns.len(), 2,
                "exactly two candidates expected; got {candidate_impl_qns:?}");
        }
        other => panic!("expected Ambiguous; got {other:?}"),
    }
}

// ── (5) Cyclic diagnostic ────────────────────────────────────────

#[test]
fn cyclic_when_conditional_subgoal_recurses() {
    // CyclicA provides CycSpec[T=CarA] conditional on CycSpec[T=CarB].
    // CyclicB provides CycSpec[T=CarB] conditional on CycSpec[T=CarA].
    // Resolution forms a cycle CarA → CarB → CarA → ... — the cycle
    // detector must reject with `Cyclic`.
    let src = r#"
        namespace test.wi224.cyc
          export CycSpec, CarA, CarB, CyclicA, CyclicB
          sort CycSpec
            sort T = ?
            operation cyc_op(x: T) -> T
          end
          sort CarA entity car_a end
          sort CarB entity car_b end
          sort CyclicA
            requires CycSpec[T = CarB]
            fact CycSpec[T = CarA]
          end
          sort CyclicB
            requires CycSpec[T = CarA]
            fact CycSpec[T = CarB]
          end
        end
    "#;
    let mut kb = load_with(src);
    let goal = goal_for(&mut kb, "test.wi224.cyc.CycSpec", "T", "test.wi224.cyc.CarA");
    let subst = Substitution::new();
    let scope = empty_scope(&subst);
    match resolve(&mut kb, &goal, &scope) {
        ResolutionResult::Cyclic { path } => {
            assert!(path.len() >= 2,
                "cycle path should record at least the entering and looping goals: {path:?}");
            assert!(path.iter().any(|s| s.contains("CycSpec") && s.contains("CarA")),
                "cycle path should mention CarA goal: {path:?}");
            assert!(path.iter().any(|s| s.contains("CycSpec") && s.contains("CarB")),
                "cycle path should mention CarB goal: {path:?}");
        }
        other => panic!("expected Cyclic; got {other:?}"),
    }
}

// ── (6) NoMatch diagnostic ───────────────────────────────────────

#[test]
fn no_match_when_no_candidate_for_bindings() {
    // OnlyForInt has only `fact NoMatchSpec[T = Int64]`. A goal at
    // T = Bool must produce NoMatch with a hint that mentions the spec.
    let src = r#"
        namespace test.wi224.nm
          import anthill.prelude.{Int64, Bool}
          export NoMatchSpec, OnlyForInt
          sort NoMatchSpec
            sort T = ?
            operation nm_op(x: T) -> T
          end
          sort OnlyForInt
            fact NoMatchSpec[T = Int64]
            operation nm_op(x: Int64) -> Int64 = x
          end
        end
    "#;
    let mut kb = load_with(src);
    let goal = goal_for(&mut kb,
        "test.wi224.nm.NoMatchSpec", "T", "anthill.prelude.Bool");
    let subst = Substitution::new();
    let scope = empty_scope(&subst);
    match resolve(&mut kb, &goal, &scope) {
        ResolutionResult::NoMatch { goal_text, hint } => {
            assert!(goal_text.contains("NoMatchSpec"),
                "goal_text should reference the spec; got {goal_text}");
            assert!(hint.contains("NoMatchSpec"),
                "hint should mention the spec name to point users at the missing fact: {hint}");
        }
        other => panic!("expected NoMatch; got {other:?}"),
    }
}

// ── (7) Coherence at diamond join points (Example 3) ──────────────

#[test]
fn diamond_coherence_picks_same_a_impl_for_both_branches() {
    // Diamond shape: B and C each `requires DiamondA[T]`; CarrierB
    // and CarrierC are their respective impls, and both transitively
    // need DiamondA. The acceptance test: resolving DiamondA[T=Int64]
    // from inside B's scope and from inside C's scope must pick the
    // SAME A impl (CarrierA). Coherence at the join point — both
    // ends of the diamond agree on which A is used.
    let src = r#"
        namespace test.wi224.diamond
          export DiamondA, DiamondB, DiamondC, CarrierA, CarrierB, CarrierC
          import anthill.prelude.Int64
          sort DiamondA
            sort T = ?
            operation a_op(x: T) -> T
          end
          sort DiamondB
            sort T = ?
            operation b_op(x: T) -> T
          end
          sort DiamondC
            sort T = ?
            operation c_op(x: T) -> T
          end
          sort CarrierA
            sort T = ?
            fact DiamondA[T = T]
            operation a_op(x: T) -> T = x
          end
          sort CarrierB
            sort T = ?
            requires DiamondA[T = T]
            fact DiamondB[T = T]
            operation b_op(x: T) -> T = x
          end
          sort CarrierC
            sort T = ?
            requires DiamondA[T = T]
            fact DiamondC[T = T]
            operation c_op(x: T) -> T = x
          end
        end
    "#;
    let mut kb = load_with(src);

    let goal_b = goal_for(&mut kb,
        "test.wi224.diamond.DiamondB", "T", "anthill.prelude.Int64");
    let goal_c = goal_for(&mut kb,
        "test.wi224.diamond.DiamondC", "T", "anthill.prelude.Int64");
    let subst = Substitution::new();
    let scope = empty_scope(&subst);

    // Each branch is a Conditional whose subgoal resolves DiamondA.
    let b_tree = match resolve(&mut kb, &goal_b, &scope) {
        ResolutionResult::Resolved(t) => t,
        other => panic!("B resolution failed: {other:?}"),
    };
    let c_tree = match resolve(&mut kb, &goal_c, &scope) {
        ResolutionResult::Resolved(t) => t,
        other => panic!("C resolution failed: {other:?}"),
    };

    // Walk each tree to the DiamondA subgoal and confirm both pick
    // the same A impl.
    fn pick_a(kb: &KnowledgeBase, t: &ResolvedRequiresNode, target: &str) -> Option<String> {
        match t {
            ResolvedRequiresNode::Leaf { impl_sort, spec_sort, .. } => {
                if kb.qualified_name_of(*spec_sort).ends_with(target) {
                    Some(kb.qualified_name_of(*impl_sort).to_string())
                } else {
                    None
                }
            }
            ResolvedRequiresNode::Conditional { impl_sort, spec_sort, sub_resolutions, .. } => {
                if kb.qualified_name_of(*spec_sort).ends_with(target) {
                    return Some(kb.qualified_name_of(*impl_sort).to_string());
                }
                for st in sub_resolutions {
                    if let Some(s) = pick_a(kb, st, target) { return Some(s); }
                }
                None
            }
            ResolvedRequiresNode::FromScope { .. } => None,
        }
    }
    let a_under_b = pick_a(&kb, &b_tree, ".DiamondA")
        .expect("expected B-branch resolution to descend into DiamondA");
    let a_under_c = pick_a(&kb, &c_tree, ".DiamondA")
        .expect("expected C-branch resolution to descend into DiamondA");
    assert_eq!(a_under_b, a_under_c,
        "coherence at the diamond join: both branches must agree on the \
         DiamondA impl. Got B→{a_under_b}, C→{a_under_c}");
    assert!(a_under_b.ends_with("CarrierA"),
        "the shared A impl should be CarrierA; got {a_under_b}");
}

// ── available_requires (FromScope) — exercises step 1 of the algorithm

#[test]
fn available_requires_match_short_circuits_resolution() {
    // When the enclosing sort declares `requires Eq[T=Int64]`, a goal at
    // Eq[T=Int64] must resolve as `FromScope` at index 0 — the caller
    // already holds the right requirement value; no impl-construction
    // needed.
    let src = r#"
        namespace test.wi224.scope
          import anthill.prelude.{Eq, Int64}
          export Wi224Holder
          sort Wi224Holder
            requires Eq[T = Int64]
          end
        end
    "#;
    let mut kb = load_with(src);
    let holder = kb.try_resolve_symbol("test.wi224.scope.Wi224Holder")
        .expect("Wi224Holder registered");
    let chain = requires_chain_flat(&kb, holder);
    let goal = goal_for(&mut kb, "anthill.prelude.Eq", "T", "anthill.prelude.Int64");
    let scope = ResolutionScope { available_requires: &chain };
    match resolve(&mut kb, &goal, &scope) {
        ResolutionResult::Resolved(ResolvedRequiresNode::FromScope { scope_index, .. }) => {
            assert_eq!(scope_index, 0,
                "Eq[T=Int64] should match the first available_requires slot");
        }
        other => panic!("expected FromScope; got {other:?}"),
    }
}

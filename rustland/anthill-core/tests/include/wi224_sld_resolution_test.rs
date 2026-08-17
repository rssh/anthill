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

use anthill_core::kb::load::{self, NullResolver};
use anthill_core::kb::subst::Substitution;
use anthill_core::kb::term::{Term, TermId};
use anthill_core::kb::typing::{
    requires_chain_flat, resolve, sort_goal_from_subst, ResolutionResult, ResolutionScope,
    ResolvedRequiresNode, SortGoal,
};
use anthill_core::kb::KnowledgeBase;
use anthill_core::parse;
use smallvec::SmallVec;

/// Load stdlib + rustland bindings + an extra source string.
fn load_with(extra: &str) -> KnowledgeBase {
    load_expecting(extra, &[])
}

/// [`load_with`] for the two fixtures whose provider is DELIBERATELY incoherent
/// — an `EqList` that declares the `Eq` marker and nothing else, so that
/// resolving `Eq[List[…]]` has an unsatisfiable `PartialEq` leg to record as
/// `Unavailable`. The loader rightly complains; `expected` pins that complaint.
///
/// WI-966: this file used to discard the loader's `Err`, which meant the two
/// conditional-resolution tests could not tell "the fixture is incoherent on
/// purpose" from "the fixture stopped loading". Both now say which they are.
fn load_expecting(extra: &str, expected: &[&str]) -> KnowledgeBase {
    let files = crate::common::collect_stdlib_and_rust_bindings();
    let mut parsed: Vec<_> = files
        .iter()
        .map(|p| {
            let src =
                std::fs::read_to_string(p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()));
            parse::parse(&src).unwrap_or_else(|e| panic!("parse {}: {e:?}", p.display()))
        })
        .collect();
    parsed.push(parse::parse(extra).expect("parse extra"));
    let refs: Vec<_> = parsed.iter().collect();
    let mut kb = KnowledgeBase::new();
    let result = load::load_all(&mut kb, &refs, &NullResolver);
    if expected.is_empty() {
        crate::common::expect_loaded(result);
    } else {
        crate::common::expect_load_errors(result, expected);
    }
    kb
}

/// Build a goal `<spec>[<param> = <carrier>]` directly. Uses
/// `sort_goal_from_subst` to mirror the typer's call-site goal
/// construction (going through SortAlias → Var → subst).
fn goal_for(
    kb: &mut KnowledgeBase,
    spec_qn: &str,
    param_short: &str,
    carrier_qn: &str,
) -> SortGoal {
    let spec_sym = kb
        .try_resolve_symbol(spec_qn)
        .unwrap_or_else(|| panic!("{spec_qn} not registered"));
    let param_qn = format!("{spec_qn}.{param_short}");
    let param_sym = kb
        .try_resolve_symbol(&param_qn)
        .unwrap_or_else(|| panic!("{param_qn} not registered"));
    let param_var = crate::common::sort_alias_backing_var(kb, param_sym)
        .unwrap_or_else(|| panic!("{}'s SortAlias not found for {spec_qn}", param_short));
    let carrier_sym = kb
        .try_resolve_symbol(carrier_qn)
        .unwrap_or_else(|| panic!("{carrier_qn} not registered"));
    let carrier_term = kb.make_sort_ref(carrier_sym);
    let mut subst = Substitution::new();
    subst.bind_term(kb, param_var, carrier_term);
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
    let outer_sym = kb
        .try_resolve_symbol(outer_qn)
        .unwrap_or_else(|| panic!("{outer_qn} not registered"));
    let inner_sym = kb
        .try_resolve_symbol(inner_qn)
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
    ResolutionScope {
        available_requires: &[],
        sigma: None,
        selected: &[],
    }
}

// ── (1) Leaf instance resolution ─────────────────────────────────

#[test]
fn leaf_resolution_picks_concrete_impl() {
    // Eq[T = Int64] resolves to the Int64 impl — stdlib registers
    // `fact Eq[T = Int64]` in the rustland bindings.
    //
    // WI-857: a `Leaf` no longer, and the reason is the point of that ticket. A
    // dictionary bundles the SPEC's own `requires` chain as its prefix, and
    // `Eq requires PartialEq[T]` — so `Eq[T = Int64]` is a Conditional whose one
    // sub-resolution is `PartialEq[T = Int64]`. The provider half is empty here:
    // `Int64` is a carrier-keyed provider and declares no `requires`, which is
    // exactly the shape that used to build an arity-0 dictionary and die at eval.
    let mut kb = load_with("");
    let goal = goal_for(&mut kb, "anthill.prelude.Eq", "T", "anthill.prelude.Int64");
    let subst = Substitution::new();
    let scope = empty_scope(&subst);
    let result = resolve(&mut kb, &goal, &scope);
    let is_int64 = |kb: &KnowledgeBase, s| {
        let qn = kb.qualified_name_of(s).to_string();
        qn.ends_with(".Int64") || qn == "anthill.prelude.Int64" || qn.ends_with("IntEq")
    };
    match result {
        ResolutionResult::Resolved(ResolvedRequiresNode::Conditional {
            impl_sort,
            sub_resolutions,
            ..
        }) => {
            assert!(
                is_int64(&kb, impl_sort),
                "expected the Int64 impl; got {}",
                kb.qualified_name_of(impl_sort)
            );
            assert_eq!(
                sub_resolutions.len(),
                1,
                "the spec half is `Eq`'s own chain — one entry, `PartialEq[T]`; got {:?}",
                sub_resolutions
            );
            match &sub_resolutions[0] {
                ResolvedRequiresNode::Leaf {
                    impl_sort: inner,
                    spec_sort,
                    ..
                } => {
                    assert_eq!(
                        kb.qualified_name_of(*spec_sort),
                        "anthill.prelude.PartialEq",
                        "slot 0 is the spec half's `PartialEq` leg"
                    );
                    assert!(
                        is_int64(&kb, *inner),
                        "`PartialEq[Int64]` is provided by Int64 too; got {}",
                        kb.qualified_name_of(*inner)
                    );
                }
                other => {
                    panic!("`PartialEq[Int64]` has an empty chain, so it is a Leaf; got {other:?}")
                }
            }
        }
        other => panic!("expected Resolved::Conditional for Eq[T=Int64]; got {other:?}"),
    }
}

// ── (2) One-level conditional ────────────────────────────────────

#[test]
fn one_level_conditional_resolves_via_subgoal() {
    // EqList provides Eq[List[T=A]] conditional on Eq[T=A]. Resolving
    // Eq[T = List[T = Int64]] must produce a Conditional node whose
    // PROVIDER-half sub_resolution is Eq[T = Int64]'s impl.
    //
    // WI-857 layout: slot 0 is the SPEC half (`Eq requires PartialEq[T]`, i.e.
    // `PartialEq[List[Int64]]`) and slot 1 is the PROVIDER half (`EqList requires
    // Eq[T = A]`, i.e. `Eq[Int64]`). Nothing in this fixture provides `PartialEq`
    // for a `List` — `EqList` declares only the `Eq` marker — so slot 0 is
    // `Unavailable`: recorded, positionally exact, and loud only if a body ever
    // reads it. That is the deliberate looseness the variant documents; the
    // properly-bundled twin (a provider declaring both) is pinned in
    // `wi857_dictionary_layout_test`.
    let src = r#"
        namespace test.wi224.one_level
          import anthill.prelude.{Eq, List, Int64}
          sort EqList
            sort A = ?
            requires Eq[T = A]
            fact Eq[T = List[T = A]]
          end
        end
    "#;
    // WI-1110: this fixture now loads CLEAN, and the change is the ticket's point.
    // `EqList` still declares only the `Eq` marker — but `Eq provides PartialEq[T = T]`
    // is a CONVERSION, so `derive_forwarded_provisions` materializes
    // `EqList provides PartialEq[T = List[T = A]]` from the row `EqList` wrote, and the
    // obligation the pinned diagnostic reported is discharged by the derivation instead
    // of by the author writing the lower floor a second time.
    let mut kb = load_with(src);

    // Build goal Eq[T = List[T = Int64]].
    let list_int = parametric_carrier(
        &mut kb,
        "anthill.prelude.List",
        "T",
        "anthill.prelude.Int64",
    );
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
        ResolutionResult::Resolved(ResolvedRequiresNode::Conditional {
            impl_sort,
            sub_resolutions,
            ..
        }) => {
            let impl_qn = kb.qualified_name_of(impl_sort).to_string();
            assert_eq!(
                impl_qn, "test.wi224.one_level.EqList",
                "expected EqList as the conditional impl; got {impl_qn}"
            );
            assert_eq!(
                sub_resolutions.len(),
                2,
                "WI-857: `Eq`'s own chain (1) then `EqList`'s (1); got {sub_resolutions:?}"
            );
            // WI-1110 — SLOT 0 IS NOW FILLED, and that is the ticket's benefit rather
            // than a loosening. It used to be `Unavailable`: `Eq requires PartialEq[T]`
            // put the slot there and nothing in this fixture provided `PartialEq` for a
            // `List`, so the leg was recorded and left empty. `Eq provides
            // PartialEq[T = T]` is a CONVERSION, so `EqList`'s own `PartialEq` row is
            // derived from the `Eq` row it wrote, and the slot resolves — through
            // `EqList` itself, conditional on `Eq[A]` exactly as the provider half is.
            // The `Unavailable` machinery is unaffected and still pinned by
            // `wi869_per_provision_conditions_test`'s sibling-provision slots.
            match &sub_resolutions[0] {
                ResolvedRequiresNode::Conditional {
                    impl_sort: inner,
                    spec_sort,
                    ..
                } => {
                    assert_eq!(
                        kb.qualified_name_of(*spec_sort),
                        "anthill.prelude.PartialEq",
                        "the spec half's leg is `PartialEq`",
                    );
                    assert_eq!(
                        kb.qualified_name_of(*inner),
                        "test.wi224.one_level.EqList",
                        "and it is answered by the DERIVED `EqList provides PartialEq` \
                         row, not by some other carrier",
                    );
                }
                other => panic!(
                    "the spec-half slot must resolve through the derived \
                     `EqList provides PartialEq` row; got {other:?}"
                ),
            }
            match &sub_resolutions[1] {
                ResolvedRequiresNode::Conditional {
                    impl_sort: inner, ..
                } => {
                    let inner_qn = kb.qualified_name_of(*inner).to_string();
                    assert!(inner_qn.contains("Int64"),
                        "expected the provider half's `Eq[T=A]` to resolve at Int64; got {inner_qn}");
                }
                other => panic!(
                    "the provider half is `Eq[Int64]`, itself Conditional on \
                     `PartialEq[Int64]`; got {other:?}"
                ),
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
          sort EqList
            sort A = ?
            requires Eq[T = A]
            fact Eq[T = List[T = A]]
          end
        end
    "#;
    // WI-1110: this fixture now loads CLEAN, and the change is the ticket's point.
    // `EqList` still declares only the `Eq` marker — but `Eq provides PartialEq[T = T]`
    // is a CONVERSION, so `derive_forwarded_provisions` materializes
    // `EqList provides PartialEq[T = List[T = A]]` from the row `EqList` wrote, and the
    // obligation the pinned diagnostic reported is discharged by the derivation instead
    // of by the author writing the lower floor a second time.
    let mut kb = load_with(src);

    // Build the outer goal: Eq[T = List[T = List[T = Int64]]].
    let list_int = parametric_carrier(
        &mut kb,
        "anthill.prelude.List",
        "T",
        "anthill.prelude.Int64",
    );
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
            impl_sort,
            sub_resolutions,
            ..
        }) => {
            let impl_qn = kb.qualified_name_of(impl_sort).to_string();
            assert_eq!(impl_qn, "test.wi224.two_level.EqList");
            // WI-857: slot 0 = the spec half (`PartialEq[List[List[Int64]]]`,
            // unprovided here), slot 1 = the provider half (`Eq[List[Int64]]`), which
            // is the middle EqList layer.
            assert_eq!(sub_resolutions.len(), 2, "got {sub_resolutions:?}");
            match &sub_resolutions[1] {
                ResolvedRequiresNode::Conditional {
                    impl_sort: mid,
                    sub_resolutions: inner,
                    ..
                } => {
                    let mid_qn = kb.qualified_name_of(*mid).to_string();
                    assert_eq!(
                        mid_qn, "test.wi224.two_level.EqList",
                        "middle layer must be EqList; got {mid_qn}"
                    );
                    assert_eq!(inner.len(), 2, "same two halves one level down");
                    // …whose provider half bottoms out at Int64.
                    match &inner[1] {
                        ResolvedRequiresNode::Conditional {
                            impl_sort: leaf, ..
                        } => {
                            let leaf_qn = kb.qualified_name_of(*leaf).to_string();
                            assert!(
                                leaf_qn.contains("Int64"),
                                "expected the innermost impl to be Int64; got {leaf_qn}"
                            );
                        }
                        other => panic!(
                            "inner-most is `Eq[Int64]` — Conditional on its own \
                             `PartialEq[Int64]` spec half; got {other:?}"
                        ),
                    }
                }
                other => panic!("the provider half must be Conditional EqList; got {other:?}"),
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
    let goal = goal_for(
        &mut kb,
        "test.wi224.amb.AmbSpec",
        "T",
        "test.wi224.amb.AmbCarrier",
    );
    let subst = Substitution::new();
    let scope = empty_scope(&subst);
    match resolve(&mut kb, &goal, &scope) {
        ResolutionResult::Ambiguous { tie, .. } => {
            // WI-843: candidates ride as SYMBOLS, rendered only where a message is
            // emitted — the resolver no longer builds strings for consumers that
            // discard them.
            let qns: Vec<&str> = tie
                .candidates
                .iter()
                .map(|s| kb.qualified_name_of(*s))
                .collect();
            assert!(
                qns.iter().any(|q| q.ends_with("AmbA")),
                "AmbA should appear in candidates: {qns:?}"
            );
            assert!(
                qns.iter().any(|q| q.ends_with("AmbB")),
                "AmbB should appear in candidates: {qns:?}"
            );
            assert_eq!(qns.len(), 2, "exactly two candidates expected; got {qns:?}");
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
    let goal = goal_for(
        &mut kb,
        "test.wi224.cyc.CycSpec",
        "T",
        "test.wi224.cyc.CarA",
    );
    let subst = Substitution::new();
    let scope = empty_scope(&subst);
    match resolve(&mut kb, &goal, &scope) {
        ResolutionResult::Cyclic { path, .. } => {
            assert!(
                path.len() >= 2,
                "cycle path should record at least the entering and looping goals: {path:?}"
            );
            assert!(
                path.iter()
                    .any(|s| s.contains("CycSpec") && s.contains("CarA")),
                "cycle path should mention CarA goal: {path:?}"
            );
            assert!(
                path.iter()
                    .any(|s| s.contains("CycSpec") && s.contains("CarB")),
                "cycle path should mention CarB goal: {path:?}"
            );
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
    let goal = goal_for(
        &mut kb,
        "test.wi224.nm.NoMatchSpec",
        "T",
        "anthill.prelude.Bool",
    );
    let subst = Substitution::new();
    let scope = empty_scope(&subst);
    match resolve(&mut kb, &goal, &scope) {
        ResolutionResult::NoMatch {
            goal_text, hint, ..
        } => {
            assert!(
                goal_text.contains("NoMatchSpec"),
                "goal_text should reference the spec; got {goal_text}"
            );
            assert!(
                hint.contains("NoMatchSpec"),
                "hint should mention the spec name to point users at the missing fact: {hint}"
            );
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

    let goal_b = goal_for(
        &mut kb,
        "test.wi224.diamond.DiamondB",
        "T",
        "anthill.prelude.Int64",
    );
    let goal_c = goal_for(
        &mut kb,
        "test.wi224.diamond.DiamondC",
        "T",
        "anthill.prelude.Int64",
    );
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
            ResolvedRequiresNode::Leaf {
                impl_sort,
                spec_sort,
                ..
            } => {
                if kb.qualified_name_of(*spec_sort).ends_with(target) {
                    Some(kb.qualified_name_of(*impl_sort).to_string())
                } else {
                    None
                }
            }
            ResolvedRequiresNode::Conditional {
                impl_sort,
                spec_sort,
                sub_resolutions,
                ..
            } => {
                if kb.qualified_name_of(*spec_sort).ends_with(target) {
                    return Some(kb.qualified_name_of(*impl_sort).to_string());
                }
                for st in sub_resolutions {
                    if let Some(s) = pick_a(kb, st, target) {
                        return Some(s);
                    }
                }
                None
            }
            // Neither pins an impl to compare (WI-857).
            ResolvedRequiresNode::FromScope { .. } | ResolvedRequiresNode::Unavailable { .. } => {
                None
            }
        }
    }
    let a_under_b = pick_a(&kb, &b_tree, ".DiamondA")
        .expect("expected B-branch resolution to descend into DiamondA");
    let a_under_c = pick_a(&kb, &c_tree, ".DiamondA")
        .expect("expected C-branch resolution to descend into DiamondA");
    assert_eq!(
        a_under_b, a_under_c,
        "coherence at the diamond join: both branches must agree on the \
         DiamondA impl. Got B→{a_under_b}, C→{a_under_c}"
    );
    assert!(
        a_under_b.ends_with("CarrierA"),
        "the shared A impl should be CarrierA; got {a_under_b}"
    );
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
          sort Wi224Holder
            requires Eq[T = Int64]
          end
        end
    "#;
    let mut kb = load_with(src);
    let holder = kb
        .try_resolve_symbol("test.wi224.scope.Wi224Holder")
        .expect("Wi224Holder registered");
    let chain = requires_chain_flat(&kb, holder);
    let goal = goal_for(&mut kb, "anthill.prelude.Eq", "T", "anthill.prelude.Int64");
    let scope = ResolutionScope {
        available_requires: &chain,
        sigma: None,
        selected: &[],
    };
    match resolve(&mut kb, &goal, &scope) {
        ResolutionResult::Resolved(ResolvedRequiresNode::FromScope { scope_index, .. }) => {
            assert_eq!(
                scope_index, 0,
                "Eq[T=Int64] should match the first available_requires slot"
            );
        }
        other => panic!("expected FromScope; got {other:?}"),
    }
}

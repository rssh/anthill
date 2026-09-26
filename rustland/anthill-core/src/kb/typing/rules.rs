//! Rule type checking: rule bodies, typed-head domain goals, and higher-order pattern
//! fragments.

use super::*;

// ── HO pattern fragment checking ───────────────────────────────

/// Validate that rules conform to the hereditary Harrop pattern fragment.
/// This ensures higher-order unification remains decidable.
pub(super) fn check_pattern_fragment(
    kb: &KnowledgeBase,
    sort_name: Symbol,
    errors: &mut Vec<TypeError>,
) {
    let ho_apply_sym = match kb.try_resolve_symbol(dt::qualified(dt::HO_APPLY)) {
        Some(s) => s,
        None => return,
    };

    for rid in kb.by_domain(sort_name) {
        if kb.is_fact(rid) {
            continue;
        } // skip facts — only check rules

        // Head stays a hash-consed term (it is searched in the discrim tree),
        // so the head checks remain term-based.
        let head = kb.rule_head(rid);

        // WI-20260902-CZJ2N: a NULLARY head is stored bare. Without the `Ref`/`Ident`
        // arm every 0-ary-headed rule (`rule flag :- …`, and now its parenthesised
        // twin, which is the same term) was skipped entirely — head rule 1 AND the
        // per-goal `check_ho_apply_pattern_occ` body walk — so a load-time refusal
        // silently stopped running on a whole class of rules.
        let head_sym = match kb.get_term(head) {
            Term::Fn { functor, .. } => *functor,
            Term::Ref(s) | Term::Ident(s) => *s,
            _ => continue,
        };
        // WI-458: the rule's OWN head span, keyed by RuleId. Deliberately no
        // `term_span(head)` fallback: the loader records a `term_spans` entry only
        // for op-body subterms and FACT heads, never for a rule head — so a hit
        // there could only be another construct that happened to intern the same
        // head TermId, i.e. exactly the cross-file span this WI removes. `None`
        // (no location) beats a confidently wrong file:line.
        let span = kb.rule_head_span(rid).map(|s| s.span);

        // Rule 1: head must not contain ho_apply (no predicate variables in head)
        if term_contains_functor(kb, head, ho_apply_sym) {
            errors.push(TypeError::Other {
                site: TypeError::here(),
                span,
                context: TypeErrorContext::Rule {
                    name: head_sym,
                    field: RuleField::Head,
                },
                expected: "no predicate variables in rule head".to_string(),
                actual: "ho_apply in head position".to_string(),
            });
        }

        // Check body goals for pattern fragment violations — WI-246: walk the
        // OCCURRENCE body (`rule_body_nodes`), not the term body. `ho_apply` is
        // not a recognized reflect materialize key, so it stays faithful
        // (`Expr::Apply { functor: ho_apply, … }`) in the occurrence form.
        for goal in kb.rule_body_nodes(rid) {
            check_ho_apply_pattern_occ(kb, goal, ho_apply_sym, head_sym, span, errors);
        }
    }
}

/// Check an occurrence (rule-body goal) for ho_apply pattern fragment
/// violations — WI-246: the occurrence-walking twin of the former
/// `check_ho_apply_pattern` term-walker. `ho_apply` materializes faithfully to
/// `Expr::Apply { functor: ho_apply, … }` (not a recognized reflect key), so
/// the structural checks carry over: the functor-bearing forms
/// (`Apply`/`Constructor`/`Instantiation`) mirror the term-walker's `Term::Fn`,
/// and `Expr::Var(DeBruijn)` mirrors `Term::Var(DeBruijn)` in the stored body.
pub(super) fn check_ho_apply_pattern_occ(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    ho_apply_sym: Symbol,
    rule_sym: Symbol,
    span: Option<Span>,
    errors: &mut Vec<TypeError>,
) {
    let Some(expr) = occ.as_expr() else {
        // WI-323: a Pattern-kind occurrence (Lambda.param / LambdaWithin.param /
        // Let.pattern / MatchBranch.pattern lifted to Pattern-kind by WI-319)
        // can carry an Expr child in a nested type-annotation slot. Descend so
        // an `ho_apply` smuggled inside a Pattern.type_ann Expr child still gets
        // the rules-1/2/3/3b pattern-fragment check instead of evading it via
        // the `as_expr()` early-return. Mirror of `collect_occurrence_global_vars`'s
        // Pattern arm — recurse via `for_each_pattern_child`.
        if occ.as_pattern().is_some() {
            for_each_pattern_child(occ, |c| {
                check_ho_apply_pattern_occ(kb, c, ho_apply_sym, rule_sym, span, errors);
            });
        }
        return;
    };

    // The ho_apply-specific fragment rules apply to the functor-bearing forms
    // (Apply/Constructor/Instantiation) — the occurrence analogue of `Term::Fn`.
    // `ho_apply` materializes to `Expr::Apply`, but match all three for parity
    // with the term-walker's functor check.
    let ho_pos_args = expr_call_parts(expr)
        .filter(|(f, _, _)| *f == ho_apply_sym)
        .map(|(_, pos_args, _)| pos_args);

    if let Some(pos_args) = ho_pos_args {
        if !pos_args.is_empty() {
            // This is an ho_apply — check pattern fragment rules.

            // Rule 2: first arg (predicate) must be a variable. If it's instead a
            // nested ho_apply (predicate applied to predicate), flag it.
            let pred = &pos_args[0];
            if !matches!(pred.as_expr(), Some(Expr::Var(_))) {
                if let Some(Expr::Apply {
                    functor: inner_f, ..
                }) = pred.as_expr()
                {
                    if *inner_f == ho_apply_sym {
                        errors.push(TypeError::Other {
                            site: TypeError::here(),
                            span,
                            context: TypeErrorContext::Rule {
                                name: rule_sym,
                                field: RuleField::Body,
                            },
                            expected: "variable as predicate in ho_apply".to_string(),
                            actual: "nested ho_apply (predicate applied to predicate)".to_string(),
                        });
                    }
                }
            }

            // Rule 3: remaining args must be distinct (no duplicate variables).
            let mut seen_vars: Vec<u32> = Vec::new();
            for arg in &pos_args[1..] {
                if let Some(Expr::Var(Var::DeBruijn(idx))) = arg.as_expr() {
                    if seen_vars.contains(idx) {
                        errors.push(TypeError::Other {
                            site: TypeError::here(),
                            span,
                            context: TypeErrorContext::Rule {
                                name: rule_sym,
                                field: RuleField::Body,
                            },
                            expected: "distinct variables in ho_apply args".to_string(),
                            actual: format!("duplicate variable ?{} in predicate application", idx),
                        });
                    }
                    seen_vars.push(*idx);
                }

                // Rule 3b: args must not contain ho_apply (no predicate variable as argument).
                if occurrence_contains_functor(arg, ho_apply_sym) {
                    errors.push(TypeError::Other {
                        site: TypeError::here(),
                        span,
                        context: TypeErrorContext::Rule {
                            name: rule_sym,
                            field: RuleField::Body,
                        },
                        expected: "first-order args in ho_apply".to_string(),
                        actual: "predicate variable as argument to predicate".to_string(),
                    });
                }
            }
        }
    }

    // Recurse into ALL sub-occurrences. The term-walker recursed every
    // `Term::Fn` child, and reflect-encoded if/match/let/lambda/list/… are
    // `Term::Fn` in term-land, so an `ho_apply` nested in a control-flow or
    // container form must still be checked.
    for_each_child(expr, |c| {
        check_ho_apply_pattern_occ(kb, c, ho_apply_sym, rule_sym, span, errors);
    });
}

/// Check if an occurrence (or any sub-occurrence) contains the given functor.
/// Occurrence-walking twin of [`term_contains_functor`] for the rule-body
/// pattern-fragment check; `Apply`/`Constructor`/`Instantiation` carry the
/// functor (mirroring `Term::Fn`).
pub(super) fn occurrence_contains_functor(occ: &Rc<NodeOccurrence>, target: Symbol) -> bool {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(occ)];
    while let Some(o) = stack.pop() {
        if let Some(expr) = o.as_expr() {
            if expr_call_parts(expr).is_some_and(|(f, _, _)| f == target) {
                return true;
            }
            for_each_child(expr, |c| stack.push(Rc::clone(c)));
        } else if o.as_pattern().is_some() {
            // WI-323: descend into Pattern children so a target functor nested
            // in a Pattern.type_ann Expr leaf is found. Without this the rules-1/3b
            // head-vs-body co-occurrence test (`check_pattern_fragment`) would
            // miss a functor smuggled inside a Pattern-kind occurrence. Mirror of
            // `collect_occurrence_global_vars`'s Pattern arm.
            //
            // `o`, NOT `occ`: `occ` is this function's ROOT parameter, still in
            // scope, so passing it compiles and then walks the wrong node. That
            // was a live defect — from an Expr root (the production shape: this
            // runs over a rule BODY) `for_each_pattern_child` took its
            // non-Pattern early return and pushed NOTHING, silently disabling the
            // descent this arm exists for; from a Pattern root with a nested
            // Pattern child it re-pushed the root's children forever. Pinned by
            // `witness_a_expr_root_finds_functor_in_pattern_annotation` and
            // `witness_b_nested_pattern_terminates` — the pre-existing test above
            // could not catch it, because it passes the pattern ITSELF as root,
            // where `o` and `occ` are the same node.
            for_each_pattern_child(&o, |c| stack.push(Rc::clone(c)));
        }
    }
    false
}

/// Check if a term (or any subterm) contains the given functor. Still used for
/// the rule HEAD (a hash-consed term); the body uses [`occurrence_contains_functor`].
fn term_contains_functor(kb: &KnowledgeBase, term: TermId, target_functor: Symbol) -> bool {
    term_any_subterm(
        kb,
        term,
        &|_, t| matches!(t, Term::Fn { functor, .. } if *functor == target_functor),
    )
}

// ── Rule type checking ─────────────────────────────────────────

/// WI-603: stamp each rule-body variable occurrence with the type
/// `collect_rule_var_types` derived for its var — sourced from op-param /
/// entity-field signatures and unified across the rule's occurrences of that var.
/// The occurrence write-back that completes the untyped→typed transform for a
/// plain `f(?x, ?y)` atom: the dot-only pass never visited it, so its arg vars
/// carried no `inferred_type`. A `Var` leaf whose vid has a collected type is
/// stamped (the same `u32` key space `collect_occurrence_type_constraints` reads);
/// every other occurrence recurses to its children (Pattern children included,
/// symmetric with the collector). `set_inferred_type` no-ops on non-`Expr`
/// occurrences, so a rule head / pattern node is unaffected.
fn stamp_rule_body_var_types(occ: &Rc<NodeOccurrence>, var_types: &HashMap<u32, Value>) {
    if occ.as_pattern().is_some() {
        for_each_pattern_child(occ, |c| stamp_rule_body_var_types(c, var_types));
        return;
    }
    let Some(expr) = occ.as_expr() else { return };
    let vid = match expr {
        Expr::Var(Var::Global(vid)) => Some(vid.raw()),
        Expr::Var(Var::DeBruijn(idx)) => Some(*idx),
        _ => None,
    };
    if let Some(vid) = vid {
        if let Some(ty) = var_types.get(&vid) {
            occ.set_inferred_type(ty.clone());
        }
        return;
    }
    for_each_child(expr, |c| stamp_rule_body_var_types(c, var_types));
}

/// WI-282 + WI-603: type every rule body in a single pass. For each live non-fact
/// rule, collect its De Bruijn var types ONCE (head + body constraints, sourced
/// from op-param / entity-field signatures) and then:
///
///   * **Contradiction** (WI-603, subsuming `check_rule_typing`): a var whose
///     constraints don't unify is reported as a rule type error — but ONLY for the
///     sort-scoped rules `check_rule_typing` walked (`reportable`, built by the
///     driver's `by_domain` sweep over each `SortInfo` sort). A free
///     namespace-level rule's contradiction stays unreported, exactly as before.
///     A contradictory rule's receiver sorts are unreliable, so it is neither
///     dispatched nor stamped.
///   * **Dot dispatch** (WI-282): rewrite every `Expr::DotApply` to its method
///     `Apply` / `field_access` form *before* the body reaches SLD (the rule-body
///     peer of the op-body dot dispatch, WI-279), the receiver's concrete sort read
///     from the collected var types. Only a body that contains a dot pays the walk.
///   * **Stamp** (WI-603): persist the collected type onto every body `Var` leaf's
///     occurrence, so downstream consumers read `inferred_type` off the occurrence
///     instead of re-walking signatures.
///
/// Runs over ALL live non-fact rules — sort-scoped AND free namespace-level (a
/// free rule's domain is its namespace, which has no `SortInfo`, so the driver's
/// sort loop misses it). This subsumes the second `collect_rule_var_types`
/// recompute: `check_rule_typing` no longer collects (it contributed only the
/// contradiction, now emitted here) and the dot pass no longer collects separately.
pub(super) fn type_rule_bodies(
    kb: &mut KnowledgeBase,
    reportable: &std::collections::HashSet<crate::kb::RuleId>,
    // WI-745 / WI-1026: parallel to `errors`, tagging each error with the
    // `source_id` of the rule-body atom (or rule head) it came from, so it renders
    // `path:line:col` instead of a bare byte offset. On entry `sources` is parallel
    // to `errors` (the caller pads); restored on exit — the `check_entity_facts` /
    // `check_operation_bodies` contract, held rather than re-invented.
    //
    // This pass used to leave every error untagged (the caller padded with `None`),
    // which was tolerable while it reported only the WI-282 dot failures. WI-1026
    // raises the WI-1012 SUPPLIER TIE here, and that refusal's whole reason for
    // living at the typer rather than at eval is that the typer HOLDS THE SPAN —
    // an unlocated copy of it would be the fallback WI-1012 removed.
    errors: &mut Vec<TypeError>,
    sources: &mut Vec<Option<crate::span::SourceId>>,
) {
    for rid in kb.live_rule_ids() {
        if kb.is_fact(rid) {
            continue; // facts have no body
        }
        // A value-carrier (denoted) head has no hash-consed term to read
        // constraints from; such heads are facts in practice, but guard rather
        // than panic.
        let head = match kb.rule_head_value(rid).clone() {
            Value::Term { id: t, .. } => t,
            _ => continue,
        };
        let body_nodes: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
        // WI-20260925-P7VP4 — A BODY THE REQUIREMENT WEAVE ELABORATED WAS TYPED BY THE RUN
        // THAT WOVE IT. The typer runs again on every later load phase (a layer, a second
        // `load_all`), over every live rule, and a woven call is a post-elaboration form it
        // has no surface case for: MEASURED, one woven stdlib clause failed 133 rows of the
        // workspace with "expected surface expression, got bottom / post-elaboration form"
        // once a second program loaded. The weave runs only after this pass, so a body
        // holding one was typed, stamped and elaborated by an earlier run, and its stamps
        // persist on the shared occurrences.
        if body_nodes.iter().any(|n| occ_holds_woven_call(n)) {
            continue;
        }
        // WI-1058 — the rule whose TEXT a checked-not-typed refusal points at.
        let rule_sym = kb.head_functor(head);
        // The one collection per rule: head + body var types + whether they unify.
        // Shared by the contradiction report, the dot env, and the stamp.
        let (var_types, contradiction) = collect_rule_var_types(kb, head, &body_nodes);
        if contradiction {
            // On a contradiction the receiver sorts are unreliable — skip dispatch
            // and stamping. Report only for the sort-scoped rules `check_rule_typing`
            // walked; a free rule's contradiction stays unreported, as before.
            // WI-20260902-CZJ2N — READ THE HEAD THROUGH `head_functor`, not a `Term::Fn`
            // destructure. `rule_sym` above already IS that read and was computed and
            // discarded here; the destructure additionally assumed a shape a NULLARY head
            // no longer has (it is stored as `Term::Ref`), so a 0-ary-headed rule would
            // lose this diagnostic.
            //
            // NOT DRIVEN, and said rather than claimed: MEASURED on
            // `wi_9c2pz_per_application_type_params_test`'s own contradiction fixture with
            // the head rewritten `bad()` and `bad`, BOTH answer zero contradictions — and
            // both answered zero on the pre-CZJ2N tree too. Something upstream of this
            // arm already declines a nullary-headed rule (the contradiction is not
            // FLAGGED, so this branch is never reached), so the `Term::Fn` gate was not
            // what suppressed it and closing the gate fixes no observable behaviour. It
            // is closed anyway because the assumption is false and the correct read was
            // already in hand — an untested branch that reads a shape the store cannot
            // produce is a trap for whoever makes the upstream case reachable.
            if reportable.contains(&rid) {
                if let Some(head_sym) = rule_sym {
                    // WI-458: the rule's own head span, keyed by RuleId — no
                    // `term_span` fallback (see `check_pattern_fragment`).
                    let head_span = kb.rule_head_span(rid);
                    errors.push(TypeError::Other {
                        site: TypeError::here(),
                        span: head_span.map(|s| s.span),
                        context: TypeErrorContext::Rule {
                            name: head_sym,
                            field: RuleField::Whole,
                        },
                        expected: "consistent variable types".to_string(),
                        actual: "contradictory variable types".to_string(),
                    });
                    sources.push(head_span.map(|s| s.source));
                }
            }
            continue;
        }
        let var_types = Rc::new(var_types);

        // WI-282: dispatch dots — only a body that contains one pays the walk.
        // (The KB-global `has_dot_applies` flag is NOT a valid gate — it is set only
        // by the EXPR-occurrence load path [op bodies]; a rule body loads its dot via
        // term→occurrence materialization, which does not set it.)
        // WI-1026 widened the gate to a DIRECT call on a defaulted spec op, which
        // needs the same walk for the same reason — see [`occ_needs_call_dispatch`].
        //
        // WI-603: stamping (`stamp_rule_body_var_types`) is interior-mutable on the
        // shared `Rc<NodeOccurrence>`, so writing the in-hand `Rc`s persists onto the
        // KB's stored body — no re-fetch needed. Stamp the FINAL occurrences: the
        // (possibly rewritten) `new_body` on the dot path, the untouched `body_nodes`
        // otherwise.
        if body_nodes.iter().any(|n| occ_needs_call_dispatch(kb, n)) {
            // Install the var types so a receiver `?x` (an `Expr::Var(DeBruijn)`)
            // resolves to its concrete sort, exactly as an operation's param env
            // resolves an op-body receiver. The env is otherwise empty — a rule body
            // carries no enclosing sort / lexical params; any let/lambda/match inside
            // a dot subtree introduces its own (named `Global`) bindings, threaded by
            // the typer's normal env handling.
            let mut env = TypingEnv::empty();
            env.set_debruijn_types(var_types.clone());
            // WI-977: the scope this rule was WRITTEN in, for the `internal`
            // visibility check a dot projection runs and for the scope its refusal
            // names. Deliberately NOT `set_enclosing_sort` — that installs a
            // requirement frame this body must not acquire (see above); this field
            // is read by `referencing_scope` alone.
            env.set_rule_scope(kb.rule_domain(rid));
            // WI-20260922-0DK3H — and what this clause DECLARES. See
            // [`TypingEnv::rule_declared_specs`]: the brackets are route 4's slot source,
            // so a rule-body call's dep is discharged by the clause's own
            // `require[Spec[…]]` exactly as an operation-body call's is by a parameter's
            // type. Collected HERE because this is the only site holding the `RuleId`.
            //
            // The builtin is absent in a minimal KB that never registered it; then no
            // rule can carry a bracket and the list is correctly empty — the same reason
            // [`check_rule_body_requirements`] states at its own `fd_sym`.
            if let Some(fd) = kb.try_resolve_symbol(crate::parse::desugar_target::qualified(
                crate::parse::desugar_target::FIND_DICTIONARY,
            )) {
                let mut declared: Vec<Value> = Vec::new();
                for node in &body_nodes {
                    collect_declared_spec_views(node, fd, &mut declared);
                }
                env.set_rule_declared_specs(declared);
            }
            // WI-557 / WI-602: mark this as rule-body context so `check_apply_iter`
            // treats the WI-539 value-precondition `requires`-check as refutation-
            // aware — a rule body is SLD/relational with no call-site Γ, so a
            // precondition over a SYMBOLIC rule-body var legitimately FLOATS and is
            // skipped (it would otherwise raise a spurious, swallowed
            // `UnsatisfiedPrecondition` that also leaves the dot undispatched); a
            // GROUND-REFUTED one is still a definite violation and surfaces (the
            // `UnsatisfiedPrecondition` arm of `dispatch_calls_in_occ`).
            env.mark_rule_body_dispatch();
            let mut changed = false;
            let new_body: Vec<Rc<NodeOccurrence>> = body_nodes
                .iter()
                .map(|n| {
                    // WI-1026: tag whatever THIS atom reports with the atom's own
                    // file. Per-atom rather than per-rule because a rule body can
                    // carry atoms from different files (a `@[simp]`-rewritten or
                    // synthesized atom keeps its origin's span), and the point of
                    // the tag is that the path names where the author must look.
                    let before = errors.len();
                    // WI-1058: a rule's top-level body atoms ARE its goals — the seed of
                    // the position walk.
                    let rewritten = dispatch_calls_in_occ(
                        kb,
                        &env,
                        n,
                        BodyPos::Goal(GoalCommit::Top),
                        rule_sym,
                        // A rule's top-level atom sits in no slot, so nothing hints or
                        // declares a type for it (WI-20260904-50B2K part (b)).
                        None,
                        None,
                        errors,
                    );
                    debug_assert_eq!(
                        sources.len(),
                        before,
                        "WI-745: `sources` must stay parallel to `errors` across each atom",
                    );
                    sources.resize(errors.len(), Some(n.span.source));
                    if !Rc::ptr_eq(&rewritten, n) {
                        changed = true;
                    }
                    rewritten
                })
                .collect();
            // Stamp the rewritten occurrences (`new_body` IS the stored body when a
            // dot fired; otherwise its entries are ptr-eq to `body_nodes`, so this
            // stamps the same occurrences either way), then write back if changed.
            for node in &new_body {
                stamp_rule_body_var_types(node, &var_types);
            }
            // `reassemble`'s ptr-eq short-circuit means an unchanged body re-clones
            // the same `Rc`s; only write back when a dot actually fired.
            if changed {
                kb.set_rule_body_nodes(rid, new_body);
            }
        } else {
            // No dot: `body_nodes` already holds the stored `Rc`s — stamp directly.
            for node in &body_nodes {
                stamp_rule_body_var_types(node, &var_types);
            }
        }
    }
}

/// WI-742 (proposal 060 §2) — the qualified name of the GENERATED typed-head guard,
/// `domain(?x, T)`.
///
/// NOT a [`crate::parse::desugar_target`]: the converter never mints it, so it is
/// outside the set `desugar_target::ALL` obliges its readers to cover. It is looked
/// up rather than written for the same reason `find_dictionary` is — `anthill.kernel`
/// is not implicitly imported, so no source `domain(…)` reaches this symbol unless the
/// author names the namespace, which is what makes WI-743's user-defined `domain`
/// member a DIFFERENT name rather than a capture of this one.
pub(crate) const TYPE_DOMAIN_GOAL: &str = "anthill.kernel.domain";

/// WI-20260925-SHED7 — the type test a FILLABLE typed-head bound runs in front of its body,
/// `__domain_guard(?x, B)` ([`install_typed_head_domain_goals`],
/// [`crate::kb::resolve::BuiltinTag::TypeDomainGuard`]): [`TYPE_DOMAIN_GOAL`]'s question,
/// except that a ground value whose type the closed reading leaves open passes — the fill
/// appended after the body owns it. Its own builtin rather than a flag on `domain`, so a
/// written `domain(…)` cannot ask for that answer.
pub(crate) const TYPE_DOMAIN_GUARD: &str = "anthill.kernel.__domain_guard";

/// WI-20260911-5G28A S3 — the metacall a typed head's bound reaches its domain through when
/// the bound names a type VARIABLE: `apply_domain(?d, ?x)` runs the domain the `SortDomain`
/// dictionary `?d` names. See [`crate::kb::resolve::BuiltinTag::ApplyDomain`].
pub(crate) const APPLY_DOMAIN_GOAL: &str = "anthill.kernel.apply_domain";

/// WI-20260911-5G28A S3 (proposal 060 §2.2) — the kernel spec whose member is a sort's
/// `domain`: evidence that `T` has one. Declared in `anthill/reflect/reflect.anthill`;
/// every instance is derived (`kb::sort_domain_derive`).
pub(crate) const SORT_DOMAIN_SPEC: &str = "anthill.reflect.SortDomain";

/// WI-20260925-SHED7 (proposal 067) — the interface `SortDomain` provides: one rule,
/// `fill(?x)`. Declared in `anthill/reflect/reflect.anthill`.
pub(crate) const FILLABLE_SPEC: &str = "anthill.reflect.Fillable";

/// WI-20260925-SHED7 — where a `SortDomain` dictionary provided by `sort` holds its FIRST
/// CONDITION: the typer lays such a dictionary out as `SortDomain`'s own chain (the
/// `Fillable` it provides, a conversion filed where a `requires` goes), then `sort`'s
/// sort-level `requires`, then the provision's conditions ([`dict_layout`]). The derived
/// `fill` clauses read condition `k` at this offset plus `k`, and a dictionary the resolver
/// builds from a type is padded to it, so every `SortDomain` dictionary — built by the
/// typer for a citation or a call, or by the resolver from a type — is read one way.
pub(crate) fn sort_domain_sub_offset(kb: &mut KnowledgeBase, sort: Symbol) -> usize {
    let spec_half = kb
        .try_resolve_symbol(SORT_DOMAIN_SPEC)
        .map_or(0, |spec| direct_requires_chain_rc(kb, spec).len());
    spec_half + provider_dict_entries(kb, sort, None).len()
}

/// WI-20260925-SHED7 — the typer's own count of a `SortDomain` dictionary's subs for
/// `sort`, both halves ([`dict_layout`]): what `sort_domain_sub_offset` plus the conditions
/// must equal once the provision rows exist.
pub(crate) fn sort_domain_dict_len(kb: &mut KnowledgeBase, sort: Symbol) -> Option<usize> {
    let spec = kb.try_resolve_symbol(SORT_DOMAIN_SPEC)?;
    let layout = dict_layout(kb, spec, sort, None);
    Some(layout.spec_len + layout.provider_len)
}

/// WI-20260925-SHED7 — is `spec` (canonically) `anthill.reflect.SortDomain`? Asked on every
/// requirement read, so the SHORT name screens first — an index off the `Symbol` — and the
/// qualified resolve runs only for a spec actually spelled `SortDomain`.
pub(crate) fn is_sort_domain_spec(kb: &KnowledgeBase, spec: Symbol) -> bool {
    kb.local_name_of(kb.canonical_sort_sym(spec)) == "SortDomain"
        && kb
        .try_resolve_symbol(SORT_DOMAIN_SPEC)
        .is_some_and(|sd| kb.canonical_sort_sym(sd) == kb.canonical_sort_sym(spec))
}

/// The synthesizing pass that owns every generated [`TYPE_DOMAIN_GOAL`] node — the
/// provenance stamp, and with it the IDEMPOTENCE test for
/// [`install_typed_head_domain_goals`].
///
/// Keyed on provenance, not on the functor, and that is the point: an author who
/// imports `anthill.kernel` and writes their own `domain(?x, T)` beside a typed head
/// must not suppress the generated guard. A functor-presence test would do exactly
/// that, and silently.
pub(crate) fn typed_head_domain_pass(kb: &mut KnowledgeBase) -> crate::kb::occurrence::PassId {
    kb.register_pass("anthill.kb.passes.typed_head_domain")
}

/// WI-742 / WI-743 / WI-20260925-SHED7 (proposal 060 §2–§2.3) — compile every `?x: B`
/// annotation on a RELATIONAL rule head into generated goals: the domain's `fill`, APPENDED
/// after the body, and in front of the body the TYPE TEST:
///
/// ```text
/// rule p(?x: B) :- body      ≡      rule p(?x) :- __domain_guard(?x, B), body,
///                                                 SortDomain[B].fill(?x)
/// ```
///
/// This is proposal 060's rule at its third instance: a type-level declaration written in a
/// rule clause becomes a generated body goal. The head stays structurally bare — the
/// annotation was stripped at load (WI-582's `typed_var` marker) — so the discrimination
/// tree indexes a typed head exactly as it indexes the untyped one.
///
/// THE FILL BOTH TESTS AND GENERATES (060-implementation §7.3, "`SortDomain` is the ONLY
/// domain mechanism"). With `?x` bound it fills `?x` in mode (in) — a membership test, which
/// for a derived domain or a primitive's waiting check is also the type test; with `?x`
/// unbound it GENERATES. What it is depends on what the bound names:
///   * a GROUND type with a domain — `Colour.domain(?x)`, the provider's `fill` called by
///     name, where the sort's `fill` reads no dictionary; else `apply_domain(B, ?x)`, the
///     dictionary built from the type (`List[T = Letter]`);
///   * a type MENTIONING A VARIABLE — `apply_domain(?d, ?x, B)`, which first CONFORMS (reads
///     `?x`'s type into `B`'s variables: the tie between two columns) and fills through
///     `?d`, the clause's implicit `SortDomain` parameter a citation routes — the read
///     `find_dictionary(SortDomain, SortDomain, ?x, out: ?d)` beside it — or, with no
///     caller, through `B` itself;
///   * a type with NO domain — a function type, a tuple, a spec, an abstract sort — the
///     conformance check `domain(?x, B)`, PREPENDED: it only tests, and delays on an unbound
///     `?x` exactly as WI-742 built it.
///
/// THE FILL IS APPENDED, because a generator ahead of the written body enumerates a recursive
/// type forever before the body can prune it: `word(?w) :- domain(?w, List[T = Letter]), ?w
/// <=> [?, ?, ?]` did not terminate, while the twin with the goal LAST answers 27 and stops
/// (WI-743).
///
/// AND A FILLABLE BOUND'S TYPE TEST ALSO RUNS FIRST — the guard [`TYPE_DOMAIN_GUARD`], WI-742's
/// conformance check with one answer changed. Without it the written body ran on a value of
/// the wrong type before any test did: a body goal that FAULTS on the wrong carrier
/// (`add(2.5, 1, ?y)` under `?x: Int64`) turned the clause's quiet refutation into a fault, a
/// CUT committed before the test ran, and a long body enumerated its answers only for the
/// appended test to refuse each of them. The guard WAITS on an unbound or partly bound `?x`,
/// and that is what keeps the fault out when a LATER goal binds it: the guard was delayed
/// first, so rotation re-asks it before the body goal that delayed after it (a guard that
/// stood aside instead let `add(2.5, 1, ?y)` run first). The one answer changed: a GROUND
/// value whose type the closed reading leaves open (`[]` against `List[T = ?t]`) passes —
/// no binding decides it any more, and the fill, which reads the open type, owns it.
///
/// Where the closed reading leaves a ground value's type open and the fill would REFUSE it
/// (`[[]]` against `List[T = Int64]`), the body still runs first: the guard cannot tell it
/// from `[]`, which the fill accepts. The boundary is the closed reading's.
///
/// A SORT'S OWN `fill` CLAUSES GET NOTHING: they are the generator, and their bound is the
/// column type a citation reads — a goal generated from it would run them again
/// (060-typedomains §0). A WRITTEN domain keeps the conformance check it always had.
///
/// THE POPULATION IS EXACTLY THE CLAUSES THE LOADER LET KEEP A BOUND: a directional equation
/// keeps WI-582's match-time reader (`apply_eq_rules`) and is skipped; everything else with
/// a bound is a RELATIONAL head, including a body-less one — `rule p(?x: T) :- true` folds to
/// an empty body (§6.1) and is still a clause that answers.
pub(super) fn install_typed_head_domain_goals(kb: &mut KnowledgeBase) {
    let (Some(dom_sym), Some(guard_sym)) =
        (kb.try_resolve_symbol(TYPE_DOMAIN_GOAL), kb.try_resolve_symbol(TYPE_DOMAIN_GUARD))
    else {
        return; // builtins not registered — nothing to generate against
    };
    let pass = typed_head_domain_pass(kb);
    for rid in kb.live_rule_ids() {
        if kb.rule_type_bounds(rid).is_empty() {
            continue;
        }
        if kb.is_directional_equation(rid) {
            continue;
        }
        // WI-20260908-PW9A0 — THE POPULATION ABOVE IS A COUPLING, SO ASSERT IT: a GUARDED
        // equation is neither a directional equation nor a relational head, and a goal
        // generated for it would never run (WI-20260820-8RJK8: nothing evaluates a matched
        // equation's body). A backstop, unreachable while `load_rule`'s typed-pattern
        // refusal stands.
        debug_assert!(
            !kb.rule_head_value(rid)
                .head(kb)
                .functor_sym()
                .is_some_and(|f| kb.is_equality_connective_functor(f)),
            "install_typed_head_domain_goals reached an EQUATIONAL head: the loader's \
             typed-pattern refusal admitted a bound whose generated goal cannot run, \
             because nothing evaluates a matched equation's body (WI-20260820-8RJK8)",
        );
        let own_fill = kb
            .rule_head_value(rid)
            .head(kb)
            .functor_sym()
            .and_then(|f| kb.fill_relation_sort(f))
            .and_then(|s| kb.sort_domain(s).map(|e| e.kind));
        if matches!(
            own_fill,
            Some(crate::kb::fill_derive::SortDomainKind::Derived | crate::kb::fill_derive::SortDomainKind::Primitive)
        ) {
            continue;
        }
        let written_domain = own_fill == Some(crate::kb::fill_derive::SortDomainKind::Written);
        let body: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
        // IDEMPOTENT by provenance: a second run finds its own stamp and stops. The typer is
        // not guaranteed to run once per KB, and generating twice would fill twice.
        if body.iter().any(|n| n.synthesized_by() == Some(pass)) {
            continue;
        }
        // The provenance anchor is the clause's first body goal where it has one; a
        // body-less clause (`:- true`) has none, so its head span stands in.
        let anchor = match (body.first(), kb.rule_head_span(rid)) {
            (Some(n), _) => Rc::clone(n),
            (None, Some(span)) => {
                NodeOccurrence::new_expr(Expr::Bottom, span, Some(kb.rule_domain(rid)))
            }
            (None, None) => {
                debug_assert!(
                    false,
                    "a type bound on a body-less clause with no source head span",
                );
                continue;
            }
        };
        let bounds: Vec<(u32, TermId)> = kb.rule_type_bounds(rid).to_vec();
        let owner = anchor.owner;
        let mut prepended: Vec<Rc<NodeOccurrence>> = Vec::new();
        let mut appended: Vec<Rc<NodeOccurrence>> = Vec::new();
        for (db_index, bound_tid) in bounds {
            // A bound written with an ALIAS has its target's domain (`dealias_type`).
            let bound_tid = dealias_type(kb, bound_tid);
            // `?x` rides as the SAME DeBruijn index the bound is keyed by
            // (`install_rule_type_bounds` stores `len - 1 - position`), so the goal names
            // the head variable itself and the rule's arity is unchanged.
            let var = || {
                NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(db_index)), anchor.span, owner)
            };
            // The bound rides as the interned type term the loader resolved, in a `Spliced`
            // leaf (`Value::carried` cancels the wrapper at the resolver).
            let ty = || {
                NodeOccurrence::new_expr(Expr::Spliced(Value::term(bound_tid)), anchor.span, owner)
            };
            let goal = |functor: Symbol, pos_args: Vec<Rc<NodeOccurrence>>| {
                NodeOccurrence::synthesized_expr(
                    Expr::Apply {
                        recv_type: None,
                        functor,
                        pos_args,
                        named_args: Vec::new(),
                        type_args: Vec::new(),
                    },
                    Rc::clone(&anchor),
                    pass,
                    owner,
                )
            };
            // What fills the bound, or `None` where only the conformance check can stand: a
            // WRITTEN domain's own clause (it IS the generator), a type with no domain, or a
            // KB that never declared `SortDomain` — the check then still guards the bound.
            let fill: Option<Vec<Rc<NodeOccurrence>>> = if written_domain
                || !bound_is_fillable(kb, bound_tid)
            {
                None
            } else if term_mentions_var(kb, bound_tid) {
                implicit_domain_goals(kb, rid, db_index, bound_tid, &anchor, pass, owner)
                    .map(Vec::from)
            } else {
                // A ground type with a domain: its `fill` by name where it reads no
                // dictionary, else through the type.
                let head = type_term_head_sym(kb, bound_tid).expect("a fillable bound has a head");
                let entry = kb.sort_domain(head).cloned().expect("a fillable bound has a domain");
                if entry.conditions.is_empty() {
                    Some(vec![goal(entry.fill, vec![var()])])
                } else {
                    kb.try_resolve_symbol(APPLY_DOMAIN_GOAL)
                        .map(|apply| vec![goal(apply, vec![ty(), var()])])
                }
            };
            // The fill APPENDED, and the guard in front of the body (see the doc above); a bound
            // with no fill keeps the waiting conformance check, which is all it has.
            match fill {
                Some(goals) => {
                    prepended.push(goal(guard_sym, vec![var(), ty()]));
                    appended.extend(goals);
                }
                None => prepended.push(goal(dom_sym, vec![var(), ty()])),
            }
        }
        kb.prepend_generated_body_goals(rid, prepended);
        kb.append_generated_body_goals(rid, appended);
    }
}

/// Can a value of the bound's type be FILLED: its sort has a `SortDomain`, and so does every
/// argument that sort's `fill` reads — its conditions? A variable counts, being pinned when the
/// clause runs. A bound that names a SPEC — WI-582's `[A]` introducer records `A`'s spec, so
/// `?a: List[T = A]` is stored `List[T = Summable]` — or a function type, a tuple, an abstract
/// sort, names a type nothing fills, and keeps the conformance check.
fn bound_is_fillable(kb: &KnowledgeBase, t: TermId) -> bool {
    match kb.get_term(t) {
        Term::Var(_) => true,
        Term::Ref(s) => kb.has_sort_domain(*s),
        Term::Fn { functor, .. } => {
            let Some(entry) = kb.sort_domain(*functor) else {
                return false;
            };
            entry.conditions.iter().all(|&j| {
                crate::kb::fill_derive::type_arg(kb, t, &entry.params, j)
                    .is_none_or(|a| bound_is_fillable(kb, a))
            })
        }
        _ => false,
    }
}

/// Does the stored type term mention a variable — a rule-scoped one, or the enclosing sort's
/// parameter opened per activation? Either way it is not known until the clause runs.
fn term_mentions_var(kb: &KnowledgeBase, t: TermId) -> bool {
    match kb.get_term(t) {
        Term::Var(_) => true,
        Term::Fn {
            pos_args,
            named_args,
            ..
        } => {
            pos_args.iter().any(|&a| term_mentions_var(kb, a))
                || named_args.iter().any(|&(_, a)| term_mentions_var(kb, a))
        }
        _ => false,
    }
}

/// WI-20260911-5G28A S3, WI-20260925-SHED7 — the two goals a bound MENTIONING A VARIABLE
/// gets:
///
/// ```text
/// apply_domain(?d, ?x, B),  find_dictionary(SortDomain, SortDomain, ?x, out: ?d)
/// ```
///
/// `apply_domain` conforms and fills — through `?d` when a citation routed one, through `B`
/// otherwise. The read is the IMPLICIT PARAMETER a citation routes to: its shape is the
/// anchor form on purpose, so `requirement_read_out` finds it, the typer routes the caller's
/// `SortDomain` slot to it (§7.3 S2) and the resolver binds `?d` when it opens the clause.
/// Unrouted, it builds its dictionary from `?x`'s type once `?x` is bound. `?d` is a new
/// clause variable, so the frame GROWS — by prepending, which leaves every existing De
/// Bruijn index where it was ([`KnowledgeBase::extend_rule_frame_with_bounds`]).
///
/// `None` where the KB never declared the spec or the builtins it is spelled with — a bare
/// KB with no `anthill.reflect`, where nothing could hand the clause a domain anyway.
#[allow(clippy::too_many_arguments)]
fn implicit_domain_goals(
    kb: &mut KnowledgeBase,
    rid: crate::kb::RuleId,
    db_index: u32,
    bound_tid: TermId,
    anchor: &Rc<NodeOccurrence>,
    pass: crate::kb::occurrence::PassId,
    owner: Option<Symbol>,
) -> Option<[Rc<NodeOccurrence>; 2]> {
    let spec = kb.try_resolve_symbol(SORT_DOMAIN_SPEC)?;
    let apply = kb.try_resolve_symbol(APPLY_DOMAIN_GOAL)?;
    let fd = find_dictionary_symbol(kb)?;
    let out_label = kb.intern(REQUIREMENT_OUT_LABEL);
    // The new clause variable: prepended, so its index is the frame's old length.
    let xd_index = kb.rule_globals(rid).len() as u32;
    let xd_name = kb.intern("domain");
    let xd = kb.fresh_var(xd_name);
    let bounds = kb.rule_type_bounds(rid).to_vec();
    kb.extend_rule_frame_with_bounds(rid, &[xd], bounds);

    let span = anchor.span;
    let node = |e: Expr| NodeOccurrence::new_expr(e, span, owner);
    let run = NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: None,
            functor: apply,
            pos_args: vec![
                node(Expr::Var(Var::DeBruijn(xd_index))),
                node(Expr::Var(Var::DeBruijn(db_index))),
                node(Expr::Spliced(Value::term(bound_tid))),
            ],
            named_args: Vec::new(),
            type_args: Vec::new(),
        },
        Rc::clone(anchor),
        pass,
        owner,
    );
    let read = NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: None,
            functor: fd,
            pos_args: vec![node(Expr::Ref(spec)), node(Expr::Ref(spec)), node(Expr::Var(Var::DeBruijn(db_index)))],
            named_args: vec![(out_label, node(Expr::Var(Var::DeBruijn(xd_index))))],
            type_args: Vec::new(),
        },
        Rc::clone(anchor),
        pass,
        owner,
    );
    Some([run, read])
}

/// WI-743 — the sort a stored TYPE TERM heads with: `Colour` for `Ref(Colour)`,
/// `List` for `List[T = ?T]`. `None` for anything that is not a nominal type head
/// (a variable bound, an arrow, a tuple) — none of which a sort derives a domain for.
fn type_term_head_sym(kb: &KnowledgeBase, t: TermId) -> Option<Symbol> {
    match kb.get_term(t) {
        crate::kb::term::Term::Ref(s) => Some(*s),
        crate::kb::term::Term::Fn { functor, .. } => Some(*functor),
        _ => None,
    }
}

/// Does this rule-body occurrence hold a WOVEN call — an `apply_within` a requirement weave
/// put there ([`weave_covered_call`], WI-1040 and WI-20260925-P7VP4)? Iterative, like the
/// other rule-body walks.
fn occ_holds_woven_call(occ: &Rc<NodeOccurrence>) -> bool {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(occ)];
    while let Some(o) = stack.pop() {
        let Some(expr) = o.as_expr() else { continue };
        if matches!(expr, Expr::ApplyWithin { .. }) {
            return true;
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    false
}

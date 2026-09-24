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

/// WI-743 (proposal 060 §2.2) — the qualified name of the DERIVED MEMBER RELATION,
/// `domain_member(?x, T)`: "`?x` is an inhabitant of type `T`".
///
/// A RELATION, not a builtin. One clause is derived per sort with constructors
/// ([`crate::kb::load::derive_domain_member_clauses`]) — a disjunction over the sort's
/// constructors with each field's own domain conjoined inside the branch — plus ONE
/// catch-all clause whose body is [`DOMAIN_LEAF_GOAL`]. That shape is what makes the
/// recursion work: `domain_member(?h, ?T)` inside the `List` clause dispatches on
/// whatever `?T` the caller's `List[T = …]` bound, so one clause serves every element
/// sort and every nesting depth, with no dictionary and no name lookup at run time.
///
/// A SECOND NAME, and deliberately not [`TYPE_DOMAIN_GOAL`]. The two goals a typed head
/// generates ask different questions and sit at opposite ends of the body: the
/// conformance guard is prepended and only TESTS, this one is appended and GENERATES.
/// Sharing one functor would put a generator at the prepended position too, which is
/// the non-termination the settled design measured. It is also mechanically impossible:
/// `step_init` sends a functor with a builtin tag to the builtin and never looks for
/// clauses, so the relation and the builtin cannot be one name.
pub(crate) const DOMAIN_MEMBER_GOAL: &str = "anthill.kernel.domain_member";

/// WI-743 — the qualified name of the leaf arm behind [`DOMAIN_MEMBER_GOAL`]'s
/// catch-all clause. See [`crate::kb::resolve::BuiltinTag::DomainLeaf`].
pub(crate) const DOMAIN_LEAF_GOAL: &str = "anthill.kernel.domain_leaf";

/// WI-20260911-5G28A S3 — the metacall a typed head's bound reaches its domain through when
/// the bound names a type VARIABLE: `apply_domain(?d, ?x)` runs the domain the `SortDomain`
/// dictionary `?d` names. See [`crate::kb::resolve::BuiltinTag::ApplyDomain`].
pub(crate) const APPLY_DOMAIN_GOAL: &str = "anthill.kernel.apply_domain";

/// WI-20260911-5G28A S3 (proposal 060 §2.2) — the kernel spec whose member is a sort's
/// `domain`: evidence that `T` has one. Declared in `anthill/reflect/reflect.anthill`;
/// every instance is derived (`kb::sort_domain_derive`).
pub(crate) const SORT_DOMAIN_SPEC: &str = "anthill.reflect.SortDomain";

/// The synthesizing pass that owns every generated [`TYPE_DOMAIN_GOAL`] node — the
/// provenance stamp, and with it the IDEMPOTENCE test for
/// [`install_typed_head_domain_goals`].
///
/// Keyed on provenance, not on the functor, and that is the point: an author who
/// imports `anthill.kernel` and writes their own `domain(?x, T)` beside a typed head
/// must not suppress the generated guard. A functor-presence test would do exactly
/// that, and silently.
fn typed_head_domain_pass(kb: &mut KnowledgeBase) -> crate::kb::occurrence::PassId {
    kb.register_pass("anthill.kb.passes.typed_head_domain")
}

/// WI-742 (proposal 060 §2) — compile every `?x: T` annotation on a RELATIONAL rule
/// head into a `domain(?x, T)` goal PREPENDED to that clause's body.
///
/// This is proposal 060's rule at its third instance: a type-level declaration written
/// in a rule clause becomes a generated body goal, which at run time only READS the
/// value's carried type. The head itself stays structurally bare — the annotation was
/// already stripped at load (WI-582's `typed_var` marker) — so the discrimination tree
/// indexes a typed head exactly as it indexes the untyped one.
///
/// WHY THE TYPER AND NOT THE LOADER OR THE CONVERTER. The converter has only an
/// unresolved parse-level `T`, and the bound's own resolution happens in the loader —
/// generating there would make the goal's `T` and the bound's `T` two resolutions of
/// one annotation. The loader could do it, but its body nodes are pre-`type_rule_bodies`,
/// so a generated goal would be walked by dot-dispatch and type-collection as if the
/// author had written it. Here, `rule_type_bounds` is installed, `rule_globals` fixes
/// the DeBruijn frame, and [`KnowledgeBase::set_rule_body_nodes`] is the supported edit —
/// the same one `record_find_dictionary_grounding` makes.
///
/// PREPENDED, not appended. In mode (in) that prunes at the earliest point the binding
/// exists; in mode (out) the goal suspends and rotation carries it to wherever it can
/// decide, so the placement costs nothing there. (`docs/design/060-implementation.md` §3.)
///
/// WI-743 ADDS A SECOND GOAL AT THE OTHER END, APPENDED, for a bound whose sort has a
/// domain ([`KnowledgeBase::has_domain_member`]). That one GENERATES, which is what turns a
/// typed head from a filter into a domain: `rule colouring(wa: Colour, …) :- wa != nt`
/// enumerates with no `palette` facts. WHAT it is depends on what the bound NAMES
/// (WI-20260911-5G28A S3, `060-implementation.md` §7.3):
///   * a sort with no parameters — `Colour.domain(?x)`, the member of `Colour`'s
///     `SortDomain`, called statically because the bound names the provider;
///   * a TYPE VARIABLE — nothing names the sort, so an implicit `SortDomain` read and
///     `apply_domain` on what it holds ([`implicit_domain_goals`]), filled by a citation's
///     caller or derived from a bound value;
///   * a parameterised sort — `domain_member(?x, T)`, the kernel relation, whose derived
///     clause carries the element type as an argument (§7.3's S3b moves this one too).
///
/// THE TWO PLACEMENTS ARE MEASURED, not symmetric (settled design §3). A generator ahead
/// of the written body enumerates a recursive type forever before the body can prune it:
/// `word(?w) :- domain(?w, List[T = Letter]), ?w <=> [?, ?, ?]` did not terminate, while
/// the twin with the goal LAST answers 27 and stops. Neither placement gives early
/// pruning of a DELAYED test — that needs wake-on-bind, which is not this.
///
/// THE CONFORMANCE GOAL STAYS, and is not made redundant by the member goal. It is what
/// a sort with NO derived domain has (`String`, a primitive, a spec, a declined sort):
/// its delay/rotate/flounder ladder is WI-742's whole behaviour and is unchanged here.
/// Where both are generated they answer the same question two ways and the member goal
/// is the stricter — a hand-written `domain` narrowing a sort makes mode (in) refute a
/// CONFORMING NON-MEMBER, which is proposal §2.2's domain-defining rule.
///
/// THE POPULATION IS EXACTLY THE CLAUSES THE LOADER LET KEEP A BOUND, and the loader's
/// refusal is what makes that list right:
///   * a DIRECTIONAL EQUATION keeps WI-582's match-time reader (`apply_eq_rules`) and is
///     skipped here — two routes, one syntax, as proposal 060 §2 and WI-742 both say;
///   * everything else with a bound is a RELATIONAL head — this feature — INCLUDING a
///     body-less one. `rule p(?x: T) :- true` folds to an empty body (§6.1) and is still
///     a CLAUSE: measured, it answers `p(5)` where a bare declaration `rule p(?x)` does
///     not, the latter never reaching an assert at all. So the guard has something to
///     guard, and [`KnowledgeBase::prepend_generated_body_goals`] — not
///     `set_rule_body_nodes`, whose assertion forbids exactly this — maintains the
///     WI-812 bodied-rule gate across the fact-ness flip.
pub(super) fn install_typed_head_domain_goals(kb: &mut KnowledgeBase) {
    let Some(dom_sym) = kb.try_resolve_symbol(TYPE_DOMAIN_GOAL) else {
        return; // builtin not registered — nothing to generate against
    };
    // WI-743 — `None` only where the loader derived nothing at all, in which case no
    // bound can have a member clause either and the lookup below never fires.
    let mem_sym = kb.try_resolve_symbol(DOMAIN_MEMBER_GOAL);
    let pass = typed_head_domain_pass(kb);
    for rid in kb.live_rule_ids() {
        if kb.rule_type_bounds(rid).is_empty() {
            continue;
        }
        // A directional equation already has a reader (`apply_eq_rules`, WI-582) —
        // the loader's own classification, re-asked here in its own terms rather than
        // restated in this pass's vocabulary. Everything else the loader let keep a
        // bound is a relational head, INCLUDING a body-less one: `rule p(?x: T) :- true`
        // folds to an empty body (§6.1) and is still a clause that answers, so the
        // guard has something to guard.
        if kb.is_directional_equation(rid) {
            continue;
        }
        // WI-20260908-PW9A0 — THE POPULATION ABOVE IS A COUPLING, SO ASSERT IT.
        //
        // The doc says "everything else with a bound is a RELATIONAL head", and that is
        // true only because `load_rule`'s typed-pattern refusal declines every other
        // shape. It is a documented coupling and was an UNENFORCED one: this pass's own
        // test is `is_directional_equation`, which reads "not a directional equation ⇒
        // relational" — a false dichotomy, since a GUARDED equation is neither.
        //
        // MEASURED, by breaking the coupling on purpose: narrowing that refusal so a
        // guarded equation could keep its bound made this pass prepend a `domain(?x, T)`
        // goal to a clause nothing evaluates (WI-20260820-8RJK8: every firing site gates
        // on `is_equation`, whose first clause is an EMPTY BODY, and nothing anywhere
        // runs a matched equation's body). The bound installed, the body grew a goal, and
        // an UNSATISFIABLE bound was byte-identical to no bound at all — the mechanism
        // running looked exactly like the effect happening. Nothing here complained.
        //
        // A BACKSTOP, NOT A VERDICT, in `RuleHeadOwnedByNoScope`'s sense: unreachable
        // while the refusal stands, and its whole value is that a future change which
        // widens the refusal fails HERE and loudly, instead of silently generating a goal
        // that cannot fire. When 8RJK8 lands and a guarded equation does fire, this is
        // one of the sites that has to be revisited rather than deleted.
        debug_assert!(
            !kb.rule_head_value(rid)
                .head(kb)
                .functor_sym()
                .is_some_and(|f| kb.is_equality_connective_functor(f)),
            "install_typed_head_domain_goals reached an EQUATIONAL head: the loader's \
             typed-pattern refusal admitted a bound whose generated goal cannot run, \
             because nothing evaluates a matched equation's body (WI-20260820-8RJK8)",
        );
        let body: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
        // IDEMPOTENT by provenance: a second run finds its own stamp and stops. The
        // typer is not guaranteed to run once per KB, and generating twice would make
        // the same guard delay twice on one unbound variable.
        if body.iter().any(|n| n.synthesized_by() == Some(pass)) {
            continue;
        }
        // The provenance anchor is the clause's first body goal where it has one; a
        // body-less clause (`:- true`) has none, so its head span stands in. Both are
        // this clause's own location, which is all the anchor is for.
        let anchor = match (body.first(), kb.rule_head_span(rid)) {
            (Some(n), _) => Rc::clone(n),
            (None, Some(span)) => {
                NodeOccurrence::new_expr(Expr::Bottom, span, Some(kb.rule_domain(rid)))
            }
            (None, None) => {
                // A body-less clause the loader never wrote (no head span means no
                // source head). Nothing here can locate the guard it would generate,
                // and a bound on such a clause is not something this pass produced —
                // say so rather than emit an unlocatable goal.
                debug_assert!(
                    false,
                    "a type bound on a body-less clause with no source head span",
                );
                continue;
            }
        };
        let bounds: Vec<(u32, TermId)> = kb.rule_type_bounds(rid).to_vec();
        let owner = anchor.owner;
        let mut new_body: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(bounds.len());
        let mut member_body: Vec<Rc<NodeOccurrence>> = Vec::new();
        for (db_index, bound_tid) in bounds {
            // `?x` rides as the SAME DeBruijn index the bound is keyed by
            // (`install_rule_type_bounds` stores `len - 1 - position`, which is
            // `node_to_debruijn`'s own convention), so the goal names the head
            // variable itself — no new slot is allocated and the rule's arity is
            // unchanged.
            let var =
                NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(db_index)), anchor.span, owner);
            // The bound rides as the interned type term the loader resolved. A
            // `Spliced` leaf is the Value carrier for exactly this (`load.rs`'s
            // `Expr::Spliced(Value::term(row))` is the precedent); the resolver arm
            // cancels the wrapper with `Value::carried`.
            let ty =
                NodeOccurrence::new_expr(Expr::Spliced(Value::term(bound_tid)), anchor.span, owner);
            new_body.push(NodeOccurrence::synthesized_expr(
                Expr::Apply {
                    recv_type: None,
                    functor: dom_sym,
                    pos_args: vec![var, ty],
                    named_args: Vec::new(),
                    type_args: Vec::new(),
                },
                Rc::clone(&anchor),
                pass,
                owner,
            ));
            // WI-743 (proposal 060 §2.2) — the GENERATOR half, for a bound whose sort
            // the loader derived a `domain_member` clause for. A bound with none gets
            // nothing here and keeps WI-742's ladder exactly, which is what makes
            // `rule f(?x: String) :- ?x <=> "abe"` still answer its one row.
            // WI-20260911-5G28A S3 — A BOUND THAT IS A TYPE VARIABLE (`?x: T`) READS ITS
            // DOMAIN THROUGH THE REQUIREMENT CHANNEL: an implicit `SortDomain[T = T]` read,
            // then `apply_domain` on what it holds. No term names the type — a citation's
            // caller holds the evidence for its own rigid, and hands it in (§7.3 S2) — so the
            // domain is a DICTIONARY the clause is given, never one it looks up by name.
            // Mode (in) needs no caller: the read derives from `?x`'s carried type. Neither,
            // and both goals delay and flounder at the drain, as the bound always did.
            if matches!(kb.get_term(bound_tid), Term::Var(_)) {
                if let Some(goals) =
                    implicit_domain_goals(kb, rid, db_index, bound_tid, &anchor, pass, owner)
                {
                    member_body.extend(goals);
                }
                continue;
            }
            let Some(member_sym) = mem_sym else {
                continue;
            };
            let Some(bound_head) = type_term_head_sym(kb, bound_tid) else {
                continue;
            };
            if !kb.has_domain_member(bound_head) {
                continue;
            }
            // WI-20260911-5G28A — THE DETERMINACY GATE IS LIFTED, because the two
            // things it was protecting against are now owned elsewhere.
            //
            // WI-743 SKIPPED a bound that did not name a determinate type, for two
            // reasons that were the same defect: a BARE reference to a parameterised sort
            // (`?w: List`) named no element domain, and a type VARIABLE named no type at
            // all, so the generated goal asked `domain_member(?x, ?T)` with `?T` unbound
            // — which unifies with the head of EVERY derived clause and enumerates TYPES
            // instead of values. Measured at 20 rows (the solution cap) for
            // `rule nest(?w: List[T = List]) :- ?w <=> [[a()]]`, a clause whose body binds
            // `?w` outright and can have at most ONE answer.
            //
            // BOTH REASONS ARE GONE, and each to a different owner:
            //   * the BARE reference is no longer a shape a bound can have — the loader's
            //     `expand_rule_head_bound_type_params` writes the unwritten parameter as a
            //     rule-scoped variable, so `?w: List` arrives here as `List[T = ?t]`;
            //   * the VARIABLE is no longer guessed — `pin_bound_from_value` reads it off
            //     the value in mode (in, out), so a bound value decides the goal in one
            //     step instead of opening a choice point per derived domain. With the
            //     value UNBOUND there is still nothing to range over, and the goal DELAYS
            //     at the resolver's dispatch site (`domain_member_goal_is_undetermined`)
            //     rather than being skipped here.
            //
            // WHAT THAT CHANGES FOR `rule anylist(?w: List) :- true` — stated exactly,
            // because this paragraph is the reason the gate went. It answered ONE
            // conditional row before and answers ONE conditional row now. What moved is
            // WHERE: the goal is GENERATED and stands in the residual, where the gate left
            // it un-asked with nothing said at load. Enumerating instead was built and
            // measured, and it does not come back at all — both operands free is a product
            // of two infinite streams, whose fairness is WI-20260911-09E6M's. An earlier
            // draft of this paragraph claimed the row "now comes back as rows", which is
            // not what ships; found by `/code-review`.
            //
            // SKIPPING WAS ALSO THE SILENT HALF. A skipped goal left `<Sort>.domain` and
            // every `?t`-bearing head reading WI-742's conformance ladder only — a
            // CONDITIONAL answer where the author wrote a generator — with nothing said
            // at load. The control for lifting it is `pin_bound_from_value`: back that
            // read out with this lifted and `nest` reddens to the 20 rows WI-743 measured.
            //
            // THE PREDICATE ITSELF IS GONE rather than left unread. A gate no caller asks
            // is not a gate, and keeping one whose doc still claims to prevent the 20-row
            // enumeration would misdescribe where that prevention now lives — at the
            // resolver's `domain_member_goal_is_undetermined`, which asks the same question
            // of the same bound at the moment the answer can be different.
            let member_bound = bound_tid;
            // THE SELF-CALL TRAP, cut here — WI-20260911-WT8WG moved it from the loader.
            //
            // A clause of a sort's OWN written `domain` carrying that sort's bound
            // (`rule domain(?x: Colour) :- …`, inside `sort Colour`) would get a member
            // goal appended, which resolves through the loader's forwarding clause
            // `domain_member(?x, Colour) :- Colour.domain(?x)`, which re-enters the
            // clause: a loop with no base case. WI-743 refused such a clause at the
            // loader, which cost nothing while the written spelling was 2-ary and the
            // annotation was redundant. At the 1-ARY spelling that annotation is the
            // NATURAL thing to write — it is the derived clause's own shape — so
            // refusing it would refuse the feature's majority spelling.
            //
            // A WRITTEN DOMAIN IS NEVER GENERATED FROM: it IS the generator. So the
            // clause keeps the prepended CONFORMANCE goal (which only tests, and is
            // WI-742's whole behaviour) and loses only the appended MEMBER goal.
            //
            // THE LOADER'S SHAPE DECISION, read back — never a name test. This pass does
            // not ask whether a rule is called `domain`; `record_sort_domain_is_written`
            // is written exactly where the 1-ary hook accepted one, which is the only
            // place that decision is made.
            let own_domain_clause = rule_defines_sort_domain(kb, rid, bound_head);
            if own_domain_clause && kb.sort_domain_is_written(bound_head) {
                continue;
            }

            let var =
                NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(db_index)), anchor.span, owner);
            // WI-20260911-5G28A S3 — A GROUND BOUND WITH NO PARAMETERS calls its sort's
            // `domain` — the member of the sort's `SortDomain` provision, dispatched
            // STATICALLY because the bound already names the provider, exactly as an
            // operation call at a concrete carrier is. The kernel relation stays the one
            // thing that bottoms out (060-typedomains §0): `S.domain`'s OWN clause keeps
            // `domain_member(?x, S)` below, or it would call itself.
            if !own_domain_clause && matches!(kb.get_term(member_bound), Term::Ref(_)) {
                if let Some(dom) = sort_domain_relation(kb, bound_head) {
                    member_body.push(NodeOccurrence::synthesized_expr(
                        Expr::Apply {
                            recv_type: None,
                            functor: dom,
                            pos_args: vec![var],
                            named_args: Vec::new(),
                            type_args: Vec::new(),
                        },
                        Rc::clone(&anchor),
                        pass,
                        owner,
                    ));
                    continue;
                }
            }
            let ty = NodeOccurrence::new_expr(
                Expr::Spliced(Value::term(member_bound)),
                anchor.span,
                owner,
            );
            member_body.push(NodeOccurrence::synthesized_expr(
                Expr::Apply {
                    recv_type: None,
                    functor: member_sym,
                    pos_args: vec![var, ty],
                    named_args: Vec::new(),
                    type_args: Vec::new(),
                },
                Rc::clone(&anchor),
                pass,
                owner,
            ));
        }
        kb.prepend_generated_body_goals(rid, new_body);
        // APPENDED, after the written body — see this function's doc for the measurement.
        kb.append_generated_body_goals(rid, member_body);
    }
}

/// WI-20260911-WT8WG — is `rid` a clause of `<sort>.domain` itself?
///
/// The narrowing that makes the self-call exclusion right. `sort_domain_is_written` says
/// the SORT writes its own domain; it does not say this clause is one of them, and the
/// difference is the whole feature: `rule pick(?x: Palette) :- true` beside a written
/// `Palette.domain` MUST keep its member goal — that appended goal is what makes it
/// answer the written domain's 2 rows instead of the sort's 3. Only `Palette.domain`'s
/// OWN clauses are the ones whose member goal would re-enter them.
///
/// BY SYMBOL, not by name: the head functor is compared against the symbol
/// `<sort_qn>.domain` resolves to, so a rule merely SPELLED `domain` somewhere else is
/// not mistaken for one.
fn rule_defines_sort_domain(kb: &KnowledgeBase, rid: crate::kb::RuleId, sort: Symbol) -> bool {
    // CANONICALISED, because its caller's other half is. `sort_domain_is_written` keys on
    // `canonical_sort_sym`, so asking this one under the sort's WRITTEN name would let an
    // ALIAS pass the first test and fail the second — the exclusion skipped, the member
    // goal appended to a clause of the written `S.domain`, and the loop it exists to cut
    // closed through the forwarding clause. One question, asked the same way twice.
    // Raised by `/code-review`.
    let qn = format!(
        "{}.domain",
        kb.qualified_name_of(kb.canonical_sort_sym(sort))
    );
    let Some(dom_sym) = kb.try_resolve_symbol(&qn) else {
        return false;
    };
    kb.rule_head_value(rid)
        .head(kb)
        .functor_sym()
        .is_some_and(|f| f == dom_sym)
}

/// WI-20260911-5G28A S3 — `<sort>.domain`, the relation a sort's `SortDomain` member is:
/// derived beside the sort (`emit_domain_value_face`) or written in it. By SYMBOL, through
/// the canonical sort, as [`rule_defines_sort_domain`] asks it.
///
/// `None` wherever the loader DECLINED the value face — the sort is parameterised, or its
/// `domain` address holds something that is not its domain: an operation, a const, or a
/// relation at another arity (kernel-language.md: such a sort "has a domain and no
/// `.domain` to cite it by"). The kernel's `domain_member(?x, S)` is then that sort's only
/// name for its domain, and both readers — the typed-head sweep and `apply_domain` — reach
/// it there. The decline record is READ, not re-derived: MEASURED, asking only "is it a
/// relation with clauses" sent `pick(?x: S)` to an author's own 3-ary `domain`, and the
/// sort's three rows became none (`wi_wt8wg…::a_domain_at_an_unrecognised_arity_declines_
/// readably`).
pub(crate) fn sort_domain_relation(kb: &KnowledgeBase, sort: Symbol) -> Option<Symbol> {
    if kb.domain_value_face_decline_reason(sort).is_some() {
        return None;
    }
    kb.try_resolve_symbol(&format!(
        "{}.domain",
        kb.qualified_name_of(kb.canonical_sort_sym(sort))
    ))
    .filter(|&sym| kb.has_kind(sym, crate::kb::SymbolKind::Goal) && kb.has_clauses_under(sym))
}

/// WI-20260911-5G28A S3 — the two goals a TYPE-VARIABLE bound gets in place of a member goal:
///
/// ```text
/// find_dictionary(SortDomain[T = <bound>], SortDomain, ?x, out: ?xd),  apply_domain(?xd, ?x)
/// ```
///
/// THE READ IS AN IMPLICIT PARAMETER, and its shape is the anchor form's on purpose: it is
/// what `requirement_read_out` finds, so a citation routes the caller's `SortDomain` slot to
/// it (§7.3 S2) and the resolver binds `?xd` when it opens the clause; unrouted, it DERIVES
/// from `?x`'s carried type as any anchored read does. `?xd` is a new clause variable, so the
/// frame GROWS — by prepending, which leaves every existing De Bruijn index where it was
/// ([`KnowledgeBase::extend_rule_frame_with_bounds`]).
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
    let param = *kb.type_param_syms_of(spec).first()?;
    let out_label = kb.intern(REQUIREMENT_OUT_LABEL);
    // The new clause variable: prepended, so its index is the frame's old length.
    let xd_index = kb.rule_globals(rid).len() as u32;
    let xd_name = kb.intern("domain");
    let xd = kb.fresh_var(xd_name);
    let bounds = kb.rule_type_bounds(rid).to_vec();
    kb.extend_rule_frame_with_bounds(rid, &[xd], bounds);

    let span = anchor.span;
    let node = |e: Expr| NodeOccurrence::new_expr(e, span, owner);
    let instance = node(Expr::Apply {
        recv_type: None,
        functor: spec,
        pos_args: Vec::new(),
        named_args: vec![(param, node(Expr::Spliced(Value::term(bound_tid))))],
        type_args: Vec::new(),
    });
    let read = NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: None,
            functor: fd,
            pos_args: vec![instance, node(Expr::Ref(spec)), node(Expr::Var(Var::DeBruijn(db_index)))],
            named_args: vec![(out_label, node(Expr::Var(Var::DeBruijn(xd_index))))],
            type_args: Vec::new(),
        },
        Rc::clone(anchor),
        pass,
        owner,
    );
    let run = NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: None,
            functor: apply,
            pos_args: vec![
                node(Expr::Var(Var::DeBruijn(xd_index))),
                node(Expr::Var(Var::DeBruijn(db_index))),
            ],
            named_args: Vec::new(),
            type_args: Vec::new(),
        },
        Rc::clone(anchor),
        pass,
        owner,
    );
    Some([read, run])
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

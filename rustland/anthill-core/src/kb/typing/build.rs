//! The iterative typer's BUILD half: `build_type` combines a node's child results into
//! its type; plus apply-site classification (`classify_pin_or_apply_within`).

use super::*;

/// Assemble a Let / Match / Lambda result from its child results.
pub(super) fn build_type(
    kb: &mut KnowledgeBase,
    frame: TypeBuildFrame,
    simp_enabled: bool,
    simp_rids: &[RuleId],
    work: &mut Vec<TypeWorkOp>,
    results: &mut Vec<Result<TypeResult, TypeError>>,
    // WI-20260904-50B2K part (c): this walk's inference state — see [`WalkSolutions`].
    // Written by the `Apply` arm, read by `LambdaBody` and by the discharge at the work
    // loop's exit.
    solving: &mut WalkSolutions,
) {
    match frame {
        TypeBuildFrame::Stamp => {
            // The node's freshly-produced result is on top of `results`
            // (this frame sits just under its Visit). Peek — don't
            // consume — and record the inferred type onto the result's
            // (possibly-rewritten) node. Ill-typed nodes (`Err`) are
            // left unstamped (`inferred_type` stays `None`).
            if let Some(Ok(r)) = results.last() {
                // WI-342: `inferred_type` is carrier-agnostic — stamp the `ty`
                // directly (a `Value::Node` denoted-bearing type is preserved,
                // not re-grounded). `min_sort` widens it via `sort_functor_of_view`.
                r.node.set_inferred_type(r.ty.clone());
            }
        }
        // Proposal 055 §2 — drain a classified nominal type value. Reproduces exactly
        // what the WI-707 arm of `TypeBuildFrame::Apply` did for a sort-headed
        // application, MINUS its `expects_reflect_type` firing condition: the node is
        // already known to be a type value, so there is nothing left to decide here.
        TypeBuildFrame::TypeValue {
            occ,
            head,
            pos_args,
            named_args,
            env,
        } => {
            let total = pos_args.len() + named_args.len();
            // WI-20260919-N31XX (proposal 065 §1) — THE LOWERING: a BARE read of a rigid
            // in value position IS a slot dispatch, and this is the leaf that changes.
            //
            // `B` becomes `TypeValue[T = B].type_value()`, classified
            // `DeferToRequirement` against the slot the enclosing frame already carries
            // for `requires TypeValue[T = B]`. Nothing else needs a new surface: a type
            // EXPRESSION mentioning `B` (`Cell[V = B]`) is evaluated by the argument
            // pump, whose leaves are these very nodes, so the pump was always the builder
            // 065 §1 says it is.
            //
            // CLASSIFIED HERE AND NOT RE-VISITED. The synthesized call is nullary and its
            // dispatch is already decided ([`type_value_slot`] says which slot), so
            // pushing it back through `check_apply_iter` would ask a question that has no
            // answer — `type_value()` names no carrier, which is the whole reason the
            // slot is looked up rather than inferred. Its type is `Type` by declaration.
            //
            // NO SLOT MEANS NO LOWERING, AND THAT IS HOW THE RULE IS ENFORCED. A read the
            // frame cannot back is left as the `Expr::TypeValue` it was;
            // `check_operation_bodies` refuses whatever bare rigid read SURVIVES typing.
            // So "is there a slot" and "is this read well-formed" are ONE question asked
            // in ONE place, and the rule can never admit a read the lowering then fails
            // to back. It is also what keeps 065 §6's nineteenth census site working: a
            // `K` that `@[simp]` inlining moves into a TYPE position is not lowered here
            // (no slot) and then vanishes from the tree when the enclosing node is
            // rewritten, so the surviving-read pass never sees it.
            if total == 0 {
                if let Some(lowered) = lower_rigid_read_to_slot(kb, &env, &occ, head) {
                    let type_ty = kb.make_sort_ref_by_name("anthill.prelude.Type");
                    results.push(Ok(TypeResult::pure(type_ty, unwrap_env(env), lowered)));
                    return;
                }
            }
            let drain_start = results.len() - total;
            let arg_results: Vec<Result<TypeResult, TypeError>> = results.split_off(drain_start);
            // An ill-typed type argument is surfaced before the WI-709 fit check, the
            // same order the `Apply` arm uses: `Cell[V = <ill-typed>]` should report the
            // argument's own error, not "the arguments do not fit".
            if let Err(e) = collect_arg_errors(arg_results.iter()) {
                results.push(Err(e));
                return;
            }
            // WI-709: the type ARGUMENTS must fit the head's declared params, by the same
            // rule the loader applies to the type written in TYPE position — so
            // `Cell[W = Int64]` (undeclared `W`) and `Cell[Int64, String]` (over-applied)
            // are rejected here rather than building a type term carrying a parameter the
            // sort never declared. Eval's `finish_sort_type` keeps its own guard as the
            // backstop for occurrences that never reach the typer (a rule body).
            let named_keys: Vec<Symbol> = named_args.iter().map(|(s, _)| *s).collect();
            let declared = kb.type_params_of_sort(head);
            if let Err(problem) =
                kb.check_sort_type_args(head, &declared, &named_keys, pos_args.len())
            {
                results.push(Err(TypeError::InvalidTypeArgument {
                    span: Some(occ.span.span),
                    sort: head,
                    problem,
                }));
                return;
            }
            let child_refs: Vec<&Result<TypeResult, TypeError>> = arg_results.iter().collect();
            let node = reassemble_children(&occ, &child_refs);
            let type_ty = kb.make_sort_ref_by_name("anthill.prelude.Type");
            results.push(Ok(TypeResult::pure(type_ty, unwrap_env(env), node)));
        }
        // WI-793: the staged projection-receiver arguments have been typed. Complete the
        // param→argument-type map with their types, build the hints for EVERY argument now
        // that the map is whole, then push the `Apply` frame and the Visits for the
        // arguments still untyped. This is the phase the single-pass "hint everything, then
        // visit everything" order could not express, and the reason a lambda's binder can
        // now read an element type off a literal receiver.
        TypeBuildFrame::ApplyHints {
            occ,
            fn_sym,
            pos_args,
            named_args,
            env,
            expected,
            fuel,
            staged,
            op_params,
            sort_app_hint,
            mut known,
            pos,
        } => {
            // Staging is keyed off the callee's declared params, so reaching here with
            // none is not a degraded case to tolerate — it would silently give EVERY
            // argument a `None` hint, putting the lambda binder back on a fresh `?param`
            // and restoring WI-793's defect with no diagnostic at all. That is the WI-791
            // footgun by name (a required child left silently empty kept two tests green
            // while covering nothing), so assert the invariant rather than comment it.
            debug_assert!(
                !op_params.is_empty(),
                "WI-793: ApplyHints reached with no declared params, but staging is keyed \
                 off them — every argument hint would silently be None",
            );
            // The staged Visits were pushed in reverse, so their results sit at the top of
            // the stack in ASCENDING unified order — the order `staged` itself is in.
            let drain_start = results.len() - staged.len();
            let staged_results: Vec<Result<TypeResult, TypeError>> =
                results.drain(drain_start..).collect();
            for (k, &unified) in staged.iter().enumerate() {
                // A staged argument that FAILED to type contributes nothing to the map, and
                // that is not a silent skip: its `Err` rides `staged_results` into the
                // `Apply` frame below, whose `collect_arg_errors` reports it as the argument
                // error it is. The hints then fall back to the un-eliminated param type —
                // exactly what this call used before staging existed.
                if let Ok(r) = &staged_results[k] {
                    if let Some(psym) = param_sym_for_arg_index(
                        kb,
                        &op_params,
                        unified,
                        pos_args.len(),
                        &named_args,
                    ) {
                        known.insert(psym, r.ty.clone());
                    }
                }
            }
            let (pos_hints, named_hints) = apply_arg_hints(
                kb,
                fn_sym,
                Some(&op_params),
                &sort_app_hint,
                &pos_args,
                &named_args,
                &known,
            );
            let staged_pairs: Vec<(usize, Result<TypeResult, TypeError>)> =
                staged.iter().copied().zip(staged_results).collect();
            work.push(TypeWorkOp::Build(TypeBuildFrame::Apply {
                occ,
                fn_sym,
                pos_args: pos_args.clone(),
                named_args: named_args.clone(),
                env: env.clone(),
                expected,
                fuel,
                staged_results: staged_pairs,
                pos,
            }));
            // Visit only what has NOT been typed — a staged argument is typed exactly once,
            // on this same work-stack, with this same fuel and `@[simp]` gate.
            for (k, (_, arg)) in named_args.iter().enumerate().rev() {
                if staged.contains(&(pos_args.len() + k)) {
                    continue;
                }
                push_visit(
                    work,
                    Rc::clone(arg),
                    env.clone(),
                    named_hints[k].clone(),
                    fuel,
                );
            }
            for (i, arg) in pos_args.iter().enumerate().rev() {
                if staged.contains(&i) {
                    continue;
                }
                push_visit(
                    work,
                    Rc::clone(arg),
                    env.clone(),
                    pos_hints[i].clone(),
                    fuel,
                );
            }
        }
        TypeBuildFrame::Apply {
            occ,
            fn_sym,
            pos_args,
            named_args,
            env,
            expected,
            fuel,
            staged_results,
            pos,
        } => {
            let total = pos_args.len() + named_args.len();
            let drain_start = results.len() - (total - staged_results.len());
            let drained: Vec<Result<TypeResult, TypeError>> =
                results.drain(drain_start..).collect();
            // WI-793: splice back the arguments typed AHEAD of the rest (a staged
            // projection receiver — see `known_arg_types_and_staged`). Empty for every
            // ordinary call, where this is the identity and `drained` already IS the
            // arguments in order; the permutation exists only because a staged argument's
            // result necessarily lands on the results stack before its siblings', whatever
            // its position in the call.
            let mut arg_results: Vec<Result<TypeResult, TypeError>> = if staged_results.is_empty() {
                drained
            } else {
                let mut slots: Vec<Option<Result<TypeResult, TypeError>>> =
                    (0..total).map(|_| None).collect();
                for (unified, r) in staged_results {
                    slots[unified] = Some(r);
                }
                let mut rest = drained.into_iter();
                for slot in slots.iter_mut() {
                    if slot.is_none() {
                        *slot = rest.next();
                    }
                }
                debug_assert!(
                    rest.next().is_none(),
                    "WI-793: more visited results than unstaged arguments",
                );
                slots
                    .into_iter()
                    .map(|s| s.expect("WI-793: staged + visited results cover every argument"))
                    .collect()
            };
            let named_results = arg_results.split_off(pos_args.len());
            let pos_results = arg_results;
            // WI-283: reassemble this Apply from its children's (possibly-
            // rewritten) `.node`s, then — when `@[simp]` rules exist — fire a
            // rule at it *before* classifying (a fired node is discarded, so
            // classifying it would be wasted); on a fire, re-type the RHS so
            // chains/cascades reach fixpoint and the produced apply gets
            // classified for req_insertion. WI-408: the reassembly itself is
            // unconditional (a typer-inserted `some(...)` coercion below must
            // propagate even with no `@[simp]` rules); `reassemble`'s ptr-eq
            // short-circuit keeps the unchanged case allocation-free.
            // WI-707: a SORT-headed application in a `Type` slot IS a type
            // (`Cell[V = Int64]`) — its result is the reflect `Type` sort, and there is
            // no operation to dispatch. Sits ahead of `@[simp]` firing and the spec-op
            // redirect below: a type application is not a redex, and it names no
            // receiver to dispatch on. Its arguments were hinted as types by the Visit
            // arm, so an ill-typed one (`Cell[V = 3]`) still surfaces here, from the
            // shared `collect_arg_errors`.
            if kb.kind_of(fn_sym) == Some(crate::intern::SymbolKind::Sort)
                && expects_reflect_type(kb, expected.as_ref())
            {
                if let Err(e) = collect_arg_errors(pos_results.iter().chain(named_results.iter())) {
                    results.push(Err(e));
                    return;
                }
                // WI-709: the type ARGUMENTS must fit the sort's declared params, by the
                // same rule the loader applies to the type written in TYPE position — so
                // `Cell[W = Int64]` (an undeclared `W`) and `Cell[Int64, String]` (an
                // over-applied positional) are rejected here rather than building a type
                // term that carries a parameter the sort never declared. Eval's
                // `finish_sort_type` keeps its own guard as a backstop for
                // programmatically-built calls; for loaded source it is now unreachable.
                let named_keys: Vec<Symbol> = named_args.iter().map(|(s, _)| *s).collect();
                let declared = kb.type_params_of_sort(fn_sym);
                if let Err(problem) =
                    kb.check_sort_type_args(fn_sym, &declared, &named_keys, pos_args.len())
                {
                    results.push(Err(TypeError::InvalidTypeArgument {
                        span: Some(occ.span.span),
                        sort: fn_sym,
                        problem,
                    }));
                    return;
                }
                let child_refs: Vec<&Result<TypeResult, TypeError>> =
                    pos_results.iter().chain(named_results.iter()).collect();
                let node = reassemble_children(&occ, &child_refs);
                let type_ty = kb.make_sort_ref_by_name("anthill.prelude.Type");
                results.push(Ok(TypeResult::pure(type_ty, unwrap_env(env), node)));
                return;
            }
            let node = {
                // Surface an ill-typed child first — we need `Ok` children to
                // read their `.node` (check_apply_iter aggregates the same).
                if let Err(e) = collect_arg_errors(pos_results.iter().chain(named_results.iter())) {
                    results.push(Err(e));
                    return;
                }
                let child_refs: Vec<&Result<TypeResult, TypeError>> =
                    pos_results.iter().chain(named_results.iter()).collect();
                let node = reassemble_children(&occ, &child_refs);
                // Fire only while fuel remains; on a fire, re-`Visit` the RHS
                // with `fuel - 1` on this same work-stack (no host recursion)
                // so the chain is bounded — a non-terminating rule bottoms
                // out at fuel 0 leaving a partial redex, not a stack overflow.
                if simp_enabled && fuel > 0 {
                    match fire_simp(kb, &node, simp_rids) {
                        Ok(Some(rhs)) => {
                            push_visit_at(work, rhs, env, expected, fuel - 1, pos);
                            return;
                        }
                        Ok(None) => {}
                        // WI-757: a macro REJECTED this redex's occurrences — report
                        // its own words at the sub-expression it named, and abandon
                        // the node (the residual template would only add a second,
                        // less informative error naming the lowering's parameter).
                        Err(rejection) => {
                            results.push(Err(macro_rejection_error(rejection, &node)));
                            return;
                        }
                    }
                }
                node
            };
            // WI-411: an UNQUALIFIED self-named spec-op call inside a provider's own
            // impl (`splitFirst(src)` in `MappedStream.splitFirst`) is bound at load to
            // the enclosing member, shadowing the spec op. When the receiver is NOT the
            // enclosing carrier, redirect to the spec op so the call value-dispatches on
            // the receiver's runtime carrier. Done as a tree-producing rewrite (synthesize
            // the spec-op Apply + re-Visit, like `fire_simp` and the dot form) so the
            // STORED occurrence carries the spec-op functor — req_insertion and eval
            // dispatch it, not just the typer. The re-Visit's `fn_sym` is the spec op
            // (`parent != enclosing`), so the redirect does not re-fire (no loop).
            if !pos_results.is_empty() {
                let recv_ty = pos_results
                    .first()
                    .and_then(|r| r.as_ref().ok())
                    .map(|tr| &tr.ty);
                if let Some(spec_op) = redirect_provider_self_spec_op(kb, &env, fn_sym, recv_ty) {
                    // `node` was `reassemble_children` of this Apply frame's occurrence,
                    // so it is always an `Expr::Apply` here — a non-Apply would be a
                    // build-frame invariant break, not a silent skip (which would
                    // resurface the bug as the original eval MatchFailed).
                    let NodeKind::Expr {
                        expr:
                            Expr::Apply {
                                pos_args: np,
                                named_args: nn,
                                type_args: ta,
                                recv_type: rt,
                                ..
                            },
                        ..
                    } = &node.kind
                    else {
                        unreachable!("WI-411: build_type Apply arm reassembled a non-Apply node");
                    };
                    let pass = crate::kb::simp_rewrite::simp_pass(kb);
                    let synth = NodeOccurrence::synthesized_expr(
                        Expr::Apply {
                            // WI-20260829-W6JH0: the spec-op re-dispatch is the SAME call
                            // with a resolved functor, so the receiver's type claim about
                            // its result survives it.
                            recv_type: rt.clone(),
                            functor: spec_op,
                            pos_args: np.clone(),
                            named_args: nn.clone(),
                            type_args: ta.clone(),
                        },
                        Rc::clone(&node),
                        pass,
                        node.owner,
                    );
                    push_visit_at(work, synth, env, expected, fuel.saturating_sub(1), pos);
                    return;
                }
            }
            let span = Some(node.span.span);
            let r = check_apply_iter(
                kb,
                &*env,
                &env.flow,
                &node,
                fn_sym,
                &pos_args,
                &named_args,
                &pos_results,
                &named_results,
                span,
                expected,
                pos,
                Some(solving),
            );
            results.push(r);
        }
        TypeBuildFrame::Constructor {
            occ,
            ctor_sym,
            pos_args,
            named_args,
            env,
            span,
            expected,
            fuel,
        } => {
            let total = pos_args.len() + named_args.len();
            let drain_start = results.len() - total;
            let mut arg_results: Vec<Result<TypeResult, TypeError>> =
                results.drain(drain_start..).collect();
            let named_results = arg_results.split_off(pos_args.len());
            let pos_results = arg_results;
            // WI-283: reassemble + fire (gated on `@[simp]` rules existing) —
            // mirrors the Apply arm (a `@[simp]` rule may target a domain
            // constructor too, e.g. `transpose(transpose(?m)) = ?m`).
            //
            // WI-1104: this frame carries no [`NodePos`] and its re-Visit is an ordinary
            // [`push_visit`], because an `Expr::Constructor` never reaches the typer AS a
            // rule-body goal: [`call_dispatch_shape`] admits `Expr::Apply` and
            // `Expr::DotApply` only, and a goal-position ENTITY head arrives as an
            // `Expr::Apply` that [`check_apply_iter`] routes to `check_constructor_iter`
            // inline (no frame). A constructor has no declared RETURN for a relational
            // column to be, so the tolerance would mean nothing here either.
            let node = {
                // WI-20260818-7X7NK — BEFORE the aggregator, and only ever INSTEAD of it.
                // THIS is where a `.( )` projection's field failure short-circuits: the
                // marked tuple never reaches `check_constructor_iter` at all, so the
                // author's projection is never consulted and dot dispatch's "no such
                // member" — about a question they did not ask — is what surfaces. It
                // returns `None` for every field failure that is not that (see its gates),
                // leaving the aggregator below the general owner.
                if let Some(errors) = projection_column_errors(
                    kb,
                    &env,
                    pos_args.len(),
                    &named_args,
                    &named_results,
                    &occ,
                ) {
                    results.push(Err(aggregate_errors(errors)));
                    return;
                }
                if let Err(e) = collect_arg_errors(pos_results.iter().chain(named_results.iter())) {
                    results.push(Err(e));
                    return;
                }
                let child_refs: Vec<&Result<TypeResult, TypeError>> =
                    pos_results.iter().chain(named_results.iter()).collect();
                let node = reassemble_children(&occ, &child_refs);
                if simp_enabled && fuel > 0 {
                    match fire_simp(kb, &node, simp_rids) {
                        Ok(Some(rhs)) => {
                            push_visit(work, rhs, env, expected, fuel - 1);
                            return;
                        }
                        Ok(None) => {}
                        // WI-757 — same contract as the Apply arm above.
                        Err(rejection) => {
                            results.push(Err(macro_rejection_error(rejection, &node)));
                            return;
                        }
                    }
                }
                node
            };
            let r = check_constructor_iter(
                kb,
                &*env,
                &env.flow,
                ctor_sym,
                &pos_args,
                &named_args,
                &pos_results,
                &named_results,
                span,
                expected,
                &node,
            );
            results.push(r);
        }
        TypeBuildFrame::DotApply {
            occ,
            member,
            pos_args: pos_nodes,
            named_args: named_nodes,
            env,
            expected,
            fuel,
            pos,
        } => {
            // Only the receiver was pre-typed (WI-443) — pop its result.
            let recv = match results.pop().expect("DotApply: missing receiver result") {
                Ok(r) => r,
                Err(e) => {
                    results.push(Err(e));
                    return;
                }
            };
            let receiver_node = Rc::clone(&recv.node);
            // WI-732: record the receiver's type on the RAW receiver occurrence too (the one
            // the dot's own `Expr::DotApply` holds — `recv.node` is the typer's rewritten
            // twin, a different `Rc`). [`projection_receiver_type`]'s third rung — "a
            // computed relation the receiver node already carries stamped" — was written for
            // this and had NO producer, which is why a multi-column projection over a
            // computed receiver silently fell through to a tuple of independent relations.
            // Cheap and local: an occurrence's inferred type is exactly what was just
            // computed for it, so recording it cannot disagree with a later re-read.
            if let Some(Expr::DotApply { receiver: raw, .. }) = occ.as_expr() {
                if !Rc::ptr_eq(raw, &recv.node) {
                    raw.set_inferred_type(recv.ty.clone());
                }
                // WI-762: record the LOWERED twin, so a consumer that must splice
                // this receiver elsewhere reads it rather than re-deriving it.
                // UNCONDITIONAL, unlike the type stamp above: when `raw` IS
                // `recv.node` the record is the identity, and the reader needs to
                // tell "the leaf lowers to itself" from "no dot was ever typed
                // here" — the guard above collapses those two. Storing it WEAKLY is
                // what makes that safe: the identity case would otherwise put an
                // `Rc` to `raw` inside `raw`. The TYPE is not recorded with it —
                // it is on this node either from the stamp above or, in the identity
                // case, from the `Stamp` frame that typed `recv.node` (the same node).
                raw.set_lowered_receiver(&recv.node);
            }
            // `min_sort`: widen the receiver to its least declared sort. Read
            // the child's result type directly (don't depend on the receiver's
            // `Stamp` frame ordering). WI-342: widen the carrier-agnostic `ty`
            // in place — a `Value::Node` receiver type need not be re-grounded.
            let recv_sort = sort_functor_of_view(kb, &recv.ty);
            let dot_span = Some(occ.span.span);

            // WI-20260824-PAPX0 (proposal 055 umbrella A step 4; design
            // 055-implementation.md §4) — THE DOT-RECEIVER SPLIT, option B: THE
            // DENOTATION DECIDES.
            //
            // A receiver whose type is `Type` and whose denotation is a known sort
            // resolves `.m` in THAT SORT's scope, not among `Type`'s members. The
            // rungs below all key on `recv_sort`, which for such a receiver is
            // `anthill.prelude.Type` — an OPAQUE handle (`sort Type = ?`) that
            // declares no members — so every one of them answered "no such member
            // (dot dispatch)" while the two NAME-route spellings of the same value
            // (`Box.tag()`, `Box[V = Int64].tag()`) resolved and returned 7. One
            // value, three spellings, two answers, decided by whether the receiver's
            // root happened to be let-bound.
            //
            // WHY THIS IS NOT JUST A SUBSTITUTED `recv_sort`. A COMPANION member takes
            // NO receiver argument: `operation tag() -> Int64` is called `tag()`, and
            // the default fallback below synthesizes `m(receiver, …args)`. Handing it
            // the denoted sort would build `tag(t)` — an arity error — so this arm
            // synthesizes the companion shape itself: the member resolved in the
            // denoted sort's scope, the args UNSHIFTED, and the receiver carried as
            // `recv_type` exactly as the loader does for the written `Box[V =
            // Int64].tag()`. That is the `ResolvedReceiver::SortCompanion` case of
            // design §4, and it is why §4 asks for three variants rather than a wider
            // value dispatch.
            //
            // PLACED BEFORE the `@[simp]` dot-rule rung and the default fallback
            // because it decides WHICH SORT the member is looked up in; running after
            // them would let a rule or member keyed on `Type` win by position, which
            // is the lookup-order settlement §4 forbids.
            // WI-20260824-PAPX0: what the receiver DENOTES, carried to the terminal
            // refusal below. The rung itself must FALL THROUGH when it finds nothing
            // (returning early made every later rung unreachable — a measured
            // regression), so the denoted sort cannot be named at the point of the
            // miss; it has to reach the one refusal that actually fires.
            let mut denoted_head_for_diag: Option<Symbol> = None;
            if let Some(type_sym) = kb.try_resolve_symbol("anthill.prelude.Type") {
                if recv_sort == Some(type_sym) {
                    // The denotation, from the receiver itself or from the binder that
                    // holds it. `recv.node` covers a receiver that IS a written type;
                    // the env covers `let t = Box[V = Int64]`, which is the reachable
                    // half (see the binding site's note).
                    let denot: Option<Rc<NodeOccurrence>> = match recv.node.as_expr() {
                        Some(Expr::TypeValue { .. }) => Some(Rc::clone(&recv.node)),
                        // DE-ALIASED FIRST. `let u = t` records `u -> [t]` in
                        // `receiver_aliases` (already transitively canonical), and
                        // `canonicalize_receiver_path` exists for exactly this read.
                        // Without it one hop lost the denotation and restored the
                        // VERBATIM pre-fix diagnostic — `let t = Box[V = Int64]; let u =
                        // t; u.tag()` reported "no such member of anthill.prelude.Type",
                        // the message this ticket exists to abolish, one `let` later.
                        _ => stable_receiver_path(kb, &recv.node)
                            .map(|p| env.canonicalize_receiver_path(p))
                            .filter(|p| p.len() == 1)
                            .and_then(|p| env.type_denotation(p[0]).cloned()),
                    };
                    if let Some(denot) = denot {
                        denoted_head_for_diag = denot
                            .as_expr()
                            .and_then(|e| match e {
                                Expr::TypeValue { head, .. } => Some(*head),
                                _ => None,
                            })
                            // NOT when the member names a CONSTRUCTOR of that sort.
                            // `find_operation_in_scope` scans `OperationInfo` facts only,
                            // so an entity constructor is invisible to every rung here —
                            // and naming the denoted sort then turns "no such member of
                            // `Type`" (a true sentence about the wrong sort) into "no such
                            // member of `Box`" (a FALSE sentence about the right one) for
                            // `t.mk(5)`, where `mk` is right there. Until the constructor
                            // route is admitted, say the less wrong thing.
                            .filter(|head| {
                                let short = short_name_of(kb.local_name_of(member));
                                !kb.constructors_of_sort(*head)
                                    .iter()
                                    .any(|c| short_name_of(kb.local_name_of(*c)) == short)
                            });
                        let Some(Expr::TypeValue { head, .. }) = denot.as_expr() else {
                            unreachable!("PAPX0: type_denotations holds only TypeValue nodes")
                        };
                        let head = *head;
                        // POSITIONAL BRACKETS ARE NOT ADMITTED HERE, and this is a
                        // refusal to guess rather than a gap. `recv_type` is read
                        // downstream by `term_backed_bindings`, which consults
                        // `named_keys` ONLY — so a denotation written `Box[Int64]`
                        // arrived with NO bindings, `V` went free, and
                        // `let t = Box[Int64]; t.wrap("s")` LOADED where the written
                        // `Box[Int64].wrap("s")` correctly refuses. A silent false accept
                        // is strictly worse than the miss it replaced, so this arm stands
                        // down and the ladder below answers exactly as it did before.
                        // Admitting them means naming the positionals against
                        // `type_params_of_sort` when the term is built; that is a real
                        // change to the denotation's lowering, not a condition here.
                        let positional_bracket = matches!(
                            denot.as_expr(),
                            Some(Expr::TypeValue { pos_args, .. }) if !pos_args.is_empty()
                        );
                        let short = short_name_of(kb.local_name_of(member)).to_string();
                        // `find_term`, NOT `alloc`: this only wants to NAME a term the
                        // KB already holds. `TermStore::alloc` bumps the refcount even on
                        // a hash-cons HIT, and `TermStore::find`'s own doc warns that such
                        // a caller "would inflate the count monotonically and keep the
                        // slot from ever being released" — once per qualifying dot frame.
                        // A sort never mentioned as a term declares no member reachable
                        // here; `None` simply falls through to the ladder below.
                        let head_term = kb.find_term(&Term::Ref(head));
                        let denoted_route =
                            head_term.filter(|_| !positional_bracket).and_then(|ht| {
                                crate::kb::load::find_operation_in_scope(kb, ht, &short)
                            });
                        // ONLY A COMPANION MEMBER IS THIS ARM'S BUSINESS, and the
                        // check is `self_receiver_param_index` — the repo's existing
                        // answer to "does this operation take the receiver?" — not a
                        // comment. An INSTANCE member (`combine(a: Box[V], b: Box[V])`)
                        // resolved here and synthesized with args UNSHIFTED silently
                        // DROPPED the receiver: `t.combine(p, q)` became
                        // `combine(p, q)` and LOADED. Measured, and it is worse than a
                        // miss — the same member then behaved oppositely depending only
                        // on whether the binder held a type or a value.
                        let denoted_route = denoted_route.filter(|op| {
                            lookup_operation_info_full(kb, *op).is_some_and(|info| {
                                self_receiver_param_index(kb, &info.params, head).is_none()
                            })
                        });
                        // THE AMBIGUITY (design §4 close, §8 "ambiguous companion versus
                        // `Type` member: name both lookup routes"). `Type` declares no
                        // members in today's stdlib, but it is an ordinary `sort Type = ?`
                        // a program CAN reopen — measured, a fixture doing so loads clean.
                        // With `tag` on BOTH routes this arm answered 7 and never said the
                        // other existed: the lookup-order settlement §4 forbids.
                        //
                        // `head != type_sym` because a receiver that denotes `Type` ITSELF
                        // makes both lookups return the SAME symbol, and the refusal then
                        // reported one route as two ("`tag` names BOTH `Type.tag` AND
                        // `Type.tag`").
                        let type_route = if head == type_sym {
                            None
                        } else {
                            let type_term = kb.find_term(&Term::Ref(type_sym));
                            type_term.and_then(|t| {
                                crate::kb::load::find_operation_in_scope(kb, t, &short)
                            })
                        };
                        if denoted_route.is_some() && type_route.is_some() {
                            results.push(Err(TypeError::Other {
                                site: TypeError::here(),
                                span: dot_span,
                                context: TypeErrorContext::DotProjection { member },
                                expected: "a member reachable by exactly one route"
                                    .to_string(),
                                actual: {
                                    let denoted = kb.local_name_of(head).to_string();
                                    let ty = kb.local_name_of(type_sym).to_string();
                                    format!(
                                        "`{short}` names BOTH the companion member `{denoted}.{short}` of the sort this receiver denotes AND the member `{ty}.{short}` of `Type` itself, and no rule orders them; spell the one you mean"
                                    )
                                },
                            }));
                            return;
                        }
                        // TAKEN ONLY WHEN A COMPANION WAS FOUND. OTHERWISE FALL THROUGH —
                        // NO `return` — and that is the whole shape of this arm, learned
                        // the hard way: the first cut returned unconditionally, which made
                        // `try_fire_dot_rule`, `find_spec_op_for_provided_sort`, the
                        // JSFHG parent rung, field access and relation projection all
                        // UNREACHABLE for a `Type`-typed receiver. `sort.anthill` declares
                        // `fact Eq[T = Type]` / `PartialEq` / `Lattice`, so `t.eq(u)` had
                        // WORKED through the spec route and stopped loading — a measured
                        // regression, with the non-denoted spelling of the same call still
                        // loading beside it. A new admission is a RUNG, never a gate in
                        // front of the ladder.
                        if let Some(op_sym) = denoted_route {
                            let recv_type =
                                crate::kb::node_occurrence::try_occurrence_to_term(kb, &denot)
                                    .map(|id| Value::Term { id });
                            let pass = crate::kb::simp_rewrite::simp_pass(kb);
                            let synth = NodeOccurrence::synthesized_expr(
                                Expr::Apply {
                                    // The receiver's own instantiation, so the callee
                                    // types at `V = Int64` rather than at an unbound `V`
                                    // — the same channel the written companion form fills.
                                    recv_type,
                                    functor: op_sym,
                                    // NOT shifted: a companion member has no receiver
                                    // parameter (enforced by the filter above).
                                    pos_args: pos_nodes,
                                    named_args: named_nodes,
                                    type_args: Vec::new(),
                                },
                                Rc::clone(&occ),
                                pass,
                                occ.owner,
                            );
                            push_visit_at(work, synth, env, expected, fuel.saturating_sub(1), pos);
                            return;
                        }
                    }
                }
            }
            // `pos_nodes` / `named_nodes` are the RAW arg occurrences — used
            // by both the dot-rule override and the default method fallback,
            // and typed once inside the synthesized call (with the callee's
            // param hints).

            // INC2: a sort-specific `@[simp]` dot rule (declared in the
            // receiver's sort) OVERRIDES the default. Fire it first; only fall
            // to the default fallback when none fires. Gated on remaining
            // fire-fuel (bounds the fire→re-Visit chain, as the Apply/Ctor arms
            // do), `@[simp]` rules existing, and a resolved receiver sort (the
            // firing guard's key).
            if fuel > 0 && simp_enabled {
                if let Some(rs) = recv_sort {
                    match try_fire_dot_rule(
                        kb,
                        rs,
                        member,
                        &receiver_node,
                        &pos_nodes,
                        &named_nodes,
                        &occ,
                        simp_rids,
                    ) {
                        Ok(Some(synth)) => {
                            push_visit_at(work, synth, env, expected, fuel - 1, pos);
                            return;
                        }
                        Ok(None) => {}
                        // WI-902 — same contract as the Apply arm above (WI-757);
                        // falling through would instead take the default dispatch,
                        // whose diagnostic names neither the macro nor the reason.
                        Err(rejection) => {
                            results.push(Err(macro_rejection_error(rejection, &occ)));
                            return;
                        }
                    }
                }
            }

            // DEFAULT method fallback: resolve `member` to an operation declared
            // on the receiver's sort, then synthesize `op(receiver, ...args)` —
            // `x.m(a)` becomes `m(x, a)`. This is engine logic (functor resolved
            // dynamically), not a writable rule.
            // Owned: `kb` is mutated below (alloc / find_operation_in_scope),
            // so the borrowed name can't be held across it.
            let short = short_name_of(kb.local_name_of(member)).to_string();
            // WI-1035: the receiver's OWN member is resolved SEPARATELY from the two
            // spec fallbacks below, because it is not merely a rung of the name ladder
            // — when it backs a spec the receiver provides it is route 1 of a SUPPLIER
            // SET, and taking it is a dispatch decision. See
            // [`dot_member_dispatch_decision`].
            //
            // `find_operation_in_scope` reads the sort symbol from a bare
            // `Ref(sort)` / `sort(args)` head, which is what `make_sort_ref` builds
            // since WI-361 (it built a `sort_ref(name:…)` wrapper before).
            let op_sym = if let Some(s) = recv_sort {
                let sort_term = kb.alloc(Term::Ref(s));
                let mut own_op = crate::kb::load::find_operation_in_scope(kb, sort_term, &short);
                // `own_member`, not `member`: the outer `member` is the dot's member NAME
                // (read above, and by `try_fire_dot_rule`); this is the operation it
                // resolved to, which is what the callee's own parameter is called.
                if let Some(own_member) = own_op {
                    match dot_member_dispatch_decision(kb, s, own_member, &short, dot_span) {
                        Ok(DotMember::Take) => {}
                        Ok(DotMember::DispatchByValue(spec_op)) => own_op = Some(spec_op),
                        Err(e) => {
                            results.push(Err(e));
                            return;
                        }
                    }
                }
                own_op
                    // WI-281: spec-satisfaction fallback — `member` may be an
                    // operation on a spec `s` *provides* (e.g. `(3).min(5)` →
                    // `Ord.min` via `fact Ord[Int]`), not declared on
                    // `s` itself. The synthesized `Apply` below is identical;
                    // re-typing it rides the normal spec-op dispatch +
                    // `req_insertion`, which threads the requirement.
                    .or_else(|| find_spec_op_for_provided_sort(kb, s, &short))
                    // WI-614: a spec-typed receiver (`FiniteCollection[…]`) can invoke a
                    // member of a spec it REQUIRES — `FiniteCollection requires Iterable`
                    // ⟹ `.find`/`.isEmpty`/`.iterator`, since a `FiniteCollection` IS
                    // walkable. Gated on an abstract-spec receiver so a concrete carrier
                    // keeps resolving via its OWN + PROVIDED members alone (its Iterable
                    // members already reach it through the provides graph).
                    .or_else(|| {
                        carrier_is_abstract_spec(kb, s)
                            .then(|| find_spec_op_for_required_sort(kb, s, &short))
                            .flatten()
                    })
            } else if let Some(param_ty) = constrained_param_receiver_type(kb, &env, &recv.ty) {
                // WI-1119: the receiver is a TYPE PARAMETER, so it has no sort whose
                // members the three rungs above could search — but a `requires` clause on
                // the enclosing operation or its sort may constrain it, and the NAMED
                // spelling of this very call is already licensed by that clause. Resolve
                // the member against the constraining specs so the dot reaches the same
                // spec operation the named spelling does (§8.7).
                // The call shape is the SYNTHESIZED call's, receiver included — the same
                // `(receiver, …pos_nodes)` list built below when a member is found.
                let call_shape = (1 + pos_nodes.len(), named_nodes.len());
                match find_spec_op_for_constrained_param(
                    kb, &env, param_ty, &short, call_shape, dot_span,
                ) {
                    Ok(found) => found,
                    // A tie between two constraining specs is refused HERE rather than
                    // fallen through: the arms below (field access, relation projection)
                    // would answer nothing and the frame would end in `DotDispatchNoMatch`,
                    // reporting "no such member" for a member found TWICE.
                    Err(e) => {
                        results.push(Err(e));
                        return;
                    }
                }
            } else {
                None
            };
            // WI-20260826-JSFHG — THE PARENT-SORT RUNG, for an ENTITY-typed receiver.
            //
            // A `Colour.red` value IS a `Colour` (§8.2), so a member declared on `Colour`
            // is reachable through it — but the three rungs above search the receiver's own
            // sort symbol, which for a variant type is the CONSTRUCTOR, and a constructor
            // declares no operations. So `r.shout()` on `r: Colour.red` reported "no such
            // member (dot dispatch)" while the named spelling `shout(r)` resolved and the
            // widening `takeAny(r)` was accepted — one value, two answers, which is the
            // position-dependence WI-752 exists to abolish. Found by /code-review: the
            // mechanism predates this ticket, but making variant-typed values REACHABLE is
            // what put values in front of it.
            //
            // PURELY ADDITIVE: it is consulted only where every rung above answered `None`,
            // so no dot that resolves today can resolve differently.
            //
            // EXCEPT AGAINST THE RECEIVER'S OWN FIELD, which it must not steal. Where
            // `op_sym` is `None` the frame falls through to field access, and an entity's
            // own field is a MORE specific answer than a same-named operation on its
            // parent; taking the parent's would make `r.v` mean something different on
            // `Colour.red` than the field it names. So the rung stands down when the member
            // names a field of the receiver entity, and the fall-through keeps it.
            let op_sym = match (op_sym, recv_sort.and_then(|s| kb.strict_parent_sort(s))) {
                (None, Some(parent)) => {
                    let names_own_field = recv_sort
                        .and_then(|s| kb.entity_field_types(s))
                        .is_some_and(|fs| {
                            fs.iter()
                                .any(|(f, _)| short_name_of(kb.local_name_of(*f)) == short)
                        });
                    if names_own_field {
                        None
                    } else {
                        let parent_term = kb.alloc(Term::Ref(parent));
                        let mut found =
                            crate::kb::load::find_operation_in_scope(kb, parent_term, &short);
                        // The SAME dispatch decision rung 1 makes, asked at the parent, so
                        // a member that backs a spec the parent provides is routed
                        // identically whether it is reached through `Colour` or through
                        // `Colour.red`.
                        if let Some(own_member) = found {
                            match dot_member_dispatch_decision(
                                kb, parent, own_member, &short, dot_span,
                            ) {
                                Ok(DotMember::Take) => {}
                                Ok(DotMember::DispatchByValue(spec_op)) => found = Some(spec_op),
                                Err(e) => {
                                    results.push(Err(e));
                                    return;
                                }
                            }
                        }
                        found.or_else(|| find_spec_op_for_provided_sort(kb, parent, &short))
                    }
                }
                (other, _) => other,
            };
            if let Some(op_sym) = op_sym {
                let mut synth_pos: Vec<Rc<NodeOccurrence>> =
                    Vec::with_capacity(1 + pos_nodes.len());
                synth_pos.push(receiver_node);
                synth_pos.extend(pos_nodes);
                let pass = crate::kb::simp_rewrite::simp_pass(kb);
                let synth = NodeOccurrence::synthesized_expr(
                    Expr::Apply {
                        recv_type: None,
                        functor: op_sym,
                        pos_args: synth_pos,
                        named_args: named_nodes,
                        type_args: Vec::new(),
                    },
                    Rc::clone(&occ),
                    pass,
                    occ.owner,
                );
                // Re-type the synthesized call: it rides normal Apply typing +
                // type-param inference + req_insertion, and its result becomes
                // this DotApply node's result.
                push_visit_at(work, synth, env, expected, fuel.saturating_sub(1), pos);
                return;
            }

            // WI-759 (was INC 1b + WI-638's separate THIRD mode): a zero-arg member
            // naming a MEMBER of the receiver — an entity/sort FIELD, a NAMED-TUPLE
            // component (`(x: A, y: B).x`, the positional `t._1`), or a runtime named arg
            // of a `Term`. The method fallback ran first (an operation of that name wins),
            // so only a non-operation member reaches here. Synthesize
            // `field_access(receiver, "member")` — the reflect field-access desugaring
            // (reflect.anthill) whose eval-side twin reads the named field off the runtime
            // `Value::Entity` / `Value::Tuple`.
            //
            // The synth is RE-TYPED via `push_visit`, exactly as the method fallback above
            // is: `field_access`'s declared return `FieldOf[T = R, Name = Name]` reduces to
            // the member's type at the ordinary return-type normalization boundary, so this
            // FORWARD direction and a later RE-TYPE of the stored node are ONE decision
            // procedure. Until WI-759 this stamped the member's type directly and the
            // reverse direction was a separate pair of typer hatches keyed on
            // `field_access`'s own identity — which had already drifted apart exactly as a
            // duplicated procedure does: the entity arm existed on both sides, the
            // named-tuple arm only on this one (WI-758).
            if pos_nodes.is_empty() && named_nodes.is_empty() {
                // The surface `?o.value` interns `value` in the use-site scope, which need
                // not equal the declaring entity's field symbol, so members resolve by SHORT
                // name. (Inherits `resolve_field_type`'s contract that a given field name is
                // the same symbol across a sort's constructors; a multi-variant short-name
                // collision resolves via the first.)
                let member_short = short_name_of(kb.local_name_of(member)).to_string();
                // The SAME resolution the `FieldOf` reduction runs — here only to decide
                // that `member` names a member AT ALL. `NoSuchMember` falls through to the
                // relation-projection mode below and then to `DotDispatchNoMatch`, exactly
                // as before; `Unresolvable` means the member EXISTS but its type does not
                // resolve, which is a real diagnostic and must never degrade into a
                // fall-through reporting "no such member" for a field that is right there.
                match resolve_projected_member(kb, &recv.ty, &member_short, dot_span) {
                    Err(MemberMiss::NoSuchMember) => {}
                    Err(MemberMiss::Unresolvable(msg)) => {
                        results.push(Err(projection_type_error(
                            &TypeErrorContext::DotProjection { member },
                            dot_span,
                            &msg,
                        )));
                        return;
                    }
                    Ok(m) => {
                        // WI-369: a cross-scope projection of a field whose owning entity is
                        // `internal` would alias encapsulated state — reject it HERE, at the
                        // dot's own span and with the precise diagnostic, rather than let the
                        // reduction report it against the rewritten node. (The reduction
                        // checks too, off this same resolution, which is what closes the
                        // hand-written desugared form that never passes through dot dispatch.)
                        if let Some((ctor, fsym, from_scope)) =
                            hidden_field_owner(kb, &m, env.referencing_scope())
                        {
                            results.push(Err(TypeError::ForbiddenInternalField {
                                span: dot_span,
                                entity: ctor,
                                field: fsym,
                                from_scope,
                            }));
                            return;
                        }
                        match synthesize_field_access(kb, &receiver_node, &member_short, &occ) {
                            Ok(synth) => {
                                push_visit_at(
                                    work,
                                    synth,
                                    env,
                                    expected,
                                    fuel.saturating_sub(1),
                                    pos,
                                );
                                return;
                            }
                            // Reflect is not loaded, so the desugaring does not exist —
                            // fall through to the remaining modes, as before.
                            Err(None) => {}
                            // Reflect IS loaded but `field_access`'s declaration is
                            // malformed. Loud: degrading to `DotDispatchNoMatch` would
                            // report "no such member" for every projection in every
                            // program, pointing at the user's code instead of the
                            // declaration.
                            Err(Some(e)) => {
                                results.push(Err(e));
                                return;
                            }
                        }
                    }
                }
            }

            // WI-714 (proposal 052) — FOURTH dot-dispatch mode: a zero-arg member naming
            // a COLUMN of a RELATION receiver is a single-column PROJECTION `r.f`. Select
            // that column: `person_row.name : Relation[T = (name: String)]`.
            //
            // WI-20260818-YQB1Y — `r.(f)` NO LONGER ARRIVES HERE. It used to 1-collapse at
            // convert time into exactly this member access, which is why this arm was
            // documented as the single-member leaf of the `.( )` form. It now builds a
            // marked one-field tuple and is recognized at the tuple checker's pre-check
            // with every other arity. Both routes end at `build_relation_projection`, so
            // `r.f` and `r.(f)` still yield the SAME schema.
            //
            // Sits last: an ordinary op/field member already resolved above.
            if pos_nodes.is_empty() && named_nodes.is_empty() {
                let member_short = short_name_of(kb.local_name_of(member)).to_string();
                if let Some(r) = build_relation_projection(
                    kb,
                    &env,
                    &env.flow,
                    &recv.ty,
                    &recv.effects,
                    &receiver_node,
                    &[(member, member_short)],
                    &occ,
                ) {
                    results.push(r);
                    return;
                }
            }

            // No method and no field matched → clear diagnostic at the dot span.
            // WI-1119: when the receiver is a type PARAMETER, name it and the specs that
            // do constrain it. Recomputing the constraint set here rather than threading it
            // down from the rung is deliberate — the rung returns `None` on the ordinary
            // "not a member of any of them" path, and every arm between it and here can
            // also decline, so the refusal must be able to say what was searched no matter
            // which arm fell through last.
            let receiver_param = constrained_param_receiver_type(kb, &env, &recv.ty).map(|tid| {
                ConstrainedParamReceiver {
                    param: type_display_name(kb, tid),
                    specs: constraining_specs_for_param(kb, &env, tid),
                }
            });
            results.push(Err(TypeError::DotDispatchNoMatch {
                span: dot_span,
                member,
                // THE DENOTED SORT WHEN THERE IS ONE. `recv_sort` for a type value is
                // `anthill.prelude.Type`, an opaque handle that declares no members —
                // a true sentence about the wrong sort, which sent authors looking for
                // a member of `Type` instead of the sort they actually named.
                receiver_sort: denoted_head_for_diag.or(recv_sort),
                receiver_param,
            }));
        }
        TypeBuildFrame::LetAfterValue {
            occ,
            pattern,
            annotation,
            body_occ,
            body_expected,
            fuel,
            outer_flow,
        } => {
            let value_r = results.pop().expect("LetAfterValue: missing value result");
            // Propagate failure up rather than typing the body under a
            // synthesized env — see WI-204 feedback (no fallbacks).
            let r = match value_r {
                Ok(r) => r,
                Err(e) => {
                    results.push(Err(e));
                    return;
                }
            };
            // WI-283: keep the value's (possibly-rewritten) node to
            // reassemble the `Let` at `LetFinal` (its result is consumed here).
            let value_node = Rc::clone(&r.node);
            // WI-342: the env binds a carrier-agnostic `Value` — carry the let
            // value's `ty` (and a `Value` annotation) without re-grounding.
            let value_ty = Some(r.ty);
            let (value_effects, mut ext_env) = (r.effects, r.env);
            // WI-379: a let with an explicit annotation must have its value
            // CONFORM to that annotation — the let-binding counterpart of the
            // operation-return check in `check_operation_bodies`. The
            // args-before-expected reorder makes the value's inferred type
            // authoritative, so a contradicting annotation
            // (`let v: List[String] = id_list(ys: List[Int])`) is a real
            // mismatch and must be rejected rather than silently rebinding the
            // value as the annotated type. (When the annotation merely fills a
            // still-free param it was threaded in as `expected` when the value
            // was typed, so `value_ty` already matches and this check passes.)
            if let (Some(ann), Some(vty)) = (annotation.as_ref(), value_ty.as_ref()) {
                let mut subst = Substitution::new();
                if !types_compatible(kb, &mut subst, vty, ann) {
                    let var = extract_pattern_var_name(&pattern).unwrap_or_else(|| kb.intern("_"));
                    // WI-801: through the shared renderer — `let f: Function[A =
                    // (Int64, Int64), B = Int64] = lambda (p, q, r) -> p` is the
                    // same arity disagreement as the op-arg channel's, and
                    // rendered raw it prints the two sides identically.
                    let (ann, vty) = (ann.clone(), vty.clone());
                    let err = conformance_error(
                        kb,
                        ann,
                        vty,
                        None,
                        TypeErrorContext::LetBinding { var },
                        Some(&value_node),
                    );
                    results.push(Err(err));
                    return;
                }
            }
            // Prefer an explicit annotation (already `Value`, S4a) over the value type —
            // but a bare/partial parametric annotation is first REWRITTEN to keep the
            // value's inferred params (WI-374; conformance already checked above).
            let bound_ty = match (annotation, value_ty) {
                (Some(ann), Some(vty)) => Some(
                    unroll_annotation_with_inferred(kb, &ann, &vty, occ.span, occ.owner)
                        .unwrap_or(ann),
                ),
                (ann, vty) => ann.or(vty),
            };
            // WI-20260904-50B2K part (c), step 3 — GENERALIZE AT THE BINDING, the half of the
            // standard rule step 2 shipped without. A reference instantiates
            // ([`check_bare_ref`]), so `let h = g` binds a MONOTYPE with a fresh carrier and
            // an obligation on it; quantifying that carrier here is what makes the alias as
            // polymorphic as the thing it aliases, and it is why an UNUSED alias no longer
            // refuses a program that loads without it.
            //
            // `ext_env` is still the OUTER environment at this point — the pattern binds
            // below — which is exactly the side condition's subject.
            // A SINGLE BINDER ONLY, and the destructuring case is a MEASURED regression, not
            // a scruple. `let (h, k) = (g, g)  h(2) + k(3)` loads without this generalization
            // and was refused with it: the bound type is the TUPLE, so quantifying it puts a
            // ∀ where `bind_and_label_pattern` reads component types, every component falls
            // to the unnameable `?pat` form, and both names report "unknown functor" — for
            // names that are in fact bound. The standard rule is stated for a VARIABLE
            // binding and that is where it is applied; pushing the ∀ inside the components is
            // a different construct and is not this slice's.
            let single_binder = extract_pattern_var_name(&pattern).is_some();
            let bound_ty = match bound_ty {
                Some(t) if !single_binder => Some(t),
                Some(t) => Some(
                    match solving.generalize_at_binding(kb, &t, &ext_env, occ.span, occ.owner) {
                        Some((binders, context)) => {
                            let binder_terms: Vec<Value> = binders
                                .iter()
                                .map(|v| Value::term(type_param_var_term(kb, Var::Global(*v))))
                                .collect();
                            let binder_list = crate::kb::load::build_value_list(kb, binder_terms);
                            let context_list = crate::kb::load::build_value_list(kb, context);
                            let body = value_to_type_child(kb, &t);
                            Value::Node(kb.make_poly_type_occ(
                                binder_list,
                                context_list,
                                body,
                                occ.span,
                                occ.owner,
                            ))
                        }
                        None => t,
                    },
                ),
                None => None,
            };
            // WI-794: a destructuring binder may carry its own annotation
            // (`let (a: String, b) = intPair`); report a contradiction rather than
            // dropping the annotation. Same rule as the lambda-binder case — the value's
            // type wins for the binding, the false claim is what is rejected.
            let mut binder_errors = Vec::new();
            // WI-803: the relabelled pattern replaces the written one in the
            // reassembled `Let` below, so a destructuring `let` over a permuted
            // value binds by label like every other binder list.
            // WI-20260827-EJ5F5: `PatternRole::Binder` — a `let` is irrefutable; a name
            // colliding with one of the bound value's constructors still binds, so
            // there is nothing to re-point either. Asserted, for the same reason the
            // lambda site asserts it.
            let mut let_repoints: Vec<(Symbol, Symbol)> = Vec::new();
            let pattern = bind_and_label_pattern(
                kb,
                &mut ext_env,
                &pattern,
                bound_ty,
                PatternRole::Binder,
                &mut let_repoints,
                // WI-20260904-50B2K: the seed, as at the lambda site. A `let` whose bound
                // value has NO type (`bound_ty` is `None`) keeps the inert form
                // deliberately — the evidence would have to come from the value's own
                // expression, which is a different channel from this one and is not
                // measured here.
                UnpinnedBinder::Unnameable,
                &mut binder_errors,
            );
            debug_assert!(
                let_repoints.is_empty(),
                "WI-20260827-EJ5F5: `PatternRole::Binder` must never rewrite",
            );
            if let Some(e) = binder_errors.into_iter().next() {
                results.push(Err(e));
                return;
            }
            if let Some(var_name) = extract_pattern_var_name(&pattern) {
                ext_env.declare_local_resource(var_name);
                // WI-400 increment C (eager let-alias): if the value is a STABLE receiver
                // path (a var / field-access chain — immutable `let` ⟹ one runtime value),
                // record `var_name`'s canonical receiver, so a later projection off
                // `var_name` canonicalizes to the aliased receiver (`let y = z ⟹
                // y.M ≡ z.M`). An unstable value (`let y = f()`) records nothing — it is
                // its own neutral receiver.
                match stable_receiver_path(kb, &value_node) {
                    Some(path) => ext_env.bind_receiver_alias(var_name, path),
                    // A re-bind to an UNSTABLE value must CLEAR any stale alias from an
                    // outer `let` of the same name — else `let y = p; let y = f(); … : y.M`
                    // would wrongly canonicalize `y.M` to `p.M` (a false accept).
                    None => ext_env.clear_receiver_alias(var_name),
                }
                // WI-20260824-PAPX0 (design 055 §4, option B): if the value is a
                // WRITTEN TYPE, record what `var_name` DENOTES, so a later `t.m(…)`
                // resolves `m` in that sort's scope instead of among `Type`'s members.
                //
                // THIS IS THE WHOLE ROUTE, not a convenience. Measured: a receiver
                // that is syntactically a type never reaches the `DotApply` frame at
                // all — `Box[V = Int64].tag()` is a `field_access` whose object is an
                // `application`, which `is_value_receiver` classifies as a NAME, and
                // `Box.tag()` is one `name` node the loader's
                // `dot_call_receiver_chain` resolves whole at its first rung. Both
                // bypass the typer's dot frame. So the only way a `Type`-typed
                // receiver arrives at a dot is through a BINDER or an operation
                // RESULT, and this is the binder half.
                //
                // The operation-result half (`let t = id_ty(Box[V = Int64]); t.tag()`)
                // is deliberately OUT OF SCOPE and still refuses: the denotation is
                // lost through the call, and recovering it needs a `Type` that CARRIES
                // its head rather than a per-binder record. Stated on the ticket as a
                // scope boundary, not left to be discovered.
                //
                // THE CLEAR ARM IS NOT DRIVEN BY ANY TEST, and that is measured, not
                // assumed: removing it leaves every row of
                // `wi_papx0_dot_receiver_split_test` green. `let t = 1` mints a FRESH
                // binder symbol (WI-550's shadowing-correct identities), so this map —
                // keyed by `Symbol` — cannot collide, and a lambda binder shadowing a
                // let does not inherit the denotation either (its receiver types as
                // `<unresolved receiver>`, so the branch above never runs). The
                // hazard `clear_receiver_alias` documents for its own channel is
                // therefore not reachable here today.
                //
                // KEPT ANYWAY, as the pairing that channel already has: the map is
                // keyed by a symbol whose freshness is someone else's invariant, and
                // if that ever changes this arm is what keeps a stale denotation from
                // becoming a FALSE ACCEPT — resolving `t.m` in a sort the current `t`
                // has nothing to do with. Said plainly rather than left to read as a
                // guard with a control behind it.
                match value_node.as_expr() {
                    Some(Expr::TypeValue { .. }) => {
                        ext_env.bind_type_denotation(var_name, Rc::clone(&value_node))
                    }
                    _ => ext_env.clear_type_denotation(var_name),
                }
            }
            // WI-550 / proposal 050: the binding rule `let x = e ⟹ Γ ∪ { x ≡ e }`,
            // re-enabled now that a binder reference reads as its indexable
            // `var_ref(x)` term twin (WI-537) AND each binding site carries a
            // shadowing-correct fresh identity (WI-550) — so `let x = 0; let x = 1`
            // add `x₁ ≡ 0`, `x₂ ≡ 1` over DISTINCT symbols, and the inner body
            // references only `x₂`, never matching the stale `x₁ ≡ 0`: no Γ-retract
            // (the type-level `clear_receiver_alias` analog) is needed.
            //
            // Gated on a PURE value (`value_effects.is_empty()`): `x` denotes the
            // VALUE of `e`, so `x ≡ e` is a sound logical fact only when `e` is
            // referentially transparent — an effectful `let x = Cell.get(c)` could
            // re-read differently than `x`. A non-var (destructuring) pattern
            // contributes no single-binder equality here. Whichever pure form `e`
            // takes — a literal, a binder, a constructor, or a (pure) call/dot-call,
            // all of which `occ_head` indexes — enters Γ soundly; `assume` only
            // drops a genuinely `Opaque`-headed value (a lambda, a collection
            // literal, an `if`/`match` expression) losslessly.
            let body_flow = match extract_pattern_var_name(&pattern) {
                Some(var_name) if value_effects.is_empty() => {
                    let value_v = Value::Node(Rc::clone(&value_node));
                    let fact = binding_gamma_fact(kb, var_name, value_v, occ.span, occ.owner);
                    outer_flow.assume(kb, fact)
                }
                _ => outer_flow,
            };
            // WI-539 (proposal 050 "operation call" rule, `ensures` half): if the
            // value is a direct call bound to `var_name`, assume the callee's
            // postconditions into the body's Γ with `result ↦ var_name`. This is
            // the canonical Γ populator — `let y = op(); …` where `op ensures
            // neq(result, 0)` puts `neq(y, 0)` in Γ, discharging a later
            // `div(_, y)` guard with no branch test written. Not gated on the
            // purity above: a postcondition holds after the call regardless of
            // effects (the binding fact, in contrast, needs `e` referentially
            // transparent).
            let body_flow = match extract_pattern_var_name(&pattern) {
                Some(var_name) => assume_call_ensures(kb, body_flow, &value_node, var_name),
                None => body_flow,
            };
            work.push(TypeWorkOp::Build(TypeBuildFrame::LetFinal {
                occ,
                value_node,
                value_effects,
                pattern,
            }));
            // WI-537: the body's types come from the value result (`ext_env`),
            // its Γ from the let-site flow narrowed by the binding fact above.
            push_visit(
                work,
                body_occ,
                Env {
                    types: Rc::new(ext_env),
                    flow: body_flow,
                },
                body_expected,
                fuel,
            );
        }
        TypeBuildFrame::LetFinal {
            occ,
            value_node,
            value_effects,
            pattern,
        } => {
            let body_r = results.pop().expect("LetFinal: missing body result");
            let body_r = match body_r {
                Ok(r) => r,
                Err(e) => {
                    results.push(Err(e));
                    return;
                }
            };
            let effects = merge_effects(kb, &value_effects, &body_r.effects);
            // WI-283: reassemble the `Let` from [pattern, value, body]
            // (`for_each_child(Let)` order, WI-318 added pattern) so a
            // rewrite in any of them propagates. WI-803: the pattern is no longer
            // "passed through unchanged" — `bind_and_label_pattern` returned it
            // relabelled, and THAT is the one that has to land in the stored tree.
            let node = crate::kb::simp_rewrite::reassemble(
                &occ,
                &[Rc::clone(&pattern), value_node, Rc::clone(&body_r.node)],
            );
            results.push(Ok(TypeResult {
                ty: body_r.ty,
                env: body_r.env,
                effects,
                node,
            }));
        }
        TypeBuildFrame::MatchAfterScrutinee {
            occ,
            branches,
            outer_env,
            body_expected,
            fuel,
        } => {
            let scr_r = results
                .pop()
                .expect("MatchAfterScrutinee: missing scrutinee result");
            // WI-20260829-1SSXM — A SCRUTINEE THAT DID NOT TYPE FAILS THE MATCH, and it
            // is the LAST frame to learn that. Every other build frame propagates a child
            // failure (`LambdaBody` re-pushes it; `IfExpr` / `Apply` / `Constructor` run
            // their children through `collect_arg_errors`); this one used to read the
            // result through `.ok()` three times and never re-push the `Err`, which typed
            // the arms against no scrutinee type at all and — worse — put the
            // UN-REWRITTEN scrutinee node back into the stored tree. The whole match then
            // reported nothing and the program LOADED, so a `match find(rs, lambda r ->
            // r.nosuchfield) …` died at eval with `Internal("unhandled Expr variant")`,
            // which is not a `Raised` payload and so cannot be caught.
            //
            // The early return is safe exactly here: this frame has pushed no work and
            // drained no results yet (the arm-body `Visit`s and `MatchFinal` go on the
            // stack at the very bottom), so one `Err` is the match's single result and
            // the stack stays balanced — the same shape the `binder_error` /
            // `guard_error` short-circuits below already rely on.
            //
            // WI-342: the scrutinee's `ty` rides as a `Value` — the sort lookup and the
            // pattern env binding read it carrier-agnostically (no re-ground). WI-283:
            // `node` is the scrutinee as any `@[simp]` rewrite left it, which is what
            // `MatchFinal` reassembles the stored `Match` from. The scrutinee's own `env`
            // is deliberately not threaded (the branch envs extend `outer_env`), as it
            // was not before.
            let (scr_ty, mut scr_effects, scr_node) = match scr_r {
                Ok(TypeResult {
                    ty, effects, node, ..
                }) => (ty, effects, node),
                Err(e) => {
                    results.push(Err(e));
                    return;
                }
            };

            // Coverage / exhaustiveness inputs are derived purely from
            // pattern terms, independent of body type-checks — compute
            // here so MatchFinal can run the check without re-walking.
            let mut covered_entities: Vec<Symbol> = Vec::new();
            let mut has_wildcard = false;
            // WI-803: relabelled branch patterns, in branch order.
            let mut branch_patterns: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(branches.len());
            // WI-20260827-EJ5F5: each arm's body and guard with references to the binders
            // the constructor rewrite REMOVED re-pointed at those constructors
            // ([`repoint_arm_binders`]). Both must be carried, and for the same reason
            // twice over: the body is what `push_visit` type-checks below, and the guard
            // is what `reassemble_match` puts back into the stored tree — a guard checked
            // in one spelling and stored in another would pass the load and then read an
            // unbound name at eval. Same `Rc` as the written one on every arm that
            // rewrote nothing, which is every arm in the corpus today.
            let mut branch_bodies: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(branches.len());
            let mut branch_guards: Vec<Option<Rc<NodeOccurrence>>> =
                Vec::with_capacity(branches.len());
            // Constructors of the scrutinee sort. A bare `case red` parses as a
            // var_pattern (the name could be a binding or a nullary
            // constructor); recognizing it as a constructor needs the
            // candidate set. The scrutinee sort's own constructors are that
            // set — resolving against them replaces the removed global
            // short→qualified fallback the late lookup relied on.
            // WI-374: read the BASE sort through `sort_functor_of_view`, not
            // `extract_sort_ref_sym` — a parameterized scrutinee type
            // (`Option[T = Int64]`, now also produced by the let-annotation
            // rewrite) must resolve its constructor set exactly like a bare
            // one; the bare-ref-only read silently skipped it.
            let scrutinee_ctors: Vec<Symbol> = sort_functor_of_view(kb, &scr_ty)
                .map(|s| sort_constructor_syms(kb, s))
                .unwrap_or_default();
            let mut branch_envs: Vec<Env> = Vec::with_capacity(branches.len());
            // WI-537: the arm guard's effects (merged into the match's effects)
            // and the first guard type-error (short-circuits the match).
            let mut guard_effects: Vec<Value> = Vec::new();
            let mut guard_error: Option<TypeError> = None;
            // WI-794: the first arm-pattern binder whose written annotation contradicts
            // the scrutinee component it destructures (`case (a: String, b) -> …` over an
            // `(Int64, Int64)` scrutinee). Short-circuits the match exactly as
            // `guard_error` does, and is reported AHEAD of it: the binder types feed the
            // guard, so a contradicting annotation is the root cause of anything the
            // guard would go on to report.
            let mut binder_error: Option<TypeError> = None;
            // WI-20260827-EJ5F5 — TWO PASSES, and the split is the point. EVERY reader of
            // an arm pattern must read the one the rewrite produced, not the one the
            // author wrote, or the resolution has two answers again. Coverage and the Γ
            // facts used to run off `branch.pattern` while the matcher ran off the
            // rewritten one, and the disagreement showed exactly where the rewrite is
            // deepest: `case some(red)` stored `some(red())` yet emitted
            // `eq(s, some(var_ref(red)))` — a `var_ref` at a binder that no longer
            // exists — and gave later arms no `neq` although the arm had become ground.
            // Reading the rewritten pattern also means nothing here has to re-derive the
            // NESTED candidate set: `bind_and_label_pattern` already threaded each
            // position's type (through the scrutinee's substitution, which a second
            // derivation would have had to duplicate), and a rewritten sub-pattern is a
            // plain `Pattern::Constructor` every reader already handles.
            //
            // PASS 1 — rewrite each arm's pattern, extend its env, and re-point its body
            // and guard. Nothing here reads another arm.
            let mut branch_env_types: Vec<TypingEnv> = Vec::with_capacity(branches.len());
            for branch in branches.iter() {
                let mut branch_env = (*outer_env).clone();
                let mut branch_binder_errors = Vec::new();
                // The ONE refutable position — a bare name naming one of the scrutinee's
                // own nullary constructors is rewritten to that constructor here, which
                // is what makes the arm actually match it at run time and what lets
                // `folded_call_match` see disjoint arms.
                let mut repointed: Vec<(Symbol, Symbol)> = Vec::new();
                let pattern = bind_and_label_pattern(
                    kb,
                    &mut branch_env,
                    &branch.pattern,
                    Some(scr_ty.clone()),
                    PatternRole::MatchArm,
                    &mut repointed,
                    // WI-20260904-50B2K: the seed. The scrutinee type is always present
                    // here, so the tuple arm answers from it and this is never read.
                    UnpinnedBinder::Unnameable,
                    &mut branch_binder_errors,
                );
                // WI-511: coverage reads the Pattern occurrence directly — no
                // `pattern_to_term` bridge. WI-20260827-EJ5F5: and it reads the REWRITTEN
                // one, so a resolved bare name reaches the `Constructor` arm rather than
                // being resolved a second time here.
                // WI-20260907-0QV5A: a GUARDED arm covers NOTHING — neither its
                // constructor nor, for a binder, the whole scrutinee. Its guard decides
                // at RUN TIME whether the arm is entered, so counting its pattern here
                // would let `case red | g -> …  case green -> …` pass exhaustiveness and
                // then raise `MatchFailed` on a `red` whose guard was false. The count
                // was RIGHT until that ticket — eval entered a guarded arm
                // unconditionally, so a guarded arm really did cover — and this is the
                // load-time twin of `eval/eval.rs::scan_match_arms`' fallthrough into
                // `raise_match_failed`. Same reading a written `: T` annotation already
                // gets (spec §"Nullary only, and at every depth": an annotated arm covers
                // nothing), for the same reason: what runs decides what covers.
                if branch.guard.is_none() {
                    collect_covered_entities(
                        kb,
                        &pattern,
                        &scrutinee_ctors,
                        &mut covered_entities,
                        &mut has_wildcard,
                    );
                }
                branch_patterns.push(pattern);
                // The rewrite removed those binders, so the arm's own text has to stop
                // naming them. Done HERE, before the guard is checked and before the body
                // is pushed, so both are checked in the form they will be STORED in.
                branch_bodies.push(repoint_arm_binders(&branch.body, &repointed));
                branch_guards.push(
                    branch
                        .guard
                        .as_ref()
                        .map(|g| repoint_arm_binders(g, &repointed)),
                );
                if binder_error.is_none() {
                    binder_error = branch_binder_errors.into_iter().next();
                }
                branch_env_types.push(branch_env);
            }
            // WI-537 / proposal 050 `match` rule: the per-arm pattern fact +
            // earlier-arm negations. Computed once over all arms (negations
            // accumulate across earlier arms) — which is why it cannot live inside
            // pass 1; the scrutinee value is the scrutinee occurrence, exactly as the
            // `if`-fork uses its condition.
            let scrutinee_value = Value::Node(Rc::clone(&scr_node));
            let arm_inputs: Vec<(Rc<NodeOccurrence>, bool)> = branch_patterns
                .iter()
                .zip(branches.iter())
                .map(|(p, b)| (Rc::clone(p), b.guard.is_some()))
                .collect();
            let arm_facts =
                match_arm_gamma_facts(kb, &scrutinee_value, &arm_inputs, &scrutinee_ctors);
            // PASS 2 — the per-arm Γ and its guard, both of which need pass 1 finished.
            for ((branch_env, branch_guard), facts) in branch_env_types
                .into_iter()
                .zip(branch_guards.iter())
                .zip(arm_facts.into_iter())
            {
                // Arm Γ = the outer Γ + this arm's pattern fact + earlier-arm
                // negations (+ the guard predicate below). `assume` is a set, so
                // a fact `view_is_indexable` rejects (an `Opaque`-headed
                // scrutinee/value) is dropped losslessly.
                let mut arm_flow = outer_env.flow.clone();
                for fact in facts {
                    arm_flow = arm_flow.assume(kb, fact);
                }
                // WI-537: type-check the arm guard (it was dropped at parse→IR
                // before WI-537, so never visited) under the arm's type env — pattern
                // vars are in scope — and narrow the arm Γ with the guard
                // predicate. No `Bool` hint (matching how `if` treats its
                // condition); the visit catches real errors in the guard.
                // WI-20260829-1SSXM: the `scr_ty.is_some()` half of this gate is GONE
                // with the swallow — it skipped the guard visit when the scrutinee
                // didn't type, to keep pattern vars typed as nothing from producing
                // cascading noise. That case no longer reaches here at all: the frame
                // returns the scrutinee's own `Err` above.
                if let Some(g) = branch_guard {
                    if guard_error.is_none() {
                        // WI-657(9): reuse the gate build_type already holds.
                        // WI-K88TN: under `arm_flow`, NOT an empty Γ. The arm's Γ is
                        // the outer one (which carries the enclosing operation's own
                        // preconditions) plus this arm's pattern facts; the guard
                        // predicate itself is assumed only AFTER this check, since a
                        // guard may not discharge itself.
                        match type_check_node_gated_in_gamma(
                            kb,
                            &branch_env,
                            g,
                            None,
                            simp_enabled,
                            simp_rids,
                            arm_flow.clone(),
                        ) {
                            Ok(r) => {
                                merge_effects_into(kb, &mut guard_effects, &r.effects);
                                // WI-20260824-Q0093: and its DESTINATION — the `if`
                                // condition's twin, through the one predicate. The
                                // comment above ("No `Bool` hint") is still true and is
                                // still not a check; this is the check.
                                guard_error = boolean_position_error(
                                    kb,
                                    &r.ty,
                                    Some(g),
                                    Some(g.span.span),
                                    "match",
                                    "guard",
                                );
                            }
                            Err(e) => guard_error = Some(e),
                        }
                    }
                    arm_flow = arm_flow.assume(kb, Value::Node(Rc::clone(g)));
                }
                branch_envs.push(Env {
                    types: Rc::new(branch_env),
                    flow: arm_flow,
                });
            }
            // A guard that doesn't type-check fails the whole match (the
            // scrutinee result was already popped, so one Err is the match's
            // single result — no MatchFinal / body visits).
            if let Some(e) = binder_error {
                results.push(Err(e));
                return;
            }
            if let Some(e) = guard_error {
                results.push(Err(e));
                return;
            }
            // WI-657(8): fold the guard effects into the owned scrutinee row in place.
            merge_effects_into(kb, &mut scr_effects, &guard_effects);

            let branch_count = branches.len();
            // Materialize Visit envs first (clone from branch_envs),
            // then move branch_envs into the MatchFinal frame.
            let visit_envs: Vec<Env> = branch_envs.iter().cloned().collect();
            work.push(TypeWorkOp::Build(TypeBuildFrame::MatchFinal {
                occ,
                scr_node,
                scr_effects,
                branch_envs,
                branch_count,
                outer_env,
                scr_ty,
                covered_entities,
                has_wildcard,
                branch_patterns,
                branch_guards,
                body_expected: body_expected.clone(),
            }));
            for (body, env) in branch_bodies.iter().zip(visit_envs.into_iter()).rev() {
                push_visit(work, Rc::clone(body), env, body_expected.clone(), fuel);
            }
        }
        TypeBuildFrame::MatchFinal {
            occ,
            scr_node,
            scr_effects,
            branch_envs,
            branch_count,
            outer_env,
            scr_ty,
            covered_entities,
            has_wildcard,
            branch_patterns,
            branch_guards,
            body_expected,
        } => {
            let drain_start = results.len() - branch_count;
            let branch_results: Vec<Result<TypeResult, TypeError>> =
                results.drain(drain_start..).collect();
            if let Err(e) = collect_arg_errors(branch_results.iter()) {
                results.push(Err(e));
                return;
            }
            // WI-283: reassemble the `Match` from the (rewritten) scrutinee
            // and branch bodies (guards re-read from `occ`, unchanged) before
            // `branch_results` is consumed below.
            let node = reassemble_match(
                &occ,
                &scr_node,
                &branch_patterns,
                &branch_guards,
                &branch_results,
            );
            let mut effects = scr_effects;
            // WI-342: branch types are carrier-agnostic `Value`s — a branch may be
            // a `Value::Node` lambda arrow; the join carries it (no re-grounding).
            let mut branch_tys: Vec<(Value, Option<Span>, Option<Rc<NodeOccurrence>>)> =
                Vec::with_capacity(branch_count);
            for (i, body_r) in branch_results.into_iter().enumerate() {
                let body_r = body_r.expect("aggregator");
                branch_tys.push((
                    body_r.ty.clone(),
                    Some(body_r.node.span.span),
                    Some(Rc::clone(&body_r.node)),
                ));
                // Filter effects against this branch's locals so
                // pattern-bound resources don't leak past the case
                // arm (their bindings live only inside the branch).
                let branch_external = external_effects(kb, &*branch_envs[i], &body_r.effects);
                merge_effects_into(kb, &mut effects, &branch_external);
            }

            // WI-287: the match's result type accounts for *every* branch,
            // not just branch 0. In checked mode (an expected type flowed
            // in) each branch must conform to it; in synthesis mode the
            // result is the join (a common supertype) of the branch types,
            // and branches with no common supertype are a type error rather
            // than being silently typed as branch 0.
            let result_ty: Value =
                match compute_branch_join_type(kb, &branch_tys, body_expected, "match") {
                    Ok(ty) => ty,
                    Err(e) => {
                        results.push(Err(e));
                        return;
                    }
                };

            let mut result_env = (*outer_env).clone();
            if !has_wildcard {
                // WI-374: base sort via `sort_functor_of_view` so a
                // PARAMETERIZED scrutinee keeps its exhaustiveness check
                // (the bare-ref-only read silently skipped it).
                if let Some(sort_sym) = sort_functor_of_view(kb, &scr_ty) {
                    if kb.sort_kind(sort_sym) == Some(SortKind::Enum) {
                        let all_entities = sort_constructor_syms(kb, sort_sym);
                        let missing: Vec<String> = all_entities
                            .iter()
                            .filter(|e| {
                                // WI-672: `covered_entities` are now resolved scrutinee
                                // ctors (via `pattern_var_ctor_sym` / `resolve_pattern_ctor`),
                                // so compare by canonical identity, not `same_symbol`.
                                !covered_entities
                                    .iter()
                                    .any(|c| same_sort_canonical(kb, *c, **e))
                            })
                            .map(|s| kb.local_name_of(*s).to_string())
                            .collect();
                        if !missing.is_empty() {
                            let sort_name = kb.local_name_of(sort_sym);
                            result_env.diagnostics.push(format!(
                                "non-exhaustive match on {}: missing {}",
                                sort_name,
                                missing.join(", ")
                            ));
                        }
                    }
                }
            }
            results.push(Ok(TypeResult {
                ty: result_ty,
                env: result_env,
                effects,
                node,
            }));
        }
        TypeBuildFrame::LambdaBody {
            occ,
            param_type,
            outer_env,
            binder_error,
            param,
        } => {
            let body_r = results.pop().expect("LambdaBody: missing body result");
            // WI-794: a contradicting binder annotation is reported ahead of any body
            // error. The body was typed with the binder bound to the CONTEXT type, so
            // when both fire the body's complaint is a CONSEQUENCE of the false
            // annotation (WI-517's `needs_str(a)` fixture is exactly this shape) —
            // reporting the annotation points at the line the user has to change. The
            // body result is popped first either way, keeping the stack balanced.
            if let Some(e) = binder_error {
                results.push(Err(e));
                return;
            }
            // Build arrow(param, result, effects) type term. `param_type`
            // is the exact type the param was bound to in the body env
            // (see the `Expr::Lambda` visit case), so the arrow's param
            // slot and the body's view of the param agree.
            let body_ty: Value = body_r
                .as_ref()
                .ok()
                .map(|r| r.ty.clone())
                .unwrap_or_else(|| {
                    let fresh = kb.intern("?result");
                    Value::term(kb.make_type_var(fresh))
                });
            let body_effects = body_r
                .as_ref()
                .ok()
                .map(|r| r.effects.clone())
                .unwrap_or_default();
            // WI-470: the lambda's arrow type is minted as an occurrence
            // (`Value::Node`, occurrence-primary). A denoted-bearing child (a
            // `Modify[c]` body effect) is CARRIED as a poisoned child rather than
            // re-grounded; a ground child rides as `TypeChild::Interned`. The
            // op-boundary return check compares it cross-carrier via `TermView`.
            // WI-791: the lambda's arity is its WRITTEN binder count, read from the
            // param pattern — `param_type` cannot supply it (an unannotated lambda's
            // is a fresh type var, and a tuple-typed one is indistinguishable from a
            // binder list). See `lambda_written_arity`.
            let arity = lambda_written_arity(&occ);
            // WI-20260904-50B2K part (c) — THE ARROW REFLECTS WHAT THE BODY SOLVED.
            //
            // `param_type` is the value minted at VISIT time, before the body ran, so an
            // un-annotated binder's arrow said `?param` however thoroughly the body had
            // pinned it — and `TypeResult` carries no substitution to correct it with.
            // The body's calls DO solve it (measured: `let f = lambda v -> twice(v)` binds
            // `?param` to `Int64` inside `twice`'s own σ); `body_solutions` is where that
            // now lands, and this is the first reader of it.
            //
            // `resolve_type_deep_value` replaces exactly the variables this walk has
            // solved and leaves every other one alone. THAT IS NOT ITSELF A SCOPING RULE,
            // and the first cut treated it as one — "a callee's variable is not IN
            // `param_type`" constrains the σ's DOMAIN and says nothing about its RANGE, so
            // a binding `?param := ?T_callee` substituted a callee variable straight into
            // the arrow. The gate lives on the WRITING side now
            // ([`report_call_solutions`]); this read is a plain resolution again.
            //
            // A BINDER THE BODY DID NOT PIN IS UNCHANGED, which is the case part (c)'s
            // generalization is for — it stays a variable here and has no ∀ to live in
            // yet.
            // BOTH HALVES, AND THE EFFECTS — resolving only the domain SPLITS a variable
            // occurring in both, and the split is a WRONG ACCEPT rather than a lost
            // refusal. /code-review drove it: `lambda v -> (a: twice(v), b: v)` against a
            // declared `B = (a: Int64, b: String)` LOADED, because once the domain was
            // `Int64` the codomain's still-raw `??param` no longer conflicted and the
            // op-return's declaration-solve bound it to `String`. This is the invariant
            // the frame's own comment above states ("the arrow's param slot and the body's
            // view of the param agree"); Path 1's rule is the precedent — resolve the
            // return type AND the effect row, "or one call reports two states of one σ".
            let param_type = resolve_type_deep_value(kb, &solving.solved, &param_type);
            let body_ty = resolve_type_deep_value(kb, &solving.solved, &body_ty);
            let body_effects: Vec<Value> = body_effects
                .into_iter()
                .map(|e| resolve_type_deep_value(kb, &solving.solved, &e))
                .collect();
            let fn_ty = make_arrow_value(
                kb,
                &param_type,
                &body_ty,
                &body_effects,
                arity,
                occ.span,
                occ.owner,
            );
            // WI-20260904-50B2K part (c) — GENERALIZATION IS NOT HERE, AND THE FIRST CUT
            // PUT IT HERE. Quantifying at every LAMBDA gives a ∀ to a lambda written
            // DIRECTLY in an argument slot, where no reader eliminates it: measured,
            // `addI(a: lambda x -> x + x, b: 1)` against `addI(a: Int64, b: Int64)` LOADED —
            // a function value in an `Int64` slot — while its requirement-free twin
            // `lambda x -> x` was correctly refused, which is what isolates the ∀ as the
            // cause. `validate_arg_against_param` has no arm for a `PolyType` and
            // `type_head_is_callable` answers `false` for one, so nothing objected.
            //
            // THE STANDARD RULE GENERALIZES AT THE `let`, NOT AT THE LAMBDA, and moving it
            // there fixes this BY CONSTRUCTION rather than by teaching every consumer to
            // eliminate: a lambda in an argument position simply keeps its arrow and is
            // checked as one. See `WalkSolutions::generalize_at_binding`, now the only
            // producer — which also makes the wrong-frame capture defect (review finding 20)
            // structurally impossible, since there is one frame. /code-review found it.
            // Creating a lambda is itself pure — body effects live in the type.
            // If the body itself errored, propagate that error rather than
            // synthesizing a lambda over an ill-typed body.
            match body_r {
                // WI-283: reassemble the lambda from its [param, body]
                // (WI-318 added param) so a `@[simp]` rewrite in either
                // propagates up. WI-803: the param is NO LONGER passed through
                // unchanged — the frame carries the relabelled one, and a lambda
                // rebuilt from `occ`'s written param would drop the labels and
                // silently destructure by slot again.
                Ok(ref r) => {
                    let node = crate::kb::simp_rewrite::reassemble(
                        &occ,
                        &[Rc::clone(&param), Rc::clone(&r.node)],
                    );
                    results.push(Ok(TypeResult {
                        ty: fn_ty,
                        env: unwrap_env(outer_env),
                        effects: Vec::new(),
                        node,
                    }))
                }
                Err(e) => results.push(Err(e)),
            }
        }
        TypeBuildFrame::IfExpr { occ, env, expected } => {
            // Children drained in [condition, then, else] order.
            let drain_start = results.len() - 3;
            let group: Vec<Result<TypeResult, TypeError>> = results.drain(drain_start..).collect();
            if let Err(e) = collect_arg_errors(group.iter()) {
                results.push(Err(e));
                return;
            }
            // WI-283: reassemble from [cond, then, else] (before consuming
            // `group`) so a `@[simp]` rewrite inside a branch propagates up.
            let node = reassemble_group(&occ, &group);
            let mut it = group.into_iter().map(|r| r.expect("aggregator"));
            let cond_r = it.next().unwrap();
            let then_r = it.next().unwrap();
            let else_r = it.next().unwrap();
            // WI-20260824-Q0093: the condition's DESTINATION, which nothing checked — see
            // [`boolean_position_error`] for what that admitted and for the control that
            // says it was never a type-value question. Reported ahead of the branch join,
            // which would otherwise answer about the arms while the condition is the thing
            // that is wrong.
            if let Some(e) = boolean_position_error(
                kb,
                &cond_r.ty,
                Some(&cond_r.node),
                Some(cond_r.node.span.span),
                "if",
                "condition",
            ) {
                results.push(Err(e));
                return;
            }
            let mut effects = Vec::new();
            merge_effects_into(kb, &mut effects, &cond_r.effects);
            merge_effects_into(kb, &mut effects, &then_r.effects);
            merge_effects_into(kb, &mut effects, &else_r.effects);
            // WI-287: the if's type is the join of both branches (checked
            // against `expected` when present), not just the then-branch
            // type — an `if` with incompatible arms is otherwise silently
            // typed as its then-branch.
            // WI-342: branch types are carrier-agnostic `Value`s (a branch may be
            // a `Value::Node` lambda arrow); the join carries it (no re-grounding).
            let branch_tys = [
                (
                    then_r.ty.clone(),
                    Some(then_r.node.span.span),
                    Some(Rc::clone(&then_r.node)),
                ),
                (
                    else_r.ty.clone(),
                    Some(else_r.node.span.span),
                    Some(Rc::clone(&else_r.node)),
                ),
            ];
            let ty: Value = match compute_branch_join_type(kb, &branch_tys, expected, "if") {
                Ok(ty) => ty,
                Err(e) => {
                    results.push(Err(e));
                    return;
                }
            };
            results.push(Ok(TypeResult {
                ty,
                env: unwrap_types(env),
                effects,
                node,
            }));
        }
        TypeBuildFrame::ProofStmt {
            occ,
            env,
            has_conclude,
        } => {
            // WI-538: children drained in [conclude?, body] order.
            let n = if has_conclude { 2 } else { 1 };
            let drain_start = results.len() - n;
            let group: Vec<Result<TypeResult, TypeError>> = results.drain(drain_start..).collect();
            if let Err(e) = collect_arg_errors(group.iter()) {
                results.push(Err(e));
                return;
            }
            // WI-283: reassemble so a `@[simp]` rewrite inside the goal or
            // body propagates up.
            let node = reassemble_group(&occ, &group);
            let mut it = group.into_iter().map(|r| r.expect("aggregator"));
            let (conclude_r, body_r) = if has_conclude {
                let c = it.next().unwrap();
                let b = it.next().unwrap();
                (Some(c), b)
            } else {
                (None, it.next().unwrap())
            };
            let mut effects = Vec::new();
            if let Some(cr) = &conclude_r {
                merge_effects_into(kb, &mut effects, &cr.effects);
            }
            merge_effects_into(kb, &mut effects, &body_r.effects);
            // The proof is transparent to types: its type is the
            // continuation's.
            let ty = body_r.ty.clone();
            results.push(Ok(TypeResult {
                ty,
                env: unwrap_types(env),
                effects,
                node,
            }));
        }
        TypeBuildFrame::ListLit {
            occ,
            env,
            element_hint,
            count,
        } => {
            let drain_start = results.len() - count;
            let group: Vec<Result<TypeResult, TypeError>> = results.drain(drain_start..).collect();
            if let Err(e) = collect_arg_errors(group.iter()) {
                results.push(Err(e));
                return;
            }
            // WI-283: reassemble from the (possibly-rewritten) elements.
            let node = reassemble_group(&occ, &group);
            let (span, owner) = (occ.span, occ.owner);
            // WI-20260826-7JDWY: the element type, and the CHECK of the elements against a
            // hint, are [`seq_literal_element_type`] — shared with the `SetLit` frame and
            // with the constructor carrier a source `[…]` actually arrives on.
            let (t_val, effects) =
                match seq_literal_element_type(kb, SeqLiteral::List, element_hint, &group) {
                    Ok(v) => v,
                    Err(e) => {
                        results.push(Err(e));
                        return;
                    }
                };
            let list_type = seq_literal_type(kb, SeqLiteral::List, t_val, span, owner);
            results.push(Ok(TypeResult {
                ty: list_type,
                env: unwrap_types(env),
                effects,
                node,
            }));
        }
        TypeBuildFrame::SetLit {
            occ,
            env,
            element_hint,
            count,
        } => {
            let drain_start = results.len() - count;
            let group: Vec<Result<TypeResult, TypeError>> = results.drain(drain_start..).collect();
            if let Err(e) = collect_arg_errors(group.iter()) {
                results.push(Err(e));
                return;
            }
            // WI-283: reassemble from the (possibly-rewritten) elements.
            let node = reassemble_group(&occ, &group);
            let (span, owner) = (occ.span, occ.owner);
            // WI-20260826-7JDWY: as the `ListLit` frame above — one owner for both surfaces.
            let (t_val, effects) =
                match seq_literal_element_type(kb, SeqLiteral::Set, element_hint, &group) {
                    Ok(v) => v,
                    Err(e) => {
                        results.push(Err(e));
                        return;
                    }
                };
            let set_type = seq_literal_type(kb, SeqLiteral::Set, t_val, span, owner);
            results.push(Ok(TypeResult {
                ty: set_type,
                env: unwrap_types(env),
                effects,
                node,
            }));
        }
        TypeBuildFrame::TupleLit {
            occ,
            env,
            pos_count,
            named_names,
        } => {
            let total = pos_count + named_names.len();
            let drain_start = results.len() - total;
            let group: Vec<Result<TypeResult, TypeError>> = results.drain(drain_start..).collect();
            if let Err(e) = collect_arg_errors(group.iter()) {
                results.push(Err(e));
                return;
            }
            // WI-283: reassemble from [positional…, named…] elements.
            let node = reassemble_group(&occ, &group);
            let (span, owner) = (occ.span, occ.owner);
            let mut effects = Vec::new();
            // WI-342: keep field types carrier-agnostic so a `Value::Node` field
            // (a tuple element that is an effectful lambda) is CARRIED, not re-grounded.
            let mut field_types: Vec<(Symbol, Value)> = Vec::new();
            let mut it = group.into_iter();
            for i in 0..pos_count {
                let r = it.next().unwrap().expect("aggregator");
                // WI-355: positional field names are 1-based `_1`, `_2`, … (spec
                // §4.5), matching the type surface (`convert.rs`) and arrow params.
                // WI-788: that match is what lets a POSITIONAL literal's type relate
                // to a positional tuple type or a multi-param arrow — slot by slot
                // with the names agreeing, `_N` to `_N`. It no longer bridges to a
                // NAMED param (`_1` does not relate to `a`), which is deliberate:
                // proposal 004 rule 4 makes those different types. Eval/patterns
                // treat `_N` positionally, so the base is invisible to them.
                let field_name = kb.intern(&positional_label(i));
                field_types.push((field_name, r.ty.clone()));
                merge_effects_into(kb, &mut effects, &r.effects);
            }
            for name in named_names {
                let r = it.next().unwrap().expect("aggregator");
                field_types.push((name, r.ty.clone()));
                merge_effects_into(kb, &mut effects, &r.effects);
            }
            let tuple_type = named_tuple_value(kb, &field_types, span, owner);
            results.push(Ok(TypeResult {
                ty: tuple_type,
                env: unwrap_types(env),
                effects,
                node,
            }));
        }
    }
}

/// Attach a call-site `CallClass` to its NodeOccurrence's `RefCell`
/// — the canonical channel for downstream consumers post-WI-251.
/// `req_insertion::run` walks `kb.op_bodies` and reads the
/// classification off each Apply NodeOccurrence; eval reads it
/// directly from the same RefCell at dispatch time.
pub(super) fn classify(_kb: &mut KnowledgeBase, occ: &Rc<NodeOccurrence>, class: CallClass) {
    occ.set_classification(class);
}

/// Tag a concrete-dispatch call site: `ConcreteApplyWithin` when the impl's own
/// sort declares `requires` (its dict must thread at eval), else a plain `PinNow`.
/// The shared tail of every concrete spec-op dispatch arm — the carrier-override
/// (WI-444), HK instance-fact (WI-453), unqualified-concrete-carrier (WI-606), and
/// `Unique` arms — which differ only in the impl symbol and whether a `resolved_-
/// tree` was resolved (`None` except on the `Unique` arm). `dispatch_dict` is
/// `None` for a SAME-SORT call (the callee inherits the caller's frame
/// requirements at eval) and for a `resolved_tree`-less arm; WI-829 sets it for a
/// CROSS-SORT call that CONSTRUCTS a dictionary (the resolved tree emitted AS the
/// dict via `emit_tree_as_projection`, since eval threads `dispatch_dict`, not the
/// diagnostic-only `resolved_tree`). The WI-415 compile-built dict is the
/// Direct-call (non-spec-op) dual.
pub(crate) fn classify_pin_or_apply_within(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    fn_sym: Symbol,
    impl_op: Symbol,
    enclosing_sort: Option<Symbol>,
    resolved_tree: Option<ResolvedRequiresNode>,
    // WI-822 LEG 1: the call-site context the OP-SCOPED half of the callee's frame is
    // built from — the per-call substitution that pins its elements, the caller's own
    // chain a forward reads, its rigids, and the call's selections. `None` at the
    // arms that have no substitution in hand; those supply no op slots, so a callee
    // that reads one raises at the read rather than being handed a wrong dictionary.
    op_supply: Option<&OpSupplyCtx<'_>>,
    // WI-1091: `Err` for the ONE absence in the op half that is a verdict rather than a
    // gap — a TIE, which no other pass will ever report (058 tier 3 admits the pair on
    // purpose). Every other unprojectable slot still classifies with the slot absent.
) -> Result<(), TypeError> {
    let impl_sort = impl_parent_of_op(kb, impl_op);
    let needs_reqs = impl_sort.is_some() && op_reads_requirement_slots(kb, impl_op);
    // WI-822 LEG 1: an operation whose OWN `requires` names slots needs the
    // requirements channel too, even when its sort declares none — that is the
    // `Holder.probe requires Zeroable[HT]` shape, which used to be `PinNow` and
    // therefore had no channel at all.
    // WI-20260921-28TAT: STAMPED, not folded into the class below. This build used to
    // feed `ConcreteApplyWithin`'s `op_dicts` field and was DISCARDED on the `PinNow`
    // arm; the stamp is read on every apply route, so a pinned callee with an op-scoped
    // clause now gets its evidence too.
    if let Some(ctx) = op_supply {
        stamp_op_scoped_dicts(
            kb,
            occ,
            ctx.subst,
            impl_op,
            ctx.caller_requires,
            ctx.param_rigids,
            ctx.selected,
            OpSlotParkSite::for_call(
                kb,
                impl_op,
                ctx.enclosing_op,
                Some(occ.span.span),
                occ.span.source,
            ),
            ctx.param_arg_types,
            ctx.held,
            Some(occ.span.span),
            false,
        )?;
    }
    // WI-822 LEG 1: … but only where there IS a parent to name as the callee's
    // `callee_spec_sort`. `needs_reqs` implied `impl_sort.is_some()`; `has_op_slots` is
    // read off the operation alone and does not, so an operation with no resolvable
    // parent and a `requires` of its own would have panicked the `unwrap` below.
    let has_op_slots = impl_sort.is_some() && !op_requires_chain_rc(kb, impl_op).is_empty();
    // WI-20260921-R10KC — …OR THE TREE PINS A PROVIDER THE CALLEE'S OWN PARENT IS NOT,
    // which is the case the two tests above cannot see: the dictionary is then the
    // callee's DISPATCH ENVIRONMENT rather than a source of its own named slots, and a
    // callee that reads no slot of its own still resolves a body-less SIBLING out of it
    // (`Dictionary.resolveOp` — `dispatch_via_sort_ops_table` plus
    // [`Interpreter::expand_dispatching_dict`] in eval).
    //
    // THE SHAPE, and it is why the two tests above are blind to it: a spec that declares
    // NO `requires` of its own, whose DEFAULT BODY calls a body-less member. `needs_reqs`
    // counts only [`op_owner_dict_entries`] — the SPEC half — so it is 0, the class was
    // `PinNow`, and the instance the defaulted fall-through arm had just resolved
    // (`Dictionary(<the carrier's own requires>, impl: carrier)`, whose PROVIDER half
    // `dict_layout` reserves) was dropped on this line. The body then reached the
    // carrier's member by VALUE, and a value carries its sort and none of its type
    // parameters — so a named requirement slot chosen at construction could not be
    // recovered and the dispatch was refused. Both routes find the same implementation;
    // only this one brings the evidence.
    //
    // GATED BY [`dictionary_covers_target`] — ASKED OF THE OP EVAL WILL ENTER, which is
    // not `impl_op`. A first cut asked it of `impl_op` with `spec := impl_parent_of_op(
    // impl_op)`, and /code-review showed that is a TAUTOLOGY: that function's own first
    // line is `impl_parent_of_op(target)`, so `owner == spec` and `slots_for` always takes
    // the self branch; and its `names.is_empty()` early return is the very reader
    // `needs_reqs` already consulted, so it could only ever answer `true` on the branch
    // where this disjunct decides anything. The guard described below did not exist.
    //
    // WHAT IT GUARDS, now that it does: eval resolves the dictionary's OWN member for this
    // op (`dispatch_via_sort_ops_table` → `resolve_op_target(provider, fn_sym)`), and that
    // can land on a THIRD sort — `FiniteCollection.filter` at a carrier that INHERITS
    // `filter` from `Iterable`. A dictionary laid out for `(spec, provider)` carries
    // nothing for such an owner, so handing it one is `expand_dispatching_dict`'s WI-857
    // raise deferred to run time. Such a call keeps the `PinNow` it has today.
    //
    // THE SPEC IS THE DISPATCHED ONE, not the callee's parent — `dispatch_spec_of_op`'s
    // collapse, so this reader and `expand_dispatching_dict`'s agree about the layout
    // (WI-866 gave that question one owner precisely so two readers could not drift).
    //
    // THIS ALSO NARROWS THE BLAST RADIUS, which the tautology did not: `threads_instance`
    // is reached at every arm that resolves a tree, including WI-1093's supplier-pinned
    // one, whose own doc records that the `impl_op`/tree pairing is UNGUARDED and
    // "examined and NOT driven". Where the two diverge the layout no longer covers the
    // resolved member, so the promotion declines instead of selecting on the divergence.
    //
    // AND NOT WHERE THE CALLEE WOULD INHERIT ANYWAY. `dispatch_dict` is `None` on the
    // same-sort arm below, so promoting there would NOT thread the instance — it would
    // hand the callee the CALLER's frame, which is the unguarded frame inheritance WI-456
    // backed out, reached by a class promotion instead of a frame read. The promotion
    // fails its own purpose there, so it declines: `PinNow` is what such a call has today.
    // Read with `same_sort_canonical`, unlike the `inherits` test below, because two
    // interned copies of one sort are one sort for this question (WI-864).
    let threads_instance = impl_sort.is_some_and(|parent| {
        if enclosing_sort.is_some_and(|encl| same_sort_canonical(kb, parent, encl)) {
            return false;
        }
        resolved_tree.as_ref().is_some_and(|tree| {
            tree.impl_sort().is_some_and(|provider| {
                if same_sort_canonical(kb, provider, parent) {
                    return false;
                }
                let spec = dispatch_spec_of_op(kb, fn_sym).or_provider(provider);
                let entered = resolve_op_target(kb, provider, impl_op);
                dictionary_covers_target(kb, spec, provider, entered)
            })
        })
    });
    let class = if needs_reqs || has_op_slots || threads_instance {
        // WI-829: a CROSS-SORT spec-op dispatch that CONSTRUCTS its callee's
        // requirement dictionary (a `resolved_tree` with a `FromScope` — the
        // deeper dict built around the enclosing frame's own requirement) cannot
        // be threaded at eval by same-sort inheritance (the callee's parent is
        // not the enclosing sort). The eval `ConcreteApplyWithin` path installs a
        // `dispatch_dict` TermId, not the `resolved_tree` (diagnostic-only), so
        // emit the tree AS that dict here — the same `emit_tree_as_projection`
        // req-insertion uses; its `FromScope` `var_ref(__req_*)` reads the
        // enclosing frame at eval. A same-sort call keeps `None` (eval inherits
        // the caller's frame requirements). `None` on `emit`/no-tree preserves
        // the pre-WI-829 behaviour (inherit or the WI-415 Direct-call dict).
        // Proposal 066 §7.4: a SAME-sort callee inherits the caller's frame only where
        // that frame serves it; a member of a provision the caller is not in holds
        // conditions the caller's frame does not, and gets its dictionary here.
        let inherits = impl_sort == enclosing_sort
            && op_supply.is_none_or(|ctx| {
                let key = callee_frame_key(kb, impl_op);
                frame_serves_callee(ctx.caller_requires, key)
            });
        let dispatch_dict = match &resolved_tree {
            Some(tree) if !inherits => {
                // WI-1033: the enclosing sort's DICTIONARY chain, which is the list
                // this tree's `FromScope` indices point into.
                // WI-822 LEG 1: the sort's chain is the PREFIX the resolution was
                // seeded from (`enclosing_requires()`), and WI-20260918-CKD4J adds the
                // op half past it — a conditional provision's SUB-goal answered by the
                // operation's own `requires` is `FromScope` at `sort_len + j`. So the
                // tree is named off the FRAME chain the call site hands in, whose
                // prefix is that same sort chain (`TypingEnv::sub_goal_requires`
                // asserts it). With no supply context the resolution had no op half
                // either, and the sort chain is exact.
                let caller = match op_supply {
                    Some(ctx) => ctx.caller_requires.clone(),
                    // Proposal 066 §7: the sort-level chain — the one prefix every
                    // chain of the sort shares, so a name read off it is right whatever
                    // provision the body belongs to.
                    None => enclosing_sort
                        .map(|s| provider_dict_entries(kb, s, None))
                        .unwrap_or_else(DictChain::empty),
                };
                let dict = ProjectionSyms::resolve(kb)
                    .and_then(|syms| emit_tree_as_projection(kb, &caller, tree, &syms));
                // A cross-sort constructing tree that fails to emit would degrade
                // to `None` → plain apply → the callee's own `requires` reads an
                // absent frame dict at eval — the wrong-dict class WI-829 fixes.
                // Every input here is well-formed (reflect is loaded and a
                // resolved `FromScope`'s scope_index names a real chain slot), so
                // a `None` is an internal inconsistency, not a supported case:
                // surface it loudly rather than silently reintroduce the bug.
                debug_assert!(
                    dict.is_some(),
                    "WI-829: cross-sort constructing tree for {} failed to emit a \
                     dispatch dict (ProjectionSyms / emit_tree_as_projection)",
                    kb.local_name_of(impl_op),
                );
                dict
            }
            _ => None,
        };
        CallClass::ConcreteApplyWithin {
            fn_target_sym: impl_op,
            callee_spec_sort: impl_sort.unwrap(),
            spec_op_sym: fn_sym,
            enclosing_sort,
            resolved_tree,
            dispatch_dict,
            enclosing_op: op_supply.and_then(|c| c.enclosing_op),
        }
    } else {
        CallClass::PinNow {
            spec_op_sym: fn_sym,
            impl_op_sym: impl_op,
        }
    };
    classify(kb, occ, class);
    Ok(())
}

/// WI-822 LEG 1 — the call-site context [`build_op_scoped_dicts`] needs, bundled so
/// the five concrete-dispatch arms that share [`classify_pin_or_apply_within`] pass
/// it as one thing. Every field is what the surrounding `check_apply_iter` frame
/// already holds; none is re-derived.
pub(crate) struct OpSupplyCtx<'a> {
    /// The per-call substitution — what pins a callee op-scoped element concretely.
    pub(crate) subst: &'a Substitution,
    /// The CALLER's own frame chain (sort half then op half), which a forwarded slot
    /// reads by name at eval.
    pub(crate) caller_requires: &'a DictChain,
    /// The body's param→rigid bridge, for the σ gate on forwarding (WI-821).
    pub(crate) param_rigids: &'a [(VarId, TermId)],
    /// The call's explicit provider selections (058 §4.5).
    pub(crate) selected: &'a [InstanceSelection],
    /// The caller's operation — recorded on the classification so eval can name the
    /// caller's op slots when a forward reads one.
    pub(crate) enclosing_op: Option<Symbol>,
    /// WI-20260909-S8CBV — each callee PARAMETER symbol → the type of the argument this
    /// call binds to it. [`build_op_scoped_dicts`] δ-grounds a projection-carried
    /// requirement against it, and the answer decides a REFUSAL: a projection that
    /// grounds here needs nothing further, one that does not can only be forwarded, and
    /// forwarding is what this ticket does not build.
    pub(crate) param_arg_types: &'a HashMap<Symbol, Value>,
    /// WI-20260921-3G1YT — ROUTE 4's slot source: the spec VIEWS the caller holds values
    /// of ([`held_spec_views`]). Rides here for the same reason every field above does —
    /// it is call-site information the op half's verdict needs and the dep cannot see.
    pub(crate) held: &'a [HeldSpecView],
}

/// WI-606: the carrier's GENUINE self-receiver override of the spec op
/// `fn_sym` (short name `op_short_sym`), or `None`. `carrier_override_op` already
/// filters to a runnable carrier member of that short name; this additionally
/// requires that member to declare a self-receiver parameter typed by the carrier
/// — so a member sharing only the short name (`C.foo(x, y)` vs the spec op
/// `S.foo(s: S)`) is rejected rather than `PinNow`'d and applied at a mismatched
/// arity. Shared by both WI-606 sites (the return-threading fallback and the
/// `NoCandidates` classification) so they cannot disagree about what counts as the
/// override.
///
/// WI-1010 deliberately did NOT widen this to [`carrier_override_suppliers`], though
/// it is the last reader of `carrier_override_op`. Not because a default cannot reach
/// it — a first draft of this note claimed both callers were body-less-gated and that
/// is FALSE, measured: the `classify_pin_or_apply_within` caller is inside
/// `lookup_spec_op_dispatch`'s block, but the other, reached through
/// [`concrete_override_threaded`], sits in the projection-elimination fallback, gated
/// only on `self_recv_spec` — which comes from the deliberately BODY-AGNOSTIC
/// `self_receiver_spec_sort`. A defaulted spec op with a projection-laden return does
/// reach here.
///
/// The reasons it stays route-1 are:
///   * declining here RE-RAISES the projection error rather than selecting anything,
///     so no supplier can be shadowed by a default — the failure mode WI-1010 exists
///     to close cannot occur at this site whatever it reads;
///   * the question is narrower: which member's RETURN to thread, gated on a
///     self-receiver parameter typed by the carrier;
///   * for a SELF-RECEIVER spec a route-2 supplier now DOES reach the carrier, and this
///     site is still route-1 by choice rather than by unreachability. WI-1076 retired
///     the premise this bullet used to state — that `provision_carrier_sort` files such
///     a provision under the spec's FIRST TYPE PARAM, so nothing reached it (058 §12,
///     WI-450's carrier-as-artifact problem). It now answers `None` for a
///     self-representing spec and the provision keys at its provider, i.e. at the
///     carrier. The two reasons above stand on their own; only the "inert" one is gone.
pub(super) fn concrete_self_receiver_override(
    kb: &mut KnowledgeBase,
    carrier_sym: Symbol,
    fn_sym: Symbol,
    op_short_sym: Symbol,
) -> Option<Symbol> {
    let impl_op = carrier_override_op(kb, carrier_sym, fn_sym, op_short_sym)?;
    let info = lookup_operation_info_full(kb, impl_op)?;
    self_receiver_param_index(kb, &info.params, carrier_sym)?;
    Some(impl_op)
}

/// WI-606: the return type a self-receiver spec op's call should thread when the
/// spec op's OWN (projection-laden) return does not eliminate against the receiver.
///
/// A body-less self-receiver spec op types its return at the abstract SPEC carrier
/// with path-dependent projections — `Stream.splitFirst(s: Stream) -> Option[Pair[A
/// = s.T, B = Stream[T = s.T, E = s.E]]]`. Against a receiver whose carrier is a
/// concrete provider that realizes the spec's members only INDIRECTLY (`Mapped
/// provides Stream[E = {ES, EF}]` — no direct `.E` on `Mapped`), `s.E` fails to
/// eliminate; because elimination is all-or-nothing that poisons the whole return,
/// leaving the destructured tail a bare `Var` → a downstream dispatch on it
/// (`cons(h, collect(rest))`) cannot ground (`expected List[T = ?T], got List[T =
/// ?_]`). The call value-dispatches to that provider's override at eval, whose
/// return is projection-FREE (`Mapped.splitFirst -> Option[Pair[A = T, B =
/// Mapped[…]]]`) — thread THAT, exactly what a qualified static `Mapped.split-
/// First(m)` computes (the ticket's "ground + thread the return from that impl's
/// signature like the qualified path").
///
/// Returns BOTH the impl's threaded return AND its threaded effects — the spec op's
/// OWN projected effects (`effects s.E`) likewise fail to eliminate against the
/// indirect-provision carrier, so the impl's effects (which the runtime target
/// actually incurs) replace them rather than being silently dropped; this keeps the
/// call's effect row sound on EVERY downstream dispatch arm (incl. the WI-239 defer
/// / NoMatch-covers early returns, which do not re-derive `dispatched_impl_effects`).
///
/// `None` — leaving the spec op's own (loudly-failing) elimination to stand — unless
/// the call is a self-receiver spec op (`self_recv_spec`) on a GENUINE concrete
/// provider (not an abstract spec, whose runtime value is some other provider
/// resolved dynamically; not the spec sort itself, an abstract self-receiver) that
/// declares a runnable self-receiver override. The impl's params are bound by
/// unifying the receiver against the impl's self-receiver param in a THROWAWAY
/// subst (the tie a Path-1 call to the impl makes): a bare self-param (`m: Mapped`)
/// binds the carrier's canonical sort params via `unify_parameterized_with_sort_-
/// ref`; a parameterized one (`f: FilteredStream[T = Elem, …]`) binds the op's own
/// `[Elem, …]` params.
pub(super) fn concrete_override_threaded(
    kb: &mut KnowledgeBase,
    op: &OperationInfoFull,
    fn_sym: Symbol,
    self_recv_spec: Option<Symbol>,
    pos_results: &[Result<TypeResult, TypeError>],
) -> Option<(Value, Vec<Value>, Symbol)> {
    // Self-receiver spec ops only (`splitFirst(s: Stream)`): the carrier-param
    // shape (`collect(c: C)`) does not write a receiver-projected return.
    let spec_sort = self_recv_spec?;
    let idx = self_receiver_param_index(kb, &op.params, spec_sort)?;
    let recv_ty = pos_results.get(idx)?.as_ref().ok()?.ty.clone();
    let carrier_sym = sort_functor_of_view(kb, &recv_ty)?;
    if carrier_is_abstract_spec(kb, carrier_sym)
        || kb.canonical_sort_sym(carrier_sym) == kb.canonical_sort_sym(spec_sort)
    {
        return None;
    }
    let op_qn = kb.qualified_name_of(fn_sym).to_string();
    let op_short_sym = kb.intern(short_name_of(&op_qn));
    let impl_op = concrete_self_receiver_override(kb, carrier_sym, fn_sym, op_short_sym)?;
    // Thread the impl's OWN return + effects through the receiver. The receiver is
    // the ground truth for the impl's element/effect params, and the deep resolve below
    // reads THIS σ — so what a failed unify leaves in it is this site's business.
    // WI-20260904-60143: "a failed unify leaves them free" is what this said, and it was
    // never true. `unify_types` does not roll back; it binds every component that AGREED
    // and answers `false` for the rest (see its "what survives a `false`" note). So a shape
    // mismatch leaves the params PARTIALLY pinned and the resolve returns a type built from
    // the agreeing half — which is the intended reading here, the receiver being ground
    // truth for exactly as much as it determines, but it is a different statement from
    // "free". What that ticket changed is that the surviving half no longer depends on the
    // order the receiver's type-args happened to be written in.
    let impl_info = lookup_operation_info_full(kb, impl_op)?;
    let impl_idx = self_receiver_param_index(kb, &impl_info.params, carrier_sym)?;
    let self_param_ty = impl_info.params[impl_idx].1.clone();
    let mut subst = Substitution::new();
    unify_types(kb, &mut subst, &recv_ty, &self_param_ty);
    let ret = resolve_type_deep_value(kb, &subst, &impl_info.return_type);
    let effs = impl_info
        .effects
        .iter()
        .map(|e| resolve_type_deep_value(kb, &subst, e))
        .collect();
    // WI-1063: `impl_op`, not the spec op the CALL named. The returned type is the
    // OVERRIDE's declaration, so every question asked about it downstream must be asked of
    // its owner — in particular whether a sort reference in it is SELF (the §3 tie). Keying
    // that on `fn_sym` would read `MappedStream.splitFirst`'s own `B = MappedStream[…]` as
    // FOREIGN, since `fn_sym` is `Stream.splitFirst`, and skolemize the very carrier tie this
    // function exists to thread.
    Some((ret, effs, impl_op))
}

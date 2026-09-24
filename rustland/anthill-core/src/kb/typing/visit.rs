//! The iterative typer's VISIT half: `visit_type` pushes a node's children with their
//! hints; plus reassembly of rewritten children and `@[simp]` firing.

use super::*;

/// Dispatch a single Visit: produce a leaf TypeResult directly,
/// delegate to a recursive helper, or push a Build frame + child
/// Visits for the env-changing Let / Match / Lambda cases.
pub(super) fn visit_type(
    kb: &mut KnowledgeBase,
    occ: Rc<NodeOccurrence>,
    env: Env,
    expected: Option<Value>,
    // WI-283: the `@[simp]` fire-fuel for this node; passed unchanged to
    // child Visits and to the Apply/Constructor/Let/Match build frames so
    // a fire can spend it (`fuel - 1`) when it re-`Visit`s the RHS.
    fuel: usize,
    // WI-1104: where this node sits in its rule body ([`NodePos`]). Passed on to the
    // three build frames that can BE a rule-body goal (`Apply` / `ApplyHints` /
    // `DotApply`); a CHILD visit is data by construction and takes `NodePos::Value` from
    // [`push_visit`] without being told.
    pos: NodePos,
    // WI-20260904-50B2K part (c), step 2 — the walk's inference state, for the ONE reader
    // in this function: `check_bare_ref`'s env-var path, which ∀-eliminates a generalized
    // lambda and must tell the walk it did (`note_instantiation`). It is `&mut` rather
    // than a return channel because the elimination happens inside a three-way dispatch
    // whose other arms have nothing to report.
    solving: &mut WalkSolutions,
    work: &mut Vec<TypeWorkOp>,
    results: &mut Vec<Result<TypeResult, TypeError>>,
) {
    // Expr / MatchBranch don't derive Clone (Expr's classification
    // RefCell + the implicit sharing through Rc), so we match by
    // reference and `Rc::clone` / hand-clone the slots we need.
    let occ_span = Some(occ.span.span);
    let expr = match &occ.kind {
        NodeKind::Expr { expr, .. } => expr,
        NodeKind::RuleHead { .. }
        | NodeKind::Pattern { .. }
        | NodeKind::Type(_)
        | NodeKind::EffectExpr(_) => {
            // RuleHead never appears in op/rule body position; Pattern
            // is reached via its parent Expr's pattern slot and handled
            // there, not as a typing target on its own (WI-318).
            // WI-342: Type/EffectExpr occurrences are type-level data,
            // not an expression typing target.
            results.push(Err(TypeError::BottomExpr { span: occ_span }));
            return;
        }
    };
    match expr {
        // ── Iterative cases ─────────────────────────────────────
        Expr::Let {
            pattern,
            value,
            body,
        } => {
            // WI-511: pattern is a Pattern-kind occurrence, read occurrence-native
            // by the env-extension helpers — no `pattern_to_term` bridge.
            let pattern = Rc::clone(pattern);
            // WI-819: the `: T` annotation comes off the PATTERN — the one
            // channel, read through the same `extract_pattern_type_ann` the
            // lambda arm uses. It used to come off an `Expr::Let.type_annotation`
            // that only a `let` had, which is why `let x: T` and `let (a, b): T`
            // behaved differently for no reason the author could see. Everything
            // downstream of this line (WI-399 projection elimination, WI-400
            // alias canonicalization, the value's expected type, and the
            // WI-379 conformance check at `LetAfterValue`) is unchanged.
            let annotation =
                extract_pattern_type_ann(&pattern).map(|ann| pattern_annotation_value(kb, ann));
            // WI-399: discharge an expression-carried projection (`s.cell.T`) in the
            // let annotation HERE, where `env` resolves the receiver's type — the
            // let-binding peer of the op-call elimination in `check_apply_iter`. The
            // eliminated type then feeds BOTH the value's expected (below) and the
            // value-vs-annotation conformance at `LetAfterValue`, so a concrete
            // projection annotation (`s.cell.T` = `String`) checks the value against
            // `String`, not the opaque projection. A projection whose receiver type is
            // NOT concretely known in scope (a bare / abstract receiver, a missing
            // member) is a LOUD error here — never silently leaked to `unify_types`
            // (which now refuses an un-eliminated projection head, the WI-399 safety
            // net). The env's `var_bindings` is exactly the `Symbol -> type` resolver
            // `eliminate_type_projections` needs (the analog of `param_to_arg_type`).
            // WI-819: the elimination below REWRITES the annotation, and the
            // pattern is now where the binder reads it from — so the rewritten
            // type is written BACK onto the pattern (`pattern` is rebound). Left
            // un-rewritten, `bind_and_label_pattern` would compare the
            // eliminated context type against the raw `s.T` and report the WI-794
            // binder contradiction between a type and itself.
            let mut pattern = pattern;
            let annotation = match annotation {
                Some(ann) if value_contains_projection(kb, &ann) => {
                    // WI-400 increment C (eager let-alias): canonicalize the annotation's
                    // projection receiver through the env's let-aliases BEFORE elimination,
                    // so `let y = z; let k: y.M` resolves `y.M` against the SAME receiver as
                    // `z.M` (`let y = z ⟹ y.M ≡ z.M`). A no-op when no alias applies.
                    let ann = canonicalize_projection_receivers(
                        kb,
                        env.receiver_aliases(),
                        &ann,
                        occ.span,
                    );
                    let var = extract_pattern_var_name(&pattern).unwrap_or_else(|| kb.intern("_"));
                    let ctx = TypeErrorContext::LetBinding { var };
                    // WI-459: a let-annotation is a BODY-site projection — the receiver is
                    // the in-scope value itself, there is no call argument to re-key to
                    // (`None`).
                    match eliminate_type_projections(
                        kb,
                        &ann,
                        &env.var_bindings,
                        None,
                        &ctx,
                        occ_span,
                    ) {
                        Ok(elim) => {
                            // WI-1059: the rewrite lands in the STORED tree (`LetFinal`
                            // reassembles the `Let` from its children so a rewrite in any
                            // of them propagates — WI-283), so it must not carry anything
                            // whose identity is PASS-LOCAL. A `Var::Rigid` is exactly that:
                            // it is minted fresh per body check, so a stored annotation
                            // holding one is stale the moment the pass ends, and a second
                            // `type_check_sorts` over the same KB compares it against that
                            // pass's rigids — `expected L[T = ?T], got L[T = ?T]`, two
                            // skolems rendering alike. MEASURED on `List.reverse`'s
                            // `let seed: List[T = xs.T] = nil`, and reachable on main by
                            // WRITING the parameter out (`xs: List[T = T]`); WI-1059 only
                            // made the bare spelling reach it too. The eliminated form is
                            // still what this pass CHECKS against — it just does not
                            // outlive the pass.
                            if !value_contains_rigid(kb, &elim) {
                                let ann_occ = value_to_pattern_annotation(kb, &elim, occ.span);
                                pattern = with_pattern_annotation(&pattern, ann_occ);
                            }
                            Some(elim)
                        }
                        Err(e) => {
                            results.push(Err(e));
                            return;
                        }
                    }
                }
                other => other,
            };
            let value_occ = Rc::clone(value);
            let body_occ = Rc::clone(body);
            // WI-270: value's expected is the let's annotation only —
            // the outer `expected` doesn't constrain `let x = e` since
            // `e`'s type isn't required to match the let-expression's
            // result type. The let's own `expected` instead flows
            // through to the body.
            work.push(TypeWorkOp::Build(TypeBuildFrame::LetAfterValue {
                occ: Rc::clone(&occ),
                pattern,
                annotation: annotation.clone(),
                body_occ,
                body_expected: expected,
                fuel,
                // WI-537: stash the let-site Γ before `env` moves into the value
                // visit — the body rebuilds its `Env` from the value's result
                // types under this same flow.
                outer_flow: env.flow.clone(),
            }));
            // WI-342 S4a: the let-annotation is a carrier-agnostic `Value` and IS
            // the value's expected type (WI-270) — thread it directly.
            push_visit(work, value_occ, env, annotation, fuel);
        }
        Expr::Match {
            scrutinee,
            branches,
        } => {
            let scrutinee_occ = Rc::clone(scrutinee);
            let branches_cloned: Vec<MatchBranch> = branches
                .iter()
                .map(|b| MatchBranch {
                    pattern: Rc::clone(&b.pattern),
                    guard: b.guard.as_ref().map(Rc::clone),
                    body: Rc::clone(&b.body),
                    span: b.span,
                })
                .collect();
            work.push(TypeWorkOp::Build(TypeBuildFrame::MatchAfterScrutinee {
                occ: Rc::clone(&occ),
                branches: branches_cloned,
                outer_env: env.clone(),
                body_expected: expected,
                fuel,
            }));
            push_visit_no_hint(work, scrutinee_occ, env, fuel);
        }
        Expr::Lambda { param, body } => {
            // WI-511: `param` is a Pattern-kind Rc<NodeOccurrence>, read
            // occurrence-native by the typer's pattern helpers — no
            // `pattern_to_term` bridge.
            let param = Rc::clone(param);
            let body_occ = Rc::clone(body);
            // Lambda param type, in priority order:
            //   1. explicit annotation on the pattern,
            //   2. the expected arrow's param slot (checking direction —
            //      e.g. `let f: Function[A, B] = lambda q -> ...` already
            //      threads `Function[A, B]` here as `expected`),
            //   3. a fresh LOGIC variable (synthesis — left for body usage and
            //      the eventual call site to pin via unification).
            // WI-20260904-50B2K: rung 3 used to mint a `type_var`, which the line
            // above already said was wrong — a `type_var` CANNOT be pinned by
            // unification. See the mint site below.
            // Previously this used only (1), so an unannotated lambda left
            // its param unbound in the body env and every reference to it
            // failed resolution as `UnresolvedName`.
            // WI-342: the param type is carrier-agnostic (`Value`) — the env binds
            // it directly, and `LambdaBody` builds the arrow's param slot from it
            // (a `Value::Node` denoted-bearing param is carried, not re-grounded).
            // WI-511 / WI-819: the annotation rides the Pattern occurrence's
            // `type_ann` child — the ONE channel, read through the same
            // `extract_pattern_type_ann` the `Expr::Let` arm uses, and decoded by
            // the same `pattern_annotation_value`.
            //
            // The comment this replaces claimed "the grammar's `pattern_var`
            // doesn't surface one today, so this is normally None". That was
            // FALSE before WI-819 and is doubly so now: WI-517's `typed_binder`
            // (`lambda (x: T) -> …`, `lambda (a: A, b: B) -> …`) has surfaced one
            // since it landed — it is the very feature this ladder's rung (1)
            // exists for.
            //
            // Reads through `pattern_annotation_value` rather than a bare
            // `occurrence_to_term`, so a `denoted`-bearing annotation keeps its
            // `Value::Node` carrier instead of being flattened to `Value::Term`
            // (the carrier is information — see that function).
            let ann_type: Option<Value> = extract_pattern_type_ann(&param)
                .map(|ann_occ| pattern_annotation_value(kb, ann_occ));
            let param_type: Value = ann_type
                .or_else(|| {
                    // Checking direction: the expected arrow's param slot, as-is.
                    expected
                        .as_ref()
                        .and_then(|exp| extract_function_param_type(kb, exp))
                })
                .unwrap_or_else(|| {
                    // WI-20260904-50B2K — SYNTHESIS MINTS THE ENGINE'S OWN VARIABLE, and
                    // the two forms answer different questions. A `type_var` means "no
                    // type is available here": INERT by design, compatible with anything
                    // WITHOUT committing (`KnowledgeBase::make_type_var`'s doc, the M6
                    // flounder posture), which is right for `value_type_term`'s runtime
                    // fallback — a run-time reader must not commit what typing never
                    // decided — and wrong here. An un-annotated binder is not a type
                    // nobody could name; it is a type TO BE INFERRED, and inference is
                    // exactly what must commit. Note the ladder comment above stated that
                    // intent all along ("to pin via unification") while the mint could
                    // not honour it.
                    // NOT INTERNED — WI-20260904-02ERR delivered the carrier this site was
                    // waiting for. `kb.fresh_var` mints a brand-new `VarId` every time, so
                    // the old `Value::term(type_param_var_term(..))` took that function's
                    // `alloc` fallback on EVERY un-annotated binder and left a refcounted
                    // `Term::Var` nothing releases — one pinned `TermStore` slot per binder
                    // PER LOAD, unbounded in a process that loads repeatedly, against
                    // CLAUDE.md's rule that transient terms are not interned.
                    //
                    // `Value::Var` IS THE CARRIER NOW, and the note this replaces was right
                    // that it used to fail: `value_to_type_child` called a `Var` in a type
                    // slot "a typer bug". It no longer does — it routes through
                    // `KnowledgeBase::type_var_child`, which gives a per-site `Global` the
                    // `TypeNode::Var` occurrence carrier and leaves a shared `DeBruijn`
                    // interned. A BARE type variable in VALUE position stays `Value::Var`,
                    // which is what σ already substitutes; the occurrence form is the
                    // NESTED spelling, minted at that narrowing seam.
                    let fresh = kb.intern("?param");
                    let vid = kb.fresh_var(fresh);
                    Value::Var(Var::Global(vid))
                });
            let mut lambda_env = (*env).clone();
            // WI-794: at arity 1 `param_type` IS the annotation (it won the priority
            // ladder above), so the two agree and nothing fires here — that case is
            // rejected one altitude up, by the whole-arrow subsumption at the argument
            // position, and keeps its existing diagnostic. At arity 2+ `param_type` comes
            // from the CONTEXT and the per-binder annotations are compared against its
            // components; this is the channel WI-794 measured as unchecked.
            let mut binder_errors = Vec::new();
            let mut param_repoints: Vec<(Symbol, Symbol)> = Vec::new();
            let param = bind_and_label_pattern(
                kb,
                &mut lambda_env,
                &param,
                Some(param_type.clone()),
                // WI-20260827-EJ5F5: a lambda parameter BINDS. `lambda red -> …` over a
                // `C` must be a total function of `C`, so a name colliding with one of
                // `C`'s constructors is still the binder the author wrote — and nothing
                // is rewritten, so nothing has to be re-pointed. Asserted rather than
                // asserted-in-a-comment: an empty sink is what makes discarding it safe.
                PatternRole::Binder,
                &mut param_repoints,
                // WI-20260904-50B2K: the SEED, and it is only ever read when
                // `param_type` gives a sub-pattern nothing. Nothing encloses a lambda's
                // parameter list, so there is no question to inherit — the tuple arm
                // below answers for the components from `param_type` itself, which is a
                // fresh variable exactly when rung 3 minted it.
                UnpinnedBinder::Unnameable,
                &mut binder_errors,
            );
            debug_assert!(
                param_repoints.is_empty(),
                "WI-20260827-EJ5F5: `PatternRole::Binder` must never rewrite",
            );
            // WI-270: if expected is `arrow(param, result, effects)`,
            // decompose and pass `result` to the body. Mismatching
            // shapes (or `None`) leave the body without a hint. WI-342 S3a: the
            // body's expected hint is a carrier-agnostic `Value` — no re-ground.
            let body_expected = expected.as_ref().and_then(|exp| {
                let exp_ty = extract_callable_type(kb, exp);
                extract_function_type_parts(kb, &exp_ty).map(|(ret, _)| ret)
            });
            // The lambda body runs under the SAME Γ as the lambda site (the
            // binder narrows types, not the flow); capture it before `env` moves
            // into the frame.
            let body_env = env.with_types(lambda_env);
            work.push(TypeWorkOp::Build(TypeBuildFrame::LambdaBody {
                occ: Rc::clone(&occ),
                param_type,
                outer_env: env,
                binder_error: binder_errors.into_iter().next(),
                param,
            }));
            push_visit(work, body_occ, body_env, body_expected, fuel);
        }

        // ── Leaf cases ──────────────────────────────────────────
        //
        // ONE ARM, and the inner match is what keeps `Literal` compile-time exhaustive
        // here: it carries no wildcard, so a sixth literal kind is a build error at this
        // site rather than a runtime surprise. (It was NOT, until the unreachable
        // `Expr::Const(_) => BottomExpr` catch-all was removed: with that arm present a
        // new variant compiled clean here while nine other sites in the crate refused
        // it — measured.)
        //
        // `try_make_sort_ref_by_name`, NOT the infallible form (WI-913). The infallible
        // one mints an Unresolved sort out of a name that denotes nothing, and its own
        // doc names exactly this caller: "a typer arm then reads it as a real type".
        // `type_check_expr`/`type_check_node` are `pub` and a `KnowledgeBase::new()`
        // that never ran `register_prelude` is a legal state, so on such a KB every
        // integer literal would type as a freshly interned phantom `Int64` that unifies
        // with nothing — surfacing far away as an unexplained subsumption mismatch
        // instead of here, at the literal that caused it.
        //
        // A `BigInt` literal is one that exceeded `i64` at parse — it cannot be an
        // `Int` value, so it types as `BigInt`. (Previously lumped with `Int`; the
        // WI-379 args-before-expected order made that mis-typing visible — `100…0 +
        // 100…0` declared `-> BigInt` pinned `Numeric.T` to the literal's type from the
        // argument, so a literal typed `Int` made the sum `Int`, rejected against the
        // `BigInt` return.)
        Expr::Const(lit) => {
            let sort_name = match lit {
                Literal::Int(_) => "Int64",
                Literal::BigInt(_) => "BigInt",
                Literal::Float(_) => "Float",
                Literal::String(_) => "String",
                Literal::Bool(_) => "Bool",
            };
            match kb.try_make_sort_ref_by_name(sort_name) {
                Some(t) => results.push(Ok(TypeResult::pure(t, unwrap_env(env), Rc::clone(&occ)))),
                None => results.push(Err(TypeError::BottomExpr { span: occ_span })),
            }
        }
        // WI-714: a macro-spliced value's type belongs to its BUILDER, not the
        // typer — only `guarded_of` (which constructs the recipe) knows it. Read
        // the type the constructor stamped (`set_inferred_type`, carrier-neutral);
        // else adopt the context's expected type; else we genuinely don't know it
        // → loud error, never a fabricated one.
        Expr::Spliced(_) => match occ.inferred_type().or_else(|| expected.clone()) {
            Some(ty) => results.push(Ok(TypeResult::pure_value(
                ty,
                unwrap_env(env),
                Rc::clone(&occ),
            ))),
            None => results.push(Err(TypeError::BottomExpr { span: occ_span })),
        },
        Expr::Ref(sym) => {
            let r = check_bare_ref(
                kb,
                &*env,
                &env.flow,
                *sym,
                occ_span,
                &occ,
                expected.as_ref(),
                solving,
            );
            results.push(r);
        }
        Expr::Ident(sym) => {
            let r = check_bare_ref(
                kb,
                &*env,
                &env.flow,
                *sym,
                occ_span,
                &occ,
                expected.as_ref(),
                solving,
            );
            results.push(r);
        }
        Expr::VarRef { name } => {
            // WI-275: thread the expected type so a bare operation reference in a
            // function-typed position is eta-lifted to a function value rather than
            // denoting its return type.
            let r = check_bare_ref(
                kb,
                &*env,
                &env.flow,
                *name,
                occ_span,
                &occ,
                expected.as_ref(),
                solving,
            );
            results.push(r);
        }

        // Proposal 055 §2 — a nominal type expression in value position, classified
        // by the LOADER. The typer's job here is what §1 calls VALIDATION, and it
        // starts at the arguments; the denotation is not re-decided.
        //
        // NOTHING PUSHES A `Type` HINT DOWN, and that absence is the point of the
        // increment: the WI-707 arm hinted every argument of a sort application with
        // `Type` so a bare sort name inside would read as one. It no longer needs to —
        // a nested nominal type is itself minted as an `Expr::TypeValue` by the same
        // loader rule that minted this node, so the reading is carried, not hinted.
        Expr::TypeValue {
            head,
            pos_args,
            named_args,
        } => {
            let head = *head;
            let occ_clone = Rc::clone(&occ);
            work.push(TypeWorkOp::Build(TypeBuildFrame::TypeValue {
                occ: occ_clone,
                head,
                pos_args: pos_args.clone(),
                named_args: named_args.clone(),
                env: env.clone(),
            }));
            for (_, arg) in named_args.iter().rev() {
                push_visit(work, Rc::clone(arg), env.clone(), None, fuel);
            }
            for arg in pos_args.iter().rev() {
                push_visit(work, Rc::clone(arg), env.clone(), None, fuel);
            }
        }

        // ── Iterative Apply / Constructor ───────────────────────
        // Push child Visits for every arg in reverse so they pop in
        // forward order, then a Build frame that drains the
        // pre-computed arg results and runs the subst / dispatch /
        // classify logic without recursing through `type_check_node`.
        Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        } => {
            // WI-20260902-4NEKZ — A DOTTED PAREN-LESS CITATION OF A RULE IS THAT
            // RELATION, in a rule-body VALUE slot as in an operation body. The chain
            // survives to here only where the loader did NOT collapse it — an operation
            // body's is already a `var_ref` by `try_qualified_rule_ref`, and a logical
            // position's is already the bare name by 719FJ — so this rung is reached by
            // exactly the population that was walking into its own leaves and reporting
            // one false "unresolved name" per segment. See
            // [`dotted_citation_relation`] for the measurement and for why the repair is
            // the typer's rather than the loader's.
            //
            // THE SHAPE GATE IS AT THE CALL SITE, not only inside, because this arm
            // types EVERY application in every body: a converter-minted `field_access`
            // is binary and unnamed, so a node that is not keeps the two `usize`
            // compares and skips the call — and with it the by-name symbol lookup
            // `field_access`'s identity needs. Not a measured saving (a single suite
            // run cannot rank one this small: 326.36s before, 326.64s after, with five
            // tests added), just the cheap tests written first.
            if pos_args.len() == 2 && named_args.is_empty() {
                if let Some(rel) = dotted_citation_relation(kb, &occ) {
                    let r = relation_reference_type(kb, rel, occ_span, &occ, None)
                        .map(|ty| TypeResult::pure_value(ty, unwrap_env(env), Rc::clone(&occ)));
                    results.push(r);
                    return;
                }
                // A dotted name of a NULLARY OPERATION in a RULE BODY is that operation's
                // CALL — the reading `seven` gets there from the loader, and the one the
                // resolver gives the chain when it reduces it (`reduce_dot_value`). Typed
                // through `check_bare_ref`'s zero-argument-call arm with NO expected type:
                // the resolver calls the chain whatever slot it sits in, so a hint here
                // could eta-lift `Box.zero` to a function value the resolver never
                // produces, and the two must give the name one reading. The node stays
                // the chain — the term the fact side stores — exactly as the relation rung
                // above leaves it.
                //
                // RULE BODIES ONLY. In an operation body the bare `Box.zero` names no
                // operation, and `Box[T = …].zero` is refused on that premise
                // (`ParenLessCitationOfNonRule`), so this reading stops where the
                // rule-body elaboration it mirrors stops. MEASURED REDUNDANT TODAY, and
                // kept as the statement of that scope: `loader_chain_dotted_name` needs
                // the written-dot flag, and only the rule-body walk (and the materializer
                // it falls back on) sets it, so with this gate removed an operation body
                // is still refused — no row can drive it. It becomes load-bearing the day
                // an operation-body producer marks its dots too.
                if env.in_rule_body() {
                    if let Some(op) = dotted_citation_nullary_op(kb, &occ) {
                        let r =
                            check_bare_ref(kb, &*env, &env.flow, op, occ_span, &occ, None, solving);
                        results.push(r);
                        return;
                    }
                }
            }
            let functor = *functor;
            // WI-707: a SORT-headed application in a slot that expects a `Type` is a
            // parameterized TYPE — `is_modifiable(Cell[V = Int64])` — not a call. Its
            // arguments are themselves TYPES, so every one takes the `Type` hint: that
            // is what lets a bare sort name inside read as a type (`check_bare_ref`'s
            // WI-206 arm) and a NESTED application recurse into this same arm
            // (`Map[K = String, V = Cell[V = Int64]]`). The Build frame turns the node
            // into the `Type` result; eval assembles the type term (`start_sort_type`).
            // `None` for every ordinary call, which then takes the hints below unchanged.
            let sort_app_hint: Option<Value> = if kb.kind_of(functor)
                == Some(crate::intern::SymbolKind::Sort)
                && expects_reflect_type(kb, expected.as_ref())
            {
                Some(Value::term(
                    kb.make_sort_ref_by_name("anthill.prelude.Type"),
                ))
            } else {
                None
            };
            // WI-657(5): keep `pos_args`/`named_args` as the borrowed pattern slots for
            // every local read AND the reversed push_visit loops; clone ONCE into the
            // Build frame below. Previously they were cloned into locals here and cloned
            // AGAIN into the frame — two SmallVec clones per Apply, ~1681+ execs.
            let occ_clone = Rc::clone(&occ);
            // WI-275: bidirectional inference for higher-order arguments. Look up
            // the callee's declared parameter types; a lambda or bare operation
            // reference in a function-typed slot gets that `Function[A, B, E]`
            // pushed in as its expected type (`hof_arg_hint`). The lambda then
            // types its parameter from `A` instead of leaving it an unconstrained
            // var (which makes an overloaded body call like `add(x, 1)` dispatch-
            // ambiguous), and a bare op name is eta-lifted to a function value.
            // Value/literal args take no hint, preserving the WI-379
            // args-before-expected order that lets their own type drive
            // dispatch. WI-427: a NESTED-CALL argument additionally gets the
            // declared param type as its hint when that type pins by equality
            // (fully ground) — the `expected → argument` half of bidirectional
            // inference (`nested_call_arg_hint`). The lookup is gated on the
            // call actually having a lambda/ref or nested-call argument.
            let has_hof_arg = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(is_hof_shaped);
            let has_call_arg = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(|a| {
                    matches!(
                        &a.kind,
                        NodeKind::Expr {
                            expr: Expr::Apply { .. },
                            ..
                        }
                    )
                });
            // WI-206 / WI-707: a sort-naming argument needs the callee's declared param
            // type as its hint too (`type_slot_arg_hint`), so the param lookup must fire
            // for it — `has_hof_arg` only covers Lambda/VarRef shapes and would miss a
            // sort named as a plain `Expr::Ref`.
            let has_sort_arg = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(|a| arg_names_sort(kb, a));
            // WI-20260826-JSFHG: a CONSTRUCTOR argument needs the callee's declared param
            // type as its hint ([`variant_slot_arg_hint`]), so the param lookup must fire
            // for it too. `has_call_arg` sees only the `Expr::Apply` spelling; the
            // field-named build `takeRed(red(v: 1))` is an `Expr::Constructor` and matched
            // NONE of the three gates, so its slot type was never looked up and the hint
            // was asked with `None`. The exact peer of `has_ctor_field` on the Constructor
            // arm, and of what WI-206/707 added here for a sort-naming argument.
            //
            // WHAT ELSE THIS UNGATES IS NOTHING, and the argument is worth stating because
            // widening a shared gate normally reaches every reader behind it: the calls
            // newly looking `op_info` up are exactly those with a constructor argument and
            // NO hof / call / sort-naming one, and each of the three older hints requires
            // the argument shape whose absence defines that case — so on such a call they
            // still answer `None` with a real `pt` in hand. Only `variant_slot_arg_hint`
            // can fire here that could not before. (`inst` likewise: `known` is empty
            // whenever `has_hof_arg` is false, and it is read only for a hof-shaped arg.)
            let has_ctor_arg = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(|a| arg_is_constructor_application(kb, a));
            // WI-821: keep the WHOLE record — `known_arg_types_and_staged` reads
            // `type_params` besides `params`, and re-looking the record up there
            // would clone every field a second time per hof-bearing call.
            let op_info = if has_hof_arg || has_call_arg || has_sort_arg || has_ctor_arg {
                lookup_operation_info_full(kb, functor)
            } else {
                None
            };
            // WI-485 + WI-793: the param→argument-type map that lets a sibling callback
            // param's projection be eliminated BEFORE it hints a lambda, and the argument
            // positions this call must type FIRST for that map to be complete. See
            // `known_arg_types_and_staged` for the ordering problem and why staging is the
            // fix; built only when a higher-order argument is present, since a hint is only
            // load-bearing for a lambda.
            let (known_param_arg_types, staged) = match (&op_info, has_hof_arg) {
                (Some(op), true) => {
                    known_arg_types_and_staged(kb, &env, functor, op, pos_args, named_args)
                }
                _ => (HashMap::new(), Vec::new()),
            };
            let op_params = op_info.map(|op| op.params);
            if staged.is_empty() {
                // THE ORDINARY PATH, unchanged: no argument hint depends on a sibling
                // argument's type, so hint everything and visit everything.
                let (pos_hints, named_hints) = apply_arg_hints(
                    kb,
                    functor,
                    op_params.as_ref(),
                    &sort_app_hint,
                    pos_args,
                    named_args,
                    &known_param_arg_types,
                );
                work.push(TypeWorkOp::Build(TypeBuildFrame::Apply {
                    occ: occ_clone,
                    fn_sym: functor,
                    pos_args: pos_args.clone(),
                    named_args: named_args.clone(),
                    env: env.clone(),
                    expected,
                    fuel,
                    staged_results: Vec::new(),
                    pos,
                }));
                for ((_, arg), hint) in named_args.iter().zip(named_hints.iter()).rev() {
                    push_visit(work, Rc::clone(arg), env.clone(), hint.clone(), fuel);
                }
                for (arg, hint) in pos_args.iter().zip(pos_hints.iter()).rev() {
                    push_visit(work, Rc::clone(arg), env.clone(), hint.clone(), fuel);
                }
            } else {
                // WI-793: STAGED. A callback param projects a sibling (`f: (…, x: xs.T) -> …`)
                // whose argument no no-typing reader can answer for, so that argument is
                // visited FIRST and the hints for everything else are built in the
                // `ApplyHints` frame below, once its type exists.
                //
                // Only the STAGED arguments are hinted here — hinting the rest now would be
                // discarded work, and the lambda's hint in particular would be computed
                // against the very map that is still incomplete. A staged argument keeps
                // exactly the hint it would otherwise have had: it is never hof-shaped, and
                // `hof_arg_hint` is the only reader of the projection-eliminated type, so
                // the incomplete map cannot change its answer (see `apply_arg_hints`).
                let staged_hints: Vec<Option<Value>> = staged
                    .iter()
                    .map(|&unified| {
                        if sort_app_hint.is_some() {
                            return sort_app_hint.clone();
                        }
                        let (arg, pt) = if unified < pos_args.len() {
                            let pt = op_params
                                .as_ref()
                                .and_then(|ps| ps.get(unified))
                                .map(|(_, t)| t.clone());
                            (&pos_args[unified], pt)
                        } else {
                            let (label, arg) = &named_args[unified - pos_args.len()];
                            // WI-426: match the named-arg label to its param by name.
                            let pt = op_params
                                .as_ref()
                                .and_then(|ps| ps.iter().find(|(s, _)| same_label(kb, *s, *label)))
                                .map(|(_, t)| t.clone());
                            (arg, pt)
                        };
                        // A staged argument is never hof-shaped, so the WI-821
                        // instantiation subst (a HOF-hint-only input) is not
                        // computed for it.
                        one_arg_hint(kb, functor, arg, pt, &known_param_arg_types, None)
                    })
                    .collect();
                work.push(TypeWorkOp::Build(TypeBuildFrame::ApplyHints {
                    occ: occ_clone,
                    fn_sym: functor,
                    pos_args: pos_args.clone(),
                    named_args: named_args.clone(),
                    env: env.clone(),
                    expected,
                    fuel,
                    staged: staged.clone(),
                    // Non-empty whenever `staged` is — staging is keyed off the params.
                    op_params: op_params.clone().unwrap_or_default(),
                    sort_app_hint,
                    known: known_param_arg_types,
                    pos,
                }));
                // Reverse, so they pop in ASCENDING unified order — the order
                // `known_arg_types_and_staged` sorted `staged` into and the order the
                // `Apply` frame splices their results back by.
                for (k, &unified) in staged.iter().enumerate().rev() {
                    let arg = arg_at(pos_args, named_args, unified)
                        .expect("WI-793: a staged index was produced by `arg_at` itself");
                    push_visit(
                        work,
                        Rc::clone(arg),
                        env.clone(),
                        staged_hints[k].clone(),
                        fuel,
                    );
                }
            }
        }
        Expr::Constructor {
            name,
            pos_args,
            named_args,
            ..
        } => {
            let name = *name;
            // WI-657(5): borrow the pattern slots for local reads + the push_visit loops;
            // clone once into the Build frame below (was two clones per Constructor).
            // WI-427: the constructor-field twin of the nested-call hint — a
            // GROUND declared field type flows down into a field value that is
            // itself a call, so `hold(poly())` pins poly's return-only type
            // param exactly like an operation param slot does. Same gate, same
            // soundness argument (`nested_call_arg_hint`); a field type that
            // mentions the sort's own params (`cell: P`) is non-ground and
            // takes no hint. Other field values stay unhinted.
            // WI-462: a positional/named tuple `(h, t)` lowers to a `Constructor{TupleLiteral}`
            // (named `_1`/`_2`/declared fields) — that, not `Expr::TupleLit`, is the surface
            // form (`convert.rs` `TupleLiteral` build) and the one `check_tuple_literal_-
            // constructor` threads. (The `Expr::TupleLit` IR is a non-surface shape whose build
            // frame takes no expected, so a hint on it would be dropped — not recognized here.)
            fn is_tuple_lit(kb: &KnowledgeBase, arg: &Rc<NodeOccurrence>) -> bool {
                let NodeKind::Expr {
                    expr: Expr::Constructor { name, .. },
                    ..
                } = &arg.kind
                else {
                    return false;
                };
                // WI-657(6): O(1) Symbol compare against the cached TupleLiteral symbol.
                // The loader stamps that same `by_qualified_name` canonical symbol on a
                // tuple constructor (`remap_symbol` of the short `TupleLiteral` resolves to
                // the single `define(.., "anthill.reflect.TupleLiteral", ..)` entry, which
                // is what `try_resolve_symbol` caches), so `*name == tl` is exact. Fall back
                // to the exact string compare only when the cache is unset (pre-type-check /
                // reflect-less). A `debug_assert` cross-checks that the Symbol compare never
                // diverges from the qualified-name compare it replaced — a non-canonical
                // `TupleLiteral` interning reaching here becomes a LOUD test failure rather
                // than a silent mis-recognition (CLAUDE.md: loud over silent).
                match kb.tuple_literal_sym {
                    Some(tl) => {
                        let by_sym = *name == tl;
                        debug_assert_eq!(
                            by_sym,
                            kb.qualified_name_of(*name) == dt::qualified(dt::TUPLE_LITERAL),
                            "WI-657(6): tuple_literal_sym Symbol-compare diverged from the \
                             qualified-name compare for constructor `{}`",
                            kb.qualified_name_of(*name),
                        );
                        by_sym
                    }
                    None => kb.qualified_name_of(*name) == dt::qualified(dt::TUPLE_LITERAL),
                }
            }
            let has_call_field = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(|a| {
                    matches!(
                        &a.kind,
                        NodeKind::Expr {
                            expr: Expr::Apply { .. },
                            ..
                        }
                    )
                });
            // WI-462: a TUPLE-LITERAL field value gets the constructor's expected pushed
            // down to its component types (so `some((h, t))` under `Option[(xs.T, …)]`
            // threads `h ⟹ xs.T`); other field values keep the nested-call hint.
            let has_tuple_field = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(|a| is_tuple_lit(kb, a));
            // Owned field-type list (Symbol + declared Value), looked up once when any
            // field needs a hint — used both for the nested-call hint and to find a
            // tuple-literal field's declared symbol for the WI-462 expected derivation.
            // WI-707: likewise a sort-naming FIELD value (`ResourceRow(t: Cell)`) needs
            // its declared field type as the hint — the bare form is neither a call nor
            // a tuple, so without this the lookup is skipped and the sort name falls
            // through to `UnresolvedName`.
            let has_sort_field = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(|a| arg_names_sort(kb, a));
            // WI-20260826-JSFHG: a CONSTRUCTOR field value needs the declared field type
            // looked up too — `has_call_field` sees only the `Expr::Apply` spelling, so a
            // field-named build (`hold(v: red(v: 1))`) took no hint at all without this.
            // Same containment argument as `has_ctor_arg` on the Apply arm: the builds
            // newly looking `field_types` up have no call / tuple / sort-naming field, and
            // each older hint here is gated on exactly one of those shapes.
            let has_ctor_field = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(|a| arg_is_constructor_application(kb, a));
            // WI-20260828-8Q0Q5: a BARE OPERATION NAME field needs the declared field type
            // too — it is the shape [`arrow_slot_arg_hint`] reads, and none of the four
            // gates above sees it (a bare name is not a call, a tuple, a sort name or a
            // constructor application), so such a build took no hint at all. Same
            // containment argument as its siblings: the builds newly looking `field_types`
            // up have none of those four shapes, and every older hint here is gated on
            // exactly one of them, so none of them can fire on a build that only just
            // started computing the table.
            let has_op_name_field = pos_args
                .iter()
                .chain(named_args.iter().map(|(_, a)| a))
                .any(|a| arg_is_bare_operation_name(kb, a));
            let field_types: Option<Vec<(Symbol, Value)>> = if has_call_field
                || has_tuple_field
                || has_sort_field
                || has_ctor_field
                || has_op_name_field
            {
                kb.entity_field_types(name).map(|ft| ft.to_vec())
            } else {
                None
            };
            // WI-20260826-JSFHG: when THIS build is itself a tuple literal, its components'
            // declared types live in the expected TUPLE, not in `field_types` (the
            // `TupleLiteral` entity declares none). See [`tuple_component_expected`].
            let self_is_tuple_lit = kb.qualified_name_of(name) == dt::qualified(dt::TUPLE_LITERAL);
            // WI-20260826-7JDWY: when THIS build is a LIST or SET literal, every element's
            // declared type is the expectation's `T` — the exact peer of the tuple case
            // above, and needed for the same reason: the `ListLiteral` / `SetLiteral`
            // entity declares no element fields, so `field_types` is empty and every
            // existing hint reads it.
            //
            // THE CHECK ALONE IS NOT ENOUGH WITHOUT IT. [`seq_literal_element_type`] now
            // judges each element against the declared element type, and a constructor
            // element with no expectation of its own is classified at its PARENT sort
            // (§8.2) — so `takeReds([red(v: 1)])` against `List[T = Colour.red]` was
            // refused `expected red, got Colour`, a program the slot exists for. The hint
            // pushed here is what makes the classification the check demands reachable.
            //
            // UNCONDITIONAL, matching what the `Expr::ListLit` build frame already does
            // for the other carrier — the two spellings of one literal must not differ by
            // which hints their elements get.
            let seq_element_expected: Option<Value> = {
                let qn = kb.qualified_name_of(name);
                let kind = if qn == dt::qualified(dt::LIST_LITERAL) {
                    Some(SeqLiteral::List)
                } else if qn == dt::qualified(dt::SET_LITERAL) {
                    Some(SeqLiteral::Set)
                } else {
                    None
                };
                kind.and_then(|k| declared_element_type(kb, k, expected.as_ref()))
            };
            let pos_hints: Vec<Option<Value>> = pos_args
                .iter()
                .enumerate()
                .map(|(i, arg)| {
                    // Ahead of the `field_types` read: a `ListLiteral` / `SetLiteral`
                    // declares no element fields, so there is nothing there to consult.
                    if let Some(h) = &seq_element_expected {
                        return Some(h.clone());
                    }
                    let field = field_types.as_ref().and_then(|fs| fs.get(i)).cloned();
                    if self_is_tuple_lit {
                        let label = crate::intern::positional_label(i);
                        if let Some(h) = tuple_component_expected(kb, &expected, &label) {
                            return Some(h);
                        }
                    }
                    if is_tuple_lit(kb, arg) {
                        if let Some((fs, _)) = &field {
                            if let Some(h) =
                                tuple_field_expected_from_ctor(kb, name, *fs, &expected)
                            {
                                return Some(h);
                            }
                        }
                    }
                    // WI-707: a `Type`-declared FIELD takes a sort name / sort
                    // application too (`ResourceRow(t: Cell)`), not just a `Type`-declared
                    // operation param — the two slots read a sort identically.
                    nested_call_arg_hint(kb, arg, field.as_ref().map(|(_, t)| t))
                        .or_else(|| type_slot_arg_hint(kb, arg, field.as_ref().map(|(_, t)| t)))
                        .or_else(|| variant_slot_arg_hint(kb, arg, field.as_ref().map(|(_, t)| t)))
                        .or_else(|| seq_slot_arg_hint(kb, arg, field.as_ref().map(|(_, t)| t)))
                        .or_else(|| arrow_slot_arg_hint(kb, arg, field.as_ref().map(|(_, t)| t)))
                        .or_else(|| {
                            let fs = field.as_ref().map(|(s, _)| *s)?;
                            arrow_field_expected_from_ctor(kb, name, fs, &expected, arg)
                        })
                        .or_else(|| {
                            let (_, ft) = field.as_ref()?;
                            ctor_arg_unlocks_an_arrow_for_a_bare_name(kb, arg, ft)
                                .then(|| ft.clone())
                        })
                        .or_else(|| {
                            let fs = field.as_ref().map(|(s, _)| *s)?;
                            variant_field_expected_from_ctor(kb, name, fs, &expected, arg)
                        })
                })
                .collect();
            let named_hints: Vec<Option<Value>> = named_args
                .iter()
                .map(|(fname, arg)| {
                    if self_is_tuple_lit {
                        let label = kb.local_name_of(*fname).to_string();
                        if let Some(h) = tuple_component_expected(kb, &expected, &label) {
                            return Some(h);
                        }
                    }
                    if is_tuple_lit(kb, arg) {
                        if let Some(h) = tuple_field_expected_from_ctor(kb, name, *fname, &expected)
                        {
                            return Some(h);
                        }
                    }
                    let ft = field_types
                        .as_ref()
                        .and_then(|fs| fs.iter().find(|(s, _)| s == fname))
                        .map(|(_, t)| t.clone());
                    // WI-707: as above — a `Type`-declared field accepts a sort.
                    nested_call_arg_hint(kb, arg, ft.as_ref())
                        .or_else(|| type_slot_arg_hint(kb, arg, ft.as_ref()))
                        .or_else(|| variant_slot_arg_hint(kb, arg, ft.as_ref()))
                        .or_else(|| seq_slot_arg_hint(kb, arg, ft.as_ref()))
                        .or_else(|| arrow_slot_arg_hint(kb, arg, ft.as_ref()))
                        .or_else(|| {
                            arrow_field_expected_from_ctor(kb, name, *fname, &expected, arg)
                        })
                        .or_else(|| {
                            let ft = ft.as_ref()?;
                            ctor_arg_unlocks_an_arrow_for_a_bare_name(kb, arg, ft)
                                .then(|| ft.clone())
                        })
                        .or_else(|| {
                            variant_field_expected_from_ctor(kb, name, *fname, &expected, arg)
                        })
                })
                .collect();
            work.push(TypeWorkOp::Build(TypeBuildFrame::Constructor {
                occ: Rc::clone(&occ),
                ctor_sym: name,
                pos_args: pos_args.clone(),
                named_args: named_args.clone(),
                env: env.clone(),
                span: occ_span,
                expected,
                fuel,
            }));
            for ((_, arg), hint) in named_args.iter().zip(named_hints.iter()).rev() {
                push_visit(work, Rc::clone(arg), env.clone(), hint.clone(), fuel);
            }
            for (arg, hint) in pos_args.iter().zip(pos_hints.iter()).rev() {
                push_visit(work, Rc::clone(arg), env.clone(), hint.clone(), fuel);
            }
        }

        // ── If / collection literals (WI-285) ───────────────────
        //    Native Build frames, like Apply / Constructor: push child
        //    Visits + a Build frame that drains their results. No
        //    re-entry into `type_check_node`, so a deep else-if chain
        //    (which nests in the else branch) stays on the heap.
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let condition = Rc::clone(condition);
            let then_branch = Rc::clone(then_branch);
            let else_branch = Rc::clone(else_branch);
            // WI-537 / proposal 050: fork Γ at the branch — the then-branch
            // assumes the condition, the else-branch its negation — so a guard
            // refutable from the flow (`if neq(b, 0) then div(a, b)`) finds the
            // fact in its env's Γ. The condition rides as a carrier-agnostic
            // `Value::Node` goal ("start raw", open Q A); it is read only by
            // the resolver bridge (WI-067 discharge), so narrowing is additive
            // — the branches' *types/effects* are unchanged from before.
            let cond_fact = Value::Node(Rc::clone(&condition));
            let then_env = env.with_flow(env.flow.assume(kb, cond_fact.clone()));
            let else_env = match negate_goal(kb, &cond_fact) {
                Some(neg) => env.with_flow(env.flow.assume(kb, neg)),
                None => env.clone(),
            };
            // Drain order [cond, then, else]: push reversed. The
            // condition is always `Bool` (no hint); both branches share
            // the if's `expected` (WI-270), now under their narrowed Γ.
            work.push(TypeWorkOp::Build(TypeBuildFrame::IfExpr {
                occ: Rc::clone(&occ),
                env: Rc::clone(&env.types),
                expected: expected.clone(),
            }));
            push_visit(work, else_branch, else_env, expected.clone(), fuel);
            push_visit(work, then_branch, then_env, expected, fuel);
            push_visit_no_hint(work, condition, env, fuel);
        }
        Expr::Proof {
            target,
            strategy,
            conclude,
            body,
            ..
        } => {
            // WI-538 / proposal 025 §"In-body and control-flow proofs":
            // discharge the proof's goal from the local Γ and, on
            // success, `assume` it into Γ for the continuation (the
            // proposal-050 in-body-`proof` modification rule, symmetric
            // to a call's `ensures`). The goal is the `conclude`
            // proposition in the Γ vocabulary, or — the short form — the
            // `target` rule as a 0-ary atom ([`in_body_proof_goal`]).
            let target = *target;
            let strategy = *strategy;
            let conclude = conclude.clone();
            let body = Rc::clone(body);
            // Built INSIDE the `derivation` arm: every other strategy
            // discards the goal, and building it interns the conclusion's
            // term twin into the hash-consed store for the KB's lifetime
            // (CLAUDE.md — transient terms are deliberately not interned).
            let discharged_goal: Option<Value> = match strategy {
                // Tier-A `by derivation`: prove inline over Γ ∪ KB under
                // the resolver's floundering guard.
                Some(strat) if kb.local_name_of(strat) == "derivation" => {
                    let goal = in_body_proof_goal(kb, target, conclude.as_ref());
                    prove_from_gamma(kb, &env.flow, &goal).then_some(goal)
                }
                // Tier-B (external) and open obligations contribute
                // nothing here: an external proof's conclusion may be
                // assumed only once the Γ-snapshot + prove-pass gate
                // verifies it (follow-on); until then it stays
                // conservatively undischarged — never a silent drop.
                _ => None,
            };
            let body_env = match discharged_goal {
                Some(goal) => env.with_flow(env.flow.assume(kb, goal)),
                None => env.clone(),
            };
            // Children order [conclude?, body] (matches `for_each_child`
            // / `reassemble_group`). The proof's type is the
            // continuation's; the goal is type-checked (no hint, like an
            // `if` condition) under the pre-proof env for well-formedness.
            work.push(TypeWorkOp::Build(TypeBuildFrame::ProofStmt {
                occ: Rc::clone(&occ),
                env: Rc::clone(&env.types),
                has_conclude: conclude.is_some(),
            }));
            push_visit(work, body, body_env, expected, fuel);
            if let Some(c) = conclude {
                push_visit_no_hint(work, c, env, fuel);
            }
        }
        Expr::ListLit(elems) => {
            let elems = elems.clone();
            // WI-270: an outer `List[T = X]` makes X each element's
            // expected, and the empty-list fallback. WI-20260826-7JDWY: read through
            // [`declared_element_type`], which is head-gated — see there.
            let element_hint = declared_element_type(kb, SeqLiteral::List, expected.as_ref());
            work.push(TypeWorkOp::Build(TypeBuildFrame::ListLit {
                occ: Rc::clone(&occ),
                env: Rc::clone(&env.types),
                element_hint: element_hint.clone(),
                count: elems.len(),
            }));
            for e in elems.iter().rev() {
                push_visit(work, Rc::clone(e), env.clone(), element_hint.clone(), fuel);
            }
        }
        Expr::SetLit(elems) => {
            let elems = elems.clone();
            let element_hint = declared_element_type(kb, SeqLiteral::Set, expected.as_ref());
            work.push(TypeWorkOp::Build(TypeBuildFrame::SetLit {
                occ: Rc::clone(&occ),
                env: Rc::clone(&env.types),
                element_hint: element_hint.clone(),
                count: elems.len(),
            }));
            for e in elems.iter().rev() {
                push_visit(work, Rc::clone(e), env.clone(), element_hint.clone(), fuel);
            }
        }
        Expr::TupleLit { positional, named } => {
            let positional = positional.clone();
            let named = named.clone();
            let named_names: Vec<Symbol> = named.iter().map(|(s, _)| *s).collect();
            // Drain order [pos…, named…]: push named reversed, then
            // positional reversed. Tuple fields take no hint.
            work.push(TypeWorkOp::Build(TypeBuildFrame::TupleLit {
                occ: Rc::clone(&occ),
                env: Rc::clone(&env.types),
                pos_count: positional.len(),
                named_names,
            }));
            for (_, e) in named.iter().rev() {
                push_visit_no_hint(work, Rc::clone(e), env.clone(), fuel);
            }
            for e in positional.iter().rev() {
                push_visit_no_hint(work, Rc::clone(e), env.clone(), fuel);
            }
        }

        // A surface `?x` whose name matches an in-scope binding (param /
        // let / lambda / match) *refers to* that binding — the same lookup
        // the `Ident` path does via `check_bare_ref`. WI-279: this is what
        // gives a value-receiver `?x.method()` a concrete type to dispatch
        // on (`?xs: List[Int]` ⇒ `min_sort` = List). Only `Var::Global`
        // carries a name; a genuinely-free `?x` (no matching binding), a
        // `DeBruijn`, or a `Rigid` falls back to a fresh type-var — not a
        // typer-level error, so the surrounding apply / let still
        // type-checks and declared signatures resolve it on the consumer
        // side.
        Expr::Var(var) => {
            // Exact-symbol lookup resolves any in-scope `?x` — let/lambda/match
            // binders share an intern with their body var, and WI-487 makes an
            // op-body `?b` referencing a param carry that param's own Symbol (the
            // key `env.bind_var` uses), so the param case now hits exactly too.
            // A genuinely-free `?x` matches nothing and gets a fresh type-var.
            let bound = match var {
                Var::Global(vid) => env.lookup_var(vid.name()),
                // WI-282: a RULE-body var is De Bruijn-encoded (rules carry no
                // lexical param env); its type comes from the rule's constraint
                // collection, installed on the env as `debruijn_types`. This is
                // what gives a rule-body `?x.field` / `?x.method(...)` receiver a
                // concrete sort to dispatch on — the op-body path's `lookup_var`
                // peer. A free body var (no constraint) misses and gets a fresh
                // type-var, as a free op-body `?x` does.
                Var::DeBruijn(idx) => env.lookup_debruijn(*idx),
                _ => None,
            };
            // WI-20260904-50B2K part (c), step 2 — THE SAME ELIMINATION AS
            // `check_bare_ref`'s, through the one owner. `?g` and `g` name one binding; a ∀
            // that leaves only one of them gives one program two verdicts.
            let bound = match bound {
                Some(t) => {
                    let name = match var {
                        Var::Global(vid) => Some(vid.name()),
                        _ => None,
                    };
                    match eliminate_env_schema(kb, solving, name, occ_span, t) {
                        Ok(t) => Some(t),
                        Err(e) => {
                            results.push(Err(e));
                            return;
                        }
                    }
                }
                None => None,
            };
            let ty = bound.unwrap_or_else(|| {
                // WI-20260904-50B2K — DELIBERATELY STILL A `type_var`, FLIPPED AND MEASURED
                // INERT, and this mint is the census row that closes the column.
                //
                // MEASURED: 22,798 reaches across the whole `wi_tests` binary — the most
                // heavily driven of the five — and the flip to the engine's own variable
                // changed NOTHING. 4127/0, and byte-identical diagnostics on every shape
                // built to tell them apart: a free `?x` at two INCOMPATIBLE slots
                // (`addI(takes_int(?x), takes_str(?x))`), at one slot, as a dot receiver,
                // and in an entity field all load under both.
                //
                // AND THE REASON IS STRUCTURAL, NOT A THIN CORPUS. Neither form can ever
                // REFUSE: the inert one is compatible-with-anything so a check that RUNS on
                // it accepts, and a variable is NON-GROUND so the check is WITHHELD. The
                // only way the flip changes an answer is if something BINDS the variable
                // and a later reader sees the binding — which needs a σ or an env SHARED
                // between this mint and that reader. A free `?x`'s type is read once per
                // use: `validate_arg_against_param`'s σ is the callee instantiation and is
                // discarded with the call, so nothing carries a binding from one use to the
                // next. That is exactly what a binder HAS (its type goes into the body's
                // env and the body reads it in the same pass), and it is why `?param` and
                // `?pat` moved and these two did not.
                //
                // SO THE COLUMN'S PREDICATE WAS NEVER "is this to be inferred" — it is
                // "does a later reader in the SAME PASS see what this mint produced".
                // Flipping this needs the inference-state thread the ticket names in its
                // wi342 discussion, which is part (c)'s ground and not a re-spelling here.
                let fresh = kb.intern("?logical_var");
                Value::term(kb.make_type_var(fresh))
            });
            results.push(Ok(TypeResult::pure_value(
                ty,
                unwrap_env(env),
                Rc::clone(&occ),
            )));
        }

        // WI-279: a value-receiver dot form `?x.member(args)` / `?x.member`.
        // Type the receiver + args (no hint), then a `DotApply` Build frame
        // resolves `member` against the receiver's least sort and synthesizes
        // the dispatched call. Running here (in the typer, env in hand) is what
        // lets a receiver referencing a let/lambda/match-bound local resolve.
        Expr::DotApply {
            receiver,
            name,
            pos_args,
            named_args,
        } => {
            let member = *name;
            let receiver = Rc::clone(receiver);
            // WI-443: only the receiver is pre-typed (its sort drives the
            // dispatch); the raw arg occurrences ride on the frame and are
            // typed exactly once — with the callee's param hints — inside
            // the synthesized call.
            work.push(TypeWorkOp::Build(TypeBuildFrame::DotApply {
                occ: Rc::clone(&occ),
                member,
                pos_args: pos_args.clone(),
                named_args: named_args.clone(),
                env: env.clone(),
                expected,
                fuel,
                pos,
            }));
            push_visit_no_hint(work, receiver, env, fuel);
        }
        // Post-elaboration forms — emitted by req_insertion, not the
        // surface typer.
        Expr::HoApply { .. }
        | Expr::Instantiation { .. }
        | Expr::ApplyWithin { .. }
        | Expr::HoApplyWithin { .. }
        | Expr::ConstructorWithin { .. }
        | Expr::LambdaWithin { .. }
        | Expr::RequirementAtSort { .. }
        | Expr::Dictionary { .. }
        | Expr::Bottom => results.push(Err(TypeError::BottomExpr { span: occ_span })),
    }
}

/// WI-283: reassemble `occ` from the children's (possibly-rewritten)
/// `TypeResult.node`s — supplied as the node's child results in
/// `for_each_child` source order, all `Ok` — returning `occ` unchanged
/// (same `Rc`) when no child moved. The mechanism that makes the typer
/// *tree-producing*: a `@[simp]` rewrite below a node propagates up as the
/// ancestor chain is rebuilt.
pub(super) fn reassemble_children(
    occ: &Rc<NodeOccurrence>,
    child_results: &[&Result<TypeResult, TypeError>],
) -> Rc<NodeOccurrence> {
    let nodes: Vec<Rc<NodeOccurrence>> = child_results
        .iter()
        .map(|r| Rc::clone(&r.as_ref().expect("reassemble_children: Ok child").node))
        .collect();
    crate::kb::simp_rewrite::reassemble(occ, &nodes)
}

/// [`reassemble_children`] for a contiguous slice of child results (the
/// `for_each_child`-ordered `group` the wrapper frames drain). WI-408:
/// unconditional — the typer itself produces rewrites (`some(...)` coercion
/// insertion), not just `@[simp]` firings, so a rewritten child must always
/// propagate; `reassemble`'s ptr-eq short-circuit keeps the unchanged case
/// allocation-free.
pub(super) fn reassemble_group(
    occ: &Rc<NodeOccurrence>,
    child_results: &[Result<TypeResult, TypeError>],
) -> Rc<NodeOccurrence> {
    let refs: Vec<&Result<TypeResult, TypeError>> = child_results.iter().collect();
    reassemble_children(occ, &refs)
}

/// WI-283: reassemble a `Match` from its (rewritten) scrutinee + branch
/// bodies. Match needs its own path because its **guards are not
/// typed/visited** (so they have no result `node`); they're re-read from
/// `occ` unchanged and interleaved after each body, reproducing
/// `for_each_child(Match)` order ([scrutinee, pattern, body, guard?, …])
/// for the shared `reassemble`. WI-318: `pattern` is a Pattern-kind
/// occurrence child. WI-803: patterns are no longer passed through identical —
/// `branch_patterns` carries each one as `bind_and_label_pattern` returned it,
/// relabelled where a `case (p, q) ->` binder list met a known named-tuple
/// scrutinee. Re-reading `branch.pattern` off `occ` here would drop those labels
/// and send the arm back to destructuring by slot.
/// `branch_results` are the branch-body `TypeResult`s (all `Ok`), in
/// branch order. Returns `occ` unchanged when nothing moved.
pub(super) fn reassemble_match(
    occ: &Rc<NodeOccurrence>,
    scr_node: &Rc<NodeOccurrence>,
    branch_patterns: &[Rc<NodeOccurrence>],
    // WI-20260827-EJ5F5: the re-pointed guards, in branch order. Handed in rather than
    // re-read off `occ` for the same reason `branch_patterns` is.
    branch_guards: &[Option<Rc<NodeOccurrence>>],
    branch_results: &[Result<TypeResult, TypeError>],
) -> Rc<NodeOccurrence> {
    let branches = match occ.as_expr() {
        Some(Expr::Match { branches, .. }) => branches,
        _ => return Rc::clone(occ),
    };
    let mut children: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(1 + branch_results.len() * 3);
    children.push(Rc::clone(scr_node));
    debug_assert_eq!(
        branch_patterns.len(),
        branches.len(),
        "WI-803: one relabelled pattern per branch",
    );
    debug_assert_eq!(
        branch_guards.len(),
        branches.len(),
        "WI-20260827-EJ5F5: one re-pointed guard slot per branch",
    );
    for (((branch, pattern), guard), r) in branches
        .iter()
        .zip(branch_patterns.iter())
        .zip(branch_guards.iter())
        .zip(branch_results.iter())
    {
        // WI-318: emit pattern in for_each_child order.
        children.push(Rc::clone(pattern));
        children.push(Rc::clone(
            &r.as_ref().expect("reassemble_match: Ok body").node,
        ));
        // WI-20260827-EJ5F5: `branch.guard` decides only WHETHER this arm has a guard
        // slot — `for_each_child` emits one exactly when the written branch has one — and
        // `branch_guards` decides WHAT goes in it.
        if branch.guard.is_some() {
            if let Some(g) = guard {
                children.push(Rc::clone(g));
            }
        }
    }
    crate::kb::simp_rewrite::reassemble(occ, &children)
}

/// WI-283: try firing a `@[simp]` rule at `node` — the typer's Apply/Constructor
/// firing site. Reuses `simp_rewrite`'s matcher + RHS builder, including its
/// type-directed guard ([`simp_fire_guard_holds`]): `node`'s children are already
/// typed (bottom-up), so their `min_sort` is available for the guard there.
///
/// WI-757: `Err` is a macro-RHS lowering whose MACRO rejected the occurrences it
/// was handed. The caller turns it into a [`TypeError::MacroRejected`] at this
/// redex via [`macro_rejection_error`] and abandons the node — so one rejection
/// yields exactly one error, and a fire that instead succeeds leaves nothing
/// behind that could go stale. `try_fire_dot_rule` is the sibling site under the
/// same contract.
pub(super) fn fire_simp(
    kb: &mut KnowledgeBase,
    node: &Rc<NodeOccurrence>,
    rids: &[RuleId],
) -> Result<Option<Rc<NodeOccurrence>>, crate::kb::simp_rewrite::MacroRejection> {
    crate::kb::simp_rewrite::try_fire(kb, node, rids)
}

/// WI-757: render a carried-out [`MacroRejection`](crate::kb::simp_rewrite::MacroRejection)
/// as the typer's error, located at the offending sub-expression the macro named —
/// falling back to `redex`, the node the rule fired on, when it named none.
pub(super) fn macro_rejection_error(
    rejection: crate::kb::simp_rewrite::MacroRejection,
    redex: &Rc<NodeOccurrence>,
) -> TypeError {
    // WI-745: a `TypeError`'s span is a bare byte range; the FILE it indexes into is
    // stamped separately, per operation body (`check_operation_bodies` tags each error
    // with `op.body_node.span.source`). So a span from another file would render a
    // `path:line:col` that is silently wrong. Every rejection today names an occurrence
    // descended from the macro's own arguments — same file as the redex by
    // construction — and this makes that a CHECKED precondition rather than a latent
    // assumption, for the `reject(message, at:)` op 043.1 §7 plans.
    debug_assert!(
        rejection.span.is_none_or(|s| s.source == redex.span.source),
        "WI-757: macro `{:?}` rejected at a span from another file than the redex — \
         the load error would resolve it against the redex's file and render the \
         wrong line:col",
        rejection.macro_name,
    );
    TypeError::MacroRejected {
        span: Some(rejection.span.map_or(redex.span.span, |s| s.span)),
        macro_name: rejection.macro_name,
        detail: rejection.detail,
    }
}

/// WI-374 (kernel-language §8.1 expansion, let-annotation site): rewrite a bare
/// or PARTIAL parametric-sort annotation to KEEP the value's inferred
/// parameters instead of erasing them. Annotation-written bindings stay
/// authoritative; every param the annotation leaves unwritten takes the
/// value's inferred binding: `let s : Stream = List.iterator(xs)` binds `s` at
/// `Stream[T = Int64, E = {}]`, and `let s : Stream[T = Int64] = …` keeps its
/// written `T` while taking `E` from the value. A defined-type / alias
/// annotation resolves to its shape FIRST (WI-381), so its definition-fixed
/// bindings count as written.
///
/// This is the site-scoped form of §8.1: the annotation occurrence is the
/// per-occurrence identity, and the value's type supplies the bindings the
/// expansion's fresh vars would have unified against — no transient vars
/// needed. Returns `None` (annotation kept as written, today's behavior) when
/// there is nothing to keep: a non-sort-application annotation, a value type
/// carrying no parameters, or a CROSS-SORT pair (the value's base merely
/// *provides* the annotated spec — enrichment there must read the provider
/// fact's view, not name-aligned params; conformance was already checked by
/// the caller either way).
pub(super) fn unroll_annotation_with_inferred(
    kb: &mut KnowledgeBase,
    ann: &Value,
    vty: &Value,
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Option<Value> {
    // Value side FIRST — cheap (no KB scan): nothing to keep unless the value's
    // type is a sort application carrying bindings. The annotation side may pay
    // a SortAlias fact scan (`resolve_alias_shape`), so it only runs after this
    // gate — `let n : Int64 = 5` never reaches it.
    let (v_base, v_bindings) = match extract_type(kb, vty) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return None,
    };
    // Annotation side: bare ref (alias-shape resolved, WI-381) or partial
    // application; its bindings seed the merge as the written-authoritative set.
    let (ann_base, mut merged) = sort_application_parts(kb, ann)?;
    if kb.canonical_sort_sym(ann_base) != kb.canonical_sort_sym(v_base) {
        return None;
    }
    let mut changed = false;
    for (p, v) in &v_bindings {
        // WI-764: locate the annotation's slot for this param by the shared key rule, NOT
        // by raw identity. The two sides are the SAME sort (checked just above) but key one
        // slot differently — the annotation writes a BARE `E`, the value carries the
        // canonical `anthill.prelude.Relation.E`. Raw identity missed, so the value's
        // binding fell to the `None` arm and was PUSHED: `let r : Relation[E = {Error}] =
        // person_row` built `Relation[T = .., E = .., E = ..]`, one slot bound twice, in
        // ordinary source. Measured, not hypothesised. A duplicate-label type then makes
        // every later lookup for that slot depend on which copy interned first.
        // Derived via `for_bases` rather than hard-coded `Label`: the two are the same sort
        // only because of the early return above, and this function's own doc contemplates
        // relaxing that for the cross-sort provider case — deriving the mode keeps it
        // tracking the gate instead of silently becoming a cross-sort label match.
        let mode = BindingKeyMatch::for_bases(kb, ann_base, v_base);
        let slot = binding_index_for_param(kb, &merged, *p, mode).map(|i| &mut merged[i]);
        match slot {
            // A written ANONYMOUS wildcard (`Stream[T = ?]`) pins nothing —
            // the value's inferred binding replaces it instead of being
            // erased under it (the wildcard already passed conformance
            // against anything). A NAMED var (`Pair[A = ?t, B = ?t]`) is NOT
            // replaced: independently overwriting each slot would silently
            // lose the same-var tie the user wrote.
            // WI-1063: via the shared [`value_is_anonymous_wildcard`], which is the one owner
            // of "the author wrote `?` here". It reads the PARSER's carrier as well as the
            // `type_var` one this site used to test alone — a widening, and a measured one:
            // the full workspace suite is green either way, so no delivered program reaches
            // this site with an anonymous `Var::Global` annotation. Shared anyway, because a
            // second reader of the convention is how the two spellings drift apart.
            Some(slot) if value_is_anonymous_wildcard(kb, &slot.1) => {
                slot.1 = v.clone();
                changed = true;
            }
            Some(_) => {}
            None => {
                merged.push((*p, v.clone()));
                changed = true;
            }
        }
    }
    if !changed {
        return None;
    }
    let base = kb.make_sort_ref(ann_base);
    Some(parameterized_value(kb, base, &merged, span, owner))
}

/// WI-374: read a type as a SORT APPLICATION — `(base sort, written
/// bindings)` — resolving a defined-type / alias to its shape first (WI-381),
/// so a structured alias contributes its definition-fixed bindings and a bare
/// alias OF a bare sort reports the UNDERLYING base (`sort MyList = List`
/// participates like `List`). `None` when the type is not a sort application
/// (arrow, tuple, projection, var, …). Shared by the let-annotation merge and
/// the signature expansion so WI-381 alias semantics live in one place.
pub(super) fn sort_application_parts(
    kb: &mut KnowledgeBase,
    ty: &Value,
) -> Option<(Symbol, Vec<(Symbol, Value)>)> {
    if let Some(s) = extract_sort_ref_sym(kb, ty) {
        // A parametric sort is never an alias: a non-empty memoized param set
        // (WI-424 cache) skips the alias-shape fact scans on the hot path.
        if !sort_type_params_as_pairs(kb, s).is_empty() {
            return Some((s, vec![]));
        }
        match resolve_alias_shape(kb, s) {
            Some(shape) => match extract_type(kb, &TermIdView(shape)) {
                TypeExtractor::Parameterized { base, bindings } => Some((base, bindings)),
                _ => Some((
                    extract_sort_ref_sym(kb, &TermIdView(shape)).unwrap_or(s),
                    vec![],
                )),
            },
            None => Some((s, vec![])),
        }
    } else {
        match extract_type(kb, ty) {
            TypeExtractor::Parameterized { base, bindings } => Some((base, bindings)),
            _ => None,
        }
    }
}

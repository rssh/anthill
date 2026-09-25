//! `check_apply_iter` — typing an application — and the rewrite records it leaves.

use super::*;

pub(super) fn check_apply_iter(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    // WI-067 (proposal 048 §"Typer delta"): the local-interpretation Γ at the
    // call site, used to constructively refute a guarded effect's guard. Kept
    // distinct from `env` (a `TypingEnv`, types only) so the discharge reads the
    // logical fact channel the `if`/`match`/proof narrowing populates (050).
    flow: &FlowEnv,
    occ: &Rc<NodeOccurrence>,
    fn_sym: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
    span: Option<Span>,
    expected: Option<Value>,
    // WI-1104: WHERE this call is written ([`NodePos`]) — the GOAL-vs-VALUE distinction
    // the functional-relation arity + 1 is scoped by. It rides the work-stack frame, not
    // `env`: see [`NodePos`] for why a per-rule env flag separates nothing.
    pos: NodePos,
    // WI-20260904-50B2K part (c): the walk's inference state — where this call's solutions
    // are REPORTED (so a frame that minted a type BEFORE the call ran can read what the
    // call decided) and where an abstract dispatch on a lambda binder is DEFERRED.
    // `None` from the caller that is not on a written body's walk —
    // `build_relation_projection` types a SYNTHESIZED projection shape, so nothing
    // downstream would read what it solved.
    mut solving: Option<&mut WalkSolutions>,
) -> Result<TypeResult, TypeError> {
    // Surface any sub-expression failure before continuing. Aggregate
    // sibling errors so a multi-arg call reports every ill-typed arg
    // in a single diagnostic rather than the first.
    collect_arg_errors(pos_results.iter().chain(named_results.iter()))?;

    // WI-839: only an OPERATION has a type-parameter list a call-site bracket could
    // bind, and `seed_op_type_args` — the one place a bracket is honoured — runs on
    // that path alone. So refuse the bracket for every other callee class HERE, ABOVE
    // the early returns rather than at each of them: this function returns early for a
    // constructor symbol, for the WI-714 applied rule citation, and further down for a
    // function VALUE, and MEASURED, guarding only the function-value path left an
    // applied rule citation (`p[Bogus = Int64](1)`, `p[Int64, Int64, Int64](1)`)
    // loading clean — the same silent drop one classification step over. The classes
    // are disjoint (`kind_of` gives a symbol ONE kind), so "not an operation" is
    // exactly "will not reach Path 1". The occurrence read comes first so a call
    // without a bracket — every call in practice — pays only a match, not a lookup.
    if call_type_args_of(occ).is_some() && lookup_operation_info_full(kb, fn_sym).is_none() {
        return Err(TypeError::TypeArgsOnNonOperation {
            span,
            callee: fn_sym,
        });
    }

    // Materializer fallback: bare-functor constructor invocations land
    // in `Apply`; route them through the constructor checker so
    // type-param inference still fires.
    //
    // WI-1056 — the question is [`KnowledgeBase::is_entity_constructor`]'s, not
    // [`KnowledgeBase::is_constructor_symbol`]'s, and the difference is exactly this
    // arm's population. `is_constructor_symbol` answers "is a CONSTRUCTOR OF some
    // enclosing sort", which WI-926 deliberately made FALSE for an eponymous `sort E {
    // entity E(…) }` (it is not a constructor OF anything — it IS the sort) and which
    // was never true for a free-standing `entity E(…)`. `is_entity_constructor` is the
    // one owner of "does an APPLICATION of this functor construct an entity value", and
    // this site is applied position — the exact reading its doc reserves for callers
    // like this one.
    //
    // THE OTHER PRODUCER already answers it that way and this one is its twin, which is
    // why the two must not diverge: the loader's `ApplyOrConstructor` drain builds an
    // `Expr::Constructor` off `is_entity_constructor`, so every expression the LOADER
    // walks (an operation body) never reaches here at all. A RULE BODY does not take
    // that drain — `build_body_atom_occurrence` hands an entity-headed atom to
    // `materialize_from_handle`, which builds a structural `Expr::Apply` for EVERY
    // domain `Term::Fn` — so this gate is the only thing that classifies it, and with
    // the narrow predicate a sort-nested `Q(a: 1)` typed while the eponymous `P(a: 1)`
    // beside it died as `UnknownApplyFunctor`.
    //
    // MEASURED, not predicted (WI-1043's widening is what made a rule body ask): `?p =
    // P(a: 1)` on `sort P { entity P(a: Int64) }` reported "unknown apply functor: P"
    // where the same construction in an OPERATION body loads clean, and the corpus
    // carried two — `Vec3(x: …)` inside an `=` goal at
    // `examples/webots-modelling/lf1/safety_common.anthill:236` (eponymous, from
    // `stdlib/anthill/geometry.anthill`) and `Pose(position: …)` at `safety_gps.anthill:154`
    // (free-standing). Both are programs that load and run today.
    if kb.is_entity_constructor(fn_sym) {
        return check_constructor_iter(
            kb,
            env,
            flow,
            fn_sym,
            pos_args,
            named_args,
            pos_results,
            named_results,
            span,
            expected,
            occ,
        );
    }

    // WI-759 — a desugared `field_access(receiver, "field")` used to need TWO early returns
    // HERE (`field_access_projection_type` re-deriving the field's type, and
    // `field_access_owning_ctor` re-checking WI-369 `internal` visibility), both keyed on
    // `field_access`'s own identity, because the reflect signature it was checked against
    // contradicted the node in all three positions: the receiver is an entity or named tuple
    // and `Term` is not a top type; the selector is a `String` constant, not a `Symbol`; the
    // result is the FIELD's type, not `Term`. It now takes ORDINARY op typing below, because
    // the signature no longer contradicts it — `field_access[R, Name](object: R, field:
    // String) -> FieldOf[T = R, Name = Name]` states the projection, and `FieldOf` reduces
    // at the same return-type normalization boundary `Concat` / `Without` reduce at. So the
    // rewrite is idempotent by construction rather than by a hatch that shadowed the
    // declaration. (The WI-506 effect re-key's own idempotency is in `stable_receiver_path`,
    // unchanged.)

    // WI-732 — a synthesized `project_run(r, <spec>)` PROJECTION call (the distribute-dot
    // `r.(f1, f2)`) used to need an early return HERE too, re-deriving its projected schema so
    // a re-visit would not widen to `project_run`'s nominal `-> Relation[T = r.T]`. It was the
    // LAST typer hatch keyed on a domain operation's identity (`fn_sym != project_run`), and
    // it existed only because the declared return named the UNPROJECTED schema. The signature
    // now states the projection — `project_run[Keep](r, spec) -> Relation[T = Project[T = r.T,
    // Keep = Keep], E = r.E]` — and `Project` reduces at the same return-type normalization
    // boundary `Concat` / `Without` / `FieldOf` reduce at, so the forward synthesis and a
    // later re-type are one decision procedure over one lookup ([`projection_columns`]) rather
    // than two that can drift.

    // WI-714 (proposal 052) — the APPLIED citation position: a rule NAME applied to
    // arguments (`queens(board)`, `queryTwoParams(x: 3)`) is a `Relation[T]` value
    // with the supplied columns bound (subtracted from the free columns → narrows T).
    // A rule is never an operation, so without this it would fall through Path 1 →
    // Path 3 and die as `UnknownApplyFunctor`. Eval re-derives via `kind_of(functor)`
    // (its `Expr::Apply` rule arm), the applied peer of `check_bare_ref`'s rule arm;
    // the value is pure to construct, so the apply's effects are its arguments' —
    // running the relation carries `{Error}` through the `provides` edge, not here.
    //
    // Gated to EXPRESSION context (`!in_rule_body`): inside a rule body a rule name
    // applied to arguments is a relational SUBGOAL (reached here only via
    // `dispatch_calls_in_occ` for a dot-bearing atom), never a `Relation` VALUE — the
    // value reading belongs to functional/operation code. In rule-body context this
    // falls through, preserving the pre-WI-714 behavior there.
    if !env.in_rule_body() && kb.cites_a_relation(fn_sym) {
        let ty = relation_reference_type_applied(
            kb,
            fn_sym,
            pos_args,
            named_args,
            pos_results,
            named_results,
            span,
            occ,
        )?;
        let mut effects: Vec<Value> = Vec::new();
        for r in pos_results.iter().chain(named_results.iter()).flatten() {
            merge_effects_into(kb, &mut effects, &r.effects);
        }
        return Ok(TypeResult {
            ty,
            env: env.clone(),
            effects,
            node: Rc::clone(occ),
        });
    }

    // WI-898 — an EQUATION-INTRODUCED functor applied, which the arm above declined
    // because it owns no clauses (an equation's live under the `eq`/`unify`
    // connective). Reaching here at all means the `@[simp]` rewriter already declined
    // the call, which IS the diagnosis — so this is a refusal that says so, rather
    // than a fall-through to `UnknownApplyFunctor`'s much vaguer "unknown functor"
    // about a name that resolved perfectly well.
    //
    // Sits AFTER the relation arm, so a name its scope also gave a predicate clause
    // takes the relational reading it has really got. Shares the `!in_rule_body`
    // gate for the reason it exists there: in a rule body the application is a term
    // in a goal, not a citation in functional code.
    if !env.in_rule_body() && kb.has_kind(fn_sym, crate::intern::SymbolKind::EquationFunctor) {
        let census = crate::kb::simp_rewrite::equation_clause_census(kb, fn_sym);
        return Err(TypeError::UnreducedEquationFunctor {
            span,
            functor: fn_sym,
            census,
        });
    }

    // WI-1056 — the same question ASKED IN A RULE BODY, where the answer is the same
    // ("this is an equation functor, not a call to type") but its consequence is not.
    // The gate above says a rule body must not report it; it did not say what happens
    // instead, and what happened was a fall-through to Path 3, refusing the node anyway
    // under a vaguer name. So the gate withheld one diagnostic and let a worse one
    // through — invisible while rule bodies went unchecked.
    //
    // MEASURED on `bool.anthill`'s `ite`, whose two `@[simp]` equations ARE its whole
    // definition ("no operation is the only correct form" — an operation would have to
    // take thunks, since the untaken branch must never evaluate). `rule clamp(?x, ?r) :-
    // ?r = ite(gte(?x, 0), ?x, 0)` reported "`ite` is a member of sort Bool, not in
    // scope as a bare name here": a misdiagnosis twice over, since the program imports
    // it and importing cannot help — the real reason is "not an operation".
    // `ordered.anthill` writes the same bare call in a rule HEAD, which this walk never
    // visits, so one expression was legal on one side of `:-` and refused on the other.
    //
    // STILL AN `Err`, and deliberately, though the rule-body policy will not report it
    // ([`dispatch_calls_in_occ`]'s exemption): failing here is what stops the ENCLOSING
    // atom's type-check, which is the pre-WI-1056 behaviour and the correct one. The
    // first cut returned `Ok` with a fresh type var instead, on the reasoning that
    // "unconstrained is the truthful answer" — and it was truthful and WRONG: with the
    // `=` goal's right-hand type unknown, `PartialEq.eq`'s carrier no longer pinned and
    // the atom was refused for AMBIGUOUS DISPATCH across all 11 `PartialEq` instances.
    // A type this typer cannot know must not be offered to a dispatch that needs it.
    //
    // NARROWER THAN ITS TWIN by one clause: an operation reading, if the symbol has one,
    // WINS. `SymbolKind` is a SET, so one name can carry both, and in a rule body such a
    // symbol reaches Path 1 today — this must not take that away.
    if env.in_rule_body()
        && kb.has_kind(fn_sym, crate::intern::SymbolKind::EquationFunctor)
        && lookup_operation_info_full(kb, fn_sym).is_none()
    {
        let census = crate::kb::simp_rewrite::equation_clause_census(kb, fn_sym);
        return Err(TypeError::UnreducedEquationFunctor {
            span,
            functor: fn_sym,
            census,
        });
    }

    // Path 1: known operation — unify args with params to instantiate type params
    if let Some(mut op) = lookup_operation_info_full(kb, fn_sym) {
        // WI-374 (§8.1, site-scoped): expand FOREIGN bare/partial parametric
        // sort applications in the callee's signature to per-call fresh-var
        // applications, so two foreign occurrences never alias and the
        // foreign sort's canonical vars are no longer touched by this call's
        // argument unification. Member self-sort refs are left bare — the §3
        // bullet-1 parametricity tie keeps riding the canonical channel
        // (`unify_parameterized_with_sort_ref` + the per-call subst).
        //
        // The expansion serves INFERENCE only: the WI-385 validation below
        // keeps checking each argument against the param type AS WRITTEN
        // (`written_params`) — an expanded param whose fresh var an
        // incompatible argument failed to bind is non-ground, and the
        // validation's groundness gate would silently skip the rejection
        // (`Function[Int64, Int64]` with open `E` vs a `String -> Bool`
        // argument must still be a loud mismatch).
        let written_params = op.params.clone();
        // WI-1063: computed ONCE, and via [`impl_parent_sort_of_op`]. Both polarities of the
        // §3 tie ask this one question — "is a reference to this sort the callee's OWN?" —
        // and until this hoist they asked it in two spellings: the parameter expansion here
        // read `kind_of`, which WI-956 exists to replace (a symbol's categories are a SET and
        // `kind_of` reports only the first-declared one), while the return opening below read
        // `has_kind`. On a §6.3 re-declared sort the two answered differently, and one gate
        // being wrong is a silent expansion of the callee's own parameters.
        let callee_parent_sort = impl_parent_sort_of_op(kb, fn_sym);
        {
            let callee_parent_canon = callee_parent_sort.map(|p| kb.canonical_sort_sym(p));
            for i in 0..op.params.len() {
                if let Some(exp) =
                    expand_foreign_sort_application(kb, &op.params[i].1, callee_parent_canon)
                {
                    op.params[i].1 = exp;
                }
            }
            // The RETURN is deliberately NOT expanded: a bare return is an
            // ERASED relationship (§5 — variables reconstruct nothing), and
            // carrying unbound fresh vars in `resolved_ret` would un-ground
            // the ARGUMENT side of a downstream WI-385 validation (silent
            // skip where bare was a loud mismatch) and stamp dangling vars
            // into annotated-let merges.
        }
        // WI-727 (proposal 056): fold any leftover named arguments into the `...args: R`
        // capture record, so everything below is the ORDINARY path — `args` matches the
        // capture parameter, `R` is inferred from the record's type, and the `Without`
        // reduction narrows the return schema. All three views are rewritten together (the
        // node's labels, the argument list, the typed results) so the node reorder for eval
        // stays consistent. `None` (no capture parameter, or an already-normalized call)
        // keeps the original borrows — the zero-cost common path.
        // WI-1100: the shape of the call AS WRITTEN, read before the rewrite below can
        // append its own argument. `capture_param` is the `...args` slot no caller names
        // and the rewrite fills; `source_args` is what the AUTHOR wrote. An arity
        // diagnostic must count in the source's currency: with the rewritten list,
        // `cap()` on `cap(x: Int64, ...rest: R)` reported "got 1 argument" about a call
        // with no arguments in it, against an "expected 2" the author can never write.
        let capture_param = kb.op_capture_param(fn_sym);
        let source_args = pos_args.len()
            + match capture_param {
                // The >99% path: no capture slot, so every label is the author's.
                None => named_args.len(),
                Some(c) => named_args
                    .iter()
                    .filter(|(label, _)| !same_label(kb, c, *label))
                    .count(),
            };
        let capture_rewrite = normalize_variadic_capture(
            kb,
            env,
            fn_sym,
            capture_param,
            &op.params,
            occ,
            pos_args,
            named_args,
            named_results,
        )?;
        let (occ, named_args, named_results): (
            &Rc<NodeOccurrence>,
            &[(Symbol, Rc<NodeOccurrence>)],
            &[Result<TypeResult, TypeError>],
        ) = match &capture_rewrite {
            Some(cr) => (&cr.occ, &cr.named_args, &cr.named_results),
            None => (occ, named_args, named_results),
        };
        let mut subst = Substitution::new();
        // WI-269 Phase D: explicit call-site `op[bindings]` bindings
        // seed the substitution first. Returns `NoSuchTypeParam` on
        // an unknown binding name.
        // WI-841: and returns what the bracket SELECTED (058 §4.2) — read below by
        // both dispatch routes, the spec-op one (`dispatch_spec_op_cached`) and the
        // Direct-call dictionary build (`build_concrete_dispatch_dict`).
        let selections = seed_op_type_args(kb, &mut subst, &op, occ, fn_sym, span)?;
        // WI-20260911-RS2G4 (058 rule 1, the SORT half of the BINDING) — and the
        // receiver bracket, which writes the SAME channel. See
        // [`seed_receiver_type_args`] for why it is here and not at the W6JH0 result arm
        // below: form (3) has to read as the callee bracket, including its diagnostics,
        // and a WRITTEN receiver must beat the WI-424 rigid fill immediately following.
        seed_receiver_type_args(kb, &mut subst, occ, callee_parent_sort, fn_sym, span)?;
        // WI-424: a SAME-SORT sibling call inside a member body shares the
        // enclosing instance's sort params — seed the callee's canonical param
        // vars with the body's rigids (the WI-392 skolems, extended to sort
        // params) BEFORE argument unification. The callee's signature references
        // the same canonical vars, so its return/effects then thread the
        // enclosing instance: `iterator(c)` inside `Iterable.find` returns
        // `Stream[Element, E]` at the body's rigids rather than dangling vars.
        // Within the sort's own definition this is exactly the parametricity tie
        // (type-parameter-scoping.md §3) — `C`/`Element`/`E` denote ONE instance
        // across all members; a different-instance argument is correctly
        // rejected against the rigid.
        if !env.enclosing_instance_param_rigids().is_empty() {
            let same_sort = impl_parent_of_op(kb, fn_sym)
                .zip(env.enclosing_sort())
                .is_some_and(|(callee_parent, enclosing)| {
                    kb.canonical_sort_sym(callee_parent) == kb.canonical_sort_sym(enclosing)
                });
            if same_sort {
                for (vid, rigid) in env.enclosing_instance_param_rigids().iter() {
                    if subst.resolve_as_value(*vid).is_none() {
                        subst.bind_term(kb, *vid, *rigid);
                    }
                }
            }
        }
        // WI-367: a self-receiver spec op consumed on a CONCRETE carrier takes
        // its element type-params from that carrier — the receiver argument is
        // the ground truth for the element. Bind them BEFORE the WI-270
        // expected-seeding below. Otherwise a caller's wrong return claim
        // (`drain(xs: List[Int]) -> List[String] = collect(xs)`) would let
        // `unify_types(op.return_type, expected)` pre-seed `Stream.T := String`,
        // after which the carrier pass (which only fills empty slots) skips and
        // the unsound element survives — `collect` over a `List[Int]` is
        // `List[Int]`, not the caller's `List[String]`. Binding from the carrier
        // first pins `Stream.T := Int`; the expected-seeding `unify_types` then
        // fails silently against the carrier-pinned slot for a differing claim
        // (it binds nothing and its boolean is already discarded) and only fills
        // the still-free params. `resolved_ret` therefore carries the carrier
        // element, and the outer return-type check rejects the differing
        // declared return. `carrier_bound` is reused below to gate the WI-357
        // effect-close, which the early bind would otherwise steal.
        let self_recv_spec = self_receiver_spec_sort(kb, &op, fn_sym);
        // WI-383 B: capture the CARRIER-PARAM provision (the `Iterable.find(c: C)` /
        // `ModifyRuntime.get(target: T)` shape — receiver typed by the spec's own carrier
        // param, not the spec sort) so the LATE ground-value bind below can reuse its
        // `view` without re-scanning the provider facts. Only when there is no
        // self-receiver (the two shapes are mutually exclusive).
        let carrier_param_info = if self_recv_spec.is_some() {
            None
        } else {
            carrier_param_receiver(kb, &op.params, fn_sym, pos_args, named_args, &|i, pname| {
                supplied_arg_type(kb, i, pname, pos_results, named_args, named_results)
            })
        };
        // WI-590 — the ENCLOSING SORT's `requires` clause licensing this call, when the
        // carrier-param classification declined. ONE lookup: the binder below and both
        // refusal arms read this, so the licence and the binding cannot disagree, and the
        // scan runs at most once per call.
        // `self_recv_spec.is_some()` FORCES `carrier_param_info` to None above, so testing
        // that alone would derive the licence from a carrier-param-typed parameter while
        // dispatch runs on the SELF receiver — suppressing the diagnostic for a receiver the
        // licence never examined (caught by review).
        let enclosing_requires_clause = if self_recv_spec.is_none() && carrier_param_info.is_none()
        {
            enclosing_requires_licensing_clause(
                kb,
                env,
                &op,
                fn_sym,
                named_args,
                pos_results,
                named_results,
            )
        } else {
            None
        };
        // WI-1027 — the ONE projection of that 7-tuple's carrier field, read by three
        // sites (the WI-496/598 abstract-spec deferral and both `statically_pinned_carrier`
        // calls). The tuple is positional and seven wide, so a `|(_, c, ..)|` pattern keeps
        // compiling with the WRONG element if a field is ever inserted before the carrier.
        let carrier_param_sym: Option<Symbol> = carrier_param_info.as_ref().map(|(_, c, ..)| *c);
        let carrier_bound = match self_recv_spec {
            Some(spec_sort) => {
                match receiver_carrier(kb, &op, spec_sort, named_args, pos_results, named_results) {
                    ReceiverCarrier::Concrete(recv) => bind_spec_params_from_carrier(
                        kb,
                        &mut subst,
                        &op,
                        spec_sort,
                        recv.sort,
                        named_args,
                        pos_results,
                        named_results,
                    ),
                    _ => false,
                }
            }
            // WI-424: no spec-sort-typed receiver — try the CARRIER-PARAM shape
            // (`Iterable.find(c: C, …)`): ground the spec's params (`Element`,
            // the written `E` row) from the concrete carrier's provision, with
            // the same bind-before-expected-seeding rationale as the arm above.
            None => match &carrier_param_info {
                Some((
                    spec_sort,
                    carrier_sym,
                    recv_ty,
                    view,
                    carrier_pvid,
                    _transitive,
                    recv_arg_sym,
                )) => bind_spec_params_from_carrier_param(
                    kb,
                    &mut subst,
                    *spec_sort,
                    *carrier_sym,
                    *carrier_pvid,
                    recv_ty,
                    view.clone(),
                    *recv_arg_sym,
                ),
                // WI-590: no carrier to read a provision from — the receiver is an
                // abstract sort PARAM (bare, or a spec view over one). Its members come
                // from the enclosing sort's own `requires Spec[C = P, …]` instead.
                None => bind_spec_params_from_enclosing_requires(
                    kb,
                    &mut subst,
                    enclosing_requires_clause.as_deref(),
                ),
            },
        };

        // WI-20260829-70XVH — the CALLEE's OWN type parameters, from the CALLEE's own
        // op-level `requires`. A DIFFERENT question from the three arms above and so an
        // unconditional pass rather than a fourth arm: those ask "what does the receiver's
        // carrier bind THE SPEC's parameters to" for a call that dispatches on a spec, and
        // are mutually exclusive by which shape the receiver has. This one asks what the
        // callee's clause determines about the callee's OWN parameters, which no spec-op
        // classification is about — the operation need not be a spec op, need not sit in a
        // parametric sort, and its clause names a spec nothing else here mentions.
        //
        // Placed HERE for WI-367's reason: above the `expected` seeding (a caller's return
        // claim is not evidence about the carrier) and below `seed_op_type_args` (a written
        // bracket outranks the clause). It reports NOTHING — unlike `carrier_bound`, nothing
        // downstream is gated on whether a clause supplied anything; the parameters it leaves
        // free reach `check_unconstrained_type_params` exactly as before.
        //
        // GATED on the callee declaring both, so the >99% of calls whose callee has neither
        // pay one pair of `is_empty()` reads and never build the argument-type table.
        if !op.type_params.is_empty() && !op.requires.is_empty() {
            // MATERIALIZED rather than passed as a closure, because the pass takes `&mut kb`
            // while [`supplied_arg_type`] reads it — and only here, so the >99% of calls the
            // gate above turns away never build it.
            let arg_tys: Vec<Option<Value>> = op
                .params
                .iter()
                .enumerate()
                .map(|(i, (pname, _))| {
                    supplied_arg_type(kb, i, *pname, pos_results, named_args, named_results)
                })
                .collect();
            bind_op_type_params_from_op_requires(kb, &mut subst, &op, fn_sym, &arg_tys);
        }

        // WI-379: synthesize from the ARGUMENTS first (the two loops below);
        // the caller-side `expected` is consulted only AFTER (moved below the
        // arg loops), so it fills still-free type params without overriding any
        // that an argument pinned.
        let mut arg_effects: Vec<Value> = Vec::new();
        let mut param_to_arg_sym: HashMap<Symbol, Symbol> = HashMap::new();
        // WI-506: EFFECTS-ONLY re-key additions for a field-projection argument.
        // `Cell.set(c.rep, …)` passes `c.rep`, which has no single value-ref sym, so
        // `param_to_arg_sym` skips it and the callee's `Modify[<param>]` would survive
        // un-re-keyed (a spurious "undeclared effect"). A `Modify` on a projection
        // argument coarsens to the projection's HEAD parameter (`Modify[c.rep]` is
        // covered by `Modify[c]`; proposal 037 §"Effect-row convention"), so record
        // param → head HERE — kept out of `param_to_arg_sym` because the head loses the
        // `.rep`, which a re-keyed RETURN type (where the exact projection matters, and a
        // sym cannot represent it) must not do.
        let mut param_to_arg_head: HashMap<Symbol, Symbol> = HashMap::new();
        // WI-20260823-4GBQV: the arguments that name NO PLACE — the population
        // [`unrekeyed_modify_argument`] judges, and the parameters the EFFECT re-key must
        // therefore skip. Recorded where the decision is made rather than recomputed
        // after, so the maps cannot disagree about which shapes count.
        //
        // NOT RARE, and saying otherwise misleads the next reader about the cost: every
        // non-variable argument lands here, a LITERAL included — `Cell.set(k, 1)` records
        // the `1`. So the check below runs on a large share of all calls, not a corner.
        // It stays cheap because it walks the callee's INCURRED effects and stops at the
        // first non-`Modify`; correctness does not depend on the population, only the
        // budget does. (`/code-review` caught the claim.)
        //
        // NOT A NARROWING OF `param_to_arg_sym`, which is read by the RETURN-type and
        // value-in-type re-keys too and asks a different question of the same argument:
        // `f(wrap)` genuinely passes `wrap`, and a return type mentioning that parameter
        // must still say so. Only the EFFECT map skips these — a `Modify` re-keyed onto a
        // name the declaration cannot spell (`Modify[T = wrap]`, over a field-bearing
        // constructor) leaves the program unwritable, which is the leak in another
        // spelling.
        let mut param_to_placeless_arg: HashMap<Symbol, Rc<NodeOccurrence>> = HashMap::new();
        // WI-376/398: only ops whose signature actually carries a projection pay for the
        // per-call elimination — the >99% that don't skip the param_to_arg_type clones
        // and the rewrite walk entirely. WI-398 adds the PARAMETER positions: a param
        // whose type projects another param (`check(s: State, k: s.provider.K)`).
        let params_have_projection = op
            .params
            .iter()
            .any(|(_, t)| value_contains_projection(kb, t));
        let op_has_projection = params_have_projection
            || value_contains_projection(kb, &op.return_type)
            || op.effects.iter().any(|e| value_contains_projection(kb, e));
        // WI-20260909-S8CBV — the REQUIRES chain is a fourth projection-bearing position,
        // and it was not in the gate above. `operation pick(x: Box) requires Desc[T = x.E]`
        // carries no projection in a param, the return or an effect, so `op_has_projection`
        // is FALSE for it and `param_to_arg_type` stayed EMPTY — leaving
        // [`build_op_scoped_dicts`] unable to tell a projection that GROUNDS at this call
        // from one that does not, which is the whole of the verdict it now makes.
        //
        // A SEPARATE FLAG, not a widening of `op_has_projection`, because that one gates a
        // SECOND thing: it SKIPS the ordinary argument/parameter unification for a
        // projection-bearing PARAMETER (the branch just below). A requires-only projection
        // must not move that branch — the parameters are ordinary and must unify as they
        // always did.
        // READ OFF THE NORMALIZED CHAIN, not `op.requires`, because the CONSUMER does.
        // `build_op_scoped_dicts` δ-grounds `op_dict_entries(...).op_entries()`, whose
        // spec is the normalized form; asking the DECLARED clause list here let the two
        // disagree, and the disagreement is not symmetric — a projection present only in
        // the normalized entry leaves this map EMPTY, δ is skipped, the projection
        // survives, and the new refusal fires on a program that should load. One list,
        // both readers: the WI-1033 discipline `build_op_scoped_dicts`' own header cites.
        // Found by `/code-review`.
        let requires_have_projection = op_dict_entries(kb, fn_sym)
            .op_entries()
            .iter()
            .any(|e| value_contains_projection(kb, &e.spec));
        // WI-20260921-EE0EP — AND A PARAM-DERIVED SLOT, for the same reason S8CBV added the
        // chain: this map IS the channel. A `FromParam` slot is filled by READING the
        // argument's type ([`param_slot_witness`]), so an empty map here is not a slower
        // path, it is no supply at all — and an unsupplied slot that still CONSTRUCTS is
        // the silent rival WI-1094 refused. Measured as exactly that: the subject program
        // loaded and answered `false` at BOTH rival orderings before this flag existed.
        let needs_param_arg_types =
            op_has_projection || requires_have_projection || op_has_param_derived_slot(kb, fn_sym);
        // WI-714 / WI-727: does the RETURN type write a type constructor (`Concat`,
        // join's schema merge; `Without`, fix's schema drop)? A per-op gate (over the
        // declared signature, like `op_has_projection`) — ONE traversal for both — so only a
        // signature that actually reduces a schema pays for the reduction at each call.
        let op_return_ctors = return_reducible_ctors(kb, &op.return_type);
        // Each param symbol → the inferred type of the argument bound to it, so a
        // projection `param.M` in the return / effects / a LATER param can read the
        // receiver's actual per-call type (the synthesis-time discharge point).
        // Populated only when the op has a projection.
        let mut param_to_arg_type: HashMap<Symbol, Value> = HashMap::new();
        // WI-329: (declared callback param type, actual argument type) per callable
        // parameter — the input to `infer_discharged_row_tails`, which runs after BOTH
        // arg loops because a row tail's lower bound is the UNION over every parameter
        // naming it. Empty for an op with no type parameters (the gate at each push).
        let mut callback_pairs: Vec<(Value, Value)> = Vec::new();
        // WI-20260827-1F0QP: the parameter each positional argument fills, from the one
        // owner ([`positional_param_indices`]) that `bind_call_arguments` and
        // `reorder_named_args_in_apply` also read. `op.params` is the inference-expanded
        // list and `written_params` its clone, so ONE index serves both loops below.
        //
        // The identity for a call with no labels, which is nearly every call; what it
        // changes is the MIXED one, whose positional arguments rank among the parameters
        // the labels did not take. Reading `params.get(i)` there checked an argument
        // against one parameter while the runtime bound it to another.
        let pos_call_params = positional_param_indices(kb, &op.params, pos_args.len(), named_args);

        for (i, arg_occ) in pos_args.iter().enumerate() {
            if let Some(arg_var_sym) = extract_var_ref_sym_node(arg_occ) {
                if let Some((param_sym, _)) = pos_call_params[i].and_then(|p| op.params.get(p)) {
                    param_to_arg_sym.insert(*param_sym, arg_var_sym);
                    // WI-20260823-4GBQV: the EFFECT re-key must not mint a label the
                    // DECLARATION cannot spell. See `param_to_placeless_arg`.
                    if kb.is_unplaceable_constructor(arg_var_sym) {
                        param_to_placeless_arg.insert(*param_sym, Rc::clone(arg_occ));
                    }
                }
            } else if let Some((param_sym, _)) = op.params.get(i) {
                // WI-506: a field-projection argument (`s.rep`) — record param → head
                // for the effects-only re-key (see `param_to_arg_head`). WI-20260823-4GBQV
                // adds the nullary-constructor argument (`set(counter(), n)`) through the
                // same map; [`arg_place_head`] is the one reader of both shapes.
                match arg_place_head(kb, arg_occ) {
                    Some(head) => {
                        param_to_arg_head.insert(*param_sym, head);
                    }
                    None => {
                        param_to_placeless_arg.insert(*param_sym, Rc::clone(arg_occ));
                    }
                }
            }
            if let Ok(ref arg_result) = pos_results[i] {
                // WI-341 Stage A: the param type is `Value` (`Value::TermView`),
                // unified carrier-agnostically — no `TermIdView` wrap.
                if let Some((param_sym, param_type)) =
                    pos_call_params[i].and_then(|p| op.params.get(p))
                {
                    // WI-398: a param whose declared type IS / CONTAINS a projection
                    // (`k: s.cell.T`) cannot be unified against its raw `ExprCarried` —
                    // the receiver param's type-args are not yet projected, and an
                    // unbound arg-var must never bind to a projection. Defer it to the
                    // post-synthesis elimination pass below; the argument type is still
                    // recorded so a LATER param projecting THIS one can read it.
                    if !(op_has_projection && value_contains_projection(kb, param_type)) {
                        let before = subst.clone();
                        let unified = unify_types(kb, &mut subst, &arg_result.ty, param_type);
                        // WI-20260904-50B2K part (c) — REPORT HERE, not at a return.
                        // `check_apply_iter` has 22 exits and an argument's solving is
                        // complete the moment its unification is: reporting at one exit
                        // measured EMPTY at the reader, because `twice(v)` leaves by a
                        // different one. This is also the exact site the probe saw
                        // `?param` bound at, so it is where the population lives rather
                        // than merely where a `defer` would have run.
                        report_walk_solutions(kb, solving.as_deref_mut(), &before, &subst, unified);
                    }
                    if needs_param_arg_types {
                        param_to_arg_type.insert(*param_sym, arg_result.ty.clone());
                    }
                    // WI-329: the (declared, actual) pairs the discharge inference reads
                    // after BOTH loops. Recorded only for a CALLABLE parameter of an op
                    // that declares type params — the population a row tail can live in —
                    // so an ordinary call allocates nothing.
                    if !op.type_params.is_empty() && type_head_is_callable(kb, param_type) {
                        callback_pairs.push((param_type.clone(), arg_result.ty.clone()));
                    }
                }
                merge_effects_into(kb, &mut arg_effects, &arg_result.effects);
            }
        }

        for (i, (arg_name, arg_occ)) in named_args.iter().enumerate() {
            // WI-426: match the label to its param by name, then key the per-call
            // maps by the PARAM symbol (not the use-site label symbol) so the
            // positional loop above, the projection eliminator, and param_to_arg_sym
            // all agree on one key.
            let matched =
                match_named_arg_param(kb, &op.params, *arg_name).map(|(s, t)| (*s, t.clone()));
            if let Some(arg_var_sym) = extract_var_ref_sym_node(arg_occ) {
                if let Some((param_sym, _)) = &matched {
                    param_to_arg_sym.insert(*param_sym, arg_var_sym);
                    // WI-20260823-4GBQV — see the positional loop.
                    if kb.is_unplaceable_constructor(arg_var_sym) {
                        param_to_placeless_arg.insert(*param_sym, Rc::clone(arg_occ));
                    }
                }
            } else if let Some((param_sym, _)) = &matched {
                // WI-506: a field-projection named argument — effects-only head re-key.
                // WI-20260823-4GBQV: a nullary-constructor named argument rides it too.
                match arg_place_head(kb, arg_occ) {
                    Some(head) => {
                        param_to_arg_head.insert(*param_sym, head);
                    }
                    None => {
                        param_to_placeless_arg.insert(*param_sym, Rc::clone(arg_occ));
                    }
                }
            }
            if let Ok(ref arg_result) = named_results[i] {
                if let Some((param_sym, param_type)) = &matched {
                    // WI-398: defer a projection param's unify (see the positional loop).
                    if !(op_has_projection && value_contains_projection(kb, param_type)) {
                        let before = subst.clone();
                        let unified = unify_types(kb, &mut subst, &arg_result.ty, param_type);
                        // WI-20260904-50B2K part (c) — REPORT HERE, not at a return.
                        // `check_apply_iter` has 22 exits and an argument's solving is
                        // complete the moment its unification is: reporting at one exit
                        // measured EMPTY at the reader, because `twice(v)` leaves by a
                        // different one. This is also the exact site the probe saw
                        // `?param` bound at, so it is where the population lives rather
                        // than merely where a `defer` would have run.
                        report_walk_solutions(kb, solving.as_deref_mut(), &before, &subst, unified);
                    }
                    if needs_param_arg_types {
                        param_to_arg_type.insert(*param_sym, arg_result.ty.clone());
                    }
                    // WI-329 — see the positional loop.
                    if !op.type_params.is_empty() && type_head_is_callable(kb, param_type) {
                        callback_pairs.push(((*param_type).clone(), arg_result.ty.clone()));
                    }
                }
                merge_effects_into(kb, &mut arg_effects, &arg_result.effects);
            }
        }

        // WI-398: CROSS-PARAMETER projection. With every argument now synthesized
        // (`param_to_arg_type` fully populated above), discharge each projection-bearing
        // PARAMETER type by projecting the receiver param's argument type — the same
        // elimination the return / effects positions use (below). A projection reads the
        // receiver's ARGUMENT type (recorded above; a concrete value, hence ground), so
        // the discharge is order-independent here; a CYCLIC projection signature
        // (`f(a: b.T, b: a.T)`) has no synthesis order and is rejected at LOAD
        // (`check_operation_bodies`), so what reaches a call is always a DAG. The
        // resolved type is unified against the argument and recorded so the WI-385
        // VALIDATION below checks the argument against `String`, not the un-eliminated
        // `s.cell.T`. A projection that cannot resolve (abstract receiver, missing
        // member) is a loud error here, never a silent skip.
        // WI-374: eliminate from the WRITTEN params, not the expanded copies —
        // an expanded partial application's unbound fresh var would make the
        // eliminated type non-ground, and the WI-385 groundness gate below
        // would silently skip a mismatch the written form rejects loudly.
        let mut effective_param_types: HashMap<Symbol, Value> = HashMap::new();
        if params_have_projection {
            // WI-459: re-key a cross-param projection NEUTRAL to the caller's argument too.
            let arg_syms = (!param_to_arg_sym.is_empty()).then_some(&param_to_arg_sym);
            // Interned ONCE for the whole loop, not per parameter (review).
            let macro_pass = crate::kb::occurrence::macro_expand_pass(kb);
            for (param_sym, param_type) in &written_params {
                if !value_contains_projection(kb, param_type) {
                    continue;
                }
                // Computed BEFORE the call: `eliminate_type_projections` takes `kb`
                // mutably, and only one of the two can hold it.
                let surface = surface_of_with(kb, macro_pass, occ, fn_sym);
                let eff = eliminate_type_projections(
                    kb,
                    param_type,
                    &param_to_arg_type,
                    arg_syms,
                    &TypeErrorContext::OperationReturn {
                        op_name: fn_sym,
                        surface,
                    },
                    span,
                )?;
                // `unify_types` borrows the arg type (it is `A: TermView`), so no clone.
                if let Some(arg_ty) = param_to_arg_type.get(param_sym) {
                    unify_types(kb, &mut subst, arg_ty, &eff);
                }
                effective_param_types.insert(*param_sym, eff);
            }
        }

        // WI-329 (proposal 045 §5.6): HANDLER DISCHARGE. Placed here for the same reason
        // WI-705 states below — `subst` now carries the FULL instantiation from every
        // argument, which is exactly what makes a shared row tail's lower bound the union
        // of its constraints rather than whichever argument reached it first. Above the
        // signature check so a discharged tail is part of the instantiation that check
        // reads, and above `check_unconstrained_type_params` so a tail this solves is no
        // longer reported unconstrained. No-op unless the callee declares type params and
        // one of them is still unbound.
        infer_discharged_row_tails(kb, &mut subst, &op, &callback_pairs);

        // WI-705: reject a call whose SIGNATURE — the op's own effect row or any
        // arrow-typed param row — an instantiation has made UNINHABITABLE (`{X, -X}`,
        // present AND absent the same label). Placed HERE, after the arg-unify loops,
        // so `subst` carries the FULL instantiation — explicit `[E = {…}]` AND
        // argument/context inference alike — and BEFORE the per-arg
        // `validate_callback_effect_row` below, which may then assume an inhabitable
        // declared row and own only actual-vs-declared conformance. Covering the op's
        // own row plus every param row, actual-agnostically, subsumes WI-700's
        // eta-scoped per-arg self-contradiction reject (removed) AND catches the two
        // shapes it missed (an op's own row; a lambda callback). No-op unless an
        // instantiation actually bound a row-bearing type param.
        check_signature_self_contradiction(kb, &subst, &op, fn_sym, span)?;
        // WI-385: VALIDATE each argument against its declared parameter type.
        // The unify loops above pin type-parameters for INFERENCE and DISCARD
        // their boolean — so before this check a caller could pass an argument
        // of any type and the typer stayed silent (`f(x: Int) -> Int` called as
        // `f("hello")` loaded clean). Now that the arguments are synthesized and
        // the type-params bound, subtype-check each argument against its param
        // type — the ARGUMENT direction, peer to the RETURN direction WI-379 made
        // authoritative. GATED on `resolved_type_is_ground` for BOTH the
        // (subst-walked) arg type and param type: a polymorphic position (`add(a:
        // T, b: T)`, an inference-`?_` arg) stays unchecked so the spec-op
        // dispatch / return-conformance path settles it — only a concrete arg
        // against a concrete param can fail here. A param a prior argument GROUND
        // by inference (`f[T](a: T, b: T)` with `a:Int`) is then checkable, so a
        // contradicting `b:"x"` is still caught. Bail on an ill-typed call
        // (aggregating sibling mismatches) rather than building its return type.
        let mut arg_type_errors: Vec<TypeError> = Vec::new();
        // WI-408: bare-`T`-vs-`Option[T]` args accepted via some-coercion —
        // (child-index, declared Option type), materialized after the loops.
        let mut some_wraps: Vec<(usize, Value)> = Vec::new();
        for (i, _) in pos_args.iter().enumerate() {
            if let Ok(ref arg_result) = pos_results[i] {
                // WI-374: validate against the param AS WRITTEN, not the
                // inference-expanded copy (see `written_params` above).
                // WI-1100: a `None` here is a SURPLUS argument — one that fills no
                // declared slot. It stays skipped, because the thing to say about it is
                // not a type mismatch; [`call_arity_error`] below reports the count, and
                // did not exist when this `get` was the whole of what a surplus argument
                // met.
                // WI-1104: …except the one surplus that IS type-checkable — a relational
                // goal's RESULT column, whose declared type is the operation's RETURN
                // rather than any parameter. Checked below beside the arity verdict that
                // admits it ([`relational_result_column`]), not here, because this loop
                // pairs arguments to PARAMETERS and that column fills none.
                if let Some((param_sym, param_type)) =
                    pos_call_params[i].and_then(|p| written_params.get(p))
                {
                    // WI-398: validate against the ELIMINATED type for a projection param
                    // (`s.cell.T` → `String`); the raw type for a non-projection param.
                    let param_type = effective_param_types.get(param_sym).unwrap_or(param_type);
                    // WI-440: the lacks/closed-row CHECKING direction for an
                    // eta'd callback argument (binder-aligned row validation).
                    // Runs FIRST: when both it and the generic subtype check
                    // would reject (e.g. a ground `@ {}` arrow), this one names
                    // the offending effect label, where the generic mismatch
                    // prints two identically-displayed arrow types.
                    if let Some(err) = validate_callback_effect_row(
                        kb,
                        &subst,
                        fn_sym,
                        *param_sym,
                        param_type,
                        &pos_args[i],
                        &arg_result.ty,
                        span,
                    ) {
                        arg_type_errors.push(err);
                    } else {
                        match validate_arg_against_param(
                            kb,
                            &mut subst,
                            &arg_result.ty,
                            param_type,
                            span,
                            TypeErrorContext::OperationArgument {
                                op_name: fn_sym,
                                param: *param_sym,
                            },
                            Some(&arg_result.node),
                        ) {
                            ArgValidation::Ok => {}
                            ArgValidation::WrapSome { declared } => some_wraps.push((i, declared)),
                            ArgValidation::Fail(err) => arg_type_errors.push(err),
                        }
                    }
                }
            }
        }
        for (i, (arg_name, arg_occ)) in named_args.iter().enumerate() {
            if let Ok(ref arg_result) = named_results[i] {
                // WI-374: validate against the param AS WRITTEN (see above).
                // WI-426: match the label to its param by name (not symbol identity).
                if let Some((param_sym, param_type)) =
                    match_named_arg_param(kb, &written_params, *arg_name)
                {
                    // WI-398: validate against the eliminated projection type (above).
                    let param_type = effective_param_types.get(param_sym).unwrap_or(param_type);
                    // WI-440: callback row check first — see the positional loop.
                    if let Some(err) = validate_callback_effect_row(
                        kb,
                        &subst,
                        fn_sym,
                        *param_sym,
                        param_type,
                        arg_occ,
                        &arg_result.ty,
                        span,
                    ) {
                        arg_type_errors.push(err);
                    } else {
                        match validate_arg_against_param(
                            kb,
                            &mut subst,
                            &arg_result.ty,
                            param_type,
                            span,
                            TypeErrorContext::OperationArgument {
                                op_name: fn_sym,
                                param: *param_sym,
                            },
                            Some(&arg_result.node),
                        ) {
                            ArgValidation::Ok => {}
                            ArgValidation::WrapSome { declared } => {
                                some_wraps.push((pos_args.len() + i, declared));
                            }
                            ArgValidation::Fail(err) => arg_type_errors.push(err),
                        }
                    }
                }
            }
        }
        // WI-426: named-argument COVERAGE (see `bind_call_arguments`, which
        // WI-783 shares with the function-VALUE call path so the two cannot drift).
        // WI-1100: and the ARITY verdict the same binding decides — every declared slot
        // filled exactly once, nothing outside the list ([`call_arity_error`]). Both are
        // read off ONE pairing of arguments to slots rather than from a second count.
        let mut binding = bind_call_arguments(
            kb,
            &op.params,
            pos_args.len(),
            named_args,
            fn_sym,
            "this operation",
            span,
        );
        arg_type_errors.append(&mut binding.label_errors);
        arg_type_errors.extend(call_arity_error(
            kb,
            &op.params,
            &binding,
            source_args,
            capture_param,
            fn_sym,
            pos,
            span,
        ));
        // WI-1104, the tolerance's other half: the column `call_arity_error` just
        // ADMITTED is the operation's RESULT, so it is checked like any argument —
        // against the RETURN. Nothing else in the language does: the goal's shape is
        // decided at resolution (`functional_relation_arity` /
        // `dispatched_relation_arity`, kb/resolve.rs), which reads the arity and never the
        // declared return, so `Desc.describe(leaf(), "not an int")` against `-> Int64`
        // loaded clean and answered nothing — a dead goal indistinguishable from one with
        // no solutions, which is exactly the deferral WI-1100 exists to remove.
        //
        // DECIDED HERE, COMPARED LATER, and the split is not tidiness. Which argument is
        // the result column is the arity verdict's own question and is answered once,
        // beside it. WHAT it must match is the return the call actually produces, which
        // does not exist yet: a projection return (`get(b: Box) -> b.T`) is discharged
        // against the receiver's argument type ~150 lines below (`proj_return_type`,
        // WI-376/WI-606). Comparing against `op.return_type` here instead was
        // review-found and MEASURED — `rule r() :- box(v: 3).get(3)` on `box(v: T)`,
        // a correct program, was refused with `expected b.T, got Int64`, a diagnostic
        // naming a type the author never wrote.
        //
        // BOTH READS ARE TOTAL, so neither is written as a case to skip (loud over
        // silent): `surplus_positional == 1` says `pos_args.len() == params.len() + 1`,
        // which puts the column at the last positional index; and `collect_arg_errors` at
        // the top of this function returned early on any `Err` argument, so every result
        // here is `Ok`. A miss would be a broken invariant, not an input.
        let result_column_type: Option<Value> = relational_result_column(&op.params, &binding, pos)
            .map(|col| {
                pos_results[col]
                    .as_ref()
                    .expect("WI-1104: every argument result is `Ok` past `collect_arg_errors`")
                    .ty
                    .clone()
            });
        if !arg_type_errors.is_empty() {
            return Err(aggregate_errors(arg_type_errors));
        }
        // WI-374 (user-decided 2026-06-12): ENFORCE the §3 parametricity tie.
        // The argument loops bind a sort's canonical param vars through bare
        // member params (`append(xs: List, ys: List)` both bind `List.T`); a
        // conflicting rebind records a contradiction that was never consulted,
        // so `append(intList, strList)` was silently accepted with
        // first-binding-wins threading. Checked HERE — after the WI-385
        // per-argument validation (whose precise diagnostics take precedence)
        // and BEFORE the expected-seeding below, whose failed unify against a
        // pinned slot is a DELIBERATE silent no-op (WI-367/WI-379) that must
        // not trip this. Scoping (review round, same day):
        //  - the callee's parent must be a SORT — `impl_parent_of_op` yields
        //    the NAMESPACE symbol for a top-level op, and a namespace prefix
        //    would sweep in every sort it contains, enforcing a "member tie"
        //    on §3-bullet-2 foreign refs;
        //  - EVERY per-var detail is scanned (a single first-detail would let
        //    an earlier benign foreign conflict mask a member violation);
        //  - a conflict whose prior binding is the body's WI-424 seeded rigid
        //    is exempt — a same-sort sibling call at a different instance
        //    keeps its pre-WI-374 acceptance (enforcing the rigid tie is a
        //    separate decision);
        //  - a UNIFIABLE pair (bare `List` vs `List[T = Int64]`, a `?_`
        //    wildcard vs a concrete, equal rows in different carriers/orders)
        //    is refinement, not violation — bind-level TermId/structural
        //    inequality over-reports, so re-test through the real relation.
        // A FOREIGN sort's var contradicted through two independent bare refs
        // (§3 bullet 2: independent) is not scanned — and with the signature
        // expansion above, foreign refs no longer touch canonical vars at all.
        let op_parent_sort = impl_parent_sort_of_op(kb, fn_sym);
        if let Some(parent) = op_parent_sort {
            enforce_member_tie(
                kb,
                &subst,
                parent,
                fn_sym,
                span,
                env.enclosing_instance_param_rigids(),
            )?;
        }
        // WI-408: materialize the recorded some-coercions — wrap each flagged
        // argument's typed node in a synthesized `some(...)` and reassemble
        // this apply from the new children. MUST run before any annotation
        // write (`classify` below): the rebuilt
        // node starts with fresh annotation cells. The parent reassembles in
        // turn from `TypeResult.node` (WI-283), and the root reaches the
        // stored body via `set_op_body_node`.
        // WI-426: when the call has NAMED args, rebuild the node with them
        // reordered into the callee's parameter order (also applying any
        // some-wraps), so eval's positional binding is correct. Falls back to
        // the some-wrap-only rebuild for a non-`Apply` node or when there are no
        // named args.
        let rebuilt_occ;
        let occ = if !named_args.is_empty() {
            match reorder_named_args_in_apply(
                kb,
                occ,
                &written_params,
                pos_args.len(),
                &some_wraps,
                pos_results,
                named_results,
            ) {
                Some(r) => {
                    rebuilt_occ = r;
                    &rebuilt_occ
                }
                None if some_wraps.is_empty() => occ,
                None => {
                    rebuilt_occ =
                        wrap_some_children(kb, occ, &some_wraps, pos_results, named_results);
                    &rebuilt_occ
                }
            }
        } else if some_wraps.is_empty() {
            occ
        } else {
            rebuilt_occ = wrap_some_children(kb, occ, &some_wraps, pos_results, named_results);
            &rebuilt_occ
        };

        // WI-376: discharge expression-carried type projections (`s.T` / `s.Sort`) in
        // the declared return type — and any effect rows that carry one — by projecting
        // the RECEIVER param's argument type, resolved here where the arguments are
        // synthesized. Concrete member → the projected type (`List[Int].T = Int`); a
        // member the receiver's sort does not declare, or one it declares but the
        // receiver left unbound (a bare / abstract receiver) → loud `TypeError`. Only
        // ops that actually carry a projection (`op_has_projection`) run the rewrite.
        // WI-396: EFFECT-POSITION projection `effects s.E` rides this same loop — it
        // lowers to an `ExprCarried` (`type_expr_to_value`, once `infer_effects_row_-
        // requires` stopped strict-resolving the dotted name) and `project_type_member`
        // reads the `E` member off the receiver's type, threading the observation effect
        // row. `l.E` on a sort with no effect member is the same loud missing-member
        // error — `E` is never silently defaulted to pure (design §5).
        // WI-1063: WHOSE declaration `proj_return_type` came from. Normally the callee's, but
        // the WI-606 fallback below threads a CONCRETE OVERRIDE's return instead, and the
        // existential opening has to ask the §3 self question of that operation's sort, not of
        // the spec op the call named.
        let mut return_owner = fn_sym;
        let (proj_return_type, proj_effects): (Value, Vec<Value>) = if op_has_projection {
            let ret_ctx = TypeErrorContext::OperationReturn {
                op_name: fn_sym,
                surface: surface_of(kb, occ, fn_sym),
            };
            // WI-459: pass the formal→argument value-reference map so a projection NEUTRAL
            // formed off a formal param is RE-KEYED to the caller's actual receiver (see
            // `rewrite_term_projections`).
            let arg_syms = (!param_to_arg_sym.is_empty()).then_some(&param_to_arg_sym);
            // WI-606: a body-less self-receiver spec op whose RETURN (and observation
            // effect row) is WRITTEN with path-dependent projections on the receiver
            // (`Stream.splitFirst -> …[B = Stream[T = s.T, E = s.E]]`, `effects {s.E}`)
            // does NOT eliminate those projections against a CONCRETE provider receiver
            // that realizes the spec's members only INDIRECTLY (`Mapped provides Stream[E
            // = {ES, EF}]` — no direct `.E` member on `Mapped`). The call value-dispatches
            // to that provider's own override, whose return + effects are projection-FREE
            // (`Mapped.splitFirst -> …[B = Mapped[…]] effects {ES, EF}`); thread THOSE —
            // exactly what a qualified static `Mapped.splitFirst(m)` computes — so a
            // destructured tail carries the concrete carrier (`rest : Mapped[…]`, not the
            // erased `Stream[…]`) and a downstream dispatch on it (`collect(rest)`) grounds.
            // Return AND effects fall back together (self-contained: the effect row stays
            // sound even on a dispatch arm that does not re-derive `dispatched_impl_-
            // effects`). A clean elimination (abstract self-receiver, or a provider with a
            // direct member) is unchanged; a genuine projection failure with no concrete
            // override stays the loud error.
            match eliminate_type_projections(
                kb,
                &op.return_type,
                &param_to_arg_type,
                arg_syms,
                &ret_ctx,
                span,
            ) {
                Ok(rt) => {
                    let mut effs: Vec<Value> = Vec::with_capacity(op.effects.len());
                    for e in &op.effects {
                        effs.push(eliminate_type_projections(
                            kb,
                            e,
                            &param_to_arg_type,
                            arg_syms,
                            &ret_ctx,
                            span,
                        )?);
                    }
                    (rt, effs)
                }
                Err(e) => {
                    match concrete_override_threaded(kb, &op, fn_sym, self_recv_spec, pos_results) {
                        Some((rt, effs, impl_op)) => {
                            return_owner = impl_op;
                            (rt, effs)
                        }
                        None => return Err(e),
                    }
                }
            }
        } else {
            (op.return_type.clone(), op.effects.clone())
        };

        // WI-481: a value-in-type (denoted) reference to a callee PARAMETER inside the
        // RETURN TYPE — `eff_stream(p) -> Strm[T = Int64, E = {Modify[p]}]`, where `p`
        // is the param and `Modify[p]` is a denoted value-in-type effect carried IN the
        // return type's `E` binding — must be re-keyed to the caller's actual argument,
        // exactly as a declared `effects Modify[c]` label is (`pre_substituted` below).
        // The effect re-keying only touches `op.effects`; a value-in-type embedded in the
        // return type was never re-keyed, so the result type — and any `s.E` projection a
        // consumer reads off it — carried the CALLEE's param symbol. A correctly-declared
        // `effects {Modify[p]}` consumer was then rejected as undeclared because the
        // declared and incurred `Modify[p]` named DIFFERENT `p` symbols (caller's vs
        // callee's).
        //
        // Gate on `!op_has_projection`: when the op HAS a projection the return type was
        // already run through `eliminate_type_projections` above, whose `Denoted` arm now
        // re-keys the value-in-type via this same `param_to_arg_sym` (so a MIXED return
        // `Strm[T = s.T, E = {Modify[p]}]` re-keys the `Modify[p]` there, alongside the
        // projection — and a δ-reduced projection NEUTRAL's receiver is left to that arm's
        // surgical, WI-459-aware handling rather than corrupted by a blanket `Ref`-sub
        // here). The projection-free case never reaches elimination, so re-key it here.
        let proj_return_type = if !param_to_arg_sym.is_empty() && !op_has_projection {
            substitute_ref_syms_value(kb, &proj_return_type, &param_to_arg_sym)
        } else {
            proj_return_type
        };

        // WI-714: EVALUATE the `Concat[A, B]` type constructor in the return type. Its
        // operands are the per-call schemas — but they reach here as the op type params
        // `L`/`R` (or `r1.T`/`r2.T` projections) BOUND IN `subst`, not yet substituted into
        // the type, so WALK the return through `subst` first (resolving `Concat[A = L, B =
        // R]` to `Concat[A = nt1, B = nt2]`), then reduce to the merged named tuple. A
        // non-named-tuple operand or a field-name collision is a loud error. Universal
        // (keyed on the `Concat` sort, not the op), gated per-op on the DECLARED return
        // type actually writing `Concat`.
        // WI-727: `Without` (fix's schema drop) reduces at the SAME boundary as `Concat`
        // (join's merge) and `s.T`. An op's return writes at most one, so share the single
        // `subst`-walk (which substitutes the bound type params — `Drop = R`, the captured
        // record — into the type before the operands are inspected), then apply whichever
        // reduction the signature actually wrote. Each is universal (keyed on the sort, not
        // the op) and gated per-op on the declared return type.
        let proj_return_type = if op_return_ctors.iter().any(|f| *f) {
            let ret_ctx = TypeErrorContext::OperationReturn {
                op_name: fn_sym,
                surface: surface_of(kb, occ, fn_sym),
            };
            // Share the single `subst`-walk (which substitutes the bound type params —
            // `Drop = R`, the captured record — into the type before the operands are
            // inspected), then apply each ctor the signature actually wrote, in family
            // order. WI-734: folded over `TYPE_CTORS` rather than an if-chain per
            // constructor, so a new ctor reduces here by construction.
            // WI-759: the reduction SITE — `FieldOf` reads its enclosing sort to decide
            // whether an `internal` field is projectable here (WI-369); the structural
            // members ignore it.
            let site = CtorReduceSite {
                sp: occ.span,
                span,
                // WI-977: the OPERATION's scope where there is one — see
                // `TypingEnv::referencing_scope`. Was `enclosing_sort()`, one scope out.
                scope: env.referencing_scope(),
            };
            // A FIXPOINT OVER THE FAMILY, not one pass in array order — WI-20260818-YQB1Y,
            // and the reason it had to change is a REGRESSION the one-pass version caused.
            //
            // THE PROBLEM ONE PASS HAS: a ctor whose operand is another family member DEFERS
            // (a sibling reads as "not yet known" — WI-734), so if that inner member sits
            // LATER in `TYPE_CTORS` it reduces afterwards and the OUTER one is left unreduced
            // over a now-concrete operand nothing revisits. Whichever order is chosen, the
            // nesting in the other direction is the one that strands.
            //
            // MEASURED, BOTH DIRECTIONS, four lines of ordinary source each:
            //   * `Concat[A = Without[T = (a, b), Drop = (b)], B = (c)]`
            //   * `Without[T = Concat[A = (a), B = (b)], Drop = (b)]`
            // With `Concat` first the second loads and the first stalls; with `Without` first
            // the first loads and the second stalls. This ticket FIRST tried reordering to
            // `Without`-first, because its own composition is the first shape — and that
            // REGRESSED the dual, which had loaded clean. A fix that recurred one coordinate
            // over, caught in review. The reorder was reverted: `TYPE_CTORS` keeps its
            // original order and the fixpoint reduces both, which no order can do.
            //
            // WHY THIS IS NOW THE RIGHT CHANGE, when it was previously declined: a fixpoint
            // was written and measured before, and its ONLY stated blocker was
            // `wi776_one_collapse_diagnostic_test::concat_over_a_collapsed_without_still_-
            // stalls`, a tripwire pinning kernel-language.md's "`Concat`/`Without` are not
            // inverses at arity one" as a weighed and declined limit of the 1-collapse. 052
            // OQ5 option A retired that decision, so the tripwire is gone and its successor
            // (`yqb1y_concat_and_without_are_inverses_at_arity_one`) requires the opposite.
            //
            // TERMINATION rests on a monotone measure: no reduction ever INTRODUCES a family
            // ctor, so the set of ctor kinds present can only shrink, and `flags` (recomputed
            // from the reduced type) can only lose entries. The loop ends when it is empty or
            // when a pass leaves it unchanged.
            //
            // THE STOP CONDITION IS AN APPROXIMATION, stated rather than glossed: unchanged
            // FLAGS mean "no ctor kind was eliminated", which is not quite "nothing changed"
            // — a pass could in principle remove some `Concat` nodes and leave others. In
            // that case this breaks one pass early and leaves a residual, which is exactly
            // the PRE-fixpoint behaviour and fails loudly downstream (the CAVEAT on
            // `reduce_type_ctor`), never a wrong answer. It is not reachable from any shape
            // measured here, because `reduce_type_ctor` descends into bindings before
            // evaluating, so same-ctor nesting collapses within a single call and only
            // CROSS-member deferral survives a pass — and eliminating the member deferred on
            // is what clears its flag.
            //
            // `MAX_PASSES` is a backstop for a reduction that neither reduces nor stabilizes,
            // which would be a bug in a `TypeCtor`. It is a LOUD error rather than a silent
            // truncation, because a silently-stranded residual is the failure mode this loop
            // exists to remove.
            //
            // ARRAY ORDER STILL MATTERS, just far less: it decides how many passes a given
            // nesting costs, not whether it reduces. `MEMBERSHIP_CTOR` stays LAST for its own
            // reason — a stranded PREDICATE loses its assertion silently rather than
            // producing an unusable type, so it must see every computing member's result.
            const MAX_PASSES: usize = 16;
            let mut reduced = walk_type_deep_value(kb, &subst, &proj_return_type);
            let mut flags = op_return_ctors;
            let mut passes = 0;
            while flags.iter().any(|f| *f) {
                passes += 1;
                if passes > MAX_PASSES {
                    return Err(projection_type_error(
                        &ret_ctx,
                        span,
                        &format!(
                            "internal: type-constructor reduction did not reach a \
                             fixpoint in {MAX_PASSES} passes over `{}` — a `TypeCtor` \
                             that neither reduces its operands nor leaves the type \
                             unchanged. Please report it.",
                            type_display_name_value(kb, &reduced)
                        ),
                    ));
                }
                for (cfg, wrote) in TYPE_CTORS.iter().zip(flags.iter()) {
                    if *wrote {
                        reduced = reduce_type_ctor(kb, &reduced, &ret_ctx, &site, cfg)?;
                    }
                }
                // Which ctors SURVIVED this pass. Recomputed from the reduced type rather
                // than tracked, because that is the same question the per-op gate asks and
                // there is one answer to it (`return_reducible_ctors`). Unchanged flags mean
                // every remaining ctor is stuck on an operand that is not yet known, so the
                // next pass would do exactly what this one did.
                let next = return_reducible_ctors(kb, &reduced);
                if next == flags {
                    break;
                }
                flags = next;
            }
            reduced
        } else {
            proj_return_type
        };

        // WI-1104 — the RESULT COLUMN of a functional-relation goal, compared against the
        // return it receives. The column was chosen at the arity verdict above (one owner
        // for "which argument is the result"); this is the first point at which the other
        // side of the comparison exists in the form the call actually produces —
        // projections discharged against the receiver (`s.T`, WI-376/WI-606), value-in-type
        // references re-keyed to the caller's arguments (WI-481), and the `Concat` /
        // `Without` family reduced (WI-714/WI-727). Above this it is still `b.T`, and
        // comparing against that spelling refused `rule r() :- box(v: 3).get(3)` — a
        // correct program — with `expected b.T, got Int64` (review-found, measured).
        //
        // Raised as its own `Err`: the sibling argument mismatches were aggregated and
        // returned ~200 lines above, so there is no longer a batch to join.
        if let Some(column_type) = &result_column_type {
            if let Some(e) =
                result_column_error(kb, &mut subst, column_type, &proj_return_type, fn_sym, span)
            {
                return Err(e);
            }
        }

        // WI-383 B (Modify provider-fact GROUND value bind): bind a still-FREE spec
        // value-param from the carrier's GROUND provider-fact binding
        // (`fact Box[T = IntCell, V = Int64]` ⟹ `Box.V := Int64`, the entity-resource
        // Modify tie). Runs HERE — AFTER the argument loops (so a param threaded by an
        // argument, e.g. Iterable's `Element` via the predicate, is already bound and the
        // still-FREE gate skips it; binding it EARLY regresses WI-424/441 effect-row
        // threading) and BEFORE expected-seeding (so the resource's declared value type
        // wins over the caller's `-> String` claim — the value-untied soundness hole the
        // Modify model names). The REF-shaped binding (`V ↦ Cell.V`) is already threaded
        // by `bind_spec_params_from_carrier_param` above; this closes only the
        // GROUND-valued case it skips.
        if let Some((
            spec_sort,
            _carrier_sym,
            _recv_ty,
            view,
            _carrier_pvid,
            _transitive,
            _recv_arg_sym,
        )) = &carrier_param_info
        {
            bind_ground_value_params_from_provider(kb, &mut subst, *spec_sort, view);
        }

        // WI-270 / WI-379: now that the arguments have been synthesized,
        // consult the caller-side `expected` type via `op.return_type`. Running
        // it AFTER argument inference (it used to run before) makes it fill only
        // STILL-FREE type params: a param an argument already pinned resists the
        // override — the `unify_types` against the pinned slot fails for a
        // differing claim and its boolean is discarded — so a wrong declared
        // return no longer masks a contradicting argument
        // (WI-379 soundness gap (a)). A genuinely free param
        // (`empty() -> List[Elem]`, `term_as_entity[E] -> Option[E]`) is still
        // filled from `expected` (WI-270's legitimate case). The synthesized
        // `resolved_ret` is then checked against `expected` at the use site
        // (`check_operation_bodies` return check / let conformance), which is
        // what actually rejects the wrong declared return.
        //
        // WI-20260904-60143 — "BINDING NOTHING" IS WHAT THIS USED TO SAY, AND IT WAS NEVER
        // TRUE OF A COMPOUND `expected`. What resists the override is the PINNED SLOT, and
        // only it: `unify_types` walks it to its value and compares, so no rebind happens
        // there. Its SIBLINGS are a separate question — a still-free param in the same type
        // IS filled from an `expected` the pinned slot has already contradicted, and it stays
        // filled, because the relation does not roll back (see its "what survives a `false`"
        // note). The paragraph's conclusion is unaffected: what rejects a wrong declared
        // return is the use-site check on `resolved_ret`, not this unify's discarded boolean,
        // and that check still sees the contradicting slot. What changed is that the sibling
        // fills are now the SAME set however the `expected` type's slots were spelled.
        if let Some(exp) = expected {
            unify_types(kb, &mut subst, &proj_return_type, &exp);
        }

        // WI-20260918-R541X (A) — what is STILL free after the arguments and `expected`,
        // the enclosing scope's own `requires` clause over the callee's sort may decide.
        // AFTER `expected` so every binding that ran before is left exactly as it was.
        bind_sort_params_from_sole_enclosing_requirement(kb, &mut subst, env, callee_parent_sort);

        // WI-1063 — OPEN the callee's existential return. A RETURN's unwritten sort
        // parameter is in POSITIVE position and is EXISTENTIALLY quantified: `operation
        // widen(…) -> Stream[T = Int64]` declares `∃E. Stream[T = Int64, E]`. The body PACKS
        // a witness (which is why `widen` loads, and why the mirror-image rewrite is NOT in
        // `check_operation_bodies` — see the block comment there), and EVERY USE OPENS: this
        // call's result is `Stream[T = Int64, E = ρ]` for a fresh rigid ρ, so a consumer that
        // demanded `E = {}` is refused HERE rather than at `widen`'s declaration.
        //
        // FRESHNESS PER OPENING IS THE SOUNDNESS, not an implementation detail — two calls
        // may genuinely return different rows, so one shared constant would relate them.
        // `UnwrittenFill::Anonymous` mints per slot per call and nothing names a ρ, which is
        // the correct reading of an UNNAMED existential: `docs/design/type-parameter-
        // scoping.md` §5's "erased" ("no consumer-side mechanism can soundly recover `l`'s
        // element or effect") is this opening said without the word.
        //
        // THE SAME WALK AS THE PARAMETER SIDE, under the other polarity, which is why it is
        // that function and not a second one: a parameter's unwritten slot is negative-
        // position and UNIVERSAL, so WI-1059/WI-1061 rigidify it in the BODY and leave it
        // flexible at a call; a return's is existential, so it stays as written in the body
        // and is rigidified at the CALL. One rule, two polarities — and the two sites now
        // differ only in [`SlotPosition`] and in the filler.
        //
        // AFTER the `expected` seeding above, deliberately, and the reason is the SECOND half
        // of this sentence rather than the first. For an OMITTED slot seeding cannot reach it
        // either way — a missing binding is width-ignored by `unify_parameterized_view`, so
        // there is nothing there to bind — but a slot written `?` is a live flexible var that
        // seeding CAN bind, and the opening then replaces it and discards that binding, which
        // is the intended verdict but not a no-op. What forces the order is that running the
        // opening first would hand `unify_types` a rigid against the caller's concrete demand,
        // and a FAILED unify may leave `subst` marked contradictory for every reader below.
        //
        // `return_owner`, not `fn_sym`: see its declaration above.
        let proj_return_type = match open_existential_return(
            kb,
            if return_owner == fn_sym {
                callee_parent_sort
            } else {
                impl_parent_sort_of_op(kb, return_owner)
            },
            return_owner,
            &proj_return_type,
            occ.span,
            occ.owner,
        ) {
            Some(opened) => opened,
            None => proj_return_type,
        };

        // WI-20260829-W6JH0 — proposal 035 FORM (3): `Map[K = String, V = Int64].empty()`.
        // The receiver's bindings ARE this call's result type. 035 states it as "method
        // dispatch on it produces values typed at those bindings", and lists form (3)
        // beside form (1)'s `let m: Map[…] = Map.empty()` annotation and form (2)'s
        // inference as three spellings of one thing — so this is the annotation's rule,
        // reached from the receiver instead of from a binding occurrence.
        //
        // IT HAS TO BE THE RESULT AND NOT THE SUBSTITUTION, which is what the ticket's own
        // proposed fix ("unify the receiver's bindings against the sort's params for the
        // call") would have been, and it is why that fix was not taken. Binding the sort's
        // params in `subst` is ALREADY what the callee bracket does — `call_bracket_scopes`
        // includes the parent sort's params, so `Map.empty[K = Bool, V = Bool]()` reaches
        // `seed_op_type_args` and binds them — and it changes nothing, because `empty()
        // -> Map` returns the sort BARE and WI-1082 deliberately leaves a constructor's
        // self-sort return untied ("NO SELF PARAMETER, NO TIE"). MEASURED: that spelling
        // still accepts a `String` key. The binding has nowhere to land.
        //
        // GATED ON THE DECLARED RETURN BEING THE RECEIVER'S OWN SORT, so it speaks only
        // where the receiver is describing the value that comes back. `Map[K = …].size(m)
        // -> Int64` is untouched: its bracket is still checked for parameter NAMES at the
        // loader, but it makes no claim this arm can honour, and inventing one would be
        // reading `Map[…]` as the type of an `Int64`.
        //
        // AFTER the existential opening, so an opened rigid is what the receiver refines
        // rather than the other way round.
        //
        // IT MERGES, IT DOES NOT REPLACE, and a first cut got this wrong in a way worth
        // recording because the wrong version LOOKS right on the ticket's own row. Taking
        // the receiver's type verbatim discards every slot it does not write, and for a
        // callee whose return IS parameterized those slots hold what the ARGUMENTS just
        // determined: `Map.put(m, key, value) -> Map[K = K, V = V]` (WI-1082's self-tie)
        // has `V` pinned to `Int64` by the `1` in `put(Map.empty(), "a", 1)`, and a
        // receiver writing only `Map[K = String]` — a TRUE claim — deleted it, silencing a
        // real error one call out. MEASURED: `size(put(Map[K = String].put(Map.empty(),
        // "a", 1), "b", true))` went from 1 error to 0. A written type that is CORRECT
        // must never remove a check. So the receiver is unified INTO the declared return
        // and the resolved declared return is what comes back; the receiver's own type is
        // the result only where the declared return has no slots to carry (a bare
        // `SortRef`, which is `empty()` and the case this ticket is about).
        //
        // AND THE VERDICT IS READ. A receiver that CONTRADICTS what the call determined
        // (`Map[V = Bool].put(Map.empty(), "a", 1)`) is a fault the author wrote, and
        // discarding the failed unify made it load clean — the same measurement, other
        // polarity. It is reported here, at the receiver, because that is where the wrong
        // claim is; the arguments are not at fault and reporting against them would send
        // the author to the wrong line.
        let proj_return_type = match call_recv_type_of(occ) {
            Some(rt)
                if matches!(
                    (type_head(kb, &proj_return_type), type_head(kb, rt)),
                    (TypeHead::SortRef(a), TypeHead::Parameterized { base: b })
                        | (TypeHead::Parameterized { base: a }, TypeHead::Parameterized { base: b })
                        if same_sort_canonical(kb, a, b)
                ) =>
            {
                let rt = rt.clone();
                let declared_carries_slots = matches!(
                    type_head(kb, &proj_return_type),
                    TypeHead::Parameterized { .. }
                );
                if !unify_types(kb, &mut subst, &proj_return_type, &rt) {
                    let actual = walk_type_deep_value(kb, &subst, &proj_return_type);
                    let surface = surface_of(kb, occ, fn_sym);
                    return Err(TypeError::TypeMismatch {
                        site: TypeError::here(),
                        span,
                        context: TypeErrorContext::OperationReturn {
                            op_name: fn_sym,
                            surface,
                        },
                        expected: rt,
                        // A DECLARED projection return against a declared receiver return:
                        // two signatures, no expression between them to denote anything.
                        denoted: None,
                        actual,
                    });
                }
                let merged = if declared_carries_slots {
                    &proj_return_type
                } else {
                    &rt
                };
                walk_type_deep_value(kb, &subst, merged)
            }
            _ => proj_return_type,
        };

        // Apply param-name substitution to op.effects (WI-209), then
        // walk each through `walk_type_deep` so type-var bindings from
        // arg-unification propagate into nested positions in the effect
        // (e.g. `Stream.head`'s `effects E` → `Error` once `vid_E` is
        // bound by `unify_parameterized_with_sort_ref`). Skip the
        // param-name walk when no var_ref args were seen.
        // WI-506: the effect re-key uses the VarRef map PLUS the projection-head
        // additions (a `Modify` on a projection arg coarsens to the head param). The
        // owned merge is built only when a projection arg was actually seen (the rare
        // case); the common path borrows `param_to_arg_sym` with no clone.
        let eff_rekey_owned;
        let eff_rekey_map: &HashMap<Symbol, Symbol> =
            if param_to_arg_head.is_empty() && param_to_placeless_arg.is_empty() {
                &param_to_arg_sym
            } else {
                // WI-20260823-4GBQV: drop the parameters whose argument names no place —
                // see `param_to_placeless_arg`. Their labels stay in the callee's own
                // vocabulary, where `unrekeyed_modify_argument` reports them against the
                // caller's expression.
                let mut m: HashMap<Symbol, Symbol> = param_to_arg_sym
                    .iter()
                    .filter(|(p, _)| !param_to_placeless_arg.contains_key(*p))
                    .map(|(k, v)| (*k, *v))
                    .collect();
                for (k, v) in &param_to_arg_head {
                    m.entry(*k).or_insert(*v);
                }
                eff_rekey_owned = m;
                &eff_rekey_owned
            };
        let pre_substituted: Vec<Value> = if eff_rekey_map.is_empty() {
            proj_effects.clone()
        } else {
            proj_effects
                .iter()
                .map(|e| {
                    // WI-459: a PROJECTION-bearing effect (`s.E`) was already eliminated
                    // AND re-keyed surgically by `eliminate_type_projections` (its Neutral
                    // branch re-forms the projection off the CALLER's argument). A blanket
                    // `Ref`-substitution here would WRONGLY re-key a δ-REDUCED projection
                    // receiver: the self-recursive `count(rest)` grounds `s.E` to the
                    // enclosing `count.s.E`, whose receiver IS the callee formal `s` — so
                    // the blanket map (`s ↦ rest`) would corrupt it to `rest.E` (exactly the
                    // ticket's "undeclared effect: s.E, body's s.E = rest.E"). Re-key only
                    // the GROUND effect labels (`Modify[c]` → `Modify[s]`, WI-209), which
                    // carry no projection and which the surgical pass never touches.
                    if value_contains_projection(kb, e) {
                        e.clone()
                    } else {
                        substitute_ref_syms_value(kb, e, eff_rekey_map)
                    }
                })
                .collect()
        };
        // Walk each effect through `walk_type_deep` so arg-unification bindings
        // propagate, then FLATTEN any element that resolved to a concrete effect-
        // ROW wrapper. WI-375: `effects E` with E bound to a WRITTEN
        // `effects_rows(…)` — from a producer's `Stream[E = {…}]` return threaded
        // into a bare-`Stream` param by `unify_parameterized_with_sort_ref` —
        // resolves to the row WRAPPER as a single effect element. Decompose it to
        // its present labels (+ open tail) so the effect machinery (propagation,
        // the pure-context check in `check_operation_bodies`, the WI-365 close
        // below) sees flat labels, not the wrapper as one opaque effect (which
        // rendered as a spurious `undeclared effect: {empty_row}`). A bare label
        // (`Modify[c]`) or an unbound row var (the WI-365 concrete-carrier path,
        // closed below) is not an `EffectsRows` head and passes through unchanged.
        // WI-539 (proposal 050 "operation call" modification rule, `requires`
        // half): check the callee's VALUE preconditions against Γ at the call
        // site. A `requires` value-goal (`neq(b, 0)`) is an OBLIGATION — it must
        // be positively PROVED from Γ + ground evaluation + KB via the same
        // `prove_from_gamma` bridge guard discharge uses, but at the OPPOSITE
        // polarity: a guard DROPS on a refutation, a precondition must be PROVED,
        // and an unproved one (incl. one that flounders over a symbolic argument)
        // is undischarged — a loud error, never a silent pass (048 §"Discharge is
        // constructive refutation"; the obligation sits on the safe side). Only
        // VALUE goals are checked here — spec/typeclass requires (`Spec[C=T]`,
        // `EffectsRuntime[…]`) have a `Sort` head and are dispatched / coverage-
        // checked elsewhere (WI-343 / WI-325), never proved from Γ.
        //
        // WI-557 / WI-602: the precondition check is primarily an OP-BODY call-site
        // obligation. A rule body is SLD/relational — no call-site Γ and no
        // imperative Hoare semantics — so a precondition over a SYMBOLIC rule-body
        // variable legitimately FLOATS (an unconstrained Γ over a symbolic arg) and
        // must NOT raise: pre-WI-557 it raised a spurious `UnsatisfiedPrecondition`
        // that `dispatch_calls_in_occ`'s `Err(_)` arm swallowed, leaving the dot
        // UNDISPATCHED. But a GROUND-REFUTED precondition in a rule body
        // (`guarded(_, 0)` ⇒ `neq(0, 0)` false) is a DEFINITE violation, not a
        // float, and IS raised exactly as an op body would — the rule-body gate is
        // refutation-aware (WI-602), not the unconditional skip WI-557 first shipped
        // (the WI-067/WI-292 polarity: act on a DECIDED obligation, never on an
        // UNDETERMINED one). Op-body checking (`in_rule_body()` false) raises on ANY
        // unproved precondition, unchanged.
        // WI-862 — SPLIT FIRST, CLASSIFY SECOND. `is_value_precondition_clause` reads a
        // clause's HEAD, and the loader lowers several comma-separated goals on ONE
        // clause as a single `conjunction(g1, …, gn)` (`convert_clause_list`). So a
        // MIXED clause — `requires neq(a, 0), lo: Ord[T = Int64]`, the shape WI-840's
        // overloaded list makes ordinary — presents the head `conjunction`, which is not
        // a `Sort`, and the whole thing was classified a value precondition and PROVED
        // as one goal. That proves the spec half from Γ, which the comment above says
        // never happens ("spec/typeclass requires … are dispatched / coverage-checked
        // elsewhere, never proved from Γ").
        //
        // IT PASSED ONLY BY ACCIDENT, and 058 §4 removed the accident: `fact Ord[T =
        // Int64]` put a raw `Ord[T = Int64]` in the RULE INDEX, so the spec conjunct
        // resolved as an ordinary SLD goal and the conjunction proved. Migrating that row
        // to `provides` — which files a provision and no fact — left the same conjunction
        // unprovable, and a TRUE precondition (`neq(7, 0)`) started reporting
        // `UnsatisfiedPrecondition`. MEASURED: `anthill query 'Ord[T = Int64]'` answers 1
        // solution under the `fact` spelling and NO SOLUTIONS under `provides`, while
        // `neq(7, 0)` answers 1 under both.
        //
        // `clause_conjuncts` is the existing owner of the split and its doc already
        // names this hazard from the other side; it was simply not reached here.
        let value_reqs: Vec<Value> = op
            .requires
            .iter()
            .flat_map(|c| clause_conjuncts(kb, c))
            .filter(|c| is_value_precondition_clause(kb, c))
            .collect();
        if !value_reqs.is_empty() {
            let req_sigma = build_call_guard_sigma(kb, &op.params, pos_args, named_args);
            let in_rule_body = env.in_rule_body();
            for clause in &value_reqs {
                // WI-9PGCM — σ_TYPE BEFORE Γ. A `requires` clause may name a variable
                // bound in the callee's PARAMETER TYPE, not among its value parameters:
                // `send(body: Text[L = ?l]) requires flows_to(?l, Public)`. The call
                // decides that variable by TYPE UNIFICATION — `send(fetch())` with
                // `fetch() -> Text[L = Untrusted]` binds `?l := Untrusted` in `subst`
                // — and `req_sigma` cannot carry it: σ maps a param SYMBOL to an
                // argument term, and `?l` is no parameter (1FKR2 subtracts the
                // `requires` source from the bound-variable set for exactly that
                // reason, so the clause's own variables are the empty set there — the
                // binding lives in the argument's type and nowhere else).
                //
                // LEAVING IT UNBOUND DID NOT MERELY MISS THE LABEL — IT PROVED THE
                // OBLIGATION. `prove_from_gamma` RESOLVES the goal, so a free `?l`
                // is witnessed EXISTENTIALLY: `flows_to(?l, Public)` succeeds with
                // `?l := Public` off the unrelated `flows_to(Public, Public)` fact,
                // discharging the clause at EVERY call regardless of the argument.
                // MEASURED at `e8efefa9` (`docs/measurements/guardians/d2c_callsite.
                // anthill` loaded clean with `flows_to(Untrusted, Public)` absent, and
                // DELETING `flows_to(Public, Public)` made the CONTROL call fail too —
                // proof that the discharge never depended on the argument at all).
                //
                // The same `subst` walk the declared EFFECTS take a few lines below
                // (`walk_type_deep_value` on each `pre_substituted` element): a
                // `requires` goal is likewise a term whose type-level variables the
                // call has decided, and this is their one substitution owner.
                let clause = walk_type_deep_value(kb, &subst, clause);
                // UNDETERMINED ⇒ FLOAT (WI-067 / WI-292: act on a DECIDED obligation,
                // never on an undetermined one). A FLEX variable surviving σ_type is one
                // no caller has bound and no later pass has solved, and deciding it here
                // by absence would be a verdict about the fact table rather than about
                // this call.
                //
                // A RIGID ONE IS NOT UNDETERMINED — WI-K88TN, and it is the reversal of
                // what this block first shipped. The comment here used to justify the
                // float by "deciding it here by absence would refuse every label-
                // polymorphic wrapper (`relay(t: Text[L = ?m]) = send(t)`)", and that
                // OVERSTATED ITS POPULATION: under the rigid reading the refusal reaches
                // only a polymorphic operation that calls a CONSTRAINED one without
                // declaring the constraint. `?m` is universally quantified in this body
                // (`rigidify_unwritten_sort_params`: "Inside the body it is therefore
                // rigid; at a CALL it is flexible again"), so `flows_to(?m, Public)` here
                // is `∀m. flows_to(m, Public)` — decided, and false — and the repair is
                // the one `requires` line the declaration owes. That obligation still
                // belongs on the ENCLOSING operation's contract; what changed is that the
                // contract must be WRITTEN rather than silently dropped.
                //
                // Γ IS WHAT DISCHARGES THE WRITTEN ONE, and it is why the seed below the
                // gate is not optional: `relay`'s own `requires flows_to(?m, Public)` is
                // an ASSUMPTION inside its body (proposal 050's Hoare reading), assumed
                // into Γ₀ by `op_requires_gamma` under the same `op.rigidify` this clause
                // was walked through, so producer and consumer name the same skolem. The
                // ordering trap the ticket named is real and is what this block's shape
                // answers: the `continue` runs BEFORE `precondition_proved`, so a Γ₀ seed
                // ALONE would change nothing — the rigid clause has to reach the prover,
                // and splitting the gate is what lets it.
                //
                // ASKED BEFORE σ_value, DELIBERATELY: at this point the only variables
                // present are the CALLEE's own, so a CALLER-introduced symbolic
                // argument — WI-539's "flounders ⇒ unproved ⇒ error" case, and WI-602's
                // rule-body float — is untouched by this gate and keeps its own rule
                // below. A value parameter is `var_ref(name: Ref(p))` (WI-552), a
                // functor and not a variable, so an ordinary `requires neq(b, 0)` never
                // reaches this `continue`.
                //
                // A MIXED CONJUNCT FLOATS WHOLE, and that is the answer rather than an
                // oversight. `clause_conjuncts` splits the comma list, but ONE goal may
                // name both an undecided type variable and a value parameter —
                // `requires in_range(?l, b)` — and there is no half of an atom to judge
                // separately: with `?l` undecided the atom is undecided, whatever `b`
                // is. Nor is a guarantee being given up. Before this change the same
                // goal went to the resolver with `?l` free, so it PASSED whenever any
                // label at all had a witness and raised only when none did — a verdict
                // about the fact table, not about this call. Floating it says the one
                // true thing. What a decided-VIOLATED mixed conjunct would deserve is a
                // constructive refutation under a free variable, which `refute_guard`
                // does not do and which WI-K88TN did NOT change: it split the gate on
                // rigid-vs-flex, so a conjunct still carrying a FLEX var floats exactly
                // as before. A mixed conjunct whose only variables are RIGID is now
                // decided, which is the same rule as the unmixed case and needs no
                // separate reading — `∀m` binds every occurrence of `?m` in the atom.
                if value_carries_undecided_var(kb, &clause) {
                    continue;
                }
                if precondition_proved(kb, flow, &req_sigma, &clause) {
                    continue;
                }
                // Unproved. In an op body that alone is the WI-539 violation. In a
                // rule body only a ground REFUTATION is (a float is skipped — WI-602).
                if !in_rule_body || precondition_refuted(kb, flow, &req_sigma, &clause) {
                    // REPORT THE CLAUSE AS JUDGED — both substitutions, in the order
                    // the check applied them — so the diagnostic names the bindings
                    // that refuted it rather than the declaration's variables:
                    // `flows_to(Untrusted, Public)`, not `flows_to(?l, Public)`, which
                    // says only that some label failed. σ_value goes on top of the
                    // σ_type walk already done above; a parameter with no clean
                    // argument twin survives it and is then read back in SOURCE
                    // spelling, so it reads as the `c` its author wrote rather than as
                    // the loader's `var_ref` wrapper.
                    let judged = substitute_ref_terms(kb, &clause, &req_sigma);
                    // WI-K88TN: a surviving RIGID is what says a DECLARATION is owed
                    // rather than a fact at this call — the same question the gate above
                    // asked, read at the other end. Asked on `judged` and not on the
                    // pre-σ_value clause because σ_value cannot introduce or remove a
                    // rigid (it maps value params to argument terms), so the two agree
                    // and this is the one already in hand.
                    //
                    // WHICH rigid decides WHICH repair, and a missing enclosing operation
                    // falls to the witness case rather than to a fallback: with no
                    // signature in scope there is likewise nothing to declare it on, so
                    // that message is the true one there too.
                    let kind = match clause_rigid_kind(kb, env, &judged) {
                        None => PreconditionFailure::AtCallSite,
                        Some(ClauseRigids::HasWitness) => {
                            PreconditionFailure::UndischargeableWitness
                        }
                        Some(ClauseRigids::AllParams) => match env.enclosing_op() {
                            Some(enclosing) => {
                                PreconditionFailure::UndeclaredInWrapper { enclosing }
                            }
                            None => PreconditionFailure::UndischargeableWitness,
                        },
                    };
                    let clause = goal_in_source_spelling(kb, &judged);
                    let err = TypeError::UnsatisfiedPrecondition {
                        span,
                        op: fn_sym,
                        clause,
                        kind,
                    };
                    // WI-20260830-JM7A8: RECORDED, NOT RAISED, wherever a drainer is
                    // installed — see [`TypingEnv::deferred_preconditions`]. Raising
                    // aborts this call before its effect row is built, and the op
                    // boundary then reports the precondition INSTEAD OF an undeclared
                    // effect the same call incurs, not beside it. The two are
                    // independent — a proof obligation over the KB and a row the body
                    // incurs — so both are owed. The remaining clauses are NOT judged
                    // (`break`, exactly where the `return` stood): a call reported one
                    // unsatisfied precondition before this change and reports one now.
                    match env.defer_precondition(err) {
                        None => break,
                        Some(err) => return Err(err),
                    }
                }
            }
        }
        // WI-067 (proposal 048 §"Typer delta" / 050 consumer 2): does the callee
        // carry any guarded effect element `L :- G`? Computed once so the >99% of
        // calls whose callee declares no guarded effect pay nothing — neither the
        // call substitution σ nor the per-atom refutation runs.
        // Scan under the REAL `subst` (not an empty one): a guarded atom can sit
        // behind a row-tail var that arg-unification bound to a guarded row
        // (WI-375 threaded-row path), and is revealed only through `subst` — the
        // same `subst` the per-effect discharge below walks with.
        let op_has_guarded = pre_substituted
            .iter()
            .any(|e| !collect_guarded_atoms(kb, &subst, e).is_empty());
        // The call substitution σ: callee param ↦ the actual argument's goal-term
        // twin (a literal `5`, a threaded `Ref(b)`). Applied to a guard before
        // refutation, so `div(a, 5)`'s `eq(b, 0)` becomes the ground `eq(5, 0)`.
        // (A threaded VARIABLE argument is already re-keyed into the guard by
        // `substitute_ref_syms` upstream; σ additionally carries the non-variable
        // arguments the rename cannot. An argument with no clean twin is absent —
        // its param stays symbolic and the guard flounders, conservatively kept.)
        let guard_sigma: HashMap<Symbol, TermId> = if op_has_guarded {
            build_call_guard_sigma(kb, &op.params, pos_args, named_args)
        } else {
            HashMap::new()
        };
        let mut substituted_op_effects: Vec<Value> = Vec::new();
        for e in &pre_substituted {
            // Deep-walk to propagate arg-unification bindings into nested effect
            // positions, then `walk_value_to_resolved` to SURFACE a top-level var
            // bound to a `Value::Node` — the term-deep walk stops at non-`Term`
            // bindings (walk_type keeps the var; its doc names `walk_term_to_
            // resolved` as the surfacing helper), so a written row threaded via
            // `bind_value` (WI-375, the `E = {Modify[c]}` path) would otherwise
            // leak as `?_`. The compose keeps the deep walk (for nested term vars)
            // and adds the recursive Node surface (chained var→…→Node bindings).
            //
            // PURE σ here (NOT the grounding `resolve_type_deep_value` used for
            // `resolved_ret`): the effect row carries no δ-groundable projection. An
            // effect-position projection is an `ExprCarried` (`effects s.E`, WI-396),
            // already eliminated when `proj_effects` was built above; and an
            // op-type-param `RigidProjection` δ-grounds VALUE members only — the
            // concrete-fill is Sort-kind-gated and a provider fact cannot bind an effect
            // member (effects aren't expressible as type args, WI-301) — so there is
            // nothing in the effect row for the grounding variant to reduce. (Revisit if
            // effect members ever become δ-groundable.)
            let deep = walk_type_deep_value(kb, &subst, e);
            let walked = walk_value_to_resolved(kb, &subst, deep);
            // WI-329 (handler discharge): the callee's declared element may itself be a
            // ROW rather than a label. A handler's result row is written `effects {Rho}`
            // — a bare row VARIABLE — and this call site is exactly where arg-unification
            // BOUND that tail to the residual (`{Modify[Res], Clock}` after `Error` is
            // dropped). The walk above therefore resolves the element to a BARE
            // `EffectExpression` (`merge(present(…), …)`), which carries no
            // `effects_rows(…)` wrapper and so missed the flatten below and was pushed
            // WHOLE as a single "label". That malformed atom is invisible at the op
            // boundary — `explode_incurred_effect_row` re-explodes it there (WI-441) —
            // but the LAMBDA arrow builder does not: `make_arrow_value` wraps each
            // element in `present(label = …)`, minting `present(label = merge(…))`. That
            // is what made a NESTED handler fail: the inner discharge's residual became
            // one opaque label in the enclosing lambda's row, and the outer handler's
            // callback-row check rejected it. Flatten the bare form here, at the
            // producer, so every reader of this flat atom list sees atoms.
            // Row-shaped means WRAPPED — there is no carrier the wrapper cannot hold,
            // because a row is a `Value::Term` or a `Value::Node` and nothing else
            // (WI-20260820-CTD6D; [`wrap_bare_effect_expr_as_row`]'s doc carries the
            // census that settles it, and the wrapper is total accordingly). The
            // pre-CTD6D `.flatten()` here declassified any other carrier back to a
            // plain atom, silently undoing this very flatten.
            push_effect_with_guard_discharge(
                kb,
                flow,
                &subst,
                &guard_sigma,
                op_has_guarded,
                walked,
                &mut substituted_op_effects,
            );
        }
        // WI-20260823-4GBQV: a `Modify` that STILL names one of the CALLEE's own
        // parameters got no argument to be re-keyed onto — refuse here, against the
        // caller's own expression, rather than letting the callee's parameter name
        // travel into the caller's row. AFTER the guard discharge above deliberately:
        // an atom the guard drops was never incurred, so refusing it earlier would
        // refuse a correct program (measured — `touch(mk(), false)` under a refuted
        // `{Modify[c] :- eq(flag, true)}` loads clean, and did so under the earlier
        // placement only because that one skipped guarded atoms outright).
        if !param_to_placeless_arg.is_empty() {
            if let Some(err) = unrekeyed_modify_argument(
                kb,
                &op,
                fn_sym,
                &substituted_op_effects,
                &param_to_placeless_arg,
                span,
            ) {
                return Err(err);
            }
        }
        // `mut`: a concretely-dispatched self-receiver spec op closes its
        // polymorphic effect row at the carrier below (WI-357).
        let mut effects = merge_effects(kb, &substituted_op_effects, &arg_effects);

        // WI-1094 (058 §3.4) — a NAMED requirement slot nobody bound is INFERRED, into
        // the substitution and therefore into `resolved_ret` below, so the choice rides
        // in the constructed value's type and every later bracket-less call reads it
        // back through σ. ABOVE the walk deliberately, and above
        // `selections_from_slot_bindings` too: this call's OWN dictionary build then
        // sees the inferred binding as an ordinary tier-1 pin, which is what makes the
        // answer compose instead of being re-derived per call. Its other half refuses
        // the ERASED slot, so it must also sit above every early return below — the
        // discipline WI-839 recorded for `check_selection_bindings`.
        infer_named_slot_bindings(
            kb,
            &mut subst,
            &op,
            fn_sym,
            &env.enclosing_dict_chain().clone(),
            env.param_rigids(),
            &selections,
            env.enclosing_op(),
            span,
        )?;

        // Resolve return type deeply so `Option[T = Var(vid_T)]`
        // collapses to `Option[T = Term]` once `vid_T` is bound. WI-341:
        // carrier-agnostic walk (the return type is a `Value`). `mut`: a
        // concretely-dispatched self-receiver spec op re-walks it below once
        // the carrier pins the spec's element params (WI-357).
        let mut resolved_ret = resolve_type_deep_value(kb, &subst, &proj_return_type);

        // WI-270: every declared op type-parameter must be pinned by
        // some combination of: explicit `[bindings]`, caller-side
        // `expected`, or argument unification. If a type-param's Var
        // is still unbound after all that, the call would silently
        // produce a `Var(?T)`-bearing return type; surface this as a
        // named diagnostic so the user can fix it by writing
        // `op[T = …](…)`. Replaces the WI-269 Phase D silent-drop
        // marker.
        //
        // WI-622: this is an OP-BODY call-site obligation (it lets the caller
        // recover the concrete return shape via a `let`-annotation / return
        // position). A rule body is relational and `dispatch_calls_in_occ` types
        // the dot with `expected: None`, so a return-only type-param has no
        // call-site pin here — but it is NOT a violation: SLD resolution unifies
        // the param against the goal context, or it stays a harmless phantom on a
        // value-less return-only param. Unlike the WI-602 precondition case there
        // is no DEFINITE sub-case to still raise on (see the `rule_body_dispatch`
        // field doc), so skip the whole check in rule-body context — mirroring how
        // WI-557/602 scoped the sibling value-precondition obligation.
        if !env.in_rule_body() {
            check_unconstrained_type_params(kb, &subst, &op, fn_sym, span)?;
        }

        // WI-272's per-call-site type-argument STAMP (`set_resolved_type_args`) was
        // written here, and WI-20260921-28TAT removed it with the channel it fed. What
        // it recorded — what each of the callee's `[T_i]` resolves to at THIS call — is
        // now carried by the requirement channel wherever it is still needed: a value
        // read of a rigid dispatches through its `TypeValue` slot (WI-20260919-N31XX),
        // and the reify boundary reads its payload sort out of the dictionary
        // `Error.reify requires ErrorTag[T = T1]` supplies.

        // WI-844 (058 §5.3 / §4.7): a NAMED requirement slot IS a type parameter, so
        // the chosen provider rides in the TYPE — and an argument carrying that type
        // says which as plainly as a bracket does. Read here, where `subst` is
        // complete, and BEFORE the validation below, so a type-carried pin is judged
        // by exactly the check a written one is.
        let selections = selections_from_slot_bindings(kb, &subst, &op, fn_sym, selections, span)?;

        // WI-20260921-3G1YT — ROUTE 4's slot source, for every classification block
        // below: the spec VIEWS this caller holds values of ([`held_spec_views`]).
        //
        // HERE, and not at the top of this function, because this statement is the
        // lowest point that dominates all of them — everything above returns before any
        // dictionary is built, so a call that builds none pays nothing. Both halves read
        // it: the SORT half through [`build_concrete_dispatch_dict`] and the OP half
        // through [`OpSupplyCtx::held`].
        // THE ARGUMENT TYPES OF THIS CALL, off the typed results rather than off
        // `param_to_arg_type`: that map is populated only for a callee whose signature
        // writes a PROJECTION (`needs_param_arg_types`), so for `MappedStream.map` — the
        // shape route 4 needs it for — it is empty. `collect_arg_errors` ran at the top of
        // this function, so every result here is `Ok`.
        let arg_types: Vec<Value> = pos_results
            .iter()
            .chain(named_results.iter())
            .filter_map(|r| r.as_ref().ok().map(|t| t.ty.clone()))
            .collect();
        let held_views = held_spec_views(kb, env, &arg_types);

        // WI-841 (058 §4.4 check 1, binding-precise half): judge every selection
        // against the GOAL it will be applied to, now that argument unification has
        // filled `subst`.
        //
        // Here rather than at each consumer: a slot is served by one of THREE routes
        // (the parent sort's dictionary, the spec-op dispatch, or — for an op-scoped
        // `requires` — value-direction at eval, which does not read the call's
        // selections), and only the first two have a place to complain from.
        //
        // And ABOVE the classification blocks below rather than after them, because
        // several of them RETURN: the WI-444 defaulted-spec-op carrier-override path
        // is one, and MEASURED, a wrong-bindings pin on such a call loaded clean when
        // this ran later. Placing it before every early return is the same discipline
        // WI-839's own review had to adopt — refuse above the returns, do not
        // enumerate them.
        check_selection_bindings(kb, &subst, fn_sym, &selections, span)?;

        // WI-365 (call-side): a self-receiver spec op WITH a default body
        // (`Stream.collect` / `takeN`) is consumed as a NORMAL op —
        // `lookup_spec_op_dispatch` (body-less only) returns `None` for it, so
        // the WI-357 carrier element/effect threading in the dispatch block
        // below never runs. When such an op is consumed on a concrete carrier
        // (a `List` walked as a `Stream`), its `effects E` row variable — the
        // enclosing sort's own effect param — stays an unbound `?_` (a provider
        // fact cannot bind an effect parameter; effects aren't expressible as
        // type arguments — WI-301), spuriously surfacing as `undeclared effect:
        // ?_` at a pure consumption site (`length(collect([1,2,3]))`). Thread
        // the element from the carrier and close the row the same way the
        // body-less path does. (The element usually already threads via
        // argument unification binding the sort param; the effect-close is the
        // load-bearing part and is NOT gated on the bind, so a pure carrier
        // still closes `E` even when the element bound separately.)
        if lookup_spec_op_dispatch(kb, fn_sym).is_none() {
            if let Some(spec_sort) = self_receiver_spec_sort(kb, &op, fn_sym) {
                if let ReceiverCarrier::Concrete(recv) =
                    receiver_carrier(kb, &op, spec_sort, named_args, pos_results, named_results)
                {
                    if bind_spec_params_from_carrier(
                        kb,
                        &mut subst,
                        &op,
                        spec_sort,
                        recv.sort,
                        named_args,
                        pos_results,
                        named_results,
                    ) {
                        resolved_ret = resolve_type_deep_value(kb, &subst, &proj_return_type);
                    }
                    let closed_op_effects: Vec<Value> = substituted_op_effects
                        .iter()
                        .filter(|e| !effect_is_unresolved_var(kb, e))
                        .cloned()
                        .collect();
                    effects = merge_effects(kb, &closed_op_effects, &arg_effects);
                }
            }
        }

        // WI-444: a DEFAULTED spec op (has its own body, so
        // `lookup_spec_op_dispatch` returned `None` and the body-less dispatch
        // block below is skipped) consumed on a CONCRETE carrier that declares
        // its OWN member backing the op must dispatch to that member —
        // typeclass default-method semantics (defaults fill GAPS, they do not
        // SHADOW). Statically PinNow to the carrier op, surfacing its real
        // effects (the WI-453 pattern — an override may incur an effect the
        // spec's default did not). The concrete carrier comes from whichever
        // shape `receiver_carrier` / `carrier_param_info` already classified:
        // the self-receiver (`collect(s: Stream)`) or carrier-param
        // (`size(c: C)`) form. A carrier WITHOUT an override classifies nothing
        // and falls through to run the default body. Eval's value-directed
        // override (eval.rs step 3) is the dynamic dual for an ABSTRACT-receiver
        // call this cannot pin.
        //
        // WI-1042 — "defaulted spec op" is [`defaulted_spec_op_parent`], the gate this
        // block OWNS and three other sites ask ([`dot_member_dispatch_decision`]'s
        // defaulted leg, [`call_dispatch_shape`]'s rule-body walk trigger,
        // [`defaulted_spec_op_witness_grounds_soundly`]'s witness scan). It stood here as
        // `lookup_spec_op_dispatch(..).is_none() && spec_op_parent_sort(..)`, which asks
        // one question twice: `lookup_spec_op_dispatch` IS `spec_op_parent_sort` plus the
        // body-less test.
        //
        // THE PRECONDITION THAT MAKES THE SWAP SAFE HERE, because the gate's body test is
        // STRICTER than the one it replaces (see its doc): this whole block is inside
        // `if let Some(mut op) = lookup_operation_info_full(kb, fn_sym)`, so `fn_sym` has
        // an `OperationInfo` by construction and the two readings coincide. Move this
        // block out of that bind and they stop coinciding.
        //
        // COST, corrected by this ticket's own review: the frame still reaches
        // `type_params_of_sort` FOUR times per defaulted-spec-op call
        // (`lookup_spec_op_dispatch` above, `self_receiver_spec_sort` beside it, this
        // gate, and `lookup_spec_op_dispatch` again at the body-less block below). It
        // was FIVE; collapsing the rest is a memo question (WI-1011), not a gate one.
        // The 51 µs O(|symbols|) figure that made those four matter is WI-954's — that
        // call is an owner-scope read now.
        if let Some(spec_sort) = defaulted_spec_op_parent(kb, fn_sym) {
            // WI-1027 moved the two-shape rule (and WI-608's abstract-spec exclusion)
            // into [`statically_pinned_carrier`], shared with the body-less guard.
            // A concrete carrier with no SUPPLIER at all yields an empty
            // `carrier_override_suppliers` list (WI-1010 — it is no longer route 1
            // alone) and defers at the gate below anyway.
            // `receiver_carrier` answers `NotApplicable` by itself when there is no
            // self-receiver param — `self_receiver_spec_sort` IS `spec_op_parent_sort`
            // plus that same param lookup, and `spec_sort` is that parent here — so a
            // `match self_recv_spec` wrapper around it would be a third gate that only
            // LOOKS authoritative.
            let recv_carrier =
                receiver_carrier(kb, &op, spec_sort, named_args, pos_results, named_results);
            // WI-20260917-NR6FJ DEFECT B: the declared slot speaks where the arguments are silent.
            // `.or_else`, so an argument-pinned carrier still wins — see the helper's doc
            // for why that order is the point and not an accident.
            let carrier =
                statically_pinned_carrier(kb, &recv_carrier, carrier_param_sym, Some(spec_sort))
                    .or_else(|| {
                        carrier_from_declared_slot(
                            kb,
                            env,
                            spec_sort,
                            &recv_carrier,
                            carrier_param_sym,
                            &op.params,
                        )
                    });
            // WI-1093: the SELF-RECEIVER half alone, which is what
            // `dispatch_spec_op_cached` discriminates on — the carrier-param shape rides
            // in the per-call `subst` instead, so passing it here would put it in the goal
            // TWICE. Same reading as the body-less block's `carrier_sym`, and named the
            // same way there.
            let self_recv_carrier =
                statically_pinned_carrier(kb, &recv_carrier, None, Some(spec_sort));
            if let Some(carrier_sym) = carrier.as_ref().map(|c| c.sort) {
                let op_qn = kb.qualified_name_of(fn_sym).to_string();
                let op_short_sym = kb.intern(short_name_of(&op_qn));
                // WI-1010: the impl may arrive by ANY of the three supply routes,
                // not just the carrier's own member — a WI-431 instance fact's
                // op-valued binding fills the same gap and must win over the
                // default for the same reason. See [`carrier_override_suppliers`].
                let cands =
                    carrier_override_suppliers(kb, spec_sort, carrier_sym, fn_sym, op_short_sym);
                // WI-1012 — a TIE on a STATICALLY CONCRETE carrier is refused HERE, at
                // load. WI-1010 left it to eval, which costs three things: `anthill check`
                // passes on a program the interpreter will refuse; a tie in a branch that
                // never runs never reports; and on the SLD path the refusal degrades to
                // SILENCE, because `resolve.rs`'s bridge residualizes
                // `AmbiguousSpecOpDispatch` to `None` and the enclosing rule just stops
                // answering (MEASURED: the rule below answered `[]`, and the program loaded
                // clean). Everything the diagnostic needs is in hand at the moment this
                // declines to pin — the span, the carrier and the route-rendered candidate
                // list — so declining silently was a fallback, not a deferral.
                //
                // Eval's read STAYS and shares this wording: this block fires only on a
                // concrete carrier, so an abstract-spec receiver still needs the late
                // refusal.
                //
                // WI-1042 — the CONDITION is [`arbitrate_defaulted_supplier_tie`], shared with
                // the dot spelling ([`dot_member_dispatch_decision`]) so one program cannot
                // be refused through `Desc.describe(x)` and accepted through `x.describe()`.
                // It takes the slice this arm already computed, so the pin below still walks
                // the suppliers once. Read its doc for why the count is bare here and
                // clause-narrowed in the body-less sibling.
                //
                // REACH — WI-1076 CLOSED THE LIMIT THIS PARAGRAPH USED TO RECORD, and took
                // the decision it demanded. It used to read: the refusal can only fire on
                // the CARRIER-PARAM shape (`describe(x: T)`), because for a SELF-RECEIVER
                // spec (`head(s: Stream)`) `provision_carrier_sort` filed every provision
                // under the spec's FIRST TYPE PARAM — `Stream`'s `T`, the element — so no
                // route-2/3 supplier reached such a carrier and `cands` never held two
                // (WI-450's carrier-as-artifact limit, 058 §12). It warned that closing it
                // would "silently widen a LOAD refusal over the stdlib's largest
                // defaulted-op family; it must be a decision taken there, not a side
                // effect."
                //
                // THE DECISION, taken deliberately and measured: the refusal now reaches
                // the self-representing shape too, and that is right. A provision keying at
                // its provider means a carrier's OWN member and its provision's op binding
                // are both visible for one op — before, one of the two was invisible and
                // route order picked the other SILENTLY, which is the exact defect this
                // whole family of refusals exists to prevent (WI-1010's rule that a written
                // implementation is never shadowed). The stdlib is unaffected: the full
                // workspace is green, no library provision writing an op binding beside its
                // carrier's own member exists. `wi1076_self_representing_spec_carrier_test::
                // a_supplier_tie_on_a_self_representing_spec_is_now_refused` pins the
                // widening so it cannot be undone by accident.
                //
                // IT IS PROSE, NOT A CLAUSE — the moment it becomes one it belongs in the
                // shared helper, not here.
                //
                // WI-1027 built the BODY-LESS half's guard out of the same construction
                // ([`supplier_tie_error`]), which is where the `NameableWitness` repair this
                // arm can never reach becomes reachable — a body-less op HAS the dispatch
                // slot a bracket binds.
                // WI-861: and it SELECTS — a tie the 058 §3.2 rung 2a default breaks
                // yields that supplier here, so `Some` now means "one supplier, or the
                // one silence takes" rather than "exactly one".
                let chosen = arbitrate_defaulted_supplier_tie(
                    kb,
                    spec_sort,
                    fn_sym,
                    carrier_sym,
                    &cands,
                    span,
                )?;
                // A supplier: pin it. NO supplier is the gap a default exists to
                // fill — fall through and run the spec's default body.
                if let Some(only) = chosen {
                    let impl_op = only.target;
                    let derived = dispatched_impl_effects(
                        kb,
                        flow,
                        impl_op,
                        &op.params,
                        &subst,
                        pos_args,
                        named_args,
                        pos_results,
                        named_results,
                    );
                    merge_effects_into(kb, &mut effects, &derived);
                    // WI-1093: RESOLVE THE SPEC AT THE PINNED CARRIER and hand the tree to
                    // the shared tail, which emits it as the callee's `dispatch_dict`
                    // (WI-829 `emit_tree_as_projection`). Without it this arm passed `None`
                    // and the pinned implementation was entered with NO requirements channel
                    // at all — so a carrier whose member reads one of its own
                    // PROVISION-CONDITION slots (058 §3.8: `provides Sp[Wrap] :- Sp[E]`,
                    // the shape `Pair`'s four provisions have) died
                    // `DeferToRequirement: … not bound … frame binds []`. The elements'
                    // dictionaries live in the INSTANCE and in nothing this arm built.
                    //
                    // This is the SAME resolution the body-less route runs a few hundred
                    // lines below, with the same arguments, and that is the point: whether
                    // the spec op happens to carry a default body decides which BODY runs,
                    // never what evidence the frame gets.
                    //
                    // THE OUTCOME IS DISCARDED ON PURPOSE, and this is the one place it
                    // could be mistaken for a silent skip. The impl is ALREADY chosen —
                    // `cands` named it, by whichever of the three supply routes — so this
                    // resolution is asked ONLY for the tree, and its verdict arbitrates
                    // nothing. Every non-`Unique` outcome yields `None`, which is exactly
                    // what this arm passed before, so no program changes shape on it:
                    //   * `Deferred` — the spec is a direct `requires` of the enclosing
                    //     sort, so the frame already carries it; `None` is the same-sort
                    //     inherit this arm has always taken, and is CORRECT, not a
                    //     degradation.
                    //   * `NoCandidates` — the carrier supplies the member but makes no
                    //     provision at these bindings, so no instance exists to thread.
                    //   * `NoMatch` / `Ambiguous` — raised on their own account by the
                    //     BODY-LESS route, which is the route that dispatches on them.
                    //     Raising here would newly refuse defaulted calls that run today,
                    //     which is a coherence change and not this ticket's.
                    // Nothing is swallowed: a body that DOES read a slot no tree supplied
                    // raises `DeferToRequirement: … not bound` NAMING the frame and its
                    // chain owner — the WI-822 LEG 2 policy, that "has a chain" and "needs
                    // it" are different questions and only the body answers the second.
                    //
                    // A SECOND CONSUMER, named because a first draft of this note claimed
                    // there was only one: `req_insertion::run` also reads
                    // `ConcreteApplyWithin.resolved_tree` and passes it to
                    // [`record_apply_within_concrete`], where `Some(tree)` switches the
                    // emitted `apply_within(requirements = …)` from
                    // `build_dispatching_dict_direct(callee_spec_sort, …)` — the parent
                    // bundle, keyed to the CALLEE's sort — to `emit_tree_as_projection`,
                    // keyed to the tree's resolved PROVIDER. So the tree decides the
                    // dictionary's `impl:` functor, hence the callee's `__req_self`, on
                    // both paths.
                    //
                    // THE PAIRING IS UNGUARDED, stated rather than asserted. `impl_op`
                    // comes from `cands` (`carrier_override_suppliers`); the tree's
                    // `impl_sort` comes from `sort_ops_lookup` inside `resolve_at_goal`.
                    // Nothing here requires them to name the same provider, and if they
                    // diverged `expand_dispatching_dict`'s `slots_for(owner)` would find
                    // the callee's parent is neither the layout's spec nor its provider
                    // and raise `Internal`. Examined and NOT driven: two attempts to make
                    // them disagree (a witness sort providing the spec at a carrier with
                    // its own same-named member, with and without slot reads) both came
                    // back non-`Unique`, so no tree was emitted and nothing changed. A
                    // `debug_assert` is deliberately not added for a relationship no
                    // fixture reaches — it would pin a claim this ticket cannot measure.
                    //
                    // COST, corrected by this ticket's own review: NOT one memoized walk.
                    // `dispatch_spec_op_cached` sets `cacheable = disambig.is_none() ||
                    // the goal is fully ground`, and this site always passes
                    // `Some(&dispatch_sigma)` — so a defaulted spec-op call inside a
                    // GENERIC body, where the spec's type param is still a var, bypasses
                    // the memo and re-runs `resolve_inner` on every visit. That is the
                    // common shape for the stdlib's defaulted-op family. Kept because the
                    // σ is what makes the resolution agree with the body-less route's
                    // (WI-829), and a tree resolved without it is not the same tree.
                    //
                    // Not gated on "will the tail use it" (`op_reads_requirement_slots`
                    // AND cross-sort) because that gate lives inside
                    // `classify_pin_or_apply_within`, and a second copy that drifted would
                    // drop the tree SILENTLY — the failure this fix exists to remove.
                    //
                    // REACHES A `debug_assert!` THIS ARM DID NOT CARRY BEFORE: with a tree
                    // in hand, `classify_pin_or_apply_within` asserts the emit succeeded.
                    // `ProjectionSyms::resolve` answers `None` on a KB without
                    // `anthill.reflect.Expr.var_ref` / `requirement_at_sort` /
                    // `Dictionary`, so a reflect-less debug build with a defaulted op
                    // pinned to a slot-reading supplier now panics in the typer where it
                    // used to degrade to `None`. Every fixture loads the stdlib, so
                    // nothing reaches it; recorded because it is a panic-vs-degrade
                    // change and not a no-op.
                    let dispatch_sigma = SigmaCtx {
                        subst: &subst,
                        param_rigids: env.param_rigids(),
                    };
                    let (_, resolved_tree) = dispatch_spec_op_cached(
                        kb,
                        &subst,
                        spec_sort,
                        op_short_sym,
                        env.enclosing_requires(),
                        self_recv_carrier.clone(),
                        Some(&dispatch_sigma),
                        &selections,
                        env.sub_goal_requires(),
                    );
                    classify_pin_or_apply_within(
                        kb,
                        occ,
                        fn_sym,
                        impl_op,
                        env.enclosing_sort(),
                        resolved_tree,
                        Some(&OpSupplyCtx {
                            subst: &subst,
                            caller_requires: env.enclosing_frame_chain(),
                            param_rigids: env.param_rigids(),
                            selected: &selections,
                            enclosing_op: env.enclosing_op(),
                            param_arg_types: &param_to_arg_type,
                            held: &held_views,
                        }),
                    )?;
                    return Ok(TypeResult {
                        ty: resolved_ret,
                        env: env.clone(),
                        effects,
                        node: Rc::clone(occ),
                    });
                }
                // WI-1093 ARM 2 / WI-1091 cause (1) — NO SUPPLIER, so the spec's own
                // DEFAULT BODY runs. It is still a call AT A CARRIER, and the evidence it
                // is entered with must be that carrier's INSTANCE. Falling through from
                // here reaches the Direct arm, which builds the WI-415 PARENT BUNDLE: the
                // SPEC's own `requires` chain resolved at the carrier, stamped with the
                // SPEC. Right for the default body's OWN reads (`Sp requires Base[T]` at
                // `T = Wrap` genuinely IS `Base[Wrap]`), wrong for the carrier's provision
                // CONDITIONS, which the bundle does not carry at all.
                //
                // NOT `dispatch_spec_op_cached`, and that is the crux: it resolves the
                // instance and then PROJECTS it to a member through
                // `sort_ops_lookup(impl_sort, op_short)`, discarding the tree when the
                // projection misses. Here it MUST miss — "no supplier" is exactly what
                // selects this arm — so it answers `NoMatch` with `None` and the fix is
                // INERT. What this arm wants is the INSTANCE, not a dispatch: the default
                // body is already the target and nothing is being chosen.
                //
                // GATED ON A CONSTRUCTED INSTANCE (`Leaf` / `Conditional`); every other
                // verdict falls through unchanged. `FromScope` is deliberately left alone
                // — the enclosing frame already carries that dictionary and the Direct
                // arm's inherit is right for it.
                //
                // MEASURED INERT ON ITS OWN (why WI-1093 reverted it): this FIRES — on the
                // wi1093 tower at both carriers and on stdlib `Iterable.find` at `List` —
                // and moves no verdict, because the eta reader's failure has a SECOND
                // cause in eval (`requirements_for_value_directed_impl` returns a
                // non-empty `incoming` unchanged after a value-directed redirect, so the
                // redirected impl runs on a channel built for another operation). Land it
                // WITH that one; the driver is
                // `wi1093_defaulted_call_instance_dict_test::pins_the_defaulted_fall_through_losing_the_elements_dictionary`,
                // which must flip from its pinned error to 10.
                let dispatch_sigma = SigmaCtx {
                    subst: &subst,
                    param_rigids: env.param_rigids(),
                };
                let goal = sort_goal_from_subst(kb, &subst, spec_sort, self_recv_carrier.clone());
                let scope = ResolutionScope {
                    available_requires: env.enclosing_requires(),
                    sigma: Some(&dispatch_sigma),
                    selected: &selections,
                    sub_goal_requires: &[],
                };
                // WI-1091 — `Conditional` ONLY, where WI-1093's draft took `Leaf` too.
                // The defect is precisely that the WI-415 parent bundle carries the
                // SPEC's chain at the carrier and none of the carrier's PROVISION
                // CONDITIONS; a provision with no conditions has nothing the bundle is
                // missing, so preferring an instance there changes the dictionary an
                // author sees for no reason and — measured on the stdlib — for a cost:
                // `Iterable.find` at `List` and `FiniteCollection.filter` at a carrier
                // that inherits `filter` from `Iterable` both resolve `Leaf`, and eval's
                // `dispatch_via_sort_ops_table` then walks that instance to a member of a
                // THIRD sort whose slots it does not carry (`Stream.find`,
                // `Iterable.filter`), which is `expand_dispatching_dict`'s WI-857 raise
                // and its `push_op_scoped_slots` twin.
                // WI-883 — no supplier, and the carrier may not be an instance at all.
                if let Some(refusal) = defaulted_call_at_non_instance(
                    kb,
                    env,
                    &subst,
                    &goal,
                    &selections,
                    carrier_sym,
                    fn_sym,
                    span,
                ) {
                    return Err(refusal);
                }
                let default_tree = match resolve(kb, &goal, &scope) {
                    ResolutionResult::Resolved(tree @ ResolvedRequiresNode::Conditional { .. }) => {
                        Some(tree)
                    }
                    _ => None,
                };
                // WI-1091 — …AND ONLY WHERE THAT INSTANCE SPEAKS ABOUT THE OPERATION
                // EVAL WILL ACTUALLY ENTER. `dispatch_via_sort_ops_table` resolves the
                // dictionary's own member for this op, and it can land on a THIRD sort:
                // `FiniteCollection.filter` at a carrier that INHERITS `filter` from
                // `Iterable` lands on `Iterable.filter`, whose chain no
                // `FiniteCollection[BoxColl]` dictionary carries. Handing it one is
                // `expand_dispatching_dict`'s WI-857 raise, deferred to run time —
                // measured on the stdlib as exactly that, plus the `push_op_scoped_slots`
                // twin for the op half (`Iterable.find` supplied, `Stream.find` entered).
                // Where the instance says nothing about that member it is not evidence
                // for this call, and the Direct arm's parent bundle stands unchanged.
                // [`dictionary_covers_target`] is the one owner of the question; the eval
                // guard asks it in the same words.
                // WI-1091 — …AND ONLY WHERE THE DEFAULT BODY IS WHAT ACTUALLY RUNS,
                // which is this arm's own stated premise, now ENFORCED rather than
                // assumed. It classifies `fn_sym` as its own target on the grounds that
                // "no supplier" means the spec's default body runs — but eval does not
                // take the classification's word for it: `dispatch_via_sort_ops_table`
                // walks the dictionary's OWN member for this op
                // (`resolve_op_target(dict.impl_sort(), fn_sym)`), and a resolved
                // instance can name a provider that HAS one. MEASURED on the stdlib:
                // `Iterable.find` at `List` resolves an instance whose impl is `Stream`,
                // whose `Stream.find` is then entered with a channel built for
                // `Iterable.find` — `push_op_scoped_slots`' producer/consumer desync
                // raise, and its `expand_dispatching_dict` twin one channel over.
                //
                // Asking the SAME `resolve_op_target` eval will ask is what keeps the two
                // from disagreeing; the equality is stronger than
                // [`dictionary_covers_target`] and subsumes it here (a target that IS the
                // spec op has the spec as its owner, which every layout covers).
                let default_tree = default_tree.filter(|tree| {
                    tree.impl_sort()
                        .is_some_and(|provider| resolve_op_target(kb, provider, fn_sym) == fn_sym)
                });
                if default_tree.is_some() {
                    // `fn_sym` as its OWN target: the default body is what runs, so the
                    // classification names the spec op on both sides, exactly as the
                    // Direct arm did — only the dictionary changes.
                    classify_pin_or_apply_within(
                        kb,
                        occ,
                        fn_sym,
                        fn_sym,
                        env.enclosing_sort(),
                        default_tree,
                        Some(&OpSupplyCtx {
                            subst: &subst,
                            caller_requires: env.enclosing_frame_chain(),
                            param_rigids: env.param_rigids(),
                            selected: &selections,
                            enclosing_op: env.enclosing_op(),
                            param_arg_types: &param_to_arg_type,
                            held: &held_views,
                        }),
                    )?;
                    return Ok(TypeResult {
                        ty: resolved_ret,
                        env: env.clone(),
                        effects,
                        node: Rc::clone(occ),
                    });
                }
            }

            // WI-883 — NO CARRIER WAS CLASSIFIED, which is also what a carrier providing
            // NOTHING looks like: the carrier-param classifier recognizes a carrier only
            // through a provision view. The call's goal still names it (`WeakOrd[T = P]`),
            // so the instance question is asked of the goal — for an operation with no
            // self-receiver, whose receiver would otherwise be the carrier (see
            // [`unclassified_goal_carrier`]). Those tests come first because they are
            // compares, and they keep every `List` member and every rule body off the walks
            // below. An abstract goal pins no carrier and passes untouched to the slot route.
            if carrier.is_none()
                && matches!(recv_carrier, ReceiverCarrier::NotApplicable)
                && env.enclosing_op().is_some()
            {
                let goal = sort_goal_from_subst(kb, &subst, spec_sort, None);
                if let Some(refusal) = unclassified_goal_carrier(kb, &goal).and_then(|c| {
                    defaulted_call_at_non_instance(
                        kb,
                        env,
                        &subst,
                        &goal,
                        &selections,
                        c,
                        fn_sym,
                        span,
                    )
                }) {
                    return Err(refusal);
                }
            }

            // WI-20260919-H20YY — NOTHING STATICALLY PINNED A CARRIER, so the enclosing
            // scope's `requires` slot is the only thing that can direct this call. Route
            // it through the SAME two slot routes a BODY-LESS spec op takes, instead of
            // falling through to a plain apply of the spec's default body — which is what
            // made a provider's override unreachable, silently. See the helper for the
            // measurement and for why the answer here is a deferral and not a carrier.
            //
            // LAST, after both carrier routes, and that order is the point: an argument
            // that names a carrier is argument-PRECISE evidence and a slot is not, so
            // this can only widen the block into ground where the carrier routes already
            // declined. It reaches no call that pins today.
            //
            // COST: [`call_names_no_carrier`] is asked a SECOND time here —
            // [`carrier_from_declared_slot`] asked it for its own route just above. Named
            // because the WI-1042 note at this block's head counts these reads, and its
            // expensive leg ([`sort_type_params_as_pairs`]) would be a fifth. It is not
            // hoisted: the gate is what makes that helper safe to call at all, so moving
            // it to the caller would leave a function whose contract is enforced
            // elsewhere. The duplicate is confined to calls that reach the expensive leg
            // — no self-receiver AND no classified carrier param, i.e. the NULLARY spec-op
            // shape — and every other call leaves on the two `matches!` compares. MEASURED
            // on the fixture load behind this ticket: 119 calls reach this block, 4 reach
            // the leg.
            if carrier.is_none()
                && call_names_no_carrier(
                    kb,
                    spec_sort,
                    &recv_carrier,
                    carrier_param_sym,
                    &op.params,
                )
            {
                let op_qn = kb.qualified_name_of(fn_sym).to_string();
                let op_short_sym = kb.intern(short_name_of(&op_qn));
                if defer_defaulted_call_to_slot(
                    kb,
                    env,
                    occ,
                    &subst,
                    spec_sort,
                    fn_sym,
                    op_short_sym,
                    &selections,
                ) {
                    return Ok(TypeResult {
                        ty: resolved_ret,
                        env: env.clone(),
                        effects,
                        node: Rc::clone(occ),
                    });
                }
            }
        }

        // WI-210 phase 3 dispatch (proposal 038): if `fn_sym` is a spec
        // op (declared without body on a parametric sort), look up the
        // unique impl op based on the per-call substitution. The proposal-
        // 038 unification of builtin-sort symbols (Int as the same Symbol
        // whether referenced bare or via anthill.prelude.Int64) makes
        // candidate matching deterministic — `fact Numeric[T = Int]` in
        // the rustland binding emits a SortProvidesInfo whose binding
        // value resolves to the same Int sort as the per-call subst sees.
        if let Some(spec_sort) = lookup_spec_op_dispatch(kb, fn_sym) {
            // The op's short name (e.g. "add" for "anthill.prelude.Additive.add")
            // joins with the impl sort to find the impl operation symbol.
            let op_qn = kb.qualified_name_of(fn_sym).to_string();
            let op_short_sym = kb.intern(short_name_of(&op_qn));
            let enclosing_requires = env.enclosing_requires();
            let enclosing_sort = env.enclosing_sort();

            // WI-350: classify the receiver to pick the dispatch carrier.
            // A self-receiver spec (`head(s: Stream)`) needs the receiver
            // argument's concrete carrier sort to disambiguate ≥2 impls
            // (its carrier is not a type-parameter, so the per-call subst
            // never pins it); an abstract spec value (`s : Stream[T]`)
            // carries no concrete impl and types through the interface.
            // WI-453 (§5.4 requirement-discharge): if a STRUCTURED carrier param
            // (`CpsMonad`'s `F` — the higher-kinded one, which has its own members)
            // has FILLED to a concrete sort through the arg/expected unify, THAT sort
            // is the dispatch carrier. Discharging the implicit `Spec[F = C]`
            // obligation IS confirming `C` provides the spec (the WI-431 instance
            // fact): no provision ⟹ a loud no-instance error here (closing the
            // otherwise-silent accept of `unit(42) : MyBox`); a provision ⟹
            // `dispatch_spec_op_cached` below routes to the instance's bound impl —
            // ONE mechanism for the arg-carrier (`flatMap(o:Option,…)`) and the
            // result-carrier (`unit(42):Option`, carrier only in the return). A
            // first-order carrier param has no members, so it keeps the
            // receiver-carrier / value-directed path unchanged.
            // PERF gate: the HK fill only applies to an op whose signature USES a
            // higher-kinded carrier — i.e. has a parameterized type (`F[T=A]`) in the
            // return or a param. A bare first-order op (`combine(x:T, y:T) -> T`) skips
            // the probe entirely, so the common case never pays the `type_params_of_sort`
            // / `sort_type_params_as_pairs` scans below.
            let op_has_parameterized_sig = matches!(
                type_head(kb, &op.return_type),
                TypeHead::Parameterized { .. }
            ) || op
                .params
                .iter()
                .any(|(_, t)| matches!(type_head(kb, t), TypeHead::Parameterized { .. }));
            let hk_carrier = op_has_parameterized_sig
                .then(|| {
                    sort_type_params_as_pairs(kb, spec_sort)
                        .iter()
                        .filter(|(p, _)| !kb.type_params_of_sort(*p).is_empty())
                        .find_map(|(_, var)| {
                            // WI-394: walk to a `Value` so a non-`Term`
                            // (`Value::Node`) carrier binding resolves through
                            // the view. A `Term` carrier views identically to
                            // the old `TermIdView` path; a `Node` that is not a
                            // concrete `sort_ref` yields `None` ("no HK
                            // carrier"), unchanged.
                            let walked = walk_term_to_resolved(kb, &subst, *var);
                            let c = extract_sort_ref_sym(kb, &walked)?;
                            (!is_sort_param_symbol(kb, c)
                                && kb.kind_of(c) == Some(crate::intern::SymbolKind::Sort))
                            .then_some(c)
                        })
                })
                .flatten();
            if let Some(c) = hk_carrier {
                // DISCHARGE the implicit `Spec[F = C]` obligation: confirm `C` provides
                // the spec (the WI-431 instance fact). No provision ⟹ undischarged: a
                // USER spec (warrants the abstract check) is a loud no-instance error
                // (never a silent accept of `unit(42):MyBox`); a host-builtin spec (no
                // fact by design) leaves the call as the spec op for the runtime to
                // resolve — the same escape the normal `NoCandidates` arm takes.
                if provider_spec_view_bindings(kb, c, spec_sort).is_none() {
                    if spec_warrants_abstract_check(kb, spec_sort) {
                        // WI-869: no search ran here — the obligation is discharged
                        // by the ABSENCE of a provision fact — so there is no unmet
                        // goal to name.
                        return Err(TypeError::DispatchNoMatch {
                            span,
                            op: fn_sym,
                            unmet: None,
                        });
                    }
                    return Ok(TypeResult {
                        ty: resolved_ret.clone(),
                        env: env.clone(),
                        effects,
                        node: Rc::clone(occ),
                    });
                }
                // DISPATCH to the instance's bound impl (`unit ↦ optionUnit`). The
                // result-carrier `unit` has no carrier VALUE to value-direct on (F is
                // only in the return), so the typer-resolved dispatch is the route; the
                // arg-carrier shares it. A spec-DEFAULT op (not bound in the fact) keeps
                // its body. `dispatch_spec_op_cached`'s SLD does not read instance-fact
                // op-bindings (WI-431 inc 2), so the impl is read straight from the fact.
                if let Some(impl_op) =
                    instance_fact_op_binding(kb, c, spec_sort, short_name_of(&op_qn))
                {
                    // WI-453 effect soundness (the WI-365 dual): surface the impl's real
                    // effects — the instance signature validator checks arity/param/return
                    // but NOT effects, so an effectful impl bound to a pure-declared spec
                    // op would otherwise mask its effect at the consumption site.
                    if impl_op != fn_sym {
                        let derived = dispatched_impl_effects(
                            kb,
                            flow,
                            impl_op,
                            &op.params,
                            &subst,
                            pos_args,
                            named_args,
                            pos_results,
                            named_results,
                        );
                        merge_effects_into(kb, &mut effects, &derived);
                    }
                    // PinNow, or ConcreteApplyWithin when the impl's OWN sort declares
                    // `requires` (so its dict threads) — the Unique-arm discipline. Only
                    // a runnable impl is rewritten (a body-less one stays the spec op).
                    if op_has_runnable_body(kb, impl_op) {
                        classify_pin_or_apply_within(
                            kb,
                            occ,
                            fn_sym,
                            impl_op,
                            enclosing_sort,
                            None,
                            Some(&OpSupplyCtx {
                                subst: &subst,
                                caller_requires: env.enclosing_frame_chain(),
                                param_rigids: env.param_rigids(),
                                selected: &selections,
                                enclosing_op: env.enclosing_op(),
                                param_arg_types: &param_to_arg_type,
                                held: &held_views,
                            }),
                        )?;
                    }
                }
                return Ok(TypeResult {
                    ty: resolved_ret.clone(),
                    env: env.clone(),
                    effects,
                    node: Rc::clone(occ),
                });
            }
            let carrier =
                receiver_carrier(kb, &op, spec_sort, named_args, pos_results, named_results);

            // WI-357: a concretely-dispatched self-receiver spec op (e.g.
            // `Stream.splitFirst` on a `List[Int]`) binds none of the spec's
            // own type parameters through argument unification — the argument
            // matched the *bare* `Stream` parameter, not `Stream[T]`. The
            // unbound `Stream.T` both leaves the return `?_` (a destructured
            // `pair(h, _)` gets `h : ?_`) and makes the dispatch goal abstract
            // (no impl matches → a spurious `requires Stream[…]` demand on the
            // caller). Recover the spec params from the receiver carrier's
            // provider fact (`List` provides `fact Stream[T = T]` ⇒ a
            // `List[Int]` as a `Stream` has `Stream.T = Int`) and re-walk the
            // return type so the element threads through and the dispatch goal
            // below is concrete.
            if let ReceiverCarrier::Concrete(recv) = &carrier {
                // WI-367: the spec params are usually already bound from this
                // carrier before expected-seeding (the early pass keys on the
                // op's PARENT sort), so this pass — keying on the dispatch-
                // resolved `spec_sort` — normally finds them filled and re-binds
                // nothing. It still runs as a fallback for the case where the
                // two resolve the spec to different symbols. `late_bound` records
                // whether it bound anything here.
                let late_bound = bind_spec_params_from_carrier(
                    kb,
                    &mut subst,
                    &op,
                    spec_sort,
                    recv.sort,
                    named_args,
                    pos_results,
                    named_results,
                );
                if late_bound {
                    resolved_ret = resolve_type_deep_value(kb, &subst, &proj_return_type);
                }
                // Close the spec op's OWN polymorphic effect row at this
                // concrete carrier. The provider fact cannot yet bind the
                // effect parameter (effects aren't expressible as type
                // arguments — WI-301 / WI-320), so the spec op's `effects E`
                // walked to an unresolved row variable above. A concrete
                // carrier that provides the spec realizes that row as its
                // own effect; the only expressible case today is a pure
                // provider (`List`), so drop the still-unresolved row var
                // rather than surface it as a spurious `undeclared effect:
                // ?_`. Self-disabling: once a provider CAN bind `E`, the
                // label resolves and is no longer a bare var, so it is kept.
                //
                // Re-merge with the UNTOUCHED `arg_effects` rather than
                // filtering the merged set, so a genuinely polymorphic
                // effect contributed by the receiver argument itself is
                // never erased — only the spec op's own row is closed.
                //
                // WI-367: gate on the carrier binding succeeding EITHER here or
                // in the early pass (`carrier_bound`), not on `late_bound`
                // alone — the early pass now usually consumes the binding, but
                // the row still needs closing. This reproduces the pre-WI-367
                // condition exactly (effect-close ran iff the carrier bound a
                // spec param) while letting the element bind move earlier.
                if carrier_bound || late_bound {
                    let closed_op_effects: Vec<Value> = substituted_op_effects
                        .iter()
                        .filter(|e| !effect_is_unresolved_var(kb, e))
                        .cloned()
                        .collect();
                    effects = merge_effects(kb, &closed_op_effects, &arg_effects);
                }
            }

            // WI-239: defer-to-requirement takes priority over provider-
            // based dispatch. If the spec op is reachable through the
            // enclosing sort's `requires` tree — directly (a frame slot)
            // or transitively (nested inside a direct requirement's
            // value) — the impl is selected at runtime from the threaded
            // requirement, so classify the deferral and skip dispatch.
            // The path's head is the direct frame slot; its tail is the
            // `requirement_at_sort` projection path (empty for a direct
            // require). The pre-WI-239 flat chain made transitive specs
            // direct slots, so `dispatch_spec_op_cached`'s direct-only
            // trigger covered them; under the direct-chain ABI the nested
            // case needs this tree walk.
            //
            // WI-841: unless the CALL SITE pinned this spec. Deferring is a FORWARD —
            // "the enclosing frame's dictionary answers this" — and explicit selection
            // outranks a forward exactly as it outranks a search (§4.1 tier 1). This
            // pre-check runs BEFORE dispatch and RETURNS, so without the gate the pin
            // is swallowed here and the twin gate inside `dispatch_spec_op_cached` is
            // never reached: measured, `Monoid.combine[Monoid = AnyM](a, b)` written
            // inside a sort that `requires Monoid[…]` computed the SEARCHED answer.
            // Two gates, because there are two places that decide to defer.
            let pinned_spec = pinned_witness_for(kb, &selections, spec_sort).is_some();
            if !pinned_spec && !enclosing_requires.is_empty() {
                // WI-613: the σ context lets `find_requires_location` disambiguate
                // two same-spec `requires` over distinct element params by element
                // identity, instead of blind first-match.
                let sigma_ctx = SigmaCtx {
                    subst: &subst,
                    param_rigids: env.param_rigids(),
                };
                if let Some(path) = enclosing_sort.and_then(|encl| {
                    find_requires_location(kb, &subst, spec_sort, encl, Some(&sigma_ctx))
                }) {
                    // `path` is non-empty on `Some`. Head = direct frame
                    // slot; tail = projection path into its bundled value.
                    let slot = path[0];
                    let proj_path: SmallVec<[usize; 2]> = path[1..].iter().copied().collect();
                    // WI-232: capture the matched direct-require entry so
                    // req_insertion::run can read it without re-indexing.
                    let resolved_spec = enclosing_requires[slot].clone();
                    classify(
                        kb,
                        occ,
                        CallClass::DeferToRequirement {
                            spec_op_sym: fn_sym,
                            op_short_sym,
                            resolved_spec,
                            slot,
                            proj_path,
                            enclosing_sort,
                            enclosing_op: env.enclosing_op(),
                        },
                    );
                    return Ok(TypeResult {
                        ty: resolved_ret.clone(),
                        env: env.clone(),
                        effects,
                        node: Rc::clone(occ),
                    });
                }
            }

            // WI-1091 — THE OPERATION'S OWN `requires` IS READ AT THE SAME POINT, and
            // this is what makes the two spellings agree rather than merely coexist.
            //
            // The pre-check above is the whole of WI-239's rule — "defer-to-requirement
            // takes priority over provider-based dispatch" — and it read the SORT's chain
            // alone. WI-822 LEG 1 gave an operation's own `requires` real frame slots and
            // a call-site supply, and WI-1091 widened which dispatch outcomes may read
            // them; but reading them only from the outcome arms leaves the licence
            // INVISIBLE wherever dispatch resolves, which is the ordinary case.
            //
            // MEASURED, and it is what the ticket's acceptance turns on:
            // `probe(a: HT, b: HT) requires Monoid[T = HT] = Monoid.combine(a, b)` over a
            // GROUND `AddM` and a PARAMETRIC `AnyM`. At the abstract `HT` only `AnyM`
            // matches, so dispatch answers `Unique(AnyM.combine)` and pins the body at
            // load — no outcome arm is reached, no slot is read, and every call computes
            // `AnyM`'s 99. Including `probe[Monoid = AddM](2, 3)`, which is the SILENT
            // WRONG NUMBER WI-841 refused rather than ship. Its sort-level twin answers
            // 5/5/99 through this very pre-check.
            //
            // ORDER: the sort half is tried FIRST and this is its fallback, so no call the
            // sort chain already served can change hands. That is also the chain's own
            // order — an operation's slots follow its sort's ([`op_dict_entries`]) — and
            // `op_scoped_defer_location` answers in the COMPOSED numbering, so the two
            // arms hand `CallClass::DeferToRequirement` slots off one list.
            if defer_to_op_scoped_slot(
                kb,
                env,
                occ,
                &subst,
                spec_sort,
                fn_sym,
                op_short_sym,
                enclosing_sort,
                pinned_spec,
            ) {
                return Ok(TypeResult {
                    ty: resolved_ret.clone(),
                    env: env.clone(),
                    effects,
                    node: Rc::clone(occ),
                });
            }

            // WI-350: an abstract spec receiver (`s : Stream[T]`, or an
            // unresolved receiver type) that the `requires` pre-check above
            // did not cover pins no concrete impl. Type through the spec
            // op's interface signature (`resolved_ret`, already walked
            // through the per-call subst) and leave the call as the spec
            // op — eval resolves the impl from the runtime value's own
            // sort. Skipping concrete dispatch is what keeps a ≥2-impl
            // self-receiver spec from resolving `Ambiguous` for a
            // legitimately abstract call.
            if carrier == ReceiverCarrier::Abstract {
                // WI-325 exception: a spec that warrants the abstract check but
                // has NO provider at all (a user-defined, wholly-unimplemented
                // spec) has no runtime witness to defer to — every call will
                // fail at first dispatch. Fall through to the dispatch
                // `NoCandidates` arm so that case is surfaced at type-check
                // (that arm still returns the same interface type, just with the
                // diagnostic attached). Specs with ≥1 provider — and host
                // built-ins, which deliberately have none and don't warrant the
                // check — take the deferring early return.
                let has_witness = spec_has_any_providers(kb, spec_sort)
                    || !spec_warrants_abstract_check(kb, spec_sort);
                if has_witness {
                    return Ok(TypeResult {
                        ty: resolved_ret.clone(),
                        env: env.clone(),
                        effects,
                        node: Rc::clone(occ),
                    });
                }
            }
            // WI-496: a body-less CARRIER-PARAM spec op (`Iterable.iterator(c: C)`)
            // on a concrete carrier that provides the spec only TRANSITIVELY — a
            // `List`, whose Iterable-ness rides through `List provides Stream` +
            // `Stream provides Iterable` with no direct `List provides Iterable`
            // fact (the `transitive` flag the classification above already set on
            // `carrier_param_info`). Direct dispatch cannot resolve it:
            // `dispatch_spec_op_cached` LOOSELY matches `Stream provides Iterable`
            // (List ≤ Stream, provider admissibility) and then recurses into
            // Stream's `requires EffectsRuntime`, which an identity iterator never
            // threads → a spurious `DispatchNoMatch`. Leave the call as the spec op
            // — its return type is already threaded from that same transitive
            // provision view — and let eval's value-directed dispatch (WI-492,
            // `transitive_carrier_for_param` → `Stream.iterator`) resolve the impl
            // from the runtime value's own sort, exactly the deferral the abstract-
            // receiver arm above takes. A DIRECT (`IntBag provides Iterable[C =
            // IntBag]`) or WITNESS (`IntBar provides Bar[T = Int64]`, WI-450)
            // provider has `transitive == false` and still dispatches concretely.
            //
            // WI-598: the SAME deferral is owed when the carrier sort is ITSELF an
            // abstract spec — a value whose static type is `FiniteStream` (the
            // declared return of the finite `map`/`filter`), which provides
            // FiniteCollection DIRECTLY (so `transitive == false`) yet has no
            // concrete representation of its own. Resolving it concretely picks the
            // FiniteStream impl and then recurses into `FiniteStream provides Stream
            // → Stream requires EffectsRuntime[E]`, unsatisfiable at the abstract
            // access row `E` → the same spurious `DispatchNoMatch`. The runtime value
            // is some concrete provider (a `List`), so defer to eval's
            // value-directed dispatch exactly as the abstract self-receiver arm
            // (`carrier == Abstract`) above does — the carrier-param analogue of it.
            //
            // WI-1027 — the abstract-spec half of that test is asked THROUGH
            // [`statically_pinned_carrier`], and the answer is kept, because the two
            // consumers of it in this frame must not each pay for it: `carrier_is_abstract_-
            // spec` reaches `sort_has_constructors`, which `format!`s a prefix and SCANS
            // every qualified name in the KB. One evaluation per call site, shared with the
            // supplier-tie guard below. (The self-receiver arm passes `None` for the carrier
            // param, so it cannot reach the predicate at all.)
            // WI-20260828-EKWDC: ONE ask, two readings — `dispatch_carrier` is what the
            // goal is built from (sort AND the receiver's own arguments), `carrier_sym` its
            // sort alone, for the readers that ask only about carrier identity. Derived and
            // not re-asked, so the two cannot name different carriers.
            let dispatch_carrier = statically_pinned_carrier(kb, &carrier, None, Some(spec_sort));
            let carrier_sym = dispatch_carrier.as_ref().map(|c| c.sort);
            let pinned_carrier =
                statically_pinned_carrier(kb, &carrier, carrier_param_sym, Some(spec_sort))
                    .map(|c| c.sort);
            if matches!(&carrier_param_info, Some((.., true, _)))
                || (carrier_param_sym.is_some() && pinned_carrier.is_none())
            {
                return Ok(TypeResult {
                    ty: resolved_ret.clone(),
                    env: env.clone(),
                    effects,
                    node: Rc::clone(occ),
                });
            }

            // WI-829: thread the call-site σ into the dispatch defer trigger so a
            // sole coarse cover whose compound element σ-disagrees (shallow-vs-deep)
            // does NOT re-defer here after `find_requires_location` above already
            // refused it — construction of the deeper dictionary runs instead.
            let dispatch_sigma = SigmaCtx {
                subst: &subst,
                param_rigids: env.param_rigids(),
            };
            let (outcome, resolved_tree) = dispatch_spec_op_cached(
                kb,
                &subst,
                spec_sort,
                op_short_sym,
                enclosing_requires,
                dispatch_carrier,
                Some(&dispatch_sigma),
                &selections,
                env.sub_goal_requires(),
            );
            // WI-508: a NULLARY spec op (`new() -> C`, carrier only in the
            // RESULT) gets no carrier from value args, so value-directed
            // dispatch finds nothing. Resolve the carrier from the EXPECTED
            // RETURN TYPE (a concrete annotation pins it) or, failing that, from
            // a UNIQUE provider (information hiding); 2+ providers with nothing
            // pinning the carrier is a loud ambiguity. A `requires`-covered call
            // (a generic consumer over `requires MutableCollection`) already
            // took the Deferred path in `dispatch_spec_op_cached`, so this only
            // fires for the concrete / standalone call.
            let outcome = if op.params.is_empty()
                && matches!(outcome, DispatchOutcome::NoCandidates)
            {
                resolve_nullary_result_carrier(kb, spec_sort, fn_sym, op_short_sym, &resolved_ret)
                    .unwrap_or(DispatchOutcome::NoCandidates)
            } else {
                outcome
            };
            // WI-1027 — the BODY-LESS half of WI-1012's load refusal, raised ONCE above
            // the outcome arms rather than at each of them (the "refuse above the returns,
            // do not enumerate them" discipline WI-839's review adopted and WI-841's
            // `check_selection_bindings` placement follows). The rule, the two narrowing
            // clauses and the measurements are at [`arbitrate_unarbitrated_supplier_tie`];
            // what has to be said HERE is only what is local to this frame.
            //
            // THE CARRIER IS NOT `carrier_sym`. That reading made the whole guard inert on
            // its own fixtures — MEASURED, and it read as "loads clean". `carrier_sym` is
            // the SELF-RECEIVER carrier, which `dispatch_spec_op_cached` takes because that
            // is the shape the per-call subst does NOT pin; every fixture this ticket
            // drives is the CARRIER-PARAM shape (`describe(x: T)`), whose carrier is
            // `carrier_param_sym`. `statically_pinned_carrier` is asked for both.
            //
            // EXHAUSTIVE, not a guarded wildcard, and for the reason `resolve_inner` states
            // 5500 lines below in this same file: a `!matches!(…)` test would default a
            // sixth `DispatchOutcome` to GUARDED, so a new variant that raises on its own
            // account would silently have its targeted diagnostic pre-empted by this
            // general one, with no reachability lint. The two excluded outcomes each name
            // something this refusal cannot — a provision tie carries `InstanceTie`'s
            // provider symbols and its own `TieRepair` (a bracket binding the DISPATCH
            // slot), and `DispatchNoMatch` says the dispatch resolved nothing at all.
            //
            // THE EXCLUSION USED TO COST SOMETHING, and WI-1032 closed it — kept here
            // because the shape is the one a reader will try next. When the carrier ALSO
            // self-provides the spec, this route-1-vs-route-2 tie used to reach `Ambiguous`
            // instead and print `Leaf, Leaf` with `TieRepair::ValueDirected`, the exact
            // rendering WI-1012 gave the supplier tie its own variant to avoid. The repair
            // was NOT to reword `render_instance_tie`: the two provisions AGREE as
            // provisions (an op binding is not a type-param binding, so it reaches no
            // `Candidate` field), so `collect_provides_candidates` now collapses them to
            // one and the conflict arrives HERE, where the routes can be named.
            let outcome_raises_on_its_own_account = match outcome {
                DispatchOutcome::Ambiguous(_) | DispatchOutcome::NoMatch { .. } => true,
                DispatchOutcome::NoCandidates
                | DispatchOutcome::Unique(_)
                | DispatchOutcome::Deferred => false,
            };
            // TIER 1 outranks this refusal, as it outranks BOTH defer triggers for the same
            // reason: the author named a provider, so nothing here is unselected. Reads the
            // `pinned_spec` the WI-841 pre-check already computed rather than asking again
            // — `pinned_witness_for`'s own doc records "one statement said four times" as
            // the typer's standing hazard, and a re-ask would keep the old semantics with
            // no compile error once 058 phase 3b makes the gate slot-precise.
            if !outcome_raises_on_its_own_account && !pinned_spec {
                if let Some(pinned_carrier) = pinned_carrier {
                    // WI-861: the supplier the rung named is DISCARDED here, and only here
                    // — this frame selects nothing. `dispatch_spec_op_cached` above already
                    // resolved the call, reading the same rung one layer down at
                    // `resolve_inner`, and lands on the same provider. The DOT caller,
                    // which does select, keeps the answer.
                    let _rung_answer = arbitrate_unarbitrated_supplier_tie(
                        kb,
                        spec_sort,
                        pinned_carrier,
                        fn_sym,
                        op_short_sym,
                        span,
                    )?;
                }
            }
            match outcome {
                DispatchOutcome::NoCandidates => {
                    // WI-606: a CONCRETE receiver carrier that statically declares a
                    // runnable override of this self-receiver spec op, yet the dispatch
                    // found no candidate — because the spec op's provision `requires`
                    // (`Stream requires EffectsRuntime[E]`) does not discharge against the
                    // carrier's ABSTRACT effect row (`Mapped provides Stream[E = {ES,
                    // EF}]`, ES/EF the enclosing witness's own rows). The override IS the
                    // runtime target (a qualified `Mapped.splitFirst(m)` static call pins
                    // it), so `PinNow` to it and defer the effect-row discharge to eval —
                    // instead of demanding a spurious `requires Stream` on the enclosing
                    // sort. `resolved_ret` was already threaded from the impl's own return
                    // (the projection-elimination fallback above). `concrete_self_receiver_-
                    // override` gates on a genuine self-receiver override (not a coincidental
                    // same-named member), so a carrier WITHOUT one resolves `None` and falls
                    // through to the WI-325 pass-through / abstract-coverage demand unchanged;
                    // a carrier whose dispatch resolved `Unique` never reaches here.
                    if let Some(impl_op) = carrier_sym
                        .filter(|_| self_recv_spec.is_some())
                        .and_then(|c| concrete_self_receiver_override(kb, c, fn_sym, op_short_sym))
                    {
                        let derived = dispatched_impl_effects(
                            kb,
                            flow,
                            impl_op,
                            &op.params,
                            &subst,
                            pos_args,
                            named_args,
                            pos_results,
                            named_results,
                        );
                        merge_effects_into(kb, &mut effects, &derived);
                        classify_pin_or_apply_within(
                            kb,
                            occ,
                            fn_sym,
                            impl_op,
                            enclosing_sort,
                            None,
                            Some(&OpSupplyCtx {
                                subst: &subst,
                                caller_requires: env.enclosing_frame_chain(),
                                param_rigids: env.param_rigids(),
                                selected: &selections,
                                enclosing_op: env.enclosing_op(),
                                param_arg_types: &param_to_arg_type,
                                held: &held_views,
                            }),
                        )?;
                        return Ok(TypeResult {
                            ty: resolved_ret.clone(),
                            env: env.clone(),
                            effects,
                            node: Rc::clone(occ),
                        });
                    }
                    // WI-883 — A CALL THAT NAMES A CARRIER WITH NO CANDIDATE: the carrier
                    // provides no such spec, and the call is refused here rather than
                    // passed through to die at eval with "operation has no body". The
                    // enclosing operation's own `requires` is exempt — an ASSUMPTION its
                    // callers discharge (058 §3.9), the licence WI-562 grants below — and
                    // so is a host-implemented callee (see the helper). An abstract
                    // carrier names nothing and falls through to WI-325.
                    //
                    // AN OPERATION BODY ONLY. A rule-body spec-op call has its own owner,
                    // `check_rule_body_requirements`, which reads the clause's declared
                    // `requires(…)` as the rule's own dictionary; answering here too gave
                    // one call two diagnoses, and refused the declared clause
                    // `wi642…::declared_in_body_requires_loads_clean` pins as legal.
                    if env.enclosing_op().is_some()
                        && !op_requires_covers_call(kb, env, &subst, spec_sort)
                    {
                        let goal = sort_goal_from_subst(kb, &subst, spec_sort, None);
                        if let Some(refusal) = pinned_carrier
                            .or_else(|| unclassified_goal_carrier(kb, &goal))
                            .and_then(|c| unprovided_spec_at_carrier(kb, &goal, c, fn_sym, span))
                        {
                            return Err(refusal);
                        }
                    }
                    // WI-325: distinguish concrete-binding NoCandidates from
                    // abstract-binding NoCandidates with no covering `requires`
                    // (unsafe — dispatch will fail at first call site). A concrete
                    // carrier that is no instance was refused just above (WI-883);
                    // one that reaches here is an instance by a route the goal did
                    // not match, or a host-implemented callee: leave it untagged so
                    // the call stays as the spec op.
                    // Abstract: tag the occurrence so `req_insertion::run`
                    // can emit a `MissingRequiresForSpecOp` diagnostic.
                    //
                    // Gate on `spec_warrants_abstract_check`: stdlib specs
                    // like `Map`, `List`, `Stream`, `Collection`, `Iteration`,
                    // … deliberately have zero `fact Spec[…]` records —
                    // they're host built-ins where the runtime resolves
                    // operations directly. Abstract calls against such
                    // specs are intentionally allowed (the `NoCandidates`
                    // doc comment names them). User-defined specs (outside
                    // the `anthill.*` namespace) without providers are NOT
                    // host-builtin — they're the WI-324 'forgot to register
                    // an impl' case and warrant the diagnostic. Stdlib
                    // specs with at least one provider (Eq, Numeric, Ord,
                    // …) also warrant it — the spec_has_any_providers leg.
                    //
                    // Detection lives here because the per-call substitution
                    // is still in scope; `req_insertion::run` only sees the
                    // IR shape, not the typer's subst.
                    //
                    // Why we walk type_params directly instead of consuming
                    // `sort_goal_from_subst`: `sort_goal_from_subst` only
                    // emits a binding when the spec var resolves to a
                    // `Value::Term` — but unification often binds the
                    // *caller's* var to the spec's var (e.g. `Container.T
                    // → Eq.T`), leaving the spec's var as the equivalence-
                    // class root with no direct binding. Resolving the
                    // spec's var then returns `None`, and the goal has zero
                    // bindings even though `T` is plainly abstract. The
                    // direct walk treats `None`-resolved AND
                    // `Var`-resolved as abstract.
                    //
                    // Loader-inconsistency arms (the three former silent
                    // `continue`s) now treat the param as abstract: if we
                    // can't introspect the param's alias var, we can't
                    // prove it's concrete either, so the conservative
                    // outcome is to surface the diagnostic. This guards
                    // against a future spec representation (e.g. denoted
                    // / value-in-type params per WI-302) silently disabling
                    // the WI-325 protection.
                    //
                    // WI-562: op-scoped `requires` coverage (WI-448) — the
                    // op-scoped dual of the sort-level defer-to-requirement. If
                    // the enclosing OPERATION's OWN `requires` covers this spec,
                    // an abstract `NoCandidates` is LICENSED (leave the call as
                    // the spec op for value-directed eval) instead of demanding a
                    // sort-level `requires`. This lets `List.member`'s `Eq[T]`
                    // need live on `member` instead of the whole `List` sort,
                    // which a sort-level `requires Eq[T]` wrongly imposed on every
                    // dispatch through `List` (`IndexedSeq.nth` on a `List[NonEq]`
                    // — diamond coherence makes a sort `requires` thread at EVERY
                    // dispatch). A concrete `NoCandidates` is already a legitimate
                    // pass-through below, so this only changes the abstract case.
                    // WI-653: carrier-aware coverage — the licensing `requires` must
                    // supply `spec_sort` OVER THE CALL'S CARRIER, not merely by symbol.
                    if op_requires_covers_call(kb, env, &subst, spec_sort) {
                        // WI-1091: licensed by the enclosing op's own `requires` — and
                        // now DEFERRED to the slot that licence names, when the chain
                        // has one. See `defer_to_op_scoped_slot`.
                        defer_to_op_scoped_slot(
                            kb,
                            env,
                            occ,
                            &subst,
                            spec_sort,
                            fn_sym,
                            op_short_sym,
                            enclosing_sort,
                            pinned_spec,
                        );
                    // WI-590 — an abstract dispatch the ENCLOSING SORT's `requires` covers
                    // is DECLARED to resolve, so it must not be reported as a
                    // missing-`requires`: the sort-level twin of WI-562's op-scoped licence.
                    // Leave the call as the spec op for value-directed eval, exactly as that
                    // licence does.
                    //
                    // ORDER MATTERS, and it is the op-scoped licence that must come first:
                    // the two read INDEPENDENT sources (`env.op_requires()` vs the enclosing
                    // SORT's `direct_requires`), so a call both cover would otherwise skip
                    // `defer_to_op_scoped_slot` and lose WI-1091's dictionary-slot
                    // classification — the thing that makes an op-scoped slot's supply, and a
                    // call-site `[Spec = Impl]` selection, reach the call at all.
                    } else if enclosing_requires_clause.is_some() {
                    } else if spec_warrants_abstract_check(kb, spec_sort) {
                        let spec_qn = kb.qualified_name_of(spec_sort).to_string();
                        // WI-387 FIX 3: the receiver carrier's provider fact may
                        // bind a spec param to a GROUND value (`List provides
                        // Stream[E = {}]`). `bind_spec_params_from_carrier`
                        // threads only type-param-REF provider bindings (`Stream.T
                        // ↦ List.T`) into the subst, so a written ground row never
                        // reaches the per-param subst resolution below and would be
                        // wrongly flagged abstract — regressing delivered
                        // wi357/wi210 once `List` writes `E = {}`. Such a param is
                        // concrete → COVERED, so skip it; a provider binding that
                        // mentions a type-param stays abstract (still demands a
                        // `requires`, e.g. a `C provides Iterable[Element = C.T]`).
                        let provider_bindings =
                            carrier_sym.and_then(|c| provider_spec_view_bindings(kb, c, spec_sort));
                        let mut abstract_params: SmallVec<[Symbol; 2]> = SmallVec::new();
                        for short in kb.type_params_of_sort(spec_sort) {
                            if provider_bindings.as_ref().is_some_and(|binds| {
                                binds.iter().any(|(p, v)| {
                                    short_name_of(kb.local_name_of(*p)) == short.as_str()
                                        && type_value_is_ground(kb, *v)
                                })
                            }) {
                                continue;
                            }
                            let short_qn = format!("{spec_qn}.{short}");
                            let short_qn_sym = match kb.try_resolve_symbol(&short_qn) {
                                Some(s) => s,
                                None => {
                                    // Loader inconsistency — qualified param
                                    // name missing. Conservatively report.
                                    abstract_params.push(kb.intern(&short));
                                    continue;
                                }
                            };
                            let alias_target = match resolve_sort_alias(kb, short_qn_sym) {
                                Some(t) => t,
                                None => {
                                    // No SortAlias fact — can't introspect.
                                    abstract_params.push(short_qn_sym);
                                    continue;
                                }
                            };
                            let vid = match kb.get_term(alias_target) {
                                Term::Var(Var::Global(v)) => *v,
                                _ => {
                                    // Future-shape alias (denoted/value-
                                    // dependent) — assume abstract.
                                    abstract_params.push(short_qn_sym);
                                    continue;
                                }
                            };
                            // A spec type parameter the CALLED OPERATION's signature
                            // never mentions cannot be what any dispatch turns on: no
                            // argument carries it, no return exposes it, no effect row
                            // names it. No witness could supply it and no `requires` could
                            // cover it, so demanding one refuses a well-typed program.
                            //
                            // MEASURED: `reify[Rho, X, T1](body: () -> X @ {Error[T1],
                            // Rho}) -> Result[E = T1, T = X]`, declared inside
                            // `sort Error { sort T = ? }`, names the sort's `T` NOWHERE —
                            // `T1` is the payload and is inferred from the body. Without
                            // this filter the sort's `T` is flagged abstract and the call
                            // refused, but only OUTSIDE `anthill.*`, because
                            // `spec_warrants_abstract_check`'s namespace leg is what turns
                            // the flag into a diagnostic. One program's verdict therefore
                            // depended on the namespace it was declared in.
                            //
                            // `type_mentions_spec_param` and NOT `occurs_in_view` on the
                            // alias var: a declared parameter type names the spec param by
                            // SYMBOL (`Ref(MySpec.T)`) as readily as by variable, and the
                            // var-only test missed the symbol spelling — measured, it let
                            // `MySpec.same(a: T, b: T)` through on an abstract `T`, which
                            // is precisely the WI-325 case that must still be refused.
                            let spec_param_syms = [short_qn_sym];
                            let spec_param_vars = [vid];
                            let signature_mentions = op.params.iter().any(|(_, t)| {
                                type_mentions_spec_param(kb, t, &spec_param_syms, &spec_param_vars)
                            }) || type_mentions_spec_param(
                                kb,
                                &op.return_type,
                                &spec_param_syms,
                                &spec_param_vars,
                            ) || op.effects.iter().any(|e| {
                                type_mentions_spec_param(kb, e, &spec_param_syms, &spec_param_vars)
                            });
                            // ...AND ONLY WHEN THE CALL HAS NO RECEIVER. A RECEIVER carries
                            // the spec's parameters even when the signature never writes
                            // them: `render(w: Widget)` on `sort Widget { sort T = ? }`
                            // names `Widget.T` nowhere, yet the witness that supplies
                            // `render` is selected per carrier, so `T` IS part of the
                            // instantiation being sought. MEASURED — without this
                            // conjunct, `wi325_missing_requires_test::
                            // user_defined_self_receiver_spec_without_providers_errors_on_abstract_call`
                            // goes green-to-red: a wholly-unimplemented self-receiver spec
                            // loaded clean instead of being caught at type-check.
                            //
                            // The same pair `self_recv_spec.is_none() && carrier_param_
                            // info.is_none()` is what `enclosing_requires_clause` tests
                            // above, for the same reason: it is the typer's spelling of
                            // "this call dispatches on nothing".
                            let has_receiver =
                                self_recv_spec.is_some() || carrier_param_info.is_some();
                            if !signature_mentions && !has_receiver {
                                continue;
                            }
                            let is_abstract = match subst.resolve_as_value(vid) {
                                None => true,
                                // WI-1059: a NEUTRAL is abstract too, and it is the form a
                                // materialized unwritten slot takes. `drive(w: Widget) =
                                // render(w)` used to bind nothing for `Widget.T` (the bare
                                // receiver carried no slot), so `None` above reported it;
                                // now the slot is there and holds `w.T`, which
                                // `is_type_param_value` — a test for a BARE param `Ref` —
                                // answers `false` for. Reading that as concrete silently
                                // dropped the WI-325 diagnostic on a wholly-unimplemented
                                // spec (measured). A projection is not concrete: it is the
                                // OTHER spelling of "still abstract", so it demands a
                                // `requires` exactly as the bare param does.
                                Some(Value::Term { id: bound, .. }) => {
                                    is_type_param_value(kb, *bound)
                                        || matches!(
                                            type_head(kb, &TermIdView(*bound)),
                                            TypeHead::ExprCarried | TypeHead::RigidProjection
                                        )
                                }
                                // A non-`Term` carrier (a denoted `Value::Node`
                                // / value-in-type param, WI-302) can't be
                                // introspected for type-param-ness here, so —
                                // like the loader-inconsistency arms above and
                                // per this loop's documented stance — assume
                                // abstract rather than silently disable the
                                // WI-325 protection. Carrier-agnostic
                                // introspection is WI-348 Phase C.
                                Some(_) => true,
                            };
                            if is_abstract {
                                abstract_params.push(short_qn_sym);
                            }
                        }
                        if !abstract_params.is_empty() {
                            let class = CallClass::UnresolvedSpecOp {
                                spec_op_sym: fn_sym,
                                spec_sort_sym: spec_sort,
                                abstract_params,
                                span,
                                enclosing_sort,
                            };
                            // WI-20260904-50B2K part (c) — THE FOURTH LICENCE, and the
                            // one whose carrier has no declaration site.
                            //
                            // The three above (WI-562's op-scoped `requires`, WI-590's
                            // sort-level one, and the `declared` set) all answer "the
                            // author DID write the clause". This one answers a different
                            // question: the carrier is a LAMBDA BINDER — a variable this
                            // walk minted, not a type parameter of any sort or operation
                            // — so `requires Additive[T = …]` has NOWHERE TO GO, and the
                            // refusal names a repair the author cannot perform. The
                            // evidence that decides it is not a declaration at all; it is
                            // what the binder's own USES solve, and those come later in
                            // the walk. So the classification is HELD, not dropped, and
                            // [`WalkSolutions::discharge`] raises it at the walk's end
                            // for every binder the uses failed to answer.
                            //
                            // MEASURED: 3 of `wi_tests`' 79,414 abstract-dispatch
                            // classifications have a walk-minted carrier — see
                            // [`walk_minted_carriers`].
                            let minted = solving
                                .as_deref()
                                .map(|w| {
                                    walk_minted_carriers(
                                        kb,
                                        pos_results,
                                        named_results,
                                        w.watermark,
                                    )
                                })
                                .unwrap_or_default();
                            match (minted.is_empty(), solving.as_deref_mut()) {
                                (false, Some(w)) => {
                                    w.defer_abstract_dispatch(occ, minted, spec_sort, class)
                                }
                                _ => classify(kb, occ, class),
                            }
                        }
                    }
                }
                DispatchOutcome::Unique(impl_op_sym) => {
                    // WI-365: ground the spec op's polymorphic effect ROW to the
                    // dispatched impl's real effects (the effect dual of WI-357's
                    // element threading). The pre-dispatch effect-close dropped
                    // the unresolved row as if the carrier were pure; a concrete
                    // impl that overrides the op with a genuine effect
                    // (`MutBox.peek effects Modify[b]`) must surface it at the
                    // consumption site so a pure consumer is rejected, exactly as
                    // a DIRECT call to the impl op is. A pure override (empty or
                    // wholly-unresolved effects) contributes nothing, so the
                    // `List`-as-`Stream` pure path is unchanged. Only a real
                    // override (`impl_op_sym != fn_sym`) can carry an effect the
                    // spec signature didn't.
                    if impl_op_sym != fn_sym {
                        let derived = dispatched_impl_effects(
                            kb,
                            flow,
                            impl_op_sym,
                            &op.params,
                            &subst,
                            pos_args,
                            named_args,
                            pos_results,
                            named_results,
                        );
                        // The spec op's polymorphic effect row is GROUNDED by
                        // this concrete dispatch. Drop the still-unresolved row
                        // var from the SPEC OP's OWN effects only — the
                        // pre-dispatch effect-close fires only for a type-param
                        // carrier binding, so an effect-only spec (`Box`:
                        // `effects Effect = ?`, no type-arg binding) still carries
                        // its `?_` here — substitute the impl's real effects in
                        // its place, then re-merge the UNTOUCHED `arg_effects`. We
                        // filter `substituted_op_effects`, not the merged
                        // `effects`, for the same reason the pre-dispatch close
                        // does (line above): a genuinely-polymorphic effect a
                        // receiver argument contributes must never be erased. A
                        // pure impl grounds the row to {} (`derived` empty); a
                        // non-pure one contributes its `Modify[b]`, so a pure
                        // consumer is rejected.
                        let mut closed_op_effects: Vec<Value> = substituted_op_effects
                            .iter()
                            .filter(|e| !effect_is_unresolved_var(kb, e))
                            .cloned()
                            .collect();
                        // WI-657(8): fold the impl's `derived` effects then the untouched
                        // `arg_effects` into the owned filtered row in place — one alloc,
                        // not the two throwaway merge results (`op_and_impl`, then `effects`).
                        merge_effects_into(kb, &mut closed_op_effects, &derived);
                        merge_effects_into(kb, &mut closed_op_effects, &arg_effects);
                        effects = closed_op_effects;
                    }
                    // WI-231: tag the call site. The requirement-
                    // insertion pass (`req_insertion::run`) reads the
                    // side-table and emits the actual IR rewrite — no
                    // inline emission here. WI-218 / WI-222 Phase E (i) /
                    // WI-228 semantics encoded by which CallClass
                    // variant we tag.
                    //
                    // WI-237: only rewrite to a *concrete* impl op — one
                    // that has a runnable body. A body-less `impl_op_sym`
                    // is a spec-level declaration (e.g. the auto-bound
                    // `anthill.prelude.String.eq` a `provides` block
                    // registers, or a derived `Ord.lt` whose body
                    // lives in a separate `rule {}`). Rewriting the call
                    // to it produces a runtime `unknown operation`
                    // (no body, no builtin) or — worse — mis-resolves to
                    // the wrong sibling op. Leaving the call as the spec
                    // op lets the runtime resolve it via its registered
                    // builtin or the spec's own derived rule.
                    if impl_op_sym != fn_sym && op_has_runnable_body(kb, impl_op_sym) {
                        // Pass the `resolved_tree` to the shared tail: a same-sort
                        // callee inherits the frame at eval; a CROSS-SORT one that
                        // constructs a dictionary has it emitted AS `dispatch_dict`
                        // there (WI-829), since eval threads the dict, not the tree.
                        classify_pin_or_apply_within(
                            kb,
                            occ,
                            fn_sym,
                            impl_op_sym,
                            enclosing_sort,
                            resolved_tree.clone(),
                            Some(&OpSupplyCtx {
                                subst: &subst,
                                caller_requires: env.enclosing_frame_chain(),
                                param_rigids: env.param_rigids(),
                                selected: &selections,
                                enclosing_op: env.enclosing_op(),
                                param_arg_types: &param_to_arg_type,
                                held: &held_views,
                            }),
                        )?;
                    }
                }
                DispatchOutcome::NoMatch { unmet } => {
                    // WI-562: op-scoped `requires` coverage (WI-448). An ABSTRACT
                    // spec-op call in an operation body — `List.member`'s
                    // `eq(head, x)` on the abstract element `T` — does not pin a
                    // concrete impl, and a loosely-matching parameterized provider
                    // in scope (e.g. a `fact Eq[List[A]]`) drives it to `NoMatch`
                    // rather than `NoCandidates`. If the enclosing OPERATION's OWN
                    // `requires` covers this spec, the call is LICENSED (the
                    // op-scoped dual of the sort-level defer-to-requirement): leave
                    // it as the spec op for value-directed eval, so `member`'s
                    // `Eq[T]` need lives on `member` instead of the whole `List`
                    // sort (a sort-level `requires Eq[T]` wrongly blocked
                    // `IndexedSeq.nth` on a `List[NonEq]`). Only failed
                    // (abstract) dispatch reaches here — a concrete call resolves
                    // `Unique` and keeps its impl effect-grounding (WI-365).
                    // WI-653: carrier-aware coverage (see the NoCandidates arm above).
                    // WI-590: as in the `NoCandidates` arm above — the enclosing SORT's
                    // `requires` covers this receiver, with the op-scoped licence tried
                    // FIRST for the same reason. UNLIKE that arm this one does not fall
                    // through to a pass-through: reaching its end is `DispatchNoMatch`, so a
                    // licence here must RETURN the spec-op result, exactly as the op-scoped
                    // branch does.
                    if op_requires_covers_call(kb, env, &subst, spec_sort)
                        || enclosing_requires_clause.is_some()
                    {
                        // WI-1091: as in the `NoCandidates` arm above. Only the op-scoped
                        // licence names a slot to defer to; the sort-level one does not.
                        if op_requires_covers_call(kb, env, &subst, spec_sort) {
                            defer_to_op_scoped_slot(
                                kb,
                                env,
                                occ,
                                &subst,
                                spec_sort,
                                fn_sym,
                                op_short_sym,
                                enclosing_sort,
                                pinned_spec,
                            );
                        }
                        return Ok(TypeResult {
                            ty: resolved_ret.clone(),
                            env: env.clone(),
                            effects,
                            node: Rc::clone(occ),
                        });
                    }
                    // WI-20260918-CKD4J — A RULE-BODY GOAL WHOSE TYPE IS STILL OPEN IS
                    // NOT REFUSED HERE. A rule body reaches eval through the SLD bridge,
                    // which resolves the provider from the CONCRETE argument values
                    // (`call_op_bridged`) and suspends when it cannot — WI-945 states the
                    // same for an element unpinned at load: it is "the ORDINARY case
                    // there, every goal argument being a variable". MEASURED: with
                    // `Option` providing `PartialEq[Option] :- PartialEq[T]`,
                    // `eq(some(?x), some(?x))` typed its goal as
                    // `PartialEq[Option[T = TypeVar[?_]]]`, the condition over the open
                    // element failed, and the rule was refused at load — where before the
                    // row existed the same call had no candidate and passed. A GROUND goal
                    // is still refused: nothing later can change its answer.
                    if env.in_rule_body() {
                        let goal = sort_goal_from_subst(kb, &subst, spec_sort, None);
                        // OPEN = a logic var or a sort parameter (`type_value_is_ground`),
                        // OR a `TypeExtractor.TypeVar` — the typer's marker for a type it
                        // could not infer, which that predicate reads as ground because
                        // its `name` field is a name and not a var.
                        let open = goal.bindings.iter().any(|(_, v)| {
                            !type_value_is_ground(kb, *v) || type_term_mentions_type_var(kb, *v)
                        });
                        if open {
                            return Ok(TypeResult {
                                ty: resolved_ret.clone(),
                                env: env.clone(),
                                effects,
                                node: Rc::clone(occ),
                            });
                        }
                    }
                    return Err(TypeError::DispatchNoMatch {
                        span,
                        op: fn_sym,
                        unmet,
                    });
                }
                DispatchOutcome::Ambiguous(tie) => {
                    // WI-822 LEG 1 — THE ONE ROUTE VALUE-DIRECTION CANNOT SERVE. Two
                    // or more providers answer and nothing here picks one: no runtime
                    // value can, because a spec op with NO receiver argument
                    // (`zero() -> T`) has none to direct it, and no bracket can
                    // either, because 058 §4.4 check 3 refuses an explicit witness
                    // over CONCRETE providers precisely on the grounds that the value
                    // decides. So the only channel left is a dictionary — and if the
                    // enclosing OPERATION declared `requires Zeroable[HT]`, it said it
                    // would be given one. Defer to that slot.
                    //
                    // MEASURED as the residue this ticket exists for: the op-scoped
                    // spelling of this program was REFUSED AT LOAD (`ambiguous
                    // dispatch of `Zeroable.zero``) while its sort-level twin — the
                    // same requirement written on the sort, one line up — loaded and
                    // computed the right answer. Two spellings of one program, one of
                    // which did not load.
                    //
                    // Gated on the tie, not applied to every op-scoped call, and the
                    // gate IS the design (see [`op_scoped_defer_location`]): an
                    // op-scoped requirement stays served by value-direction wherever
                    // value-direction can serve it, which is everywhere else.
                    if defer_to_op_scoped_slot(
                        kb,
                        env,
                        occ,
                        &subst,
                        spec_sort,
                        fn_sym,
                        op_short_sym,
                        enclosing_sort,
                        pinned_spec,
                    ) {
                        return Ok(TypeResult {
                            ty: resolved_ret.clone(),
                            env: env.clone(),
                            effects,
                            node: Rc::clone(occ),
                        });
                    }
                    return Err(TypeError::DispatchAmbiguous {
                        span,
                        op: fn_sym,
                        tie,
                    });
                }
                DispatchOutcome::Deferred => {
                    // Fallback: the WI-239 pre-check above already caught
                    // every spec reachable via `find_requires_location`
                    // (a superset of `find_requires_slot`), so this fires
                    // only when `resolve_at_goal` deferred via a path the
                    // tree walk's matcher missed. It can only resolve a
                    // DIRECT slot, hence an empty `proj_path`.
                    let sigma_ctx = SigmaCtx {
                        subst: &subst,
                        param_rigids: env.param_rigids(),
                    };
                    if let Some(slot) = find_requires_slot(
                        kb,
                        &subst,
                        spec_sort,
                        enclosing_requires,
                        Some(&sigma_ctx),
                    ) {
                        // WI-232: capture the matched entry so
                        // req_insertion::run can read it directly,
                        // without re-indexing the chain at emit time.
                        let resolved_spec = enclosing_requires[slot].clone();
                        classify(
                            kb,
                            occ,
                            CallClass::DeferToRequirement {
                                spec_op_sym: fn_sym,
                                op_short_sym,
                                resolved_spec,
                                slot,
                                proj_path: SmallVec::new(),
                                enclosing_sort,
                                enclosing_op: env.enclosing_op(),
                            },
                        );
                    }
                }
            }
            // WI-20260921-28TAT — A SPEC-OP CALL THAT NO ARM ABOVE CLASSIFIED still
            // owes its callee any op-scoped `requires`. Every classification above is a
            // DISPATCH REWRITE, and some spec-op calls rightly need none: `Error.reify`
            // is declared inside `sort Error { sort T = ? }` and names that `T`
            // NOWHERE, so no carrier dispatches on it, the spec-op machinery
            // deliberately excludes it (see the `signature_mentions` filter below), and
            // the prelude declares it body-less because the boundary is a FRAME the
            // interpreter installs by symbol. There is nothing to redirect — and until
            // this site existed, nothing to supply either: its `requires
            // TypeValue[T = T1]` loaded clean and measured `reqs=[]` at dispatch.
            //
            // GATED ON "nothing classified", not run unconditionally, because the
            // concrete-dispatch arms above reach `classify_pin_or_apply_within`, which
            // already stamped; running here too would build the same dictionaries a
            // second time.
            //
            // AND THE TWO `DeferToRequirement` ARMS STAMP TOO, as of this ticket: they
            // call `classify()` directly rather than through
            // `classify_pin_or_apply_within`, so a deferred call whose callee declares an
            // op-level `requires` used to get no dictionary at all — the same
            // silent-absence class this site fixes for the unclassified arm, one dispatch
            // route over. They key the stamp on the SPEC op, which is what the typer has:
            // the impl is chosen at run time from the dictionary, and §8.7 forbids an
            // override from strengthening the clause, so the spec's chain is the one both
            // ends agree on. So the gate below is exact — every classifying arm stamps.
            if occ.classification_is_none() && !op_dict_entries(kb, fn_sym).op_entries().is_empty()
            {
                stamp_op_scoped_dicts(
                    kb,
                    occ,
                    &subst,
                    fn_sym,
                    env.enclosing_frame_chain(),
                    env.param_rigids(),
                    &selections,
                    OpSlotParkSite::for_call(kb, fn_sym, env.enclosing_op(), span, occ.span.source),
                    &param_to_arg_type,
                    &held_views,
                    span,
                    false,
                )?;
            }
        } else {
            // WI-222 Phase E (i) Direct case: fn_sym is not a spec op.
            // If its parent sort declares any `requires`, tag for an
            // `apply_within(fn = Ref(fn_sym), …)` rewrite. Otherwise no
            // tag and the call stays as plain apply.
            // WI-822 LEG 1: OR the operation itself declares one. An op-scoped
            // `requires` names frame slots of its own now, so a direct call to
            // `Holder.probe(x) requires Zeroable[HT]` needs the channel even though
            // `Holder` declares nothing — that call used to be a plain apply with no
            // channel at all, which is exactly why the receiver-less `Zeroable.zero()`
            // in its body had nothing to defer to.
            if let Some(parent_sym) = impl_parent_of_op(kb, fn_sym) {
                let callee_has_op_slots = !op_requires_chain_rc(kb, fn_sym).is_empty();
                if op_reads_requirement_slots(kb, fn_sym) || callee_has_op_slots {
                    // WI-415: build the parent-bundle dispatching dict NOW,
                    // while the per-call subst still pins `parent_sym`'s type
                    // params (`member(2, …)` ⇒ `List.T := Int`). A cross-sort /
                    // no-enclosing-sort call then threads the CONCRETE
                    // requirement (`Eq[Int]`) into the callee's frame; eval
                    // installs the pre-built dict without re-resolving. `None`
                    // when no param binds concretely: an in-sort call inherits
                    // the enclosing frame's requirement at eval, while a
                    // cross-sort abstract call has no covering requirement at
                    // all (a pre-existing gap WI-415 does not address).
                    let enclosing_sort = env.enclosing_sort();
                    let callee_provision = op_owner_provision(kb, fn_sym);
                    // Proposal 066 §7.4 — A MEMBER OF A PROVISION THE CALLER IS NOT IN.
                    // The same-sort inherit cannot serve it (the caller's frame holds
                    // none of that provision's conditions), so its dictionary is built
                    // here — and from the caller's WHOLE frame, its own `requires`
                    // included: this dictionary is this call's alone and is installed
                    // at this call, so the reason the instance dictionaries do not
                    // forward an op slot (see `TypingEnv::enclosing_chain`) — an
                    // op-scoped slot is evidence about ONE call and an instance
                    // dictionary outlives it — does not arise. A helper's
                    // `requires PartialEq[T]` is exactly what answers the member's
                    // `PartialEq[T]` condition.
                    let serves = enclosing_sort != Some(parent_sym)
                        || frame_serves_callee(
                            env.enclosing_dict_chain(),
                            callee_frame_key(kb, fn_sym),
                        );
                    // WI-20260921-159S9 — **THE WHOLE FRAME, UNCONDITIONALLY: a slot
                    // declared on the OPERATION is as good as one declared on its SORT.**
                    //
                    // This read used to be the SORT half, widened for two special cases
                    // (`!serves`, and WI-20260919-N31XX's `TypeValue` dep out of a free
                    // operation). The narrowing was WI-822 LEG 1's central decision and
                    // it had a real reason: this channel is read STRICTLY at eval, so
                    // projecting from a slot no route fills turns WI-828's load-time
                    // refusal into an eval-time unbound `var_ref`. Four routes into an
                    // operation filled none.
                    //
                    // THREE OF THE FOUR HAVE SINCE CLOSED, and the fourth closes with
                    // this change: a HOST entry seeds the op half from the argument
                    // values (WI-1091 `seed_entry_op_requirements`), an eta'd `OpRef`
                    // carries its slots captured (`push_captured_op_scoped_slots`),
                    // value-directed dispatch already resolves the COMPOSED chain, and
                    // `Interpreter::fill_missing_op_scoped_slots` now fills whatever the
                    // entering route left unbound — which is what the DEFERRED route
                    // left. So the premise the narrowing rested on no longer holds.
                    //
                    // MEASURED, both halves, on this tree:
                    //  * the widening ALONE — 4841 passed, 2 failed, and both failures
                    //    are the two rows that pin the old decision
                    //    (`wi456 an_op_scoped_slot_is_refused_for_now`, `wi822
                    //    the_instance_dictionary_channel_never_forwards_an_op_slot`).
                    //    The 30-test breakage WI-822 recorded is NOT this read: it
                    //    belongs to `enclosing_requires()`, which decides whether a call
                    //    DEFERS instead of being value-directed, and is untouched here.
                    //  * `wi822`'s own fixture, which that row asserts is refused, now
                    //    LOADS AND RUNS and computes 1 and 12 — so the "composing only
                    //    mis-attributes the failure" measurement is superseded rather
                    //    than contradicted: there is no longer a failure to attribute.
                    //  * the widening WITHOUT the eval gate is a genuine regression, and
                    //    that is why the two land together: a deferred call to an
                    //    override repeating its spec's op-scoped clause loaded clean and
                    //    died `var_ref(__req_desc) unbound`. Backing the gate out fails
                    //    `wi_159s9_op_scoped_entry_test::a_deferred_dispatch_fills_the_
                    //    targets_op_scoped_slot`, and exactly that row.
                    //  * backing THIS line out fails 20 rows, five of them this ticket's
                    //    and FIFTEEN belonging to the two special cases the unconditional
                    //    form subsumed — `wi_1z3e7`'s helper row (the old `!serves` arm)
                    //    and all fourteen `wi_r541x_body_read_of_type_param_test` rows
                    //    (N31XX's `TypeValue` arm, whose gate `callee_chain_reads_type_-
                    //    value` this ticket deleted as unread). They pass on the general
                    //    rule, which is what says it is general.
                    //
                    // `serves` STAYS, because it also gates the proposal 066 §7.4 refusal
                    // below — flipping that turned 59 unit tests red with `PartialOrd.lt`
                    // refused by a diagnostic aimed at calls it was never about. Only the
                    // CHAIN moved.
                    //
                    // MERGE NOTE (2026-09-22) — WI-20260921-EE0EP arrived on the same
                    // line from the other direction, ADDING a disjunct to a conditional
                    // `whole_frame` (`op_chain_is_only_param_derived`, for a caller
                    // holding a param-derived slot) while this side DELETED the
                    // conditional outright: WI-20260921-3G1YT found its `TypeValue` gate
                    // `callee_chain_reads_type_value` unread and generalized the rule to
                    // "always the whole frame chain".
                    //
                    // THE UNCONDITIONAL FORM SUBSUMES THE DISJUNCT — `whole_frame` is
                    // now always true, so a param-derived slot takes the whole chain by
                    // the general rule rather than by a case written for it. Taken this
                    // way and not the other because EE0EP's branch calls a function this
                    // side deleted, so it could not compile; and because a special case
                    // subsumed by a general rule is the shape 3G1YT was closing. EE0EP's
                    // own rows are what say the subsumption holds, and they are run.
                    let caller_requires = env.enclosing_frame_chain().clone();
                    // WI-828: a σ-refused requirement is a LOAD diagnostic —
                    // classifying `dispatch_dict: None` here loaded clean and
                    // died at eval reading the unbound `__req_*`.
                    let mut unsuppliable: Option<Box<RequirementRefusal>> = None;
                    let dispatch_dict = build_concrete_dispatch_dict(
                        kb,
                        // WI-20260921-3G1YT — a RULE-body site, and only then: an
                        // operation-body site's unsuppliable deps are PARKED just below
                        // and decided against the callee's body, which is the right
                        // machinery; a rule body can neither park (the queue is drained
                        // before rule bodies are typed) nor be value-rescued.
                        env.enclosing_op().is_none().then_some(fn_sym),
                        &held_views,
                        &subst,
                        parent_sym,
                        callee_provision,
                        enclosing_sort,
                        &caller_requires,
                        env.param_rigids(),
                        &selections,
                        // WI-945: asked for ONLY inside an operation body — see the park
                        // below for why a rule-body goal is a different question.
                        env.enclosing_op().is_some().then_some(&mut unsuppliable),
                    )
                    .map_err(|refusal| {
                        TypeError::UnsatisfiableRequirement {
                            span,
                            op: fn_sym,
                            callee_sort: parent_sym,
                            eta: false,
                            refusal,
                        }
                    })?;
                    // WI-945 — §5.2's unconstrained-element refusal, PARKED for the
                    // pass that runs once every body is typed. Two gates, each with a
                    // mechanism behind it rather than a corpus behind it:
                    //
                    //  * `enclosing_op` (asked for above): this dictionary is the
                    //    call's only supply only in an OPERATION body, where eval
                    //    installs it or plain-applies. A RULE-body goal reaches eval
                    //    through the SLD bridge, which resolves real provider
                    //    dictionaries from the CONCRETE argument values
                    //    (`call_op_bridged` → `resolve_bridge_requirements`) and
                    //    SUSPENDS when it cannot — so an element unpinned at load is
                    //    the ORDINARY case there, every goal argument being a
                    //    variable. MEASURED: `gap3b.combiner`'s `combines_to(?b, ?r)`
                    //    (wi625 Layer B) and `PartialEq[T = PartialOrd.T]` at
                    //    `anthill.prelude.PartialOrd` are exactly this — 93 of the 97
                    //    instrumented hits across the workspace — and they all work.
                    //  * whether the callee's body reads the slot — deferred to
                    //    [`report_unsuppliable_requirements`]; see
                    //    [`UnsuppliableRequirement`].
                    //
                    // No `dispatch_dict.is_none()` guard beside this: the builder fills
                    // the slot on the one path that then returns `Ok(None)`, so a
                    // refusal here and a dictionary are already mutually exclusive.
                    // Proposal 066 §7.4: with no dictionary a same-sort member call would
                    // fall back to the inherit, handing the member a frame without its
                    // provision's conditions — unbound at eval. So it is a load error
                    // here, unless a refusal is already parked for it just below.
                    //
                    // WI-456 — "already parked" means a refusal that says MORE than this
                    // one does, and [`RequirementRefusal::no_scope_route`] says less: it is
                    // the signature for "no route, and none of the four reasons applies",
                    // whose tail can only advise declaring a slot. THIS error names both
                    // operations and the provision, and its repair ("or give it its own
                    // `requires …`") is the one an author can act on. So the least-specific
                    // signature YIELDS here rather than displacing it.
                    //
                    // MEASURED as the one regression the no-route arm caused across the
                    // workspace (7226 tests, this alone):
                    // `wi_1z3e7 a_helper_calling_a_member_directly_builds_its_dictionary`,
                    // where parking turned §7.4's message into the generic tail.
                    let parked_says_more =
                        unsuppliable.as_deref().is_some_and(|r| !r.no_scope_route);
                    if !serves && dispatch_dict.is_none() && !parked_says_more {
                        let provision = callee_provision.unwrap_or(parent_sym);
                        return Err(TypeError::ProvisionConditionOutOfScope {
                            span,
                            op: env.enclosing_op().unwrap_or(fn_sym),
                            spec_op_sym: fn_sym,
                            spec_sort_sym: provision,
                            provisions: SmallVec::from_elem(provision, 1),
                        });
                    }
                    if let Some(refusal) = unsuppliable {
                        // THE BUILTIN GATE, and since WI-20260921-3G1YT it is the WHOLE
                        // gate rather than the carrier signature's half of one. A spec op
                        // registered as a RESOLVER BUILTIN resolves STRUCTURALLY: the
                        // default body carrying the `requires` is never entered, so the
                        // dictionary is never consulted and no supply — a `provides` line,
                        // a pinned element, anything — would change its outcome. That is a
                        // property of the callee's SIGNATURE (a registry lookup), not of
                        // its body, which is what makes it a legitimate exemption under
                        // this ticket's rule while a body walk is not.
                        //
                        // IT WAS `refusal.unprovided.is_none() || !kb.is_builtin(…)`, so
                        // WI-945's unconstrained-element signature parked even at a
                        // builtin. That reading survived only because the body walk then
                        // dropped the entry anyway — a builtin's default body reads no
                        // slot — so the carve-out never had to be right. With the walk
                        // gone it is loud, and it is wrong: MEASURED, `Holder requires
                        // Ord[T]` whose `atLeast(a: T, b: T) = gte(a, b)` reaches
                        // `PartialOrd`'s own `requires PartialEq[T]` at a rigid, and
                        // `wi1110 …a_converted_spec_lends_its_names` is refused although
                        // `gte` never consults the slot. The harm the WI-945 signature
                        // exists to prevent is an eval-time `__req_* not bound`, and a
                        // structural resolution cannot produce one.
                        if !kb.is_builtin(fn_sym) {
                            kb.unsuppliable_requirements.push(UnsuppliableRequirement {
                                span,
                                source: occ.span.source,
                                callee_op: fn_sym,
                                callee_sort: parent_sym,
                                refusal,
                            });
                        }
                    }
                    // WI-822 LEG 1: and the callee's OWN op-scoped slots, from the same
                    // substitution. Its caller chain is the COMPOSED one — a callee op
                    // slot may forward from the caller's own op slots, which is how an
                    // op-scoped requirement relays hop to hop — whereas the instance
                    // dict above must not (see `TypingEnv::enclosing_chain`).
                    stamp_op_scoped_dicts(
                        kb,
                        occ,
                        &subst,
                        fn_sym,
                        env.enclosing_frame_chain(),
                        env.param_rigids(),
                        &selections,
                        OpSlotParkSite::for_call(
                            kb,
                            fn_sym,
                            env.enclosing_op(),
                            span,
                            occ.span.source,
                        ),
                        &param_to_arg_type,
                        &held_views,
                        span,
                        false,
                    )?;
                    classify(
                        kb,
                        occ,
                        CallClass::ConcreteApplyWithin {
                            fn_target_sym: fn_sym,
                            callee_spec_sort: parent_sym,
                            spec_op_sym: fn_sym,
                            enclosing_sort,
                            resolved_tree: None,
                            dispatch_dict,
                            enclosing_op: env.enclosing_op(),
                        },
                    );
                }
            }
        }

        return Ok(TypeResult {
            ty: resolved_ret,
            env: env.clone(),
            effects,
            node: Rc::clone(occ),
        });
    }

    // Path 2: variable with arrow type. WI-341 Stage A: the env carries `Value`.
    // WI-361/WI-342: one carrier-agnostic read — a ground (`Value::Term`) and a
    // `Value::Node` callback arrow (denoted-bearing effect, e.g. `Modify[a]`)
    // both flow through `extract_function_type_parts`, the occurrence never
    // re-grounded.
    if let Some(fn_type) = env.lookup_var(fn_sym) {
        // WI-20260904-50B2K part (c), step 2 — ∀-ELIMINATION HERE, WHERE THE COMMENT THIS
        // REPLACES SAID NONE COULD ARRIVE. That reading was correct and is now out of date,
        // and the sentence it turned on is the one worth keeping: "what would make it
        // reachable is let-polymorphism … that is the capability the PolyType makes
        // expressible and this ticket does not deliver." It delivers it now, from the other
        // end — not by eta-lifting an operation into a `let`, but by GENERALIZING A LAMBDA
        // whose binder the walk could not pin, so `let g = lambda x -> x + x` binds a ∀ and
        // `g(2)` is this path.
        //
        // The instantiation is per REFERENCE, exactly as `check_bare_ref`'s is, so two uses
        // of one `g` share no variable and each is checked at its own carrier. Its
        // obligations are handed to the walk ([`WalkSolutions::note_instantiation`]) rather
        // than tested here: the arguments have not been unified yet, so the fresh carrier
        // is not pinned until the loop below runs — and the machinery that answers "was
        // this variable seen at a providing carrier" already exists, with one owner.
        let fn_type = match instantiate_poly_type(kb, &fn_type) {
            Some(inst) => {
                // THE SAME LOUD READING AS `check_bare_ref`'s: a context nothing claims is
                // a constraint dropped. With no `solving` there is no walk to claim it at
                // all, which is the same absence and is reported the same way.
                let claimed = solving
                    .as_deref_mut()
                    .map(|w| w.note_instantiation(&inst.binder_map))
                    .unwrap_or(0);
                if !inst.obligations.is_empty() && claimed == 0 {
                    return Err(TypeError::Other {
                        site: TypeError::here(),
                        span,
                        context: TypeErrorContext::OperationAsFunctionValue { op_name: fn_sym },
                        expected: "a quantified function value whose constraints this walk \
                                   can discharge"
                            .to_string(),
                        actual: format!(
                            "a `PolyType` carrying {} constraint(s) no deferred requirement \
                             claims (WI-20260904-50B2K part (c))",
                            inst.obligations.len()
                        ),
                    });
                }
                inst.ty
            }
            None => fn_type,
        };
        // WI-798: the callee is classified ONCE for the whole path — the
        // result/effects read here, the WI-792 positional argument check, and the
        // WI-783 named-label resolution below all read THIS extraction. They used
        // to derive it up to four times per application, each a head classify plus
        // a fresh binding vector with every bound type cloned in. Via
        // `extract_callable_type`, not `extract_type`: the child-key pre-intern it
        // performs is what lets a `Value::Node` callee's children be found at all,
        // and it used to happen inside `arrow_parts` on the line below.
        let callee_ty = extract_callable_type(kb, &fn_type);
        if let Some((ret_ty, call_effects)) = extract_function_type_parts(kb, &callee_ty) {
            // WI-798: and the DECLARED PARAMETER LIST likewise once — the
            // positional check reads it as its slot list (for every arity but
            // one), and the WI-783 named-label resolution below reads the SAME
            // list to bind labels to slots. Deriving it twice meant a second
            // `extract_type` of the arrow's `param` plus a second walk of the
            // parameter cons-list on every named-argument call.
            //
            // What must NOT be shared is the POSITIONAL slot list: it diverges
            // from this one at arity 1, where an arrow drops its lone binder's
            // name, so `arrow_positional_param_slots` mints a synthetic `_1` while
            // this stays `None` so a LABEL there is refused. That divergence lives
            // in the reader's match, not in whether the list is computed, so
            // hoisting the computation leaves it intact.
            let declared_params = arrow_declared_param_list(kb, &callee_ty);
            // WI-516: `f(arg…)` performs the arrow's OWN call effect UNIONED with
            // the effects of EVALUATING each argument — the same arg-effect
            // accumulation Path 1 (known op) and Path 3 (unknown functor) do.
            // Omitting it dropped an effectful nested argument: `f(delayForce(m))`
            // lost the inner `delayForce(m)`'s effect (only `let a = delayForce(m);
            // f(a)` accumulated it), under-reporting a call's effect row.
            let mut effects = call_effects;
            for r in pos_results.iter().chain(named_results.iter()).flatten() {
                merge_effects_into(kb, &mut effects, &r.effects);
            }
            // WI-792: CHECK THE ARGUMENTS against the arrow's parameter list.
            // Until this ran, the `param` slot was DISCARDED here — only `result`
            // and `effects` were read — so a function-VALUE application enforced
            // nothing about what it was handed. `f(true, 7)` against a declared
            // `(x: Int64, y: Bool) -> Int64` loaded clean and an operation
            // declared `-> Int64` returned `Bool(true)`. No permutation and no
            // subtyping were involved: the call put each value in the wrong slot
            // and nothing objected. It is also what made WI-782's premise — that a
            // mis-aligned parameter list would then fail on the TYPES — hold only
            // where conformance is checked, which this site was not.
            //
            // The relation is [`validate_arg_against_param`], CALLED rather than
            // restated. A bespoke comparison here would get the types right and
            // silently lose the three things that function already owns: the
            // WI-408 some-coercion, the `is_reflect_term_type` reflection bypass,
            // and the WI-385/WI-469 groundness discipline. A function-value
            // application is simply the THIRD argument position (after the
            // named-operation and entity-field ones that function's doc names),
            // not a new relation — so it also ACTS on `WrapSome` below rather than
            // treating it as Ok, which would leave a value bare in memory while
            // its type says `Option[T]` (the WI-385 interim WI-408 replaced).
            //
            // `subst` is fresh: unlike Path 1 there is no callee SIGNATURE to
            // instantiate here. WI-20260904-50B2K — but its bindings ARE read, at the
            // return below. The premise this comment used to state ("an arrow VALUE's
            // type is already whatever the environment resolved it to — so nothing
            // outside these loops reads a binding they make") held only while an
            // un-annotated lambda binder was minted as an inert `type_var`. Once rung 3
            // mints the engine's own variable, a let-bound `lambda q -> q` has type
            // `?v -> ?v`, checking the argument binds `?v`, and DISCARDING that binding
            // returned `?v` as the call's type: `let g = lambda q -> q  g(x)` in a
            // `-> String` operation reported "expected String, got ??param".
            let mut subst = Substitution::new();
            let mut arg_errors: Vec<TypeError> = Vec::new();
            // WI-408: `(child-index, declared Option type)`, materialized below.
            let mut some_wraps: Vec<(usize, Value)> = Vec::new();
            // WI-788: ONE reader, ONE loop, for BOTH callable spellings — an
            // `arrow` and a `Function[A, B, E]`. They used to be two inline
            // branches with a hand-rolled arity error and a per-argument loop
            // each, differing only in where the expectation came from, which is
            // precisely how the `Function` half came to check nothing at all.
            // WI-801: `A` when this call is `A`'s components spread and must be
            // handed to eval as ONE whole-`A` tuple; `None` otherwise.
            let mut gather_into: Option<(Value, Vec<Symbol>)> = None;
            match positional_arg_expectations(
                kb,
                &callee_ty,
                declared_params.as_deref(),
                pos_args.len(),
                pos_args.len() + named_args.len(),
            ) {
                ArgExpectations::CountMismatch { expected } => {
                    let arity_sym = kb.intern("arity");
                    let supplied = pos_args.len() + named_args.len();
                    return Err(TypeError::Other {
                        site: TypeError::here(),
                        span,
                        context: TypeErrorContext::OperationArgument {
                            op_name: fn_sym,
                            param: arity_sym,
                        },
                        expected,
                        actual: format!(
                            "{supplied} argument{}",
                            if supplied == 1 { "" } else { "s" },
                        ),
                    });
                }
                // The callee's argument type states nothing checkable. Named, so
                // that this is a decision rather than a fallthrough.
                ArgExpectations::NoVerdict => {}
                ArgExpectations::Slots { slots, gather } => {
                    gather_into = gather.map(|a| {
                        // WI-801: the component LABELS come from the slot list the
                        // check just used, not from a second `extract_type` of `A`
                        // — `slots` IS that extraction, and re-running it per
                        // gathered application is the cost the typer's WI-798 notes
                        // single out (a head classify plus a fresh binding vector
                        // with every bound type cloned in).
                        (a, slots.iter().map(|(l, _)| *l).collect::<Vec<_>>())
                    });
                    // WI-20260827-1F0QP: through the same owner as a NAMED operation's
                    // call. An arrow's `slots` are a parameter list like any other, so a
                    // mixed application of a function VALUE ranks its positional
                    // arguments the same way — and must be CHECKED against the slot it
                    // ranks to, or a mixed `f("hi", acc: 3)` is refused naming a
                    // parameter it never filled.
                    let slot_params: SmallVec<[(Symbol, Value); 4]> =
                        slots.iter().cloned().collect();
                    let pos_slots =
                        positional_param_indices(kb, &slot_params, pos_args.len(), named_args);
                    for (i, _) in pos_args.iter().enumerate() {
                        if let (Ok(arg_result), Some((param_sym, slot_type))) =
                            (&pos_results[i], pos_slots[i].and_then(|p| slots.get(p)))
                        {
                            match validate_arg_against_param(
                                kb,
                                &mut subst,
                                &arg_result.ty,
                                slot_type,
                                span,
                                TypeErrorContext::OperationArgument {
                                    op_name: fn_sym,
                                    param: *param_sym,
                                },
                                Some(&arg_result.node),
                            ) {
                                // WI-20260904-50B2K — BIND THE ARROW'S OWN HOLES from the
                                // argument, exactly as Path 1's argument loop does. The
                                // boolean is DISCARDED for the reason that site states:
                                // unify is EQUALITY while the check above is SUBTYPING plus
                                // three conversions, so a unify-false must not reject. What
                                // it is FOR is the slot's variables — an un-annotated
                                // `lambda q -> q` has type `?v -> ?v`, and with nothing
                                // binding `?v` the call `g(x)` returned `?v` and an
                                // operation declared `-> String` reported "expected String,
                                // got ??param".
                                //
                                // ONLY ON `Ok`. On the `WrapSome` arm the argument is the
                                // UN-COERCED value, so unifying it against an `Option[…]`
                                // slot can only fail — and failing there leaves the slot's
                                // `T` free exactly where the coercion has just determined
                                // it, so a `ret_ty` mentioning it would come back
                                // `??param` instead of `Int64`. Found by `/code-review`.
                                //
                                // WHAT A FAILED UNIFY LEAVES BEHIND IS SETTLED AT THE
                                // RELATION, not here — WI-20260904-60143, see
                                // [`unify_types`]' "what survives a `false`" note.
                                // `unify_types` still does not roll back (four refusals are
                                // reached BY the partial binding, measured), so a pair that
                                // conforms by SUBTYPING but not by EQUALITY keeps what it
                                // bound. What that ticket removed is the part of it that was
                                // ARBITRARY: an author-ordered slot list now contributes
                                // every slot that agreed rather than the prefix before the
                                // first that did not, so the `ret_ty` read below no longer
                                // depends on how the argument's type was spelled.
                                ArgValidation::Ok => {
                                    let before = subst.clone();
                                    let unified =
                                        unify_types(kb, &mut subst, &arg_result.ty, slot_type);
                                    // WI-20260904-50B2K part (c) — REPORT FROM PATH 2 TOO.
                                    // The first slice reported at Path 1's two argument
                                    // loops only, and MEASURED, that is exactly the half
                                    // that cannot see a binder's USE: `let g = lambda x ->
                                    // x  g(2)` calls an ENV-BOUND ARROW, which is this
                                    // path, and the walk learned nothing from it (probe:
                                    // zero solutions, against one for the same program
                                    // with the body doing the pinning). Part (c)'s
                                    // discharge is asked precisely about the use, so
                                    // without this the licence below could never fire.
                                    report_walk_solutions(
                                        kb,
                                        solving.as_deref_mut(),
                                        &before,
                                        &subst,
                                        unified,
                                    );
                                }
                                ArgValidation::WrapSome { declared } => {
                                    some_wraps.push((i, declared))
                                }
                                ArgValidation::Fail(err) => arg_errors.push(err),
                            }
                        }
                    }
                }
            }
            // WI-783: resolve NAMED arguments against the arrow's declared binder
            // names — the job Path 1 does for a named operation via its
            // `op.params` (coverage check + `reorder_named_args_in_apply`), and
            // which this path used to skip entirely. Skipping it was silently
            // WRONG, not merely unchecked: eval's `start_apply` DISCARDS the
            // labels and binds what is left positionally, so `f(x: 10, acc: 3)`
            // and `f(acc: 3, x: 10)` on `(acc: Int64, x: Int64) -> Int64` bound
            // opposite ways and a `sub`-like callee returned 7 and -7 — a
            // plausible wrong number, with the binder names inert and even an
            // unknown label accepted. Binding by the DECLARED names is sound
            // despite WI-775 letting the actual callee's own binder names differ
            // (`sub2(a, b)` may be passed for `(acc, x)`): an arrow's parameter
            // list is applied POSITIONALLY, so declared slot i is the callee's
            // slot i, and resolving label → slot against the static type before
            // handing eval a positional call composes exactly.
            //
            // WI-792 folded the per-argument TYPE check for these labels in below,
            // beside the positional loop above: resolving a label to a slot and
            // then not checking what lands in it is the same silence in the other
            // channel.
            let params = if named_args.is_empty() {
                Vec::new()
            } else {
                let params = declared_params.ok_or_else(|| {
                    // No declared names to bind to (a 1-param arrow, whose binder
                    // name the arrow type drops; a `Function[A, B]`, whose `A` is
                    // one tuple argument; an abstract param). The label can be
                    // neither ordered nor validated, so it must not be silently
                    // ignored — reject and point at the positional form.
                    aggregate_errors(
                        named_args
                            .iter()
                            .map(|(arg_name, _)| TypeError::Other {
                                site: TypeError::here(),
                                span,
                                context: TypeErrorContext::OperationArgument {
                                    op_name: fn_sym,
                                    param: *arg_name,
                                },
                                expected: "positional arguments — the type of this function \
                                           value records no parameter names to bind a label to"
                                    .to_string(),
                                actual: format!(
                                    "named argument '{}'",
                                    short_name_of(kb.local_name_of(*arg_name))
                                ),
                            })
                            .collect(),
                    )
                })?;
                // The same WI-426 coverage rule the named-operation path applies,
                // via the shared checker so the two cannot drift.
                //
                // WI-1100: the LABEL half only. This path's ARITY is already owned, one
                // block up, by `positional_arg_expectations` — which knows the two
                // readings a `Function[A, B, E]` slot admits (one whole-`A` argument, or
                // `A`'s components spread) and so states a count where the binder, which
                // reads a parameter LIST, cannot. A wrong total returned `CountMismatch`
                // there and never reached here.
                arg_errors.extend(
                    bind_call_arguments(
                        kb,
                        &params,
                        pos_args.len(),
                        named_args,
                        fn_sym,
                        "this function value's type",
                        span,
                    )
                    .label_errors,
                );
                // WI-792: and the same per-argument conformance the positional
                // loop applies, at the slot each label resolved to. An UNKNOWN
                // label matches no param and is skipped here, so it is reported
                // once, by the coverage check. A DUPLICATE label does match, so it
                // is type-checked too and can draw a second, different diagnostic
                // — measured, and the same thing Path 1 does with the same two
                // checks in the other order. Left alone deliberately: the two
                // errors say different true things about the argument, and
                // suppressing one here would make the two paths diverge.
                for (i, (arg_name, _)) in named_args.iter().enumerate() {
                    let Ok(arg_result) = &named_results[i] else {
                        continue;
                    };
                    let Some((param_sym, param_type)) =
                        match_named_arg_param(kb, &params, *arg_name)
                    else {
                        continue;
                    };
                    let (param_sym, param_type) = (*param_sym, param_type.clone());
                    match validate_arg_against_param(
                        kb,
                        &mut subst,
                        &arg_result.ty,
                        &param_type,
                        span,
                        TypeErrorContext::OperationArgument {
                            op_name: fn_sym,
                            param: param_sym,
                        },
                        Some(&arg_result.node),
                    ) {
                        // WI-20260904-50B2K — the named twin of the positional bind above;
                        // see its note, including why it is `Ok`-only. Written at BOTH
                        // loops rather than once, because a rule written twice at one site
                        // and not the other is the asymmetry the typer has been bitten by
                        // before.
                        ArgValidation::Ok => {
                            let before = subst.clone();
                            let unified = unify_types(kb, &mut subst, &arg_result.ty, &param_type);
                            // WI-20260904-50B2K part (c) — the named twin; see the
                            // positional loop's note.
                            report_walk_solutions(
                                kb,
                                solving.as_deref_mut(),
                                &before,
                                &subst,
                                unified,
                            );
                        }
                        ArgValidation::WrapSome { declared } => {
                            some_wraps.push((pos_args.len() + i, declared));
                        }
                        ArgValidation::Fail(err) => arg_errors.push(err),
                    }
                }
                params
            };
            if !arg_errors.is_empty() {
                return Err(aggregate_errors(arg_errors));
            }
            // Materialize the WI-408 some-coercions recorded above, and — when the
            // call has NAMED args, every label having resolved — hand eval a
            // positionally-correct call. `check_apply_iter` bailed on any ill-typed
            // child up front (`collect_arg_errors`), so the rebuilders' Ok-child
            // expectation holds. Mirrors Path 1's rebuild, minus its reorder
            // fallback: that fallback is for a callee with no parameter names,
            // which this path has already rejected above.
            let named_node;
            let occ = if !named_args.is_empty() {
                match reorder_named_args_in_apply(
                    kb,
                    occ,
                    &params,
                    pos_args.len(),
                    &some_wraps,
                    pos_results,
                    named_results,
                ) {
                    Some(r) => {
                        named_node = r;
                        &named_node
                    }
                    // Unreachable: the reorder declines only a non-`Apply`
                    // occurrence, and both `check_apply_iter` call sites pass an
                    // `Expr::Apply`. Kept LOUD rather than falling back to `occ`
                    // — that fallback would hand eval the labels in WRITTEN order
                    // and silently restore the very mis-binding this path exists
                    // to prevent, which is precisely the "reads as handled when
                    // it isn't" failure the repo's loud-error rule targets.
                    None => {
                        debug_assert!(false, "named-arg reorder declined a non-Apply occurrence");
                        return Err(TypeError::Other {
                            site: TypeError::here(),
                            span,
                            context: TypeErrorContext::OperationArgument {
                                op_name: fn_sym,
                                param: named_args[0].0,
                            },
                            expected: "an application occurrence whose named arguments can be \
                                       bound to the callee's declared parameters"
                                .to_string(),
                            actual: "an occurrence this typer cannot reorder; pass the arguments \
                                     positionally"
                                .to_string(),
                        });
                    }
                }
            } else if let Some((a_type, labels)) = gather_into {
                // WI-801: normalize the SPREAD form into the whole-`A` form. Both
                // admitted callee arities then take the identical one-argument
                // call — a 1-parameter callee receives `A` itself, and an
                // `|A|`-parameter one has eval's existing spread adapter applied
                // to it (`spread_eta_args` / `match_tuple_pattern`) — so the
                // callee's own arity, the quantity eval pivots on, can no longer
                // disagree with `A`'s component count, the quantity this site
                // pivots on. That disagreement is WI-801.
                //
                // AFTER the some-wraps, which index the ORIGINAL children: a
                // coerced argument must be wrapped before it becomes a component.
                named_node = gather_spread_args_into_tuple(
                    kb,
                    occ,
                    a_type,
                    &labels,
                    &some_wraps,
                    pos_results,
                )
                .ok_or_else(|| {
                    // TWO causes, both unreachable, both loud rather than falling
                    // back to `occ` — which would hand eval the un-normalized
                    // spread call and silently restore the trap this branch exists
                    // to remove. (1) A non-`Apply` occurrence, unreachable for the
                    // same reason the reorder's `None` is: both
                    // `check_apply_iter` call sites pass an `Expr::Apply`. (2) The
                    // labels and the arguments disagreeing in count, which cannot
                    // happen because both descend from the same `positional`.
                    debug_assert!(false, "spread gather declined a well-formed application");
                    TypeError::Other {
                        site: TypeError::here(),
                        span,
                        context: TypeErrorContext::OperationArgument {
                            op_name: fn_sym,
                            param: kb.intern("arity"),
                        },
                        expected: "an application occurrence whose spread arguments can be \
                                   gathered into the function's declared argument type"
                            .to_string(),
                        actual: "an application this typer cannot rebuild — its shape or its \
                                 argument count does not match the declared components; pass \
                                 the whole tuple"
                            .to_string(),
                    }
                })?;
                &named_node
            } else if some_wraps.is_empty() {
                occ
            } else {
                named_node = wrap_some_children(kb, occ, &some_wraps, pos_results, named_results);
                &named_node
            };
            // WI-20260904-50B2K — resolved through the argument check's own `subst`, the
            // same way Path 1 resolves its declared return. For a ground arrow this is an
            // identity. BOTH HALVES, and Path 1 is the precedent: resolving only the
            // return type would have one call reporting two states of one σ — a variable
            // the argument check pinned, solved in the type and unsolved in the effect
            // row. Found by `/code-review`.
            let ret_ty = resolve_type_deep_value(kb, &subst, &ret_ty);
            let effects: Vec<Value> = effects
                .into_iter()
                .map(|e| resolve_type_deep_value(kb, &subst, &e))
                .collect();
            return Ok(TypeResult {
                ty: ret_ty,
                env: env.clone(),
                effects,
                node: Rc::clone(occ),
            });
        }
    }

    // Path 3: unknown functor — collect arg effects (from pre-computed
    // results) and fall back to the declared return type if any.
    let mut effects: Vec<Value> = Vec::new();
    for r in pos_results.iter().chain(named_results.iter()) {
        if let Ok(r) = r {
            merge_effects_into(kb, &mut effects, &r.effects);
        }
    }
    let _ = pos_args;
    let _ = named_args;
    // WI-1063: the declared return becomes this call's result here too, outside the Path-1
    // block, so the opening runs here as well — a callee with a recorded return but no full
    // `OperationInfo` is still a callee, and a rule that holds only on the path the typer
    // usually takes is not a rule.
    //
    // WI-1078 REACHES THIS SITE AND CANNOT FIRE ON IT, which is stated rather than left to be
    // rediscovered. Path 1 is entered iff `lookup_operation_info_full` succeeded, so anything
    // arriving here has NO decodable signature — and that is the exact condition on which
    // `unbound_return_var_openings` returns an empty map, because "bound" is a question about a
    // signature it cannot read. So the anonymous/omitted spellings still open here and a NAMED
    // unbound one does not: this path keeps WI-1063's rule, deliberately, since the evidence
    // WI-1078 runs on is absent. `fn_sym` is passed anyway so the site cannot silently drift
    // out of the set if the Path-1 gate is ever widened.
    lookup_operation_return_type(kb, fn_sym)
        .map(|ty| {
            let ret = Value::term(ty);
            let ret = open_existential_return(
                kb,
                impl_parent_sort_of_op(kb, fn_sym),
                fn_sym,
                &ret,
                occ.span,
                occ.owner,
            )
            .unwrap_or(ret);
            TypeResult {
                ty: ret,
                env: env.clone(),
                effects,
                node: Rc::clone(occ),
            }
        })
        .ok_or_else(|| {
            // WI-565: refine the terse "unknown functor" when the bare name IS a
            // member operation of some sort — bare member names are in scope only
            // within their defining sort, so name the owning sort(s) and the
            // qualified/dot remedy. A genuinely-unknown name (no owning sort)
            // keeps the plain `UnknownApplyFunctor`.
            let candidates = member_owning_sorts_for_bare(kb, fn_sym);
            if candidates.sorts.is_empty() {
                TypeError::UnknownApplyFunctor { span, name: fn_sym }
            } else {
                TypeError::BareMemberCall {
                    span,
                    member: fn_sym,
                    owning_sorts: candidates.sorts,
                    dot_dispatchable: candidates.dot_dispatchable,
                }
            }
        })
}

/// WI-218: allocate a rewritten `apply` term with `fn = impl_op_sym`,
/// keeping the same args, and record it against `site` in `kb.dispatch_rewrites`.
///
/// THAT MAP IS DIAGNOSTIC-ONLY — reflection / proof tooling that wants to see the
/// elaborated Term shape, and nothing else. This doc used to say "the post-typing
/// rewrite pass uses these maps to substitute the rewritten term into operation
/// bodies bottom-up"; no such pass exists. Runtime reads `CallClass` off the
/// `NodeOccurrence` directly (post-WI-248), and after WI-873 the map is keyed by
/// [`crate::kb::CallSite`], so a term→term substitution could not read it even if one
/// wanted to. (Found in review of WI-873, which rewrote the words around that clause
/// and left it, contradicting the field's own doc one file over.)
///
/// `apply_functor` is the `anthill.reflect.Expr.apply` symbol the caller already
/// holds. Taking it rather than re-interning the short name "apply" keeps it the
/// same `Symbol` the loader registered, which the eval's reflect-symbol cache
/// compares against. (Before WI-873 it was read back off a synthesized "original
/// apply" term, which is where that same symbol came from.)
pub(crate) fn record_apply_rewrite(
    kb: &mut KnowledgeBase,
    site: crate::kb::CallSite,
    apply_functor: Symbol,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    pos_args: &SmallVec<[TermId; 4]>,
    spec_op_sym: Symbol,
    impl_op_sym: Symbol,
) {
    if kb.dispatch_rewrite_at(site).is_some() {
        // Idempotent — the same call site may be type-checked through
        // multiple paths (e.g. when the typer is invoked twice on a
        // body). The first rewrite is canonical.
        return;
    }
    let fn_arg = kb.intern("fn");
    let new_fn_ref = kb.alloc(Term::Ref(impl_op_sym));
    let new_named: SmallVec<[(Symbol, TermId); 2]> = named_args
        .iter()
        .map(|(s, t)| {
            if *s == fn_arg {
                (*s, new_fn_ref)
            } else {
                (*s, *t)
            }
        })
        .collect();
    let rewritten_apply = kb.alloc(Term::Fn {
        functor: apply_functor,
        pos_args: pos_args.clone(),
        named_args: new_named,
    });
    kb.record_dispatch_rewrite(site, rewritten_apply, spec_op_sym);
}

/// Last segment of a dotted qualified name (`foo.bar.baz` → `baz`).
/// Returns the input unchanged when it has no dot.
pub(crate) fn short_name_of(qn: &str) -> &str {
    qn.rsplit_once('.').map(|(_, s)| s).unwrap_or(qn)
}

/// WI-958 — THE one reader of "which symbol declares this operation". Every other
/// site that wants an op's owner goes through this, so the answer cannot be spelled
/// two ways: [`spec_op_parent_sort`] layers the spec-sort gates on it, and callers
/// wanting a member's SORT layer `kind_of(..) == Sort` (see `call_bracket_scopes`,
/// `rigidify_op_type_params`, the WI-374 member tie) — because this deliberately
/// returns the NAMESPACE for a free op, which declares no type parameters.
///
/// The parent owns the op's `requires_chain` — the right `callee_spec_sort` to feed
/// into `build_projected_requirements_list` (WI-228 fix: the previous Pin-now path
/// passed the spec sort instead of the impl's parent, so projections walked an
/// empty chain).
///
/// NOT [`KnowledgeBase::declaring_scope_symbol`], which answers the same question
/// from the symbol table and which a reader whose subject is a type param at depth 2
/// (`<ns>.<Sort>.<op>.<T>`, TWO plausible owners) rightly prefers — WI-943's
/// `op_declared_type_param_var` did, until WI-954 removed the need to ask at all.
/// This one's subject is always a DIRECT child of the scope it wants, so
/// the split has nothing to decide. What separates them is the symbols that are
/// NOT operations — this is called with any apply functor. MEASURED over
/// stdlib + anthill-stl (2598 distinct symbols): the two agree for all 373
/// operations and all 246 entity constructors, and disagree for 293 others — 227
/// entity FIELDS and 53 callback param/result slots, where the scope link is absent
/// or points a level up, and the 13 DOT-LESS names (the kernel vocabulary `Fact` /
/// `Sort` / `Rule` / `meta` / …, and the `anthill` namespace root), where the split
/// correctly finds NO parent and the scope link answers the `<global>` pseudo-scope.
///
/// That last group decides it — and say the strength of it plainly: a LATENT trap,
/// not a live bug. A caller like [`own_eq_op_carrier`] does
/// `impl_parent_of_op(functor)?` to reach a CARRIER SORT, so the scope link would
/// hand it `<global>` where the split stops: a `?` meaning "no owner, give up" turned
/// into a wrong answer that reads as a real one. But nothing in the tested surface
/// can tell the two apart — MEASURED, with this body replaced by
/// `declaring_scope_symbol` the whole workspace ran 4084 tests with exactly ONE
/// failure, the WI-958 test written against this paragraph. So it is a judgement
/// between two spellings that both work today, settled on failure mode: the split's
/// domain is exactly its readers' — it cannot answer a scope that is not a
/// declaration.
///
/// (The `kind_of`-vs-`has_kind` asymmetry between those caller-side gates and
/// [`spec_op_parent_sort`] was real, and WI-956 settled it — in `has_kind`'s favour,
/// against a driven case. The gate now lives once, in [`impl_parent_sort_of_op`].)
///
/// Note the qualified name is read via `qualified_name_of`, NOT by walking
/// `by_qualified_name` — one symbol can be registered under several keys (`BigInt`
/// alongside `anthill.prelude.BigInt`), and only the canonical name is the one this
/// splits.
pub fn impl_parent_of_op(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    let qn = kb.qualified_name_of(op_sym);
    let (parent_qn, _) = qn.rsplit_once('.')?;
    kb.try_resolve_symbol(parent_qn)
}

/// WI-956 — [`impl_parent_of_op`] narrowed to the case its callers almost always
/// mean: the SORT that declares `op_sym`, and `None` for a FREE operation (whose
/// parent is a NAMESPACE, which declares no type parameters and owns no requirement
/// slots). Five sites spelled this as `impl_parent_of_op(..).filter(kind is Sort)`;
/// [`spec_op_parent_sort`] is this plus its two extra gates.
///
/// `has_kind`, not `kind_of`. This is the WHOLE point of the function, so state it
/// once here rather than five times: a symbol's categories are a SET (§6.3 — an
/// eponymous constructor IS its sort), and `kind_of` reports only the FIRST-declared
/// one. The two answers differ, and DRIVEN, not argued:
///
/// ```text
/// entity Rec(n: Int64)          -- §6.3 sugar: registers Rec as Entity, then Sort
/// sort Rec                      -- the same name, now with a body
///   sort T = ?
///   operation peek(x: T) -> T
/// end
/// ```
///
/// loads clean, and `Rec` comes out `kinds = [Entity, Sort]` with
/// `type_params_of_sort(Rec) == ["T"]`. Under `kind_of` the gate answers "not a sort"
/// and `call_bracket_scopes(peek)` returned `[]` — the sort's own `T` silently
/// missing from the bracket scopes, so `peek[T = …]` could not name it. The same
/// misread dropped the parent in [`rigidify_op_type_params`], the WI-374 member tie,
/// [`names_any_requirement_slot`] and [`callee_requirement_slots`]. Write the two
/// declarations the other way round and everything works, which is precisely the
/// source-order sensitivity `kind_of`'s own doc warns against.
///
/// Inert on today's libraries, and that is worth writing down rather than leaving as
/// a green suite: MEASURED over stdlib + anthill-stl (2598 symbols), 64 sorts are
/// invisible to `kind_of` — all 64 from the top-level `entity X(…)` sugar, whose
/// desugared body is that one entity — and 0 of them carries a type param, a named
/// requirement slot or a `requires` chain, so 0 of the 373 operations has such a
/// parent. It takes the re-declaration above to build one.
pub(crate) fn impl_parent_sort_of_op(kb: &KnowledgeBase, op_sym: Symbol) -> Option<Symbol> {
    impl_parent_of_op(kb, op_sym).filter(|p| kb.has_kind(*p, crate::intern::SymbolKind::Sort))
}

/// WI-883 (058 §3.9) — a DEFAULTED spec op called at a carrier that is not an instance of
/// its spec: the refusal, or `None` when the call may run its default body.
///
/// NO SUPPLIER IS THE GAP A DEFAULT FILLS ONLY FOR AN INSTANCE. The default body's sibling
/// calls dispatch through the carrier's own provision, so at a carrier with none it is
/// entered and dies on the first of them — `max(p, q)` on a `P` providing `Eq` and
/// `PartialOrd` but not `WeakOrd` died "operation has no body: WeakOrd.compare".
///
/// AN OPERATION BODY ONLY, for the body-less arm's reason: a rule-body call is
/// `check_rule_body_requirements`' to judge, with the clause's declared `requires(…)` in
/// hand.
///
/// TWO HALVES, BOTH REQUIRED, cheapest first. [`carrier_is_an_instance`] finds no provision
/// of the spec at this carrier by any route — the binding-blind half, which alone cannot
/// see a GENERIC witness. And the call's own resolution fails — the half that sees one, and
/// that honours what the call site holds: its explicit selection (`f[Spec = W](…)`, 058
/// §4.1 tier 1), the enclosing sort's and operation's `requires` (with σ, as the body-less
/// arm's dispatch reads them, so the two arms agree). Neither alone: the resolution by
/// itself ends `NoMatch` wherever a call leaves an element open (`isEmpty(nil)`), and every
/// such program runs.
///
/// A spec with no ABSTRACT member ([`spec_has_an_abstract_member`]) is exempt: it is a
/// parameterized module, whose every operation runs by itself. A spec WITH one owes the
/// instance at EVERY member, including a default that happens never to reach the abstract
/// one (`label(s: T) -> Int64 = 0`): calling a spec's operation asserts the carrier is an
/// instance (058 §3.9), and what one default body reads today is that body's business, not
/// the call's — WI-20260921-3G1YT's reason for deleting the body walks, one question over.
/// A decision, raised by /code-review, and kept.
#[allow(clippy::too_many_arguments)]
fn defaulted_call_at_non_instance(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    subst: &Substitution,
    goal: &SortGoal,
    selections: &[InstanceSelection],
    carrier: Symbol,
    fn_sym: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    if env.enclosing_op().is_none()
        || carrier_is_an_instance(kb, carrier, goal.spec_sort)
        || !spec_has_an_abstract_member(kb, goal.spec_sort)
        || op_requires_covers_call(kb, env, subst, goal.spec_sort)
    {
        return None;
    }
    let sigma = SigmaCtx {
        subst,
        param_rigids: env.param_rigids(),
    };
    let scope = ResolutionScope {
        available_requires: env.enclosing_requires(),
        sigma: Some(&sigma),
        selected: selections,
        sub_goal_requires: env.sub_goal_requires(),
    };
    if !matches!(resolve(kb, goal, &scope), ResolutionResult::NoMatch { .. }) {
        return None;
    }
    unprovided_spec_at_carrier(kb, goal, carrier, fn_sym, span)
}

//! `check_operation_bodies` — typing every operation body.

use super::*;

/// Check operation bodies against their declared return types.
pub(super) fn check_operation_bodies(
    kb: &mut KnowledgeBase,
    op_syms: &[Symbol],
    errors: &mut Vec<TypeError>,
    // WI-745: parallel to `errors`; each error this pass pushes is tagged with
    // the `source_id` of the body it came from (every occurrence in one op body
    // carries that body's file). On entry `sources` is parallel to `errors`
    // (each tagging pass restores that on exit); it is restored here too.
    sources: &mut Vec<Option<crate::span::SourceId>>,
    // WI-314's region set for result-escape masking, computed ONCE by the caller —
    // see where it is used below for why it is a parameter and not a local.
    region_sorts: &HashSet<Symbol>,
) {
    struct OpInfo {
        op_sym: Symbol,
        return_type: Value, // WI-341 carrier-agnostic
        declared_effects: Vec<Value>,
        body_node: Rc<NodeOccurrence>,
        params: Vec<(Symbol, Value)>,
        span: Option<Span>,
        /// WI-424/WI-942 — every type param in scope for this body → its per-body
        /// rigid, enclosing-SORT params first (`sort_rigid_len` of them) then the
        /// op's own. Installed on the body env; see `TypingEnv::param_rigids`.
        param_rigids: Rc<Vec<(VarId, TermId)>>,
        /// How many leading `param_rigids` entries are the enclosing sort's.
        sort_rigid_len: usize,
        /// WI-441 — the full type-param rigidify substitution (op + enclosing
        /// sort params). The boundary effects check walks BOTH sides through
        /// it: `walk_type_deep_value` cannot rewrite inside a `Value::Node`
        /// carrier (occurrences are shared, not rebuilt), so a Node-carried
        /// callback arrow's row TAIL stays the original Global var while the
        /// declared atom was rigidified — the same param then compared
        /// unequal (`?Eff` vs `?Eff`). Resolving incurred components through
        /// this subst maps that Global to the same Rigid.
        rigidify: Rc<Substitution>,
        /// WI-K88TN — the op's own `requires` clauses, to seed its body's Γ₀
        /// ([`op_requires_gamma`]). The stored, un-rigidified form; the seed builder
        /// walks them, since it is the one place that knows which substitution to use.
        requires: Vec<Value>,
        /// WI-657(10): the op's enclosing sort, resolved ONCE here via
        /// `impl_parent_of_op` (already computed for `parent_sort_params` below).
        /// The per-op body loop reuses it for `set_enclosing_sort` instead of
        /// re-deriving it by a `qualified_name_of(..).to_string()` + rsplit +
        /// re-resolve — that string form is byte-identical to `impl_parent_of_op`.
        parent_sym: Option<Symbol>,
    }

    let mut ops_to_check = Vec::new();

    for &op_sym in op_syms {
        let rec = match crate::kb::op_info::lookup_operation_info(kb, op_sym) {
            Some(r) => r,
            None => continue,
        };
        let span = kb.functor_span(rec.op_sym).map(|s| s.span);
        // WI-398: a CYCLIC cross-parameter projection signature is ill-formed; the loud
        // error is raised once, for EVERY op, by `check_operation_signatures` (which
        // covers body-less free specs this body-check pass never reaches). Here we only
        // SKIP body-checking such an op so its un-resolvable projection params do not
        // cascade into spurious secondary errors.
        if param_projection_cycle(kb, &rec.params).is_some() {
            continue;
        }
        // Body-less ops (specs) have no body to type-check.
        let body_node = match rec.body_node {
            Some(n) => n,
            None => continue,
        };
        // WI-392: while CHECKING this operation's body, its OWN declared type
        // parameters are universally quantified — Skolemize them to `Var::Rigid`
        // so the body may USE them but never CONSTRAIN them (a `Rigid` unifies
        // only with itself, so e.g. `add(h, 1)` on `h: Elem` is correctly
        // rejected; the body must type-check for ALL `Elem`). Inner calls keep
        // their own FLEXIBLE `Global` type params, which solve TO these rigids
        // (rigid ⇒ global; `resolved_var` matches only `Global`), and
        // `check_unconstrained_type_params` passes them unchanged (it flags only
        // bare `Global`s) — so a self-receiver / recursive call whose type param
        // resolves to the enclosing rigid is no longer a false "unconstrained"
        // leak. Declared ⇒ check-mode ⇒ rigid; an *inferred* param would stay
        // flexible (you cannot infer a rigid), but operation type params are
        // always declared. A rigid in an effect-row position is CHECKED
        // structurally, never *bound* (`bind_row_tail` is the binding path), so
        // its WI-336 rigid-tail rejection is not on the checking path.
        //
        // WI-424: the ENCLOSING parametric sort's type params are skolemized the
        // same way — within a member body they denote THIS instance's parameters
        // (the parametricity tie, type-parameter-scoping.md §3), fixed-but-
        // abstract exactly like the op's own. The rigid asymmetry is what makes
        // the member-body threading land: a sibling call's flexible params solve
        // TO the rigids (a `Rigid` is never bound), so `iterator(c)`'s return
        // `Stream[Element, E]` carries the enclosing rigids through to an inner
        // `Stream.find`'s `[Elem, Eff]` and to the declared-effects check. The
        // (vid → rigid) map rides `OpInfo` onto the body env for the same-sort
        // sibling-call seeding in `check_apply_iter`.
        // WI-657(10): resolve the enclosing sort once; reused below for both
        // `parent_sort_params` and the `OpInfo.parent_sym` the body loop reads.
        let parent_of_op = impl_parent_of_op(kb, rec.op_sym);
        let parent_sort_params: Rc<Vec<(Symbol, TermId)>> = parent_of_op
            .map(|p| sort_type_params_as_pairs(kb, p))
            .unwrap_or_default();
        // The body's rigid bridge: enclosing-sort params first (`sort_rigid_len` of
        // them), then the op's own. Filled below, empty when the op has neither.
        let mut param_rigids: Vec<(VarId, TermId)> = Vec::new();
        let mut sort_rigid_len = 0usize;
        let mut rigidify_subst = Substitution::new();
        // WI-1FKR2: the THIRD family — a logical variable the author wrote INLINE in the
        // signature (`via(b: Box[?t]) -> Box[?t]`), which §5.4 quantifies exactly as it does
        // an `[A]` binder. Computed before `rec` is consumed below; empty for every operation
        // that writes none, which is almost all of them.
        let inline_type_params = inline_signature_type_params(
            kb,
            rec.op_sym,
            &rec.params,
            &rec.type_params,
            &parent_sort_params,
        );
        // WI-1FKR2: the op's OWN half is its declared brackets PLUS its inline variables —
        // both are per-call and caller-instantiated, so both sit after the enclosing sort's
        // prefix in `param_rigids` (see that field's doc: the sort view means "THIS
        // instance's params", which an inline variable is not). Joined HERE so the gate
        // below stays one test over the op's half and one over the sort's.
        let mut op_own_params = rec.type_params.clone();
        op_own_params.extend(inline_type_params);
        let (params, return_type, declared_effects) =
            if op_own_params.is_empty() && parent_sort_params.is_empty() {
                (rec.params, rec.return_type, rec.effects)
            } else {
                let mut all_params = op_own_params;
                // Read BEFORE the sort's half is appended — the split below is exactly here.
                let op_param_len = all_params.len();
                // WI-849: the op table is `Var`-typed; the sort table is still TermId-typed
                // (its other consumers want the param as a TERM, under `&KnowledgeBase`
                // where they could not re-alloc).
                all_params.extend(param_pairs_as_vars(kb, &parent_sort_params));
                let rigidify = rigidify_op_type_params(kb, &all_params);
                // EVERY param the rigidifier was given gets its bridge ([`rigid_bridge`]):
                // what the record holds is what a written occurrence resolves to
                // ([`type_param_global_var`], WI-943).
                // `all_params` is `op_own_params ++ parent_sort_params`; `param_rigids` is
                // the other order — enclosing SORT params first, so `sort_rigid_len` is where
                // the op's own begin. Split and reverse explicitly rather than partitioning
                // in-place: the length must be read BETWEEN the two halves, which is why
                // `op_param_len` is taken above rather than here.
                let (op_half, sort_half) = all_params.split_at(op_param_len);
                param_rigids = rigid_bridge(&rigidify, sort_half);
                sort_rigid_len = param_rigids.len();
                param_rigids.extend(rigid_bridge(&rigidify, op_half));
                let params = rec
                    .params
                    .iter()
                    .map(|(n, t)| (*n, walk_type_deep_value(kb, &rigidify, t)))
                    .collect();
                let return_type = walk_type_deep_value(kb, &rigidify, &rec.return_type);
                let declared_effects = rec
                    .effects
                    .iter()
                    .map(|e| walk_type_deep_value(kb, &rigidify, e))
                    .collect();
                rigidify_subst = rigidify;
                (params, return_type, declared_effects)
            };
        // WI-1059/WI-1061: the THIRD family of rigids — a parameter of ANOTHER sort left
        // unwritten in a parameter's TYPE, at its top level (WI-1059) or nested inside
        // one of its bindings (WI-1061). Runs for EVERY op, including one that
        // declares no `[T]` and sits in no parametric sort (the two-family branch
        // above is skipped entirely for those, and `feed(s: Stream[T = Int64])` is
        // exactly that shape). AFTER the substitution, so a slot written as the op's
        // own `[E]` is already the rigid WI-392 minted and is not skolemized twice.
        let params: Vec<(Symbol, Value)> = params
            .iter()
            .map(|(n, t)| {
                let ty = rigidify_unwritten_sort_params(
                    kb,
                    UnwrittenFill::Projection(*n),
                    t,
                    SlotPosition::Body {
                        sort: parent_of_op,
                        rigidify: &rigidify_subst,
                    },
                    body_node.span,
                    body_node.owner,
                );
                (*n, ty.unwrap_or_else(|| t.clone()))
            })
            .collect();
        // NOT THE RETURN TYPE, and **WI-1063** is why — not an omission but the other half of
        // one rule. Read the quantifier off the POLARITY of the arrow.
        //
        // A PARAMETER's unwritten slot is negative-position and UNIVERSAL: the caller
        // instantiates it, so it is flexible at a call and rigid HERE, in the body, which is
        // what the walk just above enforces (WI-1059/WI-1061). A RETURN's is positive-position
        // and EXISTENTIAL: `-> Stream[T = Int64]` declares `∃E. Stream[T = Int64, E]`. The BODY
        // PACKS a witness — so `widen(s: Stream[T = Int64, E = {Error}]) -> Stream[T = Int64]
        // = s` is CORRECT as written and must keep loading, and "the inferred type is more
        // specific than the declared one" is existential introduction, not a defect. EACH USE
        // OPENS, minting a fresh skolem per opening, so `widen(s) : Stream[T = Int64, E = ρ]`
        // and the CONSUMER is what fails. The opening therefore lives at the call
        // ([`open_existential_return`], in `check_apply_iter`) and there is nothing to do here.
        //
        // THE OTHER READING WAS BUILT, MEASURED AND REJECTED, and it is worth the lines
        // because it is one call to the same function above (`UnwrittenFill::Anonymous` over
        // `return_type`, written back onto `OpInfo.return_type`) and so looks like the obvious
        // completion. It refuses `widen` at `widen.return`, `expected E = ?E` — that is the
        // WRONG QUANTIFIER, a universal in a positive position, demanding the body be good for
        // EVERY row when only a witness was asked. Its cost is the symptom: 40 tests across
        // thirteen delivered tickets (WI-353/374/401/402/405/457/480/488/491/734/762/776/839),
        // mostly correct programs refused for failing to be polymorphic. Against that, the
        // existential reading shipped costing THREE — the two WI-1061 pins that flip by design
        // and `wi374_expansion_test::foreign_bare_return_op_loads_and_narrows`, which pinned
        // the accepting side of this very hole (a `List` of Strings bound to an annotated
        // `List[T = Int64]`, driven on the delivered tree). Do not revive the universal reading
        // without defending it on its merits.
        //
        // It also silently retires the escape gate: `abstracting_return_error` sits in the
        // `else` of `!conforms`, so materializing the return makes the WI-401/402/457/480/488/
        // 491 family unreachable rather than merely re-fixtured. Opening at the call leaves
        // that gate's precondition — a bare abstract-spec return CONFORMING by provider upcast
        // — exactly as it was; driven, its diagnostic is byte-identical before and after.
        //
        // `docs/design/type-parameter-scoping.md` §5's informal "erased" ("no consumer-side
        // mechanism can soundly recover `l`'s element or effect") is this existential said
        // without the word, and `docs/kernel-language.md` §"Expansion during unification" now
        // states both polarities. The two documents were never in conflict; one names the
        // quantifier and the other describes its effect.
        ops_to_check.push(OpInfo {
            op_sym: rec.op_sym,
            return_type,
            declared_effects,
            body_node,
            params,
            span,
            sort_rigid_len,
            param_rigids: Rc::new(param_rigids),
            rigidify: Rc::new(rigidify_subst),
            parent_sym: parent_of_op,
            requires: rec.requires.clone(),
        });
    }

    // WI-314: region set for result-escape masking — program-global, so
    // compute it once before the per-op loop.
    //
    // WI-20260920-E3DC5 — "ONCE" NOW MEANS ONCE. This function is called PER SORT
    // (`type_check_sorts_collect`'s loop) plus once for the free ops, so the line that
    // used to stand here — `let region_sorts = region::region_sorts(kb);` — ran 204 times
    // on a stdlib load, and each run is a full walk of the provision relation
    // (`all_provisions`, which `modifiable_claim_heads` filters down to the `Modifiable`
    // claims). That is `sorts × provisions` — a term that grows with BOTH factors, in a
    // pass whose own comment said it was computed once. MEASURED (release, stdlib + an
    // empty namespace, medians of 15 interleaved runs, both arms in one binary): the
    // `type_check_sorts` mark is 18.61 ms with the per-call walk and 16.09 ms with this
    // hoist, and its growth when WI-20260919-HXGXF's gate is forced open falls from
    // +3.37 ms to +1.70 ms. Per-call counters: `all_provisions` goes from 204 calls to 1.
    // Hoisted to the caller, which computes it before the loop, exactly as this comment
    // always claimed. `region.rs`' own note ("`region_sorts` is computed ONCE per typing
    // pass — `type_check_sorts` calls it before the per-op loop") is true as of this
    // change and was not before.
    //
    // THE HOIST IS ONLY SOUND IF THE SET IS LOOP-INVARIANT, which is the same property
    // the `simp_enabled` gate below rests on and states: this pass rewrites op bodies and
    // asserts no `SortProvidesInfo`. Pinned rather than asserted in prose — the
    // `debug_assert` recomputes and compares, so every debug-build test run (the whole
    // suite) checks the invariant at all 204 call sites, and a future pass that starts
    // minting `Modifiable` claims mid-loop is LOUD instead of silently masking a `Modify`
    // it should have kept. It restores the per-call walk in debug builds, which is what
    // those builds already paid before this change, so it costs nothing that was not
    // already being spent.
    debug_assert_eq!(
        *region_sorts,
        crate::kb::region::region_sorts(kb),
        "WI-20260920-E3DC5: the region set changed during type-checking, so hoisting it \
         out of the per-sort loop is no longer sound — a pass now asserts a `Modifiable` \
         provision mid-pass and result-escape masking would read a stale set"
    );

    // WI-657(9): the `@[simp]` gate is loop-invariant across this whole pass (typing
    // rewrites op bodies, never asserts/retracts an equation), so compute it ONCE
    // here and thread it into each per-op body walk via `type_check_node_gated` —
    // instead of `type_check_node` recomputing `has_simp_equations` + two
    // `simp_equation_rids` bucket scans per operation.
    let simp_enabled = crate::kb::simp_rewrite::has_simp_equations(kb) || kb.has_dot_applies;
    let simp_rids: Vec<RuleId> = if simp_enabled {
        kb.simp_equation_rids()
    } else {
        Vec::new()
    };

    // WI-745: the file whose occurrences the CURRENT op's errors come from. Tag
    // lazily — errors pushed during op K are stamped at the top of iteration K+1
    // (and the final flush), which is robust to the loop's early `continue`s.
    let mut cur_src: Option<crate::span::SourceId> = None;
    for op in &ops_to_check {
        while sources.len() < errors.len() {
            sources.push(cur_src);
        }
        cur_src = Some(op.body_node.span.source);
        let mut env = TypingEnv::empty();
        // WI-20260830-JM7A8 — this pass is the DRAINER for value-precondition failures,
        // so it installs the sink. `check_apply_iter` then records them and keeps typing
        // the call, which is what leaves the call's effects attributed and the
        // op-boundary coverage check below able to run. Drained after the body match on
        // BOTH arms — a body that also failed to type for an unrelated reason still owes
        // the precondition diagnostic.
        env.collect_deferred_preconditions();
        // WI-221: snapshot the enclosing sort + its requires chain so
        // defer-to-requirement detection in `check_apply` runs from a
        // cached chain instead of re-walking SortRequiresInfo per call.
        // WI-657(10): reuse the parent resolved once at ops_to_check build time.
        env.set_enclosing_sort(kb, op.parent_sym);
        // WI-562: snapshot this op's OWN op-scoped `requires` (WI-448) so the
        // body's abstract spec-op calls against an op-type-param the op
        // `requires` are licensed — `List.member requires Eq[E]` covers its
        // `eq(head, x)` without the whole `List` sort having to `requires Eq[T]`
        // (which wrongly blocked `IndexedSeq.nth` on a `List[NonEq]`).
        // WI-822 LEG 1: and APPEND those requirements' frame slots to the chain the
        // line above installed, so a body call the licence covers but no runtime
        // value can direct has a slot to defer to. Ordered — the op setter composes
        // onto the sort half.
        env.set_enclosing_op(kb, op.op_sym);
        // WI-424/WI-942: the body's param → rigid bridge, both scopes in one list
        // (see the `TypingEnv::param_rigids` field doc; Rc clone).
        env.set_param_rigids(Rc::clone(&op.param_rigids), op.sort_rigid_len);
        // WI-400 (body-site): a projection param type (`k: s.cell.T`) must be discharged
        // against the OTHER params' DECLARED types before it is bound into the body env —
        // the body-check peer of the call-site elimination (`check_apply_iter` / WI-398,
        // which discharges against ARGUMENT types). δ-grounding makes a MANIFEST receiver's
        // member concrete (`s: Wrapper[P = Inner[T = String]]` ⟹ `k : String`); an ABSTRACT
        // receiver (`s: State`, `P` open) whose declared interface provides the member
        // forms a rigid NEUTRAL (`k : ⟨s.provider⟩.K` — abstract-stays-poly), which the
        // body then path-identity-matches via the ζ arm of `unify_types`. Only a member NO
        // interface declares stays a loud error. Only ops whose params carry a projection
        // pay for the map + walk.
        if op
            .params
            .iter()
            .any(|(_, t)| value_contains_projection(kb, t))
        {
            // Order-INDEPENDENT elimination (matching the call-site, which discharges over
            // a fully-populated `param_to_arg_type`): iterate to a FIXPOINT — each pass
            // re-discharges every still-projection param against the current `decl` and
            // commits any param whose type CHANGED (a manifest receiver grounding, or a
            // receiver resolved by an earlier pass), so a receiver declared in ANY order
            // (forward OR backward) feeds its dependents. A pass with no change is the
            // fixpoint. `Ok` no longer implies "no projection remains" — a stable abstract
            // NEUTRAL eliminates to itself (`structural_eq`, no change) and legitimately
            // survives; an `Err` means the receiver is not YET resolved (retried) OR is
            // genuinely un-dischargeable (surfaced after the fixpoint).
            let mut decl: HashMap<Symbol, Value> =
                op.params.iter().map(|(n, t)| (*n, t.clone())).collect();
            loop {
                let mut changed = false;
                for (name, _) in &op.params {
                    let cur = decl.get(name).cloned().expect("param present in decl");
                    if value_contains_projection(kb, &cur) {
                        if let Ok(elim) = eliminate_type_projections(
                            kb,
                            &cur,
                            &decl,
                            None,
                            &TypeErrorContext::OperationArgument {
                                op_name: op.op_sym,
                                param: *name,
                            },
                            op.span,
                        ) {
                            if !views_structurally_equal(kb, &elim, &cur) {
                                decl.insert(*name, elim);
                                changed = true;
                            }
                        }
                    }
                }
                if !changed {
                    break;
                }
            }
            // Fixpoint reached. A param that STILL eliminates to an `Err` is genuinely
            // un-dischargeable (missing member, non-param receiver); surface it and skip
            // this op's body-check to avoid cascading (mirrors the cyclic-signature skip).
            // A param that eliminates to `Ok` but still carries a projection is a sound
            // abstract NEUTRAL (abstract-stays-poly) — bound as-is for the ζ path-identity.
            let mut proj_failed = false;
            for (name, _) in &op.params {
                let cur = decl.get(name).cloned().expect("param present in decl");
                if value_contains_projection(kb, &cur) {
                    if let Err(e) = eliminate_type_projections(
                        kb,
                        &cur,
                        &decl,
                        None,
                        &TypeErrorContext::OperationArgument {
                            op_name: op.op_sym,
                            param: *name,
                        },
                        op.span,
                    ) {
                        errors.push(e);
                        proj_failed = true;
                    }
                }
            }
            if proj_failed {
                continue;
            }
            for (name, _) in &op.params {
                env.bind_var(*name, decl.remove(name).expect("param present in decl"));
            }
        } else {
            for (name, ty) in &op.params {
                // WI-341 Stage A: op param types are carrier-agnostic `Value`. A
                // callback param whose arrow effect is denoted-bearing binds as a
                // `Value::Node` arrow; a ground param as `Value::Term`.
                env.bind_var(*name, ty.clone());
            }
        }

        // WI-1059: the params AS BOUND — after the projection fixpoint above, which may
        // have rewritten them. The return type and the declared effects are discharged
        // against exactly these, so a projection in a signature and the same projection in
        // the body resolve through one table.
        let param_map: HashMap<Symbol, Value> = op
            .params
            .iter()
            .map(|(n, t)| (*n, env.lookup_var(*n).unwrap_or_else(|| t.clone())))
            .collect();

        // WI-491: a COVARIANT return rooted at the receiver — an expression-carried
        // projection of one parameter's own type (`operation iterator(m: MappedStream)
        // -> m.Sort = m`, `m.Sort` = the whole type of `m`; also a member form `m.T`) —
        // is eliminated against the op's own parameter types BEFORE the conformance and
        // escape checks. Then the body (`= m`, type `MappedStream`) conforms to the
        // projected type, and the WI-401 avoidance gate sees the input-rooted concrete
        // type (`m.Sort` ⟹ `MappedStream`, same sort as the body ⟹ admitted) rather
        // than the raw `ExprCarried`, which has no sort functor.
        //
        // WI-1059 widened the gate from the TOP-LEVEL form to a projection ANYWHERE
        // ([`value_contains_projection`], the same predicate the parameter fixpoint
        // above uses). The note that stood here said a NESTED projection
        // (`-> List[T = s.T]`, `-> Stream[T = l.T, E = {}]`) was "left to the existing
        // conformance machinery" — and that worked only while the receiver was ABSTRACT:
        // with `s: Stream` carrying no `T` binding, `s.T` survived on BOTH sides and the
        // ζ arm matched neutral to neutral. Once an unwritten parameter is materialized
        // ([`rigidify_unwritten_sort_params`]), the receiver is MANIFEST, so the body
        // resolves `s.T` to the enclosing rigid while the declared return still read the
        // raw neutral — `expected List[T = s.T], got List[T = ?T]`, measured across the
        // stdlib. Eliminating both against one param table is what keeps them the same
        // type. An abstract receiver still eliminates to the same neutral (`-> p.K = m`,
        // WI-400), unchanged.
        let effective_return = if value_contains_projection(kb, &op.return_type) {
            match eliminate_type_projections(
                kb,
                &op.return_type,
                &param_map,
                None,
                &TypeErrorContext::OperationReturn {
                    op_name: op.op_sym,
                    surface: None,
                },
                op.span,
            ) {
                Ok(elim) => elim,
                // The projection is un-dischargeable: the receiver is not a
                // parameter (`-> result.Sort`) or names a member the receiver's
                // type does not have (`-> m.Nonexistent`). Surface the PRECISE
                // elimination error and skip this op's body check — never swallow
                // it behind a vaguer conformance mismatch (project principle:
                // loud error early, no fallback). Mirrors the param-projection
                // `proj_failed` skip above.
                Err(e) => {
                    errors.push(e);
                    continue;
                }
            }
        } else {
            op.return_type.clone()
        };

        // WI-1059: the DECLARED EFFECTS get the same discharge as the return, against the
        // same param table, and for the same reason: `Stream.collect(s: Stream) effects
        // s.E` reads its row off the receiver, and once `s` carries its slot the BODY
        // incurs the enclosing rigid `?E` while the declared atom is still the neutral
        // `s.E` — `expected declared: [s.E], got undeclared effect: ?E`, seven of them
        // across `sort Stream` alone. An atom carrying no projection (a concrete label, a
        // denoted `Modify[c]`, a row var) is left untouched, and an UNDISCHARGEABLE one is
        // surfaced rather than silently kept — the same policy as the return.
        let mut effect_proj_failed = None;
        let effective_effects: Vec<Value> = op
            .declared_effects
            .iter()
            .map(|e| {
                if !value_contains_projection(kb, e) {
                    return e.clone();
                }
                match eliminate_type_projections(
                    kb,
                    e,
                    &param_map,
                    None,
                    &TypeErrorContext::OperationEffects { op_name: op.op_sym },
                    op.span,
                ) {
                    Ok(elim) => elim,
                    Err(err) => {
                        effect_proj_failed.get_or_insert(err);
                        e.clone()
                    }
                }
            })
            .collect();
        if let Some(err) = effect_proj_failed {
            errors.push(err);
            continue;
        }

        // WI-270: thread the declared return type as the body's
        // top-down `expected`. The body's `let v: T = …`-style
        // annotations and inner Apply/Constructor calls then see a
        // caller-side hint that pins otherwise-free type-params.
        // WI-341: `type_check_node`'s top-down hint is a ground `TermId`; pass it
        // for a ground return type, drop it (`None`) for a `Value::Node` (denoted-
        // bearing) return — never materialize the occurrence into the hint.
        // WI-K88TN: Γ₀ is the op's OWN value preconditions, not `FlowEnv::empty()` —
        // proposal 050's Hoare reading, and what discharges the now-DECIDED rigid
        // obligation a body raises against a constrained callee. Built here because this
        // is the one place holding both the clauses and the `rigidify` that puts them in
        // the body's vocabulary.
        let gamma0 = op_requires_gamma(kb, &op.requires, &op.rigidify);
        // WI-20260830-JM7A8: where THIS op's errors start, so the preconditions its body
        // deferred can be spliced back in AHEAD of the op-boundary verdicts below rather
        // than trailing them. A precondition names a CALL and carries that call's span;
        // the return/effect errors are the operation's own. Reading them in that order is
        // what the single-diagnostic output looked like before this ticket, with the
        // second verdict added rather than the first moved.
        let op_err_mark = errors.len();
        match type_check_node_gated_in_gamma(
            kb,
            &env,
            &op.body_node,
            Some(effective_return.clone()),
            simp_enabled,
            &simp_rids,
            gamma0,
        ) {
            Ok(result) => {
                // WI-283: the typer is tree-producing — `result.node` is
                // the (possibly `@[simp]`-rewritten) body. Write the
                // redex-free tree back so the return-type check below and
                // every downstream consumer (req_insertion, eval, codegen)
                // see the rewritten form. Only when a rule actually fired
                // (`ptr_eq` unchanged ⇒ no allocation, no write).
                if !Rc::ptr_eq(&result.node, &op.body_node) {
                    kb.set_op_body_node(op.op_sym, Rc::clone(&result.node));
                }
                // WI-20260828-N2FHM — see [`surviving_dot_apply`]. Checked on the STORED
                // tree (after the write-back above), because the stored tree is what eval
                // will run; checking `op.body_node` would ask about the pre-rewrite one.
                if let Some((member, span, receiver)) = surviving_dot_apply(&result.node) {
                    errors.push(TypeError::DotDispatchNoMatch {
                        span,
                        member,
                        // The stamp the `DotApply` frame left on the raw receiver (WI-732),
                        // read through the same `sort_functor_of_view` that frame's own
                        // refusal uses — so the backstop's message names the same sort the
                        // in-frame diagnostic would have, rather than claiming the receiver
                        // is unresolved when it is not.
                        receiver_sort: receiver
                            .inferred_type()
                            .and_then(|ty| sort_functor_of_view(kb, &ty)),
                        receiver_param: None,
                    });
                }
                // WI-20260919-N31XX (proposal 065, "The rule") — A RIGID READ AS A VALUE
                // NEEDS A `requires TypeValue[T = B]` IN SCOPE.
                //
                // ON THE STORED TREE, AFTER THE WRITE-BACK ABOVE, and that placement is
                // the rule rather than a detail. 065 §6 measured the nineteenth census
                // site: `operation dq[K]() -> Int64 = size(put(mkq(K), "a", 1))` passes
                // `K` to `rule mkq(?k) <=> Map[K = ?k, V = Int64].empty() @[simp]`, and
                // after inlining `K` sits in a TYPE position. Judged BEFORE expansion —
                // which is where WI-20260919-BQHGD's temporary census pass sat, at the
                // top of this function — the rule would refuse a program whose only use
                // of `K` is as a type. `result.node` is the redex-free body, so the rule
                // sees what eval will run. DRIVEN by
                // `wi_n31xx_type_value_read_rule_test::a_simp_expanded_type_position_is_not_a_value_read`,
                // whose `dq` carries no clause beside a control op that does; measured
                // the other way round, `wi_h054k_type_position_subst_test` is the census
                // file that does NOT appear among the refusals when the rule goes on.
                //
                // ONE DIAGNOSTIC PER BODY, the first read in source order, like the
                // dot backstop above: the repair is a single clause on the signature, so
                // reporting every read of the same parameter would be one fix told many
                // times.
                let reads = rigid_value_reads(kb, &result.node);
                if !reads.is_empty() {
                    let backed = type_value_backed_params(kb, op.op_sym);
                    if let Some((_, param, span)) =
                        reads.into_iter().find(|(vid, _, _)| !backed.contains(vid))
                    {
                        errors.push(TypeError::TypeValueReadUnbacked {
                            span,
                            param,
                            op: op.op_sym,
                        });
                    }
                }
                let mut subst = Substitution::new();
                // WI-341/342: both sides are carrier-agnostic `Value` — the
                // subtype check takes them directly (`Value: TermView`), where a
                // lambda's `Value::Node` arrow flows cross-carrier against the
                // declared return arrow. `TypeError` fields are `Value` (S2), so
                // the carrier flows straight into the diagnostic (no re-grounding).
                // WI-461: a bare self-receiver identity body (`= l`) infers the bare
                // carrier sort; if it does not conform directly, retry with the body type
                // refined to the receiver's projections (`List` → `List[T = l.T]`) so a
                // provided return threading the projection conforms. Purely additive — only
                // attempted on the unrefined failure — so no delivered accept regresses.
                // WI-20260904-50B2K — SOLVE THE BODY'S OWN HOLES FROM THE DECLARATION,
                // then compare the SOLVED type. This is the checking direction at the
                // return position: a body type carrying a free variable is one the body
                // did not determine, and the declaration is what determines it.
                //
                // BOTH HALVES ARE LOAD-BEARING, and the first cut had only the unify —
                // measured, it changed NOTHING. `unify_types` binds into `subst`
                // correctly (`?param := Int64`, verified by probe), but `types_compatible`
                // was still handed the UNRESOLVED `result.ty` and never saw the binding.
                // Resolving is what makes the unify count.
                //
                // WHY IT IS NEEDED: `let f = lambda v -> set_cell(s, v)` then `f` RETURNED.
                // The body pins `v` (`set_cell` declares `v: Int64`) but that call is
                // Path 1, whose argument unification binds `?v` into the CALLEE-
                // INSTANTIATION σ and drops it with the call — no substitution is threaded
                // through an operation body, so a binding made in one call cannot reach
                // the lambda that owns the variable. Both neighbours already work and say
                // this is the only hole: the same lambda written DIRECTLY in the return
                // position takes rung 2, and the ANNOTATED `lambda (v: Int64)` takes rung
                // 1. Until an un-annotated binder was a real variable this never showed,
                // because an inert `type_var` conformed to anything.
                //
                // The unify's boolean is DISCARDED: `types_compatible` below is still the
                // verdict, since unify is EQUALITY while conformance is SUBTYPING plus the
                // refinement retry. WHAT A FAILED UNIFY LEAVES IN σ is settled at the
                // relation — WI-20260904-60143, see [`unify_types`]' "what survives a
                // `false`" note: it does not roll back (deliberately — four refusals are
                // reached BY the partial binding), and an author-ordered slot list now
                // contributes every slot that agreed rather than an arbitrary prefix. This
                // site still takes the probe, because that settles WHICH bindings a failed
                // unify leaves and not WHETHER this σ should absorb them, and this one is
                // read two lines down into a user-visible message.
                // PROBE ON A CLONE, COMMIT ONLY ON SUCCESS — the file's own pattern
                // (`hint_instantiation_subst`), applied here because this σ is READ two
                // lines down and its reading is USER-VISIBLE. `unify_types` binds as it
                // descends and does not roll back, so a pair that fails partway leaves its
                // partial bindings behind; `body_ty` is what `conformance_error` renders,
                // so on the REFUSAL path — the path
                // `the_body_use_binds_a_let_bound_lambdas_binder_before_the_declaration_can`
                // exercises — the "got …" half of the message would be built from a
                // half-applied substitution. A `Substitution` clone is O(1) (`imbl`,
                // WI-569), so this costs a refcount bump on the path that already failed.
                // Raised by `/code-review`; the file-wide census of the ~10 sites sharing
                // the discarded-boolean idiom is WI-20260904-60143, and this is the one of
                // them whose σ a diagnostic reads.
                let mut probe = subst.clone();
                if unify_types(kb, &mut probe, &result.ty, &effective_return) {
                    subst = probe;
                }
                // PURE σ (`walk_type_deep_value`), not the grounding
                // `resolve_type_deep_value`: the typer singles the pair out at
                // `validate_arg_against_param` — a rigid projection must stay an inert
                // neutral leaf. WI-491/WI-1059 keep `-> List[T = s.T]` neutral on BOTH
                // sides; grounding only the body side would re-open the asymmetry WI-1059
                // closed. Found by `/code-review`.
                let body_ty = walk_type_deep_value(kb, &subst, &result.ty);
                let conforms = types_compatible(kb, &mut subst, &body_ty, &effective_return)
                    || match refine_self_receiver_body_type(kb, &result.node, &body_ty) {
                        Some(refined) => {
                            let mut probe = Substitution::new();
                            let ok = types_compatible(kb, &mut probe, &refined, &effective_return);
                            if ok {
                                subst = probe;
                            }
                            ok
                        }
                        None => false,
                    };
                if !conforms {
                    // WI-801: through the shared renderer — an operation RETURNING a
                    // callback (`-> Function[A = (Int64, Int64), B = Int64]`) is the
                    // third channel that can carry an arity disagreement, and the
                    // third that printed the two sides identically.
                    errors.push(conformance_error(
                        kb,
                        effective_return.clone(),
                        body_ty.clone(),
                        None,
                        TypeErrorContext::OperationReturn {
                            op_name: op.op_sym,
                            surface: None,
                        },
                        Some(&result.node),
                    ));
                } else if let Some(e) =
                    abstracting_return_error(kb, &body_ty, &effective_return, op.op_sym)
                {
                    // WI-401: the body conforms, but only by a provider UPCAST to a bare
                    // abstract spec — the sealing return that would let an abstract member
                    // escape its scope. Forbidden so the base model stays escape-free (§5).
                    errors.push(e);
                } else if let Some(e) = branch_leaf_abstracting_return_error(
                    kb,
                    &result.node,
                    &effective_return,
                    op.op_sym,
                ) {
                    // WI-457: a JOIN body widened divergent concrete providers up to the
                    // bare spec, so the joined `body_ty == ret_sort` slipped the direct
                    // gate above. Re-apply it per branch leaf — the same escape, hidden
                    // behind the branch join.
                    errors.push(e);
                }

                // WI-314: operation-boundary effect masking. Drops effects
                // on non-escaping locals (as before) and masks / re-keys
                // `Modify[result]` from freshly-allocated regions per the
                // return type — see kb::region. WI-657(11): `<op>.result` is
                // now resolved LAZILY inside `op_boundary_effects`, only when the
                // result-region / callback-param arm actually needs it (the common
                // effect-free op no longer pays the per-op format+resolve).
                let ext_effects = crate::kb::region::op_boundary_effects(
                    kb,
                    &result.env,
                    &op.return_type,
                    op.op_sym,
                    region_sorts,
                    &result.effects,
                );
                // Validate every effect the body produces was declared. WI-365:
                // compare by representation-independent STRUCTURAL IDENTITY
                // (`views_structurally_equal`), not by rendered display name. A
                // name compare is fragile in both directions — distinct effects
                // can share a name, and one effect can render two ways across
                // representations. The concrete failure: an abstract sort's
                // `effects E` row variable is stored as `Ref(S.E)` in the
                // signature, but a body call — the abstract self-receiver spec
                // op (`splitFirst(s)`) or the recursive op itself
                // (`collect(rest)`) — has that row variable resolved through its
                // `SortAlias` to the (anonymous) alias `Var`. As names those are
                // `"E"` vs `"?_"` and never match, so a pure-`effects E` body
                // spuriously reported `undeclared effect: ?_`.
                //
                // Canonicalize first, then compare structurally — mirroring how
                // the return-type check above (`types_compatible`) already walks
                // both sides. The (empty) `canon_subst` walk collapses a
                // sort-parameter `Ref(S.E)` to its alias `Var` on both the
                // declared and the body side, so the row variable's two encodings
                // agree; a concrete effect sort (`Error`) is not a sort param and
                // walks to itself; a denoted `Modify[c]` (a `Value::Node`)
                // compares structurally against another via the same `TermView`
                // recursion. Diagnostics still render the raw (readable) names.
                // WI-441: the op's rigidify subst (not an empty one) — a
                // Node-carried callback arrow's row tail reaches here as the
                // ORIGINAL Global var (`walk_type_deep_value` does not rewrite
                // inside occurrence carriers), so resolving through the
                // rigidify maps it to the same Rigid the declared atom became.
                // WI-1059: over `effective_effects` — the declared atoms with their
                // receiver projections discharged — not the raw `op.declared_effects`.
                // The DISPLAY is built from the same list, so a diagnostic names the atoms
                // AS DISCHARGED: `effects s.E` on a manifest receiver prints the row it
                // resolved to, not the written `s.E`. That is the honest rendering for this
                // message, whose two halves must be comparable — printing the written form
                // beside a resolved incurred effect is what made the pre-WI-441 version
                // report `expected [E], got ?_` for a row that matched.
                //
                // WI-20260830-APWM3: FLATTENED FIRST. A declared atom that is itself a
                // ROW — which is what an `effects {llm.E, …}` projection becomes as
                // soon as the receiver's type is concrete — contributes its MEMBERS,
                // not itself; see [`explode_declared_effect_row`] for the defect and
                // for why the absences ride out of the same walk instead of a separate
                // top-level `absent` scan. A non-row atom is kept whole, so a plain
                // label, a denoted `Modify[c]` and a bare row var compare exactly as
                // before.
                let canon_subst = (*op.rigidify).clone();
                let atom_label_key = kb.intern("label");
                let mut declared_canon: Vec<Value> = Vec::new();
                // WI-20260825-CBRSW — the DENIED atoms of the declared row, kept apart
                // so an effect the row explicitly forbids is not reported as one the
                // author merely forgot to declare. The two have different repairs: an
                // undeclared effect is fixed by adding the label, and a denied one
                // cannot be — the row says the body must not perform it. Proposal 064's
                // whole value is in that negative claim, so it gets its own message.
                let mut declared_absent: Vec<Value> = Vec::new();
                // THE DISPLAY IS BUILT FROM THE SAME FLATTENING, which is the rule the
                // pre-APWM3 note here already stated for the elimination — "a
                // diagnostic names the atoms AS DISCHARGED" — carried one step
                // further. The two halves of this message must be comparable, and
                // printing `{merge[left = present[label = External], right =
                // empty_row]}` beside an incurred `External` is the un-comparable
                // rendering that made the gap read as a mystery rather than as the
                // over-declaration it asks for. Absences keep their written `-X` form
                // via [`effect_atom_display`].
                let mut declared_display: Vec<String> = Vec::new();
                for e in &effective_effects {
                    match explode_declared_effect_row(kb, e) {
                        Some((admitting, absent)) => {
                            for a in &admitting {
                                declared_display.push(effect_atom_display(kb, a, atom_label_key));
                                declared_canon.push(walk_type_deep_value(kb, &canon_subst, a));
                            }
                            for l in &absent {
                                declared_display
                                    .push(format!("-{}", type_display_name_value(kb, l)));
                                declared_absent.push(walk_type_deep_value(kb, &canon_subst, l));
                            }
                        }
                        None => {
                            declared_display.push(effect_atom_display(kb, e, atom_label_key));
                            declared_canon.push(walk_type_deep_value(kb, &canon_subst, e));
                        }
                    }
                }
                for effect in &ext_effects {
                    // WI-441: a ROW-shaped incurred effect — a callback's row
                    // value flowing into the body effects (applying a
                    // `@ {EffP, -…}` callback incurs its whole row; a declared
                    // row var bound at a call site walks to a `merge(…)`
                    // structure) — EXPLODES into its components: each present
                    // label and each row-tail var is checked against the
                    // declared atoms individually. Absences are constraints,
                    // not incurred effects, and `empty_row` contributes
                    // nothing. A non-row effect stays a single atom. Each
                    // component is canon-walked AFTER the explode: a
                    // Node-carried row's tail extracts as the raw Global var,
                    // which only the per-component walk maps to its Rigid.
                    let components: Vec<Value> = match explode_incurred_effect_row(kb, effect) {
                        Some(atoms) => atoms,
                        None => vec![effect.clone()],
                    };
                    for comp in &components {
                        let comp_canon = walk_type_deep_value(kb, &canon_subst, comp);
                        // WI-818: a declared GUARDED atom `L :- g` conservatively
                        // CONTAINS its label ([`guarded_effect_label`]'s reading),
                        // so a body incurring raw `L` — `head`'s raise under the
                        // declared `Error[EmptyStream] :- isEmpty(s)` — is within
                        // the declaration. The guard is a CALL-SITE discharge
                        // device (WI-067), not a body-side obligation — the
                        // author's asserted claim, exactly as for the body-less
                        // partial primitive `div`.
                        //
                        // WI-20260830-APWM3 LEFT THAT SECOND LEG FIRING NOWHERE, and it
                        // is kept deliberately rather than by oversight. `guarded` is
                        // row-shaped, so [`explode_declared_effect_row`] now flattens a
                        // top-level `L :- g` to `L` via `decompose_effect_row`'s guarded
                        // arm — which states the SAME conservative-presence rule — and
                        // the direct compare above answers first. MEASURED across the
                        // whole suite: 19 312 firings with the flattening backed out
                        // (`Stream.head`, `Stream.tail`, `List.head` — the WI-818
                        // primitives themselves), 0 with it in. What is left to it is the
                        // atom the explode DECLINES: `decompose_effect_row` returns
                        // `None` on a row whose own present/absent sets clash
                        // ([`row_self_contradiction`]), and the un-flattened atom then
                        // reaches here whole. A single written element cannot be that
                        // row — an `effects {a, b}` group loads as SEPARATE atoms, so a
                        // guarded one decomposes alone and never clashes — but a
                        // PROJECTED row carrying `{L :- g, -L}` from a carrier binding
                        // can be, and that shape was not constructible to drive here.
                        // So this is a narrow, measured, un-driven guard, and the
                        // asymmetry decides it: keeping it costs one qualified-name
                        // compare on a path already failing, and dropping it would
                        // refuse `Stream.head` outright if any decline path exists that
                        // this reading missed.
                        let declared = declared_canon.iter().any(|d| {
                            views_structurally_equal(kb, &comp_canon, d)
                                || guarded_effect_label(kb, d).is_some_and(|lbl| {
                                    views_structurally_equal(kb, &comp_canon, &lbl)
                                })
                        });
                        if !declared {
                            // WI-20260825-CBRSW: a DENIED effect first. The verdict is
                            // [`label_violates_absence`], so the closure holds here too
                            // — a body minting `Permission[GptModel]` under a declared
                            // `-Permission[Model]` names the denial it broke rather than
                            // a label the row never mentioned.
                            // The op's OWN rigidify subst, not an empty one — the same
                            // one every neighbouring comparison in this block uses.
                            // `walk_type_deep_value` does not rewrite inside occurrence
                            // carriers (the WI-441 note above), so a `Value::Node`-carried
                            // label still holds its Global var here; resolving through
                            // the rigidify is what maps it to the Rigid the declared atom
                            // became. With an empty subst that pair silently degraded to
                            // the generic "undeclared effect" wording — the failure this
                            // branch exists to avoid. (Found by review.)
                            let denied = declared_absent
                                .iter()
                                .find(|a| label_violates_absence(kb, &canon_subst, &comp_canon, a));
                            let actual = match denied {
                                Some(a) => format!(
                                    "denied effect: {} — the row DECLARES `-{}`, so this \
                                     is not a missing declaration but a violated one; \
                                     the body must not perform it",
                                    type_display_name_value(kb, &comp_canon),
                                    type_display_name_value(kb, a),
                                ),
                                None => format!(
                                    "undeclared effect: {}",
                                    type_display_name_value(kb, &comp_canon)
                                ),
                            };
                            errors.push(TypeError::Other {
                                site: TypeError::here(),
                                span: op.span,
                                context: TypeErrorContext::OperationEffects { op_name: op.op_sym },
                                expected: format!("declared: [{}]", declared_display.join(", ")),
                                actual,
                            });
                        }
                    }
                }

                // Collect exhaustiveness diagnostics from the typing env
                for diag in &result.env.diagnostics {
                    errors.push(TypeError::Other {
                        site: TypeError::here(),
                        span: op.span,
                        context: TypeErrorContext::OperationMatch { op_name: op.op_sym },
                        expected: "exhaustive".to_string(),
                        actual: diag.clone(),
                    });
                }
            }
            Err(err) => {
                // Body failed to type — surface the structured error
                // instead of silently dropping it. Flatten an aggregation
                // node into its leaves so each sibling failure shows up
                // as its own load error.
                for e in err.flatten() {
                    errors.push(e);
                }
            }
        }
        // WI-20260830-JM7A8 — DRAIN, on both arms. A body whose call carried an
        // unsatisfied precondition typed fine otherwise and lands in `Ok`; one that ALSO
        // failed for an unrelated reason lands in `Err` and still owes this diagnostic,
        // so the drain sits after the match rather than inside either arm. `sources` is
        // tagged lazily by COUNT at the top of the next iteration, so a splice inside
        // this op's own range is attributed to this op's file exactly as a push is.
        let deferred = env.take_deferred_preconditions();
        if !deferred.is_empty() {
            errors.splice(op_err_mark..op_err_mark, deferred);
        }
    }
    // WI-745: flush the last op's errors and restore the `sources`/`errors`
    // parallel invariant for the next pass.
    while sources.len() < errors.len() {
        sources.push(cur_src);
    }
}

/// Collect which entity constructors a pattern covers.
///
/// WI-511 (WI-348): reads the `Pattern` occurrence DIRECTLY — its constructor
/// name is already a `Symbol`, so there is no `pattern_to_term` lowering and no
/// `Ref`/`Fn` carrier to disambiguate. Carrier-agnostic by construction, and
/// immune to the 0-ary-constructor storage representation.
pub(super) fn collect_covered_entities(
    kb: &KnowledgeBase,
    pattern: &NodeOccurrence,
    scrutinee_ctors: &[Symbol],
    covered: &mut Vec<Symbol>,
    has_wildcard: &mut bool,
) {
    let NodeKind::Pattern { pattern: pat, .. } = &pattern.kind else {
        return;
    };
    match pat {
        Pattern::Wildcard => {
            *has_wildcard = true;
        }
        Pattern::Var { name, .. } => {
            // A var pattern is either a nullary constructor (`case red`) or a
            // binding (`case x`) — resolved by the shared `pattern_var_ctor_sym`
            // (also used to build the match-arm Γ pattern fact, so the two never
            // disagree on what is a nullary ctor). A name matching no constructor
            // is a catch-all binding.
            match var_pattern_ctor(kb, pattern, *name, scrutinee_ctors) {
                Some(ctor) => covered.push(ctor),
                None => *has_wildcard = true,
            }
        }
        // WI-672: resolve the constructor name to the scrutinee's ctor (by short name)
        // so `covered` holds resolved symbols the exhaustiveness check compares canonically
        // — a bare `some` would otherwise read as uncovered under `same_sort_canonical`.
        Pattern::Constructor { name, .. } => {
            covered.push(resolve_pattern_ctor(kb, *name, scrutinee_ctors).unwrap_or(*name));
        }
        // Literals don't cover enum entities.
        Pattern::Literal { .. } => {}
        // A tuple pattern matches a tuple, not an enum constructor — conservative
        // (mirrors the old term-reader's unknown-form fallthrough).
        Pattern::Tuple { .. } => {
            *has_wildcard = true;
        }
    }
}

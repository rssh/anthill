//! `check_operation_bodies` — typing every operation body.

use super::*;

/// What one call of [`check_operation_bodies`] types.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum OpBodyPass {
    /// The whole operation: its contract's comparisons, its parameters' defaults, its body.
    Full,
    /// Its contract's comparisons alone ([`type_contract_comparisons`]) — the typed conjuncts
    /// a rule body's call of it is refuted with, which a typer run types ahead of its rule
    /// sweep and then again with the body (WI-20261117-8J8NG).
    ContractsOnly,
}

/// WI-20261117-8J8NG — THE BODIES A TYPER RUN TYPES, while it types them: the operation bodies
/// and the constant values it has not begun, those it has begun, and those that came out typed;
/// and whether a proof that reaches one it has not begun types it there ([`body_readiness`]).
///
/// A proof run while a body is typed — a guard refuted, a precondition proved — evaluates the
/// operations and constants it calls, and so does the refutation of a rule-body call's
/// precondition in the rule sweep. An operation of the same load whose body the run had not
/// reached yet was evaluated as loaded, its dots undispatched: MEASURED, `operation big(n:
/// Int64) -> Bool = n.gt(3)` written after `operation caller() -> Int64 = g(1)`, where `g`
/// declares `effects { Boom :- big(n) }`, aborted the load ("unhandled Expr variant in eval"),
/// and loaded clean written before it. So the run types such a body where the proof reaches it,
/// as it would at its turn, and passes over it at its turn.
#[derive(Debug)]
pub(crate) struct BodiesInRun {
    /// The run's operations and constants whose typing has not begun.
    pending: HashSet<Symbol>,
    /// The value of each of the run's constants, for one typed where a proof reaches it.
    constants: HashMap<Symbol, ConstantValue>,
    /// Every one whose typing has begun in this run.
    begun: HashSet<Symbol>,
    /// Every one that came out typed: its stored text is the one that runs. Begun and not
    /// typed is one being typed now, or one whose typing failed.
    typed: HashSet<Symbol>,
    /// Off while the run types its contracts ahead of its rules (`type_contracts_ahead`), a
    /// pass whose reports are dropped: a body it reaches is not typed yet.
    on_demand: bool,
    region_sorts: HashSet<Symbol>,
    /// What typing a body on demand reported, each error with its file, for the run.
    reported: Vec<(TypeError, Option<crate::span::SourceId>)>,
}

impl BodiesInRun {
    pub(super) fn new(
        ops: impl IntoIterator<Item = Symbol>,
        constants: &[ConstantValue],
        region_sorts: HashSet<Symbol>,
    ) -> Self {
        BodiesInRun {
            pending: ops
                .into_iter()
                .chain(constants.iter().map(|c| c.symbol))
                .collect(),
            constants: constants.iter().map(|c| (c.symbol, c.clone())).collect(),
            begun: HashSet::new(),
            typed: HashSet::new(),
            on_demand: false,
            region_sorts,
            reported: Vec::new(),
        }
    }

    /// From the rule sweep on, a proof that reaches a body the run has not begun types it.
    pub(super) fn type_on_demand(&mut self) {
        self.on_demand = true;
    }

    /// What typing bodies on demand reported.
    pub(super) fn into_reported(self) -> Vec<(TypeError, Option<crate::span::SourceId>)> {
        self.reported
    }
}

/// Whether a body may be run where it is reached ([`body_readiness`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BodyReadiness {
    Ready,
    /// The typer run has not typed it: it is being typed now, its typing failed, or it is
    /// reached where nothing may be typed ([`crate::eval::EvalError::BodyNotTyped`]).
    NotTyped,
}

/// Is the stored text of `sym` — an operation's body, a constant's value — the one that runs?
/// Outside a typer run, and for one the run does not type or has typed, yes. Asks; types
/// nothing ([`body_readiness`] does).
pub(crate) fn body_is_typed(kb: &KnowledgeBase, sym: Symbol) -> bool {
    match kb.bodies_in_run.as_ref() {
        None => true,
        Some(run) => run.typed.contains(&sym) || !(run.begun.contains(&sym) || run.pending.contains(&sym)),
    }
}

/// WI-20261117-8J8NG — MAY THE STORED TEXT OF `sym` BE RUN WHERE THE EVALUATOR REACHES IT? Yes
/// where [`body_is_typed`] says so, and for an operation with no body of its own, which the
/// evaluator runs nothing of. One the run has not begun is typed here first, as at the top of
/// the run — no proof or guard around it, so its own are made as at its turn — and may then be
/// run if it came out typed. Not where nothing may be typed: in the contracts pass ahead of the
/// rules, and under an applied layer, whose discard would take the typed text back while the
/// run held it typed.
///
/// TWO THINGS ARE NOT AS AT ITS TURN, each by choice. (1) One reached from a proof of the rule
/// sweep — the refutation of a rule-body call's precondition — is typed before the sweep has
/// elaborated the load's rules, so a proof of its own that runs a rule of this load may be
/// undecided where at its turn it would not; its citations wait for the sweep
/// ([`settle_pending_citation_routes`]). Answering such a body "not typed" instead would leave
/// the precondition unrefuted, a definite violation loading clean; typed early, it is what every
/// body was before the rules came first. (2) The eval↔SLD crossings it is reached through still
/// count (`resolve::BRIDGE_REENTRY_CAP`): that cap bounds the native stack, which typing it here
/// adds to, so its own proofs may reach the cap sooner and be undecided.
pub(crate) fn body_readiness(kb: &mut KnowledgeBase, sym: Symbol) -> BodyReadiness {
    if body_is_typed(kb, sym) {
        return BodyReadiness::Ready;
    }
    let layered = kb.terms.is_pinned();
    let run = kb.bodies_in_run.as_mut().expect("a body not typed is one of a run");
    let constant = run.constants.get(&sym).cloned();
    if constant.is_none() && kb.op_body_node(sym).is_none() {
        return BodyReadiness::Ready;
    }
    let run = kb.bodies_in_run.as_mut().expect("a body not typed is one of a run");
    if !run.pending.contains(&sym) || !run.on_demand || layered {
        return BodyReadiness::NotTyped;
    }
    let region_sorts = run.region_sorts.clone();
    let around = (
        std::mem::take(&mut kb.gamma_proof_depth),
        std::mem::take(&mut kb.simp_guard_depth),
        std::mem::take(&mut kb.spec_as_providers_depth),
    );
    let (mut errors, mut sources) = (Vec::new(), Vec::new());
    match &constant {
        Some(value) => check_constant_bodies(kb, std::slice::from_ref(value), &mut errors, &mut sources),
        None => check_operation_bodies(kb, OpBodyPass::Full, &[sym], &mut errors, &mut sources, &region_sorts),
    }
    (kb.gamma_proof_depth, kb.simp_guard_depth, kb.spec_as_providers_depth) = around;
    debug_assert_eq!(errors.len(), sources.len(), "a typing pass keeps `sources` parallel to `errors`");
    let run = kb
        .bodies_in_run
        .as_mut()
        .expect("typing a body leaves the run's record in place");
    // One the pass found nothing of its own to type in is not asked again.
    run.pending.remove(&sym);
    run.reported.extend(errors.into_iter().zip(sources));
    if run.typed.contains(&sym) {
        BodyReadiness::Ready
    } else {
        BodyReadiness::NotTyped
    }
}

/// Begin typing `sym`'s text in a typing pass: `false` where the run has begun it already —
/// typed on demand before its turn.
pub(super) fn begin_typing_body(kb: &mut KnowledgeBase, sym: Symbol) -> bool {
    let Some(run) = kb.bodies_in_run.as_mut() else {
        return true;
    };
    if !run.begun.insert(sym) {
        return false;
    }
    run.pending.remove(&sym);
    true
}

/// `sym`'s text came out typed: what is stored is what runs.
pub(super) fn typed_body(kb: &mut KnowledgeBase, sym: Symbol) {
    if let Some(run) = kb.bodies_in_run.as_mut() {
        run.typed.insert(sym);
    }
}

/// Check operation bodies against their declared return types.
pub(super) fn check_operation_bodies(
    kb: &mut KnowledgeBase,
    pass: OpBodyPass,
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
        /// `None` for a body-less operation, which is checked only for the defaults its
        /// parameters declare (proposal 069 §1.1).
        body_node: Option<Rc<NodeOccurrence>>,
        /// Where the operation's checked text is — its body, else its first default, else
        /// its declaration — and the declaration it sits in: the span and owner the
        /// signature's slot fills read.
        site: (crate::span::SourceSpan, Option<Symbol>),
        /// A body-less operation with no default, checked for its contract and its guards
        /// alone (WI-20261109-5VM2G).
        contract_only: bool,
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
        // Body-less ops (specs, host operations) have no body to type-check, but a default
        // their parameters declare is typed here as a body is (proposal 069 §3), and so are
        // the comparisons of their contract and their guards (§5.4, WI-20261109-5VM2G): a
        // host operation's guard was never typed, and `BigInt.div`'s compared its `BigInt`
        // divisor with the `Int64` literal `0`. Such an op is typed at its declaration.
        let body_node = rec.body_node;
        let (site, contract_only) = match (&body_node, kb.op_param_defaults(rec.op_sym).first())
        {
            (Some(body), _) => ((body.span, body.owner), false),
            (None, Some((_, default))) => ((default.span, default.owner), false),
            (None, None) => match kb
                .op_decl_sites
                .get(&rec.op_sym)
                .and_then(|sites| sites.first().copied())
            {
                Some(declared) if declares_contract_comparisons(kb, rec.op_sym) => {
                    ((declared, Some(rec.op_sym)), true)
                }
                // Nothing to type; or no declaration in this load phase (`op_decl_sites` is
                // the phase's): an earlier load's operation was typed by that load.
                _ => continue,
            },
        };
        // WI-392: while CHECKING this operation's body, its OWN declared type
        // parameters are universally quantified — Skolemize them to `Var::Rigid`
        // so the body may USE them but never CONSTRAIN them (a `Rigid` unifies
        // only with itself, so e.g. `add(h, 1)` on `h: Elem` is correctly
        // rejected; the body must type-check for ALL `Elem`). Inner calls keep
        // their own FLEXIBLE `Global` type params, which solve TO these rigids
        // (rigid ⇒ global; `resolved_var` matches only `Global`), and
        // `first_unconstrained_type_param` passes them unchanged (it flags only
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
        // carries the enclosing rigids through to an inner `Stream.find`'s
        // `[Elem, Eff]` and to the declared-effects check. The (vid → rigid) map
        // rides `OpInfo` onto the body env for a sibling call's placement at this
        // instance in `check_apply_iter` — after its arguments, where WI-424 seeded
        // before them (WI-20261001-80ZV8, `place_sibling_call_at_callers_instance`).
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
        // WI-1FKR2: a named variable that reaches a parameter type without being written in
        // the declaration — a slot an ALIAS's definition leaves open (`sort LT = List[T =
        // ?a]`), opened anew at each use — which §5.4 quantifies as it does the record's own
        // (the record lists the variables the declaration writes, WI-20260911-VNQTR).
        // Computed before `rec` is consumed below; empty for almost every operation.
        //
        // ONE AT THE TOP OF A PARAMETER'S TYPE IS READ BY ITS PATH (WI-20260911-VNQTR), as a
        // slot the signature leaves out is ([`UnwrittenFill::Projection`]): `y: LT` is checked
        // as `y: List[T = y.T]`, and every other place the variable stands takes the same
        // projection, so a tie the alias writes stays one (`Pair[A = ?a, B = ?a]` is `Pair[A =
        // p.A, B = p.A]`). Opened to a rigid of its own, no clause could name it: the
        // refusal of its forward advised writing a variable the alias does not take, and
        // `requires TypeValue[T = y.T]` did not cover it (MEASURED). One that stands only
        // inside an argument has no path, and keeps its rigid.
        let alias_params = alias_opened_type_params(
            kb,
            rec.op_sym,
            &rec.params,
            &rec.type_params,
            &parent_sort_params,
        );
        let mut by_path: Vec<(VarId, Value)> = Vec::new();
        let mut alias_rigid_params: Vec<(Symbol, Var)> = Vec::new();
        for (name, var) in alias_params {
            let at_path = match var {
                Var::Global(vid) => top_level_slot_path(kb, &rec.params, vid, site.0),
                _ => None,
            };
            match (var, at_path) {
                (Var::Global(vid), Some(path)) => by_path.push((vid, path)),
                _ => alias_rigid_params.push((name, var)),
            }
        }
        // WI-1FKR2: the op's OWN half is its declared type parameters PLUS an alias's slots
        // that stand inside an argument — all per-call and caller-instantiated, so all sit
        // after the enclosing sort's prefix in `param_rigids` (see that field's doc: the sort
        // view means "THIS instance's params", which these are not). Joined HERE so the gate
        // below stays one test over the op's half and one over the sort's.
        let mut op_own_params = rec.type_params.clone();
        op_own_params.extend(alias_rigid_params);
        let (params, return_type, declared_effects) = if op_own_params.is_empty()
            && parent_sort_params.is_empty()
            && by_path.is_empty()
        {
                (rec.params, rec.return_type, rec.effects)
            } else {
                let mut all_params = op_own_params;
                // Read BEFORE the sort's half is appended — the split below is exactly here.
                let op_param_len = all_params.len();
                // WI-849: the op table is `Var`-typed; the sort table is still TermId-typed
                // (its other consumers want the param as a TERM, under `&KnowledgeBase`
                // where they could not re-alloc).
                all_params.extend(param_pairs_as_vars(kb, &parent_sort_params));
                let mut rigidify = rigidify_op_type_params(kb, &all_params);
                for (vid, path) in &by_path {
                    rigidify.bind_value(kb, *vid, path.clone());
                }
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
                    UnwrittenFill::Projection(ValuePath::var(*n)),
                    t,
                    SlotPosition::Body,
                    site.0,
                    site.1,
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
            site,
            contract_only,
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
    // (`all_provisions`, which `region_sorts` filters down to the `Modifiable` claims).
    // That is `sorts × provisions` — a term that grows with BOTH factors, in a
    // pass whose own comment said it was computed once. MEASURED (release, stdlib + an
    // empty namespace, medians of 15 interleaved runs, both arms in one binary): the
    // `type_check_sorts` mark is 18.61 ms with the per-call walk and 16.09 ms with this
    // hoist, and its growth when WI-20260919-HXGXF's gate is forced open falls from
    // +3.37 ms to +1.70 ms. Per-call counters: `all_provisions` goes from 204 calls to 1.
    // Hoisted to the caller, which computes it before the loop, exactly as this comment
    // always claimed; `region_sorts`' own COST note says so (and, since WI-20260823-TR8CF,
    // reads one provider-index bucket per modifiable sort rather than the relation).
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
    let (simp_enabled, simp_rids) = simp_gate(kb);

    // WI-745: the file whose occurrences the CURRENT op's errors come from. Tag
    // lazily — errors pushed during op K are stamped at the top of iteration K+1
    // (and the final flush), which is robust to the loop's early `continue`s.
    let mut cur_src: Option<crate::span::SourceId> = None;
    // WI-20261117-8J8NG: the citations the current operation writes are queued from
    // `citations`; they are routed once it is typed ([`route_citations_from`]).
    let mut citations: Option<usize> = None;
    for op in &ops_to_check {
        if let Some(mark) = citations.take() {
            route_citations_from(kb, mark);
        }
        // A body the run typed on demand before its turn is passed over at it; the contracts
        // pass begins nothing.
        if pass == OpBodyPass::Full && !begin_typing_body(kb, op.op_sym) {
            continue;
        }
        if pass == OpBodyPass::Full {
            citations = Some(kb.pending_citation_routes.len());
        }
        if op.body_node.is_some() && pass == OpBodyPass::Full {
            count_body_typed(BodyKind::Operation);
        }
        while sources.len() < errors.len() {
            sources.push(cur_src);
        }
        cur_src = Some(op.site.0.source);
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
        env.set_param_rigids(
            Rc::clone(&op.param_rigids),
            op.sort_rigid_len,
            Rc::clone(&op.rigidify),
        );
        // The environment before any parameter is bound: a parameter default is typed in
        // it with the parameters declared before it alone (proposal 069 §3).
        let base_env = env.clone();
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
                            Receivers::Own(Some(&env)),
                            None,
                            &TypeErrorContext::OperationArgument {
                                op_name: op.op_sym,
                                param: *name,
                            },
                            op.span,
                        ) {
                            // WI-20261001-80ZV8 — WHAT THE PROJECTION READ IS A PARAMETER'S
                            // TYPE, so a slot it leaves open is the CALLER's to fix and
                            // unknown here: the fill a written parameter type got when this
                            // operation was collected ([`rigidify_unwritten_sort_params`],
                            // `o.V`), which never saw this type — it saw `s.T`. Left as
                            // read, `pick(s: Self, o: s.T) = takes_int(o)` loaded at `T =
                            // Other` and at `T = Other[W = ?]` alike, and `Sp.pick(x,
                            // other(w: "s"))` then ran `takes_int` on a `String` one
                            // (MEASURED, found by /code-review; the bare binding's half
                            // predates this ticket).
                            let elim = rigidify_unwritten_sort_params(
                                kb,
                                UnwrittenFill::Projection(ValuePath::var(*name)),
                                &elim,
                                SlotPosition::Body,
                                op.site.0,
                                op.site.1,
                            )
                            .unwrap_or(elim);
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
                        Receivers::Own(Some(&env)),
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
        // -> m.Self = m`, `m.Self` = the whole type of `m`; also a member form `m.T`) —
        // is eliminated against the op's own parameter types BEFORE the conformance and
        // escape checks. Then the body (`= m`, type `MappedStream`) conforms to the
        // projected type, and the WI-401 avoidance gate sees the input-rooted concrete
        // type (`m.Self` ⟹ `MappedStream`, same sort as the body ⟹ admitted) rather
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
                Receivers::Own(Some(&env)),
                None,
                &TypeErrorContext::OperationReturn {
                    op_name: op.op_sym,
                    surface: None,
                },
                op.span,
            ) {
                Ok(elim) => elim,
                // The projection is un-dischargeable: the receiver is not a
                // parameter (`-> result.Self`) or names a member the receiver's
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

        type_contract_comparisons(kb, &env, op.op_sym, &effective_return, op.site.0, errors);
        if op.contract_only || pass == OpBodyPass::ContractsOnly {
            // A precondition a call in the contract failed is drained here, as a body's is
            // below.
            errors.extend(env.take_deferred_preconditions());
            continue;
        }

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
                    Receivers::Own(Some(&env)),
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
        // Each call in the body, and in a parameter default, is held to the row's guarded
        // elements where it incurs their label (§5.5).
        let guarded_row =
            GuardedRow::of(kb, op.op_sym, &op.rigidify, &effective_effects).map(Rc::new);
        env.hold_to_guarded_row(guarded_row.clone());

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
        // Proposal 050.1 §1.2: the separations it requires are hypotheses of its body's
        // memory record, answered in either spelling.
        env.assume_required_separations(kb, &op.requires);
        // WI-20260830-JM7A8: where THIS op's errors start, so the preconditions its body
        // deferred can be spliced back in AHEAD of the op-boundary verdicts below rather
        // than trailing them. A precondition names a CALL and carries that call's span;
        // the return/effect errors are the operation's own. Reading them in that order is
        // what the single-diagnostic output looked like before this ticket, with the
        // second verdict added rather than the first moved.
        let op_err_mark = errors.len();
        // Proposal 069 §3 — each parameter default, typed as the argument a call that leaves
        // the parameter out is given: in the body's environment holding only the parameters
        // declared before it, against the parameter's type, its effects held to the
        // operation's declared row. Each call that takes it types it again where the call
        // is (`complete_defaulted_arguments`); this is the declaration's own verdict, so an
        // operation no call reaches is held to it too.
        let defaults = kb.op_param_defaults(op.op_sym).to_vec();
        for (param, default) in &defaults {
            let Some(at) = op.params.iter().position(|(n, _)| n == param) else {
                errors.push(TypeError::Other {
                    site: TypeError::here(),
                    span: Some(default.span.span),
                    context: TypeErrorContext::OperationArgument {
                        op_name: op.op_sym,
                        param: *param,
                    },
                    expected: "a default filed under one of the operation's parameters".into(),
                    actual: "a default whose parameter the signature does not list — an \
                             internal error"
                        .into(),
                });
                continue;
            };
            // A parameter the signature reads — an effect over it (`Modify[c]`), a
            // projection off it (`b.V`), a value in a type (`Vector[Int64, n]`) — is read off
            // the argument a call gives it while the call's inference runs, and a default is
            // taken after: refused here rather than met at each call as a type that names
            // nothing.
            let unwritten = kb.intern_unique("$left-out");
            let rename: HashMap<Symbol, Symbol> = HashMap::from([(*param, unwritten)]);
            let read_by = op
                .params
                .iter()
                .filter(|(n, _)| n != param)
                .map(|(_, t)| t)
                .chain(std::iter::once(&op.return_type))
                .chain(op.declared_effects.iter())
                .cloned()
                .collect::<Vec<Value>>()
                .into_iter()
                .any(|v| {
                    let renamed = substitute_ref_syms_value(kb, &v, &rename);
                    !views_structurally_equal(kb, &renamed, &v)
                });
            if read_by {
                let name = short_name_of(kb.local_name_of(*param)).to_owned();
                errors.push(TypeError::Other {
                    site: TypeError::here(),
                    span: Some(default.span.span),
                    context: TypeErrorContext::OperationArgument {
                        op_name: op.op_sym,
                        param: *param,
                    },
                    expected: format!(
                        "a default for a parameter the signature does not read; `{name}` is \
                         read by it (an effect over `{name}`, a projection off it, a value in \
                         a type)"
                    ),
                    actual: format!(
                        "a default for `{name}`: a call reads the parameter off the argument it \
                         gives while its inference runs, and takes a default after"
                    ),
                });
                continue;
            }
            let mut default_env = base_env.clone();
            default_env.hold_to_guarded_row(guarded_row.clone());
            for (name, ty) in &op.params[..at] {
                default_env.bind_var(*name, env.lookup_var(*name).unwrap_or_else(|| ty.clone()));
            }
            let declared = env
                .lookup_var(*param)
                .unwrap_or_else(|| op.params[at].1.clone());
            let context = TypeErrorContext::OperationArgument {
                op_name: op.op_sym,
                param: *param,
            };
            match type_check_node_gated_in_gamma(
                kb,
                &default_env,
                default,
                Some(declared.clone()),
                simp_enabled,
                &simp_rids,
                gamma0.clone(),
            ) {
                Ok(result) => {
                    let mut subst = Substitution::new();
                    if let ArgValidation::Fail(err) = validate_arg_against_param(
                        kb,
                        &mut subst,
                        &result.ty,
                        &declared,
                        Some(default.span.span),
                        context.clone(),
                        Some(&result.node),
                    ) {
                        errors.push(err);
                    }
                    // A default is evaluated as a body is, in the parameters before it.
                    errors.extend(unbacked_value_reads(kb, op.op_sym, &result.node, &result.env));
                    let in_scope: Vec<Symbol> = op.params[..at].iter().map(|(n, _)| *n).collect();
                    if let Some((var, span)) = unbound_value_variable(
                        kb,
                        &result.node,
                        &in_scope,
                        result.env.param_rigids(),
                    ) {
                        errors.push(TypeError::UnboundVariableRead {
                            span: Some(span),
                            var,
                            owner: op.op_sym,
                            param: Some(*param),
                        });
                    }
                    // At the operation's boundary, as its body's: what the default makes
                    // fresh is the parameter's value, which escapes only where the
                    // operation returns it.
                    let incurred = crate::kb::region::op_boundary_effects(
                        kb,
                        &result.env,
                        &op.return_type,
                        op.op_sym,
                        region_sorts,
                        &result.effects,
                    );
                    let name = short_name_of(kb.local_name_of(*param)).to_owned();
                    for (expected, actual) in
                        undeclared_effects(kb, &op.rigidify, &effective_effects, &incurred)
                    {
                        errors.push(TypeError::Other {
                            site: TypeError::here(),
                            span: Some(default.span.span),
                            context: context.clone(),
                            expected,
                            actual: format!("{actual}, incurred by the default of `{name}`"),
                        });
                    }
                }
                Err(err) => errors.extend(err.flatten()),
            }
        }
        let Some(body_node) = op.body_node.as_ref() else {
            let deferred = env.take_deferred_preconditions();
            if !deferred.is_empty() {
                errors.splice(op_err_mark..op_err_mark, deferred);
            }
            continue;
        };
        match type_check_node_gated_in_gamma(
            kb,
            &env,
            body_node,
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
                if !Rc::ptr_eq(&result.node, body_node) {
                    kb.set_op_body_node(op.op_sym, Rc::clone(&result.node));
                }
                // WI-20261117-8J8NG: the stored body is the typed one, and may be run.
                if pass == OpBodyPass::Full {
                    typed_body(kb, op.op_sym);
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
                // WI-20261020-VQPRP — a variable read as a value that nothing binds, on the
                // stored tree for the same reason ([`unbound_value_variable`]).
                let in_scope: Vec<Symbol> = op.params.iter().map(|(n, _)| *n).collect();
                if let Some((var, span)) =
                    unbound_value_variable(kb, &result.node, &in_scope, result.env.param_rigids())
                {
                    errors.push(TypeError::UnboundVariableRead {
                        span: Some(span),
                        var,
                        owner: op.op_sym,
                        param: None,
                    });
                }
                // TWO PARAMETERS OF ONE CARRIER, A READ THAT NAMES NEITHER: refused, on the
                // stored tree, once per body ([`contested_slot_read`]).
                // Only a frame that holds a contested slot can have such a read.
                let contested_frame = op_requires_chain_rc(kb, op.op_sym).iter().any(|e| {
                    matches!(
                        e.supply,
                        SupplySource::FromParam {
                            contested: Some(_),
                            ..
                        }
                    )
                });
                let read = contested_frame
                    .then(|| contested_slot_read(&result.node))
                    .flatten();
                if let Some((call, slot)) = read {
                    if let SupplySource::FromParam {
                        param,
                        binder,
                        contested: Some(other),
                    } = slot.supply
                    {
                        errors.push(TypeError::Other {
                            site: TypeError::here(),
                            span: Some(call.span.span),
                            context: TypeErrorContext::OperationArgument {
                                op_name: op.op_sym,
                                param,
                            },
                            expected: format!(
                                "one slot of the frame answering a read of `{}`",
                                kb.qualified_name_of(slot.required_sort)
                            ),
                            actual: contested_account(kb, param, binder, other),
                        });
                    }
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
                errors.extend(unbacked_value_reads(kb, op.op_sym, &result.node, &result.env));
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
                // (`hint_instantiation_into`), applied here because this σ is READ two
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
                // WI-20261001-80ZV8 — AND THE DECLARED SIDE'S HOLES FROM THE BODY. A
                // variable still open in the declared return is one the SIGNATURE binds
                // nowhere — the operation's and the sort's type parameters are rigids here
                // — so it is the return's own `?`: a type the operation PICKS (opened at
                // each call, WI-1063/1078), and the body is where it is picked. The unify
                // above already bound it; the relation below is structural about a
                // variable and never read that binding, so `some(s: Self) -> Car[V = ?] =
                // car(v: "s")` was refused, `expected Car[V = ?_], got Car[V = String]`
                // (MEASURED) — and that is what a bare `-> Car` inside `Car` is too, the
                // loader writing its `?` (proposal 070 §1.3) — where the unwritten `->
                // Other` it stands beside always packed. The message keeps the return AS
                // DECLARED.
                let declared = walk_type_deep_value(kb, &subst, &effective_return);
                let conforms = types_compatible(kb, &mut subst, &body_ty, &declared)
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
                    //
                    // WI-20260829-6RBPD: AT THE BODY'S VALUE, which it had no span for at
                    // all — `operation c() -> Int64 = "x"` named only `c`.
                    errors.push(conformance_error(
                        kb,
                        effective_return.clone(),
                        body_ty.clone(),
                        Some(result_position(body_node).span.span),
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

                // Proposal 073 §2 — a value of a known sort used at an abstract type is the
                // instance it is there: stamped once the body conforms, on the stored tree.
                if conforms {
                    errors.extend(stamp_instance_conversions(
                        kb,
                        &env,
                        TypeErrorContext::OperationReturn {
                            op_name: op.op_sym,
                            surface: None,
                        },
                        &result.node,
                        &effective_return,
                    ));
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
                // Proposal 050.1: a write charged to a pool — state outside the process no
                // row can name — cannot be declared, so it is refused here, once per name.
                //
                // WI-20260903-2VPHT: both are reported AT THE BODY, which is what performs
                // the effect, as an effect a parameter's default incurs is reported at the
                // default (above). `op.span` is the functor's span, the first TERM the
                // loader built with the operation's functor: an operation no clause writes
                // as a term has none, so the mismatch of `div` in `sort Money` and in `sort
                // Cash` carried no location, and nothing told the two apart.
                let body_span = Some(body_node.span.span);
                let mut pool_writes = result.env.take_pool_writes();
                pool_writes.dedup_by(|a, b| a.name == b.name && a.pool == b.pool);
                for write in &pool_writes {
                    errors.push(pool_write_refusal(kb, op.op_sym, body_span, write));
                }
                for (expected, actual) in undeclared_effects(
                    kb,
                    &op.rigidify,
                    &effective_effects,
                    &ext_effects,
                ) {
                    errors.push(TypeError::Other {
                        site: TypeError::here(),
                        span: body_span,
                        context: TypeErrorContext::OperationEffects { op_name: op.op_sym },
                        expected,
                        actual,
                    });
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
    if let Some(mark) = citations {
        route_citations_from(kb, mark);
    }
}

/// The effects of `incurred` that the operation's declared row (`effective_effects`, its
/// atoms with their receiver projections discharged) does not admit, each as the
/// `(expected, actual)` pair of its diagnostic. `rigidify` is the operation's type-parameter
/// rigidify substitution, which both sides are walked through. Read for the body and for
/// each parameter default, whose effects are the operation's (proposal 069 §3).
/// The comparisons a contract clause or an effect guard makes are calls of their carrier's
/// member, typed in the operation's signature: its parameters as the body binds them, `result`
/// at the return type (proposal 073 §5). Each `=`, `eq` and `neq` in a `requires` or `ensures`
/// clause or in a guard of the effects row is typed there, and one that does not type is
/// refused (`ensures eq(result, "a")` over an `Int64` result, `effects { Boom :- eq(c, 1) }`
/// over `c: Color`), naming `===` for a structural comparison. The conjunct is kept in the
/// operation's record as the typed occurrence, so a proof over it reads each comparison's
/// member (`proof_verify::contract_goal`, `typing::clause_goal`), and so is the swapped
/// comparison a refutation of it proves ([`negated_comparison_term`]).
///
/// A comparison is typed on a copy that writes each field projection the way an operation
/// body's lowering does (`synthesize_field_access`; the clause holds the term form,
/// `field_access(result, value)`), and the member it gets is put on the clause's own node: the
/// stored clause keeps the shape the proofs read.
fn type_contract_comparisons(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    op_sym: Symbol,
    ret: &Value,
    site: crate::span::SourceSpan,
    errors: &mut Vec<TypeError>,
) {
    // A KB with no `PartialEq` spec loaded has no member to type a comparison at, as a rule
    // body's `=` is not typed there either.
    let eq_functor = kb.eq_functor();
    if lookup_spec_op_dispatch(kb, eq_functor).is_none() {
        return;
    }
    let Some(sig) = kb.op_record(op_sym).and_then(|r| r.signature.clone()) else {
        return;
    };
    let mut cenv = env.clone();
    if let Some(result_sym) = crate::kb::region::resolve_op_result_sym(kb, op_sym) {
        cenv.bind_var(result_sym, ret.clone());
    }
    let mut conjuncts: Vec<(ContractPart, Value)> = Vec::new();
    for (part, clauses) in [(ContractPart::Requires, &sig.requires), (ContractPart::Ensures, &sig.ensures)] {
        for clause in clauses {
            if is_value_precondition_clause(kb, clause) {
                conjuncts.extend(clause_conjuncts(kb, clause).into_iter().map(|c| (part, c)));
            }
        }
    }
    for effect in &sig.effects {
        for (_, guard) in collect_guarded_atoms(kb, &Substitution::new(), effect) {
            let Some(guard) = guard_conjuncts(kb, &guard) else {
                continue;
            };
            conjuncts.extend(guard.into_iter().map(|c| (ContractPart::EffectGuard, c)));
        }
    }
    for (part, conj) in conjuncts {
        let mut refused = Vec::new();
        // An `ensures` is proved over the operation's parameters and has no call to be typed
        // at; a `requires` and a guard are decided at each call, typed at its arguments
        // (`CallSigma::clause_goal`).
        let proved_only = matches!(part, ContractPart::Ensures);
        type_conjunct_comparisons(kb, &cenv, op_sym, &conj, site, proved_only, &mut refused);
        errors.extend(refused.into_iter().map(|(comparison, cause)| match cause {
            // A field projection that names nothing is refused as its own error.
            Refusal::Projection(e) => e,
            Refusal::Comparison(e) | Refusal::Call(e) => TypeError::IllTypedComparison {
                span: e.span(kb),
                op: op_sym,
                part,
                comparison,
                cause: Box::new(e),
            },
        }));
        // The negation a refutation proves types with the conjunct; refused, it is the
        // conjunct's refusal, reported above. A `requires` is refuted at a rule-body call and
        // a guard at every call; an `ensures` is only proved.
        let refuted = matches!(part, ContractPart::Requires | ContractPart::EffectGuard);
        if let Some(negated) = negated_comparison_term(kb, &conj).filter(|_| refuted) {
            type_conjunct_comparisons(kb, &cenv, op_sym, &Value::term(negated), site, false, &mut Vec::new());
        }
    }
}

/// Does `op_sym` declare something [`type_contract_comparisons`] types: a value precondition
/// or postcondition, or a guarded effect? What brings a body-less operation with no default
/// into [`check_operation_bodies`].
pub(super) fn declares_contract_comparisons(kb: &mut KnowledgeBase, op_sym: Symbol) -> bool {
    let Some(sig) = kb.op_record(op_sym).and_then(|r| r.signature.clone()) else {
        return false;
    };
    sig.requires
        .iter()
        .chain(&sig.ensures)
        .any(|clause| is_value_precondition_clause(kb, clause))
        || sig
            .effects
            .iter()
            .any(|effect| !collect_guarded_atoms(kb, &Substitution::new(), effect).is_empty())
}

/// Why a contract comparison or a contract's goal of a spec member is refused
/// ([`type_conjunct_comparisons`]).
enum Refusal {
    /// A field projection in it names nothing.
    Projection(TypeError),
    /// The comparison does not type.
    Comparison(TypeError),
    /// The goal of a spec's member does not type: no provider at its type, or two.
    Call(TypeError),
}

/// Type each comparison of the contract conjunct `conj` ([`type_contract_comparisons`]), put the
/// member it gets on its node, and keep the typed conjunct beside the one loaded; each refused
/// comparison, as written, and why, into `refused`. `proved_only`: the conjunct is only proved
/// (an `ensures`), so a comparison left at a spec operation no requirement answers is refused.
fn type_conjunct_comparisons(
    kb: &mut KnowledgeBase,
    cenv: &TypingEnv,
    op_sym: Symbol,
    conj: &Value,
    site: crate::span::SourceSpan,
    proved_only: bool,
    refused: &mut Vec<(Value, Refusal)>,
) {
    let occ = crate::kb::node_occurrence::value_as_occurrence(kb, conj);
    // Each comparison, and each goal calling a body-less spec member (`Pred.ok(x)`, its twin
    // `Pred.ok(x, true)`, `Desc.describe(x, 3)`), the walk reaches through the goal's
    // connectives; a call inside a comparison's operand is the comparison's to type. A goal of a
    // spec operation with a default body (`isEmpty(xs)`, [`is_contract_default_goal`]) is typed
    // where it types, and left as it was where it does not: such goals were typed nowhere, and
    // one at a type nothing provides (`gt(x, 0)` over `x: T`) still loads (WI-347's rows).
    // (the call, a comparison, typed only where it types)
    let mut calls: Vec<(Rc<NodeOccurrence>, bool, bool)> = Vec::new();
    let mut stack = vec![Rc::clone(&occ)];
    while let Some(node) = stack.pop() {
        let Some(expr) = node.as_expr() else { continue };
        if let Some((functor, pos, named)) = expr_call_parts(expr) {
            if is_equality_comparison(kb, functor) {
                calls.push((Rc::clone(&node), true, false));
                continue;
            }
            if is_contract_member_goal(kb, functor, pos.len() + named.len()) {
                calls.push((Rc::clone(&node), false, false));
                continue;
            }
            if is_contract_default_goal(kb, functor, pos.len() + named.len()) {
                calls.push((Rc::clone(&node), false, true));
                continue;
            }
        }
        crate::kb::node_occurrence::for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    let mut kept = false;
    for (call, comparison, is_optional) in calls {
        let copy = match typable_comparison(kb, &call, site) {
            Ok(copy) => copy,
            Err(_) if is_optional => continue,
            Err(e) => {
                refused.push((Value::Node(Rc::clone(&call)), Refusal::Projection(e)));
                continue;
            }
        };
        match type_check_node(kb, cenv, &copy, None) {
            // A comparison an `ensures` makes at a type nothing the operation requires answers
            // — `eq(result, x)` over `x: B` under `requires Eq[T = A]` — does not type, as the
            // same comparison in the body does not. A `requires` or a guard is typed at each
            // call instead (`effects { Boom :- eq(c, d) }` over a spec's `c: T, d: T`).
            // A spec's own operation compares at its own parameter, as `req_insertion` reads it.
            Ok(_) if let Some(CallClass::UnresolvedSpecOp {
                spec_op_sym,
                spec_sort_sym,
                abstract_params,
                span,
                enclosing_sort,
            }) = copy.call_class().filter(|_| comparison && proved_only)
                && enclosing_sort != Some(spec_sort_sym) =>
            {
                let e = TypeError::MissingRequiresForSpecOp {
                    span,
                    spec_op_sym,
                    spec_sort_sym,
                    abstract_params,
                    site: RequiresSite::Operation {
                        op: op_sym,
                        sort: enclosing_sort.filter(|s| kb.has_kind(*s, crate::intern::SymbolKind::Sort)),
                    },
                };
                refused.push((Value::Node(Rc::clone(&call)), Refusal::Comparison(e)));
            }
            Ok(_) => {
                let written = call.as_expr().and_then(expr_call_parts).map(|(f, p, n)| (f, p.len() + n.len()));
                let class = copy
                    .call_class()
                    .filter(|class| written.is_some_and(|(f, arity)| goal_reads_member(kb, f, arity, class)));
                if let Some(class) = class {
                    call.set_classification(class);
                    kept = true;
                }
            }
            Err(_) if is_optional => {}
            Err(e) if comparison => refused.push((Value::Node(Rc::clone(&call)), Refusal::Comparison(e))),
            Err(e) => refused.push((Value::Node(Rc::clone(&call)), Refusal::Call(e))),
        }
    }
    // The conjunct as loaded is a term, which carries no member: its typed twin is kept
    // beside it, keyed by it. A conjunct carried on an occurrence (a denoted label) holds its
    // members on its own nodes.
    if let (true, Value::Term { id, .. }) = (kept, conj) {
        kb.record_typed_contract_conjunct(op_sym, *id, occ);
    }
}

/// A copy of the contract comparison `cmp` the typer reads as an operation body's: each field
/// projection in the clause's term form, `field_access(receiver, name)`, written as the body
/// lowering writes it, and every node at `site`, the operation's declaration, so a refusal
/// points there.
pub(super) fn typable_comparison(
    kb: &mut KnowledgeBase,
    cmp: &Rc<NodeOccurrence>,
    site: crate::span::SourceSpan,
) -> Result<Rc<NodeOccurrence>, TypeError> {
    let field_access = kb.try_resolve_symbol(dt::qualified(dt::FIELD_ACCESS));
    fn copy(
        kb: &mut KnowledgeBase,
        node: &Rc<NodeOccurrence>,
        site: crate::span::SourceSpan,
        field_access: Option<Symbol>,
    ) -> Result<Rc<NodeOccurrence>, TypeError> {
        let Some(expr) = node.as_expr() else {
            return Ok(Rc::clone(node));
        };
        let Some((functor, pos_args, named_args)) = expr_call_parts(expr) else {
            return Ok(NodeOccurrence::new_expr(expr.clone(), site, node.owner));
        };
        let pos: Vec<Rc<NodeOccurrence>> = pos_args
            .iter()
            .map(|a| copy(kb, a, site, field_access))
            .collect::<Result<_, _>>()?;
        if Some(functor) == field_access && pos.len() == 2 && named_args.is_empty() {
            let name = match pos[1].as_expr() {
                Some(Expr::Ident(n) | Expr::Ref(n)) => Some(kb.local_name_of(*n).to_string()),
                _ => None,
            };
            if let Some(name) = name {
                return match synthesize_field_access(kb, &pos[0], &name, node) {
                    Ok(fa) => Ok(fa),
                    Err(Some(e)) => Err(e),
                    Err(None) => Ok(Rc::clone(node)),
                };
            }
        }
        let named: Vec<(Symbol, Rc<NodeOccurrence>)> = named_args
            .iter()
            .map(|(k, a)| copy(kb, a, site, field_access).map(|c| (*k, c)))
            .collect::<Result<_, _>>()?;
        Ok(NodeOccurrence::new_expr(
            Expr::Apply {
                recv_type: None,
                functor,
                pos_args: pos,
                named_args: named,
                type_args: Vec::new(),
            },
            site,
            node.owner,
        ))
    }
    // A comparison or a member's goal written with its result column (`neq(x, 1, true)`,
    // `Pred.ok(x, true)`, the relational form a goal may take) is typed as the call of its
    // arguments before the column; the column is its `Bool`.
    let Some(Expr::Apply {
        functor, pos_args, named_args, ..
    }) = cmp.as_expr()
    else {
        return copy(kb, cmp, site, field_access);
    };
    let declared = kb
        .op_record(*functor)
        .and_then(|r| r.signature.as_ref())
        .map(|sig| sig.params.len());
    let result_column = if is_equality_comparison(kb, *functor) {
        pos_args.len() == 3
    } else {
        declared.is_some_and(|n| pos_args.len() == n + 1)
    };
    if result_column && named_args.is_empty() {
        let operands = NodeOccurrence::new_expr(
            Expr::Apply {
                recv_type: None,
                functor: *functor,
                pos_args: pos_args[..pos_args.len() - 1].to_vec(),
                named_args: Vec::new(),
                type_args: Vec::new(),
            },
            cmp.span,
            cmp.owner,
        );
        return copy(kb, &operands, site, field_access);
    }
    copy(kb, cmp, site, field_access)
}

/// WI-20260829-6RBPD — WHERE A BODY'S VALUE IS WRITTEN: the body, past the `let`s that lead
/// to it. A return mismatch is reported here, at the expression that disagrees: `let k = n +
/// 1` then `"tail"` is refused at `"tail"`, not at the `let`. A `let` is the one form whose
/// value is another sub-expression's; an `if` or a `match` checks each branch against the
/// declared return itself, so a mismatch that reaches the boundary through one is the
/// whole form's.
///
/// The body AS WRITTEN, not the typed tree: a `@[simp]` rule fired at the tail keeps its
/// right-hand side's span, which is the rule's file and not the body's, and the error is
/// stamped with the body's.
fn result_position(body: &Rc<NodeOccurrence>) -> &Rc<NodeOccurrence> {
    let mut node = body;
    while let Some(Expr::Let { body, .. }) = node.as_expr() {
        node = body;
    }
    node
}

fn undeclared_effects(
    kb: &mut KnowledgeBase,
    rigidify: &Substitution,
    effective_effects: &[Value],
    incurred: &[Value],
) -> Vec<(String, String)> {
    let mut out = Vec::new();
    let canon_subst = rigidify.clone();
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
    // AN ALIAS LABEL IS THE LABEL IT STANDS FOR, on both sides (`sort Fails =
    // Error[Foo]`): compared as written, a body applying a callback whose row says
    // `Fails` was refused against a declared `Error[Foo]` on every build ("undeclared
    // effect: Fails", MEASURED: review 9's fix pass). The display keeps the spelling.
    for e in effective_effects {
        match explode_declared_effect_row(kb, e) {
            Some((admitting, absent)) => {
                for a in &admitting {
                    declared_display.push(effect_atom_display(kb, a, atom_label_key));
                    let a = walk_type_deep_value(kb, &canon_subst, a);
                    declared_canon.push(dealiased(kb, &a));
                }
                for l in &absent {
                    declared_display
                        .push(format!("-{}", type_display_name_value(kb, l)));
                    declared_absent.push(walk_type_deep_value(kb, &canon_subst, l));
                }
            }
            None => {
                declared_display.push(effect_atom_display(kb, e, atom_label_key));
                let e = walk_type_deep_value(kb, &canon_subst, e);
                declared_canon.push(dealiased(kb, &e));
            }
        }
    }
    for effect in incurred {
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
            let comp_key = dealiased(kb, &comp_canon);
            // WI-818: a declared GUARDED atom `L :- g` conservatively
            // CONTAINS its label ([`guarded_effect_label`]'s reading),
            // so a body incurring raw `L` — `head`'s raise under the
            // declared `Error[EmptyStream] :- isEmpty(s)` — is within
            // the declaration here. Whether `L` is incurred only where
            // `g` holds is asked at each call, where Γ says what holds
            // ([`hold_call_to_guarded_row`]).
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
            // A row a `requires` clause leaves unwritten is the projection `P.E` the
            // signature writes for it (WI-20261103-JGW88).
            let written = declared_canon.iter().any(|d| {
                views_structurally_equal(kb, &comp_key, d)
                    || atom_is_projected_instance_member(kb, d, &comp_key)
                    || guarded_effect_label(kb, d).is_some_and(|lbl| {
                        views_structurally_equal(kb, &comp_key, &lbl)
                    })
            });
            if written {
                continue;
            }
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
            // Each absence read through its aliases as the labels above are; the
            // message keeps the spelling.
            let denied = declared_absent.iter().find(|a| {
                let a = dealiased(kb, a);
                label_violates_absence(kb, &canon_subst, &comp_key, &a)
            });
            // An `Error` label is declared where a boundary at a declared payload catches it
            // ([`error_label_admits`]): `Error[Wide]` admits a raise of `Narrow`, unless the
            // row denies it (`{Error, -Error[Wide]}`).
            let admitted = denied.is_none()
                && declared_canon
                    .iter()
                    .any(|d| error_label_admits(kb, &canon_subst, d, &comp_key));
            if !admitted {
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
                out.push((
                    format!("declared: [{}]", declared_display.join(", ")),
                    actual,
                ));
            }
        }
    }
    out
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
        // The pattern says which constructor it is: a case named without an import was
        // found among the scrutinee's own where the pattern was bound
        // (`position_constructor`), and the pattern read here is the one that returned.
        Pattern::Constructor { name, .. } => covered.push(*name),
        // Literals don't cover enum entities.
        Pattern::Literal { .. } => {}
        // A tuple pattern matches a tuple, not an enum constructor — conservative
        // (mirrors the old term-reader's unknown-form fallthrough).
        Pattern::Tuple { .. } => {
            *has_wildcard = true;
        }
    }
}

/// WI-20260919-N31XX (proposal 065, "The rule") — the refusals of a typed body or default's
/// value reads of a rigid ([`rigid_value_reads`]): the first read no `requires TypeValue[T =
/// B]` in scope backs, and the first structural bracket entry left open
/// ([`OpenStructuralEntry`]). A default is held to them as the body is (WI-20261020-VQPRP):
/// both are evaluated in the operation's frame.
fn unbacked_value_reads(
    kb: &mut KnowledgeBase,
    op_sym: Symbol,
    node: &Rc<NodeOccurrence>,
    env: &TypingEnv,
) -> Vec<TypeError> {
    let mut out = Vec::new();
    let (reads, open_entry) =
        rigid_value_reads(kb, node, env.enclosing_frame_chain(), env.param_rigids());
    if !reads.is_empty() {
        let backed = type_value_backed_params(kb, op_sym);
        if let Some((_, param, span)) = reads.into_iter().find(|(vid, _, _)| !backed.contains(vid)) {
            out.push(TypeError::TypeValueReadUnbacked {
                span,
                param,
                op: op_sym,
            });
        }
    }
    // A structural type written as a bracket's entry is one type, read when the body is
    // loaded: see [`OpenStructuralEntry`].
    if let Some(OpenStructuralEntry { entry, name }) = open_entry {
        let written = crate::persistence::print::TermPrinter::new(kb).print_occurrence(&entry);
        out.push(TypeError::Other {
            site: TypeError::here(),
            span: Some(entry.span.span),
            context: TypeErrorContext::OperationTypeParams { op_name: op_sym },
            expected: "a tuple type, an arrow type or an effect row that names no \
                       type parameter, no variable and no value, where it is \
                       written as a bracket's entry in a value position"
                .to_string(),
            actual: format!(
                "`{written}`, which names `{name}`: the entry is read as one type \
                 when the body is loaded, and nothing gives `{name}` a type there"
            ),
        });
    }
    out
}

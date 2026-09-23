//! Expected-type hints threaded into call arguments before they are typed (higher-order,
//! constructor-field, tuple and variant slots).

use super::*;

/// WI-275: the expected-type hint for a higher-order argument occurrence. Only a
/// lambda or a bare reference needs a top-down function type — to type a lambda's
/// parameter, or to eta-lift an operation name to a function value — so those, in
/// a function-typed parameter slot (`arrow` / `Function[A, B, E]`), get that type
/// as their hint; every other argument gets `None`, preserving the WI-379
/// args-before-expected synthesis order.
pub(super) fn hof_arg_hint(
    kb: &mut KnowledgeBase,
    arg: &Rc<NodeOccurrence>,
    param_type: Option<Value>,
) -> Option<Value> {
    let pt = param_type?;
    if is_hof_shaped(arg) && arrow_parts(kb, &pt).is_some() {
        Some(pt)
    } else {
        None
    }
}

/// WI-485: the type of an argument occurrence that is a plain variable / operation
/// REFERENCE, read straight from the typing env WITHOUT synthesizing it. The receiver
/// arg `xs` of `findX(xs, lambda …)` (or the dot-call `xs.findX(…)`) is a `VarRef` whose
/// `List[Int64]` type is already bound in `env`, so a sibling callback param's projection
/// (`pred: (x: s.T) -> …`) can be eliminated against it at HINT time.
pub(super) fn varref_arg_env_type(
    kb: &KnowledgeBase,
    env: &TypingEnv,
    arg: &Rc<NodeOccurrence>,
) -> Option<Value> {
    let name = leaf_var_ref(arg)?;
    // WI-723: a dot-call receiver reference already TYPED in an earlier frame
    // (`r.where(λ)` synthesizes `where(r, λ)` with `r` pre-typed + stamped) carries
    // its type on the node — but a RULE reference (a `Relation[T]` value, WI-714) is
    // not bound in the value env, so `lookup_var` misses it. Read the stamped
    // `inferred_type` as a fallback so the receiver's schema still eliminates a
    // sibling callback param's projection (`(c: r.T) -> Bool`) at hint time — the
    // same threading a let-local receiver gets for free through the env. Env first:
    // a still-flexible env binding is the live one; the stamp is only a fallback for
    // a reference the env doesn't carry.
    // WI-20260904-50B2K part (c), step 2 — NO SCHEMA THROUGH THE HINT CHANNEL. This is
    // the THIRD reader of `env.lookup_var`, and unlike the other two it computes a HINT
    // rather than a verdict: it has no walk to hand an obligation to and no `Result` to
    // refuse with. A ∀ pushed down as an `expected` would be a hint no consumer can read
    // — so it answers `None` here, which is the pre-(c) behaviour for a name the env
    // does not carry, and the real elimination happens at the reader that types the
    // reference. /code-review named this site with the two it drove.
    //
    // NO ROW HOLDS THIS, MEASURED: backing it out leaves all 27 rows of
    // `wi_50b2k_binder_inference_test` green, because this helper is only reached for a
    // DOT-CALL RECEIVER (`projection_receiver_type` is its sole caller) and a lambda has
    // no members to dot into. It is kept as the third reader of one channel being made
    // to agree with the other two, and is recorded as having no witness rather than
    // being credited with one.
    // THE FALLBACK IS FILTERED TOO, and the first cut filtered only the env hit — which
    // the fallback then defeated: `set_inferred_type` stamps the lambda's own type onto
    // its occurrence, so a `VarRef` to a let-bound generalized lambda reaches the SAME
    // schema through `inferred_type()`. A guard whose bypass is the next line of the
    // same expression is not a guard. /code-review found it.
    env.lookup_var(name)
        .or_else(|| arg.inferred_type())
        .filter(|t| !matches!(type_head(kb, t), TypeHead::PolyType))
}

/// WI-714: the `Relation[T]` type of an argument occurrence that is a bare RULE
/// reference (`join(r1, r2, …)`'s `r2`), computed directly from the rule's schema. A
/// rule reference is a `Relation` value (WI-714 C2/C3) but is never bound in the value
/// env, so [`varref_arg_env_type`] misses it — yet a sibling callback param may project
/// its schema (`cond: (c: r1.T, q: r2.T) -> Bool`), which must be eliminated at HINT time
/// so the two-row lambda's binder types at the concrete schema. Only fires for a
/// reference whose resolved symbol is a `Goal`/`Rule`; any other arg yields `None` (the
/// env/stamp path already covers a receiver and ordinary values).
///
/// WI-898: `EquationFunctor` is deliberately not in that set — it owns no clauses, so
/// there is no schema to project. `None` here is correct and not a silent skip: the
/// argument still gets typed on the ordinary path, where `check_bare_ref`'s own
/// `EquationFunctor` arm reports it.
///
/// WI-734 asked whether this recompute could be retired in favour of the `inferred_type`
/// stamp the RECEIVER path already uses, so a bare rule-ref argument and a bare rule-ref
/// receiver share one mechanism. IT CANNOT — and the reason is ORDERING, not oversight.
/// A/B-verified: dropping this rung from [`projection_receiver_type`] fails all five
/// `wi714_join` tests with `<unresolved receiver>.name` / `.who` / `.dept`.
///
/// The consumer is the row-lambda's callback param HINT. At the `DotApply` frame only the
/// RECEIVER is pre-typed (WI-443) — a callback argument is deliberately not — so when
/// `join(r1, lambda (c, q) -> …)` hints `q` with `r2`'s schema, `r2` has not been typed
/// yet and carries NO stamp to read. A stamp cannot satisfy a reader that runs before the
/// producer. Retiring this would require pre-typing sibling args at the DotApply frame,
/// which is the very thing WI-443 removed.
pub(super) fn relation_ref_arg_type(
    kb: &mut KnowledgeBase,
    arg: &Rc<NodeOccurrence>,
) -> Option<Value> {
    let name = leaf_var_ref(arg)?;
    if !kb.cites_a_relation(name) {
        return None;
    }
    relation_reference_type(kb, name, Some(arg.span.span), arg).ok()
}

/// WI-275: a lambda or a bare reference — the two argument shapes that need a top-down
/// function type (to type a lambda's parameter, or to eta-lift an operation name to a
/// function value). [`hof_arg_hint`] gives those, and only those, the declared param type.
///
/// WI-793 named it: the SAME predicate decides which arguments must never be staged
/// ahead of the hints, because a staged argument is visited before any hint exists and
/// these are exactly the arguments a hint is for.
pub(super) fn is_hof_shaped(arg: &Rc<NodeOccurrence>) -> bool {
    matches!(
        &arg.kind,
        NodeKind::Expr {
            expr: Expr::Lambda { .. } | Expr::VarRef { .. },
            ..
        }
    )
}

/// WI-793: the UNIFIED `pos_args ++ named_args` index of the argument bound to parameter
/// `psym` at declared position `param_pos` — positional by slot, named by LABEL (WI-426,
/// not symbol identity). One index space so a staged argument can be named once and
/// located in either channel. [`arg_at`] reads it back; [`param_sym_for_arg_index`] is
/// the inverse.
fn param_arg_index(
    kb: &KnowledgeBase,
    psym: Symbol,
    param_pos: usize,
    pos_len: usize,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Option<usize> {
    if param_pos < pos_len {
        return Some(param_pos);
    }
    named_args
        .iter()
        .position(|(n, _)| same_label(kb, *n, psym))
        .map(|k| pos_len + k)
}

/// WI-793: the argument at a unified [`param_arg_index`].
///
/// Written as an explicit branch rather than `pos_args.get(u).or_else(|| named_args.get(u
/// - pos_args.len()))`: that form is correct only because `or_else` is lazy, so the
/// subtraction's precondition lives in the evaluation order instead of in the code. Here
/// the `else` states it.
pub(super) fn arg_at<'a>(
    pos_args: &'a [Rc<NodeOccurrence>],
    named_args: &'a [(Symbol, Rc<NodeOccurrence>)],
    unified: usize,
) -> Option<&'a Rc<NodeOccurrence>> {
    if unified < pos_args.len() {
        pos_args.get(unified)
    } else {
        named_args.get(unified - pos_args.len()).map(|(_, a)| a)
    }
}

/// WI-793: the parameter symbol an argument at a unified index is bound to — the inverse
/// of [`param_arg_index`], used to key a staged argument's computed type back onto its
/// parameter.
pub(super) fn param_sym_for_arg_index(
    kb: &KnowledgeBase,
    ps: &[(Symbol, Value)],
    unified: usize,
    pos_len: usize,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Option<Symbol> {
    if unified < pos_len {
        return ps.get(unified).map(|(s, _)| *s);
    }
    let label = named_args.get(unified - pos_len)?.0;
    ps.iter()
        .find(|(s, _)| same_label(kb, *s, label))
        .map(|(s, _)| *s)
}

/// WI-20260828-N2FHM — does a declared param type MENTION one of `spec_sort`'s own type
/// params? The gate on the carrier-param staging trigger, and the exact question
/// [`op_tp_pinning_params`] asks for WI-821's — asked over a carrier that one cannot read.
///
/// WHY IT IS NOT [`type_mentions_op_tp`]. That reader answers `false` for a
/// `Value::Node`-carried type, and says so in its own doc ("no staging extension — sound,
/// just not extended"). MEASURED on `Iterable.find`: `c: C` is `Value::Term` and answers
/// `true`, while `pred: (x: Element) -> Bool @ {EffP, -Modify[x]}` is `Value::Node` — the
/// dependent-absence arrow puts it on the occurrence carrier — and answers `false`. So
/// gating this trigger on that reader would decline exactly the shape the trigger exists
/// for. This walks the carrier-agnostic [`extract_type`] view instead, and hands a
/// `Value::Term` subtree straight to `type_term_mentions_op_tp` so the two agree wherever
/// both can see.
///
/// DELIBERATELY LOCAL, and not a widening of `type_mentions_op_tp`: that reader is shared
/// with WI-821's `tp_pinning`, and making it see through the Node carrier would change
/// which arguments THAT trigger stages — a different question, with its own corpus.
///
/// Leaves are compared by SYMBOL as well as by canonical `VarId`, since a sort param is
/// spelled `Ref`/`Ident`/nullary-`Fn` through its alias and `extract_type` renders those as
/// `SortRef`/`TypeVar` without the term to run [`elem_var_step`] over.
pub(super) fn type_mentions_spec_param(
    kb: &KnowledgeBase,
    ty: &Value,
    spec_syms: &[Symbol],
    spec_vars: &[VarId],
) -> bool {
    if let Value::Term { id, .. } = ty {
        return type_term_mentions_op_tp(kb, *id, spec_vars);
    }
    let names = |sym: Symbol| spec_syms.iter().any(|s| same_sort_canonical(kb, *s, sym));
    let recur = |v: &Value| type_mentions_spec_param(kb, v, spec_syms, spec_vars);
    match extract_type(kb, ty) {
        TypeExtractor::SortRef(sym) | TypeExtractor::TypeVar(sym) => names(sym),
        TypeExtractor::Parameterized { base, bindings } => {
            names(base) || bindings.iter().any(|(_, v)| recur(v))
        }
        TypeExtractor::Arrow {
            param,
            result,
            effects,
            arity: _,
        } => recur(&param) || recur(&result) || recur(&effects),
        TypeExtractor::NamedTuple(fields) => fields.iter().any(|(_, v)| recur(v)),
        TypeExtractor::EffectsRows(e) => recur(&e),
        // WI-20260904-50B2K part (c): a spec parameter named in a CONSTRAINT is mentioned
        // by this type as surely as one in the body — `Additive[T = ?a]` is the shape this
        // predicate exists to see.
        TypeExtractor::PolyType { context, body, .. } => recur(&body) || context.iter().any(recur),
        TypeExtractor::Denoted(v) => recur(&v),
        TypeExtractor::ExprCarried { value, .. } => recur(&value),
        // A logical variable, a rigid, and the two empties are LEAVES that name no
        // declared param. `RigidTypeProjection` bottoms out in a skolem, likewise.
        TypeExtractor::FlexVar { .. }
        | TypeExtractor::Skolem { .. }
        | TypeExtractor::RigidTypeProjection { .. }
        | TypeExtractor::Nothing
        | TypeExtractor::Error => false,
    }
}

/// WI-485 + WI-793: the param→argument-type map that lets a sibling callback param's
/// projection be eliminated BEFORE it hints a lambda — plus the argument positions whose
/// type this call must compute FIRST for that map to be complete.
///
/// THE ORDERING PROBLEM this exists to solve. A callback param can be typed with a
/// path-dependent projection over a SIBLING param — `List.foldLeft`'s
/// `f: (acc: Acc, x: xs.T) -> Acc`. That declared type is what gets pushed into a lambda
/// argument as its expected type, and it is the only thing that tells the binder `x` what
/// it is, so `xs.T` must become `Int64` BEFORE the lambda is visited. That needs the type
/// of the argument in the `xs` slot. But the `Expr::Apply` arm builds hints for EVERY
/// argument and only then pushes the argument Visits — so at hint time nothing has been
/// typed at all, the receiver included.
///
/// WI-485 worked around it with readers that need no typing: an env binding for a
/// var-ref, a rule's schema, a stamp from an earlier frame. Those cover a receiver whose
/// type already exists somewhere. They do not cover an ordinary EXPRESSION — a list
/// literal `[1, 2, 3]`, a `cons` spine, a call `mk()` — so `List.foldLeft([1, 2, 3], 0, λ)`
/// hinted the lambda with an un-eliminated `xs.T`, the binder bound the rigid NEUTRAL, and
/// a CORRECT program failed to LOAD with `expected Int64, got xs.T` (WI-793). A named
/// operation callback was unaffected — its own declared param types drive, and the arrow
/// conforms after the WI-398 call-site elimination — which is why the defect needed the
/// literal AND the lambda together.
///
/// So the second return value is the fix: the arguments to VISIT FIRST, in dependency
/// order, rather than typing them a second time out of band. This is the shape the
/// DOT-CALL path already had — `[1, 2, 3].foldLeft(0, λ)` never had the bug because the
/// `DotApply` frame pushes only its receiver's Visit and reads that result before the
/// arguments are typed (WI-443). Staging gives the qualified spelling the same footing,
/// on the same work-stack, with the same fuel and the same `@[simp]` gate.
///
/// STAGING IS NARROW, and each condition earns its place:
///  - the call must have a higher-order argument at all (the caller's gate) — a hint is
///    only load-bearing for a lambda;
///  - the parameter must be one some OTHER parameter's type actually PROJECTS (what
///    `projected` computes), or — WI-821 — one that PINS a callee TYPE PARAM some
///    hof-shaped argument's param type mentions (what `tp_pinning` computes): in
///    `apply_fn(fn: Function[A = X, B = Int64], a: X)` the lambda's binder types from
///    `X`, and only the `a` argument can pin it, so `a` must be typed first or the
///    lambda body types against an unconstrained wildcard — and a requires-carrying
///    call inside it builds its dispatch dict against that wildcard (the WI-817
///    witness measured exactly that);
///  - or — WI-20260828-N2FHM — one that could be the callee's CARRIER-PARAM RECEIVER
///    (`Iterable.find(c: C, …)`, what [`spec_carrier_param_candidates`] recognizes),
///    since a callback param naming one of the spec's own params (`x: Element`) is
///    grounded from that receiver's provision and from nothing in the signature;
///  - the no-typing readers must have MISSED, so a var-ref receiver still costs nothing;
///  - and the argument must not itself be [`is_hof_shaped`]. That last one is not
///    hypothetical: `foo(g: (x: Int64) -> Int64, h: (y: g.T) -> Int64)` puts a CALLBACK
///    in `projected`, and staging it would visit the lambda with no hint — the exact
///    thing this machinery exists to provide.
pub(super) fn known_arg_types_and_staged(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    functor: Symbol,
    op: &OperationInfoFull,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> (HashMap<Symbol, Value>, Vec<usize>) {
    let ps = &op.params;
    // The params some param type PROJECTS. ONE walk of the signature; empty ⟹ this call
    // eliminates nothing, so no argument is worth staging.
    let mut projected: Vec<Symbol> = Vec::new();
    for (_, t) in ps.iter() {
        collect_projection_receivers(kb, t, &mut projected);
    }
    // WI-821: the params that can PIN a callee type param a hof-shaped argument's
    // declared type mentions (see the doc above). Disjoint from `projected` in
    // mechanism (type-param identity, not path projection) but identical in
    // treatment: their arguments are typed first so the hint map can be completed.
    let tp_pinning = op_tp_pinning_params(kb, functor, op, pos_args, named_args);
    // WI-20260828-N2FHM: the THIRD trigger — the callee's CARRIER-PARAM receiver
    // (`Iterable.find(c: C, …)`). A callback param that names one of the spec's OWN params
    // (`pred: (x: Element) -> Bool`) is grounded from that receiver's PROVISION, not from
    // the signature, so `bind_spec_params_for_hint` needs its type before the lambda is
    // hinted — and neither trigger above reaches it. `projected` sees only path
    // projections, and `tp_pinning`'s mention-walk answers `false` for a `Value::Node`
    // param type by its own doc, which is exactly what `find`'s dependent-absence arrow
    // (`@ {EffP, -Modify[x]}`) is. MEASURED: with a var-ref receiver the WI-485 env reader
    // already supplies the type and this changes nothing; with a COMPUTED receiver
    // (`find(rows(), λ)`) nothing was staged, the binder typed as the bare sort ref
    // `Iterable.Element`, and `r.flag` reached eval as an un-desugared `DotApply`.
    //
    // No wider than the classification it feeds: [`spec_carrier_param_candidates`] is the
    // recognizer `carrier_param_receiver` itself runs, so an argument staged here is one
    // whose type that classification will read.
    let spec_carrier: SmallVec<[Symbol; 2]> = spec_carrier_param_candidates(kb, ps, functor)
        .filter(|(spec_sort, _)| {
            // THE GATE, the peer of `op_tp_pinning_params`' `some_hof_mentions_tp` (added on
            // /code-review): stage nothing unless a HOF-shaped argument's declared type
            // actually names one of the spec's params — otherwise every call to a
            // carrier-param spec op that happens to carry a lambda took the two-phase
            // `ApplyHints` path for a hint that could not change. `find(xs, λ)` passes it on
            // `pred: (x: Element) -> …`; `Stream.find`, whose `pred: (x: s.T)` is a path
            // PROJECTION rather than a spec param, does not — that one is `projected`'s.
            //
            // IT IS NOT VACUOUS, measured rather than argued: on one stdlib + fixture load
            // the gate is asked 97 times and DECLINES 36 of them, so better than a third of
            // the calls that reach here keep their single-phase order. No verdict changes
            // either way — this is an ordering gate, and nothing in the corpus can be red
            // for it — so the count IS the evidence, and there is no test to point at.
            let spec_params = sort_type_params_as_pairs(kb, *spec_sort);
            let spec_syms: SmallVec<[Symbol; 4]> = spec_params.iter().map(|(s, _)| *s).collect();
            let spec_vars: SmallVec<[VarId; 4]> = spec_params
                .iter()
                .filter_map(|(_, t)| match kb.get_term(*t) {
                    Term::Var(Var::Global(v)) => Some(*v),
                    _ => None,
                })
                .collect();
            ps.iter().enumerate().any(|(j, (psym, pty))| {
                param_arg_index(kb, *psym, j, pos_args.len(), named_args)
                    .and_then(|u| arg_at(pos_args, named_args, u))
                    .is_some_and(is_hof_shaped)
                    && type_mentions_spec_param(kb, pty, &spec_syms, &spec_vars)
            })
        })
        .map(|(_, cands)| cands.iter().map(|(_, psym, _)| *psym).collect())
        .unwrap_or_default();
    let mut known: HashMap<Symbol, Value> = HashMap::new();
    let mut staged: Vec<usize> = Vec::new();
    for (j, (psym, _)) in ps.iter().enumerate() {
        let Some(unified) = param_arg_index(kb, *psym, j, pos_args.len(), named_args) else {
            continue;
        };
        let Some(a) = arg_at(pos_args, named_args, unified) else {
            continue;
        };
        // A sibling callback param may project this arg's schema (`join`'s
        // `cond: (c: r1.T, q: r2.T) -> Bool`). The env covers a let-bound receiver
        // (WI-723); a bare RULE-reference arg (`join(r1, r2, …)`'s `r2`) is a
        // `Relation[T]` value never bound in the env, so its schema is computed directly
        // (WI-714) — else `r2.T` cannot be eliminated at hint time and the two-row
        // lambda's binder stays an unresolved projection. WI-750: the third reader (the
        // node's STAMPED type) covers a COMPUTED receiver — `r.where(λ).where(λ)`, whose
        // inner call is an `Expr::Apply` that neither of the first two match.
        //
        // SCOPE OF THE STAMP READER, stated as the code actually behaves — carried
        // forward from WI-750 because it is a warning aimed at edits like WI-793's, and
        // the `projected` / `is_hof_shaped` gates BELOW must not be read back onto it:
        // `projection_receiver_type` reads the stamp of ANY arg in ANY `Expr::Apply`
        // carrying a HOF arg. There is no receiver gate on it, and it would be wrong to
        // claim one. What bounds it is that a stamp is only present where a pass already
        // typed the node, which for the shape WI-750 fixed is the spliced dot-call
        // receiver. On a RE-typed tree other args carry stamps too and may now contribute
        // a binding; that is a widening, deliberate — a computed
        // `join(r1, mk().where(λ), cond)` operand needs exactly the same reading — but it
        // means the bound is EMPIRICAL, not structural, so do not rely on "receiver only"
        // when editing here. Leaf args are unaffected either way: `varref_arg_env_type`
        // already consulted the stamp for them.
        //
        // The staging gates below are narrower than this reader ON PURPOSE and do not
        // constrain it: they decide only which args are worth TYPING, never which args
        // may be READ.
        //
        // `env` stays FIRST: a still-flexible env binding is the live one, a stamp only a
        // fallback. This is [`projection_receiver_type`], the reader the WI-714 projection
        // path already composes.
        if let Some(t) = projection_receiver_type(kb, env, a) {
            known.insert(*psym, t);
        } else if (projected.contains(psym)
            || tp_pinning.contains(psym)
            || spec_carrier.contains(psym))
            && !is_hof_shaped(a)
        {
            staged.push(unified);
        }
    }
    // ASCENDING: the caller pushes the staged Visits in reverse, so their results land on
    // the results stack in this order, and the `Apply` frame splices them back by it.
    // A named argument's unified index does not follow declaration order, so this sort is
    // load-bearing, not tidiness.
    staged.sort_unstable();
    staged.dedup();
    (known, staged)
}

/// WI-821: the params of the callee whose declared type can PIN a callee TYPE
/// PARAM that some hof-shaped argument's declared param type mentions — the
/// type-param sibling of `collect_projection_receivers`' path-projection
/// trigger. In `apply_fn(fn: Function[A = X, B = Int64], a: X)` a lambda in
/// the `fn` slot is hinted from `X`, and only the `a` argument determines it,
/// so `a` is worth staging. Covers the callee's op-scoped `[X]` params (their
/// declared-type mentions ARE `Var::Global` terms — `extract_type_params`'
/// invariant) and its parent sort's params (the same pinning shape one scope
/// up, mentioned as `Ref`/nullary-`Fn` through the sort alias — both spellings
/// via [`elem_var_step`]). Empty whenever nothing is pinnable, no hof-shaped
/// argument mentions a pinnable param, or the mention walk cannot see the
/// spelling (a `Value::Node` param type) — staging then simply does not
/// extend, today's order stands.
fn op_tp_pinning_params(
    kb: &KnowledgeBase,
    functor: Symbol,
    op: &OperationInfoFull,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Vec<Symbol> {
    // WI-849: the op table holds each param's `Var` directly. A non-`Global` entry is
    // SKIPPED, not refused — this function computes a STAGING HINT (which arguments to
    // type first), so an entry it cannot use costs only a missed reordering, never a
    // wrong judgement. Deliberately not an `unreachable!` even though
    // `extract_type_params` yields only `Global` today: `OpInfoRecord::type_params` is a
    // `pub` field on a `pub` struct, so an out-of-crate producer can hand this a `Rigid`
    // or `DeBruijn`, and aborting a downstream tool over a heuristic would be far worse
    // than declining to stage.
    let mut tp_vars: Vec<VarId> = op
        .type_params
        .iter()
        .filter_map(|(_, v)| match v {
            Var::Global(v) => Some(*v),
            _ => None,
        })
        .collect();
    // (code-review) Kind-gate + memoized read. A free op's parent is a NAMESPACE, and
    // the uncached `impl_param_symbols` → `type_params_of_sort` walk scanned the whole
    // symbol table per call — paid on every call with any lambda-or-VarRef argument
    // just to learn a namespace has no params. (WI-954 made that walk an owner-scope
    // read, so the memo is now about not rebuilding the pairs, not about the scan.)
    // `sort_type_params_as_pairs` is the same filter chain, memoized on
    // `sort_param_pairs_cache`. WI-956: the gate is
    // `impl_parent_sort_of_op`'s, which asks `has_kind` — see its doc for the
    // re-declared sort whose params this dropped under `kind_of`.
    if let Some(parent) = impl_parent_sort_of_op(kb, functor) {
        for (_, target) in sort_type_params_as_pairs(kb, parent).iter() {
            if let Term::Var(Var::Global(v)) = kb.get_term(*target) {
                tp_vars.push(*v);
            }
        }
    }
    if tp_vars.is_empty() {
        return Vec::new();
    }
    let ps = &op.params;
    // ONE walk per param type, shared by the hof-side scan and the collect.
    let mentions: Vec<bool> = ps
        .iter()
        .map(|(_, t)| type_mentions_op_tp(kb, t, &tp_vars))
        .collect();
    let some_hof_mentions_tp = ps.iter().enumerate().any(|(j, (psym, _))| {
        mentions[j]
            && param_arg_index(kb, *psym, j, pos_args.len(), named_args)
                .and_then(|u| arg_at(pos_args, named_args, u))
                .is_some_and(is_hof_shaped)
    });
    if !some_hof_mentions_tp {
        return Vec::new();
    }
    ps.iter()
        .zip(&mentions)
        .filter(|(_, m)| **m)
        .map(|((s, _), _)| *s)
        .collect()
}

/// WI-821: does a declared param type mention one of the callee's pinnable
/// type params? Leaves classify through [`elem_var_step`] — the shared
/// "element term → canonical var" primitive — so an op-tp's direct
/// `Var::Global` and a sort param's `Ref`/`Ident`/nullary-`Fn` alias spelling
/// answer uniformly (a `Var::Rigid` can never be in `tp_vars`, so its arm is
/// inert here). A `Value::Node`-carried type answers `false` (no staging
/// extension — sound, just not extended).
fn type_mentions_op_tp(kb: &KnowledgeBase, ty: &Value, tp_vars: &[VarId]) -> bool {
    match ty {
        Value::Term { id, .. } => type_term_mentions_op_tp(kb, *id, tp_vars),
        _ => false,
    }
}

/// The `TermId` walk under [`type_mentions_op_tp`].
fn type_term_mentions_op_tp(kb: &KnowledgeBase, tid: TermId, tp_vars: &[VarId]) -> bool {
    term_any_subterm(kb, tid, &|t, _| {
        elem_var_step(kb, t).is_some_and(|(v, _)| tp_vars.contains(&v))
    })
}

/// WI-821: the substitution that instantiates a hof param type's callee type
/// params from the KNOWN sibling argument types — unify each known param's
/// DECLARED type against its argument's type (`a: X` vs `Wrap[A = GT]` pins
/// `X`), exactly the pinning the call itself performs later at argument
/// unification, done early so a lambda's hint can carry it. `None` when
/// nothing is known or nothing BINDS (a monomorphic callee's pairs unify
/// without binding, and an empty σ would only buy every hint a no-op deep
/// rebuild) — the hint then stays as declared.
pub(super) fn hint_instantiation_subst(
    kb: &mut KnowledgeBase,
    ps: &[(Symbol, Value)],
    known: &HashMap<Symbol, Value>,
) -> Option<Substitution> {
    if known.is_empty() {
        return None;
    }
    let mut s = Substitution::new();
    for (psym, declared) in ps {
        if let Some(arg_ty) = known.get(psym) {
            // Probe on a CLONE of the accumulated σ and commit atomically: a
            // failed pair mutates as it goes and its partial bindings must not
            // ride into the hint (they would move a plain argument type error
            // onto a corrupted lambda binder). The clone sees earlier pairs'
            // bindings, so a pair that unifies alone but conflicts CROSS-pair
            // is also discarded whole — the fresh-probe version was blind to
            // that (code-review). `Substitution::clone` is O(1) (imbl), so
            // this is one unification per pair, not two.
            let mut probe = s.clone();
            if unify_types(kb, &mut probe, declared, arg_ty) {
                s = probe;
            }
        }
    }
    (!s.is_empty()).then_some(s)
}

/// WI-275/427/707: the top-down hint for ONE argument, given its declared parameter type.
/// Shared by the positional and named channels (they differ only in how `pt` is looked
/// up) and by both staging phases, so a hint cannot be computed one way before the
/// receiver is typed and another way after.
///
/// WI-821: `inst` — the [`hint_instantiation_subst`] pinning callee type params from
/// known sibling argument types — is applied to a HOF hint only, mirroring how the
/// projection elimination is: the other hint kinds are gated on ground declared types
/// and never mention a callee type param.
pub(super) fn one_arg_hint(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    arg: &Rc<NodeOccurrence>,
    pt: Option<Value>,
    known: &HashMap<Symbol, Value>,
    inst: Option<&Substitution>,
) -> Option<Value> {
    // WI-485: eliminate a callback param projection for the lambda hint (`s.T ⟹ Int64`);
    // keep the original `pt` for the nested-call hint (that path is gated on a ground
    // type and rides the call-site path).
    let pt_hof = pt
        .as_ref()
        .and_then(|t| eliminate_callback_hint_projection(kb, t, known, functor))
        .or_else(|| pt.clone());
    // Only a hof-shaped arg consumes `pt_hof` (`hof_arg_hint`'s own gate), so
    // the deep rebuild is skipped for every other argument.
    let pt_hof = match (inst, pt_hof) {
        (Some(s), Some(t)) if is_hof_shaped(arg) => Some(resolve_type_deep_value(kb, s, &t)),
        (_, t) => t,
    };
    let pt_eliminated = pt_hof.clone();
    let base = hof_arg_hint(kb, arg, pt_hof)
        .or_else(|| nested_call_arg_hint(kb, arg, pt.as_ref()))
        .or_else(|| type_slot_arg_hint(kb, arg, pt.as_ref()))
        .or_else(|| variant_slot_arg_hint(kb, arg, pt.as_ref()))
        .or_else(|| seq_slot_arg_hint(kb, arg, pt.as_ref()));
    if base.is_some() {
        return base;
    }
    // WI-20260828-5NSZY: the fifth kind, written after the chain rather than inside it
    // because its gate needs `&mut kb` (it performs a unification to walk the parameter
    // type through the constructor) while the four above read immutably. Last, so it
    // cannot pre-empt a hint any of them would have produced.
    // WI-20260828-5NSZY review: the PROJECTION-ELIMINATED type (`pt_hof`), not the raw `pt`.
    // Every other callback-shaped hint reads the eliminated one (WI-485), and this hint's
    // whole job is to deliver an arrow to a name that will be checked against it — an
    // un-eliminated `s.T` there would be checked against a projection the caller has already
    // resolved. Falls back to `pt` when elimination declines, which is what `pt_hof` already
    // encodes. MEASURED: no verdict in the workspace changes, so this is an agreement with
    // the siblings rather than a fix — recorded because `one_arg_hint`'s own doc says the
    // non-HOF hints "never mention a callee type param", which this one can.
    let pt = pt_eliminated.or(pt)?;
    ctor_arg_unlocks_an_arrow_for_a_bare_name(kb, arg, &pt).then_some(pt)
}

/// WI-20260828-N2FHM — the substitution that grounds a spec's OWN type params from the
/// receiver argument's carrier, computed at HINT time so a callback param that names one
/// can be eliminated before it hints a lambda.
///
/// THE GAP THIS CLOSES, measured. `Iterable.find(c: C, pred: (x: Element) -> Bool)` types
/// its callback binder from `Element`, a param of the SPEC — not, as `Stream.find`'s
/// `pred: (x: s.T)` does, a PROJECTION of a sibling. WI-485's elimination and WI-821's
/// `hint_instantiation_subst` between them cover the projection and the callee-type-param
/// spellings; neither covers this one. `hint_instantiation_subst` unifies the declared
/// `c: C` against `List[T = Row]` and so binds `C`, but nothing in the signature relates
/// `Element` to `C` — that relation lives in the carrier's PROVISION
/// (`List provides Stream provides Iterable[C = …, Element = T, E = {}]`), which is
/// exactly what [`carrier_param_receiver`] classifies and
/// [`bind_spec_params_from_carrier_param`] reads. So `find(rows, lambda r -> r.flag)`
/// hinted its binder with the bare sort ref `Iterable.Element`, the dot found no `flag`
/// on it, and the resulting `DotDispatchNoMatch` was swallowed by the match frame
/// (repaired separately) — leaving an un-desugared `Expr::DotApply` for eval to die on.
///
/// ONE DECISION PROCEDURE, TWO MOMENTS: this runs the SAME classification + binder pair
/// `check_apply` runs after the arguments are typed, differing only in where the
/// receiver's type comes from (the WI-793 `known` map rather than the typed results).
/// It cannot bind anything the later pass would not bind — same view, same provision,
/// same skip of the carrier param `C` — so it can only make a hint MORE ground, never
/// redirect a dispatch.
///
/// `false` whenever the classification declines (no carrier-param receiver, no provision
/// view, a receiver whose type no no-typing reader knows) or nothing binds; the hint then
/// stays exactly as declared, which is today's behaviour.
///
/// Binds into the SAME `subst` [`hint_instantiation_subst`] filled, not a second one the
/// caller would have to merge: the two are disjoint by construction — that one pins the
/// callee's params from the declared/argument pairs (the carrier param `C` among them),
/// this one the spec's OTHER params from the provision, and
/// [`bind_spec_params_from_carrier_param`] skips `C` for exactly that reason. Filling one
/// σ keeps the hint's single deep resolve, and a contradiction (should the disjointness
/// ever stop holding) is loud from `bind_term` rather than silently order-dependent.
pub(super) fn bind_spec_params_for_hint(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    functor: Symbol,
    params: &[(Symbol, Value)],
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    known: &HashMap<Symbol, Value>,
) -> bool {
    if known.is_empty() {
        return false;
    }
    let Some((spec_sort, carrier_sym, recv_ty, view, carrier_pvid, _transitive, recv_arg_sym)) =
        carrier_param_receiver(kb, params, functor, pos_args, named_args, &|_i, pname| {
            known.get(&pname).cloned()
        })
    else {
        return false;
    };
    bind_spec_params_from_carrier_param(
        kb,
        subst,
        spec_sort,
        carrier_sym,
        carrier_pvid,
        &recv_ty,
        view,
        recv_arg_sym,
    )
}

/// WI-275: the top-down hints for every argument of a call, positional then named.
///
/// WI-793 note on why calling this BEFORE the staged arguments are typed is sound: only
/// [`hof_arg_hint`] reads the projection-eliminated type, and it answers `None` for
/// anything not [`is_hof_shaped`]. A staged argument is never hof-shaped, so its hint
/// does not depend on `known` — computing it with the incomplete map yields exactly the
/// hint the completed map would. That is what lets a staged argument keep the
/// `nested_call_arg_hint` / `type_slot_arg_hint` it would otherwise have received.
pub(super) fn apply_arg_hints(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    op_params: Option<&Vec<(Symbol, Value)>>,
    sort_app_hint: &Option<Value>,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    known: &HashMap<Symbol, Value>,
) -> (Vec<Option<Value>>, Vec<Option<Value>>) {
    // WI-821: pin callee type params from the known sibling argument types once,
    // so every HOF hint below carries the instantiation (`Function[A = X]` hints
    // as `Function[A = Wrap[…]]` when the sibling `a: X` argument is known).
    //
    // WI-20260828-N2FHM: and, into the SAME σ, the callee spec's own params read off the
    // receiver's provision — the third spelling a callback param can name its element in
    // (`Iterable.find`'s `pred: (x: Element) -> Bool`), which neither the WI-485
    // projection elimination nor the pairwise pinning above can reach. See
    // [`bind_spec_params_for_hint`].
    let inst = op_params.and_then(|ps| {
        let mut s = hint_instantiation_subst(kb, ps, known).unwrap_or_else(Substitution::new);
        bind_spec_params_for_hint(kb, &mut s, functor, ps, pos_args, named_args, known);
        (!s.is_empty()).then_some(s)
    });
    // WI-20260904-50B2K — WHICH PARAMETER A POSITIONAL ARGUMENT TAKES IS
    // [`positional_param_indices`]' QUESTION, not `ps.get(i)`. A named argument CONSUMES a
    // parameter, so a positional one beside it does not land at its own index — the
    // rank-among-NOT-named rule (WI-20260827-1F0QP), which `check_apply_iter` has always
    // used for the CHECK. This loop used a raw index, so the hint and the check read
    // different slots. Driven, and it is a WRONGLY REFUSED program rather than a missed
    // hint:
    //
    //     operation f4(a: Function[A = String, B = String],
    //                  b: Function[A = Int64,  B = Int64]) -> Int64
    //     f4(lambda x -> x + 1, a: g)
    //       -> "type mismatch in add.b (op-arg): expected String, got Int64"
    //
    // The lambda is parameter `b`, and the raw index hinted it with `a`'s `String`, so its
    // body was checked at the wrong type. BOTH BODIES reported it identically — this loop
    // is shared, which is what kept the defect symmetric and is why the rule-body/operation-body
    // agreement never showed it. Found by /code-review on the sibling list in
    // [`data_slot_arg_hints`], which had been corrected to this owner and left this one
    // disagreeing INSIDE ONE FUNCTION.
    //
    // ON AN OVER-APPLIED MIXED CALL THIS HINTS NOTHING, AND THE TWO OVER-ARITY SPELLINGS
    // THEREFORE DISAGREE. `positional_param_indices` answers `OverArity` with all-`None`
    // (its own documented decision: which argument is surplus has no answer), while its
    // `named_args.is_empty()` early return still maps `i < params.len()`. MEASURED:
    //
    //   f(lambda x -> x + x, 7, n: 2)   2 errors — the arity error, AND a spurious
    //                                   `missing requires Additive[T = …]` from the
    //                                   binder nothing hinted
    //   f(lambda x -> x + x, 2, 3)      1 error  — the arity error alone
    //
    // KEPT, and the reason is that every repair is worse than the symptom. Restoring a
    // leading-argument guess for the HINT re-creates exactly the defect the comment above
    // records — hint and check reading different slot owners — and a wrong hint is not
    // cosmetic: it checks a lambda body at the wrong type and REFUSES. Here the call is
    // already refused for arity, so what is at stake is one extra true-but-consequential
    // error on a program that cannot load either way, against re-opening a channel that
    // wrongly refused a VALID one. Raised by /code-review; measured before deciding.
    let pos_slots = op_params
        .map(|ps| positional_param_indices(kb, ps, pos_args.len(), named_args))
        .unwrap_or_default();
    let mut pos_hints = Vec::with_capacity(pos_args.len());
    for (i, arg) in pos_args.iter().enumerate() {
        // WI-707: inside a sort application every argument is a type.
        if sort_app_hint.is_some() {
            pos_hints.push(sort_app_hint.clone());
            continue;
        }
        let pt = pos_slots
            .get(i)
            .copied()
            .flatten()
            .and_then(|slot| op_params.and_then(|ps| ps.get(slot)))
            .map(|(_, t)| t.clone());
        pos_hints.push(one_arg_hint(kb, functor, arg, pt, known, inst.as_ref()));
    }
    let mut named_hints = Vec::with_capacity(named_args.len());
    for (name, arg) in named_args.iter() {
        if sort_app_hint.is_some() {
            named_hints.push(sort_app_hint.clone());
            continue;
        }
        // WI-426: match the named-arg label to its param by name.
        let pt = op_params
            .and_then(|ps| ps.iter().find(|(s, _)| same_label(kb, *s, *name)))
            .map(|(_, t)| t.clone());
        named_hints.push(one_arg_hint(kb, functor, arg, pt, known, inst.as_ref()));
    }
    (pos_hints, named_hints)
}

/// WI-485: eliminate a cross-param projection in a callback PARAM type (e.g. find's
/// `pred: (x: s.T) -> Bool @ {EffP, -Modify[x]}`) against the receiver param's argument
/// type, so a LAMBDA callback's param is hinted with the THREADED element
/// (`s.T ⟹ Int64` when the receiver `s`'s argument is `xs: List[Int64]`). The WI-398
/// call-site elimination runs only AFTER every argument is synthesized — too late for a
/// lambda, whose BODY is checked at synthesis against the pushed param hint (a named-op
/// callback is unaffected: its own declared param drives, and the arrow conforms after the
/// WI-398 elimination). Returns the eliminated type, or `None` to keep the original when
/// the projection's receiver arg is not a known `VarRef`; an un-eliminable projection is
/// swallowed here (the later call-site elimination still reports a genuine bad projection
/// loudly), never silently grounded.
fn eliminate_callback_hint_projection(
    kb: &mut KnowledgeBase,
    pt: &Value,
    param_arg_types: &HashMap<Symbol, Value>,
    fn_sym: Symbol,
) -> Option<Value> {
    if param_arg_types.is_empty() || !value_contains_projection(kb, pt) {
        return None;
    }
    let ctx = TypeErrorContext::OperationReturn {
        op_name: fn_sym,
        surface: None,
    };
    eliminate_type_projections(kb, pt, param_arg_types, None, &ctx, None).ok()
}

/// WI-427: true iff the type term mentions a `TypeExtractor.TypeVar` form
/// anywhere — an operation's own type parameter, which is out of scope as a
/// top-down hint for a *different* call (and a wildcard in the subtype
/// relation, so it could never pin by equality anyway). The recursive
/// complement of [`type_value_is_ground`], which catches logic vars and
/// SORT-param refs but keys its functor test on sort-param symbols only.
pub(super) fn type_term_mentions_type_var(kb: &KnowledgeBase, tid: TermId) -> bool {
    term_any_subterm(kb, tid, &|_, term| {
        matches!(term, Term::Fn { functor, .. }
            if kb.qualified_name_of(*functor) == "anthill.prelude.TypeExtractor.TypeVar")
    })
}

/// WI-427: the expected-type hint for a nested-call argument — the
/// `expected → argument` half of bidirectional inference (WI-379 delivered
/// the `argument → expected` half). The declared param type flows *down*
/// into an argument that is itself a call, so a callee type-param that
/// appears ONLY in the argument's return type
/// (`poly[X]() -> Wrapper[P = Inner[T = X]]` in a
/// `Wrapper[P = Inner[T = String]]` slot) is pinned by the call context
/// instead of failing "X unconstrained".
///
/// SOUNDNESS (the WI-379 variance sidestep, expansion-during-unification.md):
/// the hint is pushed only where it pins by EQUALITY — a fully-GROUND
/// declared param type (no logic var, no sort-param ref, no TypeVar
/// anywhere). A projection param type (`k: s.cell.T`) rides a non-`Term`
/// carrier and is skipped by the same gate (its elimination is the
/// call-site's job, after the args are typed). Inside the argument's own
/// `check_apply_iter` the hint is consulted only AFTER its arguments pinned
/// the params (the WI-270/379 fill-only-still-free order) and a
/// contradicting hint binds nothing — so a wrong hint cannot mask the
/// normal arg-vs-param mismatch diagnostic, and no metavariable is ever
/// solved through a `<:` constraint.
pub(super) fn nested_call_arg_hint(
    kb: &KnowledgeBase,
    arg: &Rc<NodeOccurrence>,
    param_type: Option<&Value>,
) -> Option<Value> {
    let pt = param_type?;
    let is_call_arg = matches!(
        &arg.kind,
        NodeKind::Expr {
            expr: Expr::Apply { .. },
            ..
        }
    );
    let pins_by_equality = resolved_type_is_ground(kb, pt)
        && !matches!(pt, Value::Term { id: t, .. } if type_term_mentions_type_var(kb, *t));
    if is_call_arg && pins_by_equality {
        Some(pt.clone())
    } else {
        None
    }
}

/// WI-206 / WI-707: the hint a parameter declared `Type` pushes down to an argument
/// that NAMES A SORT — a bare reference (`is_modifiable(Cell)`, WI-206) or a sort
/// APPLICATION (`is_modifiable(Cell[V = Int64])`, WI-707). Neither has a value
/// reading of its own: [`check_bare_ref`] reads a sort name as the sort's `Type`
/// value, and the Apply arms read a sort-headed application as a parameterized type,
/// only in a slot that asks for a `Type` — this hint is what tells them the slot
/// does. (An ENTITY reference needs no hint: it denotes its `Type` unconditionally.)
///
/// Confined to sort-naming arguments and to a `Type` param: no other argument shape
/// changes reading under this hint, so a call / lambda argument keeps exactly the
/// `hof_arg_hint` / `nested_call_arg_hint` it has today, and a sort name in any
/// non-`Type` slot stays the loud `UnresolvedName` it is today.
pub(super) fn type_slot_arg_hint(
    kb: &KnowledgeBase,
    arg: &Rc<NodeOccurrence>,
    param_type: Option<&Value>,
) -> Option<Value> {
    let pt = param_type?;
    // Cheapest gate first (see [`arg_names_sort`]): only an argument whose head names
    // a SORT can change reading here, so an ordinary variable / literal / call
    // argument never reaches the `Type` name-resolve below.
    if !arg_names_sort(kb, arg) {
        return None;
    }
    if expects_reflect_type(kb, Some(pt)) {
        Some(pt.clone())
    } else {
        None
    }
}

/// WI-20260826-JSFHG: the hint a slot declared with a VARIANT type — `Colour.red`,
/// `Option.some[T = Int64]` — pushes down to a CONSTRUCTOR-application argument, so the
/// application is classified at the constructor §8.2 says it belongs to rather than at
/// the parent sort. The `expected → argument` direction of the same decision
/// [`check_constructor_iter`] makes from its own `expected`, and it shares that decision's
/// ONE predicate ([`type_head_names_an_entity`]) so the two cannot drift.
///
/// THE FOURTH HINT KIND, and confined the way its three siblings are: gated on the slot
/// naming an entity AND on the argument being a TUPLE literal or a constructor application
/// ([`arg_is_constructor_application`]) — the argument shapes whose classification this
/// changes. Every other argument keeps exactly the `hof_arg_hint` /
/// `nested_call_arg_hint` / `type_slot_arg_hint` it has today. A LIST/SET literal was a
/// third shape here and is now [`seq_slot_arg_hint`], its own kind: that gate asks about
/// the ELEMENT type and admits a callable as well as an entity, which is a different
/// question from §8.2's classification and did not belong in a function named for it.
///
/// ITS POPULATION ON EXISTING CODE IS EMPTY, which is the soundness argument and is
/// measurable rather than asserted: before this ticket a slot declared with a variant type
/// was UNSATISFIABLE — every constructor application typed at the parent, so the program
/// did not load — so no loading program has such a slot for the hint to reach.
///
/// **THE SECOND HALF OF THAT ARGUMENT — "so it can only turn a refusal into an acceptance,
/// never the reverse" — IS RETIRED**, and this is where it stood. It was true of this hint
/// ALONE and is false of it beside WI-20260826-7JDWY's element check. MEASURED:
/// `takeReds(l: List[T = Colour.red])` applied to `[r, c]` with `r: Colour.red` and
/// `c: Colour` is refused now (`list.element 2: expected red, got Colour`) and LOADED
/// before, because with no hint the literal's element type was element ONE's and element
/// two was never looked at. The new verdict is the correct one; what is gone is the
/// ARGUMENT, so a future widening of this gate is not justified by a claim that stopped
/// being true — its flip-set has not been measured and would have to be. The row is
/// `wi_7jdwy_hinted_literal_elements_test::the_restored_argument_hint_also_turns_an_-
/// acceptance_into_a_refusal`.
///
/// IT SEES ONLY THE DECLARED TYPE, which is a real limit rather than a simplification:
/// `entity box(v: T)` declares a type VAR, so a variant arriving through the parameter
/// (`Box[T = Colour.red]`) is invisible here and needs the expected type substituted in
/// first. [`variant_field_expected_from_ctor`] is that second reading, consulted after
/// this one declines.
pub(super) fn variant_slot_arg_hint(
    kb: &KnowledgeBase,
    arg: &Rc<NodeOccurrence>,
    param_type: Option<&Value>,
) -> Option<Value> {
    let pt = param_type?;
    // Cheapest gate first, mirroring [`type_slot_arg_hint`]: only these two argument
    // shapes can change reading here. The TUPLE test runs FIRST — see
    // [`arg_is_tuple_literal`] for why the constructor test would otherwise swallow it.
    // A LIST/SET literal has its own hint kind beside this one ([`seq_slot_arg_hint`]);
    // it lived here while the variant case was the only one that needed it.
    if arg_is_tuple_literal(kb, arg) {
        return type_mentions_an_entity(kb, pt).then(|| pt.clone());
    }
    if arg_is_constructor_application(kb, arg) {
        return type_head_names_an_entity(kb, pt).then(|| pt.clone());
    }
    None
}

/// WI-20260826-JSFHG: is this argument a CONSTRUCTOR APPLICATION — the two surface forms
/// [`check_constructor_iter`] itself handles? The explicit `Expr::Constructor` (a field-
/// named build, `red(v: 1)`) and an `Expr::Apply` whose functor is a registered
/// constructor (the implicit form `check_apply_iter` routes there), and a BARE 0-ary
/// reference, which [`check_bare_ref`] routes there with no arguments at all.
///
/// EACH ARM BORROWS ITS OWN DESTINATION'S PREDICATE rather than picking one for all three,
/// because the two destinations do not ask the same question and this gate must agree with
/// whichever one the argument actually reaches: the applied forms are keyed on
/// [`KnowledgeBase::entity_field_types`], which is what `check_constructor_iter` reads to
/// decide it has a constructor, and the bare form on
/// [`KnowledgeBase::is_constructor_symbol`], which is what `check_bare_ref` reads. They
/// differ exactly where it matters — a FIELDLESS `entity red` has no field-types entry, so
/// the field-types predicate answers `false` for §8.2's own worked example. Measured: with
/// one predicate at all three arms, `takeRed(red)` on a fieldless enum was still refused.
///
/// ALL THREE BARE SPELLINGS, and `VarRef` is the one that actually arrives — measured, a
/// bare `red` in an argument loads as `Expr::VarRef`, so a `Ref | Ident` arm alone left the
/// gate answering `false` on the very shape it was added for. [`arg_names_sort`] lists the
/// same three for the same reason; a bare name's Expr variant is not decided by whether it
/// turns out to name a constructor.
pub(super) fn arg_is_constructor_application(kb: &KnowledgeBase, arg: &Rc<NodeOccurrence>) -> bool {
    match &arg.kind {
        NodeKind::Expr {
            expr: Expr::Constructor { .. },
            ..
        } => true,
        NodeKind::Expr {
            expr: Expr::Apply { functor, .. },
            ..
        } => kb.entity_field_types(*functor).is_some(),
        // A BARE 0-ARY REFERENCE (`takeRed(red)`), which [`check_bare_ref`] routes to
        // `check_constructor_iter` with no arguments — so it IS an application here even
        // though nothing is applied at the surface. Found by /code-review, and it is §8.2's
        // OWN worked example (`sort Color { entity red; entity green; entity blue }`): the
        // field-carrying spellings were the only ones the first cut reached, which made
        // the fieldless enum — the shape the spec illustrates the feature with — the one
        // shape still unable to inhabit its own variant type.
        //
        // A LOCAL BINDING OF THE SAME NAME COSTS NOTHING: `check_bare_ref` resolves
        // `env.lookup_var` FIRST and returns the variable's type without reading
        // `expected` at all, so a hint pushed at a shadowed name is inert.
        NodeKind::Expr {
            expr: Expr::Ref(sym) | Expr::Ident(sym) | Expr::VarRef { name: sym },
            ..
        } => kb.is_constructor_symbol(*sym),
        _ => false,
    }
}

/// WI-206 / WI-707: whether an argument's HEAD names a sort — a bare reference
/// (`Cell`) or an application (`Cell[V = Int64]`). These are the only argument shapes
/// whose reading a `Type` slot changes, so this is the gate both the hint
/// ([`type_slot_arg_hint`]) and the declared-type lookups that FEED it are keyed on.
///
/// O(1) — a pattern match plus a `kind_of` read — because it runs for every argument
/// of every call and constructor the typer visits.
pub(super) fn arg_names_sort(kb: &KnowledgeBase, arg: &Rc<NodeOccurrence>) -> bool {
    let head = leaf_var_ref(arg).or_else(|| match arg.as_expr() {
        Some(Expr::Apply { functor, .. }) => Some(*functor),
        _ => None,
    });
    head.is_some_and(|h| kb.kind_of(h) == Some(crate::intern::SymbolKind::Sort))
}

/// WI-20260828-8Q0Q5: is `arg` a BARE OPERATION NAME — the spelling that eta-lifts?
///
/// The sibling of [`arg_names_sort`], and deliberately NARROWER than it in one place: an
/// `Expr::Apply` is excluded. `inc` is a name the reader may lift to a function value;
/// `inc(x)` is a call and already carries its own type.
pub(super) fn arg_is_bare_operation_name(kb: &KnowledgeBase, arg: &Rc<NodeOccurrence>) -> bool {
    leaf_var_ref(arg)
        .is_some_and(|head| kb.kind_of(head) == Some(crate::intern::SymbolKind::Operation))
}

/// WI-20260828-8Q0Q5: the hint an ARROW-typed constructor FIELD pushes down to a bare
/// operation-name argument, so the name eta-lifts against the DECLARED arrow and the
/// arrow's EFFECT ROW binds.
///
/// THE FIFTH HINT KIND. Without it the argument was typed with NO expected type at all:
/// the surrounding arm looks `entity_field_types` up only when some argument is a call, a
/// tuple, a sort name or a constructor application, and a bare name is none of those. So
/// [`check_bare_ref`] had no arrow to lift against, the operation's declared row never met
/// the field's row PARAMETER, and the row escaped the construction unbound — surfacing at
/// the constructing operation as `undeclared effect ?_`.
///
/// MEASURED, and each row isolates one axis (`wi_8q0q5_arrow_field_eta_row_test`): the same
/// eta-lifted operation into an OPERATION-PARAMETER arrow slot with the same row parameter
/// was already clean — that path pushes its declared param type down — so this is the FIELD
/// path and not eta-lift; an inline `lambda` in the same FIELD slot was already clean, so it
/// is the bare-NAME reading and not the arrow.
///
/// GATED ON THE FIELD BEING CALLABLE BY HEAD, not on the argument alone: pushing an
/// expected type where none was pushed before can only change a reading, so the hint is
/// confined to the slot whose reading it is for. [`type_head_is_callable`] is the same
/// question `validate_callback_effect_row` asks when it routes a slot, so the two cannot
/// drift on what a callable is.
pub(super) fn arrow_slot_arg_hint(
    kb: &KnowledgeBase,
    arg: &Rc<NodeOccurrence>,
    field_type: Option<&Value>,
) -> Option<Value> {
    let ft = field_type?;
    if !arg_is_bare_operation_name(kb, arg) {
        return None;
    }
    if type_head_is_callable(kb, ft) {
        Some(ft.clone())
    } else {
        None
    }
}

/// WI-462: the expected type a TUPLE-LITERAL constructor field value should receive — the
/// `expected → field-value` push the constructor BUILD already performs via unify, surfaced
/// here as a top-down hint. A tuple literal carries no constructor of its own, so the
/// constructor's expected-seed binds its component vars only AFTER it is typed (too late to
/// shape the built tuple type). Here we replay that seed in a SCRATCH subst — unify the
/// parent sort type against the constructor's `expected`, then walk the field's declared
/// type through it — to derive the field value's expected (`some(...)` whose declared field
/// is `value: T` and whose expected is `Option[T = (xs.T, …)]` yields `(xs.T, …)`). `None`
/// unless `expected` is a parameterized type of the constructor's parent sort and the walk
/// SPECIALIZES the field type to a `named_tuple` (the only shape a tuple literal threads).
///
/// WI-946 left the STRICT accessor here, alone among the belongs-to readers, because
/// no probe made the difference observable: an eponymous parametric `sort Box { sort
/// T = ?; entity Box(v: T) }` gets no hint (strict answers `None`), yet both the
/// direct build `Box((a, b))` against `Box[T = (Int64, Int64)]` and the WI-462-shaped
/// path-dependent `Box((h, t))` off a `case cons(h, t)` destructure load clean either
/// way — the components type bottom-up to the same thing the hint would have pushed.
/// Recorded rather than converted: the ticket's bar is a test that FAILS before the
/// change, and there is none. Converting is still the right move the moment one exists.
pub(super) fn tuple_field_expected_from_ctor(
    kb: &mut KnowledgeBase,
    ctor_sym: Symbol,
    field_sym: Symbol,
    expected: &Option<Value>,
) -> Option<Value> {
    let walked = ctor_field_expected(kb, ctor_sym, field_sym, expected)?;
    // Only a useful hint if the walk produced a concrete tuple type (a still-abstract
    // field param, or a non-tuple field, leaves a tuple literal nothing to thread).
    matches!(extract_type(kb, &walked), TypeExtractor::NamedTuple(_)).then_some(walked)
}

/// One constructor field's declared type, INSTANTIATED by unifying the constructor's
/// parent sort against `expected` — `Box`'s `v: T` read as `Colour.red` when the slot
/// awaits a `Box[T = Colour.red]`.
///
/// Extracted from [`tuple_field_expected_from_ctor`], which was the only caller and kept
/// only the tuple-typed answers. [`variant_field_expected_from_ctor`] wants the same walk
/// and a different filter, and doing the unify twice in two spellings is how the two
/// readings of one field would drift.
fn ctor_field_expected(
    kb: &mut KnowledgeBase,
    ctor_sym: Symbol,
    field_sym: Symbol,
    expected: &Option<Value>,
) -> Option<Value> {
    let exp = expected.as_ref()?;
    let field_types = kb.entity_field_types(ctor_sym)?.to_vec();
    let (_, field_decl) = field_types.iter().find(|(s, _)| *s == field_sym)?;
    let field_decl = field_decl.clone();
    // WI-20260828-5NSZY: the TOTAL belongs-to. WI-946 left `strict_parent_sort` here alone
    // among the belongs-to readers, recording that converting was "the right move the moment
    // a failing test exists" — for an EPONYMOUS parametric sort (`sort Wrap { sort T = ?;
    // entity Wrap(v: T) }`) strict answers `None`, so no hint was pushed, and every probe it
    // had typed bottom-up to the same thing anyway. WI-20260828-2TMB5 supplied that test by
    // making a missing hint a REFUSAL rather than a worse inference: `apply_it(Wrap(inc),
    // 41)` was a hard load error while the `Option`/`some` spelling of the identical program
    // returned 42, and a lambda in the same slot returned 41. Same author-written arrow,
    // three verdicts by spelling.
    let parent_sym = kb.sort_of_constructor(ctor_sym)?;
    let parent_type = kb.make_sort_ref(parent_sym);
    let mut subst = Substitution::new();
    if !unify_types(kb, &mut subst, &TermIdView(parent_type), exp) {
        return None;
    }
    Some(walk_type_deep_value(kb, &subst, &field_decl))
}

/// [`variant_slot_arg_hint`] for a field whose VARIANT type arrives through a type
/// parameter — the one-level-nested case its own gate cannot see.
///
/// `variant_slot_arg_hint` asks [`type_head_names_an_entity`] of the field's DECLARED
/// type. For `entity box(v: T)` that is the type var `T`, which names no entity, so no
/// hint reached the argument and `box(v: red(v: 1))` classified `red(…)` at `Colour` —
/// making `Box[T = Colour.red]` uninhabitable exactly as §8.2's own variant types were
/// before WI-20260826-JSFHG, one level down. Driven: `mk() -> Box[T = Colour.red] =
/// box(v: red(v: 1))` reported *"expected Box[T = red], got Box[T = Colour]"*. Found by
/// `/code-review`.
///
/// SAME CONFINEMENT AS ITS SIBLING, and it is what keeps this from widening anything:
/// gated on the argument being a constructor application, and consulted only AFTER the
/// declared-type hint has declined — so a slot that already had a hint keeps it, and the
/// only arguments whose reading changes are those that had none.
pub(super) fn variant_field_expected_from_ctor(
    kb: &mut KnowledgeBase,
    ctor_sym: Symbol,
    field_sym: Symbol,
    expected: &Option<Value>,
    arg: &Rc<NodeOccurrence>,
) -> Option<Value> {
    if !arg_is_constructor_application(kb, arg) {
        return None;
    }
    let walked = ctor_field_expected(kb, ctor_sym, field_sym, expected)?;
    type_head_names_an_entity(kb, &walked).then_some(walked)
}

/// WI-20260828-5NSZY — [`arrow_slot_arg_hint`] for a field whose ARROW arrives through a
/// type PARAMETER, the one-level-nested case its own gate cannot see. The exact peer of
/// [`variant_field_expected_from_ctor`], walking through the same [`ctor_field_expected`],
/// and gated on the WALKED type rather than the declared one.
///
/// `arrow_slot_arg_hint` asks [`type_head_is_callable`] of the field's DECLARED type. For
/// `entity some(value: T)` that is the type var `T`, which is not callable, so no hint
/// reached the argument. Since WI-20260828-2TMB5 that is not merely a worse message: a bare
/// operation name with no arrow to lift against is REFUSED, because such a value cannot be
/// minted — [`attach_eta_dispatch_dict`] reads the expected arrow to pin both the
/// requirement dictionary and the argument-spread labels, and has nothing to read without
/// one. So the author who wrote `o: Option[T = Function[…]]` had pinned an arrow that never
/// reached the name.
///
/// IT TAKES BOTH HALVES, and this one alone was measured to fire NOWHERE: the walk needs
/// the CONSTRUCTOR's own `expected`, and an op-call argument that is a constructor
/// application was given none unless its parameter type named an ENTITY
/// ([`variant_slot_arg_hint`]'s gate) — `Option[T = …]` names a SORT. See
/// [`ctor_arg_unlocks_an_arrow_for_a_bare_name`], which supplies it.
pub(super) fn arrow_field_expected_from_ctor(
    kb: &mut KnowledgeBase,
    ctor_sym: Symbol,
    field_sym: Symbol,
    expected: &Option<Value>,
    arg: &Rc<NodeOccurrence>,
) -> Option<Value> {
    if !arg_is_bare_operation_name(kb, arg) {
        return None;
    }
    let walked = ctor_field_expected(kb, ctor_sym, field_sym, expected)?;
    type_head_is_callable(kb, &walked).then_some(walked)
}

/// WI-20260828-5NSZY — the OTHER half: may a call's declared parameter type be pushed into
/// a CONSTRUCTOR-APPLICATION argument, because doing so unlocks an ARROW for a bare
/// operation name in one of that constructor's fields?
///
/// THE GATE IS THE WHOLE ANSWER, not a formality. Pushing an expected type where none was
/// pushed before is not neutral for a constructor: `check_constructor_iter` reads it for the
/// §8.2 classification decision (`expected_names_an_entity`, WI-20260826-JSFHG) and seeds it
/// into the build after the field loops (WI-384/WI-270). So this does not push whenever the
/// argument is a constructor, nor whenever it carries a bare name — it performs the walk
/// [`arrow_field_expected_from_ctor`] would perform and pushes only when that walk actually
/// reaches a CALLABLE for a field whose argument IS a bare operation name. The hint
/// therefore fires exactly where it changes the reading it exists to change, and the census
/// of what newly receives one is that same set.
pub(super) fn ctor_arg_unlocks_an_arrow_for_a_bare_name(
    kb: &mut KnowledgeBase,
    arg: &Rc<NodeOccurrence>,
    pt: &Value,
) -> bool {
    let NodeKind::Expr {
        expr:
            Expr::Constructor {
                name,
                pos_args,
                named_args,
                ..
            },
        ..
    } = &arg.kind
    else {
        return false;
    };
    let (ctor, pos_args, named_args) = (*name, pos_args.clone(), named_args.clone());
    // The cheap predicate FIRST: this runs for every constructor-shaped argument of every
    // call that reaches the hint chain, and `entity_field_types(..).to_vec()` allocates.
    // Nothing below can fire unless some argument is a bare operation name.
    if !pos_args
        .iter()
        .chain(named_args.iter().map(|(_, a)| a))
        .any(|a| arg_is_bare_operation_name(kb, a))
    {
        return false;
    }
    let Some(fields) = kb.entity_field_types(ctor).map(|f| f.to_vec()) else {
        return false;
    };
    let exp = Some(pt.clone());
    // THE WALK MUST UNLOCK SOMETHING. A field whose DECLARED type is already callable is
    // [`arrow_slot_arg_hint`]'s (WI-20260828-8Q0Q5), which reads the declaration and needs
    // no `expected` at all — firing here for one of those would push an expected type into a
    // constructor purely to re-derive a hint that already exists, widening what
    // `check_constructor_iter` sees for no reading. MEASURED: without this condition the
    // hint fires on four stdlib call sites (`Stream.splitFirst`, `Iterable.iterator`,
    // `FiniteCollection.collect`) plus `wi8q0q5`'s arrow-field carrier, every one of them an
    // already-arrow field; with it, on nothing but the nested-through-a-parameter shape.
    let unlocks = |kb: &mut KnowledgeBase, field: Symbol, declared: &Value| {
        !type_head_is_callable(kb, declared)
            && ctor_field_expected(kb, ctor, field, &exp)
                .is_some_and(|w| type_head_is_callable(kb, &w))
    };
    // WI-20260827-1F0QP: the field a positional ARGUMENT takes is the same
    // rank-among-NOT-named rule the constructor's build will use
    // (`positional_to_named_plan`), so a MIXED `mk(f, other: 1)` asks about the field
    // `f` will actually land in. Indexing `fields` by slot asked about the wrong
    // declaration whenever a named argument came earlier in the field order.
    let named_syms: SmallVec<[Symbol; 2]> = named_args.iter().map(|(s, _)| *s).collect();
    let decl_syms: SmallVec<[Symbol; 4]> = fields.iter().map(|(s, _)| *s).collect();
    let pos_fields = match KnowledgeBase::rank_positional_among_unnamed(
        &decl_syms,
        |fs| named_syms.contains(&fs),
        pos_args.len(),
    ) {
        PositionalPlan::Assign(f) => Some(f),
        // Over-arity is refused elsewhere; `Skip` cannot arise (this is the explicit
        // field list). Either way there is no ranking to apply — fall back to the slot.
        _ => None,
    };
    for (i, a) in pos_args.iter().enumerate() {
        if arg_is_bare_operation_name(kb, a) {
            let field = match &pos_fields {
                Some(pf) => fields.iter().find(|(fs, _)| *fs == pf[i]).cloned(),
                None => fields.get(i).cloned(),
            };
            if let Some((fs, decl)) = field {
                if unlocks(kb, fs, &decl) {
                    return true;
                }
            }
        }
    }
    for (fname, a) in named_args.iter() {
        if !arg_is_bare_operation_name(kb, a) {
            continue;
        }
        let Some((_, decl)) = fields.iter().find(|(s, _)| s == fname).cloned() else {
            continue;
        };
        if unlocks(kb, *fname, &decl) {
            return true;
        }
    }
    false
}

/// Aggregate sibling errors into one `TypeError`. Flattens nested
/// `Multiple` so the result has a single-level error vec. Single-
/// error fast-path avoids the Vec allocation when one ill-typed
/// sibling is the typical case.
pub(super) fn aggregate_errors(errors: Vec<TypeError>) -> TypeError {
    if errors.len() == 1 && !matches!(errors[0], TypeError::Multiple { .. }) {
        return errors.into_iter().next().unwrap();
    }
    let flat: Vec<TypeError> = errors.into_iter().flat_map(TypeError::flatten).collect();
    if flat.len() == 1 {
        flat.into_iter().next().unwrap()
    } else {
        TypeError::Multiple { errors: flat }
    }
}

/// Aggregate any `Err` entries in `results` into a single `TypeError`.
/// Returns `Ok(())` when every result is `Ok` — callers then proceed
/// to use the sub-results with the invariant that they're all `Ok`.
pub(super) fn collect_arg_errors<'a>(
    results: impl IntoIterator<Item = &'a Result<TypeResult, TypeError>>,
) -> Result<(), TypeError> {
    let errors: Vec<TypeError> = results
        .into_iter()
        .filter_map(|r| r.as_ref().err().cloned())
        .collect();
    if errors.is_empty() {
        Ok(())
    } else {
        Err(aggregate_errors(errors))
    }
}

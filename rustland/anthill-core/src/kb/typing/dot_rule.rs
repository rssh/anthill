//! WI-279 INC2: sort-specific `@[simp]` dot-rule override, and locating the spec
//! operation a dot call on a provided, required or constrained receiver reaches.

use super::*;

// ── WI-279 INC2: sort-specific `@[simp]` dot-rule override ────────────────
//
// A dot rule like `dot_apply(?e, map, ?f) <=> either_map(?e, ?f) @[simp]`
// (declared in a sort) OVERRIDES the default method fallback for receivers
// whose least sort conforms to that sort. A written dot rule LOADS as the
// reflect `Expr.dot_apply` ENTITY (`receiver:` / `name:` / `args:
// List[ApplyArg]`) — a different shape than a surface occurrence's
// `Expr::DotApply` (flattened `pos_args`, `name` as a Symbol field). Rather
// than teach the generic matcher both shapes, this dedicated path scans the
// `@[simp]` dot equations, guards by the rule's enclosing sort (`rule_domain`),
// matches the entity LHS against the occurrence's receiver/args, and
// instantiates the RHS — reusing `simp_rewrite`'s opener + RHS builder. It
// handles a *var* receiver with *positional var* args (the Either-style
// case); a name mismatch, a non-var pattern, a named-arg dot call, or an arity
// mismatch makes it skip the rule, falling through to the default.

/// Fire a sort-specific `@[simp]` dot rule at a DotApply, or `Ok(None)` to fall to
/// the default. `recv_sort` is the receiver's least sort (the firing guard's
/// key); `from` is the DotApply occ (synthesized-RHS provenance).
///
/// WI-902: the RHS is instantiated by the shared
/// [`crate::kb::simp_rewrite::instantiate_rhs`], so a macro-headed dot rule expands at
/// compile time exactly as a macro-headed `Apply` rule does — this site used to
/// stop at the template. `Err` is that macro's REJECTION of the occurrences it was
/// handed, for the caller to report at this redex (WI-757), the same contract as
/// [`fire_simp`].
///
/// WI-903: this site does NOT consult `kb.rule_type_bounds`, and does not have to
/// — a dot rule it fires can carry none. A `?x: T` bound is enforced at one site,
/// the RESOLVER's `apply_eq_rules`, which never sees a `dot_apply` head; the loader
/// therefore refuses the annotation here rather than letting it load and be ignored
/// (`load::TypedPatternRefusal::DotRule`). Adding a second, typer-side enforcer was
/// the alternative and was declined: the typer does not enforce typed bounds
/// anywhere ([`crate::kb::simp_rewrite::try_fire`] skips bound-carrying rules), and a
/// compile-time firing decision keyed on an inferred type would make the rule's
/// reach depend on inference order.
///
/// `rids` are the SAME eq+unify candidates [`fire_simp`] gets — gathered once per
/// typing pass (WI-657(9)) and filtered here by `is_simp_equation`. This site used
/// to re-scan the `eq` bucket alone, per DotApply, behind its own inlined copy of
/// that predicate: a `<=>`-spelled `@[simp]` dot rule was therefore NEVER SEEN, and
/// silently did not fire (MEASURED; WI-646 unified the other three selection sites
/// and missed this one). `@[simp]` is the enablement, the connective is not —
/// `is_equation` accepts both, so selection must too, and 043.1's own macro rules
/// are written `<=>`.
pub(super) fn try_fire_dot_rule(
    kb: &mut KnowledgeBase,
    recv_sort: Symbol,
    member: Symbol,
    receiver: &Rc<NodeOccurrence>,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    from: &Rc<NodeOccurrence>,
    rids: &[RuleId],
) -> Result<Option<Rc<NodeOccurrence>>, crate::kb::simp_rewrite::MacroRejection> {
    // WI-903: hoisted out of the loop, as before — but the selection itself is now
    // `fires_as_dot_rule`, the SAME predicate the loader's typed-bound refusal
    // asks. A third condition added here therefore narrows the refusal with it,
    // instead of silently leaving it wider (this function's WI-902 defect exactly).
    let Some(dot_apply_sym) = crate::kb::simp_rewrite::dot_apply_head_sym(kb) else {
        return Ok(None);
    };
    for &rid in rids {
        if !crate::kb::simp_rewrite::fires_as_dot_rule(kb, rid, dot_apply_sym) {
            continue;
        }
        // Enclosing-sort guard: a dot rule fires only where the receiver's
        // least sort conforms to the rule's defining sort — by identity or spec
        // satisfaction. `rule_domain` IS that sort's symbol (it was a nullary
        // `Fn`/`Ref` term unwrapped here). Do NOT reach for `sort_functor_of` —
        // that is for `sort_ref`-wrapped *type* terms. Without this guard one
        // sort's `map` rule would hijack the member name for every receiver.
        let encl = kb.rule_domain(rid);
        // WI-672 `same_sort_canonical` (not raw `==`): a sort's differently-interned
        // copies share a canonical symbol — match the convention used by `sort_provides`
        // / sort widening. Identity OR spec satisfaction.
        if !same_sort_canonical(kb, recv_sort, encl) && !sort_provides(kb, recv_sort, encl) {
            continue;
        }
        // WI-20260903-FCZ3N: `fresh` is threaded on so `instantiate_rhs` can open this
        // rule's WRITTEN RHS occurrence in the same frame the head term was opened in.
        let Some((lhs, rhs, fresh)) = crate::kb::simp_rewrite::open_equation(kb, rid) else {
            continue;
        };
        if let Some(subst) = match_dot_rule_lhs(kb, lhs, member, receiver, pos_args, named_args) {
            // WI-20260820-8RJK8 — THE THIRD SELECTION SITE, and it needs the guard for
            // the reason it needed `fires_as_dot_rule`: that predicate is
            // `is_simp_equation`, which 8RJK8 widened from "bodyless equation" to
            // "equational head", so a `@[simp]`-tagged GUARDED dot rule reaches this loop
            // now where it could not before. Selecting it and skipping its precondition
            // would fire a conditional rewrite unconditionally — silently, since a
            // wrongly-fired rewrite leaves no diagnostic. Found by `/code-review`; the
            // spec's "both firing sites answer alike" was written from a census of two.
            //
            // NOTHING IN THE CORPUS DRIVES THIS, and that is said here rather than left
            // to a green suite: no guarded dot rule is written anywhere today, so
            // removing this call turns no test red. It is here so that the first author
            // who writes one gets the guard rather than a coincidence.
            let extended;
            let build = match crate::kb::simp_rewrite::guard_verdict(kb, rid, rhs, &fresh, &subst) {
                crate::kb::simp_rewrite::GuardVerdict::NotHeld => continue,
                crate::kb::simp_rewrite::GuardVerdict::HoldsUnchanged => &subst,
                crate::kb::simp_rewrite::GuardVerdict::HoldsWith(s) => {
                    extended = s;
                    &extended
                }
            };
            return crate::kb::simp_rewrite::instantiate_rhs(kb, rid, rhs, &fresh, build, from)
                .map(Some);
        }
    }
    Ok(None)
}

/// WI-281: spec-satisfaction method resolution. When `member` is not declared
/// directly on the receiver's sort, look for it on a spec the receiver's sort
/// *provides* (`fact Spec[Carrier = recv_sort]`): e.g. `(3).min(5)` resolves
/// `min` to `Ord.min` because `Int` provides `Ord`. Returns the spec
/// operation's fully-qualified symbol; the caller synthesizes the same
/// `Apply(op, [receiver, ...args])` as the direct-sort case, so the produced
/// call rides the normal spec-op dispatch + `req_insertion` — the requirement
/// (`Ord[Int]`) is threaded by that machinery, not re-implemented here.
///
/// Walks `SortProvidesInfo` for the specs `recv_sort` provides (mirroring
/// `build_sort_ops_table`'s pass-2 snapshot) and resolves `member` within each
/// spec's scope via `find_operation_in_scope`. First match wins (a member name
/// shared across two provided specs is left for a later disambiguation pass).
pub(super) fn find_spec_op_for_provided_sort(
    kb: &mut KnowledgeBase,
    recv_sort: Symbol,
    short: &str,
) -> Option<Symbol> {
    // Snapshot the provided specs first: the resolution loop below mutates `kb`
    // (`alloc` / `find_operation_in_scope`), so it can't run while iterating.
    let mut spec_syms: Vec<Symbol> = Vec::new();
    let recv_canon = kb.canonical_sort_sym(recv_sort);
    // WI-660: deliberately NOT served by the carrier index. This site matches a
    // provider EITHER by carrier (`same_sort_canonical(carrier, recv_sort)`) OR as a WITNESS
    // (`recv_sort` is the provider's carrier-PARAM value, e.g. `sort TagCombiner
    // provides Combiner[T = Tag]` matched for `recv_sort = Tag`). A witness provider's
    // `sort_ref` is a DIFFERENT sort (`TagCombiner`), so it lives in another carrier
    // bucket — the carrier index's `by_carrier` bucket for `recv_sort` would drop it. Nor is it spec-keyed
    // (it collects EVERY spec `recv_sort` provides). So the full scan is required.
    for row in provides_rows(kb) {
        let spec_sym = row.spec_base;
        // Carrier-keyed: the receiver's sort IS the provider — `(3).min(5)` →
        // `Ord.min` via `fact Ord[Int]`. WI-672: canonical sort identity (see
        // `same_sort_canonical`), not `same_symbol`'s last-segment bridge.
        let carrier_match = same_sort_canonical(kb, row.provider, recv_sort);
        // WI-450 witness: the receiver's sort is the spec's CARRIER-PARAM VALUE of a
        // provider whose `sort_ref` is some OTHER (witness) sort — `tag.combine(t)`
        // → `Combiner.combine` via `sort TagCombiner provides Combiner[T = Tag]`. The
        // dot-call synthesises a `combine(tag, t)` Apply that then value-directs to
        // the witness impl at eval (param-agnostic, like the non-dot call form).
        let witness_match = !carrier_match
            && provision_carrier_sort(kb, spec_sym, &Value::term(row.spec_view))
                .map(|c| kb.canonical_sort_sym(c) == recv_canon)
                .unwrap_or(false);
        if carrier_match || witness_match {
            spec_syms.push(spec_sym);
        }
    }
    // WI-495: a member can live on a TRANSITIVELY-provided spec — `xs.map` on a
    // `List` is `Iterable.map`, reached via `List provides Stream` + `Stream
    // provides Iterable` (List no longer declares `provides Iterable` directly).
    // BFS-expand the directly-provided set with each spec's own provisions; the
    // direct specs stay at the front, so a directly-provided member still wins
    // over a transitively-inherited one (more-specific-first). `same_sort_canonical`
    // dedup guards a cyclic `provides` chain.
    // Track BFS depth alongside each spec: the directly-provided specs are depth 0,
    // each transitive hop +1. Distance is the PRIMARY ordering (direct-before-
    // transitive); depth lets us identify a genuine equal-distance TIE.
    let mut depths: Vec<usize> = vec![0; spec_syms.len()];
    let mut i = 0;
    while i < spec_syms.len() {
        let s = spec_syms[i];
        let d = depths[i];
        for next in directly_provided_specs(kb, s) {
            if !spec_syms.iter().any(|&x| same_sort_canonical(kb, x, next)) {
                spec_syms.push(next);
                depths.push(d + 1);
            }
        }
        i += 1;
    }
    // Collect EVERY provided spec that defines `short`, with its distance.
    let mut definers: Vec<(Symbol, Symbol, usize)> = Vec::new(); // (spec, op, depth)
    for (idx, &spec_sym) in spec_syms.iter().enumerate() {
        let spec_term = kb.alloc(Term::Ref(spec_sym));
        if let Some(op) = crate::kb::load::find_operation_in_scope(kb, spec_term, short) {
            definers.push((spec_sym, op, depths[idx]));
        }
    }
    let min_depth = definers.iter().map(|(_, _, d)| *d).min()?;
    let nearest: Vec<(Symbol, Symbol)> = definers
        .into_iter()
        .filter(|(_, _, d)| *d == min_depth)
        .map(|(s, o, _)| (s, o))
        .collect();
    if nearest.len() == 1 {
        return Some(nearest[0].1);
    }
    // Equal-distance TIE: prefer the requires-REFINEMENT. A spec that
    // (transitively) `requires` every other tied spec is the more specific one,
    // so its operation wins — e.g. `FiniteCollection requires Iterable`, so
    // `FiniteCollection.map`/`filter` beat the lazy `Iterable` ones on a `Map`
    // (which provides BOTH directly, unlike a `List` where Iterable is farther).
    // A genuine ambiguity (no single tied spec requires all the others) keeps the
    // prior first-match behavior. See kernel-language.md §8.7.
    let tied: Vec<Symbol> = nearest.iter().map(|(s, _)| *s).collect();
    if let Some(winner) = most_refined_spec(kb, &tied) {
        if let Some((_, op)) = nearest
            .iter()
            .find(|(s, _)| same_sort_canonical(kb, *s, winner))
        {
            return Some(*op);
        }
    }
    Some(nearest[0].1)
}

/// Among `specs` — all at equal provision-graph distance from a carrier and all
/// defining the same operation short-name — return the one that is the
/// requires-REFINEMENT of all the others: the spec whose (transitive)
/// `requires` chain contains every other listed spec. That spec is the most
/// specific (`FiniteCollection requires Iterable` ⇒ FiniteCollection refines
/// Iterable), so its operation wins the otherwise order-dependent tie. Returns
/// `None` on a genuine ambiguity (no single spec requires all the others).
pub(super) fn most_refined_spec(kb: &mut KnowledgeBase, specs: &[Symbol]) -> Option<Symbol> {
    for &cand in specs {
        let chain = requires_chain(kb, cand);
        if specs.iter().all(|&other| {
            // WI-672 canonical: `specs`/`required_sort` are resolved (stdlib specs
            // qualified; top-level user specs self-consistent — see `entries_cover`).
            same_sort_canonical(kb, other, cand)
                || chain
                    .iter()
                    .any(|e| same_sort_canonical(kb, e.required_sort, other))
        }) {
            return Some(cand);
        }
    }
    None
}

/// WI-614 — dot-dispatch member resolution over the receiver spec's REQUIRES graph: the
/// requires-side analogue of [`find_spec_op_for_provided_sort`] (which walks PROVIDES). A
/// value whose static type is an abstract spec (`FiniteCollection[…]`) can invoke a member of
/// a spec it REQUIRES — `FiniteCollection requires Iterable[C=C, Element=Element, E=E]`, so
/// `.find` / `.isEmpty` / `.iterator` (Iterable-only members) are sound on it: a
/// `FiniteCollection` IS walkable. Dot-dispatch tries the receiver's OWN members (the base
/// `find_operation_in_scope`) and its PROVIDED specs (the first `.or_else`) first; this is the
/// caller's SECOND `.or_else`, gated on `carrier_is_abstract_spec(recv_sort)` so only a
/// spec-typed receiver reaches it (a concrete carrier resolves members via provides). This
/// performs only RESOLUTION — once it returns `Iterable.find`, the synthesized
/// `Iterable.find(receiver, …)` re-types through the carrier-param requires-view path (WI-608)
/// that grounds Iterable's `C`/`Element`/`E` from the `FiniteCollection` receiver.
///
/// CARRIER-PRESERVATION (soundness): only a *carrier-preserving* requires lends its members —
/// one that binds the required spec's carrier to the RECEIVER's own carrier, so a receiver
/// value IS a value of the required spec's carrier (`FiniteCollection requires Iterable[C=C]`).
/// A *constraint-style* requires over an ELEMENT/scalar (`Set requires Eq[T]`, `VectorSpace
/// requires Ring[F]`) binds the required spec's carrier to a NON-carrier param, so `PartialEq.eq(a:
/// element)` must NOT be borrowable on the whole collection — [`requires_edge_is_carrier_preserving`]
/// filters those out (without this, `s.eq(x)` on an abstract `Set` receiver would mis-resolve
/// to `PartialEq.eq`). Walks the ROOT-SCOPED transitive `requires_chain` (bindings composed into
/// `recv_sort`'s vocabulary, so the carrier check is correct at any depth); pre-order keeps
/// direct requires first (nearest), and a genuine multi-spec tie prefers the requires-
/// REFINEMENT via [`most_refined_spec`], as the provides resolver does.
pub(super) fn find_spec_op_for_required_sort(
    kb: &mut KnowledgeBase,
    recv_sort: Symbol,
    short: &str,
) -> Option<Symbol> {
    // Root-scoped transitive requires chain: each entry's `spec` bindings are composed into
    // `recv_sort`'s vocabulary (WI-230), so `requires_edge_is_carrier_preserving` compares the
    // required spec's bound carrier against `recv_sort`'s own carrier correctly at every depth.
    let chain = requires_chain(kb, recv_sort);
    // Collect every CARRIER-PRESERVING required spec that defines `short`, pre-order
    // (direct-before-transitive); dedup by spec so a spec re-reached transitively is kept once
    // (its nearest, pre-order-first occurrence).
    let mut definers: Vec<(Symbol, Symbol)> = Vec::new(); // (spec, op)
    for entry in &chain {
        if !requires_edge_is_carrier_preserving(kb, recv_sort, entry) {
            continue;
        }
        let spec_sym = entry.required_sort;
        if definers
            .iter()
            .any(|(s, _)| same_sort_canonical(kb, *s, spec_sym))
        {
            continue;
        }
        let spec_term = kb.alloc(Term::Ref(spec_sym));
        if let Some(op) = crate::kb::load::find_operation_in_scope(kb, spec_term, short) {
            definers.push((spec_sym, op));
        }
    }
    if definers.len() <= 1 {
        return definers.first().map(|(_, op)| *op);
    }
    // Multi-spec TIE: prefer the requires-REFINEMENT (mirrors the provides resolver).
    let tied: Vec<Symbol> = definers.iter().map(|(s, _)| *s).collect();
    if let Some(winner) = most_refined_spec(kb, &tied) {
        if let Some((_, op)) = definers
            .iter()
            .find(|(s, _)| same_sort_canonical(kb, *s, winner))
        {
            return Some(*op);
        }
    }
    definers.first().map(|(_, op)| *op)
}

/// WI-1119 — is this dot receiver a TYPE PARAMETER declared in the body's scope, and if so
/// what is its type term? The gate on the third member-resolution rung, and on the refusal
/// that names the parameter.
///
/// MEMBERSHIP IN [`TypingEnv::param_rigids`], NOT merely [`is_type_param_value`]: every
/// receiver that reaches this point has no sort head, and a fair share of them are
/// anonymous unification variables — a rule-head variable the goals never constrained
/// (WI-282), a `Value::Node` the typer has not grounded. Those ARE `Term::Var`s, so the
/// coarse predicate admits them, and there is nothing about them to name or constrain: no
/// clause can mention a variable the author never wrote. The rigid list holds exactly the
/// parameters in scope — the enclosing sort's and the operation's own (WI-942) — so it is
/// the precise question, and it is the same list the σ-alignment below bridges through.
///
/// "THE OPERATION'S OWN" INCLUDES A VARIABLE WRITTEN INLINE in a parameter type
/// (WI-1FKR2) — `via(b: Box[?t])`'s `?t` is a type parameter by §5.4 and is in the list.
/// That keeps this gate precise rather than widening it: such a variable IS a parameter a
/// `requires` clause can name and a call can instantiate, which is the property the test
/// is for. What is deliberately kept OUT, so the sentence above stays true, is a VALUE
/// precondition's variable (`requires p(x, ?v)`) — it names no type — and
/// [`inline_signature_type_params`] states at its own site why it does not read the
/// `requires` field to get there.
pub(super) fn constrained_param_receiver_type(
    kb: &KnowledgeBase,
    env: &TypingEnv,
    recv_ty: &Value,
) -> Option<TermId> {
    // A `Value::Node` receiver type carries no `TermId` and so names no parameter: the
    // rigid list is keyed by term, and a denoted type is WI-348 Phase C work.
    let Value::Term { id: tid, .. } = recv_ty else {
        return None;
    };
    let tid = *tid;
    let (vid, _) = elem_var_step(kb, tid)?;
    let canon = canonical_global_var(kb, vid, env.param_rigids());
    env.param_rigids()
        .iter()
        .any(|(g, rigid)| {
            *g == canon || matches!(kb.get_term(*rigid), Term::Var(Var::Rigid(rv)) if *rv == canon)
        })
        .then_some(tid)
}

/// WI-1119 — dot dispatch on a `requires`-CONSTRAINED TYPE-PARAMETER receiver: the third
/// member-resolution rung, beside [`find_spec_op_for_provided_sort`] (the receiver sort's
/// PROVIDES graph) and [`find_spec_op_for_required_sort`] (an abstract-spec receiver's
/// REQUIRES graph). Those two are gated on a resolved `recv_sort`; a type parameter has
/// none, so `x.describe()` inside `operation probe[PT](x: PT) requires Desc[PT]` used to
/// skip the whole ladder and land on `DotDispatchNoMatch{None}` while its own named twin
/// `Desc.describe(x)` loaded and ran. The dot **reaches the same rule** as the named
/// spelling (§8.7 "Operation override"), so what it resolves to here is the spec
/// operation, handed on for the value to decide — and the licence that admits the call is
/// then the named spelling's own ([`op_requires_covers_call`] for the op-scoped clause, the
/// sort-level defer-to-requirement for the sort's). This rung performs RESOLUTION only.
///
/// TWO CHAIN SOURCES, COMPOSED AT ONE READ, because a clause may be written in either
/// scope and the receiver cannot tell which: the enclosing OPERATION's own
/// ([`TypingEnv::op_requires`], §5.4 / proposal 042) and the enclosing SORT's dictionary
/// chain ([`TypingEnv::enclosing_requires`]). MEASURED at the miss: the op-scoped spellings
/// reach the constraining spec through the first and the sort-level one through the second
/// alone, so a rung wired to either half serves two of the three shapes and refuses the
/// third — the defect WI-945 and WI-1098 each record from a different side.
///
/// THE TWO SOURCES NEED DIFFERENT SEED DECODERS, and that is not drift but the established
/// split: an op-scoped clause is stored as the written application (`Desc[PT]`, a plain
/// `Fn`), which [`op_requires_entry_carrier_map`] pairs positionally against the spec's
/// declared params, while a sort-level entry is a `SortView`, whose bindings are named and
/// which [`compose_reached_carrier_map`] decodes — seeded here with an EMPTY parent map,
/// which is the identity, exactly as [`op_requires_covers`]' BFS composes every entry it
/// reaches. Feeding a `SortView` to the positional decoder pairs the spec's first type
/// param with the view's own base (measured: `{Desc.T ↦ Desc}` beside the real
/// `{Desc.T ↦ HT}`), which is why the seeds are picked by the entry's shape.
///
/// THE ALIGNMENT IS [`reached_carrier_matches_call`]'s QUESTION ASKED FROM THE OTHER SIDE:
/// there a chain entry's carrier is σ-matched against a deferred call's carriers; here
/// against the RECEIVER's type. A clause lends its spec's members only where it constrains
/// *this* parameter — `probe[PT, QT](x: PT, y: QT) requires Desc[QT]` must not resolve
/// `x.describe()` off the `QT` clause, which is WI-823's "the clause is keyed on the param
/// it names" read at the dot. WHICH param of the spec the receiver must fill is
/// [`spec_carrier_param_or_sole`]'s answer, the same owner [`requires_edge_is_carrier_preserving`]
/// asks on the sibling rung (WI-1076: two independent "first type param" readers silently
/// disagreed).
///
/// TRANSITIVE, like both siblings and like the licence: `requires Ord[PT]` lends
/// `PartialEq.eq` because `Ord requires Eq requires PartialEq` (WI-644 / proposal 004), and
/// [`op_requires_covers`] already licenses the named spelling of exactly that call. The
/// expansion composes carriers at every hop, so a spec reached over a SIBLING element
/// (`requires Foo[PT]`, `Foo requires Bar[T = Foo.E]`) lands unaligned and lends nothing.
///
/// A TIE IS REFUSED, NOT ORDERED. Two constraining specs declaring one member name are
/// settled first by the §8.7 requires-REFINEMENT rule the sibling rungs use
/// ([`most_refined_spec`] — `FiniteCollection.map` beats `Iterable.map`); a genuine
/// ambiguity is an error naming both, rather than the siblings' first-match. It has to be:
/// those two order their candidates by provision distance / requires pre-order, while a
/// clause on the operation and a clause on its sort have no distance between them at all,
/// so first-match here would let the ORDER THE TWO CLAUSES ARE WRITTEN decide the program's
/// meaning — the very thing §"Where the ambiguity error is raised" refuses.
pub(super) fn find_spec_op_for_constrained_param(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    recv_ty: TermId,
    short: &str,
    call_shape: (usize, usize),
    span: Option<Span>,
) -> Result<Option<Symbol>, TypeError> {
    let definers = constraining_spec_definers(kb, env, recv_ty, short, call_shape);
    if definers.len() <= 1 {
        return Ok(definers.first().map(|(_, op)| *op));
    }
    let tied: Vec<Symbol> = definers.iter().map(|(s, _)| *s).collect();
    if let Some(winner) = most_refined_spec(kb, &tied) {
        if let Some((_, op)) = definers
            .iter()
            .find(|(s, _)| same_sort_canonical(kb, *s, winner))
        {
            return Ok(Some(*op));
        }
    }
    Err(TypeError::AmbiguousConstrainedParamMember {
        span,
        member: kb.intern(short),
        receiver: type_display_name(kb, recv_ty),
        specs: tied,
    })
}

/// WI-1119 — of the specs that constrain the receiver's type parameter, those declaring
/// `short`, paired with the operation each declares. [`find_spec_op_for_constrained_param`]
/// owns the rule; this is the member filter over [`constraining_specs_for_param`]'s walk.
///
/// `call_shape` is the SYNTHESIZED call's `(positional count including the receiver, named
/// count)`. It is used to narrow a MULTI-candidate result and never to empty one: see
/// [`definer_accepts_call_shape`].
pub(super) fn constraining_spec_definers(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    recv_ty: TermId,
    short: &str,
    call_shape: (usize, usize),
) -> Vec<(Symbol, Symbol)> {
    let declaring: Vec<(Symbol, Symbol)> = constraining_specs_for_param(kb, env, recv_ty)
        .into_iter()
        .filter_map(|spec| {
            let spec_term = kb.alloc(Term::Ref(spec));
            crate::kb::load::find_operation_in_scope(kb, spec_term, short).map(|op| (spec, op))
        })
        .collect();
    if declaring.len() <= 1 {
        return declaring;
    }
    // A TIE IS COUNTED ONLY AMONG CANDIDATES THE CALL COULD REACH. Two specs declaring one
    // name are not rivals when only one of them can take this call: `Desc.describe(x: T)`
    // and `Show.describe(x: S, prefix: Int64)` are distinguished by the dot's own argument
    // list, and refusing the pair would both reject a call that is unambiguous and offer a
    // repair (`Show.describe(…)`) that is itself an arity error — which §"Where the
    // ambiguity error is raised" forbids ("the message says to keep exactly one text rather
    // than suggest a spelling that would be refused"). It is also stricter than the
    // shadowing rule this mirrors (WI-1048), whose distinguishability test starts at arity.
    //
    // NARROWS, NEVER EMPTIES: if no candidate fits, the ORIGINAL set stands. A lone definer
    // is never dropped either — an arity mismatch there is the synthesized call's own error
    // to report, and it says what is wrong far better than "no such member" would.
    let applicable: Vec<(Symbol, Symbol)> = declaring
        .iter()
        .copied()
        .filter(|(_, op)| definer_accepts_call_shape(kb, *op, call_shape))
        .collect();
    if applicable.is_empty() {
        declaring
    } else {
        applicable
    }
}

/// WI-1119 — could `op` be the callee of a dot synthesized with `pos` positional arguments
/// (the receiver among them) and `named` named ones? Exact, because the language has no
/// default parameter values — a declaration is refused the `= Type` form on its type params
/// (WI-850) and has no value-level counterpart — so a call supplies every declared parameter
/// exactly once.
///
/// Answers TRUE when it cannot tell (no operation record). This predicate only narrows a
/// tie, and a wrong `false` would drop a real candidate and change which implementation
/// runs; a wrong `true` merely leaves the tie to be refused as before.
fn definer_accepts_call_shape(
    kb: &KnowledgeBase,
    op: Symbol,
    (pos, named): (usize, usize),
) -> bool {
    lookup_operation_info_full(kb, op).is_none_or(|info| info.params.len() == pos + named)
}

/// WI-1119 — every spec constraining the receiver's type parameter, in source order (the
/// enclosing operation's own clauses, then its sort's, each expanded transitively over the
/// requires graph with carriers composed at every hop). Deduplicated by spec.
///
/// SPLIT FROM THE MEMBER FILTER because the two readers ask it differently: the resolution
/// wants the specs declaring one member, while `DotDispatchNoMatch` must name the specs
/// that were SEARCHED — including every one that declares nothing, which is exactly the set
/// that makes "these constrain it and none declares that member" a usable sentence.
pub(super) fn constraining_specs_for_param(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    recv_ty: TermId,
) -> Vec<Symbol> {
    // σ has no per-call substitution to chase here: the receiver's type is already the
    // body's own, so the whole bridge is `param_rigids` (written `Var::Global` ↔ body
    // `Var::Rigid`). An empty `Substitution` is that context, not a stand-in for a missing
    // one — `sigma_class` reads it only to chase bindings a call would have made.
    let subst = Substitution::new();
    let ctx = SigmaCtx {
        subst: &subst,
        param_rigids: env.param_rigids(),
    };
    // BFS state, exactly [`op_requires_covers`]': (spec, {spec's type-param ↦ carrier in
    // the BODY's scope}). Grown by index rather than popped so the walk stays in source
    // order — which spec a tie NAMES is then stable across runs.
    type State = (Symbol, SmallVec<[(Symbol, TermId); 2]>);
    let mut states: Vec<State> = Vec::new();
    for e in env.op_requires().to_vec() {
        states.push((
            kb.canonical_sort_sym(e.required_sort),
            op_requires_entry_carrier_map(kb, &e),
        ));
    }
    for e in env.enclosing_requires().to_vec() {
        states.push((
            kb.canonical_sort_sym(e.required_sort),
            compose_reached_carrier_map(kb, &[], &e),
        ));
    }
    let mut constraining: Vec<Symbol> = Vec::new();
    let mut i = 0;
    while i < states.len() {
        let (cs, map) = states[i].clone();
        i += 1;
        // Does this constraint range over the RECEIVER — is the receiver's type what fills
        // the spec's carrier param? A spec whose carrier goes somewhere else constrains a
        // SIBLING element and not this receiver (`Set requires Eq[T]` constrains the
        // element), so it lends nothing; its own requires are still expanded below, since a
        // spec it requires may bind its carrier here.
        //
        // [`spec_carrier_param_or_sole`], the WI-1102 owner of "WHICH type parameter of
        // this spec the carrier goes in" — the question actually being asked. An earlier
        // draft used rung 1 alone ([`spec_carrier_param`], "a param some declared operation
        // RECEIVES on") on the argument that only a receiving spec can lend a member. That
        // is true of RESOLUTION and false of this walk, which the refusal ALSO reads to name
        // what constrains the parameter: a spec no operation receives on still constrains
        // it, and dropping it here made `requires Zeroed[PT]` report "no `requires` clause
        // constrains it" at a program that wrote one — telling the author to add the clause
        // they had written. The two questions are separated where they belong, at the member
        // filter in [`constraining_spec_definers`].
        if let Some(carrier_param) = spec_carrier_param_or_sole(kb, cs) {
            let bound = binding_for_param(kb, &map, carrier_param, BindingKeyMatch::Label).copied();
            if bound.is_some_and(|v| sigma_pair_precise(kb, &ctx, v, recv_ty))
                && !constraining.iter().any(|s| same_sort_canonical(kb, *s, cs))
            {
                constraining.push(cs);
            }
        }
        for reached in direct_requires_chain(kb, cs) {
            let composed = compose_reached_carrier_map(kb, &map, &reached);
            let next = (kb.canonical_sort_sym(reached.required_sort), composed);
            // Dedup on the FULL state, [`op_requires_covers`]' rule: a spec re-reached
            // under a DIFFERENT carrier is a different constraint and must be re-explored.
            if !states.contains(&next) {
                states.push(next);
            }
        }
    }
    constraining
}

/// WI-614 — is `recv_sort requires <entry>` CARRIER-PRESERVING: does it bind the required
/// spec's carrier to `recv_sort`'s OWN carrier, so a `recv_sort` value can serve as the
/// required spec's self-receiver? Carrier-preserving requires (refinements) lend their members
/// (`FiniteCollection requires Iterable[C = C]` — Iterable's carrier `C` ↦ FiniteCollection's
/// carrier `C`); constraint-style requires over an element/scalar do NOT (`Set requires Eq[T]`
/// binds `Eq`'s carrier to Set's ELEMENT, so `PartialEq.eq`/`neq` compare elements, not Sets).
///
/// A SELF-REPRESENTING receiver (`Set`/`Map`, whose members take `s: Set` — the carrier is the
/// spec itself, with the type-params as elements) has no carrier PARAM for a required spec to
/// bind to, so every requires it carries is constraint-style ⟹ rejected. A CARRIER-PARAM
/// receiver (`FiniteCollection`, members take `c: C`) preserves the carrier iff the required
/// spec's carrier binds to its carrier param — and WHICH parameter that is has one owner,
/// [`spec_carrier_param`], asked here and by [`provision_carrier_binding`] on the other
/// side of the comparison (WI-1076). Both sides used to read "the first type-param"
/// independently; when the provides side stopped, a receiver declaring its element first
/// (`sort Coll { sort Element = ?; sort C = ?; operation get(c: C) }`) would have compared
/// `Element` against the required spec's `C` and silently judged a carrier-preserving edge
/// constraint-style, lending none of the required spec's members.
pub(super) fn requires_edge_is_carrier_preserving(
    kb: &KnowledgeBase,
    recv_sort: Symbol,
    entry: &RequiresEntry,
) -> bool {
    if spec_is_self_representing(kb, recv_sort) {
        return false;
    }
    let Some(s_carrier) = spec_carrier_param(kb, recv_sort) else {
        return false;
    };
    provision_carrier_sort(kb, entry.required_sort, &entry.spec)
        .is_some_and(|bound| same_sort_canonical(kb, bound, s_carrier))
}

/// WI-614 — is `sort_sym` SELF-REPRESENTING: does any declared operation take the sort ITSELF
/// as a self-receiver parameter (`Set.insert(s: Set, …)`, `Stream.head(s: Stream)`)? A
/// self-representing spec's carrier is the spec, not a type-param; a carrier-parameter spec
/// (`FiniteCollection.collect(c: C)`) takes its carrier param instead and answers `false`.
/// ([`self_receiver_param_index`] matches a param typed as the sort itself — exactly the
/// self-representing shape — so any hit means self-representing.)
pub(super) fn spec_is_self_representing(kb: &KnowledgeBase, sort_sym: Symbol) -> bool {
    crate::kb::op_requirements::operations_of_sort(kb, sort_sym)
        .iter()
        .any(|&op| {
            lookup_operation_info_full(kb, op)
                .and_then(|info| self_receiver_param_index(kb, &info.params, sort_sym))
                .is_some()
        })
}

/// WI-411 — redirect an UNQUALIFIED self-named spec-op call inside a provider's OWN
/// impl to the spec op, so it value-dispatches on the receiver's carrier instead of
/// statically self-dispatching to the enclosing impl.
///
/// Inside `MappedStream.splitFirst`'s body, `splitFirst(src)` resolves (at load, by
/// scope chain) to the enclosing member `MappedStream.splitFirst`, shadowing the spec
/// op `Stream.splitFirst` — the typer would then treat it as a direct concrete call
/// and never dispatch, so at eval a `List` source's value hits `MappedStream`'s
/// `case mapped` arm and fails. The dot form `src.splitFirst` already resolves
/// type-directed via [`find_spec_op_for_provided_sort`]; this brings the unqualified
/// function-call form into line. Returns the spec op `Spec.<op>` when ALL hold:
///   * there is an enclosing sort and `fn_sym` is ITS OWN member (`parent ==
///     enclosing`) — a qualified `Stream.splitFirst` already names the spec op
///     (`parent != enclosing`), so it is untouched;
///   * the call has a positional receiver whose static type is NOT that enclosing
///     carrier. A receiver that IS the enclosing carrier (a concrete same-sort
///     self-recursion such as `FilteredStream`'s `splitFirst(filtered(...))`) keeps
///     its static self-call — the receiver's type already singles out the impl, so
///     the spec-op dispatch would only `PinNow` back to it, and keeping the direct
///     call leaves the WI-424 same-sort seeding / WI-413 effect threading untouched;
///   * the enclosing sort `provides Spec` and `Spec` declares an op of the same short
///     name (the spec op, distinct from `fn_sym`).
/// The existing spec-op dispatch then resolves the impl by the receiver's static type
/// (`PinNow` for a concrete carrier, `DeferToRequirement` / value-directed for an
/// abstract `Stream` receiver) — exactly what the qualified `Stream.splitFirst` form
/// already produces.
///
/// The receiver is taken as the FIRST positional argument's type (`recv_ty`) — the
/// self-receiver in every spec op the stdlib overrides. This heuristic governs only
/// the redirect DECISION; the downstream dispatch finds the real receiver via
/// `self_receiver_param_index`, so a future spec op whose self-receiver is not the
/// first positional arg would only mis-decide redirect-vs-static, never corrupt the
/// dispatch. `recv_ty` is read carrier-agnostically and only after the cheap
/// enclosing-member gate, so the common (non-self-member) call pays nothing.
pub(super) fn redirect_provider_self_spec_op(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    fn_sym: Symbol,
    recv_ty: Option<&Value>,
) -> Option<Symbol> {
    let enclosing = env.enclosing_sort()?;
    let parent = impl_parent_of_op(kb, fn_sym)?;
    if kb.canonical_sort_sym(parent) != kb.canonical_sort_sym(enclosing) {
        return None;
    }
    // Receiver IS the enclosing carrier (concrete same-sort) → keep the static self-
    // call. `None` (an abstract / type-var receiver) falls through to the redirect,
    // which is the value-dispatch case the ticket targets. Computed AFTER the gate
    // above so the type-head read is skipped for the common non-self-member call.
    let recv_sort = recv_ty.and_then(|ty| sort_functor_of_view(kb, ty));
    if recv_sort.is_some_and(|rs| kb.canonical_sort_sym(rs) == kb.canonical_sort_sym(enclosing)) {
        return None;
    }
    let short = short_name_of(kb.local_name_of(fn_sym)).to_string();
    let spec_op = find_spec_op_for_provided_sort(kb, enclosing, &short)?;
    (spec_op != fn_sym).then_some(spec_op)
}

/// Match a reflect `dot_apply(receiver:, name:, args:List[ApplyArg])` rule LHS
/// against a DotApply occurrence's parts, binding the LHS's logical vars to the
/// (typed) receiver / arg occurrences. Handles a *var* receiver and *positional
/// var* args; returns `None` (skip → default) for a name mismatch, a non-var
/// pattern, a named-arg dot call, or an arity mismatch.
fn match_dot_rule_lhs(
    kb: &KnowledgeBase,
    lhs: TermId,
    member: Symbol,
    receiver: &Rc<NodeOccurrence>,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Option<Substitution> {
    if !named_args.is_empty() {
        return None; // named-arg dot calls: follow-up
    }
    let la = match kb.get_term(lhs) {
        Term::Fn { named_args, .. } => named_args.clone(),
        _ => return None,
    };
    let r_pat = get_named_arg(kb, &la, "receiver")?;
    let name_t = get_named_arg(kb, &la, "name")?;
    let args_t = get_named_arg(kb, &la, "args")?;
    // Member name — compared by short name, robust to interning differences
    // between the rule's `name:` field and the occurrence's member symbol.
    let rule_name = view_ref_symbol(kb, &TermIdView(name_t))?;
    if short_name_of(kb.local_name_of(rule_name)) != short_name_of(kb.local_name_of(member)) {
        return None;
    }
    let val_pats = collect_positional_arg_value_pats(kb, args_t)?;
    if val_pats.len() != pos_args.len() {
        return None;
    }
    let mut subst = Substitution::new();
    bind_var_pattern_to_node(&mut subst, kb, r_pat, receiver)?;
    for (pat, occ) in val_pats.iter().zip(pos_args.iter()) {
        bind_var_pattern_to_node(&mut subst, kb, *pat, occ)?;
    }
    // A non-linear LHS (a var repeated across receiver/args) implies an
    // equality constraint: `bind_value` flags a contradiction when the same
    // var is bound to two structurally-distinct occurrences. Honour it (the
    // generic `try_fire` does the same) — else the rule would fire unsoundly,
    // dropping the equality the pattern demanded.
    if subst.is_contradiction() {
        return None;
    }
    Some(subst)
}

/// Bind a logical-var pattern term to an occurrence as a `Value::Node` (so the
/// RHS builder substitutes the typed occurrence in). `None` for a non-var
/// pattern — the caller then skips the rule (constructor-pattern receivers are
/// a follow-up).
fn bind_var_pattern_to_node(
    subst: &mut Substitution,
    kb: &KnowledgeBase,
    pat: TermId,
    occ: &Rc<NodeOccurrence>,
) -> Option<()> {
    match kb.get_term(pat) {
        Term::Var(Var::Global(vid)) => {
            subst.bind_value(kb, *vid, Value::Node(Rc::clone(occ)));
            Some(())
        }
        _ => None,
    }
}

/// Collect a dot rule's positional arg value-patterns from its reflect
/// `args: List[ApplyArg]` field (`cons(head: ApplyArg(name: none, value: pat),
/// tail: …)` … `nil`). `None` (→ rule skipped) if the list is malformed or any
/// ApplyArg is named (`name: some(…)`) — named dot-rule args are a follow-up.
fn collect_positional_arg_value_pats(kb: &KnowledgeBase, args_t: TermId) -> Option<Vec<TermId>> {
    let mut out = Vec::new();
    // `list_to_vec` walks the `cons(head, tail) … nil` spine; each element is an
    // `ApplyArg(name: <none/some>, value: <pat>)`.
    for elem in list_to_vec(kb, args_t) {
        let aargs = match kb.get_term(elem) {
            Term::Fn {
                functor,
                named_args,
                ..
            } if short_name_of(kb.local_name_of(*functor)) == "ApplyArg" => named_args.clone(),
            _ => return None,
        };
        // Positional only: `name` must be `none()` (a named arg is `some(...)`).
        let name_t = get_named_arg(kb, &aargs, "name")?;
        let name_functor = match kb.get_term(name_t) {
            Term::Fn { functor, .. } => *functor,
            // WI-511: the nullary `none()` constructor canonicalizes to `Ref(none)`.
            Term::Ref(s) => *s,
            _ => return None,
        };
        if short_name_of(kb.local_name_of(name_functor)) != "none" {
            return None; // named arg → follow-up
        }
        out.push(get_named_arg(kb, &aargs, "value")?);
    }
    Some(out)
}

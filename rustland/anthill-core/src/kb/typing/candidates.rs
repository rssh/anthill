//! Provider candidates for a goal: collecting, matching against the goal, choosing the
//! most specific, and their sub-goals.

use super::*;

/// WI-508: distinct carrier sorts that `provides` `spec_sort` (canonical,
/// deduped, the spec sort itself excluded). Used to resolve a nullary
/// carrier-only-in-result spec op (`new()`) from a UNIQUE provider when the call
/// site pins no carrier. Mirrors `spec_has_any_providers`' indexed walk.
pub(crate) fn impl_sorts_providing_spec(kb: &KnowledgeBase, spec_sort: Symbol) -> Vec<Symbol> {
    let mut out: Vec<Symbol> = Vec::new();
    let spec_canon = kb.canonical_sort_sym(spec_sort);
    // WI-660: the spec-base bucket (built index) or the full scan (pre-build); the
    // `canonical_sort_sym` filter below is a no-op for the bucket (already keyed by
    // canonical spec-base) and the real filter for the scan — one loop body serves both.
    for rid in provides_rids_by_spec(kb, spec_canon) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(head_named) = kb.fact_head_named_args(rid) else {
            continue;
        };
        let Some(sort_ref_tid) = get_named_arg(kb, &head_named, "sort_ref") else {
            continue;
        };
        let Some(spec_view_tid) = get_named_arg(kb, &head_named, "spec") else {
            continue;
        };
        let Some((view_base_sym, _)) = unwrap_spec_view(kb, spec_view_tid) else {
            continue;
        };
        if kb.canonical_sort_sym(view_base_sym) != spec_canon {
            continue;
        }
        let impl_sort = match kb.get_term(sort_ref_tid) {
            Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => *functor,
            _ => continue,
        };
        let carrier = kb.canonical_sort_sym(impl_sort);
        if carrier != spec_canon && !out.contains(&carrier) {
            out.push(carrier);
        }
    }
    out
}

/// WI-508: resolve a NULLARY spec op (carrier only in the result, e.g.
/// `MutableCollection.new() -> C`) to its concrete impl op when value-directed
/// dispatch found no candidate (the carrier is not pinned by any argument).
///
/// Priority:
/// - (a) the EXPECTED RETURN TYPE names a concrete carrier sort ⇒ that carrier
///   is PINNED; use its override (or give up — never silently pick a different
///   provider for an explicitly named carrier);
/// - (b) no carrier pinned and exactly ONE sort provides the spec ⇒ use it
///   (information hiding);
/// - (c) no carrier pinned and 2+ providers ⇒ `Ambiguous` (a loud error).
///
/// `None` keeps the caller's `NoCandidates` (no provider; a named carrier that
/// does not provide the spec; or a provider whose nullary override needs a
/// dispatch dict — see `nullary_carrier_impl_op`).
pub(super) fn resolve_nullary_result_carrier(
    kb: &mut KnowledgeBase,
    spec_sort: Symbol,
    spec_op_sym: Symbol,
    op_short_sym: Symbol,
    resolved_ret: &Value,
) -> Option<DispatchOutcome> {
    let spec_canon = kb.canonical_sort_sym(spec_sort);
    // (a) A concrete (non-type-param) carrier named by the expected return type
    // is PINNED: resolve through it exclusively. A still-abstract return (the
    // spec's own carrier param, e.g. an unannotated `let x = new()`) falls
    // through to the provider-count path below.
    if let Some(base) = carrier_sort_of_value(kb, resolved_ret) {
        if !is_sort_param_symbol(kb, base) {
            let carrier = kb.canonical_sort_sym(base);
            if carrier != spec_canon {
                return if sort_provides(kb, carrier, spec_sort) {
                    nullary_carrier_impl_op(kb, carrier, spec_op_sym, op_short_sym)
                        .map(DispatchOutcome::Unique)
                } else {
                    None
                };
            }
        }
    }
    // (b)/(c) No carrier pinned — unique provider, else ambiguous.
    let providers = impl_sorts_providing_spec(kb, spec_sort);
    match providers.as_slice() {
        [] => None,
        [one] => nullary_carrier_impl_op(kb, *one, spec_op_sym, op_short_sym)
            .map(DispatchOutcome::Unique),
        // WI-843: the SECOND `Ambiguous` producer, and it names its own candidates
        // — these are the providers THIS path counted (`impl_sorts_providing_spec`,
        // no goal to match against), so reusing `resolve_inner`'s list here would
        // report a set nothing on this path consulted. Always `at_call_goal`: this
        // path resolves the CALL's own nullary dispatch, with no sub-resolution.
        many => Some(DispatchOutcome::Ambiguous(InstanceTie {
            spec: spec_sort,
            candidates: many.iter().copied().collect(),
            at_call_goal: true,
            // Always `at_call_goal`, so there is no enclosing provider and no slot.
            slot: None,
        })),
    }
}

/// WI-508 helper: a carrier's RUNNABLE override of a nullary spec op, usable via
/// a plain PinNow redirect. `None` when the carrier does not override the op
/// (the body-less spec op is returned), or when the resolved op's OWN defining
/// sort declares `requires` — such an op would be classified `ConcreteApplyWithin`
/// (needing a dispatch dict) by the `Unique` arm, which this nullary path does
/// not build; it falls through to the caller's existing diagnostic rather than
/// emit a dict-less classification eval can't honor.
///
/// The requires-check keys on `impl_parent_of_op(impl_op)`, NOT on `carrier`, to
/// mirror the `Unique` arm's own PinNow-vs-`ConcreteApplyWithin` decision. They
/// coincide when the carrier overrides the op (the op's parent IS the carrier),
/// but diverge for an INHERITED defaulted op (`build_sort_ops_table` pass 2
/// records an intermediate spec's runnable default for a non-overriding carrier):
/// a requires-bearing default on a requires-free carrier would otherwise slip a
/// carrier-only check and reach a dict-less `ConcreteApplyWithin`.
fn nullary_carrier_impl_op(
    kb: &mut KnowledgeBase,
    carrier: Symbol,
    spec_op_sym: Symbol,
    op_short_sym: Symbol,
) -> Option<Symbol> {
    let impl_op = kb.sort_ops_lookup(carrier, op_short_sym)?;
    if impl_op == spec_op_sym || !op_has_runnable_body(kb, impl_op) {
        return None;
    }
    impl_parent_of_op(kb, impl_op)?;
    // WI-869: the DICTIONARY chain (`op_reads_requirement_slots`), which is the same
    // question the two `classify_pin_or_apply_within` sites ask — "would this callee
    // read requirement slots this path cannot fill". A sort whose only requirements are
    // its provisions' conditions declares no `requires` at all, so the old spelling
    // said "no slots" and this path handed back a dict-less classification for a body
    // that reads them.
    if op_reads_requirement_slots(kb, impl_op) {
        return None;
    }
    Some(impl_op)
}

/// WI-1110 — the impl sorts [`collect_provides_candidates`] offers for `goal`, in the
/// order it offers them.
///
/// A DIAGNOSTIC READER, and the ticket that added it could not be measured without one:
/// its defect was a candidate that should never have been offered, and cycle detection
/// rejected that candidate afterwards, so every observable outcome — the load verdict,
/// the resolved tree, the error text — was IDENTICAL with and without it. The only place
/// the difference exists is this list. Carries no policy of its own: it is
/// `collect_provides_candidates` with the head-only match (`sigma = None`), projected to
/// the impl symbol.
pub fn dispatch_candidate_impl_sorts(kb: &mut KnowledgeBase, goal: &SortGoal) -> Vec<Symbol> {
    collect_provides_candidates(kb, goal, None)
        .into_iter()
        .map(|c| c.impl_sort)
        .collect()
}

/// WI-1111 — HOW FAR THIS SEARCH REACHES, reviewed and recorded so the next reader does
/// not re-derive it. The question was whether a goal answerable only through a CHAIN of
/// parametrized `requires` and `provides` edges is found, and found at the right bindings.
///
/// ONE HOP, DELIBERATELY, because the OTHER hops are materialized rather than searched.
/// This function matches the goal against `SortProvidesInfo` rows whose spec base equals
/// the goal's; multi-hop reach comes from [`derive_forwarded_provisions`], which walks the
/// forwarding tower at load time and asserts a DIRECT row per carrier per floor. Depth is
/// therefore free — the bounded fixpoint doubles its reach per round, and three floors
/// settle in two. What WI-1111 measured and fixed was that the materialization was
/// narrower than the exclusion it justifies:
///
///   * A RENAMING or PERMUTING forwarding (`provides Sp[X = A]`, `provides Sp[X = B,
///     Y = A]`) derived NOTHING, because the pass copied bindings instead of translating
///     them — and, not being an identity forwarding, was not a conversion either, so the
///     FORWARDER was offered as the `impl_sort` for every `Sp` goal (its own parameters
///     being wildcards, the permuting form answered the MIRRORED goal too). The program
///     loaded clean and died at eval. [`forwarding_param_map`] now translates.
///   * A DERIVED SPEC-TO-SPEC ROW from a two-floor tower escaped the skip below, because
///     the chain deliberately holds no entry for a derived row. The second skip asks it
///     through its ORIGIN edge.
///   * AN OPLESS MULTI-PARAMETER FLOOR was never classified a conversion, because
///     [`provision_is_conversion`]'s conjunct 2 read `spec_carrier_param_or_sole(..) ==
///     None` as "self-representing" when it also means "no operation names a carrier and
///     there is not exactly one parameter to be it". Split there.
///
/// THE CALLER'S OWN CHAIN IS A SEPARATE ROUTE and needed nothing: `ResolutionScope::
/// available_requires` plus the Strategy 1/2/3 projection search composes across more than
/// one hop of parametrized `requires` and meets this route at the end, including when the
/// last link is a conversion. Driven by `a_two_hop_requires_chain_reaches_the_provider`
/// and `a_requires_chain_ending_in_a_conversion_reaches_the_provider`, whose answers
/// discriminate between two carriers rather than merely arriving.
///
/// WHAT A GOAL WITH NO ANSWER GETS is an EMPTY candidate list, and the refusal built on it
/// names the spec and the binding (`no impl provides …; `Other` provides no …`) — not a
/// cycle, and not an unrelated missing requirement. One caveat, and it is not this
/// function's: a spec-op call at a CONCRETE receiver written in a sort that declares no
/// `requires` is unchecked at load whatever this list says, so it loads clean and traps at
/// eval (WI-1110's shape A; WI-879 owns it). `the_direct_call_mask_is_not_this_tickets`
/// pins it.
pub(super) fn collect_provides_candidates(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    // WI-827: the call-site σ (`ResolutionScope.sigma`), threaded through so a
    // per-call element is classified by its σ-role (rigid / wildcard /
    // concrete) not its surface spelling. `None` keeps the head-only match.
    sigma: Option<&SigmaCtx>,
) -> Vec<Candidate> {
    let spec_canon = kb.canonical_sort_sym(goal.spec_sort);
    // WI-660: the spec-base bucket (built index) or the full scan. The bucket keys on
    // `canonical_sort_sym(base)`, and the filter below compares canonically too — see
    // there. Owned `Vec` — the loop below borrows `kb` mutably.
    let candidates = provides_rids_by_spec(kb, spec_canon);
    // Spec's type-param short names — hoisted out of the candidate
    // loop so the inner binding-walk just does a string membership
    // check instead of format!+resolve+sort-alias per binding.
    let type_param_names: Vec<String> = kb.type_params_of_sort(goal.spec_sort);

    // WI-714 (proposal 052): transitive-carrier acceptance (below) is a FALLBACK,
    // enabled only when the carrier does NOT directly provide the spec. A carrier
    // that BOTH directly and transitively provides `Stream` — `List provides Stream`
    // AND `List provides FiniteStream provides Stream` — must keep resolving to its
    // DIRECT impl; broadening unconditionally matched both and regressed to
    // `Ambiguous` (wi357). A `Relation` provides `Stream` ONLY through the chain
    // `Relation provides LogicalStream provides Stream` (no direct fact), so the
    // fallback fires exactly for it. Computed once (immutable) before the mutable
    // candidate loop.
    let carrier_directly_provides = goal
        .carrier
        .as_ref()
        .is_some_and(|c| provider_spec_view_bindings(kb, c.sort, goal.spec_sort).is_some());

    let mut out: Vec<Candidate> = Vec::new();
    for rid in candidates {
        if !kb.is_fact(rid) {
            continue;
        }
        // A value-fact SortProvidesInfo (denoted-bearing spec) is skipped from
        // dispatch-candidate collection; occurrence-based dispatch is gated
        // effect-expressions-as-types work (avoid the term-only `rule_head`
        // panic on a value head).
        let Some(head_named) = kb.fact_head_named_args(rid) else {
            continue;
        };
        let sort_ref_tid = match get_named_arg(kb, &head_named, "sort_ref") {
            Some(t) => t,
            None => continue,
        };
        let spec_view_tid = match get_named_arg(kb, &head_named, "spec") {
            Some(t) => t,
            None => continue,
        };
        let impl_sort = match kb.get_term(sort_ref_tid) {
            Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => *functor,
            _ => continue,
        };
        let Some((view_base_sym, view_bindings)) = unwrap_spec_view(kb, spec_view_tid) else {
            continue;
        };
        // BY CANONICAL SORT, not raw symbol (WI-20260923-N3W68 #10). The raw `!=` this was
        // justified itself in one direction only — raw-equal ⟹ canonical-equal ⟹ in the
        // bucket, so no provider is missed BY THE BUCKET — and said nothing of the other: a
        // provision whose `SortView` base was resolved in another import scope is in the
        // canonical bucket and was then dropped HERE, the silent no-op
        // `provider_spec_view_bindings` warns a raw `==` makes. MEASURED unreachable before
        // the change (a probe on "canonical-equal, raw-different" fired zero times across
        // the workspace suite), so this is the reader agreeing with its bucket and with
        // `provider_spec_view_bindings`, not a program newly served.
        if !same_sort_canonical(kb, view_base_sym, goal.spec_sort) {
            continue;
        }
        // WI-1110 — A CONVERSION IS NOT A PROVIDER. `Ord provides WeakOrd[T = T]` says
        // "hold an `Ord[T]` and you can obtain a `WeakOrd[T]`"; it does not say anything
        // has type `Ord`, and nothing ever will. Offering it here made `Ord` an answer to
        // every `WeakOrd` goal — MEASURED on the shipped tree, `WeakOrd[T = Int64]`
        // returned `[Ord, Int64]` and `WeakOrd[T = <rigid>]` returned `[Ord]` ALONE — so
        // every ordering goal at a real carrier carried a spurious second candidate
        // eliminated only by cycle detection running and failing, and at an abstract
        // element the only candidate offered was one that cannot answer.
        //
        // NOT A LOST ANSWER, A RELOCATED ONE: the row's carriers get their own direct
        // provision materialized by [`derive_forwarded_provisions`], whose predicate is
        // strictly wider than [`provision_is_conversion`] — so `Int64 provides WeakOrd`
        // exists as a fact and answers the goal `Ord` used to be offered for.
        //
        // The `goal.carrier = Some(..)` route (a VALUE dispatching a spec op, which
        // reaches `LogicalStream provides Stream` deliberately — WI-714 / WI-495 /
        // WI-496) is out of reach here rather than exempted: a conversion's target has a
        // carrier PARAMETER by construction, and a spec with one is not the
        // self-representing kind a value's static type dispatches through.
        //
        // A SKIP AT TWO READERS, NOT A CHANGE TO THE RELATION. The conversion stays a
        // live `SortProvidesInfo` fact — it has to, because `derive_forwarded_provisions`
        // reads it to materialize each carrier's row — so every OTHER reader still sees
        // it. MEASURED on the shipped tree rather than reasoned about, because a review
        // raised it as a hole and the measurement says something more precise:
        //
        //   sort_provides(Ord, WeakOrd)          = true
        //   sort_provides(Eq, PartialEq)         = true
        //   sort_ops_lookup(Ord, "compare")      = anthill.prelude.WeakOrd.compare
        //   sort_ops_lookup(Eq,  "eq")           = anthill.prelude.PartialEq.eq
        //
        // Every one of those is the RIGHT answer, and it is right for the conversion's
        // own reason: "hold an `Ord[T]` and you can obtain a `WeakOrd[T]`" is exactly
        // what "Ord provides WeakOrd, and `compare` is reachable through it" says. These
        // readers are not being fooled; they are reading the edge correctly. What they
        // cannot do is TELL a conversion from a membership claim — which only the two
        // readers below need to, one because a conversion can answer no goal (nothing
        // has type `Ord`) and one because its obligations belong to the eventual carrier.
        //
        // So the limitation is narrower than "patched readers": a FUTURE reader that
        // needs the distinction must be taught it here as these two were, because the
        // relation does not carry it. The finished shape marks the ROW (as
        // `mark_derived_provision` marks a derived one) so the relation itself
        // distinguishes a conversion. That is a change to the provision relation's
        // schema, and this ticket already moves the dictionary layout twice. WI-1111 owns
        // it, together with the prior question of whether this skip is needed at all once
        // a self-supplied slot is a projection rather than a search — see
        // [`SupplySource`].
        if is_conversion_edge_at(kb, impl_sort, view_base_sym, &view_bindings) {
            continue;
        }
        // WI-1111 — AND A DERIVED ROW IS A CONVERSION WHEN THE EDGE IT WAS DERIVED
        // THROUGH IS ONE. A two-floor tower (`Top provides Mid[T = T]`,
        // `Mid provides Low[T = T]`) makes [`derive_forwarded_provisions`] assert
        // `Top provides Low[T = T]` — a row whose carrier is a SPEC and whose shape is a
        // conversion's, which the skip above cannot see: [`self_supplied_entries`]
        // deliberately reads no derived row back into the chain (it would give `Top` a
        // second slot for a dictionary already reachable inside its first), so
        // [`chain_has_conversion`] answers `false` for exactly these.
        //
        // MEASURED, and it is WI-1110's headline defect one floor up: `Low[T = Car,
        // E = Bool]` offered `["Top", "Car"]`, and the goals no carrier answers —
        // `Low[T = Car, E = Int64]`, the mirrored `Low[T = Bool, E = Car]` — offered
        // `["Top"]` ALONE, so a dispatch that should be refused resolved to a spec that
        // declares no operation and died at eval.
        //
        // THE ORIGIN IS THE QUESTION, NOT THE SHAPE, so that this stays the chain's
        // answer rather than a second copy of the predicate: `derived_provision_origin_of`
        // gives the forwarder the row came through (`Mid`), and `Top provides Mid` being
        // a conversion is what says `Top` already HOLDS a `Low` dictionary inside its
        // `Mid` slot. Nothing is deleted — the tower's real carriers get their own derived
        // `Low` rows in the same pass, which is the `conversion ⟹ derived-through`
        // invariant applied one level up. A derived row at a real carrier
        // (`Car provides Low[T = Car]`) has a concrete carrier binding, its origin edge is
        // no conversion, and it stays.
        if let Some(origin) = kb.derived_provision_origin_of(rid) {
            if chain_has_conversion(kb, impl_sort, origin) {
                continue;
            }
        }

        // WI-350: when the call supplies a concrete receiver carrier (a
        // self-receiver spec — `head(s: Stream)` with `s : List[…]`),
        // keep only the impl that carrier provides. Without this, a spec
        // whose carrier is not a type parameter (Stream's only param is
        // the *element*) matches every impl's universally-quantified
        // `fact Stream[T]` and resolves `Ambiguous` for ≥2 impls — even a
        // fully concrete call. For type-parameter-carrier specs (`Eq`,
        // `Numeric`, `Iterable`) `goal.carrier` is `None` and binding
        // matching below does the discrimination. Canonicalize both sides:
        // `impl_sort` (a `SortProvidesInfo.sort_ref` functor) and the carrier
        // may be interned under different copies of the same logical sort —
        // the same normalization `sort_ops_lookup` applies to `impl_sort`.
        if let Some(carrier) = goal.carrier.as_ref().map(|c| c.sort) {
            // WI-714 (proposal 052): accept the provider when the carrier IS the
            // impl sort (the direct hot path) OR — only as a FALLBACK, when the
            // carrier does not directly provide the spec — when it TRANSITIVELY
            // provides it (a provider CHAIN). A `Relation[T, E]` value dispatches a
            // `Stream` op (`takeN`/`find`/`isEmpty`) whose only provider of
            // `Stream` is `LogicalStream` (`impl_sort = LogicalStream`), reached via
            // `Relation provides LogicalStream provides Stream`. Before 052 the typer
            // never saw a 2-hop carrier (a `.map` return type collapses to the direct
            // provider `Stream`), so exact-equality sufficed; a relation is the first
            // value whose STATIC type is two `provides` hops from the spec.
            // `sort_provides` is transitive and cycle-guarded.
            let impl_canon = kb.canonical_sort_sym(impl_sort);
            let carrier_canon = kb.canonical_sort_sym(carrier);
            let accept = impl_canon == carrier_canon
                || (!carrier_directly_provides && sort_provides(kb, carrier, impl_sort));
            if !accept {
                continue;
            }
        }

        let impl_param_set = impl_param_symbols(kb, impl_sort);
        let mut impl_subst: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        let mut head_specificity: u32 = 0;
        let mut all_match = true;
        let mut resolved_head_bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        for (binding_short, candidate_value) in &view_bindings {
            let short_name = kb.local_name_of(*binding_short);
            if !type_param_names.iter().any(|n| n == short_name) {
                // Op-binding (auto-bound `eq`/`neq`/…) — doesn't drive
                // dispatch.
                continue;
            }
            let per_call_value = match goal_binding_value(kb, goal, *binding_short) {
                Some(t) => t,
                None => {
                    // WI-387 + WI-714: the goal under-constrains this spec param (no
                    // per-call value). The decision turns on the param's ROLE:
                    //  - An EFFECT-ROW param the goal omits is NON-discriminating on
                    //    BOTH paths — carrier-less (provider admissibility: "does some
                    //    carrier provide Stream?") AND the concrete self-receiver path
                    //    (`goal.carrier = Some`), where the carrier filter above has
                    //    ALREADY selected the impl. A row is the observation effect,
                    //    not carrier identity, so it must not drop the candidate (two
                    //    providers still resolve `Ambiguous`; the dispatch analogue of
                    //    FIX 3 — a provided `E` covers, it does not demand). Keyed on
                    //    the SPEC PARAM (`sort_param_is_effect_row`), not the binding
                    //    value's surface shape, so it holds whether the provider writes
                    //    a concrete row (`E = {}`) OR threads its own param (`E = E`,
                    //    LogicalStream / Relation — a bare param ref, not an
                    //    `effects_rows` literal); else `head`/`find` on such a carrier
                    //    resolve `NoCandidates`.
                    //  - A TYPE param the goal omits (a concrete `T = Int` on `fact
                    //    Eq[T = Int]`) IS discriminating and keeps the strict reject —
                    //    else every concrete `Eq` impl would match a bare `Eq` goal (a
                    //    coherence violation: wi325 / wi237); WI-357's pre-dispatch
                    //    element re-walk owns the self-receiver element threading.
                    let param_name = kb.local_name_of(*binding_short).to_string();
                    if sort_param_is_effect_row(kb, goal.spec_sort, &param_name) {
                        continue;
                    }
                    all_match = false;
                    break;
                }
            };
            if !match_candidate_against_goal(
                kb,
                impl_sort,
                true, // top-level spec-view binding — arm (2.5) may self-capture here
                *candidate_value,
                per_call_value,
                &impl_param_set,
                &mut impl_subst,
                &mut head_specificity,
                sigma,
            ) {
                all_match = false;
                break;
            }
            // Build resolved head bindings inline; consumers want the
            // per-callsite ground value (not the candidate's free
            // pattern).
            resolved_head_bindings.push((*binding_short, per_call_value));
        }
        if !all_match {
            continue;
        }
        // WI-20260828-EKWDC — AND THE RECEIVER'S OWN ARGUMENTS FILL WHAT THE PROVISION
        // HEAD LEFT FREE. See [`carrier_arg_impl_subst`] for the rule and the shape it
        // exists for.
        carrier_arg_impl_subst(kb, goal, impl_sort, &impl_param_set, &mut impl_subst);
        let cand = Candidate {
            impl_sort,
            resolved_head_bindings,
            impl_subst,
            head_specificity,
        };
        // WI-1032 — TWO PROVISIONS THAT SAY THE SAME THING ARE ONE CANDIDATE. The rule
        // was already written down, one layer over, at [`Provider::SelfProvider`]: "Two
        // self-provisions of one spec by one carrier are therefore ONE candidate, which is
        // right: they name one member set, and a disagreement between their BINDINGS is
        // `ConflictingProvisionBindings`'s (WI-842), not a second dictionary." The LOAD
        // grouping had it — `record` collapses duplicate `SelfProvider`s — and this
        // collector did not.
        //
        // Structural equality is the whole criterion and it is SOUND BY CONSTRUCTION: a
        // `Candidate` is `(impl_sort, resolved_head_bindings, impl_subst,
        // head_specificity)`, and everything downstream — the resolved tree node, the
        // subgoals `requires_chain(impl_sort)` instantiates through `impl_subst` — is a
        // function of exactly those. Two equal candidates therefore resolve identically,
        // so picking either is picking the same thing. This is NOT first-match: candidates
        // that differ in ANY field are all kept, and `pick_most_specific` still refuses to
        // choose among them.
        //
        // WHAT IT FIXES, measured: `sort Leaf { provides Desc[T = Leaf]; operation
        // describe … }` beside a namespace `fact Desc[T = Leaf]` is ONE dictionary written
        // in two places, and the CALL was refused — `2 instances provide Desc (Leaf,
        // Leaf)`, naming one carrier twice and advising a repair that changes nothing. A
        // program with a single implementation, rejected.
        //
        // WHICH COHERENCE CELL THAT IS, stated because the first cut of this comment got
        // it WRONG and review measured it: NOT WI-859's (1 fact, 0 witnesses, 1
        // self-provider). `Provider::Fact` is recorded only when the provision BINDS an op
        // (`provision_binds_any_op` → `binding_op_symbol`, which demands a
        // `SymbolKind::Operation` value), and a bare `fact Desc[T = Leaf]` binds a SORT. So
        // both provisions classify as `SelfProvider(Leaf)`, `record` collapses them, and
        // the group holds ONE — cell (0, 0, 1), which the size gate skips and
        // `fact_beside_self_provider_is_one_carrier` never sees. WI-859's licence for its
        // own cell was therefore never falsified by this; the shape that IS in (1, 0, 1) is
        // the op-binding pair below, which genuinely has a conflict.
        //
        // AND IT IS IN THE COLLECTOR, not at `pick_most_specific`, because a SECOND
        // consumer counts: `check_selection_bindings` refuses an unthreadable selection on
        // `candidates.len() > 1`, and its own doc says why the sole-provider case is
        // accepted — "with a sole provider the pin necessarily names it, so accepting is
        // exact rather than lenient". Two provisions saying one thing ARE a sole provider,
        // so deduping here makes that gate exact too; deduping at the tie would have left
        // it refusing a selection that could not have differed.
        //
        // The op-binding leg is why the CONFLICTING pair collapses rather than merely
        // rendering badly: the loop above `continue`s on any binding that is not a spec
        // TYPE param, so a `fact Desc[T = Leaf, describe = otherDescribe]` differs from a
        // bare `provides Desc[T = Leaf]` in nothing this struct records. As PROVISIONS they
        // agree, so collapsing them is right, and it is what lets the genuine conflict
        // reach the reader that can SEE it — WI-1027's supplier tie, which names the two
        // texts by supply route instead of printing the carrier twice.
        //
        // ONE ASYMMETRY THIS CREATES, recorded because it is the WI-838 shape: for the
        // `[SelfProvider, Fact]` pair the LOAD grouping still counts TWO (its `record`
        // dedup is per-KIND and cannot merge a `SelfProvider(Symbol)` with a
        // `Fact(TermId)`), while this collector now counts ONE. Benign today — the group
        // is admitted by `fact_beside_self_provider_is_one_carrier` and the conflict lands
        // on the supplier tie — but the two readers no longer agree about how many
        // provisions a carrier has, and the arm's own justification ("the group cannot tell
        // that shape from a rival, because the question is per-OP and a group is per-SPEC")
        // described a symmetric ignorance that is now one-sided.
        //
        // CANONICAL, not raw, on the carrier: one qualified name can be interned under
        // several `Symbol`s, and `push_supplier_deduped` dedups canonically for exactly
        // that reason — "a raw compare would let ONE operation reached through two interned
        // copies read as two candidates — refusing a correct program". No driver exists
        // today (WI-838 measured every provision's carrier equal to its canonical symbol),
        // so this is untested; it is spelled the strong way because the untested direction
        // is refusing a correct program, and because the named owner of the rule spells it
        // so. The other three fields compare raw: they hold per-call `TermId`s from ONE
        // goal, so two provisions that agree produce identical ids by construction.
        let cand_carrier = kb.canonical_sort_sym(cand.impl_sort);
        if !out.iter().any(|c| {
            kb.canonical_sort_sym(c.impl_sort) == cand_carrier
                && c.resolved_head_bindings == cand.resolved_head_bindings
                && c.impl_subst == cand.impl_subst
                && c.head_specificity == cand.head_specificity
        }) {
            out.push(cand);
        }
    }
    out
}

/// WI-20260828-EKWDC — extend a candidate's impl-param substitution with the arguments
/// the RECEIVER's own type wrote at that carrier.
///
/// `impl_subst` is what [`candidate_provider_sub_goals`] instantiates the carrier's
/// `requires` chain through, and it is built by matching the PROVISION HEAD against the
/// goal. A head names only the parameters the spec is about, so every other parameter of
/// the carrier stays a bare reference into the carrier's own declaration — and
/// `MappedStream requires Iterable[C = Source, Element = Src, E = ES]` mentions three
/// parameters that `provides Stream[T = T, E = {ES, EF}]` does not write. The sub-goal
/// that reached the resolver was therefore `Iterable[C = MappedStream.Source, …]`, which
/// asks about a PARAMETER; nothing provides that, and `Stream.splitFirst(mapped(xs,
/// inc))` was refused for a receiver whose type is fully ground.
///
/// ADDITIVE, NEVER OVERRIDING. Only a parameter the head match left unbound is filled.
/// The head match is what the goal DEMANDED of this provision, so it stays the
/// authority; a receiver argument is what the value happens to be, which can only be
/// consulted where the demand said nothing. That also bounds the change: no dispatch
/// whose head already pinned a parameter can resolve differently than before.
///
/// ACROSS THE PROVIDER CHAIN AS WELL AS AT THE CARRIER ITSELF, through
/// [`provision_path_subst`]. `collect_provides_candidates` accepts a candidate the carrier
/// reaches only TRANSITIVELY (WI-714), so `impl_sort` can be a sort the receiver's type
/// never mentions; there it is the carrier's PROVISION that connects them, composed per
/// hop. At zero hops that walk is the identity and this is the receiver's arguments
/// aligned to the carrier's parameters, which is the shape [`GoalCarrier`] exists for.
///
/// JOINED BY SHORT NAME, which is exact here and nowhere else: both sides are parameters
/// of ONE sort, and [`impl_param_symbols`] already resolves them from that sort's
/// qualified name. (Across scopes it would not be — a `requires` clause and the spec it
/// names mint different symbols for one parameter, which is why
/// [`direct_requires`] compares local names and why `resolve_requires_bindings` re-keys.)
///
/// THE SAME RULE ALREADY EXISTS ONE ROUTE OVER, and is spelled the same way on purpose:
/// [`match_candidate_against_goal`]'s arm (2.5) threads a per-call instance's type
/// arguments into `impl_subst` "keyed by the impl sort's OWN type-params so the
/// requires-chain resolves at the concrete element", for a self-representing carrier
/// whose spec-view binding is a bare `Ref(impl_sort)` (`Set provides PartialEq[T = Set]`
/// against a `Set[T = Int64]`). That arm reaches the receiver through a BINDING; this one
/// reaches it through [`SortGoal::carrier`], which is where a self-receiver spec's
/// carrier lives instead (WI-350). Two routes to one receiver, one rule.
pub(super) fn carrier_arg_impl_subst(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    impl_sort: Symbol,
    impl_params: &[Symbol],
    impl_subst: &mut SmallVec<[(Symbol, TermId); 2]>,
) {
    let Some(carrier) = goal.carrier.as_ref() else {
        return;
    };
    // The receiver's arguments re-keyed by the CARRIER SORT's own parameter symbols —
    // the form [`substitute_impl_params_alloc`] matches, and the starting substitution of
    // the walk below. At zero hops it IS the answer.
    let carrier_params = impl_param_symbols(kb, carrier.sort);
    let carrier_subst = align_by_short_name(kb, &carrier.args, &carrier_params);
    let mut visited: SmallVec<[Symbol; 8]> = SmallVec::new();
    let Some(path) =
        provision_path_subst(kb, carrier.sort, &carrier_subst, impl_sort, &mut visited)
    else {
        return;
    };
    // RE-KEYED THROUGH `impl_params`, the caller's own parameter symbols, rather than
    // trusting the walk's keys to have landed on the same ones. They are resolved from a
    // qualified name at both ends, so today they agree — but `carrier.sort` is CANONICAL
    // (`canonical_sort_sym`) where `impl_sort` is the raw `SortProvidesInfo.sort_ref`
    // functor, and the typer canonicalizes exactly because one qualified name can be
    // interned under several `Symbol`s (WI-838/WI-864). A disagreement would be SILENT IN
    // BOTH DIRECTIONS: the additivity test below would not see the head match's binding,
    // so a duplicate key would be pushed, and `substitute_impl_params_alloc`'s `*k == s`
    // would never match the `Ref` in the `requires` clause, so the fill would do nothing.
    for (param, value) in align_by_short_name(kb, &path, impl_params) {
        if impl_subst.iter().any(|(k, _)| *k == param) {
            continue;
        }
        impl_subst.push((param, value));
    }
}

/// WI-20260828-EKWDC — re-key `pairs` by the parameter symbols of one sort, joining on
/// SHORT NAME. The written key of a type argument and the sort's own parameter symbol are
/// two spellings of one parameter; see [`carrier_arg_impl_subst`] for why that join is
/// exact within a sort and nowhere else. A key naming no parameter of the sort is
/// dropped — it constrains nothing the substitution can reach.
pub(super) fn align_by_short_name(
    kb: &KnowledgeBase,
    pairs: &[(Symbol, TermId)],
    params: &[Symbol],
) -> SmallVec<[(Symbol, TermId); 2]> {
    let mut out: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    for (written, value) in pairs {
        let short = short_name_of(kb.local_name_of(*written));
        if let Some(param) = params
            .iter()
            .copied()
            .find(|&p| short_name_of(kb.local_name_of(p)) == short)
        {
            out.push((param, *value));
        }
    }
    out
}

/// WI-20260828-EKWDC (two-hop) — the substitution from `impl_sort`'s OWN type parameters
/// to types in the RECEIVER's terms, following the `provides` chain from `from` to
/// `impl_sort`.
///
/// AT ZERO HOPS this is the identity: `from` IS the sort whose provision head was
/// matched, so its parameters are already the receiver's own and `from_subst` is the
/// answer. That is the shape [`GoalCarrier`] was introduced for.
///
/// AT ONE OR MORE HOPS the receiver's arguments are NOT the answer, and this is the whole
/// reason the walk exists. `collect_provides_candidates` accepts a candidate the carrier
/// reaches only TRANSITIVELY (WI-714: `Relation provides LogicalStream provides Stream`),
/// so `impl_sort` is a sort the receiver's type never mentions — `Chained[Out = Int64]`
/// says nothing about `Mid.Src`. What connects them is the CARRIER'S PROVISION: `Chained
/// provides Mid[Src = Heavy, Out = Out]` maps the intermediate's parameters to types
/// written in the carrier's own parameter space, and instantiating THOSE at `from_subst`
/// carries the receiver's arguments across the hop. Composed per hop, exactly as
/// [`transitive_provision_view`] composes its own view, and recursive for the same reason:
/// nothing bounds the chain at one edge.
///
/// MEASURED as the shape it exists for — one fixture, two carriers differing in whether
/// the sort carrying the `requires` is the receiver's own or one hop away:
///
/// ```text
/// sort Mid { sort Src = ?  sort Out = ?          -- constructor-less
///   requires Tagger[T = Src]                     -- names Src
///   provides Stream[T = Out, E = {}]             -- names Out, NOT Src
///   operation splitFirst(m: Mid) -> ... }
/// sort Chained { sort Out = ?  entity chained(item: Heavy, out: Out)
///   provides Mid[Src = Heavy, Out = Out]  ... }
/// ```
///
/// `Stream.splitFirst(chained(heavy(7), 42))` asked `Tagger[T = Mid.Src]` — the
/// INTERMEDIATE's declaration parameter — and is now `Tagger[T = Heavy]`, read off the
/// provision.
///
/// FIRST PATH WINS where several reach `impl_sort`, and the cycle guard is `visited`.
/// Both are [`transitive_provision_view`]'s properties, held for its reasons: a carrier
/// with two routes to one spec is a coherence question its own readers answer, not one to
/// re-decide here.
fn provision_path_subst(
    kb: &mut KnowledgeBase,
    from: Symbol,
    from_subst: &[(Symbol, TermId)],
    impl_sort: Symbol,
    visited: &mut SmallVec<[Symbol; 8]>,
) -> Option<SmallVec<[(Symbol, TermId); 2]>> {
    if same_sort_canonical(kb, from, impl_sort) {
        return Some(SmallVec::from_slice(from_subst));
    }
    if visited.iter().any(|&v| same_sort_canonical(kb, v, from)) {
        return None;
    }
    visited.push(from);
    // THE DIRECT EDGE FIRST. `directly_provided_specs` returns provides-facts in
    // assertion order, so a plain DFS would take whichever edge happens to come first —
    // and where `from` reaches `impl_sort` BOTH directly and through an intermediate
    // (`List provides Stream` beside `List provides FiniteStream provides Stream`, the
    // very shape WI-714's fallback is written around), that means discharging
    // `impl_sort`'s `requires` at what the INTERMEDIATE's provision binds rather than at
    // what `from` itself wrote. `collect_provides_candidates`, this walk's only caller,
    // states the preference one level up — "accept when the carrier IS the impl sort (the
    // direct hot path) OR — only as a FALLBACK … when it TRANSITIVELY provides it" — and
    // a walk that contradicted its own caller would bind a requirement to the wrong type
    // with both arms naming a concrete sort, so nothing downstream could tell.
    //
    // NOT the same question as the "first path wins" note above, which is about two
    // routes to one SPEC — a coherence matter its own readers answer. This is two routes
    // to one PROVIDER SORT, which coherence does not refuse.
    let mut edges = directly_provided_specs(kb, from);
    if let Some(i) = edges
        .iter()
        .position(|&e| same_sort_canonical(kb, e, impl_sort))
    {
        edges.swap(0, i);
    }
    for intermediate in edges {
        let Some(view) = provider_spec_view_bindings(kb, from, intermediate) else {
            continue;
        };
        // `view` keys the INTERMEDIATE's parameters and writes their values in `from`'s
        // parameter space; instantiate those values at `from_subst` so what crosses the
        // hop is in the receiver's terms.
        let inter_params = impl_param_symbols(kb, intermediate);
        let mut inter_subst: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        for (key, value) in view {
            let short = short_name_of(kb.local_name_of(key)).to_string();
            let Some(param) = inter_params
                .iter()
                .copied()
                .find(|&p| short_name_of(kb.local_name_of(p)) == short)
            else {
                continue;
            };
            let instantiated = substitute_impl_params_alloc(kb, value, from_subst);
            inter_subst.push((param, instantiated));
        }
        if let Some(found) =
            provision_path_subst(kb, intermediate, &inter_subst, impl_sort, visited)
        {
            return Some(found);
        }
    }
    None
}

/// Is `functor` the `SortView` wrapper — `anthill.reflect.SortView`, or a `.SortView`
/// re-export of it? The ONE discriminant for "this spec term is a view, whose positional 0
/// is the base" (WI-20260923-N3W68 #9).
///
/// It was spelled at each site that asked: this exact-or-dotted-suffix test inline at five
/// sites and again inside [`view_is_sort_view`]; a dotless `ends_with("SortView")` in
/// `check_provider_requires`, which a spec named `MySortView` also passes — its first
/// positional would then be skipped as the "base"; and the canonical-symbol compare
/// `normalize_op_requires_entry` made. A census of the dotless outlier found no program
/// reaching it (every provision's spec view is the loader's own `SortView`), so unifying
/// changes no answer a corpus reads.
pub(super) fn is_sort_view_functor(kb: &KnowledgeBase, functor: Symbol) -> bool {
    let qn = kb.qualified_name_of(functor);
    qn == "anthill.reflect.SortView" || qn.ends_with(".SortView")
}

/// Unwrap a `SortView(base, …named)` term into `(base_sort_sym,
/// named_bindings)`. Accepts a bare functor (no SortView wrap) as the
/// no-bindings case. Returns `None` for shapes that don't fit either
/// case (caller must filter).
pub(super) fn unwrap_spec_view(
    kb: &KnowledgeBase,
    spec_view_tid: TermId,
) -> Option<(Symbol, SmallVec<[(Symbol, TermId); 2]>)> {
    match kb.get_term(spec_view_tid) {
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => {
            if is_sort_view_functor(kb, *functor) {
                let base_sym = pos_args
                    .first()
                    .copied()
                    .and_then(|t| match kb.get_term(t) {
                        Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => {
                            Some(*functor)
                        }
                        _ => None,
                    })?;
                Some((base_sym, named_args.clone()))
            } else {
                Some((*functor, SmallVec::new()))
            }
        }
        Term::Ref(s) | Term::Ident(s) => Some((*s, SmallVec::new())),
        _ => None,
    }
}

/// WI-662: the carrier-agnostic [`unwrap_spec_view`] for a `RequiresEntry.spec`
/// `Value`. A ground `Value::Term` delegates to the TermId decode above
/// (byte-identical). A denoted spec (`Value::Entity` / `Value::Node`, e.g.
/// `Foo[E = Modify[c]]`) is decoded via [`TermView`] with the SAME SortView
/// logic. A denoted BINDING value (`E = Modify[c]`) has no `TermId` and is
/// dropped from the returned bindings — every caller filters to type-param
/// bindings (`is_type_param_binding`) and threads `TermId`s into `SortGoal` /
/// the child subst map, so an effect binding is never one they consume; the full
/// denoted spec stays preserved on `RequiresEntry.spec` regardless.
pub(crate) fn unwrap_spec_view_value(
    kb: &KnowledgeBase,
    spec: &Value,
) -> Option<(Symbol, SmallVec<[(Symbol, TermId); 2]>)> {
    if let Value::Term { id, .. } = spec {
        return unwrap_spec_view(kb, *id);
    }
    match spec.head(kb) {
        ViewHead::Functor {
            functor: Some(f), ..
        } => {
            if is_sort_view_functor(kb, f) {
                let base_sym = spec.pos_arg(kb, 0).and_then(|p| match p.head(kb) {
                    ViewHead::Functor {
                        functor: Some(s), ..
                    }
                    | ViewHead::Ident(s) => Some(s),
                    _ => None,
                })?;
                let mut bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                for key in spec.named_keys(kb) {
                    if let Some(v) = spec.named_arg(kb, key).and_then(|it| it.as_term_id()) {
                        bindings.push((key, v));
                    }
                }
                Some((base_sym, bindings))
            } else {
                Some((f, SmallVec::new()))
            }
        }
        ViewHead::Ident(s) => Some((s, SmallVec::new())),
        _ => None,
    }
}

/// Look up `goal.bindings[short]` (the per-call value for the spec's
/// short parameter name). Compared by **resolved short name** rather
/// than symbol-identity: the candidate's binding_short and the goal's
/// stored key may have been interned through different paths (the
/// candidate-side loader vs. the goal-construction call below) — but
/// they always render to the same short name (e.g. "T").
fn goal_binding_value(kb: &KnowledgeBase, goal: &SortGoal, short: Symbol) -> Option<TermId> {
    if let Some(v) = goal
        .bindings
        .iter()
        .find(|(k, _)| *k == short)
        .map(|(_, v)| *v)
    {
        return Some(v);
    }
    let name = kb.local_name_of(short);
    goal.bindings
        .iter()
        .find(|(k, _)| kb.local_name_of(*k) == name)
        .map(|(_, v)| *v)
}

/// Type-param short-name symbols declared on an impl sort. Used to
/// distinguish impl-param `Ref(EqList.A)` from concrete refs (e.g.,
/// `Ref(Int)`) when matching the candidate's head.
pub(super) fn impl_param_symbols(kb: &KnowledgeBase, impl_sort: Symbol) -> SmallVec<[Symbol; 2]> {
    let mut out: SmallVec<[Symbol; 2]> = SmallVec::new();
    let impl_qn = kb.qualified_name_of(impl_sort).to_string();
    for short in kb.type_params_of_sort(impl_sort) {
        let qn = format!("{impl_qn}.{short}");
        if let Some(s) = kb.try_resolve_symbol(&qn) {
            out.push(s);
        }
    }
    out
}

/// Match a candidate-side value (potentially containing impl-param
/// `Ref`s) against a per-call value. Captures impl-subst bindings on
/// the way; returns false on shape mismatch. Recursive on parametric
/// values so `List[T = A]` properly binds `A` to the per-call's `T`.
pub(super) fn match_candidate_against_goal(
    kb: &mut KnowledgeBase,
    impl_sort: Symbol,
    top_level: bool,
    candidate_value: TermId,
    per_call_value: TermId,
    impl_params: &[Symbol],
    impl_subst: &mut SmallVec<[(Symbol, TermId); 2]>,
    specificity: &mut u32,
    // WI-827: the call-site σ (`None` on the σ-less dispatch/diagnostic path).
    sigma: Option<&SigmaCtx>,
) -> bool {
    // (1) Candidate side is an impl-param ref → bind it (or check consistency
    // with an earlier binding). Both σ modes live in [`match_impl_param`] so
    // they cannot drift (mirrors [`binding_pair_covers`]); an impl-param ref
    // contributes no specificity weight.
    if let Some(p) = impl_param_ref(kb, candidate_value, impl_params) {
        return match_impl_param(kb, sigma, p, per_call_value, impl_subst);
    }
    // (2) Candidate side is a parametric Fn — recurse into its bindings.
    if let Some((c_base, c_bindings)) = parametric_value_parts(kb, candidate_value) {
        // Per-call side must also be parametric with the same base.
        let (p_base, p_bindings) = match parametric_value_parts(kb, per_call_value) {
            Some(parts) => parts,
            None => {
                // WI-824: with a call-site σ in hand, a BARE TYPE-PARAM element
                // does NOT match a STRUCTURED candidate head. Matching a var
                // against a structure is unification; dispatch is MATCHING, and
                // the goal side is what the call already fixed. `FT` is not
                // provably `Wrap[A = E]` for any `E` — accepting PINNED the
                // call to an impl the caller never chose, and since the result
                // was `Unique`, WI-325's abstract-call protection (which guards
                // `NoCandidates` / `NoMatch`) never saw it: the program died at
                // eval reading a field the value lacks, or computed a WRONG
                // VALUE silently. The rule, the conditional twin that never
                // mis-pinned, and the row this changes are in
                // `docs/design/spec-instance-dispatch.md` §"Step 3 is MATCHING,
                // not unification"; the witnesses are
                // `wi824_abstract_mispin_test.rs`.
                //
                // ONE rule for the whole branch, deliberately — not "refuse a
                // rigid skolem, keep the leniency for an element nothing pins".
                // The narrower form was written first and is MEASURED IDENTICAL
                // (of 17 678 σ-present firings here, every one classifies
                // rigid), so the two differ only in what they claim. The
                // narrow claim does not hold up: WI-507's unpinned-sibling
                // case, which the leniency exists for, meets an impl-param REF
                // and so is decided by arm (1) — not by this branch, whose
                // candidate side is a parameterized application; and an element
                // nothing determines is exactly what WI-828 calls genuinely
                // unconstrained and refuses to guess at. Keying on σ-PRESENCE
                // rather than on a σ-CLASS also drops a dependency on the
                // classifier: it returns `None` on chase-bound exhaustion, and it
                // chases a KB-wide canonical global — two ways a spelling-sensitive
                // rule could silently not fire. (A third was listed until WI-942:
                // "it cannot see an OPERATION's own type param". It can now — the
                // bridge carries both scopes — so that leg no longer argues for
                // presence-keying, and the two above are what the choice rests on.)
                //
                // The neighbours this agrees with, neither a duplicate of it:
                //  - step (3) refuses a rigid against a CONCRETE candidate
                //    (`dispatch_values_match`) — the same rule one candidate
                //    shape over, emergent there rather than stated.
                //  - [`match_impl_param`] refuses a rigid meeting a DISAGREEING
                //    stored value (WI-827), i.e. slot RECONCILIATION. A rigid
                //    still RECORDS into an empty slot there — arm (1)'s
                //    candidate side is a VARIABLE, which a skolem does match.
                //
                // The σ-LESS path keeps today's leniency verbatim (WI-827's
                // discipline). Its FOUR entries, since "compat-only" is the
                // easy thing to assume and is wrong: `find_unique_impl_op` /
                // `dispatch_spec_op_with_tree` (no `src/` caller — tests);
                // `build_dispatching_dict_direct` (the req-insertion DIAGNOSTIC
                // dict, whose call-site subst is gone by then);
                // `resolve_bridge_requirements` (eval, RUNTIME dicts — but it
                // resolves only FULLY-GROUND goals, so no abstract element
                // reaches here, and its own guard says so); and
                // `spec_resolves_at_bindings` (declared-binding validation —
                // probed at delivery: its verdict on an abstract binding is the
                // same with and without a parametric provider in scope, so this
                // branch is not what decides it).
                return is_type_param_value(kb, per_call_value) && sigma.is_none();
            }
        };
        // WI-768: this arm requires ONE base, and that is exactly the question
        // [`BindingKeyMatch::for_bases`] answers — so derive the guard and the key-match
        // mode from a single canonical comparison. `Label` here means "same sort", which
        // arm (2) demands; `Identity` means the bases are different sorts, which it
        // rejects. Reading the mode rather than hardcoding `Label` keeps the gate in the
        // one place that owns it (a caller must not pick a mode by hand).
        //
        // This also WIDENS the old raw `c_base != p_base`: the same sort interned under
        // two copies is one base, as arm (2.5) just below already reads it
        // (`canonical_sort_sym`), so raw `!=` had the two arms disagreeing about sort
        // identity inside one function. MEASURED INERT on the corpus — of 265 arm-(2)
        // calls, 235 differ in base and EVERY one is `same_sort_canonical == false`
        // (`MutableStack` vs `List`, …), i.e. genuinely different sorts. Nothing in the
        // corpus discriminates the widening; it ships on consistency with the
        // sort-identity rule (WI-672), NOT on a failing case, and no test covers it.
        let key_match = BindingKeyMatch::for_bases(kb, c_base, p_base);
        if key_match != BindingKeyMatch::Label {
            return false;
        }
        *specificity = specificity.saturating_add(1);
        // WI-768: one base ⟹ compare binding KEYS by the shared rule. The two producers
        // spell one slot differently — a WRITTEN `provides Spec[T = Relation[T = .., E =
        // ..]]` keys `T`/`E` BARE (loader `reintern(p.last())`), a relation VALUE from a
        // rule citation keys them CANONICALLY (`anthill.prelude.Relation.T`) — and raw
        // identity missed that pair and DROPPED the provider, so dispatch disagreed with
        // the typer that WI-764 had already taught to accept it.
        // Each candidate binding must find a matching per-call binding.
        for (k, c_val) in &c_bindings {
            let p_val = match binding_for_param(kb, &p_bindings, *k, key_match) {
                Some(v) => *v,
                None => return false,
            };
            if !match_candidate_against_goal(
                kb,
                impl_sort,
                false, // nested sub-binding — arm (2.5) applies only at top level
                *c_val,
                p_val,
                impl_params,
                impl_subst,
                specificity,
                sigma,
            ) {
                return false;
            }
        }
        return true;
    }
    // (2.5) Candidate is a BARE ref to the impl sort ITSELF, matched against a
    // concrete parametric instance of it — the self-representing carrier's
    // `provides Spec[T = Self]` shape (`Set`/`Map`: `provides PartialEq[T = Set]`
    // writes `Set` with no element binding). Step (3)'s shallow `dispatch_values_
    // match` would accept `Set` vs `Set[T = Int64]` but bind NOTHING, so the impl's
    // own conditional requires-chain (`Set requires Eq[T]`) then resolves at the
    // abstract `Set.T` instead of `Int64` and dispatch spuriously fails — the
    // typed op-body `eq(a: Set[Int64], b)` LOAD path (WI-625 / WI-300 Tier B load
    // side). Thread the instance's type-args into `impl_subst` keyed by the impl
    // sort's OWN type-params so the requires-chain resolves at the concrete element
    // (`Eq[Int64]` resolves; `Eq[Float]` — Float has no lawful Eq — correctly does
    // not). SOUND because the capture is gated on the candidate ref being the impl
    // sort AND on `top_level`: the self-provides binding is the COMPARED-TYPE
    // itself (a direct spec-view binding), never a nested sub-binding, so its
    // per-call params are exactly the params the requires-chain substitutes. The
    // `top_level` gate blocks a bare `Ref(impl_sort)` reached through step (2)'s
    // recursion — a provider whose compared-type is a DIFFERENT parameterized sort
    // that merely embeds `impl_sort` (`Set provides Eq[T = Pair[A = Set, …]]`) —
    // from capturing a NESTED instance's element into the outer impl's params
    // (code-review). A provider whose compared-type is a different parameterized
    // sort at top level (`EqList provides Eq[T = List[A]]`) is parametric, handled
    // by step (2), and never reaches here.
    if top_level
        && extract_sort_ref_sym(kb, &TermIdView(candidate_value))
            .is_some_and(|s| kb.canonical_sort_sym(s) == kb.canonical_sort_sym(impl_sort))
    {
        if let Some((p_base, p_bindings)) = parametric_value_parts(kb, per_call_value) {
            if kb.canonical_sort_sym(p_base) == kb.canonical_sort_sym(impl_sort) {
                let mut aligned = false;
                for (p_key, p_val) in &p_bindings {
                    let p_short = short_name_of(kb.local_name_of(*p_key));
                    let Some(ip) = impl_params
                        .iter()
                        .find(|ip| short_name_of(kb.local_name_of(**ip)) == p_short)
                    else {
                        continue;
                    };
                    aligned = true;
                    // WI-827 (defect d): under σ, give this self-provides
                    // alignment the same slot discipline arm (1) uses — an
                    // incoming concrete threaded into a slot arm (1) filled with
                    // a rigid must YIELD (order symmetry), not be rejected by a
                    // raw `values_structurally_equal(rigid, concrete)`. The
                    // σ-less path keeps today's bare structural check (verified
                    // no divergence there — it is NARROWER than arm (1)'s coarse
                    // rule, so it is not routed through `match_impl_param`).
                    if sigma.is_some() {
                        if !match_impl_param(kb, sigma, *ip, *p_val, impl_subst) {
                            return false;
                        }
                    } else if let Some((_, prev)) = impl_subst.iter().find(|(k, _)| k == ip) {
                        if !values_structurally_equal(kb, *prev, *p_val) {
                            return false;
                        }
                    } else {
                        impl_subst.push((*ip, *p_val));
                    }
                }
                // Only claim the (scored) match when we actually aligned an element
                // to an impl param; a zero-alignment instance (param-name drift)
                // falls through to step (3)'s shallow match — the pre-fix behavior —
                // rather than masking an abstract sub-goal as a full match (review).
                if aligned {
                    *specificity = specificity.saturating_add(1);
                    return true;
                }
            }
        }
    }
    // (3) Concrete sort ref/identifier — use the existing shallow check.
    if dispatch_values_match(kb, per_call_value, candidate_value) {
        *specificity = specificity.saturating_add(1);
        return true;
    }
    false
}

/// WI-827 — reconcile an impl param `p` against a per-call element, recording
/// the binding into `impl_subst` (or checking consistency with an earlier one).
/// Both σ modes live here so they cannot drift, mirroring [`binding_pair_covers`].
///
/// **`Some(ctx)` — σ-PRESENT (call-site dict build).** Classify the element by
/// its σ-ROLE, spelling-neutrally (the head-only `Var::Rigid` test below
/// mis-reads a compound requirement's `Ref`-spelled interior — an abstract
/// element `substitute_spec_via_subst` preserved — as a non-rigid wildcard and
/// skips recording it):
///  - unbound-global sibling wildcard (WI-507): accept WITHOUT recording;
///  - empty slot: first writer records (rigid-terminal or concrete alike) —
///    recording a `Ref`-spelled skolem lets the conditional sub-goal instantiate
///    at it and resolve `FromScope` instead of keeping the raw impl param and
///    dying Cyclic (defect a);
///  - occupied slot: one slot names ONE type, so the two values reconcile only
///    when they ARE the same type — the same rigid class (defect b), or
///    σ-structural equality for concretes (a compound interior compared
///    component-wise, defect c). A rigid meeting a distinct rigid or ANY
///    concrete disagrees (a skolem is never provably a specific concrete); a
///    concrete meeting a different concrete disagrees. Every disagreement
///    REFUSES — never a yield, which would drop a slot's constraint and build an
///    unsound dict (`diagonal_distinct_rigids_refused`,
///    `diagonal_mixed_rigid_concrete_refused`).
///
/// **`None` — σ-LESS (dispatch / diagnostic path).** The pre-WI-827 head-only
/// rule, verbatim — verified no divergence, this path never builds a dict.
fn match_impl_param(
    kb: &mut KnowledgeBase,
    sigma: Option<&SigmaCtx>,
    p: Symbol,
    per_call_value: TermId,
    impl_subst: &mut SmallVec<[(Symbol, TermId); 2]>,
) -> bool {
    let Some(ctx) = sigma else {
        // WI-507: a type-param WILDCARD on the per-call side — the enclosing
        // sort's own param left unpinned because no call arg determined it
        // (a carrier-only `clear(c)` pins only the carrier `C`, so the spec's
        // sibling `Element` arrives as `Ref(Sort.Element)`) — matches any
        // impl-param binding WITHOUT constraining it: the concrete carrier
        // already pins the shared impl param `T`, and this sibling is whatever
        // that pinning implies via the provider's `provides` fact. Without this
        // the sibling clashes with the already-bound `T` (`values_structurally_
        // equal(Int64, Ref(Sort.Element))`), defeating dispatch-dict resolution
        // and leaving the body's deferred spec-op call with no `__req_*` to
        // read at eval. The all-wildcard call already resolves (its carrier is
        // a wildcard too, so `T` never pins); this extends the same leniency to
        // the carrier-concrete / sibling-abstract mix — matching the wildcard
        // tolerance the parametric arm and `entries_cover` already apply.
        if is_type_param_value(kb, per_call_value) {
            // WI-821: a RIGID per-call value is a definite per-body skolem
            // (the enclosing sort's own param), not an unpinned wildcard —
            // RECORD it (first writer wins, never rejecting the match) so a
            // resolution sub-goal instantiates at it (`Desc[T = Wrap[A = E]]`
            // matched at `A := rigid GT` must yield sub-goal `Desc[rigid GT]`,
            // which resolves FromScope against the caller's chain). Left
            // unbound, the sub-goal keeps the raw impl param, matches the
            // SAME parametric fact again, and dies Cyclic. Other type-param
            // spellings (an unpinned `Ref(Sort.Element)` sibling) stay
            // unconstraining exactly as WI-507 established.
            if matches!(kb.get_term(per_call_value), Term::Var(Var::Rigid(_)))
                && !impl_subst.iter().any(|(k, _)| *k == p)
            {
                impl_subst.push((p, per_call_value));
            }
            return true;
        }
        if let Some(slot) = impl_subst.iter_mut().find(|(k, _)| *k == p) {
            if values_structurally_equal(kb, slot.1, per_call_value) {
                return true;
            }
            // WI-821 order symmetry: a stored RIGID yields to an incoming
            // CONCRETE, exactly as an incoming rigid already yields to a
            // stored concrete (the type-param early-return above skips the
            // slot). Without this, a provider binding one impl param in two
            // spec slots was accepted or SILENTLY DROPPED depending on which
            // binding the fact happened to declare first. Either order now
            // ends with the concrete in the slot; only concrete/concrete
            // disagreement rejects.
            if matches!(kb.get_term(slot.1), Term::Var(Var::Rigid(_))) {
                slot.1 = per_call_value;
                return true;
            }
            return false;
        }
        impl_subst.push((p, per_call_value));
        return true;
    };

    // σ-PRESENT — classify by σ-role.
    let incoming = sigma_class_terminal(kb, ctx, per_call_value);
    // Unbound-global sibling wildcard (WI-507): accept, do not constrain.
    if matches!(incoming, Some((_, false))) {
        return true;
    }
    // Empty slot — first writer records (rigid-terminal or concrete alike).
    let Some(i) = impl_subst.iter().position(|(k, _)| *k == p) else {
        impl_subst.push((p, per_call_value));
        return true;
    };
    let stored = impl_subst[i].1;
    // One impl-param slot names ONE type. Two per-call values reconcile only
    // when they ARE the same type — never by yielding one to the other, which
    // would silently drop a slot's constraint and build an unsound dict (a
    // diagonal `Spec[T = E, U = E]` at `T := rigidCT, U := Pebble` cannot be one
    // `E`: `rigidCT` is a universally-quantified skolem, never provably that
    // concrete). So:
    //  - incoming rigid vs stored: the SAME rigid class agrees; a distinct
    //    rigid OR any concrete disagrees (a rigid ≠ a concrete);
    //  - incoming concrete vs stored: σ-structural equality
    //    ([`sigma_pair_precise`]) agrees; anything else — a different concrete
    //    OR a rigid — disagrees.
    // Either disagreement REFUSES the candidate (the sound outcome — see
    // `diagonal_distinct_rigids_refused` / `diagonal_mixed_rigid_concrete_refused`).
    if let Some((vid, true)) = incoming {
        return matches!(
            sigma_class_terminal(kb, ctx, stored),
            Some((svid, true)) if svid == vid
        );
    }
    sigma_pair_precise(kb, ctx, stored, per_call_value)
}

/// If `value` is `Ref(sym)` / `Ident(sym)` where `sym` is one of
/// `impl_params`, return `Some(sym)`. None otherwise.
pub(super) fn impl_param_ref(
    kb: &KnowledgeBase,
    value: TermId,
    impl_params: &[Symbol],
) -> Option<Symbol> {
    let sym = match kb.get_term(value) {
        Term::Ref(s) | Term::Ident(s) => *s,
        _ => return None,
    };
    if impl_params.contains(&sym) {
        Some(sym)
    } else {
        None
    }
}

/// Decompose a parametric value `Functor(named: [(k, v), ...])` into
/// `(functor, named_args)`. Returns `None` for non-parametric shapes
/// (bare refs, sort_ref wraps, literals).
pub(super) fn parametric_value_parts(
    kb: &KnowledgeBase,
    value: TermId,
) -> Option<(Symbol, SmallVec<[(Symbol, TermId); 2]>)> {
    match kb.get_term(value) {
        Term::Fn {
            functor,
            named_args,
            pos_args,
        } => {
            let f_qn = kb.qualified_name_of(*functor);
            // SortView is the candidate-side parametric encoding —
            // unwrap into (base, bindings).
            if is_sort_view_functor(kb, *functor) {
                let base = pos_args
                    .first()
                    .copied()
                    .and_then(|t| match kb.get_term(t) {
                        Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => {
                            Some(*functor)
                        }
                        _ => None,
                    });
                return base.map(|b| (b, named_args.clone()));
            }
            // WI-361: a parameterized type is the term backing `Fn{S, named}` (base
            // sort IS the functor, bindings ARE the named args) — handled by the
            // generic-Fn arm below as `(S, named_args)`, no `parameterized(base,
            // bindings)` wrapper to translate.
            // WI-320: `effects_rows(effects_expr = E)` is a structural Type
            // variant (wraps an EffectExpression), not a parametric spec
            // carrier — `effects_expr` is a *field*, not a spec parameter.
            // Without this explicit None, the generic-Fn catch-all below
            // would falsely classify it as a parametric instance with a
            // phantom (param = effects_expr, value = E) binding, leading
            // spec-resolution and `values_structurally_equal` to treat it
            // as a satisfaction site.
            if f_qn == "EffectsRows" || f_qn.ends_with(".EffectsRows") {
                return None;
            }
            // Generic Fn — non-empty named_args means parametric.
            if !named_args.is_empty() {
                Some((*functor, named_args.clone()))
            } else {
                None
            }
        }
        _ => None,
    }
}

/// Structural equality check on two term values — used when an impl
/// param is encountered twice in the head and must bind consistently.
pub(super) fn values_structurally_equal(kb: &KnowledgeBase, a: TermId, b: TermId) -> bool {
    if a == b {
        return true;
    }
    // Hash-consing collapses identical structures into one TermId, so
    // distinct ids generally indicate a shape difference. Still, walk
    // sort_ref / parametric forms to catch the shallow encoding noise.
    let a_sym = sort_sym_of_term(kb, a);
    let b_sym = sort_sym_of_term(kb, b);
    match (a_sym, b_sym) {
        (Some(x), Some(y)) if x == y => {
            // Check nested bindings if parametric.
            match (parametric_value_parts(kb, a), parametric_value_parts(kb, b)) {
                (Some((ab_base, ab)), Some((bb_base, bb))) => {
                    if ab.len() != bb.len() {
                        return false;
                    }
                    // WI-768: the second raw-identity binding lookup of the same defect
                    // class as arm (2) above — enrolled in the shared rule so the two
                    // cannot drift apart the way `unify_parameterized_view` and
                    // `parameterized_compatible_view` did between WI-726 and WI-764.
                    //
                    // UNDEMONSTRATED, unlike arm (2), and deliberately shipped without a
                    // test rather than with one that passes for another reason. Both sides
                    // here are PER-CALL values (`impl_subst` only ever stores the per-call
                    // side), so they normally share a producer and therefore a spelling.
                    // The obvious probe — an impl param bound twice, meeting a
                    // citation-typed argument at one occurrence and an annotation-typed one
                    // at the other — was built and did NOT discriminate: it dispatches
                    // identically with this lookup reverted to raw identity (the two values
                    // reach the `a == b` fast path above). If a case is ever found, it
                    // presents as arm (2) did — a key miss reads as "these two bindings of
                    // one param disagree" and drops the candidate.
                    let key_match = BindingKeyMatch::for_bases(kb, ab_base, bb_base);
                    ab.iter().all(|(k, av)| {
                        binding_for_param(kb, &bb, *k, key_match)
                            .is_some_and(|bv| values_structurally_equal(kb, *av, *bv))
                    })
                }
                _ => true,
            }
        }
        _ => false,
    }
}

/// Coherence-by-specificity. Picks the candidate with the strictly-
/// highest `head_specificity` count. Returns `None` if no unique
/// winner (multiple candidates tied at the max).
pub(super) fn pick_most_specific(_kb: &KnowledgeBase, candidates: &[Candidate]) -> Option<usize> {
    if candidates.is_empty() {
        return None;
    }
    let max = candidates.iter().map(|c| c.head_specificity).max().unwrap();
    let mut winners = candidates
        .iter()
        .enumerate()
        .filter(|(_, c)| c.head_specificity == max);
    let first = winners.next()?;
    if winners.next().is_some() {
        return None;
    }
    Some(first.0)
}

/// WI-861 — 058 §3.2 RUNG 2a at the PROVISION tie: the index of the tied candidate the
/// default names, or `None` for "say which" (tier 3, unchanged).
///
/// A candidate's provider IS its `impl_sort` — for a witness the witness sort, for a
/// carrier-keyed provision the carrier — which is the same symbol
/// [`crate::kb::defaults::DefaultRow::provider`] carries, so the two need no translation.
///
/// THE CARRIER IS THE GOAL'S, not the candidate's, and it is what makes the lookup
/// precise rather than "does any row name this sort": a provider with two provisions of
/// one spec at disjoint carriers contributes two rows, and only the one whose carrier the
/// goal describes may answer. `None` from [`goal_carrier_key`] — a SELF-REPRESENTING
/// spec (WI-1076), whose dispatch is directed by the receiver value and which therefore
/// has no carrier position a row could be keyed at — declines the rung outright rather
/// than falling back to a base-only lookup: there is no base to fall back to. Since
/// WI-20260916-8WRJC that is the only shape which declines: a spec whose carrier
/// parameter no operation receives on reaches rung 2 of `spec_carrier_param_or_sole`
/// and is keyed like any other.
pub(super) fn default_among_candidates(
    kb: &KnowledgeBase,
    goal: &SortGoal,
    candidates: &[Candidate],
) -> Option<usize> {
    let carrier = goal_carrier_key(kb, goal)?;
    crate::kb::defaults::default_among(
        kb,
        goal.spec_sort,
        carrier,
        candidates.iter().map(|c| c.impl_sort),
    )
}

/// WI-861 — the CARRIER a [`SortGoal`] names, as 058 §3.6's rows are keyed.
///
/// Read off the spec's carrier PARAMETER through [`spec_carrier_param_or_sole`] —
/// WI-1102's ONE owner of "which type parameter of `spec` the carrier goes in" — and
/// then through the same [`binding_for_param`] rule every other binding lookup in this
/// file runs.
///
/// WI-20260916-8WRJC — IT USED TO ASK RUNG 1 ALONE ([`spec_carrier_param`], "the param
/// some declared OPERATION receives on"), AND THAT CONFLATED TWO DIFFERENT `None`s. A
/// spec declaring `sort T = ?` whose operations are all NULLARY has a carrier parameter
/// and no operation mentioning it, so rung 1 answered `None` and the default rung was
/// declined outright — 058 §3.2 rung 2a never asked, and two providers of one instance
/// tied with their own default (the self-providing carrier) never consulted. MEASURED:
/// that program reported `two providers answer …` where the SAME program with one
/// DEFAULTED, uncalled carrier-bearing op added to the spec answers the default. One op
/// declaration decided whether a default existed, which is not what a default means.
/// Rung 2 (a SOLE type parameter) is gated on [`spec_is_self_representing`] inside
/// `spec_carrier_param_or_sole`, which is what keeps WI-1076's other `None` — the
/// element-not-carrier shape, seven stdlib provisions — out of this answer. `Label` is
/// [`BindingKeyMatch::for_bases`]' verdict by construction: both sides are `goal.
/// spec_sort`'s own parameters, and the two producers key them differently (a canonical
/// `Ord.T` against a written bare `T`), which is exactly what identity-then-label exists
/// for.
///
/// [`SortGoal::carrier`] is deliberately NOT a second source. It is WI-350's
/// SELF-RECEIVER discriminator, set only for specs whose carrier is not a binding — the
/// self-representing shape both rungs answer `None` for — and there
/// `collect_provides_candidates` has already narrowed every candidate to that one sort,
/// so a surviving tie is one provider reached twice and no default separates it (see
/// [`crate::kb::defaults::default_among`]'s "exactly one, not the first").
///
/// A binding that names a TYPE PARAMETER rather than a sort (`Ord[T = E]` inside a
/// generic body) yields no carrier: [`carrier_view_parts`] answers on the `Ref`, but
/// [`is_type_param_value`] is what says the name denotes no carrier, and a default for
/// "any carrier" is not a thing 058 §3.6 can express — the abstract goal resolves through
/// the caller's own `requires` slot, not through a default.
fn goal_carrier_key(
    kb: &KnowledgeBase,
    goal: &SortGoal,
) -> Option<crate::kb::defaults::CarrierKey> {
    let param = spec_carrier_param_or_sole(kb, goal.spec_sort)?;
    let view = *binding_for_param(kb, &goal.bindings, param, BindingKeyMatch::Label)?;
    if is_type_param_value(kb, view) {
        return None;
    }
    // The WRITTEN view alone: `X[Y]` and `X[Z]` are different carriers and this is what
    // says so. Its base is the index's bucket key and is derived at the lookup
    // ([`crate::kb::defaults::CarrierKey`]), never carried alongside where the two could
    // disagree.
    Some(crate::kb::defaults::CarrierKey::View(view))
}

/// WI-861 — the BASE sort of a carrier view (`List[T = Int64]` ⇒ `List`), for the one
/// reader that needs the [`crate::kb::defaults::DefaultProviderIndex`] BUCKET rather than the
/// comparison. `None` for a term that is not a carrier shape at all, which that reader
/// takes as "no default here".
pub(crate) fn carrier_view_base(kb: &KnowledgeBase, view: TermId) -> Option<Symbol> {
    carrier_view_parts(kb, view).map(|(base, _)| base)
}

/// Build subgoals for a chosen conditional candidate by substituting
/// the impl-side substitution into the impl sort's **direct** `requires`
/// (WI-239). Filters out op-bindings (which the loader stores alongside
/// type-param bindings on a `SortView` — see `find_requires_slot`'s same
/// distinction) — only type-param bindings drive resolution.
///
/// WI-239: direct, not transitive. The resolution tree mirrors the
/// runtime requirement-value tree: each `Conditional` node bundles one
/// `sub_resolution` per *direct* require, and transitive requires are
/// resolved recursively when those sub-resolutions are themselves
/// `Conditional`. This keeps a constructed requirement value's arity
/// equal to `synth_req_names(impl_sort)` (also direct) — the invariant
/// eval's `expand_dispatching_dict` cross-checks. A flat chain here
/// would over-count the sub-resolutions (the duplicated-subtree problem)
/// and break that arity check.
/// WI-653 — decode ONE op-level `requires` entry into `{canonical spec type-param ↦
/// carrier}`, the carrier expressed in the OPERATION's own scope (a `Ref` to the
/// enclosing sort / op type-param, e.g. `Ref(List.T)`). The carrier link IS present in
/// the stored op-`requires` — it is just held in a shape the named-only decoders
/// (`unwrap_spec_view`, `entry_type_param_bindings`, `spec_mentions_key`) silently drop:
///   * POSITIONAL `Fn{spec, [c0, c1, …]}` — the common `requires Eq[T]` form; paired
///     against the spec's declared type-params in SOURCE order (`type_params_of_sort`).
///   * NAMED `Fn{spec, [(short, c)]}` — an explicit `Spec[C = T]`, the WI-201 bare-spec
///     sugar, or a WI-320 auto-require; keyed by the short param name.
/// Op-`requires` is always this bare `Fn{spec, …}` — never a `SortView` wrapper (that
/// is the SORT-level requires shape; see `push_op_requires_clause`, which takes the
/// spec application verbatim). Every key is routed through [`type_param_sym_of_binding`]
/// / `try_resolve_symbol` so the map key is the CANONICAL spec-param symbol the
/// reached-requirement `Ref`s use — the interning bridge without which
/// `substitute_impl_params_alloc`'s `Symbol`-equality composition is a silent no-op (the
/// wall the prior carrier-aware attempt hit). Non-type-param keys (`eq`, `neq`, …) are
/// dropped.
pub(super) fn op_requires_entry_carrier_map(
    kb: &KnowledgeBase,
    entry: &RequiresEntry,
) -> SmallVec<[(Symbol, TermId); 2]> {
    let spec_qn = kb.qualified_name_of(entry.required_sort).to_string();
    let mut out: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    // Positional carriers pair with the spec's declared type-params by the language's
    // rule — the next param no NAMED binding took (`KnowledgeBase::positional_param_slots`).
    // WI-20260923-N3W68 (#9): this zipped params against positionals by RAW INDEX, so an
    // op-scoped `requires Spec2[T = X, Y]` paired `Y` with `T` — the parameter the name had
    // already bound — and never with `U`. A positional with no slot binds no parameter: the
    // loader refuses an over-applied op-scoped `requires` where it is written.
    let params = kb.type_params_of_sort(entry.required_sort);
    let bound_by_name = |kb: &KnowledgeBase, keys: &[Symbol], d: &str| {
        keys.iter().any(|k| {
            type_param_sym_of_binding(kb, *k, &spec_qn)
                .is_some_and(|p| short_name_of(kb.local_name_of(p)) == d)
        })
    };
    match &entry.spec {
        // WI-662: ground fast path — byte-identical to the pre-WI-662 term read.
        Value::Term { id, .. } => {
            let Term::Fn {
                pos_args,
                named_args,
                ..
            } = kb.get_term(*id).clone()
            else {
                return out; // a bare `Ref`/`Ident` spec carries no bindings
            };
            let keys: SmallVec<[Symbol; 2]> = named_args.iter().map(|(k, _)| *k).collect();
            let slots = KnowledgeBase::positional_param_slots(
                &params,
                |d| bound_by_name(kb, &keys, d),
                pos_args.len(),
            );
            for (v, slot) in pos_args.iter().zip(slots) {
                // No slot: refused at load where it is written (the op-contract arity gate
                // in `convert_term`), and binding nothing.
                let Some(short) = slot.map(|i| &params[i]) else {
                    continue;
                };
                if let Some(param) = kb.try_resolve_symbol(&format!("{spec_qn}.{short}")) {
                    out.push((param, *v));
                }
            }
            // Named carriers (sugar / explicit `Spec[C = T]`) — keyed by short param
            // name, resolved to the canonical spec-param symbol.
            for (k, v) in &named_args {
                if let Some(param) = type_param_sym_of_binding(kb, *k, &spec_qn) {
                    out.push((param, *v));
                }
            }
        }
        // WI-662: a denoted op-spec — the same positional/named carrier extraction via
        // TermView, keeping only term-representable binding values (a denoted binding
        // value has no TermId; its carrier threading is deferred parametric-effect work).
        other => {
            let ViewHead::Functor { pos_arity, .. } = other.head(kb) else {
                return out;
            };
            let keys = other.named_keys(kb);
            let slots = KnowledgeBase::positional_param_slots(
                &params,
                |d| bound_by_name(kb, &keys, d),
                pos_arity,
            );
            for (i, slot) in slots.into_iter().enumerate() {
                let Some(short) = slot.map(|j| &params[j]) else {
                    continue;
                };
                if let Some(v) = other.pos_arg(kb, i).and_then(|it| it.as_term_id()) {
                    if let Some(param) = kb.try_resolve_symbol(&format!("{spec_qn}.{short}")) {
                        out.push((param, v));
                    }
                }
            }
            for k in other.named_keys(kb) {
                if let Some(param) = type_param_sym_of_binding(kb, k, &spec_qn) {
                    if let Some(v) = other.named_arg(kb, k).and_then(|it| it.as_term_id()) {
                        out.push((param, v));
                    }
                }
            }
        }
    }
    out
}

/// WI-653 — compose `parent_map` ({parent spec's type-param ↦ carrier in op scope})
/// through ONE reached sort-level requirement, yielding {reached spec's type-param ↦
/// carrier in op scope}. The reached `SortView` binding is spec-param-relative
/// (`Foo requires Bar[T = Foo.B]`); substituting the parent map re-scopes it to the
/// op's carrier (`Bar[T = Host.B]`). This carrier-threading step is exactly what the
/// carrier-blind BFS skipped.
pub(super) fn compose_reached_carrier_map(
    kb: &mut KnowledgeBase,
    parent_map: &[(Symbol, TermId)],
    reached: &RequiresEntry,
) -> SmallVec<[(Symbol, TermId); 2]> {
    let mut out: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    // A reached SORT-level requirement's `spec` is always a decodable spec application
    // (a `SortView`, or a bare `Fn`/`Ref` → empty bindings). A shape `unwrap_spec_view`
    // cannot decode is an unexpected `SortRequiresInfo` form — surface it loudly rather
    // than silently returning an empty (carrier-less) map that would false-reject a
    // legitimate coverage.
    let Some((base, bindings)) = unwrap_spec_view_value(kb, &reached.spec) else {
        debug_assert!(
            false,
            "WI-653: reached requirement spec {} did not decode as a spec view",
            type_display_name_value(kb, &reached.spec),
        );
        return out;
    };
    let base_qn = kb.qualified_name_of(base).to_string();
    for (k, v) in &bindings {
        let Some(reached_param) = type_param_sym_of_binding(kb, *k, &base_qn) else {
            continue;
        };
        let composed = substitute_impl_params_alloc(kb, *v, parent_map);
        out.push((reached_param, composed));
    }
    out
}

/// WI-653 — the deferred spec-op call's carrier per `spec_sort` type-param, resolved
/// through the per-call `subst`: `{canonical spec type-param ↦ carrier}`. A param the
/// call left unbound (`None` — an equivalence-class root) is omitted — a wildcard for
/// coverage. An EMPTY result means the call pinned no carrier (the fully-open case),
/// which [`op_requires_covers`] treats as the pre-WI-653 carrier-blind license.
///
/// INVARIANT this fix rests on: `empty call_carriers ⟺ the call pinned no real carrier`.
/// It holds because only a FAILED abstract dispatch reaches the arms that call this —
/// there the spec op's params are FRESH vars unified AGAINST the arg types, so a real
/// carrier resolves to a `Value::Term` (the arg's `List.T` / `Host.A`) while a genuinely
/// unpinned param resolves to `None`. This is deliberately less eager than the
/// abstract-param DIAGNOSTIC loop in `check_apply` (which treats a `None`-resolved param
/// as still-abstract for a WI-325 flag): omitting it is sound here because the `blind`
/// fallback defers to value-directed eval, not a wrong-carrier license. A future denoted
/// / value-in-type param representation (WI-302 / WI-348 Phase C) is where this invariant
/// would need re-checking — hence the loud `debug_assert` on the non-`Term` carrier below
/// (mirroring `entry_type_param_bindings`).
fn call_carriers_from_subst(
    kb: &KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
) -> SmallVec<[(Symbol, TermId); 2]> {
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();
    let mut out: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    for short in kb.type_params_of_sort(spec_sort) {
        let Some(param) = kb.try_resolve_symbol(&format!("{spec_qn}.{short}")) else {
            continue;
        };
        let Some(alias_target) = resolve_sort_alias(kb, param) else {
            continue;
        };
        let Term::Var(Var::Global(vid)) = kb.get_term(alias_target) else {
            continue;
        };
        match subst.resolve_as_value(*vid) {
            // Unbound spec param — the call did not pin this carrier; a wildcard.
            None => {}
            Some(Value::Term { id, .. }) => out.push((param, *id)),
            // A denoted `Value::Node` carrier: carrier-agnostic alignment is WI-348
            // Phase C. Omitting it lets coverage fall to the `blind` license (deferred
            // to value-directed eval, the module's FAILED-dispatch stance); flag loudly
            // in debug so the gap surfaces, mirroring `entry_type_param_bindings`.
            Some(other) => debug_assert!(
                false,
                "WI-348/WI-653: denoted {} call carrier — carrier-agnostic alignment is Phase C",
                other.type_name(),
            ),
        }
    }
    out
}

/// WI-653 — does the reached target-spec carrier map σ-align with the deferred call's
/// carriers? Every target type-param the call PINNED that the reached map also bound
/// must share a σ-class ([`sigma_pair_precise`] — type-param↔type-param by σ, concrete↔
/// concrete structurally); at least one such param must overlap (an empty overlap does
/// not confirm coverage). A `requires Foo[A, B]` reaching `Bar[T = Foo.B]` binds
/// `Bar.T ↦ …B`, so a `Bar`-op called over `A` (`Bar.T ↦ …A`) fails the σ-check and is
/// correctly NOT licensed.
pub(super) fn reached_carrier_matches_call(
    kb: &mut KnowledgeBase,
    ctx: &SigmaCtx,
    reached_map: &[(Symbol, TermId)],
    call_carriers: &[(Symbol, TermId)],
) -> bool {
    let mut aligned = false;
    for (cp, cc) in call_carriers {
        let Some(rc) = reached_map
            .iter()
            .find(|(rp, _)| *rp == *cp)
            .map(|(_, v)| *v)
        else {
            continue;
        };
        if !sigma_pair_precise(kb, ctx, rc, *cc) {
            return false;
        }
        aligned = true;
    }
    aligned
}

/// WI-562/WI-653: does the enclosing operation's OWN op-scoped `requires` chain
/// (WI-448) cover `spec_sort` OVER THE CALL'S CARRIER? Used only in the FAILED dispatch
/// arms (`NoMatch` / abstract `NoCandidates`) to LICENSE an abstract spec-op call in
/// the op's body that the op explicitly declared it `requires` — `List.member requires
/// Eq[T]` covering its `eq(head, x)` — leaving the call as the spec op for
/// value-directed eval (the op-scoped dual of the sort-level defer-to-requirement).
/// Only a FAILED abstract dispatch reaches these arms — a concrete call resolves
/// `Unique` (keeping its impl effect-grounding, WI-365) and never gets here.
///
/// WI-644 / proposal 004: TRANSITIVE coverage. `requires Eq[T]` covers a `PartialEq.eq`
/// call because `Eq requires PartialEq` — the partial ops moved onto the `PartialEq`/
/// `PartialOrd` bases, so a comparison-only op that declares `requires Eq`/`requires
/// Ord` (`List.member`) reaches its `eq`/`gt` through the chain.
///
/// WI-653: CARRIER-AWARE. The prior version compared only spec SYMBOLS, so a `requires
/// Foo[A, B]` whose `Foo requires Bar[B]` wrongly licensed a `Bar`-op over the SIBLING
/// `A` (the threaded `Foo` dict bundles a `Bar[B]` sub-dict, never `Bar[A]`). The
/// carrier link is present in the stored op-`requires` but held positionally; this BFS
/// threads it — [`op_requires_entry_carrier_map`] seeds each top-level requirement's
/// `{spec param ↦ op carrier}` map and [`compose_reached_carrier_map`] re-scopes each
/// reached spec-param-relative `SortView` binding through it, so at `target` the reached
/// carrier is expressed in the op's scope and [`reached_carrier_matches_call`] σ-aligns
/// it with the call's carrier. `call_carriers` empty (a fully-open call that pinned no
/// carrier) falls back to carrier-blind symbol reachability — the pre-WI-653 license,
/// which value-directed eval resolves.
pub(super) fn op_requires_covers(
    kb: &mut KnowledgeBase,
    ctx: &SigmaCtx,
    op_requires: &[RequiresEntry],
    spec_sort: Symbol,
    call_carriers: &[(Symbol, TermId)],
) -> bool {
    let target = kb.canonical_sort_sym(spec_sort);
    let blind = call_carriers.is_empty();
    // BFS over the requires graph. State: (current spec, {current spec's canonical
    // type-param ↦ carrier in the op's own scope}). Dedup on the FULL state, not the
    // spec alone: a carrier-divergent diamond (a shared intermediate spec re-reached
    // under a different carrier) must be re-explored, else a legit coverage reachable
    // only via the second carrier would be missed (a false reject). Full-state dedup
    // stays terminating — well-formed `requires` graphs are acyclic and carriers only
    // re-scope toward the op's own (finite) params, so the distinct states are finite.
    type State = (Symbol, SmallVec<[(Symbol, TermId); 2]>);
    let mut stack: Vec<State> = op_requires
        .iter()
        .map(|e| {
            (
                kb.canonical_sort_sym(e.required_sort),
                op_requires_entry_carrier_map(kb, e),
            )
        })
        .collect();
    let mut visited: Vec<State> = Vec::new();
    while let Some(state) = stack.pop() {
        if visited.contains(&state) {
            continue;
        }
        visited.push(state.clone());
        let (cs, map) = &state;
        if *cs == target && (blind || reached_carrier_matches_call(kb, ctx, map, call_carriers)) {
            return true;
        }
        for reached in direct_requires_chain(kb, *cs) {
            let composed = compose_reached_carrier_map(kb, map, &reached);
            stack.push((kb.canonical_sort_sym(reached.required_sort), composed));
        }
    }
    false
}

/// WI-653 — [`op_requires_covers`] at a body-call site: assemble the σ context and the
/// deferred call's carriers from the per-call `subst`, then run carrier-aware coverage.
/// Factors the identical wiring the `NoMatch` / `NoCandidates` arms of `check_apply_iter`
/// share.
pub(super) fn op_requires_covers_call(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    subst: &Substitution,
    spec_sort: Symbol,
) -> bool {
    let ctx = SigmaCtx {
        subst,
        param_rigids: env.param_rigids(),
    };
    let call_carriers = call_carriers_from_subst(kb, subst, spec_sort);
    op_requires_covers(kb, &ctx, env.op_requires(), spec_sort, &call_carriers)
}

/// WI-857 — the sub-requirement goals a dictionary for `goal` supplied by
/// `impl_sort` bundles, in [`DictLayout`] order: the SPEC half (the spec's own
/// `requires` chain at this goal's bindings) then the PROVIDER half
/// ([`candidate_provider_sub_goals`], the pre-WI-857 list). One producer for one
/// layout — `dict_layout(goal.spec_sort, impl_sort).arity()` counts what this
/// returns, and every consumer slices by that same layout.
///
/// The spec half goes through [`provider_requires_subgoals`], which is the very
/// walk `check_provider_requires` (WI-343/WI-356) already runs to VERIFY that each
/// spec-level `requires`, instantiated at the provision's bindings, resolves. That
/// check is why the spec half can be built at all: the information was already
/// established at load and merely not put in the dictionary. σ is the candidate's
/// RESOLVED head bindings — the per-call values, so a parametric provision
/// (`fact Ord[T = Duo[A, B]]` matched at `Duo[Int64, Int64]`) instantiates the
/// spec's chain at the call's carrier and not at the provision's pattern.
///
/// `impl_sort == goal.spec_sort` (a sort providing its own spec) contributes the
/// provider half ALONE, per the layout's one-list rule.
pub(super) fn dict_sub_goals(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    impl_sort: Symbol,
    impl_subst: &[(Symbol, TermId)],
    head_bindings: &[(Symbol, TermId)],
) -> DictSubGoals {
    let mut goals: Vec<SortGoal> = Vec::new();
    if !same_sort_canonical(kb, impl_sort, goal.spec_sort) {
        // σ keyed by the spec's short param name — `provider_requires_subgoals`'
        // convention, and the only key that reaches the stdlib shorthand
        // (`Ord requires Eq[T]` stores the value as `Eq`'s OWN `T`).
        let sigma: SmallVec<[(String, TermId); 2]> = head_bindings
            .iter()
            .map(|(k, v)| (kb.local_name_of(*k).to_string(), *v))
            .collect();
        goals.extend(provider_requires_subgoals(kb, goal.spec_sort, &sigma));
    }
    let provider_half_start = goals.len();
    let provider_goals = candidate_provider_sub_goals(kb, impl_sort, impl_subst, goal.spec_sort);
    let provider_len = provider_goals.len();
    goals.extend(provider_goals);

    // The self case's one list came out of `candidate_provider_sub_goals` laid out for
    // `goal.spec_sort` — which, there, is the provider itself.
    let layout = DictLayout::from_halves(
        kb,
        goal.spec_sort,
        impl_sort,
        Some(goal.spec_sort),
        provider_half_start,
        provider_len,
    );
    // WI-866 — THE PRODUCER/CONSUMER CONTRACT: this list IS the layout
    // `expand_dispatching_dict` and `stand_in_requirement` PREDICT from the two sorts
    // alone. See [`check_against_prediction`] for why it is checked here and why it
    // raises the way it does.
    check_against_prediction(kb, layout, "the resolver's sub-goal list");
    DictSubGoals {
        goals,
        provider_half_start,
    }
}

/// WI-866 — what [`dict_sub_goals`] produced.
///
/// TWO LENGTHS THAT ARE NOT ONE NUMBER, which is why this is a struct and not the
/// `(goals, usize, mask)` tuple it replaced. [`DictLayout`]'s `spec_len` answers
/// *which slice of the dictionary does an op owned by sort X read*
/// ([`DictLayout::slots_for`]); `provider_half_start` answers *where in `goals` does
/// `candidate_provider_sub_goals`' output begin*. They coincide everywhere except the
/// self case (a sort providing its own spec, or a WI-415 parent bundle), where the
/// layout folds the one list into the spec half (`n, 0`) while the producer emitted
/// all of it from the provider walk and so starts that half at 0. A single
/// `spec_half_len` served both readings by accident of the non-self case being the
/// common one, and only this field is the producer's.
///
/// THE LAYOUT ITSELF IS NOT CARRIED, deliberately: nothing downstream of here holds a
/// goal, so nothing downstream can be handed the produced layout instead of
/// predicting one — [`Interpreter::expand_dispatching_dict`] has a runtime
/// `Dictionary` value and `stand_in_requirement` two bare symbols. It is built and
/// CHECKED against the prediction inside [`dict_sub_goals`], which is what makes
/// those predictions safe; a field nobody reads would not add a source of truth, only
/// a copy of one.
pub(super) struct DictSubGoals {
    /// The sub-requirement goals in dictionary-slot order.
    pub(super) goals: Vec<SortGoal>,
    /// Where [`candidate_provider_sub_goals`]' half begins in `goals`. The index
    /// [`slot_pin_at`]'s `chain_index` is relative to — NOT the layout's `spec_len`,
    /// see the type's own doc.
    pub(super) provider_half_start: usize,
}

/// WI-865 — a sub-goal's failure as the reason its slot pins no provider.
///
/// EXHAUSTIVE on [`ResolutionResult`], with `Resolved` raising rather than falling
/// into a default: the only caller reaches here on the FAILURE arm of a match that
/// already took `Resolved`, so a `Resolved` would mean that arm moved — and a silent
/// "no provider" for a slot that in fact resolved is precisely the mis-attribution
/// this ticket is about. A new failure variant likewise has to choose an arm here
/// rather than inherit one.
pub(super) fn unavailable_why_of(err: &ResolutionResult) -> UnavailableWhy {
    match err {
        // Each arm reads the FAILURE's own spec, never the slot's — see
        // [`UnavailableWhy`] for the falsehood the other reading produces.
        ResolutionResult::NoMatch { spec, .. } => UnavailableWhy::NoProvider { goal: *spec },
        ResolutionResult::Ambiguous { tie, .. } => UnavailableWhy::Ambiguous {
            goal: tie.spec,
            candidates: tie.candidates.clone(),
        },
        ResolutionResult::Cyclic { spec, .. } => UnavailableWhy::Cyclic { goal: *spec },
        ResolutionResult::Resolved(_) => unreachable!(
            "unavailable_why_of is called only on `resolve_inner`'s failure arm, \
             which `Resolved` cannot reach"
        ),
    }
}

/// The PROVIDER half of [`dict_sub_goals`]: the impl sort's dictionary chain FOR THE
/// PROVISION BEING DISPATCHED (proposal 066 §7 — its `requires` plus that provision's
/// `:- goals`), instantiated at the substitution matching its head against the goal —
/// the conditional evidence the provision's member bodies read.
///
/// WI-869 laid this out per CARRIER — every provision's conditions — and left a
/// sibling provision's slots `Unavailable` by a strictness mask. A member backs only its
/// own provision (§7.3), so a dispatch through `goal_spec` reaches a member of
/// `goal_spec`'s block or an operation outside every block, and this chain is exactly
/// the frame either one reads.
pub(super) fn candidate_provider_sub_goals(
    kb: &mut KnowledgeBase,
    impl_sort: Symbol,
    impl_subst: &[(Symbol, TermId)],
    goal_spec: Symbol,
) -> Vec<SortGoal> {
    let chain = provider_dict_entries(kb, impl_sort, Some(goal_spec)).entries_rc();
    instantiate_provider_entries(kb, &chain, impl_subst)
}

/// Proposal 066 §7 — the ALTERNATIVE clauses of `impl_sort`'s provision of `goal_spec`,
/// each instantiated like [`candidate_provider_sub_goals`]: `Some(groups)` when the
/// carrier provides the spec through two or more written clauses, all conditioned, and
/// the dispatch holds iff ONE group resolves. `None` when there are no alternatives to
/// decide — one clause (its conditions are the layout's own slots), or an unconditioned
/// clause among them, which holds outright.
///
/// Alternatives contribute no SLOT (no body reads them — §7.5 refuses a `where` block on
/// such a spec), so they are decided here and not laid out. WI-869 laid every clause's
/// conditions into one chain and demanded all of them: the conjunction WI-1033 had
/// already measured wrong for the entailment check, still wrong at the dispatch.
pub(super) fn alternative_condition_goals(
    kb: &mut KnowledgeBase,
    impl_sort: Symbol,
    impl_subst: &[(Symbol, TermId)],
    goal_spec: Symbol,
) -> Option<Vec<Vec<SortGoal>>> {
    let clauses = kb.provides_clause_count(impl_sort, goal_spec) as usize;
    if clauses < 2 {
        return None;
    }
    let spec_canon = kb.canonical_sort_sym(goal_spec);
    let conditional: Vec<Vec<Value>> = provision_conditions(kb, impl_sort)
        .into_iter()
        .filter(|g| kb.canonical_sort_sym(g.provided) == spec_canon)
        .map(|g| g.conditions)
        .collect();
    // A clause with no `ProvidesConditionInfo` row is unconditioned: it holds.
    if conditional.len() < clauses {
        return None;
    }
    let base = direct_requires_chain_rc(kb, impl_sort);
    let mut groups = Vec::with_capacity(conditional.len());
    for conditions in conditional {
        let mut entries: Vec<RequiresEntry> = Vec::with_capacity(conditions.len());
        for spec in conditions {
            let Some(required_sort) = spec_base_functor(kb, &spec) else {
                debug_assert!(false, "WI-869: a condition with no readable spec head");
                continue;
            };
            // A condition restating a sort-level `requires` is already a slot.
            if base.iter().any(|e| {
                e.required_sort == required_sort
                    && crate::kb::term_view::views_structurally_equal(kb, &e.spec, &spec)
            }) {
                continue;
            }
            entries.push(RequiresEntry {
                required_sort,
                spec,
                supply: SupplySource::Required,
            });
        }
        groups.push(instantiate_provider_entries(kb, &entries, impl_subst));
    }
    Some(groups)
}

/// A provider chain's entries as the sub-goals a dispatch resolves, at `impl_subst` —
/// shared by the laid-out half and the alternatives, so one decoding serves both.
fn instantiate_provider_entries(
    kb: &mut KnowledgeBase,
    chain: &[RequiresEntry],
    impl_subst: &[(Symbol, TermId)],
) -> Vec<SortGoal> {
    let mut out: Vec<SortGoal> = Vec::with_capacity(chain.len());
    for entry in chain.iter() {
        let required_sort = entry.required_sort;
        // WI-857: the synthetic `requires EffectsRuntime[E]` that every effect-row
        // param (`effects ES = ?`) contributes KEEPS ITS SLOT, and `resolve_inner`
        // places a structural leaf in it without resolving — `EffectsRuntime` is the
        // effect-runtime kind-anchor, never a resolvable dispatch provider, so
        // resolving it would fail with a spurious `no impl provides EffectsRuntime`
        // (WI-590's witness over an effect-row-parameterized carrier). It used to be
        // SKIPPED here, which made the dictionary shorter than the chain it is
        // indexed by — see [`effects_runtime_sym`] for the measurement. The
        // parent-bundle producer (`build_dep_projection`) already emitted the same
        // structural leaf; now both agree.
        let Some((_, entry_bindings)) = unwrap_spec_view_value(kb, &entry.spec) else {
            // A `requires` spec with no readable head cannot become a goal. Keep the
            // SLOT anyway so the halves stay positionally exact — and see the twin in
            // `provider_requires_subgoals` for why the bindings-free goal is a GUESS
            // and why this is asserted rather than merely commented. Measured
            // unreachable there and here.
            debug_assert!(
                false,
                "WI-857: `requires {}` has no readable spec head — the dictionary slot \
                 for it is a bindings-free guess",
                kb.qualified_name_of(required_sort),
            );
            out.push(SortGoal {
                spec_sort: required_sort,
                bindings: SmallVec::new(),
                carrier: None,
            });
            continue;
        };
        let spec_qn = kb.qualified_name_of(required_sort).to_string();
        let mut bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        for (k, v) in &entry_bindings {
            // Op-bindings (auto-bound `eq`, `neq`, …) don't constrain
            // resolution — skip.
            if !is_type_param_binding(kb, *k, &spec_qn) {
                continue;
            }
            let substituted = substitute_impl_params_alloc(kb, *v, impl_subst);
            bindings.push((*k, substituted));
        }
        out.push(SortGoal {
            spec_sort: required_sort,
            bindings,
            // Transitive `requires` sub-goals resolve by binding; the
            // receiver carrier discriminates only the top-level call (WI-350).
            carrier: None,
        });
    }
    out
}

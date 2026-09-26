//! Delivering a requirement at runtime: `build_dep_projection`, σ-classes of type
//! parameters, and the absence records a missing provider leaves.

use super::*;

/// WI-227: recursively search for an IR projection that delivers a
/// requirement value satisfying `dep` at runtime, given `caller_requires`
/// as the caller's frame-level requirement chain. Tries named-param
/// match, then nested-handle match via `caller_sub_chains[i]`, then SLD
/// resolution against `SortProvidesInfo`. `caller_sub_chains` must be
/// `[direct_requires_chain(c.required_sort) for c in caller_requires]`
/// (WI-239) — the nested-search index, computed once by the caller. It
/// is the *direct* sub-chain because a requirement value bundles only
/// its own direct sub-requires, so a single `requirement_at_sort`
/// projection indexes it.
///
/// `caller_sort` is the enclosing op's parent sort — needed to turn a
/// caller-chain index into the synthesized `__req_*` param name
/// (`req_name_for_chain_index`). It is `None` only for ops with no
/// enclosing sort, in which case `caller_requires` is empty and
/// Strategies 1 & 2 never fire.
///
/// `pub` so the WI-227 test file can drive each strategy synthetically.
///
/// Reference: docs/design/operation-call-model.md §"Two primitives",
/// §"Call rewrite cases".
pub fn build_dep_projection(
    kb: &mut KnowledgeBase,
    dep: &RequiresEntry,
    // WI-1033: a `DictChain`, so the slot NAMES this function reads come off the very
    // list it indexes. The pair used to be `(&[RequiresEntry], caller_sort)` and
    // `req_insertion::chain_for` — the second producer of this list — was one of the
    // four WI-869 desynchronized: it kept building the DECLARED chain while
    // `synth_req_names` moved to the dictionary one, so index `i` named a slot that was
    // not the slot at `i`.
    caller_requires: &DictChain,
    caller_sub_chains: &[Vec<RequiresEntry>],
    syms: &ProjectionSyms,
    // WI-419/WI-821: the call-site context, when available (the WI-415/418
    // concrete-dispatch path). σ-class agreement GATES forwarding in
    // Strategies 1 & 2 — a covering entry whose element disagrees with the
    // dep's under the call-site subst is NO cover and falls through to
    // Strategy 3's construction. `None` (the req-insertion diagnostic path)
    // keeps the original coarse first-match behavior.
    disambig: Option<&SigmaCtx>,
    // WI-828: when present, receives Strategy 3's TERMINAL failure
    // (`NoMatch`/`Ambiguous`/`Cyclic`) so the caller can explain a refusal
    // without re-running the resolution. Written only when Strategy 3 runs
    // and does not resolve; left `None` on success or when an earlier
    // strategy served the dep.
    s3_failure_out: Option<&mut Option<ResolutionResult>>,
    // WI-841 (058 §4.5): the call site's explicit provider selections. A dep this
    // bracket PINNED skips Strategies 1 & 2 outright — those FORWARD the caller's own
    // dictionary, and explicit selection outranks a forward exactly as it outranks a
    // search (§4.1 tier 1) — and rides into Strategy 3's scope, where step 0 restricts
    // the candidate set. Empty on the req-insertion diagnostic path, which has no call
    // site in hand.
    selected: &[InstanceSelection],
    // WI-861 (058 §3.2 rung 2a): may Strategy 3's CONSTRUCTION take a default when its
    // providers tie? [`DefaultRung::Withhold`] where the dep is the callee's NAMED slot —
    // a type parameter whose binding the caller erased, not a silence to fill. Every
    // caller derives it through [`rung_for_dep`] from the owner whose chain it is
    // walking; the WI-227 test file passes `Consult`, which is the anonymous case its
    // fixtures use.
    rung: DefaultRung,
) -> Option<TermId> {
    // WI-424: the `EffectsRuntime` kind-anchor (synthesized from `effects
    // E = ?`) is satisfied STRUCTURALLY by the effect-row machinery — there is
    // no carrier `fact` to resolve it against and no runtime dispatch ever
    // consults it (the same convention `check_provider_requires` and the
    // override-contract check follow). Project it as a synthetic structural
    // leaf so a chain containing it still completes: without this, a
    // `require_complete` dict build aborts on the un-projectable anchor and
    // the callee's frame slot stays unfilled, while a forwarded
    // `var_ref(__req_effectsruntime)` read (a cross-sort delegating body —
    // `Iterable.find` → `Stream.find`) then dies "unbound in requirement
    // position" at eval.
    if is_effects_runtime(kb, dep.required_sort) {
        return Some(build_empty_bundle(kb, syms, dep.required_sort));
    }

    // WI-1091 — Strategy 0: the dep IS THE ENCLOSING SORT'S OWN SPEC, at its own
    // parameters. The caller's `requires` chain cannot cover that — a sort does not
    // `requires` itself — but the frame already holds the evidence under `__req_self`:
    // the dictionary this very body was dispatched through, whose spec is the enclosing
    // sort and whose instantiation is this call's.
    //
    // MEASURED as the shape without which WI-1091 cannot widen the op-scoped deferral:
    // `anthill.prelude.Ord.max` calls `PartialOrd.gte`, whose op-scoped `requires
    // Ord[T]` is exactly `Ord` at `Ord`'s own parameter. Read from the chain it is
    // unprojectable and `Ord.max` dies `__req_ord not bound … frame binds
    // ["__req_self", "__req_partialeq"]` — with the answer sitting in the frame it
    // names. Three stdlib comparison-surface tests (wi876, wi886, wi869) turn on it.
    //
    // GATED ON IDENTITY, not on the spec symbol alone: every type-param binding the dep
    // states must σ-resolve to the ENCLOSING SORT'S OWN parameter, so `Ord[T = Ord.T]`
    // forwards and `Ord[T = SomethingElse]` does not — `__req_self` is one
    // instantiation, and handing it to a different one is the wrong-dictionary class
    // this whole file guards. No σ context ⇒ no Strategy 0 (the req-insertion
    // diagnostic path, which has no call site to be precise about).
    //
    // AND IT YIELDS TO A CALL-SITE PIN, for the reason Strategies 1 and 2 do (found by
    // /code-review, and it is this ticket's OWN defect class one strategy over): this is
    // a FORWARD — "the enclosing frame's dictionary answers this" — and §4.1 tier 1 says
    // an explicit witness on the call outranks a forward exactly as it outranks a search.
    // Without the gate, `helper[Ord = LoudOrd](x)` written inside `Ord`'s own default
    // body forwards `__req_self` and the named witness is never consulted: a bracket
    // accepted and silently dropped, which is precisely the silent wrong number WI-841
    // measured and WI-1091 exists to close.
    if pinned_witness_for(kb, selected, dep.required_sort).is_none() {
        if let (Some(owner), Some(ctx)) = (caller_requires.owner(), disambig) {
            if same_sort_canonical(kb, dep.required_sort, owner)
                && dep_is_owner_self_instance(kb, ctx, dep, owner)
            {
                let req_self = kb.intern("__req_self");
                return Some(build_req_var_ref(kb, syms, req_self));
            }
        }
    }

    // Strategy 1 — named-param, binding-aware. Match by (required_sort,
    // bindings) so a caller with Eq[T=X] does NOT match dep Eq[T=Y]
    // (WI-226 correctness fix).
    //
    // WI-419: `entries_cover` is wildcard-tolerant — a caller `Eq[A]` covers a
    // dep `Eq[B]` whenever either element is a type param. A caller declaring
    // TWO `requires` of the same spec over DISTINCT element params (`requires
    // Eq[A], Eq[B]`) has BOTH cover a dep over one of them, and a blind
    // first-match forwards the wrong dictionary (a soundness bug — wrong
    // runtime dispatch).
    //
    // WI-821: with a call-site σ in hand, σ-class agreement is a GATE on
    // forwarding, not just a tie-break — a SOLE covering wildcard entry whose
    // element the call-site subst maps to a DIFFERENT type (polymorphic
    // recursion re-entering at `FT := Wrap[GT]`, or a concrete `BT := Pebble`
    // hand-off) used to blindly forward the caller's dictionary, shadowing
    // Strategy 3's construction of the correct one. A disagreeing entry is NO
    // cover; no agreeing entry falls through to Strategies 2/3. Same-class
    // forwarding (wi418 abstract delegation, wi419 disambiguation) still
    // forwards BY NAME. On the σ-less diagnostic path the coarse first-match
    // stands — there is no subst to consult. Both modes are ONE scan with the
    // mode-selecting `entries_cover` (σ-precise implies coarse).
    //
    // WI-841: a dep the CALL SITE pinned takes neither forward. Strategies 1 and 2
    // both answer "the caller's frame already holds a dictionary for this" — true, and
    // beside the point once the call has said which provider it wants.
    let pinned = pinned_witness_for(kb, selected, dep.required_sort).is_some();
    let chosen = if pinned {
        None
    } else {
        (0..caller_requires.len()).find(|&i| entries_cover(kb, &caller_requires[i], dep, disambig))
    };
    if let Some(i) = chosen {
        let name = caller_requires.name_at(kb, i)?;
        return Some(build_req_var_ref(kb, syms, name));
    }

    // Strategy 2 — nested via caller slots' DIRECT requires (WI-239),
    // binding-aware. The slot's runtime requirement value bundles its
    // own direct sub-requires in the same order, so a single
    // `requirement_at_sort` projects them. A dep reachable only past a
    // second level is not found here and falls through to Strategy 3's
    // SLD construction.
    //
    // WI-841: skipped wholesale for a PINNED dep. Loop-invariant, so it is the
    // iteration SOURCE that says so — a test inside would read as "this can go true
    // mid-loop" and invite real work above it.
    let s2_chains: &[Vec<RequiresEntry>] = if pinned { &[] } else { caller_sub_chains };
    for (i, sub_chain) in s2_chains.iter().enumerate() {
        // WI-613/WI-821: same σ-class gate as Strategy 1 (same predicate). A
        // sub-chain entry is written in the SLOT sort's own param space
        // (`direct_requires_chain(slot)` roots at the slot — `Eq[T = Eq.T]`
        // under a caller `requires Ord[T = CT]`), whose vars the call-site
        // subst never binds — compared raw, a correct nested forward would
        // σ-disagree. So the σ gate compares the sub-entry COMPOSED into
        // caller scope through the slot entry's own bindings (`Eq[T = CT]`) —
        // the same one-level composition `requires_tree` applies — which is
        // also the element the slot's RUNTIME bundle actually carries at
        // index `k`. The composition map depends only on the slot, so it is
        // built once per slot, not per candidate.
        let chosen = match disambig {
            Some(ctx) => {
                // (code-review) Compose lazily, and only for a SAME-SORT
                // candidate: the pre-filter is the identical first check
                // `entries_cover` applies (composition never changes
                // `required_sort`), so a sort-mismatched entry skips the
                // allocating `substitute_in_spec` walk entirely, and the map —
                // a function of the slot alone — is built at most once and
                // never for a chain with no same-sort entry (leaf-spec slots
                // have EMPTY chains).
                let mut slot_map: Option<HashMap<Symbol, TermId>> = None;
                (0..sub_chain.len()).find(|&k| {
                    if !same_sort_canonical(kb, sub_chain[k].required_sort, dep.required_sort) {
                        return false;
                    }
                    if slot_map.is_none() {
                        slot_map = Some(build_child_subst_map(kb, &caller_requires[i]));
                    }
                    let map = slot_map.as_ref().expect("filled on the preceding line");
                    let composed = RequiresEntry {
                        required_sort: sub_chain[k].required_sort,
                        spec: substitute_in_spec(kb, &sub_chain[k].spec, map),
                        supply: sub_chain[k].supply,
                    };
                    entries_cover(kb, &composed, dep, Some(ctx))
                })
            }
            None => (0..sub_chain.len()).find(|&k| entries_cover(kb, &sub_chain[k], dep, None)),
        };
        if let Some(k) = chosen {
            let name = caller_requires.name_at(kb, i)?;
            let inner = build_req_var_ref(kb, syms, name);
            return Some(build_req_at_sort(kb, syms, inner, k));
        }
    }

    // WI-456 — Strategy 2b: the caller slots' PROVIDER halves. Strategy 2 searches each
    // slot spec's DECLARED chain, which is the dictionary's SPEC half; a carrier's own
    // `requires` lives in the provider half, past it ([`provider_half_projection`]).
    //
    // A SECOND PASS, not interleaved into the loop above (found by /code-review). Run
    // per-slot it would order the search `slot0.spec → slot0.provider → slot1.spec`, so a
    // dep that slot 1's SPEC half covers would be taken from slot 0's PROVIDER half
    // instead — silently changing which real dictionary is forwarded, in a function whose
    // own Strategy 1 comment calls blind first-match "a soundness bug (wrong runtime
    // dispatch)". Every spec half is searched before any provider half, so the existing
    // preference is exactly preserved and 2b only answers what nothing else would.
    //
    // `s2_chains` is EMPTY for a pinned dep (Strategy 2's own `if pinned` source), so this
    // loop is likewise skipped there — an explicit `if !pinned` here would be dead.
    for i in 0..s2_chains.len() {
        if let Some(t) = provider_half_projection(kb, dep, caller_requires, i, syms, disambig) {
            return Some(t);
        }
    }

    // Strategy 3 — static construction via SortProvidesInfo. Build a
    // SortGoal from the dep's spec bindings and run SLD resolution. WI-821:
    // the σ context rides into the scope so the resolution's own
    // `FromScope` lookup is gated the same way Strategies 1/2 are — without
    // it, the wildcard-tolerant scope cover would resurrect the exact
    // forward the gate above refused.
    let goal = goal_from_requires_entry(kb, dep)?;
    let scope = ResolutionScope {
        available_requires: caller_requires,
        sigma: disambig,
        selected,
        sub_goal_requires: &[],
    };
    match resolve_with_rung(kb, &goal, &scope, rung) {
        ResolutionResult::Resolved(tree) => {
            emit_tree_as_projection(kb, caller_requires, &tree, syms)
        }
        failure => {
            if let Some(out) = s3_failure_out {
                *out = Some(failure);
            }
            None
        }
    }
}

/// WI-456 — Strategy 2b: project a dep out of the PROVIDER HALF of a caller slot's
/// dictionary.
///
/// Strategy 2 searches `direct_requires_chain(slot spec)`, which is the dictionary's
/// SPEC half. A conditional provider's own `requires` is not there: for `spec != provider`
/// [`dict_layout`] lays the dictionary out as the spec half and THEN the provider half
/// (`provider_dict_entries(provider, Some(spec))`, which prefixes the provider's own
/// sort-level `requires`). So a caller holding `PersistentCollection[C = SortedSet[T = E,
/// O = OE], Element = E]` holds `SortedSet`'s `WeakOrd` dictionary — at `spec_len + k`,
/// where Strategy 2 never looks.
///
/// MEASURED as the shape that needed it: `insertD(s: SortedSet[T = E, O = OE], x: E)` on a
/// sort requiring that collection instance loaded clean and died at eval with
/// `Internal(DeferToRequirement: __req_weakord not bound … frame binds [])`, while the
/// comparator sat one `requirement_at_sort` step inside the slot it did hold.
///
/// # Why the index is sound rather than a guess
///
/// A wrong index here is the WI-869 failure — a projection that reads a REAL dictionary
/// from the WRONG slot, which resolves and computes the wrong answer, and which
/// `check_against_prediction` cannot catch because that guards a dictionary's
/// CONSTRUCTION and this is a READ. Three things pin it, and none is optional:
///
///  * the offset is [`DictLayout::spec_len`], from the file's single owner of the split,
///    rather than a second computation of the spec chain's length here;
///  * the search runs over `provider_dict_entries(carrier, Some(spec))` — the very list
///    the producer bundles into that half — so index `k` means the same thing at both ends;
///  * [`carrier_is_its_own_sole_provider`] GATES it. The provider half belongs to whichever
///    sort provides the spec, and that is the carrier only when the carrier provides it
///    ITSELF (`SortedSet provides PersistentCollection[C = SortedSet[…]]`) and no witness
///    rivals it there. `carrier_has_provision_row` is NOT that question — it answers `true`
///    for a witness too, by design — and using it here shipped a measured wrong-slot read;
///    see the predicate's own doc.
///
/// Entries of the provider half are written in the PROVIDER's own parameter space
/// (`SortedSet.T`, `SortedSet.O`), so they are composed into caller scope through the
/// carrier binding's own arguments before being compared — the same one-level composition
/// Strategy 2 applies through [`build_child_subst_map`], with the map read off the carrier
/// rather than off the spec. [`align_by_short_name`] is the join, exactly as
/// [`carrier_arg_impl_subst`] makes it.
pub(super) fn provider_half_projection(
    kb: &mut KnowledgeBase,
    dep: &RequiresEntry,
    caller_requires: &DictChain,
    i: usize,
    syms: &ProjectionSyms,
    disambig: Option<&SigmaCtx>,
) -> Option<TermId> {
    let entry = caller_requires[i].clone();
    let spec = entry.required_sort;
    let (carrier, bound) = provider_half_carrier(kb, &entry)?;
    // THE PRE-FILTER FIRST, before any allocation (found by /code-review). Strategy 2
    // builds its composition map lazily and only for a same-sort candidate for exactly
    // this reason, and 2b runs for EVERY dep Strategies 0-2 miss — so a dep whose spec
    // appears nowhere in this half must cost an `Rc` clone and a symbol compare, not a
    // chain copy plus a `HashMap`. Same load-time path the ticket measures at +9%
    // sensitivity elsewhere.
    let entries = provider_dict_entries(kb, carrier, Some(spec)).entries_rc();
    if !entries
        .iter()
        .any(|e| same_sort_canonical(kb, e.required_sort, dep.required_sort))
    {
        return None;
    }
    let args = carrier_named_args(kb, bound);
    let carrier_params = impl_param_symbols(kb, carrier);
    let map: HashMap<Symbol, TermId> = align_by_short_name(kb, &args, &carrier_params)
        .into_iter()
        .collect();
    // [`DictLayout::slots_for`] OWNS the two-half fold — its spec arm answers for BOTH
    // when spec == provider — so the base comes from it rather than from a `spec_len`
    // read that is only right in one of the two cases.
    let base = dict_layout(kb, spec, carrier, None)
        .slots_for(kb, carrier)?
        .start;
    let k = (0..entries.len()).find(|&k| {
        // The same same-sort pre-filter Strategy 2 applies: composition never changes
        // `required_sort`, so a mismatched entry skips the allocating walk.
        if !same_sort_canonical(kb, entries[k].required_sort, dep.required_sort) {
            return false;
        }
        let composed = RequiresEntry {
            required_sort: entries[k].required_sort,
            spec: substitute_in_spec(kb, &entries[k].spec, &map),
            supply: entries[k].supply,
        };
        entries_cover(kb, &composed, dep, disambig)
    })?;
    let name = caller_requires.name_at(kb, i)?;
    let inner = build_req_var_ref(kb, syms, name);
    Some(build_req_at_sort(kb, syms, inner, base + k))
}

/// Strategy 2b's reading of one caller slot: the CARRIER its spec's carrier binding
/// names, with that binding, when the carrier's own chain is what fills the slot
/// dictionary's provider half. Shared by [`provider_half_projection`] and
/// [`carried_named_frame_slot`] (WI-20260923-WN9P8), so the two cannot disagree about
/// whose provider half a slot holds.
pub(super) fn provider_half_carrier(
    kb: &mut KnowledgeBase,
    entry: &RequiresEntry,
) -> Option<(Symbol, TermId)> {
    let spec = entry.required_sort;
    // WHICH parameter holds the carrier — the same two-rung ladder `unprovided_provision`
    // reads, so the two cannot disagree about it.
    let param = spec_carrier_param_or_sole(kb, spec)?;
    let param_name = kb.local_name_of(param).to_string();
    let goal = goal_from_requires_entry(kb, entry)?;
    let bound = goal
        .bindings
        .iter()
        .find(|(k, _)| kb.local_name_of(*k) == param_name)
        .map(|(_, v)| *v)?;
    let carrier = sort_functor_of_view(kb, &TermIdView(bound))?;
    if !carrier_is_its_own_sole_provider(kb, carrier, spec) {
        return None;
    }
    // AND DECLINE `spec == carrier` OUTRIGHT (found by /code-review). There
    // [`dict_layout`] folds the two halves into ONE list — `spec_len` becomes the WHOLE
    // length and `provider_len` 0 — and the two sides would also be keyed by different
    // provisions (`None` there, `Some(spec)` here), so no index computed from them is
    // one this function can justify. A self-providing spec used as its own carrier is
    // exotic and 2b has no measured need for it; declining falls through to Strategy 3
    // and costs nothing, where guessing loaded clean and died
    // `Internal(requirement_at_sort: index out of range)` at run time.
    if same_sort_canonical(kb, spec, carrier) {
        return None;
    }
    Some((carrier, bound))
}

/// The named arguments of a carrier binding (`SortedSet[T = E, O = OE]`), as the pairs a
/// provider-half entry is composed through ([`align_by_short_name`]).
pub(super) fn carrier_named_args(
    kb: &KnowledgeBase,
    carrier_value: TermId,
) -> SmallVec<[(Symbol, TermId); 2]> {
    let view = TermIdView(carrier_value);
    view.named_keys(kb)
        .into_iter()
        .filter_map(|k| {
            view.named_arg(kb, k)
                .and_then(|it| it.as_term_id())
                .map(|v| (k, v))
        })
        .collect()
}

/// WI-226: binding-aware predicate for slot matching in
/// `build_dep_projection`. True iff `caller`'s spec covers `dep`'s spec
/// — same `required_sort` AND every type-param binding of `dep` is
/// satisfied by `caller`'s binding for the same key.
///
/// `sigma` selects the per-pair verdict via the shared
/// [`binding_pair_covers`] (WI-821 folded the former `entry_sigma_matches`
/// clone into this walk; the code-review pass then hoisted the pair verdict
/// itself so this and `requires_entry_covers_goal` cannot drift):
///   - `None` — the coarse wildcard rule: either side a type-param wildcard
///     is unconstrained. The req-insertion diagnostic path's behavior.
///   - `Some(ctx)` — the σ-precise GATE (WI-419/821): the per-pair verdict is
///     [`sigma_pair_precise`] (which owns the type-param / mixed / concrete /
///     both-compound rules). σ-precise implies coarse, so one walk decides.
///
/// WI-826 moved the KEY ITERATION out to the shared
/// [`supply_covers_demanded_keys`], so this and [`requires_entry_covers_goal`]
/// can no longer disagree about which keys a cover answers for — the same
/// consolidation WI-821 did for the per-pair verdict. Nothing this function
/// decides changed: it always walked the DEMAND (`dep`), and its
/// `dep_bindings.is_empty() => true` early return was redundant with the walk,
/// which falls through to `true` on an empty demand (and on one carrying only
/// op-bindings, which the early return never caught).
///
/// A demand naming NO type param stays a cover here, deliberately: `dep` is what
/// the CALLEE WROTE, so an unnamed element is the author's wildcard — a bare
/// `requires Desc` slot takes any `Desc` dictionary because nothing in the callee
/// says which one it wants. [`requires_entry_covers_goal`] reads its own empty
/// demand differently, and says why.
pub(super) fn entries_cover(
    kb: &mut KnowledgeBase,
    caller: &RequiresEntry,
    dep: &RequiresEntry,
    sigma: Option<&SigmaCtx>,
) -> bool {
    // WI-672: canonical sort identity. `required_sort` is RESOLVED — stdlib specs resolve
    // to their qualified name (`requires Eq` → `anthill.prelude.Eq`; a probe found NO bare
    // `Eq`), and the only bare `required_sort`s are top-level USER specs (`Ring`, …) with
    // no qualified twin, so canonical is self-consistent for them. It correctly
    // de-conflates a testcase `Ring` from stdlib `anthill.prelude.algebra.Ring`, which the
    // old `same_symbol` last-segment bridge (WI-420, now vestigial) wrongly merged.
    if !same_sort_canonical(kb, caller.required_sort, dep.required_sort) {
        return false;
    }
    let Some((_, caller_bindings)) = unwrap_spec_view_value(kb, &caller.spec) else {
        return false;
    };
    let Some((_, dep_bindings)) = unwrap_spec_view_value(kb, &dep.spec) else {
        return false;
    };
    let spec_qn = kb.qualified_name_of(dep.required_sort).to_string();
    supply_covers_demanded_keys(
        kb,
        sigma,
        &spec_qn,
        Supply(&caller_bindings),
        Demand(&dep_bindings),
    )
}

/// The two sides of a cover question, as DISTINCT types (WI-826). Both are the
/// same `&[(Symbol, TermId)]`, and which one is which IS the whole semantics of
/// [`supply_covers_demanded_keys`] — this ticket exists because one walk had them
/// the wrong way round. Newtyped so a transposed call is a compile error rather
/// than a silent re-creation of the defect.
#[derive(Clone, Copy)]
pub(super) struct Supply<'a>(pub(super) &'a [(Symbol, TermId)]);
/// The demand side of a cover question — see [`Supply`].
#[derive(Clone, Copy)]
pub(super) struct Demand<'a>(pub(super) &'a [(Symbol, TermId)]);

/// WI-826 — THE key iteration shared by the two cover walks, the way WI-821
/// hoisted the per-pair verdict into [`binding_pair_covers`]: for every
/// type-param key the DEMAND names, the SUPPLY must name it too and the pair must
/// cover. A supply that says LESS than the demand is no cover, in either mode. A
/// demand that names nothing is answered vacuously — what that MEANS differs per
/// caller, so each states its own reading rather than this one guessing.
///
/// The key lookup goes through [`binding_for_param`], the shared binding-key rule
/// (WI-726/764/768/769/825) — NOT the `find(same_label)` this walk used before
/// being hoisted, which lacked the identity-first pass that makes an exact key
/// beat a merely same-labelled one. `BindingKeyMatch::Label` is
/// [`BindingKeyMatch::for_bases`]' verdict under the same-spec gate every caller
/// already applies (`entries_cover`'s `same_sort_canonical`;
/// `requires_entry_covers_goal`'s two callers compare `required_sort` to
/// `goal.spec_sort` before calling) — a PRECONDITION of this function, since one
/// spec's type-param short names are unique but two specs both have a `T`.
///
/// Non-type-param keys (auto-bound `eq`, `neq`, …) constrain nothing and are
/// skipped on the demand side.
pub(super) fn supply_covers_demanded_keys(
    kb: &mut KnowledgeBase,
    sigma: Option<&SigmaCtx>,
    spec_qn: &str,
    supply: Supply,
    demand: Demand,
) -> bool {
    for (d_key, d_val) in demand.0 {
        if !is_type_param_binding(kb, *d_key, spec_qn) {
            continue;
        }
        let supplied = binding_for_param(kb, supply.0, *d_key, BindingKeyMatch::Label).copied();
        let Some(s_val) = supplied else {
            return false;
        };
        if !binding_pair_covers(kb, sigma, s_val, *d_val) {
            return false;
        }
    }
    true
}

/// The σ (substitution) context for type-param **identity** questions — the
/// per-call substitution plus the enclosing sort's param→rigid map. This is the
/// shared σ primitive's context: given it, [`sigma_class`] maps any type element
/// to its canonical representative variable, so two elements can be tested for
/// "same type parameter, really?" ([`sigma_same`]) rather than the coarse "both
/// are *some* type param" wildcard.
///
/// Why the rigids map is needed: an element is unified at a call against a
/// RIGIDIFIED enclosing param (WI-392/424: `Wrap.W := Var(Rigid(B))`), while a
/// `requires` entry is written over the canonical param symbol (`Tag[B]`, ↦
/// `Var::Global`). The two live in different var spaces; `param_rigids`
/// (`(canonical-global-var, rigid-term)` per param in scope, exactly as
/// `TypingEnv::param_rigids` holds — the enclosing sort's AND the operation's
/// own, WI-942) bridges them so the same parameter lands on one id from either
/// side. It must be the FULL list: keying it on the sort half alone is what made
/// an op-declared param σ-invisible.
///
/// Used by both requirement-attribution paths: same-spec forwarding
/// (`build_dep_projection` → [`entries_cover`]'s σ mode, WI-419/821) and
/// direct-body dispatch (`find_requires_slot` / `find_requires_location` →
/// [`entry_sigma_verdict`], WI-613/829).
pub struct SigmaCtx<'a> {
    pub(super) subst: &'a Substitution,
    pub(super) param_rigids: &'a [(VarId, TermId)],
}

/// The σ-class of a type element under `ctx`: the canonical representative
/// unification variable it resolves to, bridging the rigid↔global split. Two
/// elements denote the SAME type parameter iff their σ-classes are equal
/// ([`sigma_same`]). `None` when the element is concrete or not a recognizable
/// type parameter — a concrete carrier has no σ-class and is compared by
/// `dispatch_values_match` instead.
///
/// Walk to a canonical representative: at each step map the current term to a
/// logical var (a `Global`/`Rigid` directly, or a sort-parameter
/// `Ref`/`Ident`/nullary-`Fn` via its sort alias — mirroring
/// [`resolve_param_value_via_subst`]), then chase what `subst` binds that var to.
/// The chase follows BOTH var→var and var→sort-param-`Ref` bindings. A
/// `Var::Rigid` is terminal (a per-body skolem — never re-bound). An unbound
/// `Global` is the representative, first canonicalized through the enclosing-sort
/// param→rigid map so a written `Var::Global(B)` and a call-site `Var(Rigid(B))`
/// land on the same id. Bounded against a pathological cycle.
pub(super) fn sigma_class(kb: &KnowledgeBase, ctx: &SigmaCtx, value: TermId) -> Option<VarId> {
    sigma_class_terminal(kb, ctx, value).map(|(vid, _)| vid)
}

/// [`sigma_class`] plus HOW the chase terminated: `true` = at a rigid — direct
/// (`Var::Rigid`) or via the enclosing-sort param→rigid canonicalization —
/// meaning the element IS an enclosing-scope parameter, constrained in
/// context; `false` = at an unbound global nothing at this call determines.
/// WI-828's refusal explanation keys on that distinction to name the
/// genuinely-unconstrained elements.
pub(super) fn sigma_class_terminal(
    kb: &KnowledgeBase,
    ctx: &SigmaCtx,
    value: TermId,
) -> Option<(VarId, bool)> {
    let mut cur = value;
    for _ in 0..128 {
        let (vid, is_rigid) = elem_var_step(kb, cur)?;
        if is_rigid {
            return Some((vid, true));
        }
        match ctx.subst.resolve_as_value(vid) {
            Some(Value::Term { id: t, .. }) => cur = *t,
            _ => {
                let canon = canonical_global_var(kb, vid, ctx.param_rigids);
                // Canonicalized ⇒ the global aliases an enclosing-sort param's
                // rigid (rigids are freshly minted, so the id changed exactly
                // when a mapping existed).
                return Some((canon, canon != vid));
            }
        }
    }
    None
}

/// Do two type elements share a σ-class under `ctx` — i.e. resolve to the SAME
/// canonical unification variable (the same type parameter, bridging
/// rigid↔global)? A concrete or unrecognized element (no σ-class) is never "the
/// same param" as anything; use `dispatch_values_match` for those.
pub(super) fn sigma_same(kb: &KnowledgeBase, ctx: &SigmaCtx, a: TermId, b: TermId) -> bool {
    match (sigma_class(kb, ctx, a), sigma_class(kb, ctx, b)) {
        (Some(x), Some(y)) => x == y,
        _ => false,
    }
}

/// WI-613 — the σ-precise verdict for ONE `(a, b)` element pair: the policy
/// shared by [`binding_pair_covers`]' σ mode (the forwarding paths, where it
/// GATES — WI-821), [`entry_sigma_verdict`] (entry-vs-subst, the
/// direct-dispatch path) and [`reached_carrier_matches_call`] (the WI-653
/// transitive-coverage alignment)
/// so the attribution paths cannot disagree on what "same element" means. Two
/// type-params must share a σ-class ([`sigma_same`]); a mixed concrete/wildcard
/// pair does NOT pin the element (a wildcard covers loosely but is not precise);
/// two concretes use the same symmetric `dispatch_values_match` as the coarse
/// cover — EXCEPT a both-COMPOUND pair, which compares σ-structurally
/// (WI-825, see below). Symmetric in `a`/`b`, so callers may pass either order.
pub(super) fn sigma_pair_precise(
    kb: &mut KnowledgeBase,
    ctx: &SigmaCtx,
    a: TermId,
    b: TermId,
) -> bool {
    match (is_type_param_value(kb, a), is_type_param_value(kb, b)) {
        (true, true) => sigma_same(kb, ctx, a, b),
        (true, false) | (false, true) => false,
        (false, false) => {
            // WI-825: a pair whose sides are BOTH parameterized applications
            // (`Wrap[A = CT]` vs `Wrap[A = Wrap[A = CT]]`) compares
            // σ-STRUCTURALLY — same base sort AND each argument pair
            // recursively σ-covering (σ-classes at param leaves,
            // `dispatch_values_match` at ground leaves). The head-symbol
            // fallback in `dispatch_values_match` ignores the interiors
            // (`types_lesseq` rejects such a pair first, so the fallback was
            // the accepting leg), which let a caller entry cover a dep
            // σ-instantiated one constructor DEEPER and forward the shallower
            // dict. Any pair not both-parameterized keeps that dispatch match.
            //
            // The `a == b` short-circuit stays INSIDE this arm, not hoisted
            // above the `is_type_param_value` match: the `(true, true)` arm
            // deliberately REFUSES an identical but σ-unclassifiable param
            // pair (`sigma_same` is false when `sigma_class` is `None`), so a
            // top-level identity fast path would silently widen the gate.
            if a == b {
                // Identical terms are the same instantiation on both sides —
                // the pre-WI-825 verdict (`types_lesseq`'s equality leg) in
                // O(1), skipping the structural walk.
                return true;
            }
            match (parameterized_parts(kb, a), parameterized_parts(kb, b)) {
                (Some((base_a, pos_a, named_a)), Some((base_b, pos_b, named_b))) => {
                    // `for_bases` IS the same-base decision (`Label` iff the two
                    // bases are one canonical sort), so it doubles as the base
                    // gate and the key-match mode — spelled through the shared
                    // binding-key rule (WI-726/764/768, `binding_for_param`)
                    // rather than a fifth hand-rolled lookup. Mirrors the
                    // `match_candidate_against_goal` arm-2 spelling.
                    let key_match = BindingKeyMatch::for_bases(kb, base_a, base_b);
                    key_match == BindingKeyMatch::Label
                        && pos_a.len() == pos_b.len()
                        && named_a.len() == named_b.len()
                        && pos_a
                            .iter()
                            .zip(pos_b.iter())
                            .all(|(pa, pb)| sigma_pair_precise(kb, ctx, *pa, *pb))
                        && named_a.iter().all(|(k_a, v_a)| {
                            binding_for_param(kb, &named_b, *k_a, key_match)
                                .is_some_and(|v_b| sigma_pair_precise(kb, ctx, *v_a, *v_b))
                        })
                }
                _ => dispatch_values_match(kb, a, b) || dispatch_values_match(kb, b, a),
            }
        }
    }
}

/// WI-825: decompose a σ-mode element into its base sort and argument lists
/// iff it is a parameterized sort application (`Wrap[A = …]`,
/// [`TypeHead::Parameterized`] — the term backing `Fn{S, named}`, never the
/// `TypeExtractor` meta-ctors). Every other form (bare sort, type param,
/// arrow, tuple, …) returns `None` and keeps its existing pair verdict —
/// NOTE a both-arrow / both-tuple / both-effects-row pair (whether a
/// top-level element OR an interior leaf of the recursion in
/// [`sigma_pair_precise`]) retains `dispatch_values_match`'s head-fallback
/// acceptance: both heads are the same `TypeExtractor` meta-ctor symbol, so
/// `types_lesseq` rejects and the head fallback accepts with the interiors
/// IGNORED — the WI-825 residual for non-parameterized structural forms (e.g.
/// `Wrap[A = (Int)->Int]` vs `Wrap[A = (Int)->String]`, or
/// `Relation[T = (a, b)]` vs `Relation[T = (c, d)]`), tracked under WI-829.
/// Positional args ride along and are compared strictly — a mixed
/// positional+named application is not provably canonicalized away before
/// this path, and an ignored channel is exactly the bug class WI-825
/// closes. Deliberately not the candidate-side [`parametric_value_parts`]:
/// an element here is a written/σ-substituted TYPE (meta-ctors excluded,
/// no `SortView` unwrap), not a provider view.
pub(super) fn parameterized_parts(
    kb: &KnowledgeBase,
    t: TermId,
) -> Option<(
    Symbol,
    SmallVec<[TermId; 4]>,
    SmallVec<[(Symbol, TermId); 2]>,
)> {
    // Shape-filter first: only a `Fn` with named args can classify
    // `TypeHead::Parameterized`, and a bare-sort `Ref` (the common element)
    // fails here before `type_head`'s meta-ctor qualified-name ladder runs.
    let Term::Fn {
        pos_args,
        named_args,
        ..
    } = kb.get_term(t)
    else {
        return None;
    };
    if named_args.is_empty() {
        return None;
    }
    // `type_head` excludes the `TypeExtractor` meta-ctors (Arrow / NamedTuple /
    // EffectsRows / …), which are also `Fn{sym, named}`; only a user-sort
    // application is a structural-comparison target, and its base is the functor.
    let TypeHead::Parameterized { base } = type_head(kb, &TermIdView(t)) else {
        return None;
    };
    Some((base, pos_args.clone(), named_args.clone()))
}

/// WI-821 (code-review): THE one per-pair cover verdict for the forwarding
/// walks — `None` is the coarse rule (either side a type-param wildcard is
/// unconstrained; concrete/concrete via symmetric `dispatch_values_match`),
/// `Some(ctx)` the σ-precise gate ([`sigma_pair_precise`]). Owned once so
/// [`entries_cover`] (entry-vs-entry) and [`requires_entry_covers_goal`]
/// (entry-vs-goal) cannot drift — a per-pair rule change lands here or
/// nowhere. Symmetric in `a`/`b` in both modes.
///
/// The σ mode is COMPOUND-aware (WI-825, see [`sigma_pair_precise`]). The
/// coarse (`None`) mode deliberately keeps the head tolerance. That tolerance
/// IS behaviour-bearing, not diagnostic-only: `requires_entry_covers_goal`'s
/// `None` call decides `DispatchOutcome::Deferred` vs `NoCandidates` in live
/// op dispatch (`resolve_at_goal`, `resolve_inner` step 1), so a same-head
/// different-interior compound still coarse-covers and defers there — the
/// residual head-only cover, tracked under WI-829. Only the forwarding
/// strategies' `None` caller (`build_dispatching_dict_direct`) is the
/// req-insertion diagnostic path.
pub(super) fn binding_pair_covers(
    kb: &mut KnowledgeBase,
    sigma: Option<&SigmaCtx>,
    a: TermId,
    b: TermId,
) -> bool {
    match sigma {
        Some(ctx) => sigma_pair_precise(kb, ctx, a, b),
        None => {
            is_type_param_value(kb, a)
                || is_type_param_value(kb, b)
                || dispatch_values_match(kb, a, b)
                || dispatch_values_match(kb, b, a)
        }
    }
}

/// WI-613 — the σ-precise selection policy shared by the same-spec DIRECT
/// attribution matchers (flat chain and requires tree), so they resolve
/// ambiguity identically. From `candidates` (all coarse-covering one
/// deferred call), return the FIRST that satisfies `is_precise` — every precise
/// candidate shares the call's element σ-class, so they denote the same
/// requirement and the first is a deterministic, correct choice — else the first
/// candidate (no precise match / no σ context: genuinely ambiguous, so no worse
/// than the pre-WI-613 first-match). The FORWARDING matchers
/// (`build_dep_projection` Strategies 1/2) shared this policy until WI-821
/// replaced their fall-back with a strict σ-gate (disagreement = no cover).
/// `is_precise` is `FnMut` because the σ check borrows `kb` mutably.
pub(super) fn pick_precise<T: Copy>(
    candidates: &[T],
    mut is_precise: impl FnMut(T) -> bool,
) -> Option<T> {
    candidates
        .iter()
        .copied()
        .find(|&c| is_precise(c))
        .or_else(|| candidates.first().copied())
}

/// Map an element term to a logical var, returning `(var, is_rigid)`.
/// `is_rigid` marks a terminal skolem (`Var::Rigid`); a `Global` (direct or via
/// a sort-param alias) is chaseable. `None` for a concrete / unrecognized term.
pub(super) fn elem_var_step(kb: &KnowledgeBase, tid: TermId) -> Option<(VarId, bool)> {
    match kb.get_term(tid) {
        Term::Var(Var::Rigid(v)) => Some((*v, true)),
        Term::Var(Var::Global(v)) => Some((*v, false)),
        Term::Ref(sym) | Term::Ident(sym) if is_sort_param_symbol(kb, *sym) => {
            type_param_global_var(kb, *sym).map(|g| (g, false))
        }
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() && is_sort_param_symbol(kb, *functor) => {
            type_param_global_var(kb, *functor).map(|g| (g, false))
        }
        _ => None,
    }
}

/// WI-419: canonicalize a `Global` param var to the per-body `Var::Rigid` id the
/// rigidification minted for it, or return it unchanged when it is not a param in
/// scope (no rigid mapping). WI-942: "in scope" is the enclosing sort's params AND
/// the operation's own — pass `TypingEnv::param_rigids`, never the sort prefix.
pub(super) fn canonical_global_var(
    kb: &KnowledgeBase,
    g: VarId,
    param_rigids: &[(VarId, TermId)],
) -> VarId {
    for (canonical, rigid_term) in param_rigids {
        if *canonical == g {
            if let Term::Var(Var::Rigid(rv)) = kb.get_term(*rigid_term) {
                return *rv;
            }
        }
    }
    g
}

/// The canonical `Var::Global` a type-parameter symbol denotes, or `None` when it
/// denotes none. This is the one shared "type-param symbol → canonical VarId"
/// primitive underlying both worlds that reason about type-param identity: the
/// σ-class machinery ([`sigma_class`] via [`elem_var_step`], for requirement
/// attribution) and carrier grounding ([`declared_type_param_vid`],
/// [`type_param_vid_in_sort`], WI-424/600). They diverge in their layers — σ-class
/// adds the substitution chase + rigid bridge, carrier grounding stays structural and
/// carrier-agnostic — but the identity resolution is identical, so it lives here once.
///
/// WI-954 — ONE MAP READ. The loader decides a parameter's variable and publishes it
/// ([`KnowledgeBase::type_param_canonical_var`]); this reads it back. There is no
/// ladder, no channel to dispatch on, and no order to get wrong.
///
/// WHAT IT REPLACED — two rungs, one per SPELLING of a declaration:
///
///   * an `alias`-form declaration → its `SortAlias` fact ([`resolve_sort_alias`]).
///     `sort T = ?` and the WI-452 marked structured param are the sort-body cases —
///     but NOT only those: WI-402's existential carrier (`-> C ensures Spec[C, …]`,
///     `build_existential_return`) registers `C` this way in the OP's own scope.
///   * a BRACKET parameter (`operation cmp[T](…)`) → its op's
///     `OperationInfo.type_params`. The loader mints it its own var and asserts NO
///     `SortAlias`, which is why WI-943 had to TEACH this channel rather than derive it.
///
/// AND THE RUNGS DID NOT ONLY DIFFER IN COST — THE FIRST ONE ANSWERED THE WRONG
/// QUESTION. `resolve_sort_alias` answers for any `SortAlias` whose target is a
/// variable, and a top-level opaque `sort Term = ?` has one: it is a DECLARATION, not a
/// parameter of its namespace (`add_type_param` is gated on the enclosing scope being a
/// SORT, so a namespace-level abstract sort registers no parameter). MEASURED — map and
/// ladder computed side by side over every symbol of three corpus tiers (stdlib +
/// host bindings, + `anthill-todo`, + `examples`/`anthill-testcases`): they disagree on
/// EXACTLY 8 symbols, identically in all three, and every one of them answers `false`
/// to [`is_sort_param_symbol`] — `prelude.Type`, `prelude.Unit`, and `reflect`'s six
/// opaque sorts (`Term`, `FactRef`, `Symbol`, `SourceId`, `NodeOccurrence`,
/// `ConstraintId`). ZERO disagreement on a declared type parameter.
///
/// `resolve_sort_alias`' other callers gate on [`is_sort_param_symbol`] first for
/// exactly this reason ("collapsing every `sort_ref(Term)` into Term's alias Var would
/// lose the sort-ref form"); this reader did not, and [`declared_type_param_vid`]
/// inherited the miss. Reading the declaration closes it — a symbol that declares no
/// type parameter now denotes no parameter variable.
///
/// `pub` so a test can drive the invariant this function owns: that its answer and the
/// declaration's own are the SAME variable. Agreement is only assertable if both sides
/// are reachable from outside — `wi943_type_param_identity_test`,
/// `wi954_published_type_param_var_test`.
pub fn type_param_global_var(kb: &KnowledgeBase, sym: Symbol) -> Option<VarId> {
    match kb.canonical_type_param_var(sym).map(|tid| kb.get_term(tid)) {
        Some(Term::Var(Var::Global(v))) => Some(*v),
        _ => None,
    }
}

/// WI-865 — WHY a frame slot a value-only route entered holds no dictionary.
///
/// Rides on [`BridgeSlot::Absent`] and, through [`absence_marker_sym`], all the way to
/// the runtime refusal, which renders it. WI-857 built the channel for the RESOLVER's
/// failures — `NoMatch`, `Ambiguous` and `Cyclic` at a spec-half slot, recorded rather
/// than refused — and WI-865 carried their kind so the refusal at the read could say
/// which. WI-20260925-4ZZKZ retired that producer: a resolution that cannot fill a
/// slot now FAILS, and the load reports the failure kind itself
/// (`LoadError::UnsatisfiedProviderRequires::failure`). What is left are the three
/// absences only a route entered with argument VALUES can record, each at its own slot
/// and each for a reason a type-directed route does not have.
///
/// Every field is a SYMBOL, never a rendering: the record keys the marker name, and a
/// string differing per call would mint an unbounded symbol family on the per-call
/// dispatch path. The family is therefore a function of the PROGRAM.
///
/// `Hash` because [`AbsenceRecord`] keys the mint side of the marker table — see
/// [`absence_marker_sym`] for why re-minting has to be cheap.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum UnavailableWhy {
    /// WI-20260830-NX4FD — the ARGUMENT TYPES left a spec type-parameter of `goal`
    /// abstract, so NO PROVIDER WAS SEARCHED FOR. Only [`resolve_bridge_requirements`]
    /// produces it: that consumer pins the parent sort's parameters from the runtime
    /// argument types alone, and an element the operation's parameters do not mention
    /// (`FiniteCollection.Element`/`E` under `size(c: C)`) stays open. "No provider"
    /// would be a FALSEHOOD here and its repair a misdirection: `List` DOES provide
    /// `Iterable`, and "declare a provider for it" is not what an author whose call
    /// under-determines a slot has to do.
    ///
    /// FIELDLESS, and that is a claim rather than an omission (the first cut carried a
    /// `goal: Symbol` and /code-review was right that it was decorative): the bridge
    /// asks per slot and nothing under it was searched, so the failing goal IS the
    /// slot's own spec, which [`AbsenceRecord::Slot::spec`] already carries.
    UnderDetermined,
    /// WI-456 — a NAMED requirement slot of the carrier, reached by a dispatch that had
    /// only the argument VALUES. A named slot is a type parameter and a value carries
    /// none, so the provider its construction chose is not recoverable here; several
    /// providers of the slot's spec exist, so none is taken. Fieldless for
    /// [`Self::UnderDetermined`]'s reason: it is recorded only at its own slot.
    ///
    /// WI-20260921-R10KC — WHAT IS LEFT OF THIS, now that the largest producer is gone.
    /// Every SPEC DEFAULT BODY calling a body-less sibling used to arrive here: the
    /// dictionary was built at the call site and dropped, the frame was empty, and the
    /// dispatch fell to value-direction. It no longer does — `classify_pin_or_apply_within`
    /// threads the instance and `Interpreter::spec_instance_for_sibling_call` projects it
    /// — so the population that remains is the routes with NO STATIC TYPE to build a
    /// dictionary from, each MEASURED in
    /// `wi_r10kc_spec_default_body_dictionary_test`'s "THE ROUTES WITH NO STATIC TYPE"
    /// section — two of the three DRIVEN there, the SLD bridge stated rather than driven
    /// because the rule shape that reaches it residualizes one goal earlier:
    ///
    ///  * AN EXISTENTIAL RETURN, opened per use to a rigid skolem (`operation mk() ->
    ///    MySet[T = String]` over a body that builds at `O = ByLength`, kernel-language.md
    ///    WI-1063). The skolem names no provider, so no dictionary can be built at the
    ///    call site either. THIS is the live population, and the one whose refusal this
    ///    variant carries.
    ///  * THE HOST ENTRY does NOT reach here: `seed_entry_requirements` installs a
    ///    self-rooted STAND-IN rather than a marker (WI-868's decision, with three
    ///    measurements at [`crate::eval::Interpreter::stand_in_requirement`]), and the
    ///    read then falls to value-direction, which answers from the ARGUMENTS. Measured
    ///    as a silently WRONG answer for a named slot, and PINNED as such by
    ///    `the_host_entry_route_answers_by_value_direction`.
    ///  * THE SLD BRIDGE does not reach here either, by construction:
    ///    [`NamedSlotTies::Raise`] keeps the tie a verdict, and the bridge residualizes
    ///    rather than entering on a recorded absence.
    NamedSlotNotCarried,
    /// WI-20260922-ATFGH — an OP-HALF slot whose witness is written in a PARAMETER's
    /// argument type ([`SupplySource::witness_in_argument_type`], today EE0EP's
    /// `FromParam`), reached by a route that has the argument VALUES only.
    ///
    /// NamedSlotNotCarried's sibling one half over, and kept apart from it because the
    /// two differ in both what they can name and what repairs them. This one knows the
    /// PARAMETER (`param`) and the carrier's BINDER (`binder`), so the sentence names the
    /// slot as the body sees it, `s.O`; and it has a host spelling
    /// (`Interpreter::call_with_witnesses`), which the sort half's value-directed absence
    /// has not.
    ///
    /// Recorded where the goal has SEVERAL providers (a tie under
    /// [`DefaultRung::Unranked`]) or the arguments leave it under-determined — where any
    /// dictionary would
    /// be a construction for the signature rather than the value's own witness, the rival
    /// WI-1094 refused. A goal with ONE provider is not recorded: the value's
    /// construction had to choose it (see `witness_in_argument_type`). The SLD bridge
    /// keeps a tie instead, and delays on it.
    ParamSlotNotCarried { param: Symbol, binder: Symbol },
}

/// WI-865 — the absence a `NoProvider` marker symbol records. Filed on the KB by
/// [`absence_marker_sym`] and read back by [`marker_refusal`]; see
/// `KnowledgeBase::absence_records` for why it is a side table and not a payload on
/// the dictionary value.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum AbsenceRecord {
    /// A frame slot a value-only route recorded absent ([`BridgeSlot::Absent`]).
    ///
    /// `spec` is the SLOT's — where the absence sits. WI-865 paired it with a `below`
    /// bit for a resolver failure forwarded from beneath the slot; every absence left
    /// is recorded at its own slot (WI-20260925-4ZZKZ), so there is no deeper level to
    /// point at and the bit went with the resolver's producer.
    Slot { spec: Symbol, why: UnavailableWhy },
    /// The sub-slots of eval's host-entry STAND-IN (`Interpreter::
    /// stand_in_requirement`). Nothing resolved and nothing failed: the frame was
    /// entered from the host with no dictionary at all, so the remedy is
    /// `call_with_requirements` and not anything in the program. It names no spec —
    /// one stand-in marker is SHARED across every sub-slot of the chain (they are
    /// empty and interchangeable, and a dictionary's children are `Rc`-backed), so
    /// there is no one slot for it to name.
    HostEntry,
}

/// WI-857/WI-865 — the functor a dictionary slot carries when it holds no dictionary
/// ([`BridgeSlot::Absent`], and the host-entry stand-in's sub-slots), and the one place a
/// marker is minted.
///
/// Not a sort: it is INTERNED, never DEFINED, and `SymbolTable` keeps those two maps
/// disjoint — that, not the choice of name, is what keeps `sort_ops_lookup` from ever
/// answering for it, and it is why the marker cannot be promoted to a declared
/// `anthill.realization.runtime` sort however much tidier that would read: a DEFINED
/// functor is one `resolve_op_target` falls through on, which is the silent
/// host-default dispatch the marker exists to refuse. It is NOT reserved, so a
/// program (or a future stdlib file) declaring `namespace anthill.reflect … sort
/// NoProvider` would produce a real sort whose qualified name matches, and every
/// dictionary rooted at it would then be refused; `intern_unique` cannot be used
/// instead because producer and consumer must agree on the symbol.
///
/// WI-865 made it a FAMILY: the name is rendered from `rec`, so distinct absences get
/// distinct symbols and the record filed under each is recoverable at the read. The
/// name is a pure function of the record and interning is idempotent, so re-minting
/// the same absence yields the same symbol and re-files the same row — which is what
/// lets both dictionary producers mint independently and still agree. It stays
/// SELF-DESCRIBING (`Dictionary.impl` is an inspection face, and the marker is a
/// truthful answer to it), while the typed record — not the name — is what
/// [`marker_refusal`] renders from; nothing parses this string back.
///
/// Every use is refused through [`marker_refusal`], which is what turns a carried
/// absence into a loud error exactly where the absence matters.
///
/// THE REPEAT MINT IS THE COMMON ONE, and it must not allocate: `dictionary_of_absence`
/// runs per CALL on the value-directed / bridge dispatch path. Rendering the name each
/// time would be three `String`s per marker per call where WI-857's single hoisted
/// symbol was one hash of a `&'static str`, so the record keys the table in BOTH
/// directions and a re-mint is one probe.
pub(crate) fn absence_marker_sym(kb: &mut KnowledgeBase, rec: AbsenceRecord) -> Symbol {
    if let Some(sym) = kb.absence_marker_for(&rec) {
        return sym;
    }
    let name = match &rec {
        // The bare prefix, so eval's stand-in keeps the exact symbol WI-857 minted.
        AbsenceRecord::HostEntry => NO_PROVIDER_NAME.to_string(),
        AbsenceRecord::Slot { spec, why } => {
            let spec_qn = kb.qualified_name_of(*spec).to_string();
            let detail = match why {
                // The name already leads with `spec_qn`, which IS this absence's goal.
                UnavailableWhy::UnderDetermined => " unpinned".to_string(),
                UnavailableWhy::NamedSlotNotCarried => " named slot not carried".to_string(),
                // Qualified, so two parameters of one short name on different
                // operations mint distinct markers.
                UnavailableWhy::ParamSlotNotCarried { param, binder } => format!(
                    " param slot not carried {} {}",
                    kb.qualified_name_of(*param),
                    kb.qualified_name_of(*binder),
                ),
            };
            format!("{NO_PROVIDER_NAME}[{spec_qn}{detail}]")
        }
    };
    let sym = kb.intern(&name);
    kb.record_absence(sym, rec);
    sym
}

/// True iff `sym` is one of [`absence_marker_sym`]'s markers. By NAME, because this
/// reader holds only a shared `kb` and cannot intern — and it IS on the per-dispatch
/// path (via [`marker_refusal`] ← `resolve_op_target_checked` ← every dict-threaded
/// dispatch). The cost is one `local_name_of` plus a 26-byte prefix compare that
/// short-circuits on length for nearly every call; making it a `Symbol` compare needs
/// the marker cached where a `&KnowledgeBase` reader can see it (a KB well-known
/// slot), which the interpreter's `fields.no_provider` does only for eval — and since
/// WI-865 there is no single symbol to cache.
///
/// A PREFIX, and the reason it is safe is the bracket: every non-bare marker name is
/// `anthill.reflect.NoProvider[…]`, so the only names this admits beyond the family
/// are ones a program would have to spell with that exact 26-byte head — the same
/// (unreserved, documented) collision [`absence_marker_sym`] already names.
///
/// IDENTITY, NOT REASON. The reason lives in `KnowledgeBase::absence_record` and may
/// be absent (a hand-built marker in a test); this must not, or a marker would stop
/// being refused the moment its record went missing — the silent fall-through the
/// whole mechanism exists to prevent.
pub(crate) fn is_absence_marker(kb: &KnowledgeBase, sym: Symbol) -> bool {
    kb.local_name_of(sym).starts_with(NO_PROVIDER_NAME)
}

const NO_PROVIDER_NAME: &str = "anthill.reflect.NoProvider";

/// WI-227: translate a `ResolvedRequiresNode` into a projection IR term.
/// `FromScope` becomes `var_ref(name = __req_<caller chain slot>)`;
/// `Leaf` becomes `Dictionary(impl: impl)`; `Conditional`
/// recursively emits sub-projections and wraps them in a
/// `Dictionary(<subs …>, impl: impl)`. `caller_sort` is the
/// enclosing op's parent sort, used to name `FromScope` chain slots.
pub(super) fn emit_tree_as_projection(
    kb: &mut KnowledgeBase,
    // WI-1033: the caller's `DictChain`, not its Symbol. `FromScope`'s `scope_index`
    // indexes `ResolutionScope.available_requires` — which IS this chain — so naming it
    // from a separately-passed sort was the last place a name could come from a
    // different list than the index did. It is also what made `DictChain::unnamed`'s
    // "cannot produce a mis-indexed dictionary" true: through this path it was false.
    caller: &DictChain,
    tree: &ResolvedRequiresNode,
    syms: &ProjectionSyms,
) -> Option<TermId> {
    match tree {
        ResolvedRequiresNode::FromScope {
            scope_index,
            projection,
            ..
        } => {
            let name = caller.name_at(kb, *scope_index)?;
            let mut t = build_req_var_ref(kb, syms, name);
            for &k in projection {
                t = build_req_at_sort(kb, syms, t, k);
            }
            Some(t)
        }
        ResolvedRequiresNode::Leaf { impl_sort, .. } => {
            Some(build_empty_bundle(kb, syms, *impl_sort))
        }
        ResolvedRequiresNode::Conditional {
            impl_sort,
            sub_resolutions,
            ..
        } => {
            let mut sub_terms: SmallVec<[TermId; 4]> = SmallVec::new();
            for sub in sub_resolutions {
                sub_terms.push(emit_tree_as_projection(kb, caller, sub, syms)?);
            }
            Some(build_dictionary_term(kb, syms, *impl_sort, &sub_terms))
        }
    }
}

/// Build a value-position `var_ref(name = Ref(name_sym))` — the named
/// requirement-param read that replaces the positional
/// `requirement_at_current(slot)` under the names model (WI-237). Shared
/// by `build_dep_projection` Strategies 1 & 2-inner, `emit_tree_as_projection`'s
/// `FromScope`, and the `DeferToRequirement` emitter. There is no Self-slot
/// `+1` shift any more — the Self requirement is the named param `__req_self`.
pub(super) fn build_req_var_ref(
    kb: &mut KnowledgeBase,
    syms: &ProjectionSyms,
    name_sym: Symbol,
) -> TermId {
    let name_ref = kb.alloc(Term::Ref(name_sym));
    kb.alloc(Term::Fn {
        functor: syms.var_ref,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(syms.name, name_ref)]),
    })
}

/// Build `requirement_at_sort(chain = <inner>, slot = <k>)`.
pub(super) fn build_req_at_sort(
    kb: &mut KnowledgeBase,
    syms: &ProjectionSyms,
    inner: TermId,
    k: usize,
) -> TermId {
    let slot_lit = kb.alloc(Term::Const(Literal::Int(k as i64)));
    kb.alloc(Term::Fn {
        functor: syms.ras,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(syms.chain, inner), (syms.slot, slot_lit)]),
    })
}

/// Build `Dictionary(impl: <Ref(functor)>)` — a dictionary bundling nothing.
/// Two producers need it: a `Leaf` resolution and `build_dep_projection`'s synthetic
/// `EffectsRuntime` anchor. One owner, so the spelling of a childless dictionary has one
/// definition.
fn build_empty_bundle(kb: &mut KnowledgeBase, syms: &ProjectionSyms, functor: Symbol) -> TermId {
    build_dictionary_term(kb, syms, functor, &[])
}

/// Build the IR construction node `Dictionary(sub₀ … subₙ₋₁, impl = <Ref(impl)>)`.
///
/// WI-1045 — ONE SPELLING. This term's functor and key set are the DICTIONARY's,
/// not a second constructor's: the sub-dictionaries are POSITIONAL children (slot
/// `k` is the k-th entry of the WI-857 layout, so the order is the identity) and
/// the provider is the one named child, exactly as
/// [`crate::eval::value::Dictionary`] lays out the value this node evaluates to.
/// It used to be `construct_requirement(impl_functor =, requirements = <cons
/// spine>)` — a different functor, different key names, and a list where the value
/// had positional children, for one thing.
pub(super) fn build_dictionary_term(
    kb: &mut KnowledgeBase,
    syms: &ProjectionSyms,
    impl_sym: Symbol,
    subs: &[TermId],
) -> TermId {
    let impl_ref = kb.alloc(Term::Ref(impl_sym));
    kb.alloc(Term::Fn {
        functor: syms.dict_ctor,
        pos_args: SmallVec::from_slice(subs),
        named_args: SmallVec::from_slice(&[(syms.dict_impl, impl_ref)]),
    })
}

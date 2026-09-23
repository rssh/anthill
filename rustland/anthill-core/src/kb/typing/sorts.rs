//! Unified type checking: `type_check_sorts` and the per-sort checks it drives
//! (signatures, effects, entity facts, provides).

use super::*;

/// Type-check the given sort terms and return errors as `LoadError` for
/// the load pipeline. Use [`type_check_sorts_typed`] when structured
/// `TypeError` values are needed (programmatic access, IDE diagnostics).
pub fn type_check_sorts(kb: &mut KnowledgeBase, sort_names: &[Symbol]) -> Vec<LoadError> {
    let (typed, sources) = type_check_sorts_collect(kb, sort_names);
    typed
        .iter()
        .zip(sources.iter())
        .map(|(e, src)| {
            let le = e.to_load_error(kb);
            // WI-745: attribute to the file the error's span indexes into (an
            // entity-fact / op-body error carries its file's `source_id`), so it
            // renders `path:line:col` instead of a byte offset naming nothing.
            match src {
                Some(sid) => le.located_in_kb_source(kb, *sid),
                None => le,
            }
        })
        .collect()
}

/// Structured form of [`type_check_sorts`]: returns `Vec<TypeError>`,
/// preserving occurrence ids and term ids so consumers can format on
/// demand or filter by variant.
/// Feature flag — type-check + simp-rewrite operations declared at
/// *namespace* level (free functions, e.g. the `anthill.cli.parse` parser).
/// They have bodies in `op_bodies` but no `SortInfo`, so the sort loop in
/// [`type_check_sorts_typed`] never reaches them; before WI-289 they were
/// **not type-checked at all** (a pre-existing gap, independent of WI-283).
///
/// **ON (WI-289, delivered).** The typer now handles the free-op-body
/// constructs that the trial sweep surfaced — higher-order calls of
/// `Function[A, B]`-typed values (`f(f(x))`, via [`arrow_function_compatible`]),
/// effect-declaration checks, and name resolution — and the eval fixtures that
/// genuinely lacked a declaration were fixed. Kept as a named marker for the
/// free-op sweep below (and so the acceptance's `TYPECHECK_FREE_OPS = true`
/// stays greppable); the `false` path is retained only as a debug kill-switch.
const TYPECHECK_FREE_OPS: bool = true;

pub fn type_check_sorts_typed(kb: &mut KnowledgeBase, sort_names: &[Symbol]) -> Vec<TypeError> {
    type_check_sorts_collect(kb, sort_names).0
}

/// WI-745: like [`type_check_sorts_typed`], but also returns, parallel to the
/// errors, the `SourceId` of the file each error's span indexes into — `None`
/// for a whole-KB pass whose error isn't tied to one file. Entity-fact and
/// operation-body errors are tagged (all of one fact's / one body's occurrences
/// carry that file's `source_id`), so `type_check_sorts` can render them
/// `path:line:col` instead of a bare byte offset. Passes after the sort loop
/// (signature/rule-body/provider checks) leave `None`.
pub(super) fn type_check_sorts_collect(
    kb: &mut KnowledgeBase,
    sort_names: &[Symbol],
) -> (Vec<TypeError>, Vec<Option<crate::span::SourceId>>) {
    let mut errors: Vec<TypeError> = Vec::new();
    // Parallel to `errors`: the file each error belongs to, where known.
    let mut sources: Vec<Option<crate::span::SourceId>> = Vec::new();
    // WI-656 — build the O(1) operation-signature index once, up front: the per-op
    // and per-node passes below make `lookup_operation_info` the typer's hottest
    // call, and without this index each call linearly scans every `OperationInfo`
    // fact (quadratic overall). Every `OperationInfo` fact is asserted by now.
    let malformed_type_params = crate::kb::op_info::build_op_signatures(kb);
    // WI-849 — the LOUD half of `extract_type_params`' skip. A `type_params` entry that
    // is not a logical variable cannot become a type parameter, and dropping it silently
    // (which is what happened before) leaves the parameter uncheckable, unbindable and
    // unskolemizable with no diagnostic anywhere. The decode itself cannot raise — it
    // runs under `&KnowledgeBase`, pre-typer — so the sweep above carries the offenders
    // out and they are reported here. `None` source: this is a whole-KB pass, and the
    // offending fact carries no occurrence span.
    for (op_sym, bad) in malformed_type_params {
        // Rendered HERE, where a renderer is in reach. `build_op_signatures` carries the
        // offending VALUE out rather than a string precisely so this renders readably
        // instead of the `Fn { functor: Symbol(16), … TermId(3060) }` a `{:?}` at the
        // decode site produced. Carrier-neutral, so a value-fact head's bad entry — which
        // has no `TermId` at all — renders by the same path as a term-carried one.
        // `TermPrinter` for a term-carried offender: it is a general TERM printer
        // (`.anthill` source text), whereas `type_display_name_value` is a TYPE renderer
        // and falls back to leaking `TermId(13506)` for an entry that is not a type —
        // which is exactly what an offender here is. A non-term carrier has no TermId to
        // print, so it renders by the carrier-neutral path.
        let rendered = match &bad {
            Value::Term { id, .. } => {
                crate::persistence::print::TermPrinter::over(kb).print_term(*id)
            }
            other => type_display_name_value(kb, other),
        };
        errors.push(TypeError::Other {
            site: TypeError::here(),
            span: None,
            context: TypeErrorContext::OperationTypeParams { op_name: op_sym },
            expected: "each `type_params` entry to be a type variable".to_string(),
            // Says "the `OperationInfo` fact naming X", NOT "operation X" (review). The
            // report is reachable ONLY for a symbol the loader emitted no fact for:
            // `build_op_signatures` keeps the FIRST fact per name and the loader emits
            // one for every real operation, so a hand-written fact naming a real
            // operation is shadowed and never decoded. Whatever reaches here is
            // therefore NOT an operation — calling it one names the wrong thing, the
            // same defect WI-839's review fixed in `TypeArgsOnNonOperation`.
            actual: format!(
                "the `OperationInfo` fact naming '{}' declares a type parameter that is \
                 not a variable ({rendered}), so it can never be bound at a call, checked \
                 for being unconstrained, or skolemized in a body",
                kb.qualified_name_of(op_sym),
            ),
        });
        sources.push(None);
    }
    // WI-659 — likewise index the SortAlias facts once: `resolve_sort_alias` is
    // called on many sort-references per node and was the #1 hotspot post-WI-656
    // (a double linear scan of every SortAlias fact per call).
    build_sort_alias_index(kb);
    // WI-660 — index the SortProvidesInfo (provider/coherence) facts once, keyed by
    // canonical spec-base and by carrier short-name, so the dispatch/coherence sites
    // stop scanning every provides fact per call. Sound build-once: `SortProvidesInfo`
    // is `constant` (053/WI-665) so it cannot mutate at runtime.
    build_provides_index(kb);
    // WI-671 — index the SortInfo (per-sort reflect metadata) facts once, keyed by the
    // sort's short name, so the four per-query keyed lookups (`find_sort_info` — called
    // once per sort in the loop below — `sort_operation_names`, `operations_of_sort`,
    // `collect_sort_operations`) stop scanning every SortInfo fact per call. Sound
    // build-once: SortInfo is frozen at the end of the file-loading loop (only
    // `emit_sort_info` asserts it; nothing re-asserts it), so no runtime guard is
    // needed and no eq_derive rebuild (eq_derive never touches SortInfo).
    build_sort_info_index(kb);
    // WI-1112 — and the SortRequiresInfo facts, keyed by canonical `sort_ref`, so
    // `collect_sort_requires` stops scanning the whole relation once per requires-TREE
    // node. Sound here: both its producers (`load_requires_decl`,
    // `resolve_requires_bindings`) are done by this line, and any later one drops the
    // index via `invalidate_requires_chain_cache` — see `KnowledgeBase::requires_index`.
    build_requires_index(kb);
    // WI-1082 — elaborate every member's declared RETURN so §3's tie is WRITTEN rather than
    // left as an absence a width-ignoring comparison cannot refute. AFTER the three index
    // builds above: it reads `canonical_sort_sym` (the SortAlias index) per parameter and the
    // signatures `build_op_signatures` just cached, and it must land BEFORE the per-sort loop
    // below, where `check_operation_bodies` and every `check_apply_iter` read those signatures.
    elaborate_self_ties(kb, sort_names);
    // WI-657(6) — resolve the `anthill.reflect.TupleLiteral` symbol once, so the
    // per-constructor-arg `is_tuple_lit` compares a `Symbol` rather than the long
    // qualified-name string. Reflect is fully loaded by now; `None` (reflect-less
    // KB) leaves `is_tuple_lit` on its exact string fallback.
    kb.tuple_literal_sym = kb.try_resolve_symbol(dt::qualified(dt::TUPLE_LITERAL));
    // Ops reached via a sort's `SortInfo` — so the gated free-op sweep
    // doesn't re-check them (collected only when the sweep is enabled).
    let mut sort_owned_ops: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    // WI-603: the sort-scoped non-fact rules whose contradiction the single
    // `type_rule_bodies` pass should report — the exact set the removed
    // `check_rule_typing` walked (`by_domain` over each SortInfo sort). A free
    // namespace-level rule's contradiction stays unreported, as before.
    let mut rule_typing_reportable: std::collections::HashSet<crate::kb::RuleId> =
        std::collections::HashSet::new();

    // WI-314 / WI-20260920-E3DC5 — the region set for result-escape masking. PROGRAM-GLOBAL
    // and loop-invariant across this pass, so it is computed here, once, and threaded into
    // every `check_operation_bodies` call; that function used to compute it itself and so
    // walked the whole provision relation once per SORT. Its own comment carries the
    // measurement and the `debug_assert` that pins the invariance.
    //
    // ABOVE BOTH CALLS, so the sort loop and the free-op sweep share the one set.
    let region_sorts = crate::kb::region::region_sorts(kb);

    if kb.try_resolve_symbol("anthill.reflect.SortInfo").is_some() {
        for &sort_sym in sort_names {
            let sort_info = find_sort_info(kb, sort_sym);
            let (ctor_syms, op_syms) = match sort_info {
                Some((ctors, ops)) => (ctors, ops),
                // WI-928 — JUSTIFIED, and only since this ticket. `sort_names` is
                // `LoadResult.defined_sorts`, and both of its producers now emit a
                // `SortInfo` for every name they push: `load_sort_with_body` (always
                // did) and `load_entity` (§6.3's free-standing spelling, added here).
                // So a `None` is no longer "this declaration has no record" — the
                // shape that made this arm a SILENT SKIP of 68 entities' facts, which
                // is the defect this ticket fixes. What remains is a KB that has no
                // `anthill.reflect.SortInfo` symbol to emit under at all, i.e. one
                // loaded without reflect: the guard above already answers that case
                // for the whole loop, so reaching here means a caller passed a name
                // that no load defined. Nothing to report about it and nothing to
                // check — there is no declaration. MEASURED rather than argued: two
                // full-workspace runs with a `panic!` in this arm never reached it.
                None => continue,
            };

            check_entity_facts(kb, &ctor_syms, &mut errors, &mut sources);
            check_operation_bodies(kb, &op_syms, &mut errors, &mut sources, &region_sorts);
            if TYPECHECK_FREE_OPS {
                sort_owned_ops.extend(op_syms.iter().copied());
            }
            check_pattern_fragment(kb, sort_sym, &mut errors);
            // WI-745 invariant, restored INSIDE the loop (review): `sources` must stay
            // parallel to `errors`, and `check_pattern_fragment` takes only `errors` (its
            // diagnostics are per-SORT, with no one file to attribute them to). The pad
            // at the end of this function cannot substitute — once this sort emits one,
            // every LATER sort's entity-fact / operation-body error pairs with the
            // PREVIOUS error's `SourceId` and renders `path:line:col` for the wrong file.
            sources.resize(errors.len(), None);
            // WI-603: contradiction is now reported by the single `type_rule_bodies`
            // pass below (one `collect_rule_var_types` per rule). Record which
            // non-fact rules `check_rule_typing` would have walked so that pass
            // preserves the exact reporting scope.
            for rid in kb.by_domain(sort_sym) {
                if !kb.is_fact(rid) {
                    rule_typing_reportable.insert(rid);
                }
            }
        }
    }

    // WI-289 (ON — see [`TYPECHECK_FREE_OPS`]): type-check +
    // simp-rewrite every operation body not owned by a sort. Snapshot first
    // — typing mutates `op_bodies` via the simp write-back; `check_operation_
    // bodies` skips body-less / OperationInfo-less symbols and derives each
    // op's enclosing sort from its QN parent (a namespace ⇒ no requires).
    if TYPECHECK_FREE_OPS {
        let free_ops: Vec<Symbol> = kb
            .op_bodies_iter()
            .map(|(s, _)| s)
            .filter(|s| !sort_owned_ops.contains(s))
            .collect();
        if !free_ops.is_empty() {
            check_operation_bodies(kb, &free_ops, &mut errors, &mut sources, &region_sorts);
        }
    }

    // WI-945: every call site whose parent-bundle dictionary could not be built for an
    // element nothing at the call pins. HERE and not inside either sweep above: the
    // verdict reads the CALLEE's body classifications, and only now has every body
    // been through one of the two.
    report_unsuppliable_requirements(kb, &mut errors, &mut sources);
    // …and nothing may park after it. Only `check_operation_bodies` sets the
    // `enclosing_op` the park is gated on, so today no later pass can — this asserts
    // that rather than trusting it, because a park added downstream would otherwise be
    // dropped in silence (/code-review).
    debug_assert!(
        kb.unsuppliable_requirements.is_empty(),
        "a requirement refusal was parked after `report_unsuppliable_requirements` drained \
         the queue — it would never be reported",
    );

    // WI-398: signature well-formedness over EVERY operation — independent of the
    // sort/body split above, so a body-less FREE spec is covered too.
    errors.extend(check_operation_signatures(kb));

    // WI-701 (proposal 054 §"Branch and External"): reject a declared effect row that
    // carries BOTH Branch and External — a Branch region may not perform External.
    // Load-time, over every OperationInfo fact, like the signature check above.
    errors.extend(check_branch_external_exclusion(kb));

    // WI-282 + WI-603: type every rule body in one pass — collect each rule's var
    // types once, report a (sort-scoped) contradiction, dispatch its `Expr::DotApply`
    // to method/field form, and stamp the collected type onto every `Var` leaf.
    // Runs over ALL rules (free namespace-level rules too, which the sort loop
    // above misses) and after signature checks, so the operation/entity metadata
    // the collection + dispatch read is settled.
    // WI-1026: takes `sources` too — this pass now raises the WI-1012 supplier-tie
    // refusal, whose value over eval's face is precisely that it is LOCATED.
    // Padded HERE, like the sort loop's own pad above: the untagged passes between that
    // loop and this call (`check_operation_signatures`,
    // `check_branch_external_exclusion` — WI-945's
    // `report_unsuppliable_requirements` pads and pairs its own) push errors, and the
    // `check_entity_facts` / `check_operation_bodies` contract is that `sources` is
    // parallel on ENTRY. Repairing it inside the callee gave this one pass a second
    // convention.
    sources.resize(errors.len(), None);
    type_rule_bodies(kb, &rule_typing_reportable, &mut errors, &mut sources);

    // WI-702 (proposal 054 §"Consumers"): reject a `@[simp]`/`@[unfold]` rewrite whose
    // sides mention an effectful operation — firing it would duplicate/reorder/drop
    // the call. Load-time (all OperationInfo facts loaded), like the WI-701 sibling,
    // and AFTER `type_rule_bodies` so a body/guard method call (`?x.effectful_op()`)
    // is already dispatched to `Apply` form — otherwise the un-dispatched `DotApply`
    // would slip the functor walk (mirrors `record_find_dictionary_grounding` below).
    errors.extend(check_simp_effectful_ops(kb));

    // WI-300: rewrite every rule body's `find_dictionary(X)` guard (the converter's
    // desugaring of a rule-body `requires(X)`) into the resolver-ready
    // `find_dictionary(spec_base, op_functor, op_arg…)` form, recording which body
    // op-call witnesses ground spec X. Runs AFTER dot-dispatch so a `?x.eq(?y)`
    // witness is already an `Apply`, and after signature checks so the spec-op
    // metadata the grounding reads is settled.
    // WI-742 (proposal 060 §2): compile every `?x: T` on a RELATIONAL head into a
    // prepended `domain(?x, T)` body goal. BEFORE the requirement sweep below, so the
    // typed binding is visible as the SECOND ANCHOR a `require[Spec[T]]` may ground on
    // (proposal 060 §3); after `type_rule_bodies`, so the bodies it extends are settled
    // and `collect_rule_var_types` has already read the body the AUTHOR wrote — the
    // generated goal must not feed the inference whose output it exists to enforce.
    install_typed_head_domain_goals(kb);

    errors.extend(record_find_dictionary_grounding(kb));

    // WI-642: the STATIC face of WI-300. `record_find_dictionary_grounding` above
    // handles a rule that DECLARES its requirement (`requires(X)` → find_dictionary);
    // this flags a rule-body spec-op call whose requirement is neither declared nor
    // satisfiable by a provision — statically missing, so the WI-300 guard would only
    // `DontFire` at resolution (a silent clause failure). Runs after the dictionary
    // rewrite so a declared `requires` is visible, and after `type_rule_bodies` so the
    // per-arg `inferred_type` the carrier decision reads is stamped.
    errors.extend(check_rule_body_requirements(kb));

    // WI-20260917-NR6FJ: the OPERATION-CALL twin of the above — a rule-body call to an
    // operation whose declared `requires` names a concrete carrier that provides no such
    // spec. Before this the program loaded and then either ABORTED in the eval bridge
    // (a body-less spec op) or silently folded the spec's default (a defaulted one).
    errors.extend(check_rule_body_operation_requires(kb));

    // WI-583 / WI-20260822-J38JE item 4: the STATIC face of the resolver's goal
    // routing — refuse a rule-body goal that has no goal reading. A Bool-returning op
    // used bare in a goal (`:- valid(?x)`) is gated to `eq(valid(?x), true)` at resolve
    // time (`bare_bodied_bool_relation`) and a boolean CONSTANT is a search answered in
    // `step_init`; a NON-Bool op and a non-boolean constant have no reading and would
    // otherwise fall through to a silent failed lookup — flag both loudly here. Same
    // rule-body-walk phase as `check_rule_body_requirements`, after
    // `build_op_signatures` so every op's return type is available.
    //
    // WI-745's localization, for the ONE late pass that can supply it: every error
    // this pass raises is anchored on a body occurrence, whose `SourceSpan` names its
    // file. The block's other passes push untagged errors (padded `None` below), so the
    // pad has to happen HERE, before these are pushed, or `sources` would fall out of
    // step with `errors`. Without it both this pass's errors render a bare byte offset,
    // which names nothing — measured on `:- 42`, which reported `at 98..100`.
    sources.resize(errors.len(), None);
    for (err, src) in check_rule_body_goal_readings(kb) {
        errors.push(err);
        sources.push(src);
    }

    // WI-650: flag a semantic `=`/`eq`/`neq` call whose operand's sort declares
    // its OWN `eq` override with no backing (a bodyless placeholder — `Map` after
    // its relational eq apparatus was dropped). Runs after `type_rule_bodies` (the
    // rule-body operand `inferred_type` it reads) and `check_operation_bodies` (the
    // op-body Stamp frame), so every operand carries its inferred sort.
    errors.extend(check_eq_override_backing(kb));

    // WI-745: the passes after the sort loop (signature/rule-body/provider/eq
    // checks) push untagged errors — pad `sources` with `None` so it stays
    // parallel to `errors`.
    sources.resize(errors.len(), None);
    (errors, sources)
}

/// WI-398: reject a CYCLIC cross-parameter type projection (`f(a: b.T, b: a.T)`, or the
/// length-1 self-projection `f(a: a.T)`) loudly at LOAD, for EVERY operation. Unlike
/// `check_operation_bodies` (keyed off `SortInfo` / `op_bodies`, so it skips body-less
/// FREE specs), this walks ALL `OperationInfo` facts, so no operation's signature escapes
/// the check. A cyclic signature has no synthesis order — it is ill-formed by the
/// projection's definitional content (design path-dependent-types.md §6, WI-398).
fn check_operation_signatures(kb: &KnowledgeBase) -> Vec<TypeError> {
    let mut errors: Vec<TypeError> = Vec::new();
    // One operation symbol may carry more than one `OperationInfo` fact (e.g. a spec and
    // its impl); report each cyclic signature once.
    let mut reported: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    for (op_sym, params) in crate::kb::op_info::all_operation_params(kb) {
        if !reported.insert(op_sym) {
            continue; // already reported this op (multiple OperationInfo facts)
        }
        if let Some(cycle_syms) = param_projection_cycle(kb, &params) {
            let mut names: Vec<String> = cycle_syms
                .iter()
                .map(|s| kb.local_name_of(*s).to_owned())
                .collect();
            // Close the cycle visually (`a -> b -> a`) so the diagnostic reads as one.
            if let Some(first) = names.first().cloned() {
                names.push(first);
            }
            let span = kb.functor_span(op_sym).map(|s| s.span);
            errors.push(projection_type_error(
                &TypeErrorContext::OperationReturn {
                    op_name: op_sym,
                    surface: None,
                },
                span,
                &format!(
                    "cyclic cross-parameter type projection among parameters: {} — a \
                 parameter's type may project an EARLIER parameter, not form a cycle",
                    names.join(" -> "),
                ),
            ));
        }
    }
    errors
}

/// The `label` child of a `guarded(label, guard)` effect atom, else `None`. WI-067
/// (proposal 048): a guarded effect element `E :- g` is CONSERVATIVELY PRESENT — the
/// same over-approximation [`decompose_effect_row_raw`] makes (guarded contributes its
/// label exactly like `present` until discharge lands) — so the co-occurrence gate
/// peeks past the guard to the underlying sort rather than silently missing it.
///
/// Matched by QUALIFIED functor (WI-818 review), like
/// [`explode_incurred_effect_row`]'s row-algebra recognition and unlike the
/// short-name decompose walk: this helper also feeds the op-effects
/// conformance ADMISSION (a declared guarded atom admits a body incurring its
/// raw label), where a user sort that merely SHARES the short name `guarded`
/// must not be read as the kernel algebra atom — that would admit an effect
/// the row never declared.
pub(super) fn guarded_effect_label(kb: &KnowledgeBase, v: &Value) -> Option<Value> {
    let sym = v.head(kb).functor_sym()?;
    if kb.qualified_name_of(sym) == "anthill.prelude.EffectExpression.guarded" {
        named_child_value(kb, v, kb.lookup_symbol("label")?)
    } else {
        None
    }
}

/// Does an effect label name the effect sort `sort` (canonically)? `Branch` and
/// `External` are nullary effect sorts, so a PRESENT label is a bare `sort_ref`; the
/// `Parameterized` arm is defensive so a future indexed spelling of either sort is
/// still recognized rather than silently missed. A guarded label is peeked past to its
/// underlying sort (conservatively present — see [`guarded_effect_label`]); an
/// `absent(...)` (`-External`) is deliberately NOT unwrapped — an absent label is not
/// performed, so it must not trip the gate. A row var / arrow / other head is not a
/// named effect sort. Carrier-agnostic — reads the head through [`TermView`].
///
/// WI-722: `pub(in crate::kb)` so the load-time macro purity gate (`load.rs`) can test a
/// macro's declared effect labels against `Error`.
pub(in crate::kb) fn effect_label_names_sort(
    kb: &KnowledgeBase,
    label: &Value,
    sort: Symbol,
) -> bool {
    let guarded = guarded_effect_label(kb, label);
    let label = guarded.as_ref().unwrap_or(label);
    match type_head(kb, label) {
        TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => {
            same_sort_canonical(kb, s, sort)
        }
        _ => false,
    }
}

/// WI-20260830-APWM3 — one operation's declared effect row AS THE PER-LABEL GATES MUST
/// READ IT: every projection eliminated against the operation's own parameter types, then
/// every resulting ROW flattened to its member labels.
///
/// A per-label gate over `all_operation_effects` asks a question about LABELS ("is this
/// one `External`?", "is this `Modify`'s target a place?"), and the list it walks holds
/// ELEMENTS. The two coincide only while every element is written as a bare label. They
/// come apart at a projection: `effects {llm.E, Error}` is two elements and, once `llm`'s
/// type is concrete, three labels — and the element carrying the third answers every
/// per-label question with "no". Both steps are needed and neither suffices:
/// ELIMINATION turns `llm.E` into the row `{External}`, FLATTENING turns that row into
/// the label `External`.
///
/// ORDER OF THE OUTPUT IS THE DECLARED ORDER, elements expanded in place. No caller
/// depends on it, but a diagnostic built from this list should read like the row.
///
/// WHAT IT COSTS: a row of bare labels — the overwhelming majority — pays two whole-list
/// scans and allocates nothing. A row carrying a PROJECTION or any row-shaped element
/// pays a `decompose_effect_row` per such element, and "row-shaped" INCLUDES a single
/// `guarded` atom, so the WI-818 partial primitives (`Stream.head`, `Stream.tail`,
/// `List.head`) take the flattening path on every load even though none of them projects
/// anything. That is a handful of operations per KB against a pass that already walks
/// every `OperationInfo` fact, so it is stated rather than optimized — but stated,
/// because an earlier draft of this doc claimed "no allocation" for exactly that
/// population and would have misled the next person sizing this pass (/code-review).
///
/// AN ELIMINATION FAILURE KEEPS THE RAW ELEMENT, deliberately: see
/// [`check_branch_external_exclusion`]'s doc for why this reader does not also own that
/// diagnostic.
///
/// TWO SIBLINGS STILL READ THE RAW ROW: [`check_modify_targets`] and
/// [`check_effect_registration`] ask the same per-label question of the same facts, so a
/// `Modify[T]` or an unregistered kind reached only through a projection is invisible to
/// each. They are left alone because this ticket's change does not worsen them, and
/// because the registration one has a SPEC EXEMPTION to renegotiate first
/// (`docs/kernel-language.md` §5.5 lists "a receiver projection (`s.E`)" among the
/// positions that name no kind). WI-20260831-RSRP5 decides both.
///
/// THE THIRD SIBLING IS FIXED HERE, and the difference is the whole rule for when a
/// deferral is legitimate: [`check_declared_row_contradiction`] was made WRONG by this
/// ticket, not merely left blind by it. Flattening the declared side removed an
/// accidental refusal — `{llm.E, -External}` had been caught downstream as a violated
/// denial, and once the coverage match succeeded nothing caught it at all. A change that
/// breaks a gate owns that gate; it takes [`eliminate_declared_row_projections`], the
/// half of this function it needs. Found by /code-review, measured loading, and
/// `a_denial_is_not_evaded_by_projecting_the_label_it_denies` is the program.
fn declared_row_labels_read_through(
    kb: &mut KnowledgeBase,
    op_sym: Symbol,
    params: &[(Symbol, Value)],
    effects: &[Value],
) -> Vec<Value> {
    let eliminated = eliminate_declared_row_projections(kb, op_sym, params, effects);
    if !eliminated.iter().any(|e| effect_value_is_row_shaped(kb, e)) {
        return eliminated;
    }
    let mut out: Vec<Value> = Vec::new();
    for e in eliminated {
        match explode_declared_effect_row(kb, &e) {
            // The ABSENT half is dropped: a per-label gate asks about labels the row
            // PRESENTS, and `-X` is the row promising X is not performed. Reading it as a
            // present label would make `effects {Branch, -External}` — a row that
            // explicitly forbids the co-occurrence — read as the co-occurrence itself.
            // A gate that must see BOTH halves does its own decomposition off the
            // eliminated elements ([`check_declared_row_contradiction`]).
            Some((admitting, _absent)) => out.extend(admitting),
            None => out.push(e),
        }
    }
    out
}

/// WI-20260830-APWM3 — THE FIRST HALF OF [`declared_row_labels_read_through`], on its own
/// because the two gates that need it need DIFFERENT second halves. Discharge each
/// declared element's receiver projections against the operation's own parameter types,
/// leaving the elements otherwise as declared.
///
/// [`check_branch_external_exclusion`] wants the result FLATTENED TO PRESENT LABELS —
/// its question is "which labels does this row perform". [`check_declared_row_contradiction`]
/// wants the elements themselves, because it decomposes present AND absent across the
/// whole list with its own measured classification, and an absence is half of the
/// question it asks. Sharing only the elimination is what lets each keep its own reading.
///
/// AN ELIMINATION FAILURE KEEPS THE RAW ELEMENT, deliberately — see
/// [`check_branch_external_exclusion`]'s doc for why neither of these readers also owns
/// that diagnostic.
///
/// COST: one [`value_contains_projection`] walk per element, and nothing else, for the
/// overwhelming majority of rows — a projection in an effect row is rare. The walk is
/// what the whole-list pre-check tests, so a row with none allocates nothing.
pub(super) fn eliminate_declared_row_projections(
    kb: &mut KnowledgeBase,
    op_sym: Symbol,
    params: &[(Symbol, Value)],
    effects: &[Value],
) -> Vec<Value> {
    if !effects.iter().any(|e| value_contains_projection(kb, e)) {
        return effects.to_vec();
    }
    let param_map: HashMap<Symbol, Value> = params.iter().cloned().collect();
    let ctx = TypeErrorContext::OperationEffects { op_name: op_sym };
    let span = kb.functor_span(op_sym).map(|s| s.span);
    effects
        .iter()
        .map(|e| {
            if !value_contains_projection(kb, e) {
                return e.clone();
            }
            eliminate_type_projections(kb, e, &param_map, None, &ctx, span)
                .unwrap_or_else(|_| e.clone())
        })
        .collect()
}

/// Is this declared effect element a ROW (rather than one label)? The `&KnowledgeBase`
/// twin of [`effect_value_as_row`]'s classification, for a caller that only needs the
/// question answered — [`declared_row_labels_read_through`]'s fast path, which must not
/// take the `&mut` wrap just to decide it has nothing to do.
pub(super) fn effect_value_is_row_shaped(kb: &KnowledgeBase, effect: &Value) -> bool {
    if matches!(type_dispatch_name_view(kb, effect), Some("effects_rows")) {
        return true;
    }
    effect.head(kb).functor_sym().is_some_and(|sym| {
        matches!(
            kb.qualified_name_of(sym)
                .strip_prefix("anthill.prelude.EffectExpression."),
            Some("merge" | "present" | "guarded" | "absent" | "open" | "empty_row")
        )
    })
}

/// WI-701 / proposal 054 §"`Branch` and `External`": a `Branch` region may not
/// perform `External`, so the typer REJECTS a declared effect row that carries both.
///
/// WHY (054): 027/037/047 §8 give a tracked resource exactly two lawful
/// branch-interaction contracts — ranked ABOVE `Branch` it is snapshotted on entry
/// and rolled back on backtrack (`register_undo`); ranked BELOW it survives across
/// branches — and both rest on one premise: the runtime mediates every change to the
/// resource. `External` names precisely the state for which that premise fails IN
/// PRINCIPLE — there is no `register_undo` for the world (above `Branch` is
/// impossible: a branch that `fail()`s after `create_issue` cannot un-mint the id),
/// and a solver multi-shot-resumes the continuation once per solution (below `Branch`
/// is unsound: an `External` call reached after a `reflect` runs once per branch) — so
/// NEITHER contract is available and the hazard is permanent.
///
/// This is the BLUNT co-occurrence reject the ticket scopes: any operation whose
/// declared effect row PRESENTS both labels is rejected at load. It is sound to add
/// now and purely additive — the `Branch`/suspend-resume runtime is still a
/// placeholder, so no runnable code declares both today (the gate forbids nothing we
/// can currently run). It is deliberately NOT compositional: WI-329's row-discharge
/// typing (047 §9 step 5) is what later makes it exact — a solver's reify discharges
/// `Branch` from the row, so `External` becomes legal again at precisely the point
/// where the search has committed to its solutions (the sound sandwich: read the
/// world before the search, search over tracked state only, write after the commit).
///
/// Walks every `OperationInfo` fact (via [`all_operation_params_and_effects`], NOT the
/// first-fact-only cache) so a spec AND its impl are each checked; a diagnostic is
/// emitted once per offending op symbol. Inert on a KB without the `External` prelude
/// (WI-699) — nothing can carry the label, so there is nothing to exclude.
///
/// READS EACH ROW THROUGH ITS PROJECTIONS (WI-20260830-APWM3), which is what makes the
/// gate hold at a concrete carrier rather than only on a literal row. `effects {Branch,
/// llm.E, Error}` with `llm: LiveLlm` and `LiveLlm provides Llm[E = {External}]` PRESENTS
/// both labels, and the un-eliminated `llm.E` names neither — so this gate saw only
/// `Branch` and admitted it. It did not matter while the sibling coverage check refused
/// that row for its own (wrong) reason; closing that gap is precisely what turned this
/// blindness into a live evasion, which is why the two moved in one commit. The evasion
/// is not theoretical: it is a `Branch` region performing `External`, the one thing 054
/// says can never be made sound.
///
/// THE ELIMINATION IS A READ, NOT A VERDICT. An un-dischargeable projection (`effects
/// s.Nonexistent`) keeps its raw atom here and is judged as one — this gate does not
/// report it. The well-formedness verdict for a broken signature projection belongs to
/// the body pass (`effect_proj_failed`), and raising it a second time here would make one
/// defect print two errors. What that leaves open is a BODY-LESS operation whose effect
/// projection names nothing: no pass eliminates its row, so no pass refuses it. That gap
/// predates this ticket and is untouched by it.
fn check_branch_external_exclusion(kb: &mut KnowledgeBase) -> Vec<TypeError> {
    let mut errors: Vec<TypeError> = Vec::new();
    let (Some(branch_sym), Some(external_sym)) = (
        kb.try_resolve_symbol("anthill.prelude.Branch"),
        kb.try_resolve_symbol("anthill.prelude.External"),
    ) else {
        return errors;
    };
    let mut reported: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    for (op_sym, params, effects) in crate::kb::op_info::all_operation_params_and_effects(kb) {
        let effects = declared_row_labels_read_through(kb, op_sym, &params, &effects);
        let has_branch = effects
            .iter()
            .any(|e| effect_label_names_sort(kb, e, branch_sym));
        let has_external = effects
            .iter()
            .any(|e| effect_label_names_sort(kb, e, external_sym));
        if has_branch && has_external && reported.insert(op_sym) {
            let span = kb.functor_span(op_sym).map(|s| s.span);
            errors.push(TypeError::Other {
                site: TypeError::here(),
                span,
                context: TypeErrorContext::OperationEffects { op_name: op_sym },
                expected: format!(
                    "operation `{}` to declare at most one of `Branch` / `External`",
                    kb.qualified_name_of(op_sym),
                ),
                actual: "effect row carries BOTH `Branch` and `External` — a Branch region \
                     may not perform External: External state has no register_undo (above \
                     Branch is impossible) and is re-run once per solution (below Branch is \
                     unsound). Proposal 054 §\"Branch and External\"."
                    .to_string(),
            });
        }
    }
    errors
}

/// WI-702: collect every `Term::Fn` functor reachable in the hash-consed head
/// term `id` — the operation symbols an equational `@[simp]`/`@[unfold]` head
/// (`eq(lhs, rhs)`) mentions, so the formation gate can test each for an effect
/// row. Iterative to survive a deep head.
fn collect_op_functors_in_term(kb: &KnowledgeBase, id: TermId, out: &mut Vec<Symbol>) {
    let mut stack = vec![id];
    while let Some(t) = stack.pop() {
        match kb.get_term(t) {
            Term::Fn {
                functor,
                pos_args,
                named_args,
            } => {
                out.push(*functor);
                for a in pos_args.iter() {
                    stack.push(*a);
                }
                for (_, a) in named_args.iter() {
                    stack.push(*a);
                }
            }
            // WI-20260902-CZJ2N — A NULLARY CALL IS STORED BARE, so `rule tau() <=> 7
            // @[simp]` has a `Term::Ref` LHS and the `Fn`-only walk never pushed `tau`.
            // That SILENTLY DROPS WI-702's soundness refusal: a `@[simp]`/`@[unfold]`
            // rule naming an EFFECTFUL nullary operation loaded clean, and the firing
            // sites are effect-blind by design, so the effectful call was free to be
            // duplicated, reordered or dropped at rewrite time. Reaches a nested call
            // too (`g(tau())`), not only the head.
            Term::Ref(s) | Term::Ident(s) => out.push(*s),
            _ => {}
        }
    }
}

/// WI-702: carrier-agnostic head-functor collection — a hash-consed `Value::Term`
/// head walks as a term; an occurrence `Value::Node` head reuses the shared
/// call-functor walk [`crate::kb::op_requirements::walk_calls_node`] (`Apply` /
/// `ApplyWithin`), so this gate and the requirement scanner can't drift.
fn collect_op_functors_in_value(kb: &KnowledgeBase, v: &Value, out: &mut Vec<Symbol>) {
    match v {
        Value::Term { id, .. } => collect_op_functors_in_term(kb, *id, out),
        Value::Node(occ) => {
            crate::kb::op_requirements::walk_calls_node(occ, &mut |sym, _| out.push(sym))
        }
        _ => {}
    }
}

/// WI-702 / proposal 054 §"Consumers that must decline it — loudly": the FORMATION
/// HOLE. A `@[simp]`/`@[unfold]`-tagged equation is a DIRECTIONAL rewrite the resolver
/// (`fire_simp_equation`) and typer (`fire_simp`) fire LHS→RHS, so firing DUPLICATES,
/// REORDERS, or DROPS the matched redex. That is sound today only because effectful
/// ops never *become* simp equations — the defining-equation family declines them
/// (`body_specialize::defining_equations`, WI-702 part 1). The one hole left is a
/// USER-WRITTEN `@[simp]`/`@[unfold]` rule whose sides mention an EFFECTFUL operation:
/// rewriting its call is unsound for the same reason equations of it are refused (an
/// `External` `create_issue` rewritten twice mints two issues; a `Modify`/`Error` op
/// is not equational either — the FUNCTION-HOOD predicate, matching the part-1 gate).
/// The firing sites stay effect-blind; this LOAD-TIME gate rejects the rule instead.
///
/// Keyed on the effect ROW only, NOT `requires`: `Set`/`Map` carry a sort-level
/// `requires Eq[T]` that rides into their ops (`member`/`insert`/`get`), and the
/// stdlib's own `member(?x, insert(?s, ?x)) <=> true @[simp]` laws mention them — a
/// requires-inclusive gate would reject the standard library. A `requires`-only op is
/// still a pure function once its dictionary is supplied, so rewriting it is sound;
/// only a non-empty EFFECT row is the hazard. (Shares the effect predicate with the
/// part-1 request-site gate — [`KnowledgeBase::effect_row_blocking_equations`].)
///
/// Runs in [`type_check_sorts_typed`] after every `OperationInfo` fact is loaded,
/// like the WI-701 sibling, so a mentioned op's effect row is visible regardless of
/// whether the rule or the op it names loaded first.
fn check_simp_effectful_ops(kb: &mut KnowledgeBase) -> Vec<TypeError> {
    let mut errors: Vec<TypeError> = Vec::new();
    // Candidate directional rewrites live under the `eq`/`unify` functors — an
    // equational head keeps its functor index only when `@[simp]`/`@[unfold]`-tagged
    // (an untagged law is `unindex_functor`'d at load, WI-139). Filter to the
    // tagged ones; their own `is_fact` status is irrelevant (a `lhs <=> rhs` law is
    // stored as an empty-body rule, i.e. a fact — so DO NOT skip facts here).
    for rid in kb.simp_equation_rids() {
        let meta = kb.rule_meta(rid);
        if !(crate::kb::load::meta_has_flag(kb, meta, "simp")
            || crate::kb::load::meta_has_flag(kb, meta, "unfold"))
        {
            continue;
        }
        // Every operation symbol the rule's sides mention: the head equation term
        // (`eq(lhs, rhs)`) plus any body goals/guards (a guarded `@[simp]` rule fires
        // with its guard). The body is already dot-dispatched (this pass runs after
        // `type_rule_bodies`), so a `?x.effectful_op()` guard is an `Apply` here. A
        // head written in method syntax stays a `dot_apply` TERM — but a `DotApply`
        // redex never fires under simp (WI-279 `try_fire` returns None), so leaving
        // its method functor uncollected declines nothing that could rewrite.
        let mut functors: Vec<Symbol> = Vec::new();
        collect_op_functors_in_value(kb, kb.rule_head_value(rid), &mut functors);
        for node in kb.rule_body_nodes(rid) {
            crate::kb::op_requirements::walk_calls_node(node, &mut |sym, _| functors.push(sym));
        }
        // WI-757 — the ONE exemption: a MACRO whose call the expander EVALUATES AWAY.
        // The gate above is about the call this rewrite EMITS; that macro is the
        // REWRITER — `try_expand_macro` runs it at compile time and splices its
        // RESULT, so the call never reaches runtime and cannot be duplicated,
        // reordered, or dropped there. Its `Error` is a COMPILE-TIME diagnostic
        // (proposal 043.1 §3.6: a macro rejects by raising), not a runtime effect, and
        // without this exemption `check_macro_purity`'s "at most `Error`" allowance
        // would be dead — every macro declaring it refused at the rule that names it.
        //
        // `macro_expanded_rhs_head` — NOT a local `is_macro` test — is what keeps the
        // exemption tied to the expansion that justifies it: it re-applies `try_fire`'s
        // own conditions (@[simp] only, no typed bounds, positional RHS), so a rule the
        // typer does NOT expand keeps the gate. MEASURED: keyed on `is_macro` alone,
        // an effectful macro under `@[unfold]` — fired by the RESOLVER, which never
        // macro-expands — loaded clean and rewrote the effectful call into the program.
        //
        // Skipping by SYMBOL also exempts that macro elsewhere in the same rule. Every
        // such spelling is refused AHEAD of here, measured: as a body goal by WI-583
        // ("no relational reading" — an occurrence-returning op is not a predicate),
        // and in any value position by the occurrence-vs-value parameter mismatch.
        // `wi757_macro_diagnostic_test` pins both, so this stays a checked claim.
        let rhs_macro = crate::kb::simp_rewrite::macro_expanded_rhs_head(kb, rid);
        let mut reported: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
        for f in functors {
            if Some(f) == rhs_macro {
                continue;
            }
            if !reported.insert(f) {
                continue;
            }
            let Some(block) = kb.effect_row_blocking_equations(f) else {
                continue;
            };
            // Name the rule (label if any) — built here, only on an actual violation.
            let label = kb
                .rule_label(rid)
                .map(|l| format!("`{}`", kb.qualified_name_of(l)))
                .unwrap_or_else(|| "an unlabeled".to_string());
            errors.push(TypeError::Other {
                site: TypeError::here(),
                span: kb.functor_span(f).map(|s| s.span),
                context: TypeErrorContext::OperationEffects { op_name: f },
                // ONE predicate, named once: POTENTIALLY EFFECTFUL. The two arms
                // are the reason, not two verdicts — a row that is already an
                // effect and a row that may become one are refused alike, because
                // nothing here can tell which instantiation will be written
                // (WI-1049 decision). The `actual` clause below says which, since
                // that is what tells the author what to do.
                expected: format!(
                    "{label} `@[simp]`/`@[unfold]` rewrite not to mention potentially \
                     effectful operation `{}`",
                    kb.qualified_name_of(f),
                ),
                // WI-1049 — one arm per case, NOT a shared prefix plus a suffix.
                // Composing them doubled the claim ("… is not a function — … an
                // effectful operation is not equational") and moved the sentence
                // boundary, which broke `wi757`'s `EFFECTFUL_REWRITE_MARKER` on
                // capitalization alone. The Effectful text is therefore byte-identical
                // to the pre-WI-1049 wording: that arm was never the defect.
                //
                // The polymorphic repair is measured, not guessed: a law over a
                // carrier's OWN pure `insert`/`isEmpty` loads clean under `@[simp]`,
                // while the same law on the effect-polymorphic spec is refused.
                actual: match block {
                    crate::kb::body_specialize::EquationBlock::Effectful(ref row) => format!(
                        "operation `{}` carries effect row {row} — a directional rewrite \
                         DUPLICATES, REORDERS, or DROPS the matched call, which no effect \
                         tolerates (an External call rewritten twice runs twice); an \
                         effectful operation is not equational. Proposal 054 §\"Consumers \
                         that must decline it\".",
                        kb.qualified_name_of(f),
                    ),
                    crate::kb::body_specialize::EquationBlock::Polymorphic(ref row) => format!(
                        "operation `{}` is effect-POLYMORPHIC — its row {row} is a row \
                         VARIABLE, so the operation is pure at a pure carrier and effectful \
                         at an effectful one, and a declaration here binds EVERY carrier. It \
                         is therefore POTENTIALLY EFFECTFUL and refused alike: a directional \
                         rewrite DUPLICATES, REORDERS, or DROPS the matched call, which no \
                         effect tolerates. Declare the equation where the row is already \
                         concrete (on a carrier whose own operations are pure) rather than on \
                         the sort that leaves `{}` open. Proposal 054 §\"Consumers that must \
                         decline it\".",
                        kb.qualified_name_of(f),
                        row.trim_matches(['{', '}']),
                    ),
                },
            });
        }
    }
    errors
}

/// Extract constructor and operation symbol lists from a SortInfo fact.
///
/// WI-237: matched by qualified-name identity (`same_symbol` then; `canonical_sort_sym`
/// since WI-672) like the other five local_name_of audit sites. The bundle's `sort Main` short
/// name no longer collides with `anthill.cli.Main` here, so the typer
/// actually checks the anthill-todo bundle's cmd_X bodies. The chain of
/// follow-up issues this exposed is fixed under WI-237: types_compatible
/// name-binding normalization, pattern type-arg propagation (now
/// ctor-aware via `entity_field_types`, not SortAlias short-name lookup),
/// anthill-stl spec-fact embedding, bundle effect declarations, and
/// `op_has_runnable_body` guarding WI-218 from rewriting spec ops to
/// body-less impl symbols. Diagnostic: `wi237_diag_test.rs`.
pub(super) fn find_sort_info(
    kb: &KnowledgeBase,
    sort_functor: Symbol,
) -> Option<(Vec<Symbol>, Vec<Symbol>)> {
    // WI-671/WI-672 — the SortInfo canonical-sort bucket (or a live scan pre-index).
    // Called once PER SORT in `type_check_sorts_typed`, so the index turns an O(sorts²)
    // scan into O(sorts). The re-filter below compares by `canonical_sort_sym` (WI-672,
    // was `same_symbol`) — no last-segment matching, so a top-level `sort Ring` no longer
    // reads `anthill.prelude.algebra.Ring`'s constructors/operations.
    for rid in sort_info_rids_by_sort(kb, sort_functor) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(head) = kb.fact_head_term(rid) else {
            continue;
        };
        let named_args = match kb.get_term(head) {
            Term::Fn { named_args, .. } => named_args,
            _ => continue,
        };

        let name_tid = match named_args
            .iter()
            .find(|(s, _)| kb.local_name_of(*s) == "name")
            .map(|(_, v)| *v)
        {
            Some(t) => t,
            None => continue,
        };
        let name_sym = match kb.get_term(name_tid) {
            Term::Fn { functor, .. } => *functor,
            Term::Ref(s) => *s,
            _ => continue,
        };
        if !same_sort_canonical(kb, name_sym, sort_functor) {
            continue;
        }

        let ctors = named_args
            .iter()
            .find(|(s, _)| kb.local_name_of(*s) == "constructors")
            .map(|(_, v)| extract_sym_list(kb, *v))
            .unwrap_or_default();

        let ops = named_args
            .iter()
            .find(|(s, _)| kb.local_name_of(*s) == "operations")
            .map(|(_, v)| extract_sym_list(kb, *v))
            .unwrap_or_default();

        return Some((ctors, ops));
    }
    None
}

/// Extract a list of Symbols from a cons-list of Ref terms.
fn extract_sym_list(kb: &KnowledgeBase, list_tid: TermId) -> Vec<Symbol> {
    list_to_vec(kb, list_tid)
        .iter()
        .filter_map(|tid| match kb.get_term(*tid) {
            Term::Ref(s) => Some(*s),
            Term::Fn { functor, .. } => Some(*functor),
            _ => None,
        })
        .collect()
}

/// Check a value against a declared type. Returns Some(TypeError) on mismatch.
///
/// Takes `&mut KnowledgeBase` because the parameterized-spec path runs
/// the canonical instance resolver (WI-274), which allocates
/// substituted subgoal terms during conditional resolution.
fn check_value_against_type(
    kb: &mut KnowledgeBase,
    value: TermId,
    declared_type: &Value,
    entity_sym: Symbol,
    field_sym: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    // WI-946: a field declared `anthill.reflect.Term` holds a QUOTED term, and
    // reflection (value → Term) is TOTAL — every value has a Term representation —
    // so ANY value conforms. Shares the one owner of that rule
    // ([`is_reflect_term_type`], whose doc carries the why, including why `Term` is
    // NOT thereby a top type) rather than restating it. Stated here because until
    // WI-946 it was never REACHED: the membership check below was skipped for the
    // free-standing carriers reflect fields actually hold (`entity Holder(pat:
    // Term)` + `fact Holder(pat: Thing(id: "z"))`, WI-716), so the accident stood
    // in for the rule. A sort-NESTED carrier in the same field was refused, which
    // is the §6.3 disagreement in reverse.
    if is_reflect_term_type(kb, declared_type) {
        return None;
    }
    // WI-361: dispatch on the canonical form tag so a term-backed `Ref(S)` /
    // `Fn{S,named}` routes to the same arms as the deep `sort_ref` / `parameterized`.
    // WI-342: the declared type is carrier-agnostic — read it through [`TermView`]
    // (a `Value::Node` denoted-bearing field type is handled, not re-grounded).
    let type_functor = type_dispatch_name_view(kb, declared_type);

    match type_functor {
        Some("sort_ref") => {
            let declared_sym = extract_sort_ref_sym(kb, declared_type)?;
            check_value_against_sort_ref(
                kb,
                value,
                declared_sym,
                declared_type,
                entity_sym,
                field_sym,
                span,
            )
        }
        Some("parameterized") => {
            check_value_against_parameterized(kb, value, declared_type, entity_sym, field_sym, span)
        }
        _ => None, // type_var, arrow, named_tuple, nothing — skip for now
    }
}

/// Check value against a simple sort_ref type.
fn check_value_against_sort_ref(
    kb: &KnowledgeBase,
    value: TermId,
    declared_sym: Symbol,
    declared_type: &Value,
    entity_sym: Symbol,
    field_sym: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    let is_prim = |sym: Symbol, expected: &str| -> bool {
        let name = kb.local_name_of(sym);
        name == expected || name == &format!("anthill.prelude.{}", expected)
    };

    match kb.get_term(value) {
        Term::Const(lit) => {
            let ok = match lit {
                Literal::String(_) => is_prim(declared_sym, "String"),
                Literal::Int(_) => is_prim(declared_sym, "Int64"),
                Literal::Float(_) => is_prim(declared_sym, "Float"),
                Literal::Bool(_) => is_prim(declared_sym, "Bool"),
                _ => true,
            };
            let actual = match lit {
                Literal::String(_) => "String",
                Literal::Int(_) => "Int64",
                Literal::Float(_) => "Float",
                Literal::Bool(_) => "Bool",
                _ => "?",
            };
            // WI-036: a primitive value also satisfies a spec-sort field when
            // its primitive sort provides the spec (e.g. `5` for a field typed
            // `Eq`, since `Int provides Eq`).
            if ok || lit_sort_provides(kb, actual, declared_sym) {
                None
            } else {
                Some(TypeError::Other {
                    site: TypeError::here(),
                    span,
                    context: TypeErrorContext::EntityField {
                        entity: entity_sym,
                        field: field_sym,
                    },
                    expected: type_display_name_value(kb, declared_type),
                    actual: actual.to_string(),
                })
            }
        }
        // WI-946: the value's sort is the TOTAL belongs-to (`sort_of_constructor`).
        // The strict view answered `None` for an eponymous / free-standing carrier,
        // and `check_value_sort_membership`'s `parent?` turned that into a SILENT
        // ACCEPT: `fact Holder(c: Vec3(x: 1.0))` on a field declared `Colour` loaded
        // clean, while the same fact with a sort-NESTED carrier was refused.
        Term::Fn {
            functor: val_functor,
            ..
        } => check_value_sort_membership(
            kb,
            kb.sort_of_constructor(*val_functor),
            declared_sym,
            declared_type,
            entity_sym,
            field_sym,
            span,
        ),
        Term::Ref(val_sym) if kb.is_constructor_symbol(*val_sym) => check_value_sort_membership(
            kb,
            kb.sort_of_constructor(*val_sym),
            declared_sym,
            declared_type,
            entity_sym,
            field_sym,
            span,
        ),
        _ => None,
    }
}

/// True if the primitive sort of a literal (`"Int64"`, `"String"`, …) provides
/// the spec sort `declared_sym` (WI-036 — a primitive value in a spec field).
fn lit_sort_provides(kb: &KnowledgeBase, prim: &str, declared_sym: Symbol) -> bool {
    kb.try_resolve_symbol(&format!("anthill.prelude.{prim}"))
        .is_some_and(|prim_sym| sort_provides(kb, prim_sym, declared_sym))
}

/// Shared check for a constructor value against a declared sort: accept direct
/// membership (the value's parent sort is the declared sort) or, per WI-036,
/// when the parent sort provides the declared spec sort.
fn check_value_sort_membership(
    kb: &KnowledgeBase,
    parent: Option<Symbol>,
    declared_sym: Symbol,
    declared_type: &Value,
    entity_sym: Symbol,
    field_sym: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    let parent = parent?;
    if constructor_matches_declared(kb, parent, declared_sym) {
        return None;
    }
    if sort_provides(kb, parent, declared_sym) {
        return None;
    }
    Some(TypeError::Other {
        site: TypeError::here(),
        span,
        context: TypeErrorContext::EntityField {
            entity: entity_sym,
            field: field_sym,
        },
        expected: type_display_name_value(kb, declared_type),
        actual: kb.local_name_of(parent).to_string(),
    })
}

/// Check value against a parameterized type like List[T=Int].
///
/// Takes `&mut KnowledgeBase` for the binding-precise spec check
/// (WI-274) — see [`spec_resolves_at_bindings`].
fn check_value_against_parameterized(
    kb: &mut KnowledgeBase,
    value: TermId,
    declared_type: &Value,
    entity_sym: Symbol,
    field_sym: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    // WI-361: read base + bindings form-agnostically — deep
    // `parameterized(base: sort_ref(S), bindings)` or term-backed `Fn{S, named}`.
    // WI-342: carrier-agnostic over [`TermView`] (the declared type is a `Value`).
    let TypeExtractor::Parameterized {
        base: base_sym,
        bindings,
    } = extract_type(kb, declared_type)
    else {
        return None;
    };

    // Get the value's constructor symbol
    let val_functor = match kb.get_term(value) {
        Term::Fn { functor, .. } => *functor,
        Term::Ref(s) if kb.is_constructor_symbol(*s) => *s,
        _ => return None,
    };

    // Check entity belongs to base sort. WI-036: when the base is a spec
    // sort (e.g. `Comparable[T = Int]`), a value whose own sort provides that
    // spec is accepted — and since its constructor is not a base constructor,
    // the per-field substitution walk below is skipped.
    //
    // WI-274: precise about the *bindings*. Rather than the base-only
    // `sort_provides` (does the value's sort provide the spec at all),
    // run the canonical instance resolver at the declared bindings —
    // the same resolver operation-requires uses. This rejects a
    // binding mismatch (`Comparable[T = Gadget]` holding a Widget,
    // where Widget provides Comparable only at `T = Widget`) and
    // checks conditional providers at the actual element type (List
    // provides Eq requires elementEq: `Eq[T = List[Int]]` resolves,
    // `Eq[T = List[NonEq]]` does not). The base-only `sort_provides`
    // is kept for the binding-free case, where it is already precise.
    //
    // WI-946: the TOTAL belongs-to. Under the strict view an eponymous /
    // free-standing carrier answered `None`, skipping this whole check and
    // falling straight through to the per-field walk below — so `fact Holder(l:
    // Vec3(x: 1.0))` on a field declared `List[T = Int64]` loaded clean while the
    // sort-NESTED carrier was refused.
    if let Some(parent) = kb.sort_of_constructor(val_functor) {
        if !constructor_matches_declared(kb, parent, base_sym) {
            let goal_bindings = declared_type_goal_bindings(kb, &bindings);
            let accepted = if goal_bindings.is_empty() {
                sort_provides(kb, parent, base_sym)
            } else {
                spec_resolves_at_bindings(kb, base_sym, goal_bindings)
            };
            if accepted {
                return None;
            }
            return Some(TypeError::Other {
                site: TypeError::here(),
                span,
                context: TypeErrorContext::EntityField {
                    entity: entity_sym,
                    field: field_sym,
                },
                expected: type_display_name_value(kb, declared_type),
                actual: kb.local_name_of(parent).to_string(),
            });
        }
    }

    // Build substitution from type bindings (T → Int). Look up each
    // param's `Var` scoped to `base_sym` — the SortAlias index has
    // multiple entries for short names like "T" (List, Option, Stream,
    // …), and an unscoped short-name lookup may return the wrong sort's
    // `Var`, leaving `walk_type` on the entity's field types
    // unsubstituted. WI-361: bindings come carrier-agnostic from `extract_type`.
    let mut subst = Substitution::new();
    for (psym, value_type) in &bindings {
        if let Some(vid) = type_param_vid_in_sort(kb, base_sym, *psym) {
            // WI-342: bind carrier-agnostically (`bind_value`) so a `Value::Node`
            // binding is carried; `walk_type_value` resolves a field type through it.
            subst.bind_value(kb, vid, value_type.clone());
        }
    }

    // Check each field of the value entity against the instantiated field type
    let val_named_args = match kb.get_term(value) {
        Term::Fn { named_args, .. } => named_args.clone(),
        _ => return None,
    };

    let ctor_field_types = match kb.entity_field_types(val_functor) {
        Some(ft) => ft.to_vec(),
        None => return None,
    };

    for (fsym, declared_field_type) in &ctor_field_types {
        let fval = match val_named_args.iter().find(|(s, _)| s == fsym) {
            Some((_, v)) => *v,
            None => continue,
        };
        if matches!(kb.get_term(fval), Term::Var(_)) {
            continue;
        }

        // Walk the field type through the substitution to resolve type params,
        // carrier-agnostically (WI-342) — a `Value::Node` field type is carried.
        let instantiated_type = walk_type_value(kb, &subst, declared_field_type);

        if let Some(err) =
            check_value_against_type(kb, fval, &instantiated_type, entity_sym, *fsym, span)
        {
            return Some(err);
        }
    }

    None
}

/// WI-274: collect a parameterized type's bindings as `SortGoal`
/// bindings — `(spec short-param symbol, value type term)` pairs. The
/// value terms are [canonicalized](canonicalize_goal_value) into the
/// bare-sort-ref shape the instance resolver matches against.
fn declared_type_goal_bindings(
    kb: &mut KnowledgeBase,
    bindings: &[(Symbol, Value)],
) -> SmallVec<[(Symbol, TermId); 2]> {
    // WI-361: `bindings` are the carrier-agnostic `(param, value-type)` pairs from
    // [`extract_type`]; a `Value::Term` value canonicalizes into the bare-sort-ref
    // shape the instance resolver matches against.
    bindings
        .iter()
        .filter_map(|(p, v)| match v {
            Value::Term { id: t, .. } => Some((*p, canonicalize_goal_value(kb, *t))),
            _ => None,
        })
        .collect()
}

/// WI-274: rewrite a field-type type term into the canonical shape the
/// instance resolver matches against: every BARE sort to `Ref(S)` — the nullary `Fn{S}`
/// spelling included, which [`extract_sort_ref_sym`] reads too — recursing through
/// parameterized types so nested element types (`List[T = Int]`) expose their real base
/// and value sorts to `parametric_value_parts`. (Written when field types still carried
/// the deep `sort_ref(name: Ref(S))` wrapper; since WI-361 nothing mints that.)
fn canonicalize_goal_value(kb: &mut KnowledgeBase, value: TermId) -> TermId {
    if let Some(s) = extract_sort_ref_sym(kb, &TermIdView(value)) {
        return kb.alloc(Term::Ref(s));
    }
    kb.map_fn_children(value, |kb, child| canonicalize_goal_value(kb, child))
}

/// WI-274: binding-precise spec satisfaction. A field declared with a
/// parameterized spec is accepted iff the spec resolves at the
/// *declared bindings* through the canonical instance resolver
/// ([`resolve`], `typing/synth.rs`) — the same resolver operation-requires
/// uses, accepting iff `Resolved`. Empty scope: field validation has
/// no enclosing `requires` to draw on. Conditional providers descend
/// recursively (List provides Eq requires elementEq), so the goal
/// resolves only when the element type also provides the spec.
pub(super) fn spec_resolves_at_bindings(
    kb: &mut KnowledgeBase,
    spec_sort: Symbol,
    bindings: SmallVec<[(Symbol, TermId); 2]>,
) -> bool {
    // Field validation resolves a spec at declared bindings — no call-site
    // receiver, so no carrier discrimination (WI-350).
    let goal = SortGoal {
        spec_sort,
        bindings,
        carrier: None,
    };
    // WI-841: no call site, hence no selection — a DECLARATION is being validated.
    let scope = ResolutionScope {
        available_requires: &[],
        sigma: None,
        selected: &[],
        sub_goal_requires: &[],
    };
    matches!(resolve(kb, &goal, &scope), ResolutionResult::Resolved(_))
}

/// Check all facts for the given entity constructors against their declared field types.
fn check_entity_facts(
    kb: &mut KnowledgeBase,
    ctor_syms: &[Symbol],
    errors: &mut Vec<TypeError>,
    // WI-745: parallel to `errors`; each error is tagged with the `source_id` of
    // the fact it came from. On entry `sources` is parallel to `errors`; restored
    // on exit. See `check_operation_bodies` for the lazy-tag rationale.
    sources: &mut Vec<Option<crate::span::SourceId>>,
) {
    // The file whose fact the current errors come from (lazily flushed).
    let mut cur_src: Option<crate::span::SourceId> = None;
    for &ctor_sym in ctor_syms {
        // WI-928 — DECLARATION RECORDS are out of this check's domain, and the
        // reason is what the check IS: `check_value_against_type` asks a SUBTYPE
        // question, and a reflect record's slots do not hold values of their
        // declared sorts — they hold reflect HANDLES. `EntityInfo.name: Symbol`
        // holds the loader's name term for the entity, `ProofRecord.witness: Term`
        // an axiom record, `OperationInfo.params: List[FieldInfo]` lowered field
        // types. Reaching a handle from a value is a CONVERSION (`as_term` /
        // `term_as_entity`, WI-406), deliberately NOT subsumption — `Term` is not a
        // top type — so a subtype check over these slots reports a mismatch for
        // every well-formed record the loader writes. MEASURED on stdlib + the Rust
        // host bindings: 685 such reports, in 7 classes, ALL of them loader-emitted
        // records and NONE a user fact.
        //
        // This is not a new exemption — it is the status quo, stated. These
        // functors are declared as free-standing entities in reflect.anthill /
        // realization.anthill, and until this ticket a free-standing entity emitted
        // no `SortInfo`, so no constructor list ever named one and their facts were
        // never reached here. What changed is that they are now reachable, so the
        // boundary has to be written down instead of falling out of an omission.
        // Whether the reflect schema and the loader's writes can be brought into
        // agreement — declaring what these slots actually hold, or converting at the
        // write — is WI-930, filed with this measurement.
        //
        // Keyed by [`KnowledgeBase::is_metadata_functor`], the same predicate the
        // WI-630 write-side tripwire uses, so the set the loader may WRITE and the
        // set this check SKIPS cannot drift apart. A user-written `fact
        // Implementation(…)` (examples/webots-modelling) is skipped by the same
        // rule and for the same reason: its slots hold the same handles.
        if kb.is_metadata_functor(ctor_sym) {
            continue;
        }
        let field_types = match kb.entity_field_types(ctor_sym) {
            Some(ft) => ft.to_vec(),
            None => continue,
        };
        if field_types.is_empty() {
            continue;
        }

        for rid in kb.rules_by_functor(ctor_sym) {
            if !kb.is_fact(rid) {
                continue;
            }

            // WI-515: no skip-list needed. It existed to exempt the loader's
            // same-functor `Entity` schema fact (field TYPES in the data
            // slots), which is no longer asserted; the other names it listed
            // (EntityInfo/SortInfo/…) never appear as fact SORTS — loader
            // metadata facts are asserted under "Sort"/"Operation" with their
            // own reflect functors, so they never reach a user constructor's
            // rules_by_functor bucket anyway.

            let Some(head) = kb.fact_head_term(rid) else {
                continue;
            };
            let named_args = match kb.get_term(head) {
                Term::Fn { named_args, .. } => named_args.clone(),
                _ => continue,
            };

            // WI-458: this fact's OWN head span, keyed by RuleId. The dropped
            // `term_span(head)` step keyed on the hash-consed head TermId, which
            // a same-head/different-domain fact in ANOTHER file shares (they are
            // distinct rules — `assert_fact` dedups only when term+sort+domain all
            // match — but alias onto one first-write-wins span). That aliasing hit
            // WI-745's `cur_src` too: the file an error is ATTRIBUTED to came from
            // the same lookup, so a cross-file alias mislabelled the file, not just
            // the offsets. Every source-written fact records a head span here, so
            // the dropped step only ever fired for a synthesized head, where it
            // could only alias. The `functor_span` fallback stays: it is the
            // constructor's own declaration site, a documented representative
            // span, not an alias.
            let head_ss = kb.rule_head_span(rid).or_else(|| kb.functor_span(ctor_sym));
            let span: Option<Span> = head_ss.map(|s| s.span);
            // WI-745: flush the previous fact's errors, then adopt this fact's
            // file for the errors its field checks below push.
            while sources.len() < errors.len() {
                sources.push(cur_src);
            }
            cur_src = head_ss.map(|s| s.source);

            for (field_sym, declared_type) in &field_types {
                let field_sym = *field_sym;
                let field_value = match named_args.iter().find(|(s, _)| *s == field_sym) {
                    Some((_, v)) => *v,
                    None => continue,
                };

                if matches!(
                    kb.get_term(field_value),
                    Term::Var(Var::Global(_) | Var::DeBruijn(_))
                ) {
                    continue;
                }

                // WI-342: the field type is a carrier-agnostic `Value` — checked in
                // place, no re-ground.
                if let Some(err) = check_value_against_type(
                    kb,
                    field_value,
                    declared_type,
                    ctor_sym,
                    field_sym,
                    span,
                ) {
                    errors.push(err);
                }
            }
        }
    }
    // WI-745: flush the last fact's errors and restore the parallel invariant.
    while sources.len() < errors.len() {
        sources.push(cur_src);
    }
}

/// True if sort `carrier` provides spec `spec` — directly OR transitively.
///
/// A `SortProvidesInfo` fact records `carrier` as its `sort_ref` and a spec as
/// its base; `maybe_emit_fact_provides_info` normalizes both explicit `provides`
/// clauses and bare `fact Spec[T=X]` facts into `SortProvidesInfo`, so this one
/// query covers both. Used so a fact field declared with a spec sort accepts a
/// value whose own sort satisfies that spec (WI-036).
///
/// WI-385 (user decision "transitive everywhere") + WI-407: the `provides` /
/// `is-a` relation is TRANSITIVE over the `SortProvidesInfo` edge set. If `A`
/// provides `M` and `M` provides `spec`, then `A` provides `spec` —
/// `IndexedFileStore → QueryableStore → Store`. Every `sort_provides` caller —
/// subtype admissibility (`types_compatible`), requires-coverage, the
/// receiver-sort checks, and the loader skip — sees the full chain rather than
/// just the first hop. WI-407 made the loader emit edges for non-parametric
/// `fact <Spec>` declarations so this closure has something to chase.
pub(crate) fn sort_provides(kb: &KnowledgeBase, carrier: Symbol, spec: Symbol) -> bool {
    let mut visited: SmallVec<[Symbol; 8]> = SmallVec::new();
    // WI-864 — CANONICALIZE ONCE PER WALK, not once per comparison. `same_sort_canonical`
    // is `a == b || canonical(a) == canonical(b)`, and `a == b` implies the canonical
    // equality, so the predicate IS `canonical(a) == canonical(b)` — which means the walk
    // can carry canonical symbols and compare them RAW. Identical verdicts, and the
    // `canonical_sym` call (a `qualified_name_of` plus a `HashMap<String, _>` probe, i.e.
    // a string hash) drops from O(visited) per node to O(1) per walk.
    sort_provides_reach(
        kb,
        kb.canonical_sort_sym(carrier),
        kb.canonical_sort_sym(spec),
        &mut visited,
    )
}

/// WI-660/WI-672 — the spec-base targets of the `SortProvidesInfo` edges OUT of `node` (the
/// specs `node` directly provides). Uses the provider index's carrier direction (canonical
/// bucket + canonical exactness), so the transitive walk queries only the out-edges per hop
/// instead of re-extracting the whole edge table on every `sort_provides` call. Falls back
/// to the full scan before the index is built (the same canonical re-filter makes both
/// paths identical). A value-fact `SortProvidesInfo` (denoted-bearing spec) is skipped
/// here; occurrence-based provides lookup is gated effect-expressions-as-types work (avoid
/// the term-only `rule_head` panic on a value head).
///
/// WI-864 — CANONICAL IN, CANONICAL OUT, and both halves are a CONTRACT rather than a
/// convention. `node_canon` must already be `canonical_sort_sym`'d: the memo is keyed that
/// way, so a raw symbol whose canonical form differs would MISS the bucket and read as "no
/// provisions" — the WI-954 failure mode. The returned spec bases are canonical for the
/// same reason the input is: the sole caller compares them against a canonical `spec` and
/// recurses on them as the next `node_canon`.
///
/// The obligation is discharged at ONE place — [`sort_provides`], which canonicalizes both
/// ends once and then never leaves canonical space — and that is why this takes the
/// canonical symbol rather than canonicalizing defensively here: canonicalizing per hop is
/// exactly the cost this ticket removed.
///
/// AND IT IS ASSERTED, because the failure is SILENT and WRONG rather than loud. A raw
/// symbol whose canonical form differs misses the canonically-keyed bucket and comes back
/// `unwrap_or_default()` — "this carrier provides nothing" — which is not a refusal but a
/// wrong verdict, feeding `sort_provides_admissibly`, the dispatch carrier filter and
/// requires-coverage, so a conforming program is silently REFUSED. Exactly WI-954's mode.
/// The corpus cannot catch it today (every provides carrier is already its own canonical
/// form, which `build_provides_index`' own `debug_assert` asserts), so a second caller
/// added later is the hazard, and this turns it into a test-time panic instead.
pub(super) fn provides_out_edges(kb: &KnowledgeBase, node_canon: Symbol) -> SmallVec<[Symbol; 4]> {
    debug_assert_eq!(
        node_canon,
        kb.canonical_sort_sym(node_canon),
        "WI-864: `provides_out_edges` is keyed on the CANONICAL carrier; `{}` is not \
         canonical, so the bucket lookup would miss and answer `provides nothing`",
        kb.qualified_name_of(node_canon),
    );
    // WI-864 — the decoded bucket when the index is live. Every filter the loop below
    // applies is already discharged at BUILD time (`is_fact`, a readable `sort_ref` whose
    // canonical form IS this key, a readable `spec` base) except liveness, which a frozen
    // bucket cannot answer — so `is_rule_alive` stays here, exactly as
    // `SymbolKeyedFactIndex::rids_or_scan` keeps it on the rid path.
    if let Some(ix) = &kb.provides_index {
        return ix
            .carrier_edges
            .get(&node_canon)
            .map(|edges| {
                edges
                    .iter()
                    .filter(|(rid, _)| kb.is_rule_alive(*rid))
                    .map(|(_, dst_canon)| *dst_canon)
                    .collect()
            })
            .unwrap_or_default();
    }
    // No index (the load-time windows where the relation is being written): decode live.
    // This is the definition the memo above is built from. A row is a FACT, as
    // `build_provides_index` buckets only facts; and the base is `provides_spec_base_sym`'s,
    // the memo's own — every row [`ProvidesRow`]'s own base decode refuses, that one refuses
    // too, so the rows the memo files and the rows this reads are the same rows.
    let mut out: SmallVec<[Symbol; 4]> = SmallVec::new();
    for row in provides_rows_of_provider_canon(kb, node_canon) {
        let Some(s) = crate::kb::load::provides_spec_base_sym(kb, row.spec_view) else {
            continue;
        };
        // CANONICAL out-edges: the sole caller compares them canonically and recurses on
        // them (where the recursion would canonicalize anyway), so canonicalizing at the
        // producer is the same relation with the conversion done once.
        out.push(kb.canonical_sort_sym(s));
    }
    out
}

/// Transitive-reachability worker for [`sort_provides`]: from `carrier_canon`, follow each
/// provides edge out of it — succeed if its target IS `spec_canon`, else recurse on the
/// target. `visited` is a cycle guard against a cyclic `provides` declaration (a sort
/// that transitively provides itself), so the walk terminates and stays
/// O(reachable × bucket).
///
/// WI-864 — BOTH ENDS ARE CANONICAL, and so is everything `visited` holds. `sort_provides`
/// converts once at the entry and the walk stays in canonical space, so every comparison
/// here is a raw `Symbol` equality rather than a `same_sort_canonical` (two
/// `qualified_name_of` reads and two `HashMap<String, _>` probes). The two are the same
/// predicate — `same_sort_canonical(a, b)` is `a == b || canonical(a) == canonical(b)`, and
/// `a == b` implies the right disjunct, so the relation IS canonical equality.
pub(super) fn sort_provides_reach(
    kb: &KnowledgeBase,
    carrier_canon: Symbol,
    spec_canon: Symbol,
    visited: &mut SmallVec<[Symbol; 8]>,
) -> bool {
    if visited.contains(&carrier_canon) {
        return false;
    }
    visited.push(carrier_canon);
    for dst_canon in provides_out_edges(kb, carrier_canon) {
        // Direct hop, then the transitive chain through the intermediate spec. WI-672
        // canonical: `spec` may be a `required_sort` (via `check_provider_requires` /
        // `check_requires_shadows`), but those are resolved (stdlib qualified; top-level
        // user specs self-consistent — see `entries_cover`), so canonical is exact.
        if dst_canon == spec_canon || sort_provides_reach(kb, dst_canon, spec_canon, visited) {
            return true;
        }
    }
    false
}

/// Check if a constructor's parent sort matches the declared type symbol.
fn constructor_matches_declared(
    kb: &KnowledgeBase,
    parent: Symbol,
    declared_type_sym: Symbol,
) -> bool {
    let declared_name = kb.local_name_of(declared_type_sym);
    let pn = kb.local_name_of(parent);
    pn == declared_name
        || pn
            .strip_suffix(declared_name)
            .is_some_and(|p| p.ends_with('.'))
        || declared_name
            .strip_suffix(pn)
            .is_some_and(|p| p.ends_with('.'))
}

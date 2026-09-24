//! Sort aliases: resolution, the alias index, and well-foundedness of alias shapes.

use super::*;

/// True iff `sym` is a sort-level type parameter — i.e., its short
/// name is registered in the type_params set of its defining scope's
/// parent sort. Distinguishes `sort T = ?` inside `sort Stream { … }`
/// (which IS a type-param) from `sort Term = ?` at namespace level
/// (which is a top-level abstract sort, not a type parameter).
pub(crate) fn is_sort_param_symbol(kb: &KnowledgeBase, sym: Symbol) -> bool {
    let Some(scope) = kb.symbols.declaring_scope(sym) else {
        return false;
    };
    let short_name = kb.local_name_of(sym);
    kb.symbols.is_type_param(scope, short_name)
}

/// The alias target of `SortAlias(<sym>, target)`, matched on EXACT symbol identity.
/// An IDENTITY — it answers "what does THIS declaration alias to" — and, since WI-956,
/// the ONLY thing it answers.
///
/// IT USED TO GUESS. A second pass keyed on the source's LOCAL NAME ran whenever the
/// exact one missed, "for legacy callers that pass a short-name symbol against a
/// qualified pos-arg". A local name means nothing outside the scope that declares it —
/// 37 `SortAlias` sources are named `T` after a stdlib load — so that pass answered
/// with whichever alias came first in `rules_by_functor` order, i.e. an unrelated
/// sort's variable. It had already caused one measured bug: WI-943 found a BRACKET
/// parameter reaching it and being answered `anthill.kernel.T`, so `cmp[T]` and
/// `cmp2[T]` shared one var. WI-943 fixed the caller and left the guess in place.
///
/// WI-956 removed it instead of re-keying it on `(parent, local name)` — MEASURED, with
/// the pass forced to `None` the FULL WORKSPACE ran 4091 tests, 0 failures. Nothing
/// wanted it. A caller that reached it now gets `None`, i.e. "not an alias", which its
/// own diagnostic can say; before, it got a plausible wrong variable.
///
/// A `sym` whose alias is genuinely wanted must therefore BE the declaration's symbol.
/// The three readers that used to lean on the guess build a qualified symbol first;
/// [`type_param_global_var`] reaches an operation's BRACKET parameter through the op's
/// own record, which is where a bracket parameter's variable actually lives.
pub(crate) fn resolve_sort_alias(kb: &KnowledgeBase, sym: Symbol) -> Option<TermId> {
    // WI-659 fast path: the SortAlias index (built once at type-check start by
    // `build_sort_alias_index`) answers in O(1). A built index is COMPLETE, so a miss
    // is a genuine "not a SortAlias" and returns `None` with NO fallback re-scan:
    // unlike a rare `op_info` miss, this is called on MANY non-alias syms, so a
    // fallback-on-miss would re-introduce the very scan the index removes.
    if let Some(index) = &kb.sort_alias_index {
        return index.by_sym.get(&sym).copied();
    }
    scan_sort_aliases(kb, |functor| functor == sym)
}

/// The pre-index scan behind both passes, for calls BEFORE `build_sort_alias_index`
/// (load-time value-typing / alias resolution). Behaviour-identical to pre-WI-659:
/// first `SortAlias` fact in `rules_by_functor` order whose source functor `matches`.
///
/// `rules_by_functor_iter`, not `rules_by_functor`: this loop only `continue`s and
/// `return`s under `&KnowledgeBase`, so it needs no snapshot — and it runs in exactly
/// the window WI-659 measured as `type_check_sorts`' #1 hotspot, where a
/// `Vec<RuleId>` sized to every `SortAlias` fact was being allocated per call, twice
/// per miss.
///
/// WI-956 made it `pub(crate)` for `load`'s
/// [`crate::kb::load::Loader::find_sort_alias_var`], which carried a verbatim copy of this
/// walk. That caller keeps only a `Var` target, and the first cut widened `matches` to
/// `(functor, target)` so the rejection could happen per fact and let the scan CONTINUE
/// — which it had to, while a by-name pass could still be looking at several same-named
/// candidates. With that pass deleted the predicate is an EXACT symbol match, one
/// source has at most one alias (`load`'s `sort_alias_exists` dedup guard; MEASURED,
/// 103 facts over 103 distinct sources in a stdlib load), so there is never a second
/// candidate to continue to and the caller post-filters instead.
pub(crate) fn scan_sort_aliases(
    kb: &KnowledgeBase,
    matches: impl Fn(Symbol) -> bool,
) -> Option<TermId> {
    let alias_sym = kb.try_resolve_symbol("SortAlias")?;
    for rid in kb.rules_by_functor_iter(alias_sym) {
        // WI-955: the SAME per-fact read as `build_sort_alias_index` — this scan is
        // that index's own pre-build fallback for `by_sym`/`by_name`, so a second
        // decoding rule here is exactly the two-readers-two-rules divergence the
        // ticket removed one map over. A denoted-bearing target carries no ground
        // `TermId` and is skipped, as callers want a ground `Var`/alias term.
        let Some((functor, target)) = sort_alias_head_slots(kb, rid) else {
            continue;
        };
        if matches(functor) {
            return Some(target);
        }
    }
    None
}

/// WI-659 — the SortAlias resolution index built once by [`build_sort_alias_index`]
/// so [`resolve_sort_alias`] is O(1) instead of a linear scan of every SortAlias fact
/// per call — the #1 `type_check_sorts` hotspot after WI-656. (It was a DOUBLE scan
/// until WI-956 deleted the by-name pass.)
#[derive(Debug, Default, Clone)]
pub(crate) struct SortAliasIndex {
    /// Source functor Symbol → alias target. Exact identity, and since WI-956 the only
    /// keying: a companion `by_name` map keyed on the source's LOCAL name was deleted
    /// with the pass that read it (see [`resolve_sort_alias`] — a local name does not
    /// identify a declaration outside its own scope).
    ///
    /// WI-954 removed a companion `by_parent` map (parent sort → its declared type
    /// params and their backing vars) that existed solely so
    /// [`reconstruct_sort_params`] could recover a sort's parameter SET from the alias
    /// facts. A parameter's declaration is published now, so that reconstruction reads
    /// it directly and this index is back to answering exactly one question.
    pub(super) by_sym: HashMap<Symbol, TermId>,
}

/// WI-955 — what every reader of a `SortAlias` FACT wants from it: the SOURCE's
/// functor `Symbol` and the TARGET as a ground `TermId`. `None` for a non-fact, a
/// missing slot, a source with no functor head, or a target that is not term-carried.
///
/// Each slot comes back in the form its consumers use, so no caller unwraps a carrier:
/// the source is only ever keyed by identity (`by_sym`), and the target is a `TermId`
/// because that is the type
/// `resolve_sort_alias` answers with. Taking the `RuleId` — not a head — means a caller
/// cannot forget the `is_fact` test and read a RULE's head as a fact.
///
/// Read through [`KnowledgeBase::rule_head_value`] + `TermView` — the CARRIER-NEUTRAL
/// surface `load`'s `sort_alias_exists` already uses — rather than `fact_head_term`,
/// which answers `None` for a head carried as a `Value::Node` and so skips the fact
/// WHOLE on a property no consumer above depends on. `ViewHead::Ref` and `Functor` are
/// both accepted for the source: a nullary sort-ref surfaces as `Ref` through the view
/// (`view_head_for`) and as `Term::Fn` in the store, and means the same either way.
///
/// Not a behaviour change. `assert_sort_alias` builds the head as
/// `[Value::term(sort_ref), target]`, so for a loader-produced alias a value-carried
/// head and a non-term target are the SAME condition and both readings skip it — a
/// stdlib + host-bindings load has 0 value-carried heads among its 107 `SortAlias`
/// facts (measured; `lower_value_or_gate` lowers a denoted target, WI-390). It is here
/// so that BOTH readers of this relation — [`build_sort_alias_index`] and
/// [`scan_sort_aliases`] — decode a fact one way.
fn sort_alias_head_slots(kb: &KnowledgeBase, rid: RuleId) -> Option<(Symbol, TermId)> {
    if !kb.is_fact(rid) {
        return None;
    }
    let head = kb.rule_head_value(rid);
    let src_functor = match head.pos_arg(kb, 0)?.head(kb) {
        ViewHead::Functor {
            functor: Some(s), ..
        } => s,
        _ => return None,
    };
    let target = head.pos_arg(kb, 1)?.as_term_id()?;
    Some((src_functor, target))
}

/// WI-659 — build the SortAlias index in ONE pass. Mirrors [`resolve_sort_alias`]'s
/// scan EXACTLY: each source is filed under its Symbol, insert-if-absent so the FIRST
/// fact per key wins (matching the scan's first-match in `rules_by_functor` order).
/// Value-fact SortAliases (no ground term head) are skipped, as the scan skips them.
/// Run at type-check start, when every SortAlias fact is asserted; SortAlias is
/// load-stable (the typer rewrites bodies, never aliases), so the built index never
/// goes stale within a load.
pub(crate) fn build_sort_alias_index(kb: &mut KnowledgeBase) {
    let Some(alias_sym) = kb.try_resolve_symbol("SortAlias") else {
        return;
    };
    let mut by_sym: HashMap<Symbol, TermId> = HashMap::new();
    for rid in kb.rules_by_functor(alias_sym) {
        let Some((functor, target)) = sort_alias_head_slots(kb, rid) else {
            continue;
        };
        by_sym.entry(functor).or_insert(target);
    }
    kb.sort_alias_index = Some(SortAliasIndex { by_sym });
}

/// WI-374 (§8.1, site-scoped): expand a FOREIGN bare/partial parametric sort
/// application in a callee-signature position to its full application form,
/// minting a FRESH logic var per unwritten declared parameter (type params
/// and effect-row params alike — an unbound plain var IS a row var). Runs
/// per call, so freshness is per application — two occurrences never alias
/// and the foreign sort's canonical vars stay untouched (§3 bullet 2).
///
/// Returns `None` (keep the form as written — today's behavior) when:
/// - the type is `Value::Node`-carried (rebuilding needs occurrence span
///   plumbing; the canonical channel still serves it),
/// - it is not a sort application, or the sort declares no parameters,
/// - it is the callee's OWN sort (the §3-bullet-1 member tie stays on the
///   canonical channel),
/// - every declared parameter is already written.
///
/// Scope: the TOP-LEVEL form of a param/return position only — a bare ref
/// NESTED inside a written binding (`Pair[B = List]`) is not yet expanded
/// (deliberate; deep expansion is follow-on scope). An alias resolves to its
/// shape first (WI-381), so only genuinely-open positions get fresh vars.
pub(super) fn expand_foreign_sort_application(
    kb: &mut KnowledgeBase,
    ty: &Value,
    callee_parent_canon: Option<Symbol>,
) -> Option<Value> {
    if !matches!(ty, Value::Term { .. }) {
        return None;
    }
    let (base, written) = sort_application_parts(kb, ty)?;
    if callee_parent_canon.is_some_and(|p| p == kb.canonical_sort_sym(base)) {
        return None;
    }
    // The WI-424 memoized pairs — `(qualified param sym, canonical Var term)`
    // — double as the declared-param list, so the per-call path never walks
    // the symbol table or SortAlias facts for an already-seen sort.
    let declared = sort_type_params_as_pairs(kb, base);
    if declared.is_empty() {
        return None;
    }
    let declared_syms: Vec<Symbol> = declared.iter().map(|(q, _)| *q).collect();
    let mut bindings: Vec<(Symbol, TermId)> = Vec::with_capacity(declared_syms.len());
    let mut filled = false;
    for qsym in declared_syms {
        let short = kb.local_name_of(qsym).to_string();
        match written.iter().find(|(k, _)| kb.local_name_of(*k) == short) {
            Some((k, v)) => match v {
                Value::Term { id: t, .. } => bindings.push((*k, *t)),
                // A Term carrier's children are Term-carried; guard anyway.
                _ => return None,
            },
            None => {
                let var_sym = kb.intern(&format!("?{short}"));
                let vid = kb.fresh_var(var_sym);
                let var_t = kb.alloc(Term::Var(Var::Global(vid)));
                // The SHORT symbol — the named-arg key convention the
                // (parameterized, parameterized) unify matches on.
                let short_sym = kb.intern(&short);
                bindings.push((short_sym, var_t));
                filled = true;
            }
        }
    }
    if !filled {
        return None;
    }
    let base_ref = kb.make_sort_ref(base);
    Some(Value::term(kb.make_parameterized_type(base_ref, &bindings)))
}

/// WI-374 (user-decided 2026-06-12): ENFORCE the §3-bullet-1 parametricity
/// tie — shared by the operation-call and constructor checkers. Scans the
/// per-var contradiction details recorded during argument/field unification;
/// a conflict on one of `owner_sort`'s OWN canonical param vars is an error
/// unless (a) its prior binding is one of the `exempt_rigids` (the WI-424
/// seeded body rigids — a same-sort sibling call at a different instance
/// keeps its pre-WI-374 acceptance; enforcing the rigid tie is a separate
/// decision), or (b) the pair RE-UNIFIES through the real relation (bare
/// `List` vs `List[T = Int64]`, wildcards, equal rows in different
/// carriers/orders are refinement — raw bind-level inequality over-reports).
/// A FOREIGN sort's var conflicting through two foreign-typed positions is
/// not scanned (§3 bullet 2: independent).
pub(super) fn enforce_member_tie(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    owner_sort: Symbol,
    error_name: Symbol,
    span: Option<Span>,
    exempt_rigids: &[(VarId, TermId)],
) -> Result<(), TypeError> {
    if !subst.is_contradiction() || subst.contradiction_details.is_empty() {
        return Ok(());
    }
    // The WI-424 memoized pairs supply the owner's canonical param vids.
    let member_vids: SmallVec<[VarId; 4]> = sort_type_params_as_pairs(kb, owner_sort)
        .iter()
        .filter_map(|(_, target)| match kb.get_term(*target) {
            Term::Var(Var::Global(v)) => Some(*v),
            _ => None,
        })
        .collect();
    if member_vids.is_empty() {
        return Ok(());
    }
    let details = subst.contradiction_details.clone();
    for (vid, prior, attempted) in &details {
        if !member_vids.contains(vid) {
            continue;
        }
        if exempt_rigids
            .iter()
            .any(|(v, r)| v == vid && matches!(prior, Value::Term { id: t, .. } if t == r))
        {
            continue;
        }
        // Walk both sides through the LIVE subst first — a recorded pair may
        // contain a var the call has since pinned (`Box[T = ?x]` with `?x`
        // later bound to Int64); re-testing the unwalked pair in an empty
        // scratch would spuriously re-unify and skip a genuine violation.
        let prior_w = walk_type_deep_value(kb, subst, prior);
        let attempted_w = walk_type_deep_value(kb, subst, attempted);
        let mut scratch = Substitution::new();
        if unify_types(kb, &mut scratch, &prior_w, &attempted_w) {
            continue;
        }
        return Err(TypeError::Other {
            site: TypeError::here(),
            span,
            context: TypeErrorContext::OperationTypeParams {
                op_name: error_name,
            },
            expected: format!(
                "consistent bindings for the sort's shared type parameter (first bound to {})",
                type_display_name_value(kb, &prior_w),
            ),
            actual: type_display_name_value(kb, &attempted_w),
        });
    }
    Ok(())
}

/// WI-381: resolve a defined-type / alias reference (`SortRef(S)`) to its underlying
/// SHAPE — following alias chains to a finite shape — so the typer judges members and
/// ungrounded positions on the *resolved* shape, not the opaque alias
/// (`docs/design/expansion-during-unification.md` §1, §6 OQ6). `sort IntStream =
/// Stream[T = Int]` resolves to `Stream[T = Int]` (so `T = Int` is KEPT and the
/// unwritten `E` stays open); a chain `Top = Mid`, `Mid = List[T = Int]` follows
/// through to `List[T = Int]`.
///
/// Returns `None` — the alias stays opaque — when `sym` is NOT a structured alias to a
/// GROUND shape:
///   - it has no `SortAlias` fact (a plain sort);
///   - the target is a bare logical `Var` — an opaque sort (`sort Term = ?`) or a type
///     parameter (`sort T = ?`); collapsing it would lose the sort-ref form (cf.
///     [`walk_type`]);
///   - the alias chain CYCLES (`sort A = A`, `A = B`/`B = A`) — a malformed definition;
///     refuse rather than loop (callers re-dispatch on the result, so a partial cyclic
///     result would not terminate);
///   - the resolved shape is NOT ground — a PARAMETRIC alias (`sort PairKey =
///     Pair[?X1, ?X2]`) with open `?` leaves, or one mentioning a sort parameter. Its
///     per-use fresh-leaf instantiation is WI-374's per-call scheme machinery; until
///     then it stays opaque, which is sound (a conservative compat / abstract-receiver
///     result, never a wrong ground bind).
pub(super) fn resolve_alias_shape(kb: &KnowledgeBase, sym: Symbol) -> Option<TermId> {
    let mut visited: Vec<Symbol> = vec![sym];
    let shape = resolve_alias_shape_chain(kb, sym, &mut visited)?;
    if !type_value_is_ground(kb, shape) {
        return None;
    }
    // WI-405: refuse a NON-WELL-FOUNDED alias — one whose ground shape transitively
    // references itself through a binding (`sort A = List[T = B]; sort B = List[T =
    // A]`). It has no finite expansion, so resolving it to a one-step shape and
    // re-dispatching through `types_compatible` (the WI-381 / WI-405 alias arms)
    // would recurse forever (a stack overflow on load). This generalizes
    // `resolve_alias_shape_chain`'s bare-ref cycle guard to DEEP structural cycles;
    // such an alias stays OPAQUE (a sound, terminating nominal comparison) exactly
    // as a bare-ref cycle does.
    if !alias_shape_well_founded(kb, shape, &mut vec![sym]) {
        return None;
    }
    Some(shape)
}

/// WI-405: a ground alias shape is WELL-FOUNDED iff fully expanding the aliases it
/// references — through bindings, recursively — terminates. `path` holds the alias
/// names on the current expansion path; encountering one already on the path is a
/// structural cycle (`sort A = List[T = B]; sort B = List[T = A]`), so the alias has
/// no finite shape. A non-alias sort-ref leaf, a logic var, or an atom is trivially
/// well-founded. The walk re-expands each alias reference with its own cycle
/// tracking, so it is robust to a bare-ref CHAIN that skipped intermediate names.
fn alias_shape_well_founded(kb: &KnowledgeBase, tid: TermId, path: &mut Vec<Symbol>) -> bool {
    // A bare sort-ref leaf (`Ref(S)` / nullary `Fn{S}`): expand if it names an alias.
    if let Some(s) = extract_sort_ref_sym(kb, &TermIdView(tid)) {
        return alias_sym_well_founded(kb, s, path);
    }
    // A parameterized / structural type: its base (the `Fn` functor) AND every
    // binding can name an alias, so check all of them. Collect the functor symbol
    // and child `TermId`s (cheap, `Copy`) so the immutable `kb` borrow from
    // `get_term` is released before the recursive calls re-borrow `kb`.
    let (functor, children): (Option<Symbol>, Vec<TermId>) = match kb.get_term(tid) {
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => (
            Some(*functor),
            pos_args
                .iter()
                .copied()
                .chain(named_args.iter().map(|(_, a)| *a))
                .collect(),
        ),
        _ => return true,
    };
    if let Some(f) = functor {
        if !alias_sym_well_founded(kb, f, path) {
            return false;
        }
    }
    children
        .iter()
        .all(|c| alias_shape_well_founded(kb, *c, path))
}

/// Expand a single sort symbol for [`alias_shape_well_founded`]: a non-alias name
/// bottoms out as well-founded; an alias is expanded under the path cycle guard
/// (revisiting a name already on the path = a structural cycle ⟹ not well-founded).
fn alias_sym_well_founded(kb: &KnowledgeBase, s: Symbol, path: &mut Vec<Symbol>) -> bool {
    let Some(target) = resolve_sort_alias(kb, s) else {
        return true;
    };
    if path.contains(&s) {
        return false;
    }
    path.push(s);
    let wf = alias_shape_well_founded(kb, target, path);
    path.pop();
    wf
}

/// The structural half of [`resolve_alias_shape`]: follow `SortAlias` (and bare-ref
/// chains) to a finite shape `TermId`. `None` for a non-alias, an alias whose target is
/// a logical `Var`, or a cyclic chain (`visited` guards revisits). A bare-ref target
/// to a NON-alias sort (`sort Top = List`) is itself the final shape.
fn resolve_alias_shape_chain(
    kb: &KnowledgeBase,
    sym: Symbol,
    visited: &mut Vec<Symbol>,
) -> Option<TermId> {
    let target = resolve_sort_alias(kb, sym)?;
    if matches!(kb.get_term(target), Term::Var(_)) {
        return None;
    }
    // A bare-ref target that NAMES another sort: if that sort is itself an alias, follow
    // the chain (`sort Top = Mid`); a revisit is a cycle → refuse. If it is NOT an alias
    // (`sort Top = List`), `target` (the bare ref) is the final shape. A parameterized
    // target (`List[T = Int]`) names its base sort, which is not an alias — same path
    // keeps `target`.
    if let Some(next) = extract_sort_ref_sym(kb, &TermIdView(target)) {
        if resolve_sort_alias(kb, next).is_some() {
            if visited.contains(&next) {
                return None;
            }
            visited.push(next);
            return resolve_alias_shape_chain(kb, next, visited);
        }
    }
    Some(target)
}

/// WI-20260924-F8PYZ — a type ALIAS read as the SORT APPLICATION it stands for, which is
/// how a spec clause reads the spec it names: `provides StoreAlias[State = WIS]` is
/// `provides Store[State = WIS]`, and `provides WisStore` over `sort WisStore = Store[State
/// = WIS]` is too. See [`alias_expansion`].
#[derive(Clone, Debug)]
pub(crate) enum AliasExpansion {
    /// The sort `base`, with the bindings the alias fixes (`WisStore` fixes `State`), each
    /// as a clause's own binding is written (`Loader::record_alias_target`), ready to
    /// splice into one.
    Sort {
        base: Symbol,
        bindings: SmallVec<[(Symbol, TermId); 2]>,
    },
    /// The alias stands for a type that is not a sort application — a tuple, an arrow, an
    /// effect row — so it names no spec.
    NotASort(TermId),
    /// The chain comes back to a name already on it (`sort A = B`, `sort B = A`), so it
    /// stands for no type at all. The chain in order, the repeated name last.
    Cycle(Vec<Symbol>),
    /// The name is an alias AND owns members of its own — a sort body beside `sort X =
    /// …`, or a `namespace X` entry at the alias's address — so it has two readings, the
    /// alias's target and itself, and nothing says which a clause means. Kernel-language
    /// §5.2 records such a duplicate as loading (rule R1 does not reach an alias); a
    /// reader that picked one reading would change what a clause about the other means.
    AlsoDeclared(Symbol),
}

/// WI-20260924-F8PYZ — what the type alias `sym` stands for, or `None` when `sym` is not a
/// type alias (a sort declared with a body, a `sort T = ?` parameter, an opaque sort).
///
/// Follows a chain of BARE links (`sort StoreAlias2 = StoreAlias`, `sort StoreAlias =
/// Store`) to the target that is not itself one, whose bindings are the ones the chain
/// fixes. An APPLIED link — `sort B = A[X = …]` with `A` an alias — is not followed, and
/// needs no rule for merging two binding lists: its declaration is refused where it is
/// written, as a type position applying arguments to a name that declares no parameters
/// (`check_sort_type_args`).
///
/// Reads [`KnowledgeBase::alias_targets`], not the `SortAlias` scan: it is asked once per
/// spec clause while files load, and that map is complete by then.
pub(crate) fn alias_expansion(kb: &KnowledgeBase, sym: Symbol) -> Option<AliasExpansion> {
    let mut target = *kb.alias_targets.get(&sym)?;
    let mut chain = vec![sym];
    loop {
        let link = *chain.last().expect("the chain starts at `sym`");
        if owns_members(kb, link) {
            return Some(AliasExpansion::AlsoDeclared(link));
        }
        let Some((head, bindings)) = sort_application(kb, target) else {
            return Some(AliasExpansion::NotASort(target));
        };
        let next = match bindings.is_empty() {
            true => kb.alias_targets.get(&head).copied(),
            false => None,
        };
        let Some(next) = next else {
            return Some(AliasExpansion::Sort {
                base: head,
                bindings,
            });
        };
        if chain.contains(&head) {
            chain.push(head);
            return Some(AliasExpansion::Cycle(chain));
        }
        chain.push(head);
        target = next;
    }
}

/// Does `sym` own a declaration's members — anything pass 1 defined inside it? A sort
/// body's parameters and operations, or a `namespace` entry's items, live in the owner's
/// scope; a `sort X = T` alias opens no scope, so a pure alias owns nothing. Pass 1
/// defines every name of every file before the declaration pass records an alias, so the
/// answer does not depend on which file or line came first.
fn owns_members(kb: &KnowledgeBase, sym: Symbol) -> bool {
    kb.symbols
        .scope(kb.symbols.scope_id(sym))
        .is_some_and(|scope| !scope.locals.is_empty())
}

/// An alias's recorded reading as a sort application — `(sort, named bindings)` — or
/// `None` for a type that is not one, by the typer's own classification (`type_head`,
/// which also keeps the tuple, arrow and effect-row meta-constructors out): a bare sort
/// reference, a sort applied by name (the plain term a clause binding lowers to), or the
/// `SortView` over a base that a binding carried as a VALUE lowers to, decoded by
/// [`unwrap_spec_view`]. A positional left over is an argument no parameter took, which
/// the alias declaration has already refused, so it reads as no application rather than
/// a partial one.
fn sort_application(
    kb: &KnowledgeBase,
    tid: TermId,
) -> Option<(Symbol, SmallVec<[(Symbol, TermId); 2]>)> {
    if let Some(sort) = extract_sort_ref_sym(kb, &TermIdView(tid)) {
        return Some((sort, SmallVec::new()));
    }
    if let Term::Fn {
        functor, pos_args, ..
    } = kb.get_term(tid)
    {
        if is_sort_view_functor(kb, *functor) {
            return match pos_args.len() {
                1 => unwrap_spec_view(kb, tid),
                _ => None,
            };
        }
    }
    let (base, positional, named) = parameterized_parts(kb, tid)?;
    positional.is_empty().then_some((base, named))
}

//! Receiver carriers and binding a spec's parameters from carriers, witnesses,
//! enclosing requirements and providers; dispatched implementation effects.

use super::*;

/// Build a `SortGoal` from a per-call substitution at a spec sort,
/// reading each declared spec param via its SortAlias-to-Var. Used by
/// `find_unique_impl_op` (compat wrapper) and by external callers
/// constructing a goal from typer state.
pub fn sort_goal_from_subst(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    carrier: Option<GoalCarrier>,
) -> SortGoal {
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();
    let mut bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    for short in kb.type_params_of_sort(spec_sort) {
        let short_sym = match kb.try_resolve_symbol(&format!("{spec_qn}.{short}")) {
            Some(s) => s,
            None => continue,
        };
        let alias_target = match resolve_sort_alias(kb, short_sym) {
            Some(t) => t,
            None => continue,
        };
        let vid = match kb.get_term(alias_target) {
            Term::Var(Var::Global(v)) => *v,
            _ => continue,
        };
        match subst.resolve_as_value(vid) {
            Some(Value::Term { id: val, .. }) => {
                let val = *val;
                let short_intern = kb.try_resolve_symbol(&short).unwrap_or_else(|| {
                    // Spec param's *short* name (e.g. "T") may not be registered
                    // as a top-level symbol; fall back to its qualified form.
                    short_sym
                });
                // WI-361: a binding value is already canonical (`Ref(S)` / `Fn{S, named}`)
                // — no `parameterized(base, bindings)` wrapper left to unwrap.
                bindings.push((short_intern, val));
            }
            // A denoted `Value::Node` binding can't ride in the `TermId`-keyed
            // `SortGoal.bindings`; carrying it is WI-348 Phase C. Omitting it is
            // sound (the dispatch goal sees one fewer constraint — a safe
            // over-approximation), but flag loudly in debug.
            Some(other) => debug_assert!(
                false,
                "WI-348: denoted {} in SortGoal bindings — carrier-agnostic SortGoal is Phase C",
                other.type_name(),
            ),
            None => {}
        }
    }
    // WI-20260828-EKWDC — THE CARRIER'S ARGUMENTS ARE RESOLVED HERE, WITH THE BINDINGS,
    // and that is the whole reason this walk is not left at the capture site. A binding
    // above is read out of σ at THIS moment; a carrier argument was read off the receiver
    // argument's `TypeResult.ty` back in [`receiver_carrier`], some 250 lines and one
    // `bind_spec_params_from_carrier` earlier, so a parameter σ pinned in between would
    // reach the provider's sub-goals as a bare variable. An under-constrained sub-goal
    // does not build a WRONG dictionary — `dispatch_values_match` refuses a variable
    // against a concrete candidate (WI-824) — but it does turn a resolvable goal into a
    // refusal, which is the defect this ticket is about, one substitution later.
    //
    // `ground = true`, matching [`resolve_type_deep_value`]: this is a call-site resolve
    // point, the same one `resolved_ret` is walked at.
    let carrier = carrier.map(|c| GoalCarrier {
        sort: c.sort,
        args: c
            .args
            .iter()
            .map(|(k, v)| (*k, walk_type_deep_g(kb, subst, *v, true)))
            .collect(),
    });
    SortGoal {
        spec_sort,
        bindings,
        carrier,
    }
}

/// WI-350 — classify a spec op's receiver at a call site to drive
/// carrier-aware dispatch. Finds the op's *self-receiver* parameter — the
/// first one declared with the spec sort itself (`head(s: Stream)`; vs
/// `PartialEq.eq(a: T, b: T)`, whose params are typed with the spec's type-
/// parameter `T`) — and reads that argument's inferred base sort.
///
/// - No self-receiver parameter ⇒ [`ReceiverCarrier::NotApplicable`]: the
///   carrier is a type-parameter binding, already pinned by the subst.
/// - Receiver's base sort is the spec sort (`s : Stream[T]`), or is ITSELF an
///   abstract-interface spec (WI-601 — a `FiniteStream`-typed value against a
///   bare `Stream` op: no own constructors, but provided), or its type is
///   unresolved ⇒ [`ReceiverCarrier::Abstract`]: no concrete impl is pinnable.
/// - Receiver's base sort is a concrete carrier (`s : List[Int]` → `List`)
///   ⇒ [`ReceiverCarrier::Concrete`].
pub(super) fn receiver_carrier(
    kb: &KnowledgeBase,
    op: &OperationInfoFull,
    spec_sort: Symbol,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> ReceiverCarrier {
    let Some(idx) = self_receiver_param_index(kb, &op.params, spec_sort) else {
        return ReceiverCarrier::NotApplicable;
    };
    let param_name = op.params[idx].0;
    // The argument may be supplied positionally (matched by declaration
    // index, as `check_apply_iter`'s unify loop does) or by name.
    let arg_ty: Option<&Value> = pos_results
        .get(idx)
        .and_then(|r| r.as_ref().ok())
        .map(|r| &r.ty)
        .or_else(|| {
            named_args
                // WI-426: a named label binds to its param by name, not symbol identity.
                .iter()
                .position(|(n, _)| same_label(kb, *n, param_name))
                .and_then(|j| named_results.get(j))
                .and_then(|r| r.as_ref().ok())
                .map(|r| &r.ty)
        });
    let spec_canon = kb.canonical_sort_sym(spec_sort);
    // WI-20260828-EKWDC: the receiver's TYPE rides beside its base sort through the
    // match, because the `Concrete` arm now needs both. A `.and_then` that kept only the
    // sort would leave the arm re-deriving `arg_ty` behind an `unwrap_or_default`, i.e. a
    // silent empty-argument fallback on a path where the value is present by
    // construction — `carrier_sort_of_value` read THIS value's head to produce `base`.
    let carrier_base = arg_ty.and_then(|v| carrier_sort_of_value(kb, v));
    match (arg_ty, carrier_base) {
        // A concrete carrier distinct from the spec sort itself, AND not itself
        // an abstract-interface spec. Store the canonical sort symbol so the
        // candidate filter (which canonicalizes `impl_sort`) compares
        // like-for-like.
        //
        // WI-601: a receiver whose static carrier is ANOTHER abstract spec — a
        // `FiniteStream`-typed value against a bare `Stream` op (`FiniteStream`
        // provides `Stream` yet has no representation of its own) — is NOT a
        // pinnable concrete impl. Resolving it concretely picks `FiniteStream`'s
        // `provides Stream → Stream requires EffectsRuntime[E]`, unsatisfiable at
        // the abstract access row `E` → a spurious `DispatchNoMatch` /
        // `MissingRequiresForSpecOp`. The runtime value is some concrete provider
        // (a `List`), so classify it `Abstract` and defer to eval's
        // value-directed dispatch, exactly the deferral the carrier-param path
        // already takes via `carrier_is_abstract_spec` (WI-598) — funnelling both
        // dispatch shapes through the one notion. Concrete carriers (`List`/`Map`
        // — they HAVE constructors, so `carrier_is_abstract_spec` is false) stay
        // `Concrete` and dispatch as before.
        (Some(ty), Some(base))
            if kb.canonical_sort_sym(base) != spec_canon && !carrier_is_abstract_spec(kb, base) =>
        {
            // WI-20260828-EKWDC: the receiver's own type ARGUMENTS ride along, read off
            // the very value `base` was read from.
            ReceiverCarrier::Concrete(GoalCarrier {
                sort: kb.canonical_sort_sym(base),
                args: receiver_type_args(kb, ty),
            })
        }
        // Base == spec sort (abstract spec value), an abstract-interface carrier
        // distinct from the op's spec (WI-601), or unresolved type: no concrete
        // impl is pinnable.
        _ => ReceiverCarrier::Abstract,
    }
}

/// WI-20260828-EKWDC — the type ARGUMENTS a receiver's own type writes at its carrier
/// sort, as the `TermId`s a [`GoalCarrier`] carries.
///
/// [`parametric_value_parts`] AND NOT [`extract_type`], for the reason
/// [`carrier_arg_impl_subst`] gives about the rule itself: that is the reader
/// [`match_candidate_against_goal`]'s arm (2.5) already asks this same question through,
/// so "what are this instance's type arguments" has one owner across both routes to a
/// receiver. It is also the cheaper walk — a `SmallVec` clone of the head's named args,
/// where `extract_type` builds a `Vec<(Symbol, Value)>` and clones a `Value` per
/// argument.
///
/// AND IT IS NOT A HOT PATH, which a review raised as a cost and a measurement settled
/// the other way: **4 calls per full stdlib load** (counted, plus a source making one
/// such call of its own). `receiver_carrier` reaches here only from its `Concrete` arm,
/// and a self-receiver spec op on a STATICALLY CONCRETE carrier is the rare shape — every
/// `Stream.splitFirst` over a `Stream`-typed value classifies `Abstract` first and never
/// arrives. Timed as well, paired and alternating both arms in ONE process (min of 9,
/// warmup dropped, debug): the distributions overlap completely and the arm that BUILDS
/// the arguments had the lower minimum, i.e. the difference is under this box's noise
/// floor for one unchanged binary. Two of the four `receiver_carrier` call sites keep
/// only `.sort`; deferring the walk for them would buy 2 SmallVec clones per load and
/// cost a second spelling of this question.
///
/// EMPTY for a bare sort reference (`s : List`, nothing written) and for every
/// non-application carrier, which is the honest answer: the receiver said nothing about
/// the carrier's parameters, so nothing is added to what the provision head already
/// pinned.
///
/// EMPTY, TOO, FOR AN OCCURRENCE-CARRIED TYPE (a `Value::Node`, WI-477), and this is a
/// stated gap rather than a silence — the WI-348 Phase C one [`SortGoal::bindings`]
/// records from the other side. It is NOT asserted against the way that sibling's is:
/// this walk sees EVERY named argument of a receiver's own type, and
/// [`witness_sort_goal`] feeds it types read back off runtime values, so a `Value::Node`
/// here is a shape the language admits and the `TermId`-keyed channel cannot carry — a
/// `debug_assert` would turn that into a dev-build panic on a legal program. Dropping one
/// argument leaves its parameter exactly as the provision head left it, which is the
/// pre-WI-EKWDC behaviour for that parameter and a refusal downstream, never a wrong
/// binding. (`witness_sort_goal` reaches the same verdict for its own bindings three
/// lines on, through `type_value_as_term`.)
pub(super) fn receiver_type_args(
    kb: &KnowledgeBase,
    ty: &Value,
) -> SmallVec<[(Symbol, TermId); 2]> {
    let Value::Term { id, .. } = ty else {
        return SmallVec::new();
    };
    parametric_value_parts(kb, *id)
        .map(|(_, args)| args)
        .unwrap_or_default()
}

/// WI-350 — index of a spec op's *self-receiver* parameter: the first one
/// declared with the spec sort itself (`head(s: Stream)`), as opposed to a
/// type-parameter-carrier parameter (`PartialEq.eq(a: T, b: T)`, whose type is the
/// spec's own type-parameter). `None` when the op has no self-receiver
/// parameter. Shared by the typer's [`receiver_carrier`] and the
/// interpreter's value-directed dispatch so the two never disagree about
/// which argument names the carrier. Compares canonical sort symbols (the
/// same logical sort may be interned under several `Symbol`s).
pub(crate) fn self_receiver_param_index(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    spec_sort: Symbol,
) -> Option<usize> {
    let spec_canon = kb.canonical_sort_sym(spec_sort);
    params.iter().position(|(_, pty)| {
        // WI-341 Stage A: carrier-agnostic. A `Value::Node` (denoted-bearing
        // callback) param type is never a spec carrier sort → `None`.
        carrier_sort_of_value(kb, pty).map(|s| kb.canonical_sort_sym(s)) == Some(spec_canon)
    })
}

/// WI-350 — the base sort symbol of a value standing in *type* position
/// (an argument's inferred `TypeResult.ty`). WI-477: read carrier-agnostically
/// through `sort_functor_of_view` — an occurrence-primary type result is a
/// `Value::Node`, and `.as_term()` would drop it; a structural carrier (arrow /
/// effect-row / denoted) has no sort head and yields `None` here, as before.
pub(super) fn carrier_sort_of_value(kb: &KnowledgeBase, v: &Value) -> Option<Symbol> {
    sort_functor_of_view(kb, v)
}

/// WI-424 — the canonical param `VarId` a declared parameter type stands for:
/// either the alias var directly (`Term::Var(Global)`) or a `Ref`/`Ident` to a
/// sort type-param resolved through its `SortAlias` — the form a signature
/// stores (`c: C` is `Ref(S.C)`, exactly as `effects E` is `Ref(S.E)`).
///
/// The carrier-grounding dual of [`sigma_class`]: both name a type-param's
/// canonical VarId, but this stays structural (no substitution chase, no rigid
/// bridge — its callers compare against static `Var::Global` spec-params) and is
/// carrier-agnostic over `&Value` (a `Value::Node` param type, WI-477), where
/// σ-class chases a `TermId` under σ. The shared alias resolution is
/// [`type_param_global_var`].
pub(super) fn declared_type_param_vid(kb: &KnowledgeBase, pty: &Value) -> Option<VarId> {
    if let Some(v) = resolved_var(kb, pty) {
        return Some(v);
    }
    // WI-477: read the head carrier-agnostically — a sort type-param ref (`c: C`
    // ⇒ `Ref(S.C)`) reads as a NULLARY head whether the param type rides as a
    // `TermId` or a `Value::Node`; a structural carrier (arrow/row) has arguments,
    // so the arity pin keeps it at `None`, as before.
    //
    // WI-20260902-CZJ2N: `pos_arity: 0, named_arity: 0` is what the retired
    // `ViewHead::Ref` variant used to carry. Without the pin this would read the
    // BASE of `List[T = Int]` as a type param.
    match pty.head(kb) {
        ViewHead::Ident(s) => type_param_global_var(kb, s),
        ViewHead::Functor {
            functor: Some(s),
            pos_arity: 0,
            named_arity: 0,
        } => type_param_global_var(kb, s),
        _ => None,
    }
}

/// WI-424 — the gate distinguishing a spec's CARRIER param from an
/// element-like param: does `carrier_sym`'s provision of `spec_sort` bind the
/// spec param whose canonical var is `pvid` to an application of the carrier
/// itself (`provides Iterable[C = List[T], …]` ⇒ true for `C`'s vid with
/// carrier `List`; false for `Element`'s)? Shared by the typer's
/// [`carrier_param_receiver`] and eval's [`carrier_param_receiver_for_values`]
/// so the two classifications cannot disagree about which argument names the
/// carrier. The binding value rides a `SortView(List[T], …)` wrapper — unwrap
/// via the same reader the provider machinery uses.
pub(super) fn provision_binds_param_to_carrier(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    pvid: VarId,
    carrier_sym: Symbol,
) -> Option<SmallVec<[(Symbol, TermId); 2]>> {
    let carrier_canon = kb.canonical_sort_sym(carrier_sym);
    let binds_pvid_to_carrier = |view: &SmallVec<[(Symbol, TermId); 2]>| {
        view.iter().any(|(sp_sym, sp_val)| {
            type_param_vid_in_sort(kb, spec_sort, *sp_sym) == Some(pvid)
                && crate::kb::load::provides_spec_base_sym(kb, *sp_val)
                    .map(|b| kb.canonical_sort_sym(b))
                    == Some(carrier_canon)
        })
    };
    // Primary: the carrier-keyed provision (`sort_ref == carrier`) — a fact whose
    // derived carrier IS the value's sort, or a normal provider whose own sort IS
    // the carrier. Unchanged hot path (Iterable.iterator on a List, Eq on Int64).
    if let Some(view) = provider_spec_view_bindings(kb, carrier_sym, spec_sort) {
        if binds_pvid_to_carrier(&view) {
            return Some(view);
        }
    }
    // WI-450: a WITNESS provision (`sort_ref != carrier`) of `spec_sort` that binds
    // this param to the carrier — `sort TagCombiner provides Combiner[T = Tag]`
    // classifies a `T`-typed arg valued `Tag` as the carrier param even though the
    // provider sort is `TagCombiner`, not `Tag`.
    //
    // WI-842 (058 §4.9): ANY witnessing provision answers, so this SEARCHES the
    // witnesses rather than taking the first one. The question here is EXISTENCE —
    // does this argument position name the carrier? — and an existence read stays
    // boolean under coexistence: every provision of `spec_sort` AT this carrier binds
    // the carrier param to it identically, that being what makes it a provision for
    // this carrier at all. Taking "the first witness" also answered `None` when the
    // first bound no matching param and a second did.
    provides_rows_of_spec(kb, spec_sort)
        .filter(|row| {
            witness_dispatch_carrier(kb, spec_sort, row.provider, row.spec_view)
                == Some(carrier_canon)
        })
        .map(|row| row.bindings)
        .find(|view| binds_pvid_to_carrier(view))
}

/// WI-20260828-57MRM — the WITNESS sort whose provision of `spec_sort` dispatches at
/// `carrier_sym`, if the provision comes from a witness rather than from the carrier's own
/// `provides`. The same scan [`provision_binds_param_to_carrier`]'s witness arm makes,
/// asked for the PROVIDER instead of the view — [`bind_spec_params_from_carrier_param`]
/// needs it to know whose binder the view's variables belong to.
fn witness_provider_for(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    pvid: VarId,
    carrier_sym: Symbol,
) -> Option<Symbol> {
    let carrier_canon = kb.canonical_sort_sym(carrier_sym);
    // The SAME iterator, filter and find-predicate `provision_binds_param_to_carrier`'s
    // witness arm uses, so the two cannot select different witnesses when several provide
    // `spec_sort` at this carrier — σ must come from the binder the VIEW came from.
    // `provider != carrier` is the additivity guard: a provider that IS the carrier is the
    // case that function's FIRST arm already answered, so reaching here means it declined.
    provides_rows_of_spec(kb, spec_sort)
        .filter(|row| {
            kb.canonical_sort_sym(row.provider) != carrier_canon
                && witness_dispatch_carrier(kb, spec_sort, row.provider, row.spec_view)
                    == Some(carrier_canon)
        })
        .find(|row| {
            row.bindings.iter().any(|(sp_sym, sp_val)| {
                type_param_vid_in_sort(kb, spec_sort, *sp_sym) == Some(pvid)
                    && crate::kb::load::provides_spec_base_sym(kb, *sp_val)
                        .map(|b| kb.canonical_sort_sym(b))
                        == Some(carrier_canon)
            })
        })
        .map(|row| row.provider)
}

/// WI-20260828-57MRM — instantiate a WITNESS provision against the receiver: the σ that
/// takes the witness sort's OWN parameters to the receiver's type-args.
///
/// A witness `fact` is a TEMPLATE over its own binder —
/// `fact Box[C = Wrap[Source = S, T = T, ES = ES, EF = EF], Element = T, E = {ES, EF}]` —
/// and the head's other bindings (`Element`, `E`) are written in THAT binder's variables,
/// not the carrier's. Reading them leaf-by-leaf against the CARRIER, as
/// [`substitute_carrier_params`] does, is the wrong namespace; it only ever appeared to work
/// when witness and carrier happened to spell a parameter the same way (MEASURED: rename the
/// witness's row parameter and the binding leaks, with no other change).
///
/// The fact's CARRIER BINDING is the equation relating the two — match it against the
/// receiver's type and every witness variable gets its value. This builds that σ.
///
/// TWO OCCURRENCE FORMS, and both must be recognized, because one parameter is spelled
/// differently by position: in a type-argument slot it is a `Ref(parameter symbol)`
/// (`Wrap[ES = ES]`), inside an effect ROW it is the bare `Var(Global(parameter vid))` the
/// row's tail carries (`{ES, EF}` ⟹ `merge[open[tail = Var], open[tail = Var]]`). Keying σ
/// on the witness's VarId covers both: a `Ref` is resolved to its parameter's vid first.
///
/// Returns EMPTY for an ordinary `provides`, whose carrier binding is a bare reference
/// rather than an application — so the non-witness path is untouched.
pub(super) fn witness_instantiation(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    carrier_sym: Symbol,
    carrier_pvid: VarId,
    view_bindings: &[(Symbol, TermId)],
    recv_bindings: &[(VarId, TermId)],
) -> Option<(Vec<(Symbol, TermId)>, Vec<(VarId, TermId)>)> {
    // CHEAP GATE FIRST — the carrier binding being an APPLICATION of the carrier is the
    // witness signature (an ordinary `provides` writes a bare reference). Every ordinary
    // dispatch answers here, before the provider scan below runs at all.
    let (_, carrier_val) = view_bindings
        .iter()
        .find(|(p, _)| type_param_vid_in_sort(kb, spec_sort, *p) == Some(carrier_pvid))?;
    let Term::Fn {
        functor,
        named_args,
        ..
    } = kb.get_term(*carrier_val).clone()
    else {
        return None;
    };
    if kb.canonical_sort_sym(functor) != kb.canonical_sort_sym(carrier_sym) {
        return None;
    }
    // …but the APPLICATION shape does NOT by itself mean a witness: an ordinary `provides`
    // may write its carrier applied too (`List provides FiniteCollection[C = List[T], …]`,
    // `MutableStack[T]`). `provision_binds_param_to_carrier` PREFERS the carrier's own
    // provides when it qualifies, and that head is written in the CARRIER's parameters, so
    // building σ from a witness's binder and applying it there would substitute across two
    // different binders — the very defect this function exists to prevent. Mirror that
    // function's arm order: if the carrier's own provides qualifies, the view came from it.
    let carrier_canon = kb.canonical_sort_sym(carrier_sym);
    let own_provides_qualifies = provider_spec_view_bindings(kb, carrier_sym, spec_sort)
        .is_some_and(|view| {
            view.iter().any(|(sp_sym, sp_val)| {
                type_param_vid_in_sort(kb, spec_sort, *sp_sym) == Some(carrier_pvid)
                    && crate::kb::load::provides_spec_base_sym(kb, *sp_val)
                        .map(|b| kb.canonical_sort_sym(b))
                        == Some(carrier_canon)
            })
        });
    if own_provides_qualifies {
        return None;
    }
    let witness = witness_provider_for(kb, spec_sort, carrier_pvid, carrier_sym)?;
    // Read the witness's parameter table ONCE — the walk below visits every leaf of every
    // head binding, and rebuilding it per leaf is the difference between one read and one
    // per node.
    let witness_params = sort_type_params_as_pairs(kb, witness).to_vec();
    let subst: Vec<(VarId, TermId)> = named_args
        .iter()
        .filter_map(|(carrier_param, witness_occ)| {
            let wvid = witness_param_vid_of_occurrence(kb, *witness_occ, &witness_params)?;
            let cvid = type_param_vid_in_sort(kb, carrier_sym, *carrier_param)?;
            let arg = recv_bindings.iter().find(|e| e.0 == cvid)?.1;
            Some((wvid, arg))
        })
        .collect();
    (!subst.is_empty()).then_some((witness_params, subst))
}

/// WI-20260828-57MRM — the WITNESS parameter a head occurrence denotes, in either spelling:
/// the `Var(Global(vid))` a row tail carries, or the `Ref(symbol)` a type-argument slot
/// writes. `None` for anything that is not one of `witness`'s own parameters (a concrete
/// leaf such as `Int64`, or another sort's parameter), which therefore substitutes nothing.
fn witness_param_vid_of_occurrence(
    kb: &KnowledgeBase,
    occ: TermId,
    // WI-20260921-3G1YT — the `witness: Symbol` parameter was dropped as unused (it
    // warned). Both arms below match against `witness_params`, which already IS that
    // witness's declared parameter list, so the symbol added nothing; passing it
    // suggested a second identity check that was never performed.
    witness_params: &[(Symbol, TermId)],
) -> Option<VarId> {
    let vid_of = |t: TermId| match kb.get_term(t) {
        Term::Var(Var::Global(v)) => Some(*v),
        _ => None,
    };
    match kb.get_term(occ) {
        // A ROW tail: the parameter's own var, so membership is EXACT — no name involved.
        Term::Var(Var::Global(v)) => witness_params
            .iter()
            .any(|(_, t)| vid_of(*t) == Some(*v))
            .then(|| *v),
        // A TYPE-ARGUMENT slot: the parameter's symbol, matched against the witness's own
        // declared parameters by SYMBOL IDENTITY. Deliberately NOT `type_param_vid_in_sort`,
        // which resolves a symbol by its LOCAL NAME in the owner's scope — that is a name
        // join, and it is exactly the hazard this paragraph excludes; using it here would
        // make the guarantee below asserted rather than true (caught by review). A head may write
        // ANOTHER sort's parameters into the slots, and may PERMUTE them
        // (`SomeAlgebra[T = X.S, S = X.T]`); joining on last segments would pair `X.S` with
        // the witness's `S` and silently invert exactly that permutation, which is the
        // cross-sort `T` collapse identity-keyed matching exists to prevent. A value that is
        // not one of this witness's own parameters resolves to `None` and substitutes
        // nothing, which is the correct answer for it.
        Term::Ref(sym) => witness_params
            .iter()
            .find(|(p, _)| *p == *sym)
            .and_then(|(_, t)| vid_of(*t)),
        _ => None,
    }
}

/// WI-20260828-57MRM — apply [`witness_instantiation`]'s σ to one head binding, replacing
/// each witness-parameter occurrence (in either spelling) by the receiver's type-arg.
///
/// The `witness: Symbol` parameter is gone for the reason WI-20260921-3G1YT dropped it from
/// [`witness_param_vid_of_occurrence`]: it was only ever passed down the recursion, and
/// `witness_params` already IS that witness's parameter list.
fn apply_witness_instantiation(
    kb: &mut KnowledgeBase,
    tid: TermId,
    witness_params: &[(Symbol, TermId)],
    subst: &[(VarId, TermId)],
) -> TermId {
    rewrite_term_leaves(kb, tid, &|kb, t| {
        let v = witness_param_vid_of_occurrence(kb, t, witness_params)?;
        subst.iter().find(|(w, _)| *w == v).map(|(_, bound)| *bound)
    })
}

/// WI-492 — the specs a carrier sort DIRECTLY provides (base symbols), read
/// from its carrier-keyed `SortProvidesInfo` facts. The transitive-provision
/// hop set for [`transitive_carrier_for_param`] (a single carrier-keyed scan,
/// mirroring the edge extraction in [`sort_provides`]).
///
/// DIRECT rows only, and its second reader — WI-879's
/// [`crate::kb::load::derive_carrier_builtin_tags`] — is why that word now matters to
/// somebody. A `provides` TOWER (`Int64 provides EuclideanDomain`, `EuclideanDomain
/// provides Divisible[T = T]`) reaches this set only once WI-1109's
/// [`derive_forwarded_provisions`] has materialized the forwarded row, so a caller that
/// needs the closure must run below that pass rather than reach for a transitive walk
/// here.
pub(crate) fn directly_provided_specs(
    kb: &KnowledgeBase,
    carrier_sym: Symbol,
) -> SmallVec<[Symbol; 4]> {
    let mut out: SmallVec<[Symbol; 4]> = SmallVec::new();
    for row in provides_rows_of_provider(kb, carrier_sym) {
        if !out
            .iter()
            .any(|&s| same_sort_canonical(kb, s, row.spec_base))
        {
            out.push(row.spec_base);
        }
    }
    out
}

/// WI-492 — the EFFECTIVE carrier sort that owns `spec_sort`'s implementation
/// for a runtime value of sort `value_sort`, following TRANSITIVE provision.
/// Provision is NOT transitive in the stored `SortProvidesInfo` facts: a
/// `MappedStream provides Stream` fact and a `Stream provides Iterable[C =
/// Stream]` fact both exist, but no `MappedStream provides Iterable` fact does
/// — yet a `MappedStream` value must dispatch the Iterable ops (`iterator`, and
/// the inherited `find`/`map`/`filter`), since its Iterable-ness rides through
/// Stream. (The TYPER never hits this — `xs.map(f)` has the declared return
/// type `Stream`, so the static receiver of a downstream `.filter` is already
/// `Stream`, which directly provides Iterable; the gap is only the RUNTIME
/// value, a `mapped(…)` entity of sort `MappedStream`.)
///
/// Resolve to the INTERMEDIATE spec that DIRECTLY binds the carrier param
/// `pvid` to itself — `Stream`, whose `iterator(s) = s` is the genuine impl —
/// so the value-directed op resolution (`sort_ops_lookup(Stream, iterator)`)
/// finds the inherited member instead of dying `UnknownOperation`. A DIRECT
/// provider wins unchanged (returns `value_sort` itself — the `iterator`-on-a-
/// `List`, `Eq`-on-`Int64` hot path). Otherwise walk the specs `value_sort`
/// provides, depth-first, first match wins; `visited` guards a cyclic
/// `provides` chain (cf. [`sort_provides_reach`]).
fn transitive_carrier_for_param(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    pvid: VarId,
    value_sort: Symbol,
) -> Option<Symbol> {
    fn walk(
        kb: &KnowledgeBase,
        spec_sort: Symbol,
        pvid: VarId,
        sort: Symbol,
        visited: &mut SmallVec<[Symbol; 8]>,
    ) -> Option<Symbol> {
        if visited.iter().any(|&v| same_sort_canonical(kb, v, sort)) {
            return None;
        }
        visited.push(sort);
        // This sort directly binds the carrier param to itself — it owns the impl.
        if provision_binds_param_to_carrier(kb, spec_sort, pvid, sort).is_some() {
            return Some(sort);
        }
        // Otherwise descend through the specs this sort itself provides.
        for intermediate in directly_provided_specs(kb, sort) {
            if let Some(found) = walk(kb, spec_sort, pvid, intermediate, visited) {
                return Some(found);
            }
        }
        None
    }
    let mut visited: SmallVec<[Symbol; 8]> = SmallVec::new();
    walk(kb, spec_sort, pvid, value_sort, &mut visited)
}

/// WI-495 — compose two provision views, eliminating the intermediate spec.
/// `outer_view` maps `spec_sort`'s params to values written in terms of the
/// INTERMEDIATE spec's params (`Stream provides Iterable[Element = T, E = E]` ⇒
/// `{Element ↦ Stream.T, E ↦ Stream.E}`); `inner_view` maps the intermediate
/// spec's params to CARRIER-relative values (`List provides Stream[T = T, E = {}]`
/// ⇒ `{Stream.T ↦ List.T, Stream.E ↦ {}}`). The result maps `spec_sort`'s params
/// to carrier-relative values (`{Element ↦ List.T, E ↦ {}}`) — exactly the shape
/// the carrier's DIRECT provision of `spec_sort` would have, so the existing
/// [`bind_spec_params_from_carrier_param`] grounds them against the receiver's
/// type args / a written row with no further change.
///
/// An outer value that is a bare type-param ref of the intermediate (`Stream.T`)
/// is substituted by the inner binding for that param (WI-600: matched by the
/// intermediate sort's canonical `Var::Global` param VarId, not the short name); a
/// ground value (a written `{}` row) or a value not referencing an intermediate
/// param (the carrier application `C ↦ Stream`) is kept verbatim. A COMPOUND that
/// merely MENTIONS an intermediate param (`Element = Pair[A = Stream.T]`) is kept
/// verbatim un-substituted — `bind_spec_params_from_carrier_param` then skips it
/// as non-ground non-ref and the param surfaces a LOUD `?_` rather than a
/// silently-wrong bind (deep compound substitution is follow-up, cf. WI-380).
///
/// WI-20260829-XZMGC — THE VERBATIM CARRIER APPLICATION IS WRONG FOR ANYONE WHO READS IT,
/// and this function keeps it anyway because its three consumers do not. `C ↦ Stream` is
/// the INTERMEDIATE naming itself; the carrier of a composed view is the sort at the far
/// end of the chain. CENSUSED: [`bind_spec_params_from_carrier`] drops it (a bare `Stream`
/// takes the `ref_shape` arm and names no parameter of the carrier, so `concrete` is
/// `None` — and it would drop a correct `List` too), [`bind_spec_params_from_carrier_param`]
/// skips the carrier param by VarId (WI-593: it binds by argument unification), and
/// [`bare_spec_arg_provision_projection`] skips it by VarId and substitutes the receiver's
/// own type — its comment is a MEASUREMENT of this artifact escaping into
/// `MappedStream[Source = Stream, …]`. The fourth reader, the SUBTYPE relation, is the one
/// that compares it, and it excludes the parameter itself: see [`subtype_provider_view`].
/// Emitting the right value here would need `kb.alloc` and therefore `&mut KnowledgeBase`
/// through two read paths that discard the value.
fn compose_provision_views(
    kb: &KnowledgeBase,
    intermediate: Symbol,
    outer_view: &SmallVec<[(Symbol, TermId); 2]>,
    inner_view: &SmallVec<[(Symbol, TermId); 2]>,
) -> SmallVec<[(Symbol, TermId); 2]> {
    outer_view
        .iter()
        .map(|(spec_param, val)| {
            if let Some(inter_vid) = typaram_ref_vid(kb, *val, intermediate) {
                if let Some((_, inner_val)) = inner_view
                    .iter()
                    .find(|(p, _)| type_param_vid_in_sort(kb, intermediate, *p) == Some(inter_vid))
                {
                    return (*spec_param, *inner_val);
                }
            }
            (*spec_param, *val)
        })
        .collect()
}

/// WI-495 — the provision view of `carrier_sym` for `spec_sort` (binding the
/// carrier param `pvid`), DIRECT or composed through TRANSITIVE provision. The
/// typer-side companion to [`transitive_carrier_for_param`] (the eval path): a
/// `List` value's STATIC type is the concrete `List`, so the typer classifies it
/// as the Iterable carrier directly and must GROUND `Iterable`'s `Element` / `E`
/// from `List`'s provision of `Stream` — `List provides Stream` + `Stream
/// provides Iterable`, with no direct `List provides Iterable` fact. Direct
/// provision wins (returns the carrier's own view unchanged — the explicit-
/// `provides Iterable` hot path). Otherwise descend the specs `carrier_sym`
/// provides, find the one that (transitively) owns `spec_sort` with `pvid`
/// bound, and compose its view back through each hop's carrier→intermediate
/// bindings via [`compose_provision_views`]. `visited` guards a cyclic chain.
///
/// The returned flag is `true` iff the view came via the TRANSITIVE (provides-
/// chain) branch at the top level — `carrier_sym` does not itself bind the carrier
/// param, the impl lives on an intermediate spec sort. WI-496 reads it to leave a
/// body-less spec-op call (`iterator(xs:List)`) as the spec op for eval rather
/// than attempting concrete dispatch (which would die on the intermediate's own
/// `requires`); a DIRECT / WITNESS provider (flag `false`) still dispatches
/// concretely. No separate walk is needed — the branch that built the view IS the
/// classification.
pub(super) fn transitive_provision_view(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    pvid: VarId,
    carrier_sym: Symbol,
    visited: &mut SmallVec<[Symbol; 8]>,
) -> Option<(SmallVec<[(Symbol, TermId); 2]>, bool)> {
    // Direct: the carrier itself provides spec_sort binding the carrier param.
    compose_through_provision_chain(kb, carrier_sym, visited, VisitOrder::VisitedFirst, &|c| {
        provision_binds_param_to_carrier(kb, spec_sort, pvid, c)
    })
}

/// WI-20260923-32XFQ — where the chain walk marks a carrier visited, relative to asking
/// the direct question of it. The ONE thing the two chain walks did differently, kept as
/// they had it.
///
/// It is not a formality, though every current answer agrees. A carrier is pushed only
/// after its direct question failed under `DirectFirst`, so a revisit fails the same way
/// either order; but under `VisitedFirst` a carrier whose direct question SUCCEEDED is in
/// `visited` too, and if the hop above it then cannot compose (no carrier→intermediate
/// view) a sibling path reaching the same carrier answers `None` where `DirectFirst`
/// answers its view. Choosing one order for both is an answer changing, not a merge.
#[derive(Clone, Copy)]
enum VisitOrder {
    /// Mark the carrier visited, then ask the direct question — [`transitive_provision_view`].
    VisitedFirst,
    /// Ask the direct question, then mark — [`transitive_provider_spec_view_bindings`].
    DirectFirst,
}

/// WI-20260923-32XFQ — a provision view of `carrier_sym`: `direct`'s own answer for it,
/// else an intermediate spec it DIRECTLY provides that (transitively) answers, composed
/// back through the carrier→intermediate hop via [`compose_provision_views`]. The flag is
/// `true` iff the view came through a hop at THIS level. `visited` guards a cyclic
/// `provides` chain, placed per `order`.
///
/// The one recursion under the two transitive readers, which spelled it twice with
/// different direct questions and different visit orders.
fn compose_through_provision_chain(
    kb: &KnowledgeBase,
    carrier_sym: Symbol,
    visited: &mut SmallVec<[Symbol; 8]>,
    order: VisitOrder,
    direct: &impl Fn(Symbol) -> Option<SmallVec<[(Symbol, TermId); 2]>>,
) -> Option<(SmallVec<[(Symbol, TermId); 2]>, bool)> {
    let seen = |visited: &SmallVec<[Symbol; 8]>| {
        visited
            .iter()
            .any(|&v| same_sort_canonical(kb, v, carrier_sym))
    };
    if matches!(order, VisitOrder::VisitedFirst) {
        if seen(visited) {
            return None;
        }
        visited.push(carrier_sym);
    }
    if let Some(view) = direct(carrier_sym) {
        return Some((view, false));
    }
    if matches!(order, VisitOrder::DirectFirst) {
        if seen(visited) {
            return None;
        }
        visited.push(carrier_sym);
    }
    // Transitive: an intermediate spec the carrier provides answers.
    for intermediate in directly_provided_specs(kb, carrier_sym) {
        let Some((outer_view, _)) =
            compose_through_provision_chain(kb, intermediate, visited, order, direct)
        else {
            continue;
        };
        // The carrier→intermediate bindings, to eliminate the intermediate's params.
        let Some(inner_view) = provider_spec_view_bindings(kb, carrier_sym, intermediate) else {
            continue;
        };
        return Some((
            compose_provision_views(kb, intermediate, &outer_view, &inner_view),
            true,
        ));
    }
    None
}

/// WI-608 — the carrier-param provision view for a receiver whose carrier is
/// ITSELF an abstract spec that `requires` `spec_sort` (rather than *providing*
/// it). `iterator(src)` over a field `src : FiniteCollection[C = SrcC, Element =
/// Src, E = ES]` dispatches `Iterable.iterator` (spec_sort = Iterable), but
/// `FiniteCollection` has no `provides Iterable` fact — it declares `requires
/// Iterable[C = C, Element = Element, E = E]` — so [`transitive_provision_view`]
/// (a `provides`-only walk) finds nothing and the produced `Stream[Element, E]`
/// leaks `??_` for both params.
///
/// The `requires` clause is stored as a `SortView` mapping each Iterable param to
/// the `FiniteCollection` param it is bound to — the SAME view shape
/// [`provider_spec_view_bindings`] returns for a `provides` fact, so the caller's
/// [`bind_spec_params_from_carrier_param`] threads each spec param off the
/// receiver's own written type-args (`Element ↦ Element ↦ Src`, `E ↦ E ↦ ES`;
/// the carrier param `C` is skipped there — it binds by argument unification).
/// DIRECT requires only: the current gap is a field typed with a spec its own
/// combinator directly requires; a transitively-required spec would need the
/// composed chain (cf. [`transitive_provision_view`]) and has no stdlib call site.
fn abstract_spec_required_view(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    carrier_sym: Symbol,
) -> Option<SmallVec<[(Symbol, TermId); 2]>> {
    for entry in direct_requires(kb, carrier_sym) {
        if kb.canonical_sort_sym(entry.required_sort) != kb.canonical_sort_sym(spec_sort) {
            continue;
        }
        let (_base, bindings) = unwrap_spec_view_value(kb, &entry.spec)?;
        if !bindings.is_empty() {
            return Some(bindings);
        }
    }
    None
}

/// WI-424 — eval-side CARRIER-PARAM receiver: among the params typed as one of
/// `spec_sort`'s own type-param vars (`Iterable.iterator(c: C)`), the first
/// whose RUNTIME value's carrier sort (`carrier_of(i)`) provides the spec WITH
/// that param bound to the carrier application — the same
/// [`provision_binds_param_to_carrier`] gate the typer applies, so an
/// element-typed param never dispatches (the value-directed dual of
/// [`self_receiver_param_index`]'s deliberate type-param-carrier exclusion).
/// Returns the param index and the value's carrier sort.
pub(crate) fn carrier_param_receiver_for_values(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    spec_sort: Symbol,
    carrier_of: &dyn Fn(usize) -> Option<Symbol>,
) -> Option<(usize, Symbol)> {
    for (i, _, pvid) in spec_param_typed_params(kb, params, spec_sort)? {
        let Some(carrier_sym) = carrier_of(i) else {
            continue;
        };
        // WI-492: a value whose sort provides `spec_sort` only TRANSITIVELY
        // (a `MappedStream` value of `Iterable`, via `MappedStream provides
        // Stream provides Iterable`) dispatches through the intermediate
        // spec that owns the impl — `transitive_carrier_for_param` returns
        // `carrier_sym` unchanged for a direct provider.
        if let Some(eff_carrier) = transitive_carrier_for_param(kb, spec_sort, pvid, carrier_sym) {
            return Some((i, eff_carrier));
        }
    }
    None
}

/// WI-365 — the parametric sort a self-receiver op belongs to, whether or not
/// it has a default body. [`lookup_spec_op_dispatch`] returns the parent only
/// for body-LESS spec ops (the dispatch candidates); a default-bodied spec op
/// (`Stream.collect`) is a normal op for dispatch but still carries the sort's
/// element / effect parameters, which must be grounded from the carrier when
/// the op is consumed on a concrete provider. `None` unless the parent is a
/// parametric sort AND the op has a self-receiver parameter (one typed as the
/// sort itself, e.g. `s: Stream`) — the same shape [`receiver_carrier`] keys on.
///
/// WI-958 — "parametric sort that declares `fn_sym`" is [`spec_op_parent_sort`]'s
/// question, so this asks it rather than re-deriving it; the self-receiver gate is
/// the ONLY thing this adds, and the callers that consult both readers in one pass
/// (`check_apply`'s WI-357 and WI-444 blocks) now agree on the spec sort by
/// construction. That merge also ADDS the `has_kind(Sort)` gate here, which this copy
/// lacked. Behaviour-identical, and MEASURED twice over: the only non-`Sort` scope
/// that can carry type params is an OPERATION (`add_type_param`'s sites are sort
/// scopes and op scopes), and across stdlib + anthill-stl every one of the 373
/// operations has a `Namespace` (70) or `Sort` (303) parent — none has an operation
/// for a parent, and `fn_sym` here is always an operation, since the caller holds its
/// `OperationInfoFull`. Added anyway: a reader should not owe its correctness to the
/// NEXT gate catching what its own is missing.
pub(super) fn self_receiver_spec_sort(
    kb: &KnowledgeBase,
    op: &OperationInfoFull,
    fn_sym: Symbol,
) -> Option<Symbol> {
    let parent_sym = spec_op_parent_sort(kb, fn_sym)?;
    self_receiver_param_index(kb, &op.params, parent_sym)?;
    Some(parent_sym)
}

/// WI-357 — bind a self-receiver spec op's own type parameters from the
/// concrete receiver carrier, so a dispatched call threads the element
/// type. `Stream.splitFirst(s: Stream) -> Option[T = Pair[A = T, …]]`
/// invoked on `s : List[Int]` unifies the argument against the *bare*
/// `Stream` parameter, which binds none of the spec's own type
/// parameters (`Stream.T`). The unbound `Stream.T` then both (a) leaves
/// the return `Option[T = Pair[A = ?_, …]]` — a destructured `pair(h, _)`
/// gets `h : ?_` — and (b) makes the dispatch goal abstract, so no impl
/// matches and the typer demands a `requires Stream[…]` on the caller.
///
/// Recover the spec params from the carrier's provider fact: `List`
/// provides `fact Stream[T = T]`, so a `List[Int]` viewed as a `Stream`
/// has `Stream.T = List.T = Int`. The element value is read by SHORT NAME
/// from the receiver's own type arguments — robust to whether the
/// provider fact stores the carrier param as a `Var` / `Ref` / nullary
/// `Fn`. Returns true iff at least one spec parameter was bound (the
/// caller then re-walks the return type through the updated subst).
pub(super) fn bind_spec_params_from_carrier(
    kb: &KnowledgeBase,
    subst: &mut Substitution,
    op: &OperationInfoFull,
    spec_sort: Symbol,
    carrier_sym: Symbol,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> bool {
    // The self-receiver argument's inferred type (e.g. `List[T = Int]`).
    let Some(idx) = self_receiver_param_index(kb, &op.params, spec_sort) else {
        return false;
    };
    let param_name = op.params[idx].0;
    // WI-470: read the receiver's inferred type as a carrier-agnostic `Value`, NOT via
    // `.as_term()` — an occurrence-primary `List[T = Int]` is a `Value::Node`, and
    // `.as_term()` would return `None` and drop the carrier (erasing its `T`/`Eff`
    // bindings → a spurious `Eff unconstrained`). The binding is read below through
    // `parameterized_short_bindings` (carrier-agnostic), so it is preserved.
    let recv_ty: Option<Value> = pos_results
        .get(idx)
        .and_then(|r| r.as_ref().ok())
        .map(|r| r.ty.clone())
        .or_else(|| {
            named_args
                .iter()
                .position(|(n, _)| *n == param_name)
                .and_then(|j| named_results.get(j))
                .and_then(|r| r.as_ref().ok())
                .map(|r| r.ty.clone())
        });
    let Some(recv_ty) = recv_ty else {
        return false;
    };

    // The receiver's own type arguments, keyed by the carrier sort's canonical
    // param VarId (WI-600 — the identity key carrier grounding joins on).
    let recv_bindings = parameterized_vid_bindings(kb, &recv_ty, carrier_sym);
    if recv_bindings.is_empty() {
        return false;
    }

    // The carrier's provider fact maps each spec parameter to a carrier-side value
    // (`fact Stream[T = T]` ⇒ spec `T` ↦ carrier `T`). WI-714: TRANSITIVE — a
    // `Relation[T, E]` receiver grounds `Stream`'s params through the chain
    // `Relation provides LogicalStream provides Stream` (no direct fact), so the
    // self-receiver spec-op-on-a-2-hop-carrier case (`takeN`/`find` on a
    // relation) threads `Stream.T ↦ Relation.T`, `Stream.E ↦ Relation.E`.
    let mut visited: SmallVec<[Symbol; 8]> = SmallVec::new();
    let Some(view_bindings) =
        transitive_provider_spec_view_bindings(kb, carrier_sym, spec_sort, &mut visited)
    else {
        return false;
    };

    // WI-393: the CONSUMING op's self-receiver param type maps each spec
    // parameter to the op's OWN type-param var — `collect[Elem, Eff](s: Stream[T =
    // Elem, E = Eff])` gives {T ↦ Elem, E ↦ Eff}. An op rewritten to explicit
    // `[Elem, Eff]` params (042) no longer uses the spec sort's own `Stream.T` /
    // `Stream.E`, so binding only those (below) leaves the op's `Elem` / `Eff` free
    // → element `?_` / `Eff unconstrained` at a cross-sort consumption site. Bind
    // the op's params from the same carrier view. Empty for a bare-`Stream` param
    // (the pre-rewrite ops) — then only the spec sort's params bind, exactly as
    // before. WI-600: keyed by the SPEC sort's canonical param VarId (the op's
    // self-receiver `Stream[T = Elem]` binds the spec's `T`), matched by identity.
    let op_param_map: Vec<(VarId, Value)> = match extract_type(kb, &op.params[idx].1) {
        TypeExtractor::Parameterized { bindings, .. } => bindings
            .into_iter()
            .filter_map(|(p, v)| type_param_vid_in_sort(kb, spec_sort, p).map(|vid| (vid, v)))
            .collect(),
        _ => Vec::new(),
    };

    let mut any = false;
    for (spec_param_sym, carrier_value) in view_bindings {
        let spec_vid = type_param_vid_in_sort(kb, spec_sort, spec_param_sym);
        // WI-600: a type-param REF SHAPE (bare `Ref`/`Ident`/nullary `Fn`/`Var`) —
        // distinct from a written row / compound. The distinction (not "does it
        // resolve to a carrier param") drives the branch: a ref shape that names a
        // NON-carrier-param (a concrete leaf `Int64`) resolves to no VarId, finds
        // no receiver arg, and is skipped — it must NOT fall to the ground-verbatim
        // arm (WI-383 reserves ground value-params to the late pass).
        let ref_shape = typaram_occurrence_sym(kb, carrier_value).is_some();
        // The carrier-side CONCRETE value for this spec parameter, as a ground
        // hash-consed term:
        //  - a type-param ref (`Stream.T` ↦ `List.T`): the receiver's binding for
        //    that carrier param (`List[T = Int]` ⇒ `Int`), looked up by the carrier
        //    sort's canonical param VarId. Threaded even if itself a var (an unbound
        //    receiver element legitimately aliases the op param).
        //  - a GROUND provider row (`Stream.E` ↦ `{}`, the WRITTEN pure row of
        //    `List provides Stream[E = {}]`): the value itself. The pre-WI-393
        //    code `continue`-skipped this (only a ref mapped), dropping the `{}`
        //    so a cross-sort `collect`'s `Eff` never grounded.
        // The `type_value_is_ground` guard on the non-ref arm is load-bearing: a
        // non-ref provider binding that still mentions the carrier's OWN params
        // (`provides Stream[T = Pair[A = C.T, B = C.T]]`) is not ground, and
        // binding it verbatim would pin the op param to a carrier-relative `?_`
        // (the receiver's actual argument is never substituted in) — silently
        // wrong. Skip it: the op param stays unbound and surfaces a LOUD
        // `unconstrained` instead. (Threading such a compound through
        // `recv_bindings` is future work — see WI-380 follow-ups.)
        let concrete: Option<TermId> = if ref_shape {
            typaram_ref_vid(kb, carrier_value, carrier_sym)
                .and_then(|vid| recv_bindings.iter().find(|e| e.0 == vid).map(|e| e.1))
        } else if type_value_is_ground(kb, carrier_value) {
            Some(carrier_value)
        } else {
            None
        };
        let Some(concrete) = concrete else { continue };

        // (a) The spec sort's OWN alias var — kept for the WI-325 abstract-
        //     coverage check on a dispatched body-less op (it resolves the spec
        //     param's alias var in the subst, and the dispatch goal is built from
        //     it). Only a type-param-ref binding (the element); a written effect
        //     row is not bound onto the spec alias (effects aren't expressible
        //     there — WI-301; the coverage check reads the provider view's
        //     groundness directly for that). Only fill a genuinely-empty slot:
        //     `bind_term` flags a CONTRADICTION against a differing existing
        //     binding (it does not rebind), and an alias whose root is bound
        //     resolves anyway.
        if ref_shape {
            if let Some(spec_vid) = spec_vid {
                if subst.resolve_as_value(spec_vid).is_none() && !occurs_in(kb, spec_vid, concrete)
                {
                    subst.bind_term(kb, spec_vid, concrete);
                    any = true;
                }
            }
        }

        // (b) The consuming op's OWN type-param var (WI-393), matched by the SPEC
        //     param's canonical VarId through `op_param_map`. `concrete` is a ground
        //     hash-consed term (the receiver's element, or a ground provider row
        //     like `{}`); bind it occurs-checked into the op's own `Elem` / `Eff`.
        //     Same empty-slot guard as (a).
        if let Some((_, op_param_val)) =
            spec_vid.and_then(|sv| op_param_map.iter().find(|(v, _)| *v == sv))
        {
            if let Some(op_vid) = resolved_var(kb, op_param_val) {
                if subst.resolve_as_value(op_vid).is_none() && !occurs_in(kb, op_vid, concrete) {
                    subst.bind_term(kb, op_vid, concrete);
                    any = true;
                }
            }
        }
    }
    any
}

/// WI-20260828-N2FHM — the parameters of `fn_sym` that could be its CARRIER-PARAM
/// receiver: those declared as one of the enclosing spec sort's own type params
/// (`Iterable.find(c: C, …)`, `sort C = ?` on Iterable), with that param's canonical
/// `VarId`. `None` when `fn_sym` is not a member of a parametric sort at all.
///
/// The first two gates of [`carrier_param_receiver`], lifted out because a SECOND reader
/// needs exactly them and nothing else: [`known_arg_types_and_staged`] decides which
/// arguments to type FIRST, and it must reach that decision before any receiver type
/// exists — which is the one input the rest of `carrier_param_receiver` is about. Sharing
/// the recognizer is what keeps "which parameter is the carrier" a single answer; a
/// staging predicate that drifted from the classification would stage the wrong argument
/// and the hint would go quietly un-grounded again.
pub(super) fn spec_carrier_param_candidates(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    fn_sym: Symbol,
) -> Option<(Symbol, SmallVec<[(usize, Symbol, VarId); 2]>)> {
    let spec_sort = impl_parent_of_op(kb, fn_sym)?;
    Some((spec_sort, spec_param_typed_params(kb, params, spec_sort)?))
}

/// WI-20260923-32XFQ — the operation parameters DECLARED at one of `spec_sort`'s own type
/// parameters (`c: C` in `Iterable.iterator(c: C)`): `(index, name, the parameter's
/// VarId)`, in declaration order; `None` when the spec declares no type parameter at all.
/// The recognizer [`spec_carrier_param_candidates`] (the typer's staging question) and
/// [`carrier_param_receiver_for_values`] (eval's value-directed dual) shared verbatim —
/// sharing it is what keeps "which parameter is the carrier" a single answer.
fn spec_param_typed_params(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    spec_sort: Symbol,
) -> Option<SmallVec<[(usize, Symbol, VarId); 2]>> {
    let spec_params = sort_type_params_as_pairs(kb, spec_sort);
    if spec_params.is_empty() {
        return None;
    }
    let mut out: SmallVec<[(usize, Symbol, VarId); 2]> = SmallVec::new();
    for (i, (pname, pty)) in params.iter().enumerate() {
        let Some(pvid) = declared_type_param_vid(kb, pty) else {
            continue;
        };
        if !spec_params
            .iter()
            .any(|(_, t)| matches!(kb.get_term(*t), Term::Var(Var::Global(v)) if *v == pvid))
        {
            continue;
        }
        out.push((i, *pname, pvid));
    }
    Some(out)
}

/// The INFERRED TYPE of the argument supplied for the parameter at index `i`, named `pname`
/// — positionally, else by its label.
///
/// WI-477: a carrier-agnostic `Value`, never `.as_term()` — an occurrence-primary
/// `List[T = …]` is a `Value::Node` whose `T`/`E` bindings live in the node, and dropping the
/// carrier leaks `Eff unconstrained`. WI-426: a named label binds to its param BY NAME, not
/// by symbol identity.
///
/// ONE OWNER, because two passes in `check_apply_iter` ask it and they must not drift
/// (`/code-review`): [`carrier_param_receiver`] asks WHICH ARGUMENT IS THE RECEIVER, and
/// [`bind_op_type_params_from_op_requires`] asks WHOSE PROVISION GROUNDS THE ELEMENT. A
/// change to how a call's arguments are matched to parameters — a variadic capture, a
/// default, the label rule — applied to one copy and not the other would answer those two
/// with different arguments.
pub(super) fn supplied_arg_type(
    kb: &KnowledgeBase,
    i: usize,
    pname: Symbol,
    pos_results: &[Result<TypeResult, TypeError>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    named_results: &[Result<TypeResult, TypeError>],
) -> Option<Value> {
    pos_results
        .get(i)
        .and_then(|r| r.as_ref().ok())
        .map(|r| r.ty.clone())
        .or_else(|| {
            named_args
                .iter()
                .position(|(n, _)| same_label(kb, *n, pname))
                .and_then(|j| named_results.get(j))
                .and_then(|r| r.as_ref().ok())
                .map(|r| r.ty.clone())
        })
}

/// WI-424 — classify a CARRIER-PARAM receiver: a spec op that takes its carrier
/// through a parameter typed as the spec's own carrier type-param
/// (`Iterable.find(c: C, …)`, `sort C = ?` on Iterable) rather than as the spec
/// sort itself (`Stream.find(s: Stream, …)`). [`self_receiver_param_index`]
/// deliberately skips such params (a type-param-typed param is not a
/// self-receiver for value dispatch), so the WI-357/393 carrier grounding never
/// engages and the spec's OTHER params (`Element`, the written `E` row) stay
/// unbound at a concrete consumption site — `find(xs, pred)` on a `List[Int64]`
/// leaks `?_` for the effect row.
///
/// A param classifies when: its declared type IS one of the spec's own
/// type-param vars; its argument's inferred type names a sort that PROVIDES the
/// spec; and the provision binds THAT spec param to an application of the
/// carrier itself ([`provision_binds_param_to_carrier`] — distinguishing the
/// carrier param from an element-like param). First match wins. Returns
/// `(spec sort, carrier sort, receiver's inferred type, the provision's view
/// bindings, carrier-param vid, transitive?, receiver-arg var-sym)` — the view
/// rides along so the binder does not re-scan the provider facts; the carrier-param
/// vid (WI-593) lets the binder skip the carrier param `C` (bound by argument
/// unification, not the provision); `transitive?` (WI-496) is `true` iff the carrier
/// provides the spec only through a provides-chain (the impl lives on an intermediate
/// spec sort), the bit the dispatch gate reads to defer to eval; and the receiver-arg
/// var-sym (WI-612) is the projection subject for threading an abstract carrier param.
///
/// WI-20260828-N2FHM — the receiver's TYPE arrives through `recv_ty_of`, not off the
/// typed argument results, because this classification now has TWO readers that learn a
/// receiver's type at different moments. `check_apply` reads it from the argument
/// results, as it always did. [`bind_spec_params_for_hint`] runs BEFORE any argument is
/// typed, off the WI-793 `known` map, so a callback param naming a spec param
/// (`Iterable.find`'s `pred: (x: Element) -> Bool`) can be grounded in time to hint the
/// lambda. Everything else about the classification — which parameter is the carrier,
/// which provision view licenses it, whether it is transitive — is ONE decision
/// procedure, deliberately: a second copy keyed on hint-time inputs is exactly the
/// desync the carrier-param path has been repaired for three times (WI-495/608/609).
pub(super) fn carrier_param_receiver(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    fn_sym: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    recv_ty_of: &dyn Fn(usize, Symbol) -> Option<Value>,
) -> Option<(
    Symbol,
    Symbol,
    Value,
    SmallVec<[(Symbol, TermId); 2]>,
    VarId,
    bool,
    Option<Symbol>,
)> {
    let (spec_sort, candidates) = spec_carrier_param_candidates(kb, params, fn_sym)?;
    for (i, pname, pvid) in candidates {
        let Some(recv_ty) = recv_ty_of(i, pname) else {
            continue;
        };
        let Some(carrier_sym) = sort_functor_of_view(kb, &recv_ty) else {
            continue;
        };
        // WI-495: DIRECT provision (the explicit `provides Iterable` hot path) or a
        // view COMPOSED through transitive provision (a `List` carrier whose
        // Iterable-ness rides through `Stream`), so `Element`/`E` still ground.
        let mut visited: SmallVec<[Symbol; 8]> = SmallVec::new();
        let Some((view, transitive)) =
            transitive_provision_view(kb, spec_sort, pvid, carrier_sym, &mut visited)
                // WI-608: the receiver's carrier is ITSELF an abstract spec — a field
                // typed `FiniteCollection[C = SrcC, …]` fed to `Iterable.iterator(c: C)`
                // (spec_sort = Iterable). `FiniteCollection` *requires* Iterable rather
                // than *providing* it, so the `provides`-only scan above finds nothing
                // and the produced `Stream`'s `Element`/`E` would leak `??_`. Build the
                // view from that `requires` relationship instead (same view shape), and
                // mark it `transitive` so the call defers to eval's value-directed
                // dispatch — the carrier-param twin of the WI-598/601 self-receiver
                // abstract-spec deferral (both keyed on `carrier_is_abstract_spec`).
                .or_else(|| {
                    // WI-609: REFLEXIVE — the receiver's carrier IS the op's own spec
                    // (`collect(c: C)` on `c : FiniteCollection`, spec_sort == carrier_sym).
                    // A spec doesn't provide itself, so there is no view to build; the spec's
                    // params are read DIRECTLY off the receiver's type-args in
                    // `bind_spec_params_from_carrier_param`'s reflexive branch. Return an
                    // EMPTY view (marked transitive → defer to eval) to engage that path and
                    // the abstract-spec deferral gate.
                    //
                    // WI-20260831-PYNS2 — ASKED ABOVE [`carrier_is_abstract_spec`], whose
                    // PROVIDER leg this case has already answered. That leg exists to keep a
                    // constructor-less but NON-SPEC sort from being read as an interface
                    // ("none today", says its doc) — and here the carrier IS the sort that
                    // DECLARES the operation being called, so spec-hood is settled by
                    // construction and the census of who implements it says nothing about it.
                    // Under the gate, a spec no carrier provides YET could not read its own
                    // row off the receiver: `ask(s: Spec[E = {Error}], …) = Spec.go(s, …)`
                    // left `Spec.E` unbound and the call incurred `?_`, refused against a
                    // declared row that had eliminated the SAME binding correctly. The
                    // constructor leg is kept: a carrier with a representation of its own is
                    // not an abstract value and must not take the eval deferral.
                    let carrier_canon = kb.canonical_sort_sym(carrier_sym);
                    if carrier_canon == kb.canonical_sort_sym(spec_sort) {
                        // The reflexive arm keeps `carrier_is_abstract_spec`'s OTHER leg
                        // and returns rather than falling through: with carrier == spec the
                        // WI-608 view below asks whether the spec requires ITSELF, so the
                        // fall-through answered `None` for a constructor-bearing carrier
                        // anyway — and asking here keeps `sort_has_constructors`, which
                        // SCANS every qualified name (WI-1027), to one evaluation.
                        return (!kb.sort_has_constructors(carrier_canon))
                            .then(|| (SmallVec::new(), true));
                    }
                    if !carrier_is_abstract_spec(kb, carrier_sym) {
                        return None;
                    }
                    // WI-608: REQUIRES — the carrier `requires` the op's spec.
                    abstract_spec_required_view(kb, spec_sort, carrier_sym).map(|v| (v, true))
                })
        else {
            continue;
        };
        // WI-612: the receiver argument's value-reference symbol (`Iterable.isEmpty(s)`
        // ⇒ `s`), when it is a simple `var_ref` — the subject a path-dependent projection
        // is keyed off. `bind_spec_params_from_carrier_param` uses it to thread an ABSTRACT
        // (unwritten) carrier param as the receiver's own projection `s.<member>` instead
        // of leaking `?_`. `None` for a non-var receiver (a compound expression) → that
        // param stays unbound and surfaces the usual loud `undeclared`/`unconstrained`.
        let recv_arg_sym = pos_args
            .get(i)
            .and_then(extract_var_ref_sym_node)
            .or_else(|| {
                named_args
                    .iter()
                    .find(|(n, _)| same_label(kb, *n, pname))
                    .and_then(|(_, occ)| extract_var_ref_sym_node(occ))
            });
        return Some((
            spec_sort,
            carrier_sym,
            recv_ty,
            view,
            pvid,
            transitive,
            recv_arg_sym,
        ));
    }
    None
}

/// WI-590 — the ENCLOSING SORT's `requires` clause that licenses this spec-op call, with
/// the spec params it supplies ALREADY RESOLVED to the terms to bind (carrier param
/// excluded — that one binds by ordinary argument unification against the receiver).
///
/// The carrier-param path ([`carrier_param_receiver`] → [`bind_spec_params_from_carrier_param`])
/// reads a spec's params off the RECEIVER's carrier: its `provides` fact (WI-424/492), the
/// spec that carrier itself `requires` (WI-608), or its own type-args when carrier and spec
/// coincide (WI-609). All three need a carrier SORT to read from. A receiver typed by an
/// abstract sort PARAMETER has none — inside a sort body the param is rigidified to a
/// Skolem, `sort_functor_of_view` answers `None`, and the parameter is skipped entirely — so
/// every spec param but the carrier leaks `?_`. The information is one level out: the
/// enclosing sort's own `requires Spec[C = P, …]` IS the statement "P provides Spec, with
/// these params". This is the wiring [`carrier_provision_short_bindings`]' doc names as
/// missing ("a free op licensing `c` through an ambient `requires FiniteCollection[C = C2,
/// …]` is NOT handled here … What is missing is the wiring, not the information").
///
/// `Some(vec![])` means LICENSED but with nothing left to bind, and is NOT the same as
/// `None` — the two refusal arms read exactly that distinction.
///
/// STRICTLY ADDITIVE: the caller runs it only where `carrier_param_receiver` already
/// declined, so it can bind only params that would otherwise have leaked and cannot
/// redirect a dispatch that resolves today.
///
/// THREE GATES, each load-bearing for soundness:
///
///  1. THE RECEIVER IS THE CARRIER SLOT. Only the op parameter typed as the spec's own
///     CARRIER param counts. Otherwise any spec-param-typed parameter would do —
///     `Bag.put(other, x)` with `x : Src` would match the clause's `Elem = Src` on parameter
///     1 and license a call nothing licenses. ([`carrier_param_receiver`] gets the same
///     guarantee from `provision_binds_param_to_carrier`, which has no analogue for a
///     `requires` clause.) NO TEST DRIVES THIS ONE, and the reason is worth recording: the
///     wrong licence does not produce a wrong TYPE, because the carrier param is already
///     bound by ordinary argument unification against the receiver and the binder's
///     `resolve_as_value(...).is_none()` guard will not overwrite it — so the declared
///     return is still checked against the real receiver and the program is still refused,
///     one diagnostic later. MEASURED: a fixture built to the shape above passes with this
///     gate and with it backed out to the earlier scan-every-parameter form. The gate stays
///     because granting a licence on a basis that does not hold is a fail-open waiting for
///     its first reader; it is not, today, a wrong answer.
///
///     LIMITATION, stated because it is a real divergence from [`carrier_param_receiver`],
///     which derives the carrier from the PROVISION and so accepts a carrier declared in any
///     position: this reads the carrier as the spec's FIRST type parameter, the convention
///     every stdlib carrier-param spec follows (`sort C = ?` first). A spec that declared its
///     carrier second would simply not be licensed here — fail-CLOSED, a missing licence and
///     the loud diagnostic that goes with it, never a wrong binding. Widening it means
///     deriving the carrier the way that function does, which is a bigger change than the
///     convention has so far been worth.
///
///  2. A VIEW RECEIVER MUST BE A SPEC VIEW. The receiver may be spelled as a view over the
///     param (`src : Iterable[C = S, …]`, what destructuring a spec-typed field yields), and
///     then the carrier is the view's own carrier binding. But `TypeExtractor::Parameterized`
///     matches ANY application, so `xs : Option[T = S]` would otherwise have its first type
///     arg read as a carrier and be licensed as if it were the `S` itself.
///     `carrier_is_abstract_spec` is the separator: a spec has no constructors and has
///     providers, where `Option` has `some`/`none`.
///
///  3. THE CLAUSE MUST BE ABOUT THIS RECEIVER. `requires Spec[C = P]` says nothing about a
///     receiver typed by a DIFFERENT param `Q`, so the clause's own carrier binding is
///     resolved and compared against the receiver's; a mismatch skips the clause rather than
///     borrowing its `Element`/`E`.
///
/// A clause value is resolved as a `Ref`/`Var` naming an enclosing param (to that param's
/// BODY RIGID — a `requires` clause is stored against the pre-rigidify forms while the body
/// references the rigids) or as an already-GROUND type (`requires Eq[T = Int64]`), bound
/// verbatim. Anything else leaves that param unbound and so still LOUD downstream; it does
/// not silently pass, because the licence and the resolution are decided together here
/// rather than in two places that can disagree.
pub(super) fn enclosing_requires_licensing_clause(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    op: &OperationInfoFull,
    fn_sym: Symbol,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> Option<Vec<(VarId, TermId)>> {
    // Cheapest gates first — this runs on every call whose carrier-param classification
    // declined, and most of those are free ops with no enclosing sort at all.
    let encl = env.enclosing_sort()?;
    let rigids = env.enclosing_instance_param_rigids().to_vec();
    if rigids.is_empty() {
        return None;
    }
    let spec_sort = impl_parent_of_op(kb, fn_sym)?;
    let spec_params = sort_type_params_as_pairs(kb, spec_sort);
    let (_, carrier_param_term) = spec_params.first()?;
    let Term::Var(Var::Global(carrier_pvid)) = kb.get_term(*carrier_param_term) else {
        return None;
    };
    let carrier_pvid = *carrier_pvid;
    // A clause value resolved to the enclosing param's BODY RIGID. SYMBOL IDENTITY ONLY,
    // via the sort's own registration — never a short-name join. A clause may write ANOTHER
    // sort's parameters into the slots, and may PERMUTE them (`requires Alg[T = X.S, S = X.T]`);
    // comparing last segments would pair `X.S` with the enclosing `S` and invert exactly that
    // permutation. It matters twice over here: this same resolution decides BOTH whether the
    // clause licenses the call and what each spec param binds to, so one false match would
    // grant a licence and bind a wrong rigid together.
    let encl_params = sort_type_params_as_pairs(kb, encl).to_vec();
    let rigid_of =
        |kb: &KnowledgeBase, t: TermId| -> Option<TermId> {
            let vid =
                match kb.get_term(t) {
                    // SYMBOL IDENTITY, against the enclosing sort's own declared parameters.
                    // NOT `type_param_vid_in_sort`, which resolves a symbol by its LOCAL NAME in
                    // the owner's scope — a name join, and the very hazard this comment claims to
                    // exclude. Identity is what makes the exclusion true rather than asserted.
                    Term::Ref(sym) => encl_params.iter().find(|(p, _)| *p == *sym).and_then(
                        |(_, pty)| match kb.get_term(*pty) {
                            Term::Var(Var::Global(v)) => Some(*v),
                            _ => None,
                        },
                    )?,
                    Term::Var(Var::Global(v)) => *v,
                    _ => return None,
                };
            rigids.iter().find(|(pv, _)| *pv == vid).map(|(_, r)| *r)
        };

    // GATE 1 — the receiver is the parameter typed as the spec's CARRIER param.
    let (i, (pname, _)) = op
        .params
        .iter()
        .enumerate()
        .find(|(_, (_, pty))| declared_type_param_vid(kb, pty) == Some(carrier_pvid))?;
    let recv_ty = pos_results
        .get(i)
        .and_then(|r| r.as_ref().ok())
        .map(|r| r.ty.clone())
        .or_else(|| {
            named_args
                .iter()
                .position(|(n, _)| same_label(kb, *n, *pname))
                .and_then(|j| named_results.get(j))
                .and_then(|r| r.as_ref().ok())
                .map(|r| r.ty.clone())
        })?;
    // GATE 2 — a bare param (a Skolem, no carrier sort), or a SPEC view over one.
    let recv_carrier: TermId = match extract_type(kb, &recv_ty) {
        TypeExtractor::Parameterized { base, bindings } => {
            if !carrier_is_abstract_spec(kb, base) {
                return None;
            }
            let params = sort_type_params_as_pairs(kb, base);
            let (view_carrier_psym, _) = params.first()?;
            match bindings
                .iter()
                .find(|(k, _)| same_label(kb, *k, *view_carrier_psym))
                .map(|(_, v)| v)
            {
                Some(Value::Term { id, .. }) => *id,
                _ => return None,
            }
        }
        _ => match &recv_ty {
            Value::Term { id, .. } => *id,
            _ => return None,
        },
    };

    for entry in direct_requires(kb, encl) {
        if kb.canonical_sort_sym(entry.required_sort) != kb.canonical_sort_sym(spec_sort) {
            continue;
        }
        let Some((_base, bindings)) = unwrap_spec_view_value(kb, &entry.spec) else {
            continue;
        };
        // GATE 3 — this clause is about THIS receiver.
        let licenses = bindings.iter().any(|(p, t)| {
            type_param_vid_in_sort(kb, spec_sort, *p) == Some(carrier_pvid)
                && rigid_of(kb, *t) == Some(recv_carrier)
        });
        if !licenses {
            continue;
        }
        let mut out: Vec<(VarId, TermId)> = Vec::new();
        for (p, t) in &bindings {
            let Some(spec_vid) = type_param_vid_in_sort(kb, spec_sort, *p) else {
                continue;
            };
            if spec_vid == carrier_pvid {
                continue;
            }
            if let Some(r) = rigid_of(kb, *t).or_else(|| type_value_is_ground(kb, *t).then_some(*t))
            {
                out.push((spec_vid, r));
            }
        }
        return Some(out);
    }
    None
}

/// WI-20260918-R541X (A) / WI-20260919-H20YY — THE SOLE `requires` ENTRY OVER `spec` in
/// the enclosing scope's COMPOSED chain (its sort's slots, then its operation's), or
/// `None` when the chain holds none — or MORE THAN ONE.
///
/// "More than one" is a REFUSAL and not a tie-break, and it is the whole reason this is
/// one function rather than four lines at each site. Nothing picks between
/// `requires TypeTerm[T = P], TypeTerm[T = Q]` at a call that names neither, so taking
/// the first written would make the answer depend on the ORDER two clauses appear in —
/// the silent route-order choice WI-1010's family of refusals exists to prevent.
/// [`carrier_from_declared_slot`] states the same rule for its own half ("TWO SLOTS THAT
/// DISAGREE PIN NOTHING") and `wi_nr6fj_defect_b_slot_over_default_test::
/// two_slots_that_disagree_pin_nothing` is the row holding it, since no corpus program
/// writes two such slots.
///
/// THE TWO ASKERS want opposite things from the same answer and must not diverge about
/// what "sole" means: [`bind_sort_params_from_sole_enclosing_requirement`] BINDS from the
/// entry, and [`defer_defaulted_call_to_slot`] uses its existence as the licence to hand
/// the call to that slot. Were the second looser than the first, a call could be
/// dispatched through a clause the typer had refused to read bindings from.
///
/// DIRECT ENTRIES ONLY, stated because the deferral's own routes search wider: both
/// [`find_requires_location`] and [`op_scoped_defer_location`] walk the requires TREE and
/// can locate a spec nested inside a direct requirement. A transitively-required spec has
/// no direct entry here, so this answers `None` and the deferral declines — conservative,
/// and deliberately so: counting only what the author wrote is what makes "more than one"
/// a statement about the PROGRAM rather than about how deep a walk happened to go.
///
/// ONE RESIDUAL DIVERGENCE, NAMED RATHER THAN LEFT SILENT. The count is over the WHOLE
/// composed chain, so a spec required at BOTH the enclosing sort and the enclosing
/// operation reads as two and the deferral declines. For a BODY-LESS op the same program
/// resolves: the body-less block tries the sort half first and its op half is only the
/// fallback ([`defer_to_op_scoped_slot`]'s ORDER note), so the sort's clause wins rather
/// than refusing. Counting per half would match that precedence and still hold both
/// refusals above — NOT DONE, because no fixture in the corpus writes that shape, and a
/// gate split on a case nothing drives would pin a claim this ticket cannot measure. The
/// cost of the conservative reading is a defaulted call falling back to its default where
/// a body-less one dispatches; the cost of guessing wrong would be a silent wrong answer,
/// which is the trade this whole family of refusals already makes.
pub(super) fn sole_chain_entry_over_spec(
    kb: &KnowledgeBase,
    chain: &DictChain,
    spec: Symbol,
) -> Option<RequiresEntry> {
    let spec_canon = kb.canonical_sort_sym(spec);
    let mut over_spec = chain
        .entries()
        .iter()
        .filter(|e| kb.canonical_sort_sym(e.required_sort) == spec_canon);
    let entry = over_spec.next().cloned()?;
    over_spec.next().is_none().then_some(entry)
}

/// WI-20260918-R541X (A) — bind a callee's STILL-FREE sort parameters from the ONE
/// clause of the enclosing scope (its sort's `requires`, then its operation's) that
/// requires the callee's own sort.
///
/// `operation tagOf[P](x: P) -> Type requires TypeTerm[T = P] = TypeTerm.valueOf()`: the
/// call `TypeTerm.valueOf()` has no argument and a `Type` return, so nothing at the call
/// pins `TypeTerm.T` — yet the scope says, in its own `requires`, which `TypeTerm` it is
/// running under. MEASURED before this: the channel write skipped the free var and the
/// spec's default body read of `T` answered `T` (and, since (D), is refused). WI-590's
/// [`enclosing_requires_licensing_clause`] reads the same clauses but is licensed by a
/// RECEIVER typed at the spec's carrier, and reads the SORT half only — a receiver-less
/// member and an operation-level `requires` both miss it.
///
/// THREE REFUSALS, each leaving the var free (and so loud downstream rather than guessed):
///   * TWO clauses over the callee's sort. No rule picks between `requires TypeTerm[T = P],
///     TypeTerm[T = Q]`, so neither is taken.
///   * a call that pinned ANY of the sort's parameters — an argument, a bracket,
///     `expected`, the WI-424 same-sort seeding. Such a call names an instance of its own,
///     which the clause need not be about (see the site for the measured case).
///   * a clause value that is neither an enclosing parameter (resolved to its BODY RIGID —
///     a clause is stored against the declared symbols, the body sees the rigids) nor a
///     ground type. Same resolution as WI-590's, by symbol identity.
pub(super) fn bind_sort_params_from_sole_enclosing_requirement(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    env: &TypingEnv,
    callee_parent_sort: Option<Symbol>,
) {
    let Some(spec) = callee_parent_sort else {
        return;
    };
    let chain = env.enclosing_frame_chain();
    if chain.entries().is_empty() {
        return;
    }
    let Some(entry) = sole_chain_entry_over_spec(kb, chain, spec) else {
        return;
    };
    // THE CALL MUST SAY NOTHING ABOUT WHICH INSTANCE. One pinned parameter means the call
    // names an instance of its own, and the clause may be about a different one:
    // `FiniteCollection.collect(rest)` over a `rest : Mapped[…]` inside a sort that
    // `requires FiniteCollection[C = S, …]` — MEASURED (wi606), borrowing the clause's
    // `Element`/`E` there bound them to the wrong carrier's. WI-590 answers the same
    // hazard with a receiver comparison (its GATE 3); a receiver-less call has nothing to
    // compare, so the only safe licence is that nothing was pinned at all.
    let param_vids: Vec<VarId> = sort_type_params_as_pairs(kb, spec)
        .iter()
        .filter_map(|(_, t)| match kb.get_term(*t) {
            Term::Var(Var::Global(v)) => Some(*v),
            _ => None,
        })
        .collect();
    if param_vids
        .iter()
        .any(|v| subst.resolve_as_value(*v).is_some())
    {
        return;
    }
    let Some((_, bindings)) = unwrap_spec_view_value(kb, &entry.spec) else {
        return;
    };
    for (p, t) in bindings {
        let Some(spec_vid) = type_param_vid_in_sort(kb, spec, p) else {
            continue;
        };
        let value = match clause_named_type_param(kb, t) {
            Some(v) => env
                .param_rigids()
                .iter()
                .find(|(pv, _)| *pv == v)
                .map(|(_, r)| *r),
            None => type_value_is_ground(kb, t).then_some(t),
        };
        if let Some(value) = value.filter(|v| !occurs_in(kb, spec_vid, *v)) {
            subst.bind_term(kb, spec_vid, value);
        }
    }
}

/// WI-590 — bind what [`enclosing_requires_licensing_clause`] resolved. Split from the
/// finder only so the LICENCE and the BINDING cannot disagree: both read one clause,
/// resolved once.
pub(super) fn bind_spec_params_from_enclosing_requires(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    clause: Option<&[(VarId, TermId)]>,
) -> bool {
    let mut any = false;
    for (spec_vid, concrete) in clause.unwrap_or(&[]) {
        if subst.resolve_as_value(*spec_vid).is_none() && !occurs_in(kb, *spec_vid, *concrete) {
            subst.bind_term(kb, *spec_vid, *concrete);
            any = true;
        }
    }
    any
}

/// WI-20260829-70XVH — the TYPE PARAMETER a `requires` clause value NAMES, of EITHER scope.
/// `None` for anything that is not one — a concrete leaf, a compound, an anonymous `?`.
///
/// The two value shapes are the ones [`enclosing_requires_provision_bindings`]' own
/// `clause_param_vid` reads, and for the same reason: a clause names a parameter as a `Ref`
/// to its symbol, and a row TAIL arrives as the bare canonical `Var::Global`.
pub(super) fn clause_named_type_param(kb: &KnowledgeBase, t: TermId) -> Option<VarId> {
    match kb.get_term(t) {
        Term::Ref(sym) | Term::Ident(sym) => type_param_global_var(kb, *sym),
        Term::Var(Var::Global(v)) => Some(*v),
        _ => None,
    }
}

/// The same, narrowed to the operation's OWN parameters — the ones a CALL may bind. An
/// enclosing SORT's parameter belongs to the sort INSTANCE and not to this call, so it may
/// be READ (as the clause's carrier, below) but never WRITTEN.
///
/// `own` is the CLASSIFICATION's own list ([`OperationInfoFull::type_params`]), not a
/// name-scoped test: §5.3 says a clause names parameters of two scopes in ONE list, and only
/// membership here separates them.
fn clause_named_op_type_param(kb: &KnowledgeBase, t: TermId, own: &[VarId]) -> Option<VarId> {
    clause_named_type_param(kb, t).filter(|v| own.contains(v))
}

/// WI-20260829-70XVH — ground the CALLEE's OWN type parameters from the CALLEE's op-level
/// `requires`, at a call that pinned the clause's carrier.
///
/// `gmap[Sc, S, Dst, EffS, EffP](s: Sc, f: (x: S) -> Dst @ …) requires Walk[C = Sc,
/// Element = S, E = EffS]` is the general free combinator — it takes ANY carrier that walks,
/// and the clause says which element and which access effect that walk has. Called as
/// `gmap(xs, f)` over a `List[T = Int64]` only `Sc` is determined by an argument: `S` and
/// `EffS` appear nowhere a value flows through, so the call is refused `type parameter 'S'
/// is unconstrained` and the author must write a bracket that repeats what the source
/// already says. The clause IS the determination — `List provides Walk[Element = T, E = {}]`
/// at `T = Int64` says `S = Int64` and `EffS = {}`.
///
/// It is the CALL-SITE twin of [`op_requires_provision_bindings`], which reads the same
/// clause in the operation's own BODY to type a construction, and it reads the provision
/// exactly the way [`carrier_param_receiver`] does — [`transitive_provision_view`], then the
/// receiver's own type-args — because the question is the same one: what does THIS carrier
/// bind that spec's parameters to. What differs is only WHICH variables the answer lands on.
/// The carrier-param path binds the SPEC's parameters, because there the spec op's signature
/// is written in them; here the spec is named by a clause, and the clause says which of the
/// OPERATION's parameters each spec parameter is.
///
/// RETURNS NOTHING, unlike every `bind_spec_params_from_*` sibling: their booleans gate the
/// WI-357 effect-close and the `expected` seeding, and nothing downstream is gated on whether
/// a clause supplied anything here — the parameters it leaves free reach
/// [`check_unconstrained_type_params`] exactly as they did before.
///
/// FOUR THINGS IT WILL NOT DO, each leaving the loud `unconstrained` rather than a guess:
///   * bind a parameter the call already pinned. A written bracket ([`seed_op_type_args`],
///     which runs above) outranks a clause, and so does the WI-424 same-sort rigid seeding;
///     this sits beside the WI-367/424 carrier grounding, above the `expected` seeding, for
///     the reason WI-367 states — a caller's return claim is not evidence about the carrier.
///     The skip is NOT INDEPENDENTLY DRIVABLE and says so here rather than claiming a
///     measurement it does not have: [`Substitution::bind_term`] already refuses to overwrite
///     an existing binding, so removing the skip changes the outcome from "leave the author's
///     value" to "mark the call's substitution CONTRADICTORY", and nothing on today's surface
///     reads that flag differently — measured, the whole row set stays green either way. It
///     is kept because those two are different behaviours and only one of them is additive.
///   * bind anything but one of the OPERATION's own type parameters
///     ([`clause_named_op_type_param`]).
///   * bind the CARRIER parameter itself: ordinary argument unification against the receiver
///     binds it, and the provision's value for it is the carrier APPLICATION — the artifact
///     [`compose_provision_views`] documents, which would pin `Sc` to the intermediate sort.
///   * bind a value the receiver does not fully determine. A provision binding still
///     carrier-relative after the receiver's type-args are substituted in (an unwritten row,
///     a witness template) is not an answer this reader has; [`bind_spec_params_from_carrier_param`]
///     recovers some of those for the SPEC's own parameters and none of that is reused here,
///     deliberately — a projection `s.E` is a path this call's parameter has no name for.
///
/// The carrier parameter is the spec's FIRST type parameter — the same convention, and the
/// same fail-CLOSED limitation, that [`enclosing_requires_licensing_clause`] gate 1 and
/// [`enclosing_requires_provision_bindings`] state. A spec that declares its carrier second
/// makes this whole pass decline and the author sees the ordinary `unconstrained`.
///
/// A CARRIER WITH TWO WITNESSES THAT DISAGREE IS **NOT** REFUSED HERE, and that was measured
/// before it was decided. [`transitive_provision_view`] takes the FIRST provision at the
/// carrier, so with `First provides Pair[E = Tag, F = Int64]` beside `Second provides
/// Pair[E = Tag, F = Tag]` this binds `F := Int64`. WI-1091 states the opposite rule —
/// "neither may be picked for the author" — but about the HOST-ENTRY dictionary completion,
/// a channel with no static receiver type to read. The typer's read of the same pair already
/// picks: MEASURED on the delivered tree with this pass neutralized, the spec-op call
/// `Pair.combine(t)` grounds its `F` to `Int64` and REFUSES a `-> Tag` return, through
/// [`bind_spec_params_from_carrier_param`]. Adding a stricter rule HERE would make two
/// readers of one question — "what does this carrier bind this spec's parameters to" —
/// disagree by which declaration named the spec. Coherence at a carrier is that other
/// reader's to settle, for both of them.
pub(super) fn bind_op_type_params_from_op_requires(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    op: &OperationInfoFull,
    fn_sym: Symbol,
    arg_tys: &[Option<Value>],
) {
    let own: Vec<VarId> = op
        .type_params
        .iter()
        .filter_map(|(_, v)| match v {
            Var::Global(g) => Some(*g),
            _ => None,
        })
        .collect();
    if own.is_empty() {
        return;
    }
    // The RAW entries, the shape [`op_requires_entry_carrier_map`] decodes — not
    // `op_requires_chain_rc`, whose `SortView`-normalized spec that decoder would read
    // positionally against the spec's own parameters. Value preconditions are filtered for
    // the reason `op_requires_chain_rc` states: one keyword writes two things, and only a
    // SPEC requirement can say a carrier provides anything.
    for entry in op_requires_entries(kb, fn_sym) {
        if is_value_precondition_clause(kb, &entry.spec) {
            continue;
        }
        let spec = entry.required_sort;
        let spec_params = sort_type_params_as_pairs(kb, spec).to_vec();
        let Some((carrier_param, _)) = spec_params.first() else {
            continue;
        };
        let Some(carrier_pvid) = type_param_vid_in_sort(kb, spec, *carrier_param) else {
            continue;
        };
        let clause = op_requires_entry_carrier_map(kb, &entry);
        // Clause binding ↦ the spec parameter it is FOR, by VarId identity (the clause's
        // keys and the spec's declared parameters are resolved in two scopes).
        let clause_value = |kb: &KnowledgeBase, want: VarId| -> Option<TermId> {
            clause
                .iter()
                .find(|(p, _)| type_param_vid_in_sort(kb, spec, *p) == Some(want))
                .map(|(_, v)| *v)
        };
        // READ EITHER SCOPE, WRITE ONLY THE OPERATION'S — the asymmetry §5.3's "one list"
        // makes, and getting it wrong here is silent. The CARRIER only has to say WHICH
        // ARGUMENT the clause is about, and an operation on a parametric sort routinely
        // takes it through its sort's parameter (`each[El](x: C) … requires Iterable[C = C,
        // Element = El]`); requiring the carrier to be the operation's own made that whole
        // clause unreadable and left `El` unconstrained, with nothing saying why. The TARGET
        // is a different question and keeps the narrow test: a sort parameter is the sort
        // INSTANCE's, not this call's. Found by `/code-review`; driven by
        // `a_clause_whose_carrier_is_the_enclosing_sorts_parameter_still_grounds`.
        let Some(carrier_tp) =
            clause_value(kb, carrier_pvid).and_then(|t| clause_named_type_param(kb, t))
        else {
            continue;
        };
        // The ARGUMENT that carries it — the parameter whose DECLARED TYPE is that
        // parameter, the same recognizer [`spec_carrier_param_candidates`] uses one scope
        // over. An operation may take the carrier in any position, so this is a search and
        // not an index.
        let Some(recv_ty) = op.params.iter().enumerate().find_map(|(i, (_, pty))| {
            (declared_type_param_vid(kb, pty) == Some(carrier_tp))
                .then(|| arg_tys.get(i).cloned().flatten())
                .flatten()
        }) else {
            continue;
        };
        let Some(carrier_sym) = sort_functor_of_view(kb, &recv_ty) else {
            continue;
        };
        let mut visited: SmallVec<[Symbol; 8]> = SmallVec::new();
        let Some((view, _transitive)) =
            transitive_provision_view(kb, spec, carrier_pvid, carrier_sym, &mut visited)
        else {
            continue;
        };
        let recv_bindings = parameterized_vid_bindings(kb, &recv_ty, carrier_sym);
        for (spec_param, carrier_value) in view {
            let Some(pvid) = type_param_vid_in_sort(kb, spec, spec_param) else {
                continue;
            };
            if pvid == carrier_pvid {
                continue;
            }
            let Some(target) =
                clause_value(kb, pvid).and_then(|t| clause_named_op_type_param(kb, t, &own))
            else {
                continue;
            };
            if subst.resolve_as_value(target).is_some() {
                continue;
            }
            let grounded =
                substitute_carrier_params(kb, carrier_value, carrier_sym, &recv_bindings);
            if !type_value_is_ground(kb, grounded) || occurs_in(kb, target, grounded) {
                continue;
            }
            subst.bind_term(kb, target, grounded);
        }
    }
}

/// WI-424 — ground a spec's sort params from the carrier's provision for a
/// CARRIER-PARAM receiver call (`find(xs, pred)` on a `List[Int64]` via
/// `provides Iterable[C = List[T], Element = T, E = {}]`): a provision binding
/// that is a carrier-param REF reads the receiver's own type-arg
/// (`Element ↦ T ↦ Int64`); a GROUND binding (the written `{}` row) binds
/// verbatim. Unlike [`bind_spec_params_from_carrier`] part (a), a ground row
/// DOES bind onto the spec's own param var here: for the carrier-param shape
/// the spec's `E` IS the op's declared effect row (`find … effects E`), and
/// leaving it unbound is exactly the `?_` leak this closes. A non-ground
/// non-ref binding (the carrier application `C ↦ List[T]` itself, or a
/// compound still mentioning carrier params) is skipped — `C` binds from
/// ordinary argument unification.
pub(super) fn bind_spec_params_from_carrier_param(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    spec_sort: Symbol,
    carrier_sym: Symbol,
    carrier_pvid: VarId,
    recv_ty: &Value,
    view_bindings: SmallVec<[(Symbol, TermId); 2]>,
    recv_arg_sym: Option<Symbol>,
) -> bool {
    let recv_bindings = parameterized_vid_bindings(kb, recv_ty, carrier_sym);
    // WI-609: REFLEXIVE — the receiver's carrier IS the op's own spec (`collect(c: C)`
    // on `c : FiniteCollection`, spec_sort == carrier_sym == FiniteCollection). A spec
    // doesn't provide itself, so `carrier_param_receiver` hands an EMPTY view here; the
    // receiver's own written type-args ARE the spec's params (same canonical VarIds,
    // since `parameterized_vid_bindings` is keyed by `carrier_sym == spec_sort`), so bind
    // each DIRECTLY — there is no provider view to indirect through. `collect(src)` on
    // `src : FiniteCollection[E = ES]` grounds `FiniteCollection.E ↦ ES`, threading the
    // declared `effects E` to the receiver's own `ES`. The carrier param `C` is skipped
    // (bound by ordinary argument unification against the receiver), matching the loop
    // below.
    if kb.canonical_sort_sym(carrier_sym) == kb.canonical_sort_sym(spec_sort) {
        let mut any = false;
        for (vid, value) in &recv_bindings {
            if *vid == carrier_pvid {
                continue;
            }
            if subst.resolve_as_value(*vid).is_none() && !occurs_in(kb, *vid, *value) {
                subst.bind_term(kb, *vid, *value);
                any = true;
            }
        }
        return any;
    }
    // WI-20260828-57MRM — a WITNESS provision's head is a TEMPLATE over the witness sort's
    // own binder, so INSTANTIATE it against the receiver before reading any binding. Empty
    // for an ordinary `provides` (bare carrier reference, nothing to instantiate), so the
    // non-witness path is unchanged.
    let instantiation = witness_instantiation(
        kb,
        spec_sort,
        carrier_sym,
        carrier_pvid,
        &view_bindings,
        &recv_bindings,
    );
    let mut any = false;
    for (spec_param_sym, carrier_value) in view_bindings {
        let spec_vid = type_param_vid_in_sort(kb, spec_sort, spec_param_sym);
        // (the carrier-param skip below runs BEFORE any instantiation: for a witness that
        // binding is the largest term in the head, and rewriting it would hash-cons a copy
        // that is discarded on the very next line.)
        // The CARRIER param itself (`FiniteCollection.C`) is bound by ordinary
        // argument unification against the receiver, NOT from the provision: its
        // provider binding is the carrier-sort application (`C ↦ Map`, or the
        // transitive `C ↦ SortView[T = T]` for a List), and grounding+binding that
        // would pin `C` to the wrong sort and conflict with the receiver arg. Skip
        // it. (Pre-WI-593 a non-ground, non-ref `C` binding fell through the `None`
        // arm; the explicit skip preserves that intent now that the WI-593 compound
        // arm below would otherwise ground it.)
        if spec_vid == Some(carrier_pvid) {
            continue;
        }
        // WI-20260828-57MRM — INSTANTIATE the witness's head binding against the receiver.
        //
        // The result is the receiver's own type-arg, so it must NOT then be run through the
        // carrier-keyed classification below: that asks `typaram_ref_vid(value, carrier_sym)`,
        // and a rewritten `Int64` is ref-shaped but is not a param OF THE CARRIER, so it
        // would answer `None` and the binding would be DROPPED. MEASURED — a `String` was
        // accepted where the witness pins `Element = Int64`, which the un-instantiated read
        // had refused. A rewritten value that is GROUND is already the answer; bind it.
        let carrier_value = match &instantiation {
            Some((witness_params, wsubst)) => {
                let rewritten =
                    apply_witness_instantiation(kb, carrier_value, witness_params, wsubst);
                if rewritten != carrier_value && type_value_is_ground(kb, rewritten) {
                    if let Some(spec_vid) = spec_vid {
                        if subst.resolve_as_value(spec_vid).is_none()
                            && !occurs_in(kb, spec_vid, rewritten)
                        {
                            subst.bind_term(kb, spec_vid, rewritten);
                            any = true;
                        }
                    }
                    continue;
                }
                rewritten
            }
            None => carrier_value,
        };
        // WI-600: match the carrier-side value's type-param leaves by the CARRIER
        // sort's canonical `Var::Global` VarId (identity), not short name. The
        // ref-SHAPE gate (not "resolves to a carrier param") drives the branch: a
        // ref shape naming a concrete leaf (`Int64`) resolves to no VarId, finds no
        // receiver arg, and is skipped — it must NOT fall to the ground-verbatim arm
        // (WI-383 reserves ground value-params to the late pass).
        let concrete: Option<TermId> = if typaram_occurrence_sym(kb, carrier_value).is_some() {
            // A ref SHAPE (`Element ↦ T`, `E ↦ Stream.E`, or a concrete leaf `Int64`).
            match typaram_ref_vid(kb, carrier_value, carrier_sym) {
                // A genuine carrier param (`Stream.T` / `Stream.E`): read the receiver's
                // written type-arg.
                Some(vid) => recv_bindings
                    .iter()
                    .find(|e| e.0 == vid)
                    .map(|e| e.1)
                    // WI-612: the receiver left this carrier param ABSTRACT (unwritten —
                    // `s : Stream[T = Int64]` writes no `E`), so there is no type-arg to
                    // read and the param would leak `?_`. For an EFFECT-ROW param (the only
                    // one with no other binder — `sort_param_is_effect_row`) whose receiver
                    // is a stable value reference, that param's value IS the receiver's own
                    // projection `s.<member>` (path-dependent: `s`'s abstract `Stream.E`,
                    // viewed from outside, is definitionally `s.E`). Bind it to that
                    // projection — built exactly as the WI-459 call-site re-key does
                    // (`ExprCarried{Ref(arg), member}`) — so an abstract access row
                    // `Iterable.E` threads as `s.E` and matches a declared `effects s.E`.
                    // A non-var receiver (`recv_arg_sym` None) or a non-effect param stays
                    // unbound and surfaces the usual loud `undeclared`/`unconstrained`.
                    .or_else(|| {
                        let arg_sym = recv_arg_sym?;
                        let param_sym = typaram_occurrence_sym(kb, carrier_value)?;
                        let member_name = short_name_of(kb.local_name_of(param_sym)).to_owned();
                        // Positively verify the row is UNWRITTEN on the receiver, not merely
                        // absent from the Term-only `recv_bindings`: a WRITTEN Node-carried
                        // row (`Stream[E = {Modify[x]}]`) is dropped by
                        // `parameterized_vid_bindings` (its `_ => None` arm), so reading only
                        // `recv_bindings` would synthesize a spurious `s.E` over an
                        // already-written row. `extract_type_param` is Node-inclusive, so a
                        // written row (any carrier) skips the projection — the row is read /
                        // grounded by the ordinary path instead.
                        if extract_type_param(kb, recv_ty, &member_name).is_some()
                            || !sort_param_is_effect_row(kb, carrier_sym, &member_name)
                        {
                            return None;
                        }
                        let member = kb.intern(&member_name);
                        let recv_term = kb.alloc(Term::Ref(arg_sym));
                        Some(kb.make_expr_carried(recv_term, member))
                    }),
                // A ref-shaped CONCRETE leaf (`Int64`) that is not one of the carrier's
                // params: skip here — WI-383 reserves ground value-params to the late pass.
                None => None,
            }
        } else if type_value_is_ground(kb, carrier_value) {
            // A ground provider value (the written `{}` row): bind verbatim.
            Some(carrier_value)
        } else {
            // WI-593: a COMPOUND provider binding still mentioning the carrier's own
            // params (`Map provides FiniteCollection[Element = Pair[A = K, B = V]]`).
            // Substitute the receiver's type-args (`K ↦ Int64, V ↦ Int64`) into it and
            // bind only if that grounds it FULLY; a carrier param left unresolved means
            // the receiver did not pin it, so skip (the spec param stays unbound → a
            // LOUD `unconstrained`, never a silently-wrong carrier-relative `?_`).
            let grounded =
                substitute_carrier_params(kb, carrier_value, carrier_sym, &recv_bindings);
            type_value_is_ground(kb, grounded).then_some(grounded)
        };
        let Some(concrete) = concrete else { continue };
        if let Some(spec_vid) = spec_vid {
            if subst.resolve_as_value(spec_vid).is_none() && !occurs_in(kb, spec_vid, concrete) {
                subst.bind_term(kb, spec_vid, concrete);
                any = true;
            }
        }
    }
    any
}

/// WI-593 — substitute a carrier's receiver-side type-args into a COMPOUND
/// provider-view binding, producing the PLAIN type term the rest of the typer
/// compares against. A provision can map a spec parameter to a term that still
/// mentions the carrier's OWN params (`Map provides FiniteCollection[Element =
/// Pair[A = K, B = V]]`); to ground `Element` at a concrete `Map[K = Int64, V =
/// Int64]` call, each carrier-param leaf (`K` / `V`) is replaced by the receiver's
/// type-arg. WI-600: leaves are matched by the carrier sort's canonical
/// `Var::Global` VarId (identity via [`typaram_ref_vid`]), not by short name, and
/// `recv_bindings` is keyed by that same VarId. A leaf absent from `recv_bindings`
/// is left intact, so the caller's groundness check rejects a partially-
/// substituted result rather than binding a carrier-relative var.
///
/// WI-600: the provider fact now stores a compound binding as the PLAIN
/// parameterized term `Fn{Pair, A = K, B = V}` (the loader no longer wraps a nested
/// binding value in a `reflect.SortView`; see `sort_binding_to_value`). A ground
/// provider spec view carries only ground `TermId` bindings (a denoted-bearing
/// spec rides as a `Value::Entity` value fact, which `provider_spec_view_bindings`
/// skips), so a compound reaching here is always this plain `Fn` — the generic-Fn
/// recursion below handles it with no `SortView` unwrap / rebuild.
pub(super) fn substitute_carrier_params(
    kb: &mut KnowledgeBase,
    tid: TermId,
    carrier_sym: Symbol,
    recv_bindings: &[(VarId, TermId)],
) -> TermId {
    rewrite_term_leaves(kb, tid, &|kb, t| {
        carrier_param_leaf_binding(kb, t, carrier_sym, recv_bindings)
    })
}

/// [`substitute_carrier_params`]' leaf set: the receiver's type-arg for a carrier-parameter
/// occurrence, in either of its two spellings; `None` for anything else, which the walk
/// descends ([`rewrite_term_leaves`]) — any other compound keeps its functor.
fn carrier_param_leaf_binding(
    kb: &KnowledgeBase,
    tid: TermId,
    carrier_sym: Symbol,
    recv_bindings: &[(VarId, TermId)],
) -> Option<TermId> {
    // (1) A carrier-param leaf (`K`) → the receiver's type-arg, keyed by the
    //     carrier sort's canonical param VarId.
    if let Some(vid) = typaram_ref_vid(kb, tid, carrier_sym) {
        if let Some((_, bound)) = recv_bindings.iter().find(|e| e.0 == vid) {
            return Some(*bound);
        }
    }
    // (1b) WI-590 — the same leaf in its OTHER SPELLING. A carrier parameter is a
    //      `Ref(symbol)` in a type-argument slot but the bare `Var(Global(vid))` a row TAIL
    //      carries (`{ES}` lowers to `open[tail = Var]`, the tail anonymous — its name is
    //      `_`). `typaram_ref_vid` reads only the first, so a row-valued provision binding
    //      walked to its leaves and substituted NOTHING, stayed non-ground, and the spec's
    //      row leaked `?_`.
    //
    //      No name is involved here and none should be: `recv_bindings` is keyed by the
    //      carrier's own param VarIds and VarIds are unique, so matching the tail's vid
    //      against them is exact.
    //
    //      MEASURED on a two-hop provision (`Wrap provides Str`, `Str provides Iter`, call
    //      `Iter.iter(w)`): composition already produced the right thing — the view's
    //      `Element` came out as `Wrap.T` and the row's tails as Wrap's OWN param vars — and
    //      only this read was missing. It went unnoticed while every route to such a call
    //      arrived with the intermediate's static type, which is a ONE-hop provision whose
    //      binding is a plain `Ref`.
    match kb.get_term(tid) {
        Term::Var(Var::Global(v)) => recv_bindings.iter().find(|e| e.0 == *v).map(|e| e.1),
        _ => None,
    }
}

/// WI-383 B — the LATE, GROUND-valued companion to [`bind_spec_params_from_carrier_param`].
/// Binds a spec value-param that is STILL FREE after the argument loops to its GROUND
/// provider-fact value (`fact Box[T = IntCell, V = Int64]` ⟹ `Box.V := Int64`). This is the
/// entity-resource Modify tie: `ModifyRuntime.get(target: T) -> V` consumed on a resource
/// whose provider fact pins `V` to a concrete sort. `V` appears only in the RETURN, so no
/// argument ever threads it; left free, the value-untied return is filled from the caller's
/// `expected`, accepting ANY declared return (the soundness hole the Modify model names).
///
/// Why it is a SEPARATE late pass, not folded into the early
/// [`bind_spec_params_from_carrier_param`]:
///  - a leaf sort ref (`Int64`) is ref-SHAPED like a type-param ref
///    ([`typaram_occurrence_sym`] `Some`), so it takes the receiver-type-arg lookup path and
///    misses (it resolves to no carrier-param VarId, and a bare entity carrier has no type
///    args) — never reaching that fn's ground arm;
///  - binding such a ground value EARLY (before the argument loops) pre-empts the WI-424/441
///    carrier threading — an Iterable's GROUND `Element` would bind before the predicate's
///    effect row threads, leaving the effect param unconstrained.
///
/// The STILL-FREE gate is the discriminator: a param an argument pinned (Iterable's
/// `Element` via the callback, the carrier param via the receiver arg) is bound by now and
/// skipped; only a never-threaded return-only value-param (`V`) is free. WI-391: the
/// provider binding is the canonical `Ref(S)` shape (a bare sort lowers to `Ref(S)` at the
/// producer, `sort_binding_to_value`), so the bound `Ref(Int64)` unifies with the declared
/// return's `Ref(Int64)` directly — no late leaf normalization.
pub(super) fn bind_ground_value_params_from_provider(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    spec_sort: Symbol,
    view_bindings: &SmallVec<[(Symbol, TermId); 2]>,
) -> bool {
    let mut any = false;
    for (spec_param_sym, carrier_value) in view_bindings {
        // GROUND value only (a concrete sort `Int64`): a type-param ref (`V ↦ Cell.V`) is
        // threaded by the early `bind_spec_params_from_carrier_param`, and the carrier
        // application / a still-abstract binding is filled by argument unification.
        if !type_value_is_ground(kb, *carrier_value) {
            continue;
        }
        let Some(spec_vid) = type_param_vid_in_sort(kb, spec_sort, *spec_param_sym) else {
            continue;
        };
        // STILL-FREE gate (see the fn doc): only a never-threaded value-param is bound; a
        // param an argument already pinned (the carrier param, an Iterable `Element`) is
        // left untouched.
        if subst.resolve_as_value(spec_vid).is_some() {
            continue;
        }
        // WI-391: the producer emits the canonical `Ref(S)` binding shape (a bare sort is
        // `Ref(S)`, never the former nullary `Fn{S}` that extracted as `Error`), so the
        // carrier value binds directly — no late `Fn{S}→Ref(S)` normalization needed.
        let bound = *carrier_value;
        if !occurs_in(kb, spec_vid, bound) {
            subst.bind_term(kb, spec_vid, bound);
            any = true;
        }
    }
    any
}

/// A `parameterized` type's bindings as `(carrier-param canonical VarId, value)`
/// pairs — the receiver-side reader for [`bind_spec_params_from_carrier`] and
/// [`bind_spec_params_from_carrier_param`]. Reads via [`extract_type`] and re-keys
/// each binding by the `owner_sort`'s canonical `Var::Global` param VarId (WI-600:
/// the identity key carrier grounding joins on, replacing the non-hygienic short
/// name). Keeps only `Value::Term` values (a parameterized type's bindings are
/// ground terms) whose param resolves to one of `owner_sort`'s declared params.
///
/// `owner_sort` is the carrier the receiver type applies (`List` for a `List[T =
/// Int]` receiver): its declared params own these binding keys, so resolving each
/// through [`type_param_vid_in_sort`] anchored to it yields the same canonical
/// VarId the provider view's carrier-side leaves resolve to — an identity match
/// that cannot cross-collide with an unrelated sort's like-named param.
pub(super) fn parameterized_vid_bindings(
    kb: &KnowledgeBase,
    ty: &impl TermView,
    owner_sort: Symbol,
) -> Vec<(VarId, TermId)> {
    // WI-361: a parameterized type's bindings (`List[T = Int]` ⇒ `[(T, Int)]`), read
    // carrier-agnostically through `extract_type` (WI-470: the receiver type is now a
    // `Value::Node` for an occurrence-primary `List[T = …]`, but its binding `T = Int`
    // is CARRIED in the node — never erased; `extract_type` reads it the same as the
    // hash-consed `Fn{S, named}` twin, so the spec-param grounding stays sound).
    let TypeExtractor::Parameterized { bindings, .. } = extract_type(kb, ty) else {
        return Vec::new();
    };
    bindings
        .into_iter()
        .filter_map(|(param, value)| match value {
            // A concrete parameterized carrier's binding is a ground sort term
            // (`List[T = Int]` ⇒ `Int`) — thread it. WI-477: a non-`Term` (Node)
            // binding — a carrier parameterized by a poisoned/occurrence type — is
            // not the ground `TermId` the carrier-grounding consumers `bind_term`;
            // leaving it unthreaded surfaces a LOUD `unconstrained` downstream (cf.
            // the `type_value_is_ground` guard in `bind_spec_params_from_carrier`)
            // rather than a silently-wrong bind. Threading such a compound is WI-380
            // follow-up work.
            Value::Term { id: t, .. } => {
                type_param_vid_in_sort(kb, owner_sort, param).map(|vid| (vid, t))
            }
            _ => None,
        })
        .collect()
}

/// WI-714 (proposal 052) — the FULL provider view of `carrier_sym` for `spec_sort`
/// (every spec param ↦ a carrier-side value), DIRECT or composed through TRANSITIVE
/// provision. The self-receiver companion to [`transitive_provision_view`] (which
/// returns a single carrier-`pvid` view for the carrier-param shape): here the
/// receiver is typed by the spec sort itself (`headOption(s: Stream)` with `s :
/// Relation[T, E]`), so ALL of the spec's params must ground off the carrier — and
/// `Relation` provides `Stream` only through the chain `Relation provides
/// LogicalStream provides Stream`, with no direct `Relation provides Stream` fact.
/// Direct provision wins (the hot path — `List provides Stream` etc.). Otherwise
/// descend the specs `carrier_sym` provides, find one that (transitively) provides
/// `spec_sort`, and compose its view back through the carrier→intermediate hop via
/// [`compose_provision_views`]. `visited` guards a cyclic `provides` chain.
fn transitive_provider_spec_view_bindings(
    kb: &KnowledgeBase,
    carrier_sym: Symbol,
    spec_sort: Symbol,
    visited: &mut SmallVec<[Symbol; 8]>,
) -> Option<SmallVec<[(Symbol, TermId); 2]>> {
    compose_through_provision_chain(kb, carrier_sym, visited, VisitOrder::DirectFirst, &|c| {
        provider_spec_view_bindings(kb, c, spec_sort)
    })
    .map(|(view, _)| view)
}

/// WI-20260829-GNPG7 — the provider view for the SUBTYPE relation: direct, else composed
/// through the provision chain, but only once a chain is known to exist.
///
/// THE PRE-FILTER IS A PERFORMANCE GUARD AND NOTHING ELSE, and it is here rather than
/// inside [`transitive_provider_spec_view_bindings`] because the two consumers have
/// different traffic. The receiver-grounding callers (WI-495/WI-714) ask about a carrier
/// they already know provides the spec; the subtype relation asks about EVERY pair of
/// parameterized types whose bases differ, and the overwhelmingly common answer is "no
/// relation at all". Answering that with the composing walk means reading provider facts
/// and allocating a view per node of the actual's whole provision closure, on a relation
/// that runs per type comparison.
///
/// MEASURED, in-process and paired, min of K full stdlib loads (72 files) in ONE process —
/// which is the instrument, because the test suite's wall clock is dominated by other work
/// and showed the ungated regression below as noise:
///
/// ```text
/// single-hop (pre-ticket)   release  71.9 ms    debug  552.4 ms
/// transitive, UNGATED       release 127.7 ms    debug  732.6 ms    (1.78x / 1.33x)
/// transitive, gated (this)  release  69.0 ms    debug  544.6 ms    (no difference)
/// ```
///
/// THE THIRD ROW IS "NO DIFFERENCE", NOT "4% FASTER". This machine's samples spread ~2x
/// under contention, so single runs are worthless here: interleaved min-of-25 rounds put
/// baseline at 72.0 / 82.0 ms and the gated version at 85.2 / 70.1 ms — the two rounds
/// DISAGREE about which is faster, which is the honest way to say the difference is inside
/// the noise. The ungated 127.7 ms is outside that band and reproduced on every sample,
/// which is why it is reported as a real regression and this row is not reported as a win.
///
/// SEMANTICS-PRESERVING, not a heuristic: [`sort_provides`] walks `provides_out_edges` and
/// the composer walks `directly_provided_specs`, and both read the same provider-index
/// carrier buckets under the same filters — so the walk can only ever succeed where
/// `sort_provides` is already true, and gating it skips exactly the calls that would have
/// returned `None`. The one asymmetry runs the safe way: `provides_out_edges` also drops a
/// non-live rule, so the filter is if anything the stricter of the two, and a provision
/// from a dead rule is not one this relation should honour.
///
/// WI-20260829-XZMGC — THE RETURNED FLAG IS `true` WHEN THE SPEC'S CARRIER PARAMETER WAS
/// TAKEN OUT OF A COMPOSED VIEW, and it means "that parameter is not in this view; the
/// caller owns it". A composed view cannot state it: `Stream provides Iterable[C = Stream,
/// …]` binds `C` to STREAM ITSELF, and [`compose_provision_views`] substitutes the
/// intermediate's PARAMS and keeps everything else verbatim (its own doc names `C ↦ Stream`
/// as exactly that case), so the composed view for `List` would say the carrier is a
/// `Stream`. It is not: `C` is the value `Iterable.iterator(c: C)` receives, and `iterator`
/// on a `List` receives the LIST. So the carrier param is EXCLUDED here (below) and each
/// caller supplies THE ACTUAL'S OWN TYPE for it, which is the same rule
/// [`bare_spec_arg_provision_projection`] already states and works around at its own site
/// ("the spec's CARRIER parameter is the receiver's own type, by definition, and must not
/// be read off the provision").
///
/// THE FLAG IS "WAS DROPPED", NOT "WAS COMPOSED", so the override replaces a mangled
/// binding and never invents an absent one. A chain whose provisions bind no carrier
/// parameter at all leaves the flag `false` and the expected binding refuses, exactly as
/// before — silence is not the same claim as a wrong value, and reading it as one would
/// widen a case this ticket measured nothing about.
///
/// EXCLUDED RATHER THAN REWRITTEN HERE, for two reasons. (1) The right value differs per
/// caller — [`parameterized_compatible_view`] has the actual's full type
/// (`List[T = Row]`), [`bare_provider_binding_precise`] has a bare sort — and emitting the
/// weaker bare `Ref(carrier)` for both would open a hole the DIRECT case does not have:
/// MEASURED, `MutableStack[T = Row]` is refused at `Iterable[C = MutableStack[T = Bool]]`,
/// and a bare `C ↦ List` would ACCEPT `Iterable[C = List[T = Bool]]` for a `List[T = Row]`
/// ((sort_ref, parameterized) on one base is compatible both directions). (2) The
/// per-route value is meaningless, so it must not reach the merge below: two routes
/// through two intermediates would each name THEMSELVES and be read as a disagreement.
///
/// THE DIRECT BRANCH IS UNTOUCHED (flag `false`, carrier param kept): a direct provision
/// names its own carrier truthfully, and this is where the ticket's alternative route —
/// recognizing the self-reference at the subtype site, from the composed view alone — was
/// rejected. That reading is "an actual-side value that is a bare ref to a sort the actual
/// provides", and it cannot tell the artifact from a provision that legitimately binds a
/// param to a spec sort the carrier also provides. Splitting on the BRANCH needs no such
/// recognition: only composition manufactures the self-reference.
pub(super) fn subtype_provider_view(
    kb: &KnowledgeBase,
    carrier: Symbol,
    spec: Symbol,
) -> Option<(SmallVec<[(Symbol, TermId); 2]>, bool)> {
    // The direct fact first — the hot path, and the answer for every carrier that
    // declares the spec itself. Reached before the reachability walk so a one-hop
    // provider pays nothing for the chain machinery.
    if let Some(view) = provider_spec_view_bindings(kb, carrier, spec) {
        return Some((view, false));
    }
    if !sort_provides(kb, carrier, spec) {
        return None;
    }
    // AMBIGUITY IS ANSWERED `None`, NOT BY SOURCE ORDER.
    // [`transitive_provider_spec_view_bindings`] returns the FIRST intermediate whose
    // subtree reaches `spec` — fine for the receiver-grounding callers, which ask about a
    // carrier already known to provide the spec through one route, and NOT fine here.
    // DRIVEN: a `Carrier` providing two intermediates that bind one spec param differently
    // (`MidA provides Spec[P = Int64]`, `MidB provides Spec[P = Bool]`) was accepted at
    // `Spec[P = Bool]` or refused depending ONLY on which `provides` line came first —
    // swapping the two lines and changing nothing else flipped the verdict. Before this
    // ticket the shape was refused BOTH ways, since the subtype relation had no transitive
    // route at all, so shipping first-match here would trade a uniform refusal for one
    // decided by declaration order.
    //
    // WHY `None` AND NOT A LOUD REFUSAL, which is what the house style otherwise asks: this
    // function returns `Option` into a `bool` subtype predicate and has no error channel —
    // the same constraint [`provider_spec_view_bindings`] records for its own ~12 consumers
    // ("whose 'loud' would read as an ordinary type mismatch"). `None` yields exactly that
    // ordinary, LOCATED type mismatch at the argument, deterministically, and it is the
    // conservative direction: this arm can only ever refuse more than first-match, never
    // accept more.
    //
    // WHY NOT MERGE, the way the DIRECT reader does (WI-842 §4.9): merging is licensed
    // there by `check_provision_binding_agreement`, which refuses a param bound two ways at
    // LOAD — a guarantee that holds for one carrier's own provisions and NOT across two
    // independent intermediate sorts, each of which is individually well-formed. Merging
    // here would re-introduce the same silent per-param first-wins in different clothes.
    // Whether such a carrier should instead be a load error, and whether an author should
    // be able to select the route, is a design question: WI-20260829-GNPG7's delivery
    // note names it.
    // MERGED, NOT PICKED. Every reachable route contributes its bindings; a param two
    // routes bind DIFFERENTLY answers `None`. Picking one route and only checking the
    // others for conflicts was the first cut and it was NOT order-independent — found by
    // /code-review, then DRIVEN: with `MidA provides Spec[P = Int64]` and `MidB provides
    // Spec[Q = Bool]` the two views have DISJOINT labels, so they trivially "agreed" and
    // the answer was whichever route came last. `Spec[Q = Bool]` loaded under one ordering
    // of `Carrier`'s two `provides` lines and was refused under the other, and
    // `Spec[P = Int64]` did the reverse — the exact defect that cut was written to remove.
    // Merging is order-independent by construction: consumers look the view up by param
    // SHORT NAME, so only the set matters, and the set is the same whichever route is
    // walked first.
    //
    // This is the DIRECT reader's rule (`provider_spec_view_bindings`, WI-842 §4.9) applied
    // one level up, and it needs its own licence because that one's does not reach here:
    // there, merging is safe because `check_provision_binding_agreement` refuses a
    // doubly-bound param at LOAD, a guarantee that holds for ONE carrier's own provisions
    // and not across two independent intermediate sorts. So the conflict case cannot be
    // assumed away and is answered `None` instead — the conservative direction, and the
    // only one available to a `bool` predicate with no error channel.
    let views = provision_route_views(kb, carrier, spec)?;
    // WI-20260829-XZMGC — the spec's CARRIER parameter is dropped from a route whose value
    // for it is the SELF-REFERENCE composition manufactured (see the header). `None` when
    // the spec has no identifiable carrier param — then nothing is dropped and nothing is
    // overridden downstream, which is the pre-ticket reading for that spec.
    let carrier_vid =
        spec_carrier_param(kb, spec).and_then(|p| type_param_vid_in_sort(kb, spec, p));
    // THE ONE SORT ON THIS CHAIN THAT NAMES ITSELF as `spec`'s carrier — `Stream`, read
    // from `List`. [`transitive_carrier_for_param`] is the existing owner of that walk (the
    // eval path's "who owns the impl" question), and it is the whole of the value gate:
    // the artifact is the composed view repeating THAT sort's self-naming, so the value
    // must BE it. Hoisted out of the loop — one walk per composed lookup.
    let self_naming = carrier_vid
        .and_then(|cvid| transitive_carrier_for_param(kb, spec, cvid, carrier))
        .filter(|owner| !same_sort_canonical(kb, *owner, carrier));
    let mut merged: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    let mut dropped_carrier = false;
    for view in &views {
        for (param, value) in view {
            // `Some(cvid)` on both sides, never `None == None`: a param whose vid does not
            // resolve is not the carrier param, and a spec with no carrier param excludes
            // nothing.
            if let (Some(cvid), Some(owner)) = (carrier_vid, self_naming) {
                if type_param_vid_in_sort(kb, spec, *param) == Some(cvid)
                    && composed_self_reference(kb, owner, *value)
                {
                    dropped_carrier = true;
                    continue;
                }
            }
            match merged.iter().find(|(mp, _)| same_label(kb, *mp, *param)) {
                Some((_, seen)) if !provision_bindings_agree(kb, *seen, *value) => return None,
                Some(_) => {}
                None => merged.push((*param, *value)),
            }
        }
    }
    // A ROUTE THAT KEPT THE PARAM WINS OVER ONE THAT DROPPED IT. Two routes can disagree
    // about whether their carrier value is a manufactured self-reference; if any of them
    // stated a real one it is in `merged`, and the caller must read that rather than
    // substitute the actual over it.
    let dropped_carrier = dropped_carrier
        && !merged.iter().any(|(p, _)| {
            carrier_vid.is_some() && type_param_vid_in_sort(kb, spec, *p) == carrier_vid
        });
    // AN EMPTY MERGE IS AN ANSWER WHEN THE CARRIER PARAM IS WHAT EMPTIED IT — for a spec
    // whose only parameter is its carrier, the composed chain has said everything it can
    // and the caller supplies that one binding itself. Keeping the flat `is_empty()`
    // refusal here would have made THAT spec the one shape this ticket does not fix.
    // Without a dropped carrier param an empty merge is the pre-ticket `None`.
    (dropped_carrier || !merged.is_empty()).then_some((merged, dropped_carrier))
}

/// WI-20260829-XZMGC — is `value`, a COMPOSED view's binding for the spec's carrier param,
/// the self-reference the composition manufactured rather than a claim anyone made?
///
/// It is when the value names `owner`: the sort on THIS carrier's provision chain that
/// binds the carrier param to ITSELF (`Stream provides Iterable[C = Stream, …]`, read from
/// `List`), which the caller resolves once through [`transitive_carrier_for_param`]. That
/// is precisely `C = Self` spelled with the intermediate's name, and it is what
/// [`compose_provision_views`] cannot substitute — it maps the intermediate's PARAMS, and
/// this is not one.
///
/// THE VALUE GATE IS LOAD-BEARING, because the PARAMETER gate cannot carry the question
/// alone: [`spec_carrier_param`] answers "the first declared type parameter some declared
/// operation TAKES", which by design (WI-1077) reads an ACCEPTED ARGUMENT as the carrier —
/// `operation touch(c: Spec, x: P)` files at `P`, the element. For such a spec the composed
/// view's `P` is an ordinary composed binding and correct, and dropping it substituted the
/// actual's whole type for the element type. MEASURED, found by /code-review:
/// `Carrier[T = Int64]` was REFUSED at `Spec[P = Int64, Q = Int64]`, a program that loads
/// on the pre-ticket tree.
///
/// AND "THE VALUE'S SORT SELF-PROVIDES THE SPEC" IS NOT THE GATE, which was the SECOND cut
/// and the second review's finding. That property holds of any self-providing sort —
/// `Int64 provides Combiner[T = Int64]` is the ordinary shape — so a mis-identified ELEMENT
/// param whose value is such a sort was still dropped. DRIVEN, both signs, on a chain
/// `Carrier provides Mid provides Spec[P = Elem]` with `Elem provides Spec[P = Elem]`:
/// `Spec[P = Elem]` was REFUSED for a `Carrier` and `Spec[P = Carrier]` ACCEPTED, while the
/// one-hop `Mid` answered the opposite to both — the composed path contradicting the direct
/// path, which is the defect this ticket removes, relocated. Identity against the chain's
/// OWN self-naming sort is the exact question: for that fixture there is none (no sort on
/// `Carrier`'s chain binds `P` to itself), so nothing is dropped.
pub(super) fn composed_self_reference(kb: &KnowledgeBase, owner: Symbol, value: TermId) -> bool {
    crate::kb::load::provides_spec_base_sym(kb, value)
        .is_some_and(|base| same_sort_canonical(kb, base, owner))
}

/// Every composed provider view of `spec` reachable from `carrier`, one per DIRECT
/// intermediate that reaches it. Used only by [`subtype_provider_view`] to tell one route
/// from several; the ordinary readers take the first and are documented for it.
fn provision_route_views(
    kb: &KnowledgeBase,
    carrier: Symbol,
    spec: Symbol,
) -> Option<SmallVec<[SmallVec<[(Symbol, TermId); 2]>; 2]>> {
    // REACHABILITY FIRST, COMPOSITION ONLY FOR THE ROUTES THAT REACH. The naive form —
    // ask `transitive_provider_spec_view_bindings` per intermediate and keep the `Some`s —
    // pays a composing walk for every spec the carrier declares, which for a carrier like
    // `List` (six direct provisions) is six of them where first-match stopped at one.
    // MEASURED: that cost 103.2 ms against a 71.9 ms baseline on the min-of-7 stdlib load;
    // splitting the cheap question from the expensive one brings it back (see
    // [`subtype_provider_view`]'s table). `sort_provides` is the same indexed edge walk the
    // pre-filter uses, with no fact reads or view allocation per node.
    let reaching: SmallVec<[Symbol; 2]> = directly_provided_specs(kb, carrier)
        .into_iter()
        .filter(|&intermediate| sort_provides(kb, intermediate, spec))
        .collect();
    // A REACHING ROUTE THAT CANNOT BE COMPOSED POISONS THE ANSWER, it does not vanish.
    // `sort_provides` said this intermediate reaches the spec, so a `None` from either
    // composition step is a route whose bindings are UNKNOWN, not a route that is absent —
    // and dropping it would let the caller see "one route, nothing to disagree with" and
    // accept a binding the unrepresentable route might contradict. Returning `None` for the
    // whole lookup is the conservative reading (the caller then refuses the comparison),
    // and it keeps this loop from being the silent `continue` the repo's principles warn
    // about (found by /code-review).
    let mut out: SmallVec<[SmallVec<[(Symbol, TermId); 2]>; 2]> = SmallVec::new();
    for intermediate in reaching {
        let mut visited: SmallVec<[Symbol; 8]> = SmallVec::new();
        let outer = transitive_provider_spec_view_bindings(kb, intermediate, spec, &mut visited)?;
        let inner = provider_spec_view_bindings(kb, carrier, intermediate)?;
        out.push(compose_provision_views(kb, intermediate, &outer, &inner));
    }
    Some(out)
}

/// The spec-view bindings of the `SortProvidesInfo` facts recording that
/// `carrier_sym` provides `spec_sort` — `(spec param symbol, carrier-side
/// value)` pairs (`fact Stream[T = T]` on `List` ⇒ `[(Stream.T, List.T)]`).
/// `None` when the carrier declares no such provision.
///
/// WI-842 (proposal 058 §4.9) — every carrier-keyed provision of `spec_sort` for
/// `carrier_sym` is read, and their bindings MERGED, rather than returning the first
/// provision's view.
///
/// Both halves of that matter, and neither is the §4.9 "loud at the read" rule —
/// which this reader cannot obey and does not need to:
///
///   * a param bound TWO WAYS by two provisions is refused at LOAD
///     ([`check_provision_binding_agreement`]), because a carrier's own provision has
///     no NAME for any call site to select (§4.3) and this reader's ~12 consumers are
///     `bool`/`Option` type predicates whose "loud" would read as an ordinary type
///     mismatch. That refusal is also the one phase 3b does NOT delete — 3b relaxes
///     coexistence for NAMEABLE providers (witness sorts), whose `sort_ref` is the
///     witness, so they never appear here as the carrier's own provision. First-match
///     was licensed by a refusal that is about to disappear; merging is licensed by
///     one that stays.
///   * with conflicts refused, merging is total and strictly more complete than
///     first-match: a provision binding a param that an earlier one omits is no
///     longer INVISIBLE behind it (§4.9's recorded blind spot — "a first
///     `SortProvidesInfo` fact that binds no `eq` hides a second that does").
///
/// The first match is returned unchanged when it is the only one, which MEASURED is
/// every (carrier, spec) this reader is ever ASKED for across the stdlib and the whole
/// test corpus; the merge path allocates only for a carrier that declares one spec more
/// than once. That measurement is about the reads, NOT about the KB: multi-provision
/// carriers do exist (`Console` provides `Effect` three times, at three different
/// applications — see [`check_provision_binding_agreement`]), and asked for such a
/// carrier's view this reader still answers the first application of several. That
/// under-determination is not §4.9's defect — no op binding is selected by it — and
/// fixing it means giving the reader the APPLICATION as an input, which is a design
/// increment of its own.
pub(super) fn provider_spec_view_bindings(
    kb: &KnowledgeBase,
    carrier_sym: Symbol,
    spec_sort: Symbol,
) -> Option<SmallVec<[(Symbol, TermId); 2]>> {
    // (An unresolved `SortProvidesInfo` symbol yields no rows, and the tail returns
    // `None` — identical to the old `?` early return.)
    let mut merged: Option<SmallVec<[(Symbol, TermId); 2]>> = None;
    for row in provides_rows_of_provider(kb, carrier_sym) {
        // Canonicalize both sides — the spec base in the provider fact's
        // `SortView` is resolved in the carrier's import scope and may be a
        // different `Symbol` id than `spec_sort` (resolved in the caller's
        // scope) even for the same logical sort. Matches the carrier compare
        // inside `provides_rows_of_provider`; a raw `==` would silently no-op
        // this binding.
        if kb.canonical_sort_sym(row.spec_base) != kb.canonical_sort_sym(spec_sort) {
            continue;
        }
        let bindings = row.bindings;
        match &mut merged {
            // The overwhelmingly common case: one provision, returned as it was
            // read, with no merge allocation.
            None => merged = Some(bindings),
            // A SECOND provision for this (carrier, spec). Its params are folded in
            // by SHORT NAME (a param resolved in two import scopes carries two
            // Symbols for one spec parameter). A param already present is left as
            // read: the two agree, because a disagreement is a load error
            // ([`check_provision_binding_agreement`]) — and during the very load
            // that reports it, keeping the first is the pre-WI-842 answer rather
            // than a new third one.
            Some(view) => {
                for (param, value) in bindings {
                    let short = short_name_of(kb.local_name_of(param));
                    if !view
                        .iter()
                        .any(|(p, _)| short_name_of(kb.local_name_of(*p)) == short)
                    {
                        view.push((param, value));
                    }
                }
            }
        }
    }
    merged
}

/// WI-357 — true iff an effect label is still an unresolved type/row
/// variable (a bare `?_`). Used to close a spec op's polymorphic effect
/// row when it dispatches to a concrete carrier whose provider fact does
/// not (yet) bind the effect parameter.
pub(super) fn effect_is_unresolved_var(kb: &KnowledgeBase, e: &Value) -> bool {
    match e {
        Value::Term { id: t, .. } => matches!(kb.get_term(*t), Term::Var(_)),
        _ => false,
    }
}

/// WI-067 / WI-478 — flatten one callee effect expression into `out`, DROPPING any
/// guarded atom whose σ(guard) refutes from Γ. The one owner of that decision.
///
/// IT HAS TWO CALLERS AND USED TO HAVE ONE, which is the whole reason it is a function.
/// The op's-own-effect loop in [`check_apply_iter`] discharged; [`dispatched_impl_effects`]
/// — the row a DISPATCHED spec-op call takes instead — did not, so an impl's guarded
/// effect came back conservatively present after the spec op's identical one had just
/// been discharged. Invisible while `/` resolved to `Int64.div` (a concrete op, no
/// dispatch); WI-20260824-VT8CF made `/` a spec operation and MEASURED it at once —
/// `Int64.div(n, 2)` loaded pure while `n / 2` and `Divisible.div(n, 2)` both demanded a
/// declared `Error[DivisionByZero]`, for a divisor literal `2` that refutes `eq(b, 0)`
/// by ground evaluation.
///
/// `has_guarded` is the caller's own "this op declares a guarded atom at all" answer,
/// kept as a parameter rather than recomputed: both callers have already paid for it,
/// and the guard-σ they pass is built only when it is true.
pub(super) fn push_effect_with_guard_discharge(
    kb: &mut KnowledgeBase,
    flow: &FlowEnv,
    subst: &Substitution,
    guard_sigma: &HashMap<Symbol, TermId>,
    has_guarded: bool,
    walked: Value,
    out: &mut Vec<Value>,
) {
    let (bare_row, walked) = if value_is_bare_row_expr(kb, &walked) {
        (true, wrap_bare_effect_expr_as_row(kb, &walked))
    } else {
        (false, walked)
    };
    if bare_row || matches!(type_head(kb, &walked), TypeHead::EffectsRows) {
        // A WRITTEN row wrapper: flatten to its present labels, then — WI-067 — drop the
        // label of any guarded atom inside whose σ(guard) refutes from Γ. The flatten
        // leaves a guarded atom's label conservatively present (WI-478); discharge
        // removes only the proven-dropped ones.
        let mut present = effect_row_present_values(kb, &walked);
        if has_guarded {
            drop_refuted_guarded_labels(kb, flow, subst, guard_sigma, &walked, &mut present);
        }
        out.extend(present);
    } else if has_guarded && resolved_functor_name(kb, &walked) == Some("guarded") {
        // A STANDALONE guarded atom (how a partial primitive declares its single effect:
        // `div … effects { Error[…] :- eq(b, 0) }`). Refute σ(guard) from Γ; drop the
        // atom on a positive proof of ¬guard, else keep it conservatively present
        // (unchanged from WI-478).
        if !guarded_atom_value_refuted(kb, flow, subst, guard_sigma, &walked) {
            out.push(walked);
        }
    } else {
        out.push(walked);
    }
}

/// WI-365 — the EFFECT dual of WI-357's element threading. When a body-less
/// self-receiver spec op (`Box.peek`, polymorphic `effects Effect`) dispatches
/// to a concrete impl that OVERRIDES it with a genuine effect
/// (`MutBox.peek effects Modify[b]`), the spec op's effect ROW must be GROUNDED
/// to the impl's real effects at the consumption site — not dropped as if the
/// carrier were pure. The pre-dispatch effect-close drops the still-unresolved
/// row var (correct for a pure provider / host builtin — a provider fact cannot
/// bind an effect parameter, WI-301); once dispatch resolves the concrete impl,
/// this re-derives its effects so a pure consumer is rejected exactly as a
/// DIRECT call to the impl op is.
///
/// Each impl effect is param-substituted (the IMPL op's params → the call's
/// argument vars) so `Modify[b]` re-keys to the caller's actual argument — the
/// same rewrite the spec op's own effects get at the call site
/// (`substitute_ref_syms_value`, WI-342 E2 re-keys a `Value::Node` label's
/// `Ref` spine). WI-604: a projection-BEARING impl effect (`Stream.isEmpty
/// effects s.E`) is instead δ-reduced against the receiver argument's concrete
/// type via `eliminate_type_projections` — a blanket re-key cannot reduce
/// `s.E` off a `Stream[E = {}]` to `{}`, so the pre-WI-604 path leaked it as a
/// spurious `undeclared effect: s.E`. It is then walked through the per-call subst and filtered to
/// CONCRETE effects: an impl whose own effect row is itself an unbound var is
/// effectively pure here, so it contributes nothing — keeping the
/// `List`-as-`Stream` pure path unchanged. Returns `[]` for a pure override
/// (empty or wholly-unresolved effects).
///
/// The map keys on the IMPL op's parameter names (the impl's effects reference
/// the impl's own params, which may be renamed vs the spec op's). Parameters
/// align positionally across a spec op and its override (the override-refinement
/// check enforces this) and the call was matched against the SPEC op, so the
/// arg for impl param `i` is the positional arg at `i`, or — for a named call —
/// the arg named with the SPEC op's param[i] name (`spec_params`).
pub(super) fn dispatched_impl_effects(
    kb: &mut KnowledgeBase,
    flow: &FlowEnv,
    impl_op_sym: Symbol,
    spec_params: &[(Symbol, Value)],
    subst: &Substitution,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> Vec<Value> {
    let Some(impl_op) = lookup_operation_info_full(kb, impl_op_sym) else {
        return Vec::new();
    };
    if impl_op.effects.is_empty() {
        return Vec::new();
    }
    // WI-20260824-VT8CF — the impl's own guarded atoms, and the call σ to refute them
    // with. `collect_guarded_atoms` walks each effect, so it is asked once and the σ
    // below is filled only when the answer is yes — the common effect-bearing op that
    // declares no guard pays nothing.
    let impl_has_guarded = impl_op
        .effects
        .iter()
        .any(|e| !collect_guarded_atoms(kb, subst, e).is_empty());
    let mut guard_sigma: HashMap<Symbol, TermId> = HashMap::new();
    let mut param_to_arg: HashMap<Symbol, Symbol> = HashMap::new();
    // WI-604: the IMPL op's parameter TYPES, keyed by impl-param symbol, so a
    // projection-bearing impl effect (`Stream.isEmpty effects s.E`) is δ-reduced
    // against the receiver argument's concrete type in the loop below.
    let mut param_to_arg_type: HashMap<Symbol, Value> = HashMap::new();
    for (i, (impl_param_sym, _)) in impl_op.params.iter().enumerate() {
        // Positional arg at this index, else the named arg carrying the spec
        // op's param[i] name (the caller names spec-op params, not impl params).
        let mut arg_sym = pos_args.get(i).and_then(extract_var_ref_sym_node);
        let mut arg_ty = pos_results
            .get(i)
            .and_then(|r| r.as_ref().ok())
            .map(|r| r.ty.clone());
        if arg_sym.is_none() || arg_ty.is_none() {
            if let Some((spec_name, _)) = spec_params.get(i) {
                for (j, (n, occ)) in named_args.iter().enumerate() {
                    // WI-426: a named label binds to its param by name, not symbol identity.
                    if same_label(kb, *n, *spec_name) {
                        if arg_sym.is_none() {
                            arg_sym = extract_var_ref_sym_node(occ);
                        }
                        if arg_ty.is_none() {
                            arg_ty = named_results
                                .get(j)
                                .and_then(|r| r.as_ref().ok())
                                .map(|r| r.ty.clone());
                        }
                        break;
                    }
                }
            }
        }
        if let Some(s) = arg_sym {
            param_to_arg.insert(*impl_param_sym, s);
        }
        if let Some(t) = arg_ty {
            param_to_arg_type.insert(*impl_param_sym, t);
        }
        // WI-20260824-VT8CF — σ for the guard, paired THE WAY THIS FUNCTION'S DOC
        // PRESCRIBES: positionally by index, or — for a named call — by the SPEC op's
        // `param[i]` label, because that is what a caller writes.
        //
        // NOT `build_call_guard_sigma(kb, &impl_op.params, …)`, which is what this did
        // first and which is wrong in both directions. That helper matches a named arg's
        // LABEL against the params it is handed — correct where the call was matched
        // against those very params, and not here, where the call was matched against the
        // SPEC op. An override may rename or permute its parameters (`align_effect_label`
        // exists for exactly that), so with impl params: a RENAMED one leaves σ empty, the
        // guard cannot ground, and a literal divisor that refutes it keeps a spurious
        // `undeclared effect` — the very false positive this discharge exists to remove,
        // reintroduced for named calls; a PERMUTED one binds the guard to the WRONG
        // OPERAND, which drops an effect that is really incurred. The second direction is
        // unsound, not merely imprecise. Found by `/code-review`, which also found that
        // the paragraph stating this rule had been displaced off this function.
        if impl_has_guarded {
            let guard_arg = pos_args.get(i).cloned().or_else(|| {
                spec_params.get(i).and_then(|(spec_name, _)| {
                    named_args
                        .iter()
                        .find(|(n, _)| same_label(kb, *n, *spec_name))
                        .map(|(_, occ)| Rc::clone(occ))
                })
            });
            if let Some(occ) = guard_arg {
                if let Some(t) = crate::kb::node_occurrence::try_occurrence_to_term(kb, &occ) {
                    guard_sigma.insert(*impl_param_sym, t);
                }
            }
        }
    }
    let arg_syms = (!param_to_arg.is_empty()).then_some(&param_to_arg);
    let ctx = TypeErrorContext::OperationReturn {
        op_name: impl_op_sym,
        surface: None,
    };
    let mut out: Vec<Value> = Vec::new();
    for e in &impl_op.effects {
        // WI-604: an override's effect can carry a self-receiver PROJECTION
        // (`Stream.isEmpty effects s.E`) that a blanket ref-substitution leaves
        // un-reduced — the exact gap the op's-own-effect loop avoids via
        // `eliminate_type_projections` (the `op_has_projection` path). Ground it
        // here too: project the effect member off the receiver argument's
        // concrete type (`s.E` off `Stream[E = {}]` → `{}`), so a defaulted spec
        // op dispatched to a carrier's `s.E`-effect override (`Iterable.isEmpty`
        // → `Stream.isEmpty` on a pure Stream value) is PURE, not a spurious
        // `undeclared effect: s.E`. Use the reduction ONLY when it GROUNDS to a
        // concrete row; on an ABSTRACT receiver (a `Stream` param whose `E` is
        // unwritten or a bare row variable) elimination instead leaves an unbound
        // row var, a projection identical to the fallback, or errors — none of
        // which a caller can match against a written `E = {}`, so fall back to the
        // blanket re-key (`s.E` → the caller's receiver projection), the pre-WI-604
        // behavior, correct there (the caller declares/threads the abstract row).
        // A projection-free effect (`Modify[b]`) skips elimination and takes the
        // plain re-key, unchanged.
        let sub = if value_contains_projection(kb, e) {
            // The `!effect_is_unresolved_var` guard is load-bearing: when `E` is a
            // bare row var the reduction returns that raw var, which a later
            // `walk_type_deep_value` + concrete-filter would SILENTLY DROP — the
            // guard routes it to the fallback re-key instead so the row survives.
            match eliminate_type_projections(kb, e, &param_to_arg_type, arg_syms, &ctx, None) {
                Ok(reduced) if !effect_is_unresolved_var(kb, &reduced) => reduced,
                _ => substitute_ref_syms_value(kb, e, &param_to_arg),
            }
        } else if param_to_arg.is_empty() {
            e.clone()
        } else {
            substitute_ref_syms_value(kb, e, &param_to_arg)
        };
        let walked = walk_type_deep_value(kb, subst, &sub);
        if !effect_is_unresolved_var(kb, &walked) {
            // WI-20260824-VT8CF — DISCHARGE HERE TOO, through the same owner the
            // op's-own-effect loop uses. σ is built over the IMPL's parameters, because
            // it is the impl's guard (`Int64.div`'s `eq(b, 0)`) being refuted and its
            // `b` that the call's argument must be bound to; the caller names the SPEC
            // op's params, which is exactly what `build_call_guard_sigma` resolves by
            // position and by label.
            push_effect_with_guard_discharge(
                kb,
                flow,
                subst,
                &guard_sigma,
                impl_has_guarded,
                walked,
                &mut out,
            );
        }
    }
    out
}

/// The name symbol carried by a type-parameter reference in any of the shapes a
/// provider fact / receiver type stores it in — a bare sort, `Ref(p)` or the nullary
/// `Fn{p}` (the `make_name_term` shape), both through [`extract_sort_ref_sym`]; an
/// `Ident`; or a `Var::Global`/`Var::Rigid` (`v.name()`). `None` for anything else.
///
/// WI-20260923-N3W68 (#12) — the nullary-`Fn` arm this function also had is gone. It could
/// fire only where [`extract_sort_ref_sym`] had already declined — on a meta-constructor
/// [`type_head`] classifies apart, `Nothing` — and there it answered `Some` for the `Fn`
/// spelling while the `Ref` spelling answered `None`: one nullary term, two answers
/// (WI-20260902-CZJ2N). Neither spelling names a type parameter. A probe on the arm fired
/// zero times across the workspace suite, so no answer any corpus reads changes.
///
/// WI-599: a `Var::Rigid` counts too — an op's own type params are Skolemized while
/// its body is checked, so a bare carrier argument `c : C` arrives as a rigid var
/// carrying the param's name.
pub(super) fn typaram_occurrence_sym(kb: &KnowledgeBase, tid: TermId) -> Option<Symbol> {
    if let Some(s) = extract_sort_ref_sym(kb, &TermIdView(tid)) {
        return Some(s);
    }
    match kb.get_term(tid) {
        // A bare sort is answered above via `extract_sort_ref_sym` (WI-361); `Ident` here.
        Term::Ident(s) => Some(*s),
        Term::Var(Var::Global(v)) | Term::Var(Var::Rigid(v)) => Some(v.name()),
        _ => None,
    }
}

/// WI-600 — the `owner_sort`'s canonical `Var::Global` param VarId that a type-param
/// occurrence denotes: the hygienic, identity-keyed replacement for the short-name
/// collapse carrier grounding used to join on. Reads the occurrence's name symbol
/// ([`typaram_occurrence_sym`]) and resolves `owner_sort.<param>` to that sort's
/// canonical param var ([`type_param_vid_in_sort`]). Anchoring to `owner_sort` is
/// what makes the key hygienic — two unrelated sorts' `T` resolve to DISTINCT
/// VarIds, so the match cannot cross-collide (the fragility the retired short-name
/// compare papered over: "safe today only because the compare is scoped per
/// spec↔carrier triad"). `None` when `tid` is not a type-param occurrence, or names
/// a parameter `owner_sort` does not declare (a concrete leaf sort like `Int64`).
pub(super) fn typaram_ref_vid(
    kb: &KnowledgeBase,
    tid: TermId,
    owner_sort: Symbol,
) -> Option<VarId> {
    let name_sym = typaram_occurrence_sym(kb, tid)?;
    type_param_vid_in_sort(kb, owner_sort, name_sym)
}

/// The short name of a type-parameter reference (see [`typaram_occurrence_sym`]).
/// Retained for the carrier-SORT short-name extraction in
/// [`carrier_arg_provision_projection`] (a bare receiver's carrier NAME feeds the
/// separate short-name provision lookup — not the WI-600 identity-keyed param
/// match, which now goes through [`typaram_ref_vid`]).
pub(super) fn typaram_ref_short_name(kb: &KnowledgeBase, tid: TermId) -> Option<String> {
    typaram_occurrence_sym(kb, tid).map(|s| short_name_of(kb.local_name_of(s)).to_string())
}

/// WI-210/WI-224 — find the unique impl operation symbol for a spec-op
/// call. Thin wrapper over `dispatch_spec_op_with_tree` that drops the
/// `ResolvedRequiresNode`. Callers that need the tree (WI-228: requirement
/// projection for Pin-now) call `dispatch_spec_op_with_tree` directly.
pub fn find_unique_impl_op(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    op_short_sym: Symbol,
    enclosing_requires: &[RequiresEntry],
) -> DispatchOutcome {
    dispatch_spec_op_with_tree(kb, subst, spec_sort, op_short_sym, enclosing_requires).0
}

/// WI-228 — same as `find_unique_impl_op` but also returns the full
/// `ResolvedRequiresNode` (when one was produced). The tree carries the impl's
/// sub_resolutions for conditional instances, which the requirement-
/// insertion pass turns into nested `Dictionary` IR.
///
/// Delegates to `dispatch_spec_op_cached` — the legacy compat path
/// (`find_unique_impl_op`) thus also benefits from WI-226 Cache B.
pub fn dispatch_spec_op_with_tree(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    op_short_sym: Symbol,
    enclosing_requires: &[RequiresEntry],
) -> (DispatchOutcome, Option<ResolvedRequiresNode>) {
    // Compat entry — no call-site receiver, so no carrier discrimination, no
    // call-site σ context (WI-829 gate off — keeps the coarse defer trigger), and no
    // call-site bracket, hence no selection (WI-841).
    dispatch_spec_op_cached(
        kb,
        subst,
        spec_sort,
        op_short_sym,
        enclosing_requires,
        None,
        None,
        &[],
        &[],
    )
}

/// WI-226 — cached variant of `dispatch_spec_op_with_tree`. Repeated
/// spec-op calls at the same `(SortGoal, scope)` hit the per-KB memo
/// (`kb.resolve_cache`) and skip the SLD walk. The defer-trigger
/// check (which depends on `subst` via `find_requires_slot`) runs
/// uncached because it reads typer-side vars; the rest is keyed on the
/// canonicalized goal + scope.
///
/// WI-829: `disambig` is the call-site σ context (present on the classification
/// path, `None` on the compat wrapper). It σ-gates ONLY the direct defer trigger
/// below — a sole coarse cover whose compound element σ-DISAGREES no longer
/// short-circuits to `Deferred`, so control falls through to `resolve_at_goal` and
/// the deeper dictionary is constructed. The gate runs BEFORE the memo, and only
/// the (σ-independent) `resolve_at_goal` result is cached, so σ never taints the
/// cache key.
/// WI-869 — what a dispatch search failed on, carried out of the resolution that saw
/// it. Pre-rendered rather than kept as a `SortGoal` for the reason
/// `RequirementRefusal` gives: a goal's `TermId`s are arena-refcounted and a
/// diagnostic outlives the resolution.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DispatchFailure {
    /// The goal, as `format_goal` rendered it — a CONDITION when a conditional
    /// provision is what declined.
    pub goal_text: String,
    /// The repair the search itself proposed. Empty when it had none.
    pub hint: String,
}

/// WI-869 — render a [`TypeError::DispatchNoMatch`]'s failure as a trailing clause, or
/// nothing. One owner because two renderers use it — the `TypeError` message and the
/// `LoadError` lowering — and a check whose two texts disagree is worse than one that
/// says less (WI-886).
pub(super) fn render_unmet(unmet: &Option<Box<DispatchFailure>>) -> String {
    match unmet {
        Some(f) if f.hint.is_empty() => format!(" \u{2014} unresolved: {}", f.goal_text),
        Some(f) => format!(" \u{2014} unresolved: {} ({})", f.goal_text, f.hint),
        None => String::new(),
    }
}

pub fn dispatch_spec_op_cached(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    op_short_sym: Symbol,
    enclosing_requires: &[RequiresEntry],
    carrier: Option<GoalCarrier>,
    disambig: Option<&SigmaCtx>,
    // WI-841 (058 §4.5): the call's explicit provider selections. Rides in the memo
    // KEY as well as into the resolution — a pin changes which impl a goal resolves
    // to, so two calls on one goal that pin differently must not share an entry.
    selected: &[InstanceSelection],
    // WI-20260918-CKD4J — the enclosing operation's own `requires`, for SUB-goals only
    // ([`ResolutionScope::sub_goal_requires`]). In the memo key: it changes the answer.
    sub_goal_requires: &[RequiresEntry],
) -> (DispatchOutcome, Option<ResolvedRequiresNode>) {
    // Direct defer trigger: a spec that is a *direct* `requires` of the
    // enclosing sort (i.e. present in `enclosing_requires`) is dispatched
    // at runtime from the threaded requirement value. The typer arm
    // (WI-239) handles transitive (nested) reachability separately via
    // `find_requires_location` before reaching here, so this trigger only
    // needs the direct chain. The compat API (`find_unique_impl_op`,
    // exercised by the WI-221 tests with synthetic chains) relies on it.
    // WI-829: `disambig` σ-gates the sole cover here exactly as
    // `find_requires_location` did on the classification path — otherwise the
    // shallow-vs-deep compound cover would re-defer here after the tree walk
    // refused it, and construction would never run.
    // WI-841: a spec the CALL SITE pinned does not defer. `Deferred` means "the
    // enclosing frame's dictionary answers this", which is the same forward
    // `resolve_inner`'s `FromScope` step makes and which explicit selection outranks
    // for the same reason (§4.1 tier 1). Without this the pin would be swallowed
    // before any resolution ran, and `f[Spec = W](…)` inside a sort that itself
    // `requires Spec` would mean nothing — the one place selection is most wanted.
    let pinned_here = pinned_witness_for(kb, selected, spec_sort).is_some();
    if !pinned_here
        && !enclosing_requires.is_empty()
        && find_requires_slot(kb, subst, spec_sort, enclosing_requires, disambig).is_some()
    {
        return (DispatchOutcome::Deferred, None);
    }
    // WI-350: `carrier` rides inside the goal so it participates in the
    // resolve-cache key (a `List` call and a `LogicalStream` call on the
    // same `Stream[T = Int]` goal must not share a memo entry) and reaches
    // `collect_provides_candidates`' impl-sort filter.
    let goal = sort_goal_from_subst(kb, subst, spec_sort, carrier);
    // WI-507: `op_short_sym` is part of the key — `resolve_at_goal`'s outcome
    // resolves the impl op via `sort_ops_lookup(impl_sort, op_short_sym)`, so
    // two carrier-only ops on the same carrier (`clear(s)` / `insert(s, x)` on
    // a `MutableStack`) share a goal but must NOT share a memo entry.
    // WI-829: the σ-present and σ-less regimes can resolve the same (op, goal,
    // scope) differently (the σ-precise scope cover), so `disambig.is_some()`
    // rides in the key to keep their memo entries apart.
    //
    // But the key is NOT sufficient on the σ-present path when the goal is
    // NON-GROUND: `resolve_at_goal` now reads `ctx.subst` (via `sigma_class`,
    // which chases vars NESTED inside a goal binding), and `sort_goal_from_subst`
    // stores only the shallow `resolve_as_value` — it does not deep-resolve a
    // nested `Global`. So two σ-present dispatches sharing this goal `TermId` but
    // binding a nested var differently would resolve differently yet collide on
    // the key. A FULLY-GROUND goal has nothing for σ to chase, so its result is
    // determined by the key and stays cacheable; a non-ground σ-present goal
    // bypasses the memo (recomputed, always sound). Every σ-less caller (the
    // compat wrapper, the pre-WI-829 behaviour) keeps the cache unconditionally.
    //
    // WI-841: the SELECTIONS ride in the key. A pin changes which impl the very same
    // goal resolves to, so two sites that pin differently — or one that pins and one
    // that does not — must not share an entry. Whole list, not `is_some()`: unlike
    // `disambig`, its CONTENT decides the answer.
    // WI-20260828-EKWDC: the CARRIER'S ARGUMENTS are held to the same test, because they
    // are now part of what makes a goal ground. `carrier` used to be a `Symbol` — ground
    // by construction — so `bindings` alone answered "has this goal anything for σ to
    // chase"; an argument is a `TermId` off the receiver's inferred type and can be an
    // unresolved var, which the paragraph above is precisely about. Reading only the
    // bindings would leave a goal the memo treats as determined while its resolution
    // still depends on σ.
    let cacheable = disambig.is_none()
        || goal
            .bindings
            .iter()
            .chain(goal.carrier.iter().flat_map(|c| c.args.iter()))
            .all(|(_, v)| type_value_is_ground(kb, *v));
    let key = (
        op_short_sym,
        goal.clone(),
        enclosing_requires.to_vec(),
        disambig.is_some(),
        selected.to_vec(),
        sub_goal_requires.to_vec(),
    );
    if cacheable {
        if let Some(cached) = kb.resolve_cache.borrow().get(&key) {
            return cached.clone();
        }
    }
    let result = resolve_at_goal(
        kb,
        &goal,
        op_short_sym,
        enclosing_requires,
        disambig,
        selected,
        sub_goal_requires,
    );
    if cacheable {
        kb.resolve_cache.borrow_mut().insert(key, result.clone());
    }
    result
}

/// Resolve a pre-built `SortGoal` to a `(DispatchOutcome, Option<ResolvedRequiresNode>)`.
/// Shared body of `dispatch_spec_op_with_tree` and `dispatch_spec_op_cached`
/// — they differ only in pre-check (defer trigger) and memoization.
///
/// WI-829: `disambig` is the call-site σ context (`Some` on the classification
/// path, `None` on the compat wrapper). When present it makes the scope
/// `FromScope` check σ-precise, so a shallow-vs-deep compound frame entry no
/// longer coarse-covers a DEEPER goal and re-defers it — the outer goal
/// constructs its deeper dictionary while a sub-goal that σ-AGREES with the
/// frame entry still resolves `FromScope`. Without it (`None`) the head-only
/// leniency the WI-827 dispatch path relied on is preserved.
pub(super) fn resolve_at_goal(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    op_short_sym: Symbol,
    enclosing_requires: &[RequiresEntry],
    disambig: Option<&SigmaCtx>,
    // WI-841 (058 §4.5): the call site's explicit selections, for `resolve`'s step 0.
    selected: &[InstanceSelection],
    // WI-20260918-CKD4J — [`ResolutionScope::sub_goal_requires`].
    sub_goal_requires: &[RequiresEntry],
) -> (DispatchOutcome, Option<ResolvedRequiresNode>) {
    let scope = ResolutionScope {
        available_requires: enclosing_requires,
        sigma: disambig,
        selected,
        sub_goal_requires,
    };

    // No matching candidate ⇒ NoCandidates (permissive fall-through).
    // An unrelated `SortProvidesInfo` record for the same spec — e.g.
    // `Eq[T = Type]` when the goal is `Eq[T = Int]` — must not gate
    // dispatch: those are distinct specifications about distinct
    // sorts. Per-binding matching in `collect_provides_candidates` is
    // the only mechanism that decides relevance.
    // WI-827/WI-829: `disambig` (the call-site σ, `None` on the compat path)
    // rides into candidate matching and the scope cover check so the whole
    // dispatch resolution is σ-consistent — a σ-disagreeing frame entry does not
    // coarse-cover an empty-candidate goal, and the compound sole-cover gate the
    // caller applied is not re-widened here.
    let candidates = collect_provides_candidates(kb, &goal, disambig);
    if candidates.is_empty() {
        for ar in scope.available_requires {
            if ar.required_sort == goal.spec_sort
                && requires_entry_covers_goal(kb, ar, &goal, disambig)
            {
                return (DispatchOutcome::Deferred, None);
            }
        }
        return (DispatchOutcome::NoCandidates, None);
    }

    let mut stack: Vec<SortGoal> = Vec::new();
    // Two `None`s: this IS the goal the call made, so there is no enclosing provider
    // whose locality could narrow it (WI-857) and no slot of one to pin (WI-870) —
    // `scope.selected` is the only pin that reaches this level.
    // WI-861: and [`DefaultRung::Consult`], because this IS the unselected DISPATCH 058
    // §3.2's ladder is about — no named slot, so silence here is silence.
    match resolve_inner(
        kb,
        &goal,
        &scope,
        &mut stack,
        None,
        None,
        DefaultRung::Consult,
    ) {
        ResolutionResult::Resolved(tree) => match &tree {
            ResolvedRequiresNode::Leaf { impl_sort, .. }
            | ResolvedRequiresNode::Conditional { impl_sort, .. } => {
                // WI-240 — direct table lookup. The load-time
                // `build_sort_ops_table` already resolved impl-override
                // vs spec-default for `(impl_sort, op_short)`; no
                // string concatenation, no try/catch fallback here.
                match kb.sort_ops_lookup(*impl_sort, op_short_sym) {
                    Some(s) => (DispatchOutcome::Unique(s), Some(tree)),
                    None => (DispatchOutcome::NoMatch { unmet: None }, None),
                }
            }
            ResolvedRequiresNode::FromScope { .. } => (DispatchOutcome::Deferred, None),
            // WI-857: `Unavailable` is only ever a SPEC-half SLOT inside a resolved
            // tree, never a whole resolution — `resolve_inner` returns the failure
            // itself at the top level and only substitutes the marker when placing a
            // sub-goal. Reaching here would mean a dispatch pinned no impl at all,
            // which `NoMatch` is the answer to.
            ResolvedRequiresNode::Unavailable { .. } => {
                (DispatchOutcome::NoMatch { unmet: None }, None)
            }
        },
        // WI-869: the failure rides out with the verdict — for a conditional provision
        // the goal it names is the unmet CONDITION, which is the only thing that
        // explains the refusal. WHOLE, hint included: the hint is the repair.
        ResolutionResult::NoMatch {
            goal_text, hint, ..
        } => (
            DispatchOutcome::NoMatch {
                unmet: Some(Box::new(DispatchFailure { goal_text, hint })),
            },
            None,
        ),
        // WI-843: the tie is FORWARDED, not restamped. Tier 3's diagnostic is the
        // only one the author now gets, and only `resolve_inner` knows which level
        // tied — substituting `goal.spec_sort` here is exactly the bug that made a
        // conditional witness's subgoal tie report the outer spec.
        ResolutionResult::Ambiguous { tie, .. } => (DispatchOutcome::Ambiguous(tie), None),
        // A CYCLE has its own account, and `describe_resolution_failure` is its owner —
        // "construction is cyclic: a -> b -> c" instead of a bare "no impl matches".
        cyclic @ ResolutionResult::Cyclic { .. } => {
            let goal_text = format_goal(kb, goal);
            let hint = describe_resolution_failure(kb, &cyclic);
            (
                DispatchOutcome::NoMatch {
                    unmet: Some(Box::new(DispatchFailure { goal_text, hint })),
                },
                None,
            )
        }
    }
}

/// WI-210 — does a per-call binding value match a candidate's binding value, for
/// DISPATCH? [`types_lesseq`] first; failing that, a coarse HEAD match through
/// [`sort_sym_of_term`] — two bare sorts by symbol, and two STRUCTURED values by their
/// functor ALONE: `List[T = Int64]` matches `List[T = String]`, and any two effect rows
/// match whatever their labels.
///
/// COARSE BY DESIGN, and load-bearing (WI-20260923-N3W68 #7, which found this doc
/// describing only the bare-sort case, as two spellings of one nominal sort — the deep
/// `sort_ref(name: …)` wrapper it named is retired, WI-361). MEASURED with a probe on the
/// structured case of the fallback: it answered `true` 337 times across the workspace
/// suite, in about fifty tests — effect rows (`{{}} vs {?_, ?_}`) in the stream-combinator
/// dispatch, and same-base applications whose bindings differ by a flex vs a rigid
/// variable (`Wrap[A = ?DT] vs Wrap[A = DT]`) in the σ deferral cover. The finer verdicts
/// are layered ON TOP where they matter — [`entry_sigma_verdict`] for the deferral cover
/// (WI-613), [`match_impl_param`] for slot reconciliation (WI-827), and a PARAMETERIZED
/// candidate never reaches this match from [`match_candidate_against_goal`], whose arm (2)
/// recurses into its bindings — so a `true` here is not binding-level agreement, and a
/// caller that needs that must not read it as such. Tightening the structured arm is a
/// design change with that census as its blast radius, not a correction of this one.
pub(super) fn dispatch_values_match(
    kb: &mut KnowledgeBase,
    per_call_value: TermId,
    candidate_value: TermId,
) -> bool {
    // A universally-quantified candidate matches any per-call value. The
    // fact-loading path stores type-params as `Term::Ref`, the op-signature
    // path as `Term::Var`; both shapes mean "for any T."
    //
    // The CANDIDATE side only. This function also owns half of WI-824's rule —
    // a per-call RIGID does not match a CONCRETE candidate — but owns it
    // EMERGENTLY, via `types_lesseq` refusing a var against a sort and
    // `sort_sym_of_term` finding no symbol for a var; nothing below states it.
    // A var-tolerant widening of either would silently re-open that half (the
    // `Leaf` candidate would start matching an abstract `Desc[T = FT]` goal),
    // which the sibling guard in `match_candidate_against_goal` arm (2) cannot
    // catch — it sees only parameterized candidate heads.
    if is_type_param_value(kb, candidate_value) {
        return true;
    }
    // WI-335: dispatch decisions are independent of each other (dispatch
    // values are typically nominal sort_refs; row reasoning is rare).
    // Each call gets a fresh scratch substitution.
    let mut subst = Substitution::new();
    if types_lesseq(kb, &mut subst, per_call_value, candidate_value) {
        return true;
    }
    let per_call_sym = sort_sym_of_term(kb, per_call_value);
    let candidate_sym = sort_sym_of_term(kb, candidate_value);
    match (per_call_sym, candidate_sym) {
        (Some(a), Some(b)) => a == b,
        _ => false,
    }
}

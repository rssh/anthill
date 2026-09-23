//! Seeding a call's type arguments and requirement slots: written brackets, slot
//! selections, named-slot binding and forwarding, and their validation.

use super::*;

/// Full operation info for type checking: params with types, return type, effects.
pub(super) struct OperationInfoFull {
    pub(super) params: Vec<(Symbol, Value)>, // (param_name, param_type); WI-341 carrier-agnostic
    pub(super) return_type: Value,           // WI-341 carrier-agnostic
    pub(super) effects: Vec<Value>,
    /// Operation-level type parameters in declaration order, as
    /// `(name, the parameter's own logical variable)` pairs. WI-849 — a `Var`,
    /// not a `Term::Var` TermId; see [`crate::kb::op_info::OpInfoRecord::type_params`].
    /// A reader that needs a term carrier (to unify against, or to walk with the
    /// term-typed `walk_type_deep`) allocs `Term::Var(v)`, which hash-conses to
    /// the identical TermId the loader built.
    pub(super) type_params: Vec<(Symbol, Var)>,
    /// WI-539: precondition (`requires`) clauses, for call-site contract checking
    /// (proposal 050 "operation call" rule). Carries the auto-inferred
    /// `EffectsRuntime[…]` and spec `Spec[C=T]` requires too; the call-site check
    /// filters to the VALUE goals (`is_value_precondition_clause`) — spec/typeclass
    /// requires are dispatched / coverage-checked elsewhere (WI-343 / WI-325).
    pub(super) requires: Vec<Value>,
}

/// WI-849 — an operation type parameter as the TERM carrier the term-typed APIs take
/// (`walk_type_deep`, `TermIdView`, `unify_types`). The table itself holds each
/// parameter's `Var`, which is its whole content; this is the one-line bridge for a
/// reader that needs it wrapped.
///
/// NOT a lossy re-materialization: the term is hash-consed, so this returns the
/// IDENTICAL `TermId` the loader built for that parameter. Two consequences the callers
/// depend on — `unify_types`' `Value::Term{x} == Value::Term{y}` identity fast-path
/// stays reachable, and the effect-row-parameter test in cpp-gen still sees one variable
/// in both the row and the table.
///
/// Looks the term up WITHOUT refcounting it (WI-849 review): every caller is a per-node
/// typer path that merely reads a parameter it already holds via the `OperationInfo`
/// record, and `alloc`'s increment-on-hit would inflate those refcounts monotonically
/// across a type-check, pinning the slots forever. The var term is alive for the same
/// reason it is readable — the fact this record was decoded from holds it — so the
/// `alloc` fallback is for a KB where that fact has since been retracted, not a case any
/// caller here is expected to hit.
/// WI-20260904-02ERR: interning a `Term::Var`. This used to be the ONLY way a variable
/// could reach a type slot, which is why it was reached unconditionally for brand-new
/// `VarId`s its own doc said no caller was expected to hit. A type slot now takes
/// `KnowledgeBase::type_var_child` instead, and this remains only for the callers that
/// genuinely want the INTERNED term (a stored/DeBruijn spine).
pub(super) fn type_param_var_term(kb: &mut KnowledgeBase, v: Var) -> TermId {
    kb.alloc_or_find_var_term(v)
}

/// Look up complete OperationInfo for a functor.
/// Thin wrapper over `kb::op_info::lookup_operation_info` for the
/// fields the typer cares about (params + return + effects, no body).
pub(super) fn lookup_operation_info_full(
    kb: &KnowledgeBase,
    functor: Symbol,
) -> Option<OperationInfoFull> {
    let rec = crate::kb::op_info::lookup_operation_info(kb, functor)?;
    Some(OperationInfoFull {
        params: rec.params,
        return_type: rec.return_type,
        effects: rec.effects,
        type_params: rec.type_params,
        requires: rec.requires,
    })
}

/// Seed `subst` from `op[bindings](args)` call sites: named bindings
/// match by name, positional by declaration order. Names that don't
/// match any declared type-param produce a `NoSuchTypeParam` error so
/// the user sees the typo rather than a silent return-type Var leaking
/// to the caller.
///
/// WI-839 — EVERY binding is now accounted for, and the two ways one used to
/// vanish were both "the callee has nothing to bind it to":
///   * `op.type_params.is_empty()` short-circuited the whole list, so a bracket on a
///     param-less callee (`plain[Bogus = Int64](n)`) — and on a callee whose params
///     are its enclosing SORT's rather than its own (`Box.mk[Bogus = Int64](5)`) —
///     loaded clean. Deleted: an unmatched NAMED key is `NoSuchTypeParam` whatever
///     the callee declares, which is exactly the diagnostic the non-empty case
///     already gave.
///   * an over-applied POSITIONAL `continue`d. It gets `ExcessCallTypeArgs` — its own
///     variant, because an unmatched positional has no key to put in a message.
///
/// A callee that is not an operation at all never gets here — `check_apply_iter`
/// refuses its bracket before classification (`TypeArgsOnNonOperation`).
///
/// WI-841 (058 §9 phase 2) added the other two things a key can name, so the bracket
/// is now a REQUIREMENT-SLOT channel as well as a type-argument one:
///   * rung (1) spans TWO SCOPES — the operation's declared parameters **and its
///     enclosing sort's**. Measured before: `Box.mk[T = String](5)` on `sort Box {
///     sort T = ? }` was `unknown type-param 'T'`, so §5.3's construction-site
///     selection had nothing to stand on. The two scopes never both answer: a
///     colliding pair is refused at the DECLARATION (`check_op_type_param_shadowing`,
///     WI-840), which is why appending one list to the other cannot capture silently.
///   * rung (2) is a spec SHORT NAME among the callee's anonymous requirement slots
///     ([`resolve_call_type_arg_targets`]).
/// A key that answers neither is `NoSuchTypeParam`, exactly as before.
///
/// The SELECTIONS a bracket makes are RETURNED, not applied here: their consumer is
/// [`resolve`]'s step 0 (§4.5), reached later in this same `check_apply_iter` through
/// the dispatch and dict-build paths. A named slot's binding does BOTH — it unifies
/// the parameter (so the witness is part of the type, §4.7) and selects the provider.
///
/// LIMIT, stated because the doc above would otherwise overclaim: `unify_types`'
/// verdict is discarded here, as it is at every seeding site (WI-367 / WI-379 depend
/// on a failed unify against an already-pinned slot being a no-op). What
/// [`resolve_call_type_arg_targets`] guarantees is that each written binding reaches a
/// DISTINCT declared parameter — so no binding is contradicted by a SIBLING binding.
/// A binding contradicted by an ARGUMENT or by the expected type is caught downstream,
/// by the WI-385/WI-836 conformance checks, not here.
///
/// WI-20260911-7TN1Q — ONE EXCEPTION, and it is narrow by construction: a value that
/// MENTIONS the parameter it binds. The occurs check refuses that binding, and a
/// discarded `false` made the refusal silent, so the leg below reads the verdict for
/// that one fault and reports it. The already-pinned case WI-367 / WI-379 rely on is
/// untouched — it is gated out by the `prior` read. See the comment at the site.
pub(super) fn seed_op_type_args(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    op: &OperationInfoFull,
    occ: &Rc<NodeOccurrence>,
    fn_sym: Symbol,
    span: Option<Span>,
) -> Result<Vec<InstanceSelection>, TypeError> {
    let Some(type_args) = call_type_args_of(occ) else {
        return Ok(Vec::new());
    };
    let declared = call_bracket_scopes(kb, op, fn_sym);
    // POSITIONALS reach the operation's OWN parameters only — `declared`'s first
    // segment. See `resolve_call_type_arg_targets`.
    let positional_limit = op.type_params.len();
    let slots = callee_requirement_slots(kb, fn_sym);
    let targets = resolve_call_type_arg_targets(
        kb,
        type_args,
        &declared,
        positional_limit,
        &slots,
        fn_sym,
        span,
    )?;
    // One target per binding, in order — nothing is skipped now, which is what lets
    // this be a plain `zip` rather than an index carried back out of the resolver.
    let mut selections: Vec<InstanceSelection> = Vec::new();
    let mut concrete: Option<std::collections::HashSet<Symbol>> = None;
    for (target, (key, value)) in targets.into_iter().zip(type_args) {
        if let Some(param_var) = target.param() {
            let param = type_param_var_term(kb, param_var);
            // WI-342 S4b: a type-arg is a carrier-agnostic `Value` (`Value: TermView`),
            // so unify it directly — a value-in-type arg (`Value::Node`) unifies
            // cross-carrier through the typer's view dispatch, no re-ground.
            //
            // WI-20260824-6RXGD — EXCEPT A CLOSED LITERAL, which is re-grounded first.
            // The unify succeeds either way; what fails is READING the binding back.
            // A callee whose RETURN type mentions the parameter
            // (`field_access[R, Name](…) -> FieldOf[T = R, Name = Name]`) is term-backed,
            // so the binding is resolved by the `TermId` deep σ-walk, and that walk STOPS
            // at a non-`Term` binding (WI-394) — leaving `Name` an unresolved var and the
            // return type a residual (`FieldOf[T = P, Name = ?Name]`) for every spelling a
            // caller can write. `synthesize_field_access` already grounds its own `Name`
            // argument for exactly this reason and says so at that site; this is the same
            // fix for the channel a PERSON writes, which had no route to it at all. (The
            // `Value`-level walk the apply resolves a return type through now SPLICES such a
            // binding back — `splice_non_term_bindings` — so that stop no longer strands it;
            // the re-grounding is kept, and dropping it is unmeasured.)
            //
            // ONLY A CLOSED LITERAL, and the narrowness is the point. The carrier rule
            // (`Loader::type_expr_to_value`) mints a denoted-bearing type as a
            // `Value::Node` because a denoted can carry POISON — a value occurrence
            // referring to a parameter, `Modify[c]`. A literal carries none, which is the
            // argument `synthesize_field_access` makes. Re-grounding at the LOADER instead
            // (`TypeExpr::Denoted`, which is emitted for literals ONLY) was measured and
            // REJECTED: it silently un-gates `wi366_value_in_type_facts_test::
            // provides_block_value_in_type_spec_loads_without_panic`, because
            // `lower_value_or_gate` decides by whether the value is term-representable —
            // so `provides Foo[Int64, 3]` would stop reporting the WI-366 "not yet
            // resolved" diagnostic and start silently accepting an unresolved clause.
            let grounded = ground_literal_denoted(kb, value);
            let written = grounded.as_ref().unwrap_or(value);
            // WI-20260911-RS2G4: a BARE parametric sort written as a bracket value
            // (`[T = List]`) erased whatever an argument said about its element. See
            // [`expand_written_bracket_value`]; the receiver spelling runs the same
            // expansion at [`seed_receiver_type_args`], one rule at both writers.
            let expanded = expand_written_bracket_value(kb, written, target.slot_spec().is_some());
            let bound = expanded.as_ref().unwrap_or(written);
            // WI-20260911-7TN1Q — THE ONE FAULT THE DISCARD BELOW MUST NOT SWALLOW. A
            // value that MENTIONS the parameter it binds (`Box.empty[T = Option[T = T]]()`
            // inside `sort Box[T]`) is refused by [`occurs_in`]'s `Term::Ref` arm, and a
            // discarded `false` would make that refusal SILENT: the call would type at
            // whatever the context wanted, which is the WI-20260911-RS2G4 defect one
            // channel over. It aborted before the arm existed, so "loads clean" is not the
            // behaviour being preserved here.
            //
            // THREE READS, and the order is the whole content. `prior` and `mentions` are
            // taken BEFORE the unify because the unify is what consumes them; the verdict
            // decides, and the other two say WHICH fault a `false` is:
            //   * `prior` SOME — the parameter was already pinned, so a `false` is a
            //     disagreement with that pin and the discard stands. WI-367 / WI-379
            //     depend on exactly that being a no-op (see the LIMIT in this function's
            //     doc), and this leg does not touch it.
            //   * `mentions` — asked as a FACT rather than inferred from `prior` alone,
            //     because `bind_resolved` also answers `false` on the STICKY contradiction
            //     flag, which an earlier binding in this same expression can have set. A
            //     `false` that is neither keeps today's discard rather than getting a
            //     message invented for a case nothing drives.
            // `mentions` is TRUE for the identity binding `[T = T]` too (the value IS the
            // var), and that is not a fault: `unify_types` walks both sides and returns on
            // its identity fast-path, so the verdict gate is what keeps the control
            // loading. That control is a row of `wi_7tn1q_occurs_check_sort_alias_test`.
            let (prior, mentions) = match param_var {
                Var::Global(vid) => (
                    subst.resolve_as_value(vid).is_some(),
                    occurs_in_view(kb, vid, bound),
                ),
                // `call_bracket_scopes` publishes a `Var::Global` per parameter; a
                // non-global would be a stored DeBruijn spine reaching a call site.
                _ => (false, false),
            };
            let agreed = unify_types(kb, subst, &TermIdView(param), bound);
            if !agreed && !prior && mentions {
                // BY THE DECLARED NAME, which is the bare spelling the author wrote
                // (`declared` is where every `Param` / `NamedSlot` target's var came
                // from, so the lookup is total); the written KEY is the fallback for a
                // positional binding whose var no scope claims — a shape
                // `resolve_call_type_arg_targets` does not produce.
                let param_name = declared
                    .iter()
                    .find(|(_, v)| *v == param_var)
                    .map(|(s, _)| *s)
                    .or(*key)
                    .map(|s| kb.local_name_of(s).to_string());
                // LOUD IN BOTH PROFILES (found by `/code-review`). The tripwire is a
                // `debug_assert`, but the REFUSAL is not: the binding has already been
                // rejected, so returning here would type the call at whatever the context
                // wants — the silent wrong answer this whole leg exists to stop. A name
                // that cannot be recovered degrades the message, never the verdict.
                debug_assert!(
                    param_name.is_some(),
                    "seed_op_type_args: bracket target {param_var:?} names no declared \
                     parameter and the binding wrote no key"
                );
                let name = param_name.unwrap_or_else(|| format!("{param_var:?}"));
                return Err(bracket_binding_mentions_its_parameter(
                    kb,
                    "a type argument",
                    &name,
                    value,
                    fn_sym,
                    span,
                ));
            }
        }
        let Some(spec_sort) = target.slot_spec() else {
            continue;
        };
        // WI-20260911-TX0G6: the written binding's checks have ONE owner, shared with the
        // receiver spelling ([`seed_receiver_type_args`]). A NAMED slot's binding is also
        // a type argument (`target.param()` is its binder), which is what lets a value
        // naming an enclosing slot forward; an ANONYMOUS one binds no parameter and may
        // not.
        let Some(witness) = validate_written_selection(
            kb,
            fn_sym,
            spec_sort,
            value,
            target.param().is_some(),
            &mut concrete,
            span,
        )?
        else {
            continue;
        };
        // WI-870: and what the value's OWN bracket bound on that witness (§3.3).
        let slots = witness_value_slot_selections(kb, fn_sym, witness, value, span)?;
        push_selection(kb, &mut selections, spec_sort, witness, slots, fn_sym, span)?;
    }
    Ok(selections)
}

/// WI-20260911-7TN1Q — the refusal BOTH bracket channels render when a written binding
/// for a type parameter MENTIONS that parameter: `Box.empty[T = Option[T = T]]()` and
/// `Box[T = Option[T = T]].empty()`, each written inside `sort Box[T]`. σ would get
/// `?T := Option[T = Ref(Box.T)]`, whose `Ref` the SortAlias chain resolves back to `?T`
/// itself — a cycle [`walk_type_deep`] chases until the stack ends, which is what both
/// spellings did before [`occurs_in`] gained its `Term::Ref` arm.
///
/// ONE MESSAGE, because it is one fault. `channel` is the only thing the two spellings do
/// not share — which bracket the author wrote — so the remaining bytes are identical, as
/// 035's interchangeable forms require. It names the PARAMETER and the VALUE because
/// "cannot unify" would name neither.
///
/// AND IT SAYS WHY, because the refusal is a REPRESENTATION limit and not a malformed
/// program (found by `/code-review`). `Box.empty[T = List[T = T]]()` — "the same operation
/// at the instance whose element is a `List` of my own `T`" — is a well-formed intent; it
/// is unexpressible only because a bracket binds the ENCLOSING sort's canonical parameter
/// variable (`call_bracket_scopes` spans that scope, and `sort_type_params_as_pairs`
/// publishes one var per parameter), so the callee's `T` and the enclosing instance's `T`
/// ARE one variable. A message asserting only "does not mention itself" sends the author
/// looking for their own mistake. Giving the callee's parameters fresh variables is what
/// would make the family expressible, and that is a design change, not a diagnostic.
///
/// `#[track_caller]` so WI-510's `site` keeps reporting the CALLING seeding site rather
/// than this builder; `here()` chains through.
#[track_caller]
fn bracket_binding_mentions_its_parameter(
    kb: &KnowledgeBase,
    channel: &str,
    param: &str,
    written: &Value,
    fn_sym: Symbol,
    span: Option<Span>,
) -> TypeError {
    TypeError::Other {
        site: TypeError::here(),
        span,
        context: TypeErrorContext::OperationTypeParams { op_name: fn_sym },
        expected: format!(
            "{channel} for '{param}' that does not mention '{param}' itself (the bracket \
             binds the ENCLOSING sort's own '{param}', so a value mentioning it would be \
             cyclic — a call at another instance cannot be written in terms of this one)"
        ),
        actual: type_display_name_value(kb, written),
    }
}

/// WI-20260911-RS2G4 (058 rule 1, the SORT half of the binding) — a form-(3) COMPANION
/// RECEIVER's bracket BINDS the enclosing sort's type parameters for this call, exactly
/// as the callee's own bracket already does through [`call_bracket_scopes`].
///
/// ONE RULE, TWO SPELLINGS. `Map.size[K = Bool, V = Bool](m)` and
/// `Map[K = Bool, V = Bool].size(m)` write the same thing in the two places proposal 035
/// lists as interchangeable, and only the first was heard: `call_bracket_scopes` spans
/// the enclosing sort's params, [`seed_op_type_args`] binds the sort's CANONICAL var, and
/// the signature's `Option[T = T]` / `Map[K = K, V = V]` sees it. The receiver channel
/// (`recv_type`, WI-20260829-W6JH0) was read ONCE and LATE, and only when the declared
/// return was the receiver's own sort — so on every OTHER member the bracket was
/// validated for parameter NAMES and then dropped, which is a silent wrong answer rather
/// than a missing feature: with nothing else carrying `T`, `Box[T = Int64].empty()` in an
/// `Option[T = Letter]` position typed as whatever the context wanted.
///
/// EARLY — before the WI-424 rigid fill and the WI-367 carrier pass — for three reasons,
/// in order of force:
///  * form (3) then reads EXACTLY as the callee bracket, including its diagnostics. The
///    rows `Box.empty[T = Int64]()`, `Map.size[…](…)`, `Map.put[…](…)` refuse at
///    `op-return` / `op-type-params` / `op-arg`; the receiver spelling now refuses at the
///    same site with the same bytes, which is what keeps 035's three forms one meaning.
///  * a WRITTEN receiver must beat WI-424's IMPLICIT rigid fill (WI-1082: a written slot
///    is never rewritten). A sibling call at another instance — `Box[T = Int64].empty()`
///    inside `sort Box[T]` — types at `Int64`; seeding after the fill would refuse it
///    against the enclosing instance's rigid.
///  * the W6JH0 arm stays as the RESULT rule for a BARE self-sort return (`empty() ->
///    Map`, WI-1082's untied return). It now finds the receiver already agreeing, reports
///    nothing new, and its merge is untouched.
///
/// GATED ON THE RECEIVER'S HEAD BEING THE CALLEE'S PARENT SORT. A receiver naming some
/// other sort binds none of this callee's parameters and is left to the W6JH0 arm exactly
/// as before; its parameter NAMES were already checked at load (`build_recv_type` →
/// `type_expr_to_child_inner`, WI-709/WI-710).
///
/// THE VERDICT IS READ, and it can only mean one thing. `subst` is fresh and
/// [`seed_op_type_args`] is the only earlier writer, so a `false` here is two WRITTEN
/// brackets binding one parameter differently — [`TypeError::ReceiverBracketConflict`],
/// the sibling of WI-839's `DuplicateCallTypeArg` one spelling over. Before this, the
/// receiver silently won.
pub(super) fn seed_receiver_type_args(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    occ: &Rc<NodeOccurrence>,
    parent: Option<Symbol>,
    fn_sym: Symbol,
    span: Option<Span>,
) -> Result<(), TypeError> {
    let Some(rt) = call_recv_type_of(occ).cloned() else {
        return Ok(());
    };
    let Some(parent) = parent else {
        return Ok(());
    };
    // The receiver must name the callee's OWN sort. A bare `Map` (no bracket at all)
    // writes no bindings, so it drops out of the loop below with nothing done and needs
    // no arm of its own.
    let Some((recv_base, written)) = sort_application_parts(kb, &rt) else {
        return Ok(());
    };
    if !same_sort_canonical(kb, recv_base, parent) {
        return Ok(());
    }
    // A BINDING THAT NAMES A REQUIREMENT SLOT IS VALIDATED HERE, by the callee leg's own
    // owner ([`validate_written_selection`]), so the two spellings refuse the same
    // bindings with the same bytes (WI-20260911-TX0G6). The σ-read producer
    // [`selections_from_slot_bindings`] still SELECTS the witness, reading the parameter
    // back out of σ, and re-runs check 1 on it. For a witness written here that second
    // check reads the same sort and agrees. It is the check an ARGUMENT's type reaches,
    // with no bracket written anywhere.
    //
    // THE HISTORY, one measured step at a time. RS2G4 left this leg with no checks at
    // all. WI-20260911-6B67S then refused two of the resulting silent shapes AT THE
    // PRODUCER: a value with no sort head (`[O = (Int64, Int64)]`, whose written `O` was
    // dropped and answered by a search) and a sort that provides nothing (`[O = NotOrd]`,
    // refused under a message claiming it provided). It left CHECK 3 open: `[O = ConcOrd]`,
    // a CONCRETE provider, loaded here and was refused by the callee. Its reason for not
    // closing that at the producer was that check 3 refuses a SPELLING, so it belongs to
    // the channel the author wrote. That reason holds, and this leg is such a channel. So
    // all three checks now run here, in the callee's order, and check 3 still does not run
    // at the producer.
    //
    // `concrete`: the §1.1 set, built lazily, so a receiver bracket that binds no slot
    // never pays for the scan. (The three corpora write no form-(3) call at all.)
    let mut concrete: Option<std::collections::HashSet<Symbol>> = None;
    for (param, var_term) in sort_type_params_as_pairs(kb, parent).iter() {
        // BY SHORT NAME. The receiver's keys are bare interns of the written spelling
        // and the declared list is qualified — the same split [`BindingKeyMatch`] closes
        // for two WHOLE types, asked here one key at a time exactly as
        // [`expand_foreign_sort_application`] asks it.
        let short = kb.local_name_of(*param).to_string();
        let Some((_, written_value)) = written.iter().find(|(k, _)| kb.local_name_of(*k) == short)
        else {
            continue;
        };
        let written_value = written_value.clone();
        // The receiver channel's own spelling of "does this key name a PROVIDER SLOT" —
        // see [`expand_written_bracket_value`] for the rule both channels obey. By NAME,
        // because the declared list is qualified and a slot's binder is a bare intern,
        // exactly as the key match one line above. The SPEC is read off the same record,
        // which is the record the callee's `named_slot_spec` reads, so a validation
        // failure below names the spec the callee spelling would.
        let slot = kb
            .named_requirement_slots(parent)
            .iter()
            .find(|slot| kb.local_name_of(slot.binder) == short)
            .copied();
        let binds_slot = slot.is_some();
        let expanded = expand_written_bracket_value(kb, &written_value, binds_slot);
        let value = expanded.unwrap_or_else(|| written_value.clone());
        // READ BEFORE THE UNIFY, because it is what decides WHICH fault a `false` is.
        // [`seed_op_type_args`] is the only earlier writer, so a parameter that is
        // already BOUND can only have been bound by the callee's bracket — that is the
        // two-bracket contradiction. A parameter that is still FREE is the OCCURS check —
        // the receiver's own value mentions the parameter it is binding (`Box[T = Box[T =
        // T]]` written inside `sort Box[T]`). Reporting that as "the callee bracket says
        // …" would name a bracket the author never wrote.
        // `sort_type_params_as_pairs` publishes a `Var::Global` term per parameter
        // (`published_param_var`), so the match is total in practice; a non-var term
        // would answer `None` and take the occurs arm, which is the honest reading of
        // "nothing was bound here".
        //
        // WI-20260911-7TN1Q (found by `/code-review`): `mentions` is READ, not inferred
        // from `prior` being `None`. This leg used to conclude "the value mentions the
        // parameter" from the verdict alone, and that is one cause too few —
        // `bind_resolved` also answers `false` on σ's STICKY contradiction flag
        // (`!subst.is_contradiction()` is its last line), which [`seed_op_type_args`] runs
        // FIRST on this same σ and can have set. A correct receiver binding of a free
        // parameter then rendered the cyclic-value message, blaming the author for a value
        // they did not write. The callee leg asks the same question the same way, and says
        // so at its site.
        let (prior, mentions) = match kb.get_term(*var_term) {
            Term::Var(Var::Global(vid)) => {
                let vid = *vid;
                (
                    subst.resolve_as_value(vid).cloned(),
                    occurs_in_view(kb, vid, &value),
                )
            }
            _ => (None, false),
        };
        if !unify_types(kb, subst, &TermIdView(*var_term), &value) {
            // AS WRITTEN, not as expanded: `[T = List]` is what the author typed, and
            // telling them their `List` disagrees with `List[T = ?T]` names a variable
            // this pass minted.
            match prior {
                // FREE, refused, and the value does NOT mention the parameter: the sticky
                // flag above. NOT a silent skip — the conflicting re-bind that set it also
                // recorded a `contradiction_details` entry, and [`enforce_member_tie`]
                // renders that as its own `OperationTypeParams` refusal naming the REAL
                // disagreeing pair. This leg adds no cycle message, which is what lets that
                // one be the one the author sees, instead of a second, wrong one.
                //
                // It FALLS THROUGH to the written binding's validation below rather than
                // `continue`ing past it (WI-20260911-TX0G6, found by `/code-review`): that
                // validation reads only the WRITTEN value, never σ, and the callee leg runs
                // it on the same verdict. No known program reaches this state (see
                // `wi_7tn1q_occurs_check_sort_alias_test`'s header), so this is reasoned,
                // not measured.
                None if !mentions => {}
                None => {
                    // WI-20260911-7TN1Q: the same bytes as the callee bracket's, one noun
                    // over — [`bracket_binding_mentions_its_parameter`].
                    let param_name = kb.local_name_of(*param).to_string();
                    return Err(bracket_binding_mentions_its_parameter(
                        kb,
                        "a receiver binding",
                        &param_name,
                        &written_value,
                        fn_sym,
                        span,
                    ));
                }
                Some(prior) => {
                    let callee = walk_type_deep_value(kb, subst, &prior);
                    return Err(TypeError::ReceiverBracketConflict {
                        span,
                        op: fn_sym,
                        param: *param,
                        receiver: written_value,
                        callee,
                    });
                }
            }
        }
        // AFTER the unify, as at the callee leg, whatever its verdict when it did not
        // return above. A written slot binding is always a type argument here (a receiver
        // key names one of the sort's parameters), so a value naming an enclosing slot
        // forwards. The selection itself is the σ-read producer's to push; this only
        // refuses what the callee spelling refuses.
        if let Some(spec_sort) = slot.and_then(|s| s.spec_base) {
            validate_written_selection(
                kb,
                fn_sym,
                spec_sort,
                &written_value,
                true,
                &mut concrete,
                span,
            )?;
        }
    }
    Ok(())
}

/// WI-20260911-RS2G4 — a bracket VALUE with a BARE parametric sort in it
/// (`Box.mine[T = List](box(v: [1]))`) ERASES what an argument says about the inner
/// element, in BOTH spellings. `[T = List]` seeds `?T := Ref(List)`; the argument's
/// `List[T = Int64]` then unifies against that through
/// [`unify_parameterized_with_sort_ref`], whose expansion variable is transient, so the
/// `Int64` reaches nothing and the result carries a bare `List` the context completes.
/// MEASURED: with the declared return `Option[T = List[T = String]]`, the bare call
/// refuses (`got Option[T = List[T = Int64]]`) and the bracketed one loads clean.
///
/// This is WI-1082's width-ignoring exploit shape re-entered through a bracket value, and
/// the repair is the one WI-374 already applies to the callee's PARAMETERS: mint a fresh
/// FLEXIBLE variable per unwritten slot, so `[T = List]` seeds `?T := List[T = ?f]`, the
/// argument binds `?f`, and a contradiction is loud. A value nothing else determines —
/// `Box.empty[T = List]()` — keeps loading, because `?f` is then filled by the context;
/// that is the partial-annotation reading, and it is a control.
///
/// THE EXPANSION ALONE IS NOT ENOUGH, which the ticket's own predicted mechanism assumed
/// it would be ("the argument binds `?f := Int64`"). Measured, it does not:
/// [`unify_parameterized_with_sort_ref`] RAW-BINDS the canonical parameter, so the
/// already-present bracket claim wins and the refinement is thrown away. That second site
/// is [`bind_or_refine_member_param`].
///
/// NO SELF-SORT EXEMPTION, deliberately, which is the one place this differs from
/// [`expand_foreign_sort_application`]'s signature use. That exemption keeps a member's
/// own sort riding the canonical channel for the §3 parametricity tie — a rule about a
/// SIGNATURE. A bracket value is not a signature: `Box[T = Box]` inside `sort Box` says
/// "a Box of Boxes", whose inner parameter is unwritten and must be fresh rather than the
/// enclosing instance's.
///
/// TOP LEVEL ONLY, the same depth WI-374 expands a signature position to, and stated
/// rather than assumed: a bare sort NESTED inside a written binding (`[T = Pair[A =
/// List]]`) is not expanded, so the erasure survives one level in. Deep expansion is
/// [`expand_foreign_sort_application`]'s own follow-on scope and closing it there closes
/// it here, since this is a call to it.
///
/// NEVER A PROVIDER SELECTION, which is what `binds_a_provider_slot` gates and the one
/// place this differs from the parameter channel it copies. A NAMED REQUIREMENT SLOT is
/// an ordinary type parameter for TYPING (058 §3.4) and a provider choice for DISPATCH,
/// and its VALUE is a witness SORT — `SortedSet.empty[T = Pair[Int64, Int64], O =
/// BySnd]()`. There is no argument that could pin anything inside it: the witness's own
/// parameters are instantiated by `resolve_inner` at the GOAL's bindings, not by
/// unification against the slot's variable. Expanding it does two wrong things, both
/// MEASURED on `wi858_pair_orderings_test`: `BySnd` declares `requires OA: Ord[A]`, so
/// the expansion mints a FLEX variable for `OA` — "some provider", which no author
/// wrote — and [`witness_value_slot_selections`] reads that variable back as a slot
/// binding that is not a sort (5 rows refused with `SelectionValueNotASort`); and the
/// slot's type stops rendering as the provider's NAME (`O = BySnd` became
/// `O = BySnd[A = ?A, B = ?B]`), which is what the merge-safety diagnostic names.
///
/// EACH CHANNEL ANSWERS IN ITS OWN CURRENCY — the callee bracket has the resolved
/// [`CallTypeArgTarget`], the receiver has its sort's own [`KnowledgeBase::
/// named_requirement_slots`] list — and the RULE lives here, once, so a third writer
/// cannot forget it.
fn expand_written_bracket_value(
    kb: &mut KnowledgeBase,
    value: &Value,
    binds_a_provider_slot: bool,
) -> Option<Value> {
    if binds_a_provider_slot {
        return None;
    }
    expand_foreign_sort_application(kb, value, None)
}

/// WI-870 (058 §3.3) — the SELECTIONS a bracket VALUE makes on the witness it names:
/// `[Ord = ListOrd[OE = LexFst]]`.
///
/// A value's bracket list has always been parsed and validated against the witness's
/// declared parameters (`check_sort_type_args` refuses an unknown name at load, naming
/// the real ones) — and then DISCARDED, which is the defect: `selection_witness_sym`
/// keeps the BASE, and the arguments reached the type-parameter half and became no
/// selection for any sub-goal. That is a silent drop of written text, and a defect
/// rather than a gap because `TieRepair::SubGoal` PRINTS this spelling as the repair.
///
/// **Only a NAMED REQUIREMENT SLOT becomes a selection.** §3.4 makes a named slot an
/// ordinary type parameter, so the witness's plain parameters share this bracket —
/// `LexFst[A = Int64]` binds a type and selects nothing, and reading every entry as a
/// selection would turn a type argument into a provider name.
/// [`named_requirement_slot_of`] is the discriminator — the WITNESS's own list, not
/// [`named_slot_spec`]'s callee ladder.
///
/// **Check 3 is deliberately NOT applied to a sub-slot**, and this is the one place
/// the sub-selection's validation differs from [`validate_instance_selection`]'s. That
/// check refuses naming a CONCRETE provider because at a call site the argument's own
/// value already directs dispatch, so an explicit witness could only agree redundantly
/// or contradict silently (§3.5). A witness's requirement slot has no value: it is a
/// dictionary slot the typer resolves, so naming the carrier's own provision there is
/// meaningful. Driven — the identical name is refused in the KEY's value position and
/// accepted one level in.
///
/// Check 1 IS applied, through the shared owner: a value that provides the slot's spec
/// nowhere gets the site's own message. The binding-precise half ("provides it, but
/// not at THESE bindings") is [`resolve_inner`]'s, exactly as it is for the outer pin.
///
/// TWO PRODUCERS, one reader — the same discipline WI-844 gave the outer channel. A
/// named slot IS a type parameter (§3.4), so `SortedSet[T = List[P], O = ListOrd[OE =
/// LexFst]]` is a writable TYPE and the nested binding reaches
/// [`selections_from_slot_bindings`] as an ARGUMENT as well as reaching
/// [`seed_op_type_args`] as a bracket. Reading the base at one producer and the whole
/// application at the other would drop the nested pin on exactly 058 §5's second
/// `SortedSet` line.
pub(super) fn witness_value_slot_selections(
    kb: &mut KnowledgeBase,
    fn_sym: Symbol,
    witness: Symbol,
    value: &Value,
    span: Option<Span>,
) -> Result<Vec<SlotSelection>, TypeError> {
    let out = value_slot_selections(kb, witness, value, SlotPinSource::Bracket)
        .map_err(|r| r.into_type_error(fn_sym, span))?;
    // Check 1 only — see this function's doc for why check 3 is not a sub-slot's.
    check_slot_witnesses_provide(kb, fn_sym, &out, span)?;
    Ok(out)
}

/// §4.4 check 1 over every level of a slot-selection tree.
fn check_slot_witnesses_provide(
    kb: &KnowledgeBase,
    fn_sym: Symbol,
    slots: &[SlotSelection],
    span: Option<Span>,
) -> Result<(), TypeError> {
    for s in slots {
        check_witness_provides_spec(kb, fn_sym, s.selection.spec_sort, s.selection.witness, span)?;
        check_slot_witnesses_provide(kb, fn_sym, &s.selection.slots, span)?;
    }
    Ok(())
}

/// WI-456 — why a slot binding written in a TYPE makes no selection, with no call site in
/// it: [`witness_value_slot_selections`] reports it as a [`TypeError`] at the call's span,
/// and the carrier path ([`carried_slot`]) has no call site to name.
enum SlotValueRefusal {
    NotASort { spec: Symbol },
    Unindexable { owner: Symbol, binder: Symbol },
}

impl SlotValueRefusal {
    fn into_type_error(self, fn_sym: Symbol, span: Option<Span>) -> TypeError {
        match self {
            SlotValueRefusal::NotASort { spec } => TypeError::SelectionValueNotASort {
                span,
                op: fn_sym,
                spec,
            },
            SlotValueRefusal::Unindexable { owner, binder } => {
                TypeError::SlotSelectionUnindexable {
                    span,
                    op: fn_sym,
                    owner,
                    binder,
                }
            }
        }
    }
}

/// The selections a type application `W[S = X, …]` makes on `witness`'s own NAMED
/// slots — [`witness_value_slot_selections`] without check 1, which is the caller's.
/// `source` says who wrote the application, which decides how an unwritten binding
/// reads ([`slot_selection_of`]).
fn value_slot_selections(
    kb: &mut KnowledgeBase,
    witness: Symbol,
    value: &Value,
    source: SlotPinSource,
) -> Result<Vec<SlotSelection>, SlotValueRefusal> {
    // The overwhelmingly common witness declares no named slot at all; a bare `[Spec =
    // W]` value has no named args either. Both are a read of an already-built list.
    if kb.named_requirement_slots(witness).is_empty() {
        return Ok(Vec::new());
    }
    let mut out: Vec<SlotSelection> = Vec::new();
    for key in value.named_keys(kb) {
        // POSITIONAL bindings arrive here too: the lowering maps each onto the next
        // free DECLARED parameter name before building the term (`type_expr_to_child`),
        // so `LexFst[Int64, Int64, Descending]` reaches this loop as named `A`, `B`,
        // `OA`. One reader for both spellings, which is what keeps the positional form
        // from being a second silent drop.
        let Some(slot) = named_requirement_slot_of(kb, witness, key) else {
            continue;
        };
        let Some(bound) = named_child_value(kb, value, key) else {
            continue;
        };
        out.extend(slot_selection_of(kb, witness, slot, &bound, source)?);
    }
    Ok(out)
}

/// One named slot of `owner` bound to `bound`, as a selection — or `None` when the
/// binding selects nothing.
fn slot_selection_of(
    kb: &mut KnowledgeBase,
    owner: Symbol,
    slot: crate::kb::NamedRequirementSlot,
    bound: &Value,
    source: SlotPinSource,
) -> Result<Option<SlotSelection>, SlotValueRefusal> {
    let Some(spec) = slot.spec_base else {
        return Ok(None);
    };
    let decided = match source {
        // An ABSTRACT binding derives nothing — the same rule [`is_type_param_value`]
        // states for the outer channel, and for the same reason: inside `report[T,
        // O](s: SortedSet[T = T, O = O])` the slot names the caller's parameter, and
        // pinning it would turn universal polymorphism into a wrong answer. `W[OE = T]`
        // written in a bracket says the same thing one level in — resolve `OE` however
        // the enclosing scope resolves `T` — so it FORWARDS rather than pins. Anything
        // else that is not a sort is refused.
        SlotPinSource::Bracket => !view_is_abstract_type_param(kb, bound),
        // WI-456 — a CARRIER type spells "unwritten" in forms a bracket never does: a
        // nested omitted slot is a fresh `Var::Rigid` (`O = ListOrd` with `OE` left
        // out), which the bracket's test reads as "not a sort". So a carrier's nested
        // binding is classified by WI-1094's own reader, and only a DECIDED one pins;
        // the rest leave the nested sub-goal to the scope and the search. Only the TOP
        // level gets WI-1094's refusal of an erased slot ([`carried_slot`]) — a nested
        // erasure is NOT refused, a limit this records rather than closes.
        SlotPinSource::Carrier => matches!(slot_binder_state(kb, bound), SlotBinderState::Decided),
    };
    if !decided {
        return Ok(None);
    }
    let Some(sub_witness) = selection_witness_sym(kb, bound) else {
        return Err(SlotValueRefusal::NotASort { spec });
    };
    let chain_index = dict_chain_index(kb, owner, &slot).ok_or(SlotValueRefusal::Unindexable {
        owner,
        binder: slot.binder,
    })?;
    let nested = value_slot_selections(kb, sub_witness, bound, source)?;
    Ok(Some(SlotSelection {
        binder: slot.binder,
        owner,
        chain_index,
        selection: InstanceSelection {
            spec_sort: spec,
            witness: sub_witness,
            slots: nested,
        },
    }))
}

/// WI-20260923-WN9P8 — the entries of a FRAME, in the one index space a
/// [`ResolvedRequiresNode::FromScope`] and a caller-chain projection both count in: a
/// [`ResolutionScope`]'s `available_requires` followed by its `sub_goal_requires`, or a
/// whole [`DictChain`] with an empty tail.
#[derive(Clone, Copy)]
pub(super) struct FrameEntries<'a> {
    pub(super) head: &'a [RequiresEntry],
    pub(super) tail: &'a [RequiresEntry],
}

impl<'a> FrameEntries<'a> {
    fn of_chain(chain: &'a DictChain) -> Self {
        FrameEntries {
            head: chain.entries(),
            tail: &[],
        }
    }

    pub(super) fn len(&self) -> usize {
        self.head.len() + self.tail.len()
    }

    pub(super) fn get(&self, i: usize) -> Option<&'a RequiresEntry> {
        match i.checked_sub(self.head.len()) {
            None => self.head.get(i),
            Some(j) => self.tail.get(j),
        }
    }
}

/// WI-20260923-WN9P8 — WHERE THE FRAME HOLDS THE DICTIONARY FOR ONE OF ITS OWN
/// PARAMETERS: the answer to a FORWARD.
///
/// A named requirement slot is a type parameter (058 §4.7). So a callee slot bound to a
/// parameter `X` the enclosing signature DECLARED says "the provider `X` stands for": the
/// value was built with it, and the dictionary the call needs is the one the enclosing
/// declaration's own caller supplied FOR `X`. The frame holds that dictionary in exactly
/// two places, and this finds it in one of them or answers `None`:
///
///  * `X`'s OWN named slot. `sort R { requires OE: WeakOrd[E] }` with `X = OE`, or the
///    operation-scoped `add[E, OE](…) requires OE: WeakOrd[E]`.
///  * a named slot of a CARRIER that one of the frame's requirements binds to `X`.
///    `requires PersistentCollection[C = SortedSet[T = E, O = OE], …]` holds
///    `SortedSet`'s own `O` dictionary in its provider half, at `O = OE`. That is the
///    shape Strategy 2b projects ([`provider_half_projection`]), under the same gates.
///
/// NOTHING ELSE IS `X`'s, however well it covers the goal, and that is the whole
/// ticket. The slot's goal is keyed by spec and bindings (`WeakOrd[T = E]`), and `X`
/// appears in neither. So a spec-keyed answer handed `s: SortedSet[T = E, O = P]` the
/// dictionary of `OE`, of an anonymous `requires WeakOrd[E]`, or of the provider half of
/// a requirement about some other parameter. Each was MEASURED loading clean and
/// inserting in the wrong order, on the direct call, through the spec
/// (`PersistentCollection.insert`), eta'd, and into a callee's op-scoped slot. Asking
/// "is this entry `X`'s" instead of "does it cover" is what tells those apart from the
/// sound shapes, which reach the same goal through `X` itself.
///
/// The OWN slot is found by `X`'s DECLARATION, not by searching the frame, because two
/// same-spec slots are otherwise indistinguishable (`requires A: WeakOrd[E]` and
/// `requires B: WeakOrd[E]` are equal entries). The binder's rigid gives its canonical
/// variable through `param_rigids`, that gives the parameter
/// ([`KnowledgeBase::type_param_of_canonical_var`]), and the parameter's declaring scope
/// gives the slot and its position in the frame. A frame that does not reach that
/// position holds no slot for `X` (`own_out_of_reach`): that happens when a route reads
/// only the sort half and `X` is an operation's slot, and it is a refusal, never a guess.
///
/// EVERY slot that is `X`'s, own first, and the caller takes the first that answers its
/// demand (found by `/code-review`). Each is `X`'s dictionary, so any of them is a sound
/// answer; stopping at the own slot would refuse a demand only a carrier's slot answers.
fn binder_frame_slots(
    kb: &mut KnowledgeBase,
    frame: FrameEntries<'_>,
    bound: TermId,
    ctx: &SigmaCtx,
) -> BinderSlots {
    let (own, own_out_of_reach) = match own_named_frame_slot(kb, frame, bound, ctx) {
        OwnSlot::Held(held) => (Some(held), false),
        OwnSlot::OutOfReach => (None, true),
        OwnSlot::NotASlot => (None, false),
    };
    let mut slots: Vec<BinderSlot> = own.into_iter().collect();
    for i in 0..frame.len() {
        slots.extend(carried_named_frame_slot(kb, frame, i, bound, ctx));
    }
    BinderSlots {
        slots,
        own_out_of_reach,
    }
}

/// [`binder_frame_slots`]' answer: the slots that hold `X`'s dictionary, and whether `X`
/// has a slot of its own that this frame does not reach.
#[derive(Clone, Debug)]
pub(super) struct BinderSlots {
    pub(super) slots: Vec<BinderSlot>,
    own_out_of_reach: bool,
}

impl BinderSlots {
    /// The first slot whose dictionary answers a demand of `demand_spec` that `covers`
    /// accepts, as `(scope_index, projection)`.
    pub(super) fn answer(
        &self,
        kb: &mut KnowledgeBase,
        demand_spec: Symbol,
        mut covers: impl FnMut(&mut KnowledgeBase, &RequiresEntry) -> bool,
    ) -> Option<(usize, SmallVec<[usize; 2]>)> {
        self.slots.iter().find_map(|b| {
            binder_slot_path(kb, b, demand_spec, &mut covers).map(|p| (b.scope_index, p))
        })
    }
}

/// [`own_named_frame_slot`]'s three answers. The middle one is its own because its repair
/// is different: the author declared the slot, and the route cannot read it.
enum OwnSlot {
    Held(BinderSlot),
    OutOfReach,
    NotASlot,
}

/// WI-20260923-WN9P8 — the parameter a body's rigid stands for: the rigid's canonical
/// variable through `param_rigids`, and the declaration that variable is canonical for.
/// `None` for a rigid that is none of this body's parameters.
fn param_of_rigid(kb: &KnowledgeBase, bound: TermId, ctx: &SigmaCtx) -> Option<Symbol> {
    let vid = ctx
        .param_rigids
        .iter()
        .find(|(_, rigid)| *rigid == bound)
        .map(|(vid, _)| *vid)?;
    kb.type_param_of_canonical_var(vid)
}

/// WI-20260923-WN9P8 — a frame slot that holds a parameter's dictionary, in
/// [`ResolvedRequiresNode::FromScope`]'s own shape, plus WHAT it holds.
#[derive(Clone, Debug)]
pub(super) struct BinderSlot {
    /// The frame entry, in [`FrameEntries`]' index space.
    pub(super) scope_index: usize,
    /// The path into that entry's dictionary. Empty for the parameter's own slot;
    /// `[provider-half offset]` for a slot a carrier holds.
    pub(super) projection: SmallVec<[usize; 2]>,
    /// The requirement the slot answers, in the ENCLOSING declaration's own parameters,
    /// which is what a cover is asked of. For a carrier's slot it is the carrier's entry
    /// composed through the carrier binding, as [`provider_half_projection`] composes it.
    pub(super) entry: RequiresEntry,
}

/// [`binder_frame_slot`]'s first place: `bound` is itself a named slot of the sort or the
/// operation that declared it.
fn own_named_frame_slot(
    kb: &mut KnowledgeBase,
    frame: FrameEntries<'_>,
    bound: TermId,
    ctx: &SigmaCtx,
) -> OwnSlot {
    let Some(param) = param_of_rigid(kb, bound, ctx) else {
        return OwnSlot::NotASlot;
    };
    let Some(owner) = kb.symbols.declaring_scope(param).map(|s| s.owner()) else {
        return OwnSlot::NotASlot;
    };
    let short = kb.local_name_of(param).to_string();
    let Some(slot) = kb
        .named_requirement_slots(owner)
        .iter()
        .find(|s| kb.local_name_of(s.binder) == short)
        .copied()
    else {
        return OwnSlot::NotASlot;
    };
    // WHERE the owner's slots sit in the frame. A sort's are the frame's prefix: its
    // declaration index IS its dictionary index ([`dict_chain_index_of_named_slot`]). An
    // operation's follow its sort's chain, at their position in the op-scoped chain.
    let index = if crate::kb::op_info::lookup_operation_info(kb, owner).is_some() {
        match op_named_slot_chain_index(kb, owner, &slot) {
            Some(j) => op_owner_dict_entries(kb, owner).len() + j,
            None => return OwnSlot::OutOfReach,
        }
    } else {
        slot.slot
    };
    let Some(entry) = frame.get(index) else {
        return OwnSlot::OutOfReach;
    };
    // VERIFIED, as `dict_chain_index` verifies: a frame whose entry there demands another
    // spec is not laid out the way the declaration says, and answering from it would be a
    // real dictionary from the wrong slot.
    if !slot
        .spec_base
        .is_some_and(|b| same_sort_canonical(kb, b, entry.required_sort))
    {
        return OwnSlot::OutOfReach;
    }
    OwnSlot::Held(BinderSlot {
        scope_index: index,
        projection: SmallVec::new(),
        entry: entry.clone(),
    })
}

/// [`binder_frame_slot`]'s second place: frame entry `i` requires a spec at a CARRIER
/// that binds one of its own named slots to `bound`, so the entry's dictionary holds that
/// slot's dictionary in its provider half.
///
/// The carrier and its gates are [`provider_half_carrier`]'s, the ones Strategy 2b
/// projects under: the provider half is the carrier's own chain only where the carrier
/// provides the spec itself and no witness rivals it.
pub(super) fn carried_named_frame_slot(
    kb: &mut KnowledgeBase,
    frame: FrameEntries<'_>,
    i: usize,
    bound: TermId,
    ctx: &SigmaCtx,
) -> Option<BinderSlot> {
    let entry = frame.get(i)?;
    let spec = entry.required_sort;
    let (carrier, carrier_value) = provider_half_carrier(kb, entry)?;
    let named = kb.named_requirement_slots(carrier).to_vec();
    if named.is_empty() {
        return None;
    }
    let args = carrier_named_args(kb, carrier_value);
    let slot = named.into_iter().find(|ns| {
        let binder = kb.local_name_of(ns.binder).to_string();
        args.iter()
            .any(|(k, v)| kb.local_name_of(*k) == binder && sigma_same(kb, ctx, *v, bound))
    })?;
    let entries = provider_dict_entries(kb, carrier, Some(spec)).entries_rc();
    let carried = entries.get(slot.slot)?;
    if !slot
        .spec_base
        .is_some_and(|b| same_sort_canonical(kb, b, carried.required_sort))
    {
        return None;
    }
    let base = dict_layout(kb, spec, carrier, None)
        .slots_for(kb, carrier)?
        .start;
    let carrier_params = impl_param_symbols(kb, carrier);
    let map: HashMap<Symbol, TermId> = align_by_short_name(kb, &args, &carrier_params)
        .into_iter()
        .collect();
    Some(BinderSlot {
        scope_index: i,
        projection: SmallVec::from_elem(base + slot.slot, 1),
        entry: RequiresEntry {
            required_sort: carried.required_sort,
            spec: substitute_in_spec(kb, &carried.spec, &map),
            supply: carried.supply,
        },
    })
}

/// WI-20260923-WN9P8 — the position of an OPERATION's named slot in its op-scoped chain.
///
/// Not `slot.slot`, which counts every `requires` goal the operation wrote, value
/// preconditions included, while the chain holds the spec goals only
/// ([`op_requires_chain_rc`]). So the position is the count of spec goals before it.
/// Verified against the goal it counts from, and `None` if that goal is not the slot's
/// spec, which a caller reads as "no slot here" and refuses.
fn op_named_slot_chain_index(
    kb: &mut KnowledgeBase,
    op: Symbol,
    slot: &crate::kb::NamedRequirementSlot,
) -> Option<usize> {
    let written = op_requires_entries(kb, op);
    let goal = written.get(slot.slot)?;
    if is_value_precondition_clause(kb, &goal.spec)
        || !slot
            .spec_base
            .is_some_and(|b| same_sort_canonical(kb, b, goal.required_sort))
    {
        return None;
    }
    Some(
        written[..slot.slot]
            .iter()
            .filter(|e| !is_value_precondition_clause(kb, &e.spec))
            .count(),
    )
}

/// WI-20260923-WN9P8 — the named slot of `owner`'s OWN chain at position `j`: a sort's
/// dictionary chain, or an operation's op-scoped chain. [`named_slot_at`] for the first,
/// [`op_named_slot_chain_index`] read backwards for the second.
pub(super) fn named_slot_of_chain(
    kb: &mut KnowledgeBase,
    owner: Symbol,
    j: usize,
) -> Option<crate::kb::NamedRequirementSlot> {
    // Asked for EVERY dep of every dictionary built, and nearly every owner names no slot.
    if kb.named_requirement_slots(owner).is_empty() {
        return None;
    }
    if crate::kb::op_info::lookup_operation_info(kb, owner).is_none() {
        return named_slot_at(kb, owner, j);
    }
    let slots = kb.named_requirement_slots(owner).to_vec();
    slots
        .into_iter()
        .find(|s| op_named_slot_chain_index(kb, owner, s) == Some(j))
}

/// WI-20260923-WN9P8 — is `owner`'s named slot `slot` a FORWARD at this call, and of
/// which parameter? `Some(bound)` exactly when the binder's value under `ctx` is one of
/// the enclosing signature's own declared parameters, the `Quantified` binding that
/// [`infer_named_slot_bindings`] and [`carried_slot`] accept as "declared here".
///
/// The binder is read through the callee's canonical parameter variable, walked and
/// surfaced as [`infer_named_slot_bindings`] reads it, so the two cannot see two values.
fn forwarded_binder(
    kb: &mut KnowledgeBase,
    owner: Symbol,
    slot: &crate::kb::NamedRequirementSlot,
    ctx: &SigmaCtx,
) -> Option<TermId> {
    let short = kb.local_name_of(slot.binder).to_string();
    // A named slot's binder IS a type parameter of its owner (the loader splices it and
    // publishes its variable), so a miss here is a loader invariant broken, and reading
    // it as "not a forward" would hand the dep to the spec-keyed search in silence
    // (found by `/code-review`).
    let var = kb
        .type_param_sym_of(owner, &short)
        .and_then(|param| kb.canonical_type_param_var(param))
        .unwrap_or_else(|| {
            panic!(
                "named slot `{short}` of `{}` has no canonical type-parameter variable — the \
                 loader publishes one for every slot binder",
                kb.qualified_name_of(owner)
            )
        });
    let walked = walk_type_deep(kb, ctx.subst, var);
    let bound = surface_node_binding_to_term(kb, ctx.subst, walked);
    let declared = matches!(
        slot_binder_state(kb, &TermIdView(bound)),
        SlotBinderState::Quantified
    ) && ctx.param_rigids.iter().any(|(_, rigid)| *rigid == bound);
    declared.then_some(bound)
}

/// WI-20260923-WN9P8 — may a SAME-SORT call inherit its caller's frame? The inherit hands
/// the callee the caller's own dictionary for each of the sort's named slots, which is the
/// forward only where the call binds each slot to ITS OWN parameter. A bracket may bind it
/// to another: `ins[OE = P](s, x)` inside the sort that declares `OE` and a plain `P`.
/// MEASURED (found by `/code-review`): that inherited `OE`'s dictionary and inserted a
/// set typed `O = P` in `OE`'s order, on all three spellings. Where this answers `false`
/// the caller builds a dictionary instead, and the forward rule answers each slot
/// ([`project_forwarded_slot`]) or refuses it.
///
/// A slot bound to a WITNESS is not asked about here: that is a selection, and the
/// callers already decline the inherit for one (`pins_this_chain`).
pub(super) fn inherit_answers_every_forward(
    kb: &mut KnowledgeBase,
    sort: Symbol,
    ctx: &SigmaCtx,
) -> bool {
    let slots = kb.named_requirement_slots(sort).to_vec();
    slots
        .iter()
        .all(|slot| match forwarded_binder(kb, sort, slot, ctx) {
            None => true,
            Some(bound) => {
                let own = kb.type_param_sym_of(sort, kb.local_name_of(slot.binder));
                own.is_some() && param_of_rigid(kb, bound, ctx) == own
            }
        })
}

/// WI-20260923-WN9P8 — the path into `slot` whose dictionary answers a demand of spec
/// `demand_spec` that `covers` accepts. The slot itself, or, for a parameter's OWN slot,
/// one level into it: `requires X: Ord[E]` answers `WeakOrd[T = E]` out of `X`'s own
/// dictionary, Strategy 2's composition over [`build_child_subst_map`]. That is still
/// `X`'s dictionary, which is what the forward asks for.
fn binder_slot_path(
    kb: &mut KnowledgeBase,
    slot: &BinderSlot,
    demand_spec: Symbol,
    covers: &mut impl FnMut(&mut KnowledgeBase, &RequiresEntry) -> bool,
) -> Option<SmallVec<[usize; 2]>> {
    // SPEC FIRST, as every caller of the two cover predicates filters: a cover compares
    // bindings key by key and assumes one spec on both sides.
    if same_sort_canonical(kb, slot.entry.required_sort, demand_spec) && covers(kb, &slot.entry) {
        return Some(slot.projection.clone());
    }
    if !slot.projection.is_empty() {
        return None;
    }
    let chain = direct_requires_chain_rc(kb, slot.entry.required_sort);
    let mut map: Option<HashMap<Symbol, TermId>> = None;
    for (k, sub) in chain.iter().enumerate() {
        if !same_sort_canonical(kb, sub.required_sort, demand_spec) {
            continue;
        }
        let map = map.get_or_insert_with(|| build_child_subst_map(kb, &slot.entry));
        let composed = RequiresEntry {
            required_sort: sub.required_sort,
            spec: substitute_in_spec(kb, &sub.spec, map),
            supply: sub.supply,
        };
        if covers(kb, &composed) {
            return Some(SmallVec::from_elem(k, 1));
        }
    }
    None
}

/// WI-20260923-WN9P8 — THE DIRECT ROUTE's forward, for both halves of a callee's
/// dictionary. `dep` fills `owner`'s named slot `slot`; when its binder is one of the
/// enclosing signature's parameters, the dep is projected out of the frame's dictionary
/// FOR that parameter ([`binder_frame_slot`]), or refused.
///
/// `None` when the dep is not a forward, and the ordinary strategies answer it. A
/// forward never reaches them. Strategy 1 is first-match by spec, and Strategy 3 would
/// construct a rival for a value that already chose.
///
/// REFUSED, not skipped, where the frame holds nothing for the parameter. A skipped dep
/// falls into the fall-backs of its caller, and the measured outcomes there were a wrong
/// order out of another slot's dictionary and an eval `Internal` out of none.
pub(super) fn project_forwarded_slot(
    kb: &mut KnowledgeBase,
    owner: Symbol,
    slot: &crate::kb::NamedRequirementSlot,
    dep: &RequiresEntry,
    caller_requires: &DictChain,
    ctx: &SigmaCtx,
    syms: &ProjectionSyms,
) -> Option<Result<TermId, Box<RequirementRefusal>>> {
    let bound = forwarded_binder(kb, owner, slot, ctx)?;
    let held = binder_frame_slots(kb, FrameEntries::of_chain(caller_requires), bound, ctx);
    let path = held.answer(kb, dep.required_sort, |kb, e| {
        entries_cover(kb, e, dep, Some(ctx))
    });
    let untied = |kb: &mut KnowledgeBase| {
        Box::new(RequirementRefusal {
            no_scope_route: false,
            construction_carries_repair: false,
            dep_text: render_requires_entry(kb, dep),
            unconstrained: Vec::new(),
            refused_covers: Vec::new(),
            construction: String::new(),
            pinned: None,
            unprovided: None,
            untied: Some(UntiedForward::of(kb, owner, slot.binder, bound, ctx, &held)),
        })
    };
    let Some((index, path)) = path else {
        return Some(Err(untied(kb)));
    };
    // A frame entry with no NAME is a chain that cannot name its slots
    // ([`DictChain::unnamed`]). The slot was found by position, so this is the chain
    // disagreeing with itself, and falling through to the spec-keyed strategies is the
    // one thing a forward must not do.
    let Some(name) = caller_requires.name_at(kb, index) else {
        return Some(Err(untied(kb)));
    };
    let mut t = build_req_var_ref(kb, syms, name);
    for k in path {
        t = build_req_at_sort(kb, syms, t, k);
    }
    Some(Ok(t))
}

/// WI-20260923-WN9P8 — a FORWARD the frame cannot answer: `owner`'s named slot `binder`
/// is bound to `param`, one of the enclosing signature's own parameters, and nothing in
/// the frame holds a dictionary for it.
#[derive(Clone, Debug)]
pub struct UntiedForward {
    pub(super) owner: Symbol,
    pub(super) binder: Symbol,
    /// The enclosing parameter, rendered (`probe.R3.P`).
    pub(super) param: String,
    /// The requirement the frame DOES hold for the parameter, rendered, when there is one
    /// and it does not answer this goal (`requires OE: WeakOrd[E]` asked for
    /// `WeakOrd[T = F]`). `None` is the frame holding nothing for it at all.
    pub(super) held: Option<String>,
    /// The parameter HAS a slot of its own, and this route does not read the half of the
    /// frame it sits in: an operation's own slot, reached by a route that reads the sort's
    /// slots only (an operation used as a function value). Found by `/code-review`: the
    /// "nothing holds a dictionary for it" sentence was false there.
    out_of_reach: bool,
}

impl UntiedForward {
    fn of(
        kb: &KnowledgeBase,
        owner: Symbol,
        binder: Symbol,
        bound: TermId,
        ctx: &SigmaCtx,
        held: &BinderSlots,
    ) -> Self {
        // The parameter's own qualified name where the rigid maps back to one, which is
        // every declared rigid; the rigid itself otherwise, which still names it.
        let param = param_of_rigid(kb, bound, ctx)
            .map(|p| kb.qualified_name_of(p).to_string())
            .unwrap_or_else(|| format_term_for_goal(kb, bound));
        UntiedForward {
            owner,
            binder,
            param,
            held: held
                .slots
                .first()
                .map(|b| render_requires_entry(kb, &b.entry)),
            out_of_reach: held.own_out_of_reach,
        }
    }

    /// The sentence every channel says it in: the dictionary build's refusal, and
    /// [`resolve_inner`]'s for the spec route, so the two read alike.
    pub(super) fn render(&self, kb: &KnowledgeBase) -> String {
        let short = short_name_of(&self.param).to_string();
        if self.out_of_reach {
            return format!(
                "named slot `{b}` of `{o}` is bound to `{p}`, whose dictionary is the enclosing \
                 OPERATION's own requirement slot, and this route reads only the enclosing \
                 SORT's slots, as an operation used as a function value does — declare the \
                 slot for `{short}` on the enclosing SORT instead",
                b = kb.local_name_of(self.binder),
                o = kb.qualified_name_of(self.owner),
                p = self.param,
            );
        }
        if let Some(held) = &self.held {
            return format!(
                "named slot `{b}` of `{o}` is bound to `{p}`, and the enclosing scope's \
                 dictionary for `{short}` (`requires {held}`) does not answer it — a \
                 requirement answers for the parameter it is declared for, so nothing else \
                 in the scope is forwarded in its place",
                b = kb.local_name_of(self.binder),
                o = kb.qualified_name_of(self.owner),
                p = self.param,
            );
        }
        format!(
            "named slot `{b}` of `{o}` is bound to `{p}`, a type parameter of the enclosing \
             declaration, and nothing in the enclosing scope holds a dictionary FOR `{short}` \
             (a requirement answers for the parameter it is declared for, so a same-spec \
             requirement of another parameter, or an anonymous one, is not `{short}`'s) — \
             declare a requirement slot for `{short}` on the enclosing SORT or OPERATION, \
             wherever `{short}` is declared (`requires {short}: <the spec above>`), or bind \
             `{b}` to a parameter that already is one",
            b = kb.local_name_of(self.binder),
            o = kb.qualified_name_of(self.owner),
            p = self.param,
        )
    }
}

/// WI-870 — [`is_type_param_value`] read through a view, so a `Value::Node`-carried
/// binding answers rather than falling into "not a sort" and being refused. The two
/// spellings an abstract binding takes are a `TypeVar` head (the occurrence carrier's)
/// and a bare reference to a `sort P = ?` symbol (the term carrier's).
fn view_is_abstract_type_param<V: TermView>(kb: &KnowledgeBase, v: &V) -> bool {
    match type_head(kb, v) {
        TypeHead::TypeVar(_) => true,
        TypeHead::SortRef(s) => is_sort_param_symbol(kb, s),
        _ => false,
    }
}

/// WI-456 — what the goal's CARRIER type says about one named slot of the chosen
/// provider, read out of the provision match.
///
/// A named slot is a type parameter (§4.7), so `provides PersistentCollection[C =
/// SortedSet[T = T, O = O], …]` matched against `C = SortedSet[T = String, O =
/// ByLength]` has already decided the provider's `O` — and before this, the sub-goal for
/// `requires O: WeakOrd[T]` searched `WeakOrd[String]` anyway and tied among every
/// provider of it. [`selections_from_slot_bindings`] reads the same binding at a DIRECT
/// call (`SortedSet.insert(s, x)`); a call through the spec
/// (`PersistentCollection.insert(s, x)`) never reaches it, because the callee is the
/// spec's and names no slot, and a provider chosen deeper in a resolution tree has no
/// call site at all. The provision match is where both learn the binding.
pub(super) enum CarriedSlot {
    /// A witness: the sub-goal is pinned to it.
    Pinned(SlotSelection),
    /// The binder is one of the enclosing signature's own declared parameters (058 §7.1,
    /// `first(s: SortedSet[T = E, O = OE])` under `requires OE: …`): the caller's slot
    /// supplies the value's own dictionary.
    ///
    /// WI-20260923-WN9P8 — and it carries WHICH slot: the one [`binder_frame_slot`] finds
    /// for that parameter, which answers the sub-goal. It used to carry nothing, and the
    /// scope then answered the sub-goal by its SPEC, which any same-spec entry of the
    /// frame covers. `None` only without a σ (the eval bridge, the diagnostic
    /// re-resolution), where there is no frame to ask and the sub-goal keeps its search.
    Forwarded(Option<BinderSlots>),
    /// WI-20260923-WN9P8 — declared by the enclosing signature, and the frame holds no
    /// dictionary for it, so nothing may answer the sub-goal. What does cover it by spec
    /// is some other parameter's.
    Untied(UntiedForward),
    /// Quantified by a signature that never declared it (`s: SortedSet[T = String]`):
    /// WI-1094's erasure. The value chose at its construction and its choice is not
    /// recoverable, so the sub-goal must be REFUSED, not searched — whatever the
    /// provider count, because even a sole provider answers for the signature and not
    /// for the value.
    Erased,
    /// A flex variable nothing has said anything about: the search is the ladder, as at
    /// a construction site (WI-1094's `Unspoken`).
    Unspoken,
    /// No witness reading at all (an arrow, a tuple): the requirement's own route
    /// reports it, as [`selections_from_slot_bindings`] leaves it.
    NoWitness,
    /// The provision the dispatch took does not bind the slot in its head. Legitimate
    /// for a WITNESS sort, whose head is about some other carrier (`LexFst provides
    /// Ord[T = Pair[…]]`) and whose slots a bracket value or an enclosing selection
    /// writes; for a CONCRETE provider it is a head that forgot `O = O`.
    NotInHead,
}

/// Classify `slot` of `owner` from the provision match `impl_subst`. See [`CarriedSlot`].
///
/// `impl_subst` records the per-call value as the match found it, so it is WALKED through
/// the call-site σ and surfaced first — the pair [`slot_binder_state`]'s own doc requires
/// of its input: a `Var::Global` the call-site σ binds to `ByLength` would otherwise read
/// as a flex variable.
pub(super) fn carried_slot(
    kb: &mut KnowledgeBase,
    owner: Symbol,
    slot: crate::kb::NamedRequirementSlot,
    impl_subst: &[(Symbol, TermId)],
    sigma: Option<&SigmaCtx>,
    // WI-20260923-WN9P8 — the frame the resolution's `FromScope` indices count in, where a
    // forwarded binder's own dictionary is looked for.
    frame: FrameEntries<'_>,
) -> CarriedSlot {
    // `impl_subst` is keyed by the owner's QUALIFIED parameter symbols
    // ([`impl_param_symbols`]) and the binder is a bare intern of the written name; within
    // one sort the short name joins them exactly ([`carrier_arg_impl_subst`]).
    let binder = kb.local_name_of(slot.binder);
    let Some(raw) = impl_subst
        .iter()
        .find(|(k, _)| kb.local_name_of(*k) == binder)
        .map(|(_, v)| *v)
    else {
        return CarriedSlot::NotInHead;
    };
    let bound = match sigma {
        Some(s) => {
            let walked = walk_type_deep(kb, s.subst, raw);
            surface_node_binding_to_term(kb, s.subst, walked)
        }
        None => raw,
    };
    match slot_binder_state(kb, &TermIdView(bound)) {
        SlotBinderState::Decided => {
            match slot_selection_of(kb, owner, slot, &Value::term(bound), SlotPinSource::Carrier) {
                Ok(Some(sel)) => CarriedSlot::Pinned(sel),
                // A DECIDED top level always has a sort head; `None` would mean the two
                // classifiers disagree about one binding.
                Ok(None) | Err(SlotValueRefusal::NotASort { .. }) => {
                    unreachable!("a Decided slot binding reads as a witness")
                }
                // [`dict_chain_index_of_named_slot`]'s invariant: the declaration order and
                // the dictionary order have drifted, and pinning by either would resolve a
                // real goal with the wrong provider. Not a verdict about the program.
                Err(SlotValueRefusal::Unindexable { owner, binder }) => panic!(
                    "named slot `{}` of `{}` has no dictionary position demanding its spec \
                     — declaration and dictionary-chain order have drifted",
                    kb.local_name_of(binder),
                    kb.qualified_name_of(owner),
                ),
            }
        }
        // The same test WI-1094's direct route makes ([`infer_named_slot_bindings`]): only
        // a binder the SIGNATURE declared forwards. Without a σ there are no declarations
        // to ask — the eval bridge and the diagnostic re-resolution, where a runtime value
        // never carries a quantified binder — and the sub-goal keeps its search.
        //
        // WI-20260923-WN9P8 — and it forwards ITS OWN dictionary or nothing. "Declared here"
        // admits a plain parameter as well as a slot's binder, and the scope used to answer
        // either by spec. MEASURED: `PersistentCollection.insert(s, x)` with `s:
        // SortedSet[T = E, O = P]`, inside a sort that also `requires OE: WeakOrd[E]`,
        // inserted in `OE`'s order.
        SlotBinderState::Quantified => match sigma {
            Some(s) if s.param_rigids.iter().any(|(_, rigid)| *rigid == bound) => {
                let held = binder_frame_slots(kb, frame, bound, s);
                if held.slots.is_empty() {
                    CarriedSlot::Untied(UntiedForward::of(kb, owner, slot.binder, bound, s, &held))
                } else {
                    CarriedSlot::Forwarded(Some(held))
                }
            }
            Some(_) => CarriedSlot::Erased,
            None => CarriedSlot::Forwarded(None),
        },
        SlotBinderState::Unspoken(_) => CarriedSlot::Unspoken,
        SlotBinderState::NoWitnessReading => CarriedSlot::NoWitness,
    }
}

/// The named slot of `owner` sitting at position `j` of its dictionary chain, if any —
/// [`dict_chain_index_of_named_slot`]'s identity (`slot` IS the chain index) read the
/// other way round.
pub(super) fn named_slot_at(
    kb: &KnowledgeBase,
    owner: Symbol,
    j: usize,
) -> Option<crate::kb::NamedRequirementSlot> {
    kb.named_requirement_slots(owner)
        .iter()
        .find(|s| s.slot == j)
        .copied()
}

/// WI-456 — two slot selections name the same instance: the same witness, and the same
/// selections on every one of its slots, recursively. The base alone is not enough —
/// `ListOrd[OE = LexFst]` and `ListOrd[OE = LexSnd]` are two orderings.
pub(super) fn same_selection(
    kb: &KnowledgeBase,
    a: &InstanceSelection,
    b: &InstanceSelection,
) -> bool {
    same_sort_canonical(kb, a.witness, b.witness)
        && a.slots.len() == b.slots.len()
        && a.slots.iter().all(|sa| {
            b.slots.iter().any(|sb| {
                sa.chain_index == sb.chain_index && same_selection(kb, &sa.selection, &sb.selection)
            })
        })
}

/// WI-870 — `owner`'s NAMED requirement slot whose binder is `key`, or `None` when
/// `key` is one of its ordinary type parameters.
///
/// A SORT's own list, deliberately not [`named_slot_spec`]'s two-scope ladder: that
/// one answers for a CALLEE, whose slots may be its enclosing sort's, and a witness
/// named in a bracket value is neither a callee nor inside one. Matching is by symbol
/// identity, which holds because both sides are BARE interns of the written name — the
/// binder from `join_segments` at the declaration, the key from `reintern(p.last())`
/// at the type application.
fn named_requirement_slot_of(
    kb: &KnowledgeBase,
    owner: Symbol,
    key: Symbol,
) -> Option<crate::kb::NamedRequirementSlot> {
    kb.named_requirement_slots(owner)
        .iter()
        .find(|s| s.binder == key)
        .copied()
}

/// WI-870 — where `slot` sits in `owner`'s DICTIONARY chain, which is the coordinate a
/// sub-goal pin is keyed by.
///
/// The two indexings coincide by construction and the identity is stated once, here,
/// per WI-857's dual lesson: `NamedRequirementSlot.slot` is the declaration's position
/// among the scope's `requires` items (`LoadPass`'s per-scope counter), `direct_requires`
/// reads one `SortRequiresInfo` fact per such item in assertion order, and
/// [`provider_dict_chain`] PREFIXES that chain with itself before appending any
/// provision conditions. So the dictionary index IS the declaration index.
///
/// VERIFIED rather than trusted: the entry found there must demand the very spec the
/// slot was recorded for. A disagreement means the two orders have drifted, and pinning
/// the wrong slot is silent — it resolves a real goal with a real provider and computes
/// the wrong answer. So it is an error, not a `debug_assert` and not a skip. Unreachable
/// on today's surface, which is exactly why nothing else would notice it.
pub(super) fn dict_chain_index_of_named_slot(
    kb: &mut KnowledgeBase,
    owner: Symbol,
    slot: &crate::kb::NamedRequirementSlot,
    fn_sym: Symbol,
    span: Option<Span>,
) -> Result<usize, TypeError> {
    dict_chain_index(kb, owner, slot).ok_or(TypeError::SlotSelectionUnindexable {
        span,
        op: fn_sym,
        owner,
        binder: slot.binder,
    })
}

/// [`dict_chain_index_of_named_slot`]'s verified index, `None` on drift — for the
/// callers with no call site to report it at.
pub(super) fn dict_chain_index(
    kb: &mut KnowledgeBase,
    owner: Symbol,
    slot: &crate::kb::NamedRequirementSlot,
) -> Option<usize> {
    // Named slots are sort-level `requires`, the prefix every chain of `owner` shares.
    let chain = provider_dict_entries(kb, owner, None);
    let demanded = chain.entries().get(slot.slot).map(|e| e.required_sort);
    match (demanded, slot.spec_base) {
        (Some(d), Some(s)) if same_sort_canonical(kb, d, s) => Some(slot.slot),
        _ => None,
    }
}

/// WI-841/WI-844 — add one selection, upholding the invariant EVERY producer shares: at
/// most one [`InstanceSelection`] per spec, and a second, DIFFERENT witness for a spec
/// already selected is [`TypeError::ConflictingSelection`], never a first match.
///
/// One owner because the invariant is one statement and there are two producers — the
/// call BRACKET ([`seed_op_type_args`]) and the argument TYPES
/// ([`selections_from_slot_bindings`]). A selection is keyed by the SPEC at
/// [`resolve`]'s step 0, so two witnesses under one key have no meaning to give,
/// wherever they were written.
///
/// **The producers are NOT ranked, and an earlier cut that ranked them was wrong.** It
/// exempted a derived witness colliding with a BRACKET-written one, on the reasoning
/// that they read one variable and so cannot disagree — true of ONE slot, false across
/// two same-spec slots. MEASURED: on a sort with `requires A: Ord[T]` and
/// `requires B: Ord[T]`, a value typed `Both[T = String, A = ByLength, B = Alphabetical]`
/// is correctly refused, and adding `[A = ByLength]` to the call DELETED the refusal —
/// the `B` read collided with the bracket entry, was exempted, and one spec-keyed pin
/// served both deps. A `debug_assert` written to document the exemption fired on the
/// first program that exercised it. So the comparison is unconditional: witnesses agree
/// or the call is refused, whoever wrote them.
///
/// WI-870 — `slots` is what the value bound on the witness's OWN named slots, and BOTH
/// producers supply it (a named slot is a type parameter, so the σ-read producer sees
/// the same application the bracket wrote). A second push for an already-selected spec
/// therefore keeps the FIRST entry's slots, which is sound for the reason the witness
/// comparison is unconditional: for one slot the two producers read one variable, so
/// they agree and the second push is a no-op.
pub(super) fn push_selection(
    kb: &KnowledgeBase,
    selections: &mut Vec<InstanceSelection>,
    spec_sort: Symbol,
    witness: Symbol,
    slots: Vec<SlotSelection>,
    fn_sym: Symbol,
    span: Option<Span>,
) -> Result<(), TypeError> {
    if let Some(prev) = selections
        .iter()
        .find(|s| same_sort_canonical(kb, s.spec_sort, spec_sort))
    {
        if !same_sort_canonical(kb, prev.witness, witness) {
            return Err(TypeError::ConflictingSelection {
                span,
                op: fn_sym,
                spec: spec_sort,
                first: prev.witness,
                second: witness,
            });
        }
        return Ok(());
    }
    selections.push(InstanceSelection {
        spec_sort,
        witness,
        slots,
    });
    Ok(())
}

/// WI-844 (058 §5.3, §4.7) — the selections this call's TYPES make, appended to the
/// ones its BRACKET made.
///
/// §4.7's rule is that a NAMED requirement slot **is a type parameter**, so the chosen
/// provider is part of the type identity and every value of that type carries it:
/// `SortedSet[T = String, O = ByLength]`. WI-841 implemented the WRITE half — a
/// bracket key binds the slot's parameter AND records an [`InstanceSelection`] — and
/// left the type carrying a choice nothing read back. MEASURED at HEAD before this
/// ticket, on §5.3's driver: two `Ord[String]` witnesses coexist and
/// `SortedSet.empty[T = String, O = ByLength]()` selects, but the very next line,
/// `SortedSet.insert(a, "zz")`, refused with *"constructing `Ord[T = String]` is
/// ambiguous among providers: String, ByLength, Alphabetical"* — the argument's
/// `O = ByLength` notwithstanding. The driver was writable only by repeating
/// `[T = String, O = ByLength]` at every call, which is the type parameter doing none
/// of the work §4.7 gives it.
///
/// So this READS the slot's parameter back out of σ. The bracket and the argument
/// write the SAME variable (`seed_op_type_args` unifies it, argument conformance then
/// checks it — WI-836), so this is one channel with two producers, not a second
/// mechanism: what the bracket returns eagerly, an argument leaves in σ for this to
/// pick up.
///
/// Three properties, each load-bearing:
///
///  * **Appended, never overwriting — and never FIRST-MATCHING.** Both producers go
///    through [`push_selection`], which refuses a second, DIFFERENT witness for one
///    spec whoever wrote it. That matters because an `InstanceSelection` is keyed by
///    the SPEC: a sort with two same-spec named slots carries two witnesses in one type
///    (`Both[T = String, A = ByLength, B = Alphabetical]` — which the bracket cannot
///    spell but a parameter ANNOTATION reaches, measured), and first-matching would pin
///    one onto both deps. For ONE slot the bracket and the argument write the same
///    variable, so they agree and the second push is a no-op.
///  * **An ABSTRACT slot derives nothing.** Inside `report[T, O](s: SortedSet[T = T,
///    O = O])` (§7.1) the slot is bound to a type PARAMETER, not a witness, and must
///    stay a FORWARD of the caller's dictionary. [`is_type_param_value`] is that test,
///    and it is the reason this cannot turn universal polymorphism into a wrong pin.
///  * **Check 1 YES, check 3 no.** Check 3 refuses a SPELLING — an explicit witness
///    where a concrete provider's values already direct dispatch (§4.4) — and there is
///    no spelling here. It runs where a selection is WRITTEN, at both call-site
///    spellings, through [`validate_written_selection`]. Check 1 (the witness provides
///    the spec at all) IS run, inline below.
///
///    DECIDED, NOT LEFT OVER (WI-20260911-TX0G6): a TYPE legitimately carries a
///    concrete witness. WI-1094's inference WRITES one:
///    `SortedSet.empty[T = Pair[Int64, Int64]]()` types as `O = Pair`, the prelude's own
///    pair order, and every later call reads that back here. A result, a parameter, a
///    `let` and an eta arrow typed `O = ConcOrd` all load and RUN in `ConcOrd`'s order.
///    Check 3 here would refuse the compiler's own inference. MEASURED by moving it
///    here: exactly three pre-existing tests fail. They are wi858's and wi869's
///    bracket-less `SortedSet`s of pairs, which carry the inferred `O = Pair`, and
///    wi_r10kc's consumer typed with a concrete `MySet`. The only other failure is
///    TX0G6's own boundary row. The three corpora read no concrete witness here at all.
///
///    WI-20260911-6B67S added CHECK 1 here, and the shape of the bug is why it belongs
///    here. This producer already ran check 1 on every NESTED slot witness
///    ([`check_slot_witnesses_provide`]) and on no top-level one, and the gap was
///    covered by a claim that [`check_selection_bindings`] "decides it more precisely,
///    at this call's own bindings". It does not: it asks the NARROWER question, renders
///    "provides the spec, but not at these bindings" from an invariant only the BRACKET
///    producer establishes, and `continue`s entirely when the goal has no candidates.
///    So a witness providing NOTHING was described as providing it — and on this
///    function's OTHER caller (the eta path, `eta.rs`' `no check_selection_bindings
///    here, unlike the direct call`) nothing asked at all. Running check 1 at the
///    producer makes the consumer's assumption TRUE instead of making the consumer ask.
pub(super) fn selections_from_slot_bindings(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    op: &OperationInfoFull,
    fn_sym: Symbol,
    mut selected: Vec<InstanceSelection>,
    span: Option<Span>,
) -> Result<Vec<InstanceSelection>, TypeError> {
    // The overwhelmingly common callee names no slot in EITHER scope, and
    // `call_bracket_scopes` is a memo read plus a per-param intern. Skip both.
    if !names_any_requirement_slot(kb, fn_sym) {
        return Ok(selected);
    }
    // The SAME two scopes rule (1) binds, read through the same owner — a slot
    // reachable by a bracket key and a slot readable from σ are one list, so a scope
    // added there cannot be forgotten here.
    for (name, var) in call_bracket_scopes(kb, op, fn_sym) {
        let Some(spec_sort) = named_slot_spec(kb, fn_sym, name) else {
            continue;
        };
        let var_term = type_param_var_term(kb, var);
        // WALKED THEN SURFACED, the pairing `check_apply_iter`'s sibling σ-read of these
        // very vars used (WI-394): the deep walk STOPS at a
        // non-`Term` (`Value::Node`) binding and leaves a bare var behind, which
        // `is_type_param_value` then reads as ABSTRACT — so a `Value::Node`-carried
        // witness would derive no selection and say nothing about it. Walking without
        // surfacing is the silent skip, not a shortcut.
        let walked = walk_type_deep(kb, subst, var_term);
        let bound = surface_node_binding_to_term(kb, subst, walked);
        if is_type_param_value(kb, bound) {
            continue;
        }
        // `sort_functor_of_view`'s `TermId` face — the SAME head read
        // `selection_witness_sym` gives a bracket value, and for the same reason: a
        // witness may carry type arguments (§4.5) and its BASE is what identifies it.
        // `None` here is a slot bound to something with no sort head at all — an arrow,
        // a tuple, an effect row.
        //
        // WI-20260911-6B67S — LOUD for ONE of the two carriers that land here, where
        // this used to `continue` for both. The skip was argued as "no witness to name,
        // and `check_selection_bindings` has no goal to judge it against; the
        // requirement's own route reports it", and the last clause was MEASURED FALSE:
        // `SortedSet[T = Int64, O = (Int64, Int64)].empty()` LOADED CLEAN, the written
        // `O` dropped and the requirement answered by an ordinary search. It only looks
        // reported when two providers happen to tie, and then it is reported as an
        // AMBIGUITY — never as the malformed binding it is. With one provider the
        // author's text is silently replaced by the search's answer, which is the silent
        // wrong answer the callee bracket has always refused (`SelectionValueNotASort`,
        // [`seed_op_type_args`]).
        //
        // WHICH CARRIER IT IS, ASKED OF [`slot_binder_state`] AND NOT OF THE `None`.
        // `sort_functor_of` answering `None` is TWO situations, and `is_type_param_value`
        // one line up separates only part of them — it reads a flex var and a sort
        // PARAMETER as abstract, and says nothing about a SKOLEM or the `s.O`
        // [`UnwrittenFill::Projection`] an UNWRITTEN slot is filled with. Those are
        // `Quantified`: the enclosing signature said "any", the dictionary must arrive
        // from the caller's frame, and refusing them breaks §7.1 forwarding outright —
        // MEASURED, 11 rows across `wi1094`, `wi844`, `wi_ee0ep` and `wi_r10kc`, every
        // one of them an unwritten slot taking its argument's own comparator. Only
        // [`SlotBinderState::NoWitnessReading`] — an arrow, a tuple, an effect row, a
        // denoted value — is a carrier no `provides` can ever answer, and it alone is
        // refused. That is also the enum's own reason for existing separately from
        // `Decided`, now load-bearing rather than documentary.
        let Some(witness) = sort_functor_of(kb, bound) else {
            if matches!(
                slot_binder_state(kb, &TermIdView(bound)),
                SlotBinderState::NoWitnessReading
            ) {
                return Err(TypeError::SelectionValueNotASort {
                    span,
                    op: fn_sym,
                    spec: spec_sort,
                });
            }
            continue;
        };
        // §4.4 CHECK 1, which this producer ran on a witness's NESTED slots
        // (`witness_value_slot_selections` → `check_slot_witnesses_provide`, one line
        // down) and on none of its TOP-LEVEL ones — inconsistent by exactly one level,
        // and the whole of WI-20260911-6B67S. A nested `ListOrd[OE = NotOrd]` was
        // refused by name while the `O = NotOrd` carrying it was passed on to be guessed
        // about downstream.
        //
        // HERE RATHER THAN AT THE CONSUMER, because this is what makes
        // [`check_selection_bindings`]' `at_bindings: true` TRUE rather than merely
        // rendered: both of this function's callers now hand on a checked selection,
        // including the eta one that runs no `check_selection_bindings` at all. The
        // shared owner is what keeps the two producers' answer to "does it provide" one
        // answer — [`seed_op_type_args`] reaches the same check through
        // [`validate_instance_selection`].
        check_witness_provides_spec(kb, fn_sym, spec_sort, witness, span)?;
        // WI-870: and the witness's OWN slot bindings, read out of the same type. A
        // named slot IS a type parameter (§4.7), so `SortedSet[T = List[P], O =
        // ListOrd[OE = LexFst]]` carries the nested selection in the ARGUMENT exactly
        // as the bracket carries it — reading only the base here would drop it on
        // every call after the construction site, which is the very asymmetry WI-844
        // built this producer to close.
        let slots = witness_value_slot_selections(kb, fn_sym, witness, &Value::term(bound), span)?;
        push_selection(kb, &mut selected, spec_sort, witness, slots, fn_sym, span)?;
    }
    Ok(selected)
}

/// WI-1094 — what a callee's NAMED requirement slot's binder resolves to AT THIS CALL,
/// which is the question 058 §3.4's two halves are told apart by.
///
/// A named slot IS a type parameter, so the binder's binding is a THREE-way question
/// and every previous reader asked a two-way one. [`is_type_param_value`] answers
/// "abstract", collapsing a still-FLEX variable with a skolem — and those are the two
/// cases that must diverge here: a flex var is *nobody has said*, which §3.4 leaves "to
/// inference"; a skolem is *the enclosing signature said ANY*, which is a universally
/// quantified parameter whose dictionary must arrive from the caller's frame, never be
/// constructed here.
enum SlotBinderState {
    /// A still-FLEX variable — the slot is unwritten at every site that could have
    /// written it. `SortedSet.empty[T = Pair[…]]()`: `O` appears only in the RESULT, so
    /// this call CONSTRUCTS the value and choosing its order is this call's to make.
    Unspoken(VarId),
    /// A skolem: a `Var::Rigid`, or the `s.O` projection [`UnwrittenFill::Projection`]
    /// mints for a parameter's unwritten slot. `size(s: SortedSet[T = String])` means
    /// "any order" — the value flowing in already chose, and its choice is not
    /// recoverable here.
    Quantified,
    /// A witness sort. Already decided — [`selections_from_slot_bindings`] reads it back
    /// as a tier-1 pin, and this mechanism has nothing to add.
    Decided,
    /// A carrier with NO witness reading at all — an arrow, a tuple, an effect row, a
    /// denoted value. Split from [`Self::Decided`] rather than folded into it (code
    /// review) because the two skip for OPPOSITE reasons and calling this one "decided"
    /// asserts a witness that is not there.
    ///
    /// Skipped all the same, and the sibling reader is STILL why — but for the opposite
    /// reason to the one recorded here until WI-20260911-6B67S. This used to cite
    /// [`selections_from_slot_bindings`]' own skip and its claim that *"the requirement's
    /// own route reports it"*, concluding that refusing here "would take that report away
    /// from the route that can render it". MEASURED: no route reported it —
    /// `SortedSet[T = Int64, O = (Int64, Int64)].empty()` loaded clean and the search
    /// silently supplied a provider the author had not written.
    ///
    /// So the sibling now REFUSES (`SelectionValueNotASort`, at the producer, for both
    /// the bracket and the type channel), and this arm skips because that refusal has
    /// already happened upstream — there is nothing left here to report. The dependency
    /// runs the other way now, and is load-bearing in that direction: if the producer's
    /// refusal is ever relaxed, this arm silently goes back to dropping the binding.
    NoWitnessReading,
}

/// WI-1094 — classify one named slot's binder. See [`SlotBinderState`].
///
/// NO `subst` PARAMETER, and the absence is a claim rather than an omission: `bound` is
/// what `surface_node_binding_to_term(walk_type_deep(subst, …))` returned, and that PAIR
/// is the substitution read — the walk resolves every binding, the surfacing recovers
/// the `Value::Node`-carried ones the walk stops at. A variable surviving both is
/// therefore unbound, and re-probing `subst` here would be a second reading of one fact
/// that can only disagree with the first. [`selections_from_slot_bindings`] and
/// WI-272's type-arg stamp read these very variables through the same pair and called a
/// surviving var abstract on the same grounds.
///
/// ASKED THROUGH [`type_head`], NOT BY MATCHING CARRIERS — WI-1079's lesson, and here it
/// is load-bearing rather than tidy: the erased slot arrives in TWO forms and a
/// hand-rolled `Term::Var` test sees only one. A slot omitted at the TOP LEVEL of a
/// parameter's type is filled with the `s.O` PROJECTION ([`UnwrittenFill::Projection`]),
/// a `TypeHead::ExprCarried`; one omitted in a NESTED binding is filled with a fresh
/// `Var::Rigid`, a `TypeHead::Skolem`. Both say the same thing — the caller quantified
/// it — and `erase3`, the shape this ticket exists for, is the projection one.
fn slot_binder_state<V: TermView>(kb: &KnowledgeBase, bound: &V) -> SlotBinderState {
    match type_head(kb, bound) {
        // The only "nobody has said" carrier: an engine flex variable no seeding, no
        // argument and no expected type bound.
        TypeHead::FlexVar(vid) => SlotBinderState::Unspoken(vid),
        // Every spelling of "the enclosing signature quantified this". A skolem and the
        // two projection neutrals are WI-400 ζ's rigid types; a reflect-minted
        // `TypeVar` carries a name and nothing else, so it can decide nothing either.
        TypeHead::Skolem(_)
        | TypeHead::ExprCarried
        | TypeHead::RigidProjection
        | TypeHead::TypeVar(_) => SlotBinderState::Quantified,
        // A bare or applied SORT reference — a witness, unless the "sort" is one of the
        // enclosing declaration's own parameters, which is abstract for the same reason
        // a skolem is ([`is_type_param_value`] reads these two shapes as abstract too).
        TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => {
            if is_sort_param_symbol(kb, s) {
                SlotBinderState::Quantified
            } else {
                SlotBinderState::Decided
            }
        }
        // Everything else is a carrier with no witness reading. ENUMERATED as its own
        // answer rather than swept into `Decided` — see [`SlotBinderState::NoWitnessReading`].
        _ => SlotBinderState::NoWitnessReading,
    }
}

/// WI-1094 — the `requires` entry a named slot `binder` of the CALLEE's ENCLOSING SORT
/// demands, decoded into the goal it states at this call's bindings.
///
/// THE SORT LEVEL ONLY, which is why there is no second decoder here. An OP-scoped named
/// slot is skipped by the caller (see [`infer_named_slot_bindings`]), and writing its
/// branch anyway was measured to be actively wrong: `op_dict_entries` yields the
/// NORMALIZED `SortView` shape while [`goal_from_op_requires_entry`] decodes the BARE
/// application on purpose, so pairing them yields a binding-free goal that every provider
/// matches — the exact vacuous-check shape that function's own doc warns about.
///
/// BY SLOT INDEX, verified — [`dict_chain_index_of_named_slot`] owns the claim that
/// `NamedRequirementSlot::slot` IS the dictionary-chain index and refuses when the entry
/// found there demands another spec. Not by SPEC, which is what [`selection_goals`] does
/// and what it may do: a selection is spec-keyed, so which of two same-spec slots it
/// matched is unobservable there. Here it is observable — the two slots are two
/// PARAMETERS with two bindings, and answering one slot's goal into the other's binder
/// is a wrong dictionary that loads clean.
fn named_slot_goal(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    fn_sym: Symbol,
    owner: Symbol,
    binder: Symbol,
    span: Option<Span>,
) -> Result<Option<(RequiresEntry, SortGoal)>, TypeError> {
    // `owner` came from [`named_slot_owner`], which found the slot there, so this and the
    // index below are total. `SlotSelectionUnindexable` is still an ERROR rather than a
    // `None`: it means the declaration order and the dictionary order have drifted, and
    // pinning the wrong slot resolves a real goal with a real provider and computes a
    // wrong answer ([`dict_chain_index_of_named_slot`] argues it).
    let Some(slot) = named_requirement_slot_of(kb, owner, binder) else {
        return Ok(None);
    };
    let idx = dict_chain_index_of_named_slot(kb, owner, &slot, fn_sym, span)?;
    let Some(entry) = provider_dict_entries(kb, owner, None)
        .entries()
        .get(idx)
        .cloned()
    else {
        return Ok(None);
    };
    let concrete = substituted_entry(kb, &entry, subst);
    let goal = goal_from_requires_entry(kb, &concrete);
    Ok(goal.map(|g| (concrete, g)))
}

/// WI-1094 — WHICH DECLARATION owns the named slot `binder` of `fn_sym`, and what spec it
/// demands: the operation's own scope, else its enclosing SORT's.
///
/// [`named_slot_spec`]'s ladder with the OWNER kept, and it exists because dropping the
/// owner is what let two readers disagree about it. That function answers a `Symbol` for
/// four callers who only need the spec; this walk needs to know *whose* slot it found —
/// to skip the op-scoped case (058 §3.9) and to index the right chain — and re-deriving
/// the owner from a second ladder is how the legs drift (`impl_parent_of_op` against the
/// kind-gated `impl_parent_sort_of_op`; see [`names_any_requirement_slot`]).
///
/// The SORT-kind gate is this ladder's, deliberately: a FREE operation's "parent" is its
/// NAMESPACE, which has no dictionary chain to index, so a namespace-level slot answers
/// `None` here and the call keeps its pre-existing reading rather than being classified
/// against a chain that does not exist.
fn named_slot_owner(
    kb: &KnowledgeBase,
    fn_sym: Symbol,
    binder: Symbol,
) -> Option<(Symbol, Symbol)> {
    if let Some(slot) = named_requirement_slot_of(kb, fn_sym, binder) {
        return slot.spec_base.map(|spec| (fn_sym, spec));
    }
    let parent = impl_parent_sort_of_op(kb, fn_sym)?;
    let slot = named_requirement_slot_of(kb, parent, binder)?;
    slot.spec_base.map(|spec| (parent, spec))
}

/// WI-1094 (058 §3.4, second half) — **INFER AN OMITTED NAMED SLOT INTO THE TYPE**, and
/// REFUSE the erasure §3.9 cannot serve. Both halves are one walk because they are one
/// question asked of one binding, and splitting them is how the second gets forgotten.
///
/// §3.4: *"Omitting a named slot in type position means ANY … Omitting it at a call
/// leaves it to inference (the ladder, §3.2)."* WI-861 delivered the ladder for a
/// DISPATCH and deliberately withheld it at a named slot ([`DefaultRung`]), because a
/// dictionary-only answer writes nothing into the TYPE: `empty` would pick an order, and
/// the very next `insert(s, x)` would see an unbound `O` and pick again, independently.
/// So the answer goes into the BINDER's variable. Everything downstream is already
/// built: `resolved_ret` walks it, so the choice rides in the constructed value's type;
/// [`selections_from_slot_bindings`] reads it back at every later bracket-less call as
/// an ordinary tier-1 pin; and THIS call's own dictionary build sees the same pin,
/// because this runs before both.
///
/// **THE LADDER'S OWN ORDER IS WHAT MAKES IT SAFE, and it is not re-implemented here.**
/// [`resolve`] answers `FromScope` when the caller's frame already carries a dictionary
/// for the goal, and `FromScope` pins no impl ([`ResolvedRequiresNode::impl_sort`] is
/// `None`) — so a slot the caller supplies is left alone and keeps forwarding. Only a
/// CONSTRUCTION (`Leaf`/`Conditional`) names a provider, and only then is there anything
/// to write into the type. A tie or a miss binds nothing: the existing refusal at the
/// dictionary build is the better diagnostic, and it still fires.
///
/// **AND THE ERASURE, which is the second face of the same measurement.** Where the
/// binder is [`SlotBinderState::Quantified`] — a signature wrote `SortedSet[T = Int64]`
/// and left `O` universally quantified — a construction is not inference, it is a rival
/// dictionary for a value that already chose. MEASURED (WI-861, `erase3`): a
/// `SortedSet[T = Int64, O = Descending]` inserted into through such a signature read
/// back **3** where the slot-keeping route read **7**, the erased route having built its
/// dictionary from `Int64`'s own ascending `Ord`. §3.9 leaves two repairs — forward the
/// value's own dictionary, or refuse — and forwarding is unavailable BY CONSTRUCTION: a
/// dictionary is never carried by a value, only by a frame, so a signature that declares
/// no slot for it has nothing to forward. Hence the refusal, and hence it is
/// COUNT-INDEPENDENT: before this ticket the two-provider spelling was loud only by
/// accident of the tier-3 tie, while the one-provider spelling loaded clean and
/// constructed silently.
///
/// `Ok(())` with nothing bound is the overwhelmingly common answer — the gate is one
/// `is_empty()` on the callee's own slot index.
#[allow(clippy::too_many_arguments)]
pub(super) fn infer_named_slot_bindings(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    op: &OperationInfoFull,
    fn_sym: Symbol,
    caller_requires: &DictChain,
    param_rigids: &[(VarId, TermId)],
    selected: &[InstanceSelection],
    // WI-20260921-EE0EP — the operation whose BODY holds this call. Its chain is what
    // says whether an unwritten slot now has a channel; see the `Quantified` arm.
    enclosing_op: Option<Symbol>,
    span: Option<Span>,
) -> Result<(), TypeError> {
    if !names_any_requirement_slot(kb, fn_sym) {
        return Ok(());
    }
    // The SAME two scopes rule (1) binds and `selections_from_slot_bindings` reads, so
    // a slot reachable by a bracket key is a slot this can infer, with no third list.
    for (name, var) in call_bracket_scopes(kb, op, fn_sym) {
        // ONE LADDER, WALKED ONCE, and the owner it lands on is carried to every reader
        // below. The first cut asked twice — `named_slot_spec` here (whose parent leg is
        // `impl_parent_of_op`) and [`named_slot_goal`] again (whose leg was the
        // kind-gated `impl_parent_sort_of_op`) — which is precisely the drift
        // [`names_any_requirement_slot`]'s doc names: a free operation's "parent" is its
        // NAMESPACE, so the two legs answer differently for one, and the disagreement
        // showed up as this walk classifying a slot and then finding no goal for it —
        // i.e. SILENTLY ACCEPTING an erasure. Resolving the owner once makes the two
        // unable to disagree.
        let Some((owner, spec_sort)) = named_slot_owner(kb, fn_sym, name) else {
            continue;
        };
        // AN OP-SCOPED NAMED SLOT IS OUT OF SCOPE FOR THIS MECHANISM, and the reason is
        // the mechanism's own definition rather than caution. The answer here is written
        // into a TYPE PARAMETER so that it rides in a VALUE's type; 058 §3.9 says an
        // op-scoped requirement is "evidence about THIS CALL of THIS OPERATION, belonging
        // to no instance", so there is no value to carry it and nothing for the write to
        // buy. Such a call keeps its pre-existing reading — `[d = W]`, or
        // `UnconstrainedTypeParam` if omitted.
        //
        // WI-1091 REMOVED THE SECOND HALF of this reason, and it is worth saying that it
        // is gone rather than leaving the narrower claim looking co-signed. The half was:
        // "WI-841 says the same thing from the other side: that route is served by
        // value-directed dispatch at eval, which never sees a selection, so a bracket
        // there is refused outright once two providers answer". It no longer is — a
        // written `[d = W]` on an op-scoped slot now DECIDES
        // (`wi1094_named_slot_inference_test::an_op_scoped_named_slot_keeps_its_own_
        // reading` drives it to `LoudDesc`'s 99). Declining to INFER one is still right,
        // for the first reason alone.
        if owner == fn_sym {
            continue;
        }
        let var_term = type_param_var_term(kb, var);
        let walked = walk_type_deep(kb, subst, var_term);
        let bound = surface_node_binding_to_term(kb, subst, walked);
        let state = slot_binder_state(kb, &TermIdView(bound));
        match state {
            // Already decided by a bracket or by an argument's type — WI-844's σ read
            // pins it, and this has nothing to add. `NoWitnessReading` skips too, for the
            // OTHER reason its doc gives: the requirement's own route owns that report.
            SlotBinderState::Decided | SlotBinderState::NoWitnessReading => continue,
            // 058 §7.1's abstract form, and the ONE shape a quantified slot may take:
            // the parameter's TYPE writes the binder as one of THIS signature's own
            // declared parameters (`first(s: SortedSet[T = T, O = O])` on a sort that
            // declares `requires O: Ord[T]`). Then the caller's matching slot supplies
            // the dictionary FOR THAT PARAMETER, so what arrives is the value's own —
            // §3.9's "run time copies it along", spelled in the type.
            //
            // ASKED OF `param_rigids` — the body's parameter→skolem map — because
            // "declared here" is exactly what that map records, and no weaker test does.
            // In particular "the frame supplies SOMETHING for this spec" does NOT: a sort
            // with an ANONYMOUS `requires Ord[LT]` covers the goal and forwards, but its
            // dictionary answers a constraint of ITS OWN and is not the order the argument
            // was built with — the erase3 wrong answer, reached through a forward instead
            // of a construction. The binder having no declaration is precisely what says
            // the signature left the slot out.
            //
            // ABOVE the goal decode, for cost and for one correctness reason: this is the
            // common path in any program using §7.1's form, and `named_slot_goal` can
            // raise `SlotSelectionUnindexable`, which must not reach a call this arm
            // accepts.
            //
            // **IT MATCHES ONE OF THE THREE CARRIERS `Quantified` ADMITS, and that bound
            // is recorded rather than closed** (code review). `param_rigids` holds
            // `Var::Rigid` terms, so a binder reaching the typer as `TypeHead::TypeVar` or
            // as a `SortRef` to a sort parameter — `slot_binder_state`'s other
            // two `Quantified` carriers for the same abstract binding — can never equal an entry here
            // and would be REFUSED where a rigid forwards. Left as is on measurement, not
            // on faith: neither the suite, the corpus, nor a review probe could construct
            // a program reaching either carrier in this position, and widening the match
            // blind would add a second, undriven reading of "declared here". The failure
            // direction is also the safe one — a spurious `ErasedRequirementSlot` is loud
            // and names its repair, where the alternative is the silent wrong order this
            // whole arm exists to stop. If one ever surfaces, the fix is to ask the
            // question carrier-neutrally (resolve the binder to its canonical `VarId` and
            // match `param_rigids`' KEY), not to add a second carrier test.
            //
            // "DECLARED HERE" ADMITS A FORWARD, AND WHETHER IT IS SOUND IS DECIDED WHERE IT
            // IS ANSWERED (WI-20260923-WN9P8). It admits a PLAIN parameter as well as a
            // named slot's binder, and the dictionary build used to answer both by the
            // slot's GOAL, keyed by spec. So in `sort R3 { sort P = ?; requires OE:
            // WeakOrd[E] }` a parameter typed `SortedSet[T = E, O = P]` took `OE`'s
            // dictionary, and a set typed `ByLength` was inserted into in `RevLen`'s order.
            // The build now answers a forward out of the frame's dictionary FOR the
            // parameter ([`project_forwarded_slot`] → [`binder_frame_slot`]), or refuses it.
            // Asking "is the binder a slot" HERE instead was built at TX0G6 and reverted:
            // it also refused a plain parameter that a requirement binds a carrier's slot
            // to, which the frame does hold a dictionary for (`wi456_no_scope_route_test`'s
            // Strategy-2b rows).
            SlotBinderState::Quantified
                if param_rigids.iter().any(|(_, rigid)| *rigid == bound) =>
            {
                continue
            }
            // WI-20260921-EE0EP — SUPPLIED AFTER ALL: the binder is the WI-1059 projection
            // `p.<slot>` off a PARAMETER, and the enclosing operation's chain carries a
            // `FromParam` slot for exactly that pair. The caller fills it from the
            // ARGUMENT's own type, so this is a forward and not the rival construction
            // WI-1094 refused — the same `continue` §7.1's declared form takes above.
            //
            // ASKED OF THE CHAIN, NOT OF THE SHAPE, and the difference is the whole
            // safety of this arm. The projection's shape and the synthesized entry are
            // derived from one condition, so testing the shape alone would USUALLY agree
            // — and on the day it did not, the refusal would stand down with no slot to
            // read and the program would load clean and die at eval reading an unbound
            // `__req_*`. That is the failure the typer refuses everywhere else; so the
            // question asked here is the one that matters, "is there a slot", and the
            // shape is only how the slot is found.
            SlotBinderState::Quantified if param_supplied_slot(kb, enclosing_op, bound) => continue,
            SlotBinderState::Unspoken(_) | SlotBinderState::Quantified => {}
        }
        // BEST-EFFORT, AND NOTHING BELOW MAY BE GATED ON IT. `goal_from_requires_entry`
        // answers `None` for a spec it cannot decode, and making the REFUSAL conditional
        // on a successful decode would turn "I could not read this requirement" into "this
        // erasure is fine" — a silent accept of the one thing this function exists to
        // refuse. The `Unspoken` arm may skip on `None` (not binding is the conservative
        // direction, and the dictionary build then reports whatever it finds); the
        // `Quantified` arm uses the goal only to NAME a provider in its message.
        let decoded = named_slot_goal(kb, subst, fn_sym, owner, name, span)?;
        match state {
            SlotBinderState::Unspoken(vid) => {
                let Some((_, goal)) = decoded else {
                    continue;
                };
                // THE LADDER, WITH THE CALLER'S FRAME IN SCOPE — which is what keeps the
                // inference a rung and not an override. `resolve` answers `FromScope`
                // when the frame already carries this goal's dictionary, and `FromScope`
                // pins no impl, so nothing is written and the forward stands. Only a
                // CONSTRUCTION names a provider, and only then is there anything to put
                // in the type.
                let scope = ResolutionScope {
                    available_requires: caller_requires,
                    sigma: Some(&SigmaCtx {
                        subst,
                        param_rigids,
                    }),
                    selected,
                    sub_goal_requires: &[],
                };
                let Some(provider) = (match resolve(kb, &goal, &scope) {
                    ResolutionResult::Resolved(tree) => tree.impl_sort(),
                    // A tie or a miss binds nothing: the dictionary build's own refusal
                    // names the candidates and the bracket to write, which is the better
                    // diagnostic, and it still fires.
                    _ => None,
                }) else {
                    continue;
                };
                // The witness as a TYPE. A bare sort reference is what a written
                // `[O = ByFst]` lowers to and what `sort_functor_of` reads back, so the
                // inferred binding and the written one are one spelling.
                let witness_term = kb.alloc(Term::Ref(provider));
                subst.bind_term(kb, vid, witness_term);
            }
            SlotBinderState::Quantified => {
                // Past the skip above, so the binder is one the signature never declared.
                //
                // What a construction WOULD have taken, which is what makes the message
                // actionable. Deliberately resolved with an EMPTY scope: a frame entry
                // that merely covers the goal is the case being refused, so consulting the
                // frame here would answer `FromScope`, pin no impl, and say nothing.
                //
                // `None` DOES NOT EXCUSE THE CALL, and gating on it was a first cut that
                // MEASURED WRONG. Where the element is abstract (`Loose requires Ord[LT]`
                // over its own `LT`) no construction is possible at all, so the gate
                // declined — and the dictionary build then FORWARDED the caller's own
                // anonymous `Ord[LT]`, which is a constraint of `Loose`'s and not the
                // order the argument was built with. Driven: a `Descending` set inserted
                // into through such a body read back **3** where its own order says 7.
                // The refusal is about the slot being unsupplied, not about what a rival
                // would have been, so the provider is a detail of the MESSAGE.
                let provider = decoded.and_then(|(_, goal)| {
                    let scope = ResolutionScope {
                        available_requires: &[],
                        sigma: Some(&SigmaCtx {
                            subst,
                            param_rigids,
                        }),
                        selected,
                        sub_goal_requires: &[],
                    };
                    match resolve(kb, &goal, &scope) {
                        ResolutionResult::Resolved(tree) => tree.impl_sort(),
                        _ => None,
                    }
                });
                // WI-20260921-EE0EP — WHICH RESIDUE, read off the binder itself. A
                // projection means the parameter channel APPLIES and was declined, which
                // only the collision screen does ([`param_derived_requires`]); anything
                // else is a skolem nothing spells, so no argument could have named a
                // provider. `param_supplied_slot` has already answered `false` above, so a
                // projection reaching here had no chain entry.
                //
                // THE COLLISION SCREEN IS THE COMMON WAY THERE, NOT THE ONLY ONE, and the
                // message says "already answers" of all of them. `param_derived_requires`
                // also declines a slot whose binding does not lower, one whose
                // `dict_chain_index` drifts, and one whose goal cannot be decoded — each
                // rare, each reported here as a collision that did not happen. Recorded
                // rather than split: every one of them is a decline the author cannot act
                // on differently, and inventing a fourth message for a path no fixture
                // reaches is the undriven arm the typer has already deleted once.
                // A THIRD ARM WAS HERE AND IS GONE. `ChannelClosedByOwnRequires` reported
                // an operation that wrote its own `requires` and so got no channel — a
                // restriction that existed only while `whole_frame` was CONDITIONAL, and
                // that WI-20260921-3G1YT's unconditional form dissolved (see
                // [`op_has_param_derived_slot`]). Such an operation now TAKES the channel,
                // measured at both rival orderings, so the arm became unreachable and an
                // unreachable arm is a message nobody can check.
                let reason = if matches!(
                    extract_type(kb, &Value::term(bound)),
                    TypeExtractor::ExprCarried { .. }
                ) {
                    ErasedSlotReason::AmbiguousWithFrame
                } else {
                    ErasedSlotReason::NoReceiver
                };
                return Err(TypeError::ErasedRequirementSlot {
                    span,
                    op: fn_sym,
                    binder: name,
                    reason,
                    // The slot's spec off the ONE ladder above, not off the decoded entry:
                    // the message must not go missing with the decode.
                    spec: spec_sort,
                    provider,
                });
            }
            SlotBinderState::Decided | SlotBinderState::NoWitnessReading => {
                unreachable!("filtered above")
            }
        }
    }
    Ok(())
}

/// WI-844 — does `fn_sym` or its enclosing SORT name any requirement slot (§4.7)?
///
/// The cheap gate on [`selections_from_slot_bindings`], and its own function because
/// "the operation's scope, else its enclosing sort's" already has three askers
/// ([`call_bracket_scopes`], [`callee_requirement_slots`], [`named_slot_spec`]) and a
/// fourth spelling of it is how the parent's KIND GATE goes missing: the other two
/// that resolve a parent require it to be a `Sort`, because a FREE operation's "parent"
/// is its NAMESPACE. That changes nothing today — a namespace's slot index is empty —
/// which is exactly why the drift would be silent. WI-956 made the gate itself one
/// function ([`impl_parent_sort_of_op`]), so there is no longer a spelling to drift.
pub(super) fn names_any_requirement_slot(kb: &KnowledgeBase, fn_sym: Symbol) -> bool {
    let owns = |owner: Symbol| !kb.named_requirement_slots(owner).is_empty();
    owns(fn_sym) || impl_parent_sort_of_op(kb, fn_sym).is_some_and(owns)
}

/// WI-841 (058 §4.1 tier 1) — the witness the CALL SITE selected for `spec`, if any.
///
/// One owner for the pin criterion, because four sites ask it and each is a place
/// where explicit selection must outrank a FORWARD: the WI-239 defer pre-check and
/// `dispatch_spec_op_cached`'s defer trigger (both "the enclosing frame answers this"),
/// `resolve_inner`'s `FromScope` step, and `build_dep_projection`'s Strategies 1 & 2.
/// Those four are one statement said four times — "forwarding" has no single owner in
/// the typer (the cover predicates `entries_cover` / `requires_entry_covers_goal` /
/// `find_requires_slot` / `find_requires_location` are four askers sharing only their
/// inner pair verdict, WI-826), and folding the pin into them would push a PER-CALL
/// policy into predicates the req-insertion pass and the eval bridge also call.
///
/// `build_dispatching_dict_from_chain`'s use is NOT one of the four: it fires AFTER a
/// pinned dep already failed to resolve, and upgrades a silent `Ok(None)` degradation
/// to a refusal. Loudness, not precedence — kept distinct so the tier-1 rule is not
/// read as covering it.
pub(super) fn pinned_witness_for(
    kb: &KnowledgeBase,
    selected: &[InstanceSelection],
    spec: Symbol,
) -> Option<Symbol> {
    pinned_selection_for(kb, selected, spec).map(|s| s.witness)
}

/// WI-870 — the WHOLE selection [`pinned_witness_for`] reads its witness out of, for
/// the one caller that also needs the witness's own slot bindings ([`resolve_inner`]'s
/// step 0). Split so the four "is this pinned" askers keep asking a `Symbol` question
/// and cannot start depending on the composition.
pub(super) fn pinned_selection_for<'a>(
    kb: &KnowledgeBase,
    selected: &'a [InstanceSelection],
    spec: Symbol,
) -> Option<&'a InstanceSelection> {
    selected
        .iter()
        .find(|s| same_sort_canonical(kb, s.spec_sort, spec))
}

/// WI-870 — the slot binding, if any, that `pin` wrote for dictionary sub-goal `i`.
///
/// The SPEC half is never reachable: those slots are the SPEC's own `requires`, which
/// the provider does not declare and whose names no author can write. `checked_sub`
/// says exactly that, and says it once.
///
/// **EVERY nameable slot is one this dispatch answers**, which is why there is no
/// "this binding steers nothing" arm here — the shape that would need one does not
/// exist. A binder is minted only for a SORT-LEVEL `requires O: Spec[…]` (058 §4's
/// `:- goals` tail is a list of spec instantiations and admits no name), and since
/// proposal 066 §7 a dispatch's provider half holds exactly the provision it took — no
/// slot of it is one the dispatch declines to answer. If a condition ever gains a
/// binder, it is named here like any other.
///
/// WI-456: `slots` is either producer's list — the bracket pin's `slots`, or
/// a [`CarriedSlot::Pinned`] selection's — since both are keyed by the same chain index.
pub(super) fn slot_pin_at(
    slots: &[SlotSelection],
    i: usize,
    // WI-866: [`DictSubGoals::provider_half_start`], the PRODUCER's split point, not
    // `DictLayout::spec_len` — `chain_index` counts from where the provider walk's
    // output begins, which in the self case is 0 while the layout says `n`.
    provider_half_start: usize,
) -> Option<&SlotSelection> {
    let j = i.checked_sub(provider_half_start)?;
    slots.iter().find(|s| s.chain_index == j)
}

/// WI-456 — who wrote a slot selection: it decides how an unwritten nested binding reads
/// ([`slot_selection_of`]) and how a refusal names its source.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum SlotPinSource {
    /// A call bracket's value, `[Ord = ListOrd[OE = LexFst]]` (WI-870) — and the same
    /// application read off an ARGUMENT's type at a direct call
    /// ([`selections_from_slot_bindings`]), which shares that reader unchanged.
    Bracket,
    /// The goal's carrier type, through the provision match: `C = SortedSet[T =
    /// String, O = ByLength]` ([`carried_slot`]).
    Carrier,
}

/// WI-841 (058 §4.2) — one explicit provider selection a call site wrote:
/// `f[Spec = W](…)`. Keyed by the requirement's SPEC, because that is the coordinate
/// [`resolve`]'s goal carries (`SortGoal::spec_sort`); two slots of ONE spec are
/// therefore indistinguishable to a pin, which is why two DIFFERENT witnesses for one
/// spec are refused at the site ([`TypeError::ConflictingSelection`]) rather than
/// silently first-matched. That corner is unreachable in a loading program until 058
/// phase 3b lets two providers coexist, and it is 3b's business to give a slot-precise
/// key if it needs one.
///
/// `Hash` is load-bearing, not derived out of habit: a selection rides in
/// `resolve_cache`'s KEY (`dispatch_spec_op_cached`), and WI-870's `slots` decide the
/// answer exactly as `witness` does — two sites pinning one witness's slot differently
/// resolve differently and must not share an entry.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InstanceSelection {
    /// The spec sort of the selected requirement slot.
    pub spec_sort: Symbol,
    /// The witness sort the call named.
    pub witness: Symbol,
    /// WI-870 (058 §3.3) — what the witness's OWN named slots were bound to, written
    /// in the key's VALUE position: `fold[Monoid = ListM[O = MyEq]]`. Empty for the
    /// overwhelmingly common bare witness.
    ///
    /// This is a SEPARATE channel from `witness`, not a refinement of it, and §3.3
    /// says why: *pinning does not reach into the resolution tree*. `spec_sort` keys
    /// the goal the CALL made; these key sub-goals of the chosen provider's own
    /// dictionary, which no spec key could reach — two same-spec slots of one witness
    /// (`requires OA: Ord[A]`, `requires OB: Ord[B]`) are one spec and two
    /// answers.
    pub slots: Vec<SlotSelection>,
}

/// WI-870 (058 §3.3) — one named slot of a WITNESS, bound in a bracket value.
///
/// Keyed POSITIONALLY (`chain_index`), because the spec cannot key it: a witness may
/// declare two slots of one spec, and that is the shape 058's own example has
/// (`requires OA: Ord[A]`, `requires OB: Ord[B]`). The index is into the
/// witness's DICTIONARY CHAIN — i.e. into the PROVIDER half of the dictionary
/// [`dict_sub_goals`] lays out — and it has one owner,
/// [`dict_chain_index_of_named_slot`], per WI-857's standing lesson about positional
/// channels.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SlotSelection {
    /// The slot's binder as the author wrote it (`OA`) — for the diagnostic, which
    /// must name the slot and not merely the sub-goal.
    pub binder: Symbol,
    /// The witness that DECLARES the slot — likewise for the diagnostic, and the sort
    /// `chain_index` indexes.
    pub owner: Symbol,
    /// The slot's position in `owner`'s dictionary chain.
    pub chain_index: usize,
    /// What the value selected for the slot — recursively, since the bound witness may
    /// carry value-position bindings of its own (`W[S = X[Inner = Y]]`).
    pub selection: InstanceSelection,
}

/// WI-841 (058 §4.2 rule 1) — the type parameters a call bracket on `fn_sym` may bind:
/// the operation's own, then its ENCLOSING SORT's. Concatenated rather than laddered:
/// a name declared in both scopes is refused AT THE DECLARATION (WI-840's
/// `check_op_type_param_shadowing`), so the two lists are disjoint by construction and
/// no key can hit two targets. Were they not, an ordered ladder here would be a
/// capture the reader cannot see, which is exactly why that guard exists.
///
/// A sort parameter's `Var` is read through [`sort_type_params_as_pairs`] — whose own
/// doc calls it *"the same shape an operation's own `type_params` take"*, which is
/// exactly the splice this function performs. Reusing it also inherits its SortAlias
/// route (the one `sort_goal_from_subst` and `resolve_param_value_via_subst` read a
/// sort param by, so seeding binds the very variable the callee's signature and its
/// `requires` chain mention) and its memo. WI-954: that route is now the loader's
/// published parameter→variable map, and the `type_params_of_sort` walk the memo used
/// to shield is an owner-scope read.
///
/// KIND-GATED, for the reason the same pairing at [`rigidify_op_type_params`]'s call
/// site is: `impl_parent_of_op` strips the last segment and resolves, so a FREE
/// operation's "parent" is its NAMESPACE, which declares no type parameters and has
/// nothing to contribute.
///
/// The key is the BARE short name — the cached pairs are keyed by the QUALIFIED param
/// symbol, while a bracket key lowers to a bare interned `Symbol`
/// (`build_call_type_args`) and `op.type_params` is keyed the same way (WI-708), and
/// rung (1) matches by identity.
pub(super) fn call_bracket_scopes(
    kb: &mut KnowledgeBase,
    op: &OperationInfoFull,
    fn_sym: Symbol,
) -> Vec<(Symbol, Var)> {
    let mut declared = op.type_params.clone();
    // WI-956: the kind gate is `impl_parent_sort_of_op`'s — under `kind_of` a sort
    // whose Entity role registered first lost its params here, silently.
    let Some(parent) = impl_parent_sort_of_op(kb, fn_sym) else {
        return declared;
    };
    // Read out of the memo first: `kb.intern` below needs `&mut kb`, and the pairs are
    // an owned `Rc` snapshot, so nothing borrows `kb` across the loop.
    let pairs: Vec<(String, Var)> = sort_type_params_as_pairs(kb, parent)
        .iter()
        .filter_map(|(qualified, target)| match kb.get_term(*target) {
            Term::Var(v) => Some((
                short_name_of(kb.qualified_name_of(*qualified)).to_string(),
                *v,
            )),
            _ => None,
        })
        .collect();
    for (short, var) in pairs {
        let name_sym = kb.intern(&short);
        declared.push((name_sym, var));
    }
    declared
}

/// WI-841 (058 §4.2 rule 2) — one requirement slot a call bracket on `fn_sym` may
/// select, carrying everything either consumer needs: which SPEC it demands, whether
/// the author NAMED it, and how its goal is formed at the call's own bindings.
pub(super) struct CalleeSlot {
    /// The slot's spec base.
    pub(super) spec: Symbol,
    /// Named at the declaration? A named slot is reached by its BINDER under rule (1),
    /// so it is not its own rule-(2) candidate — but it is still SUBTRACTED from its
    /// spec's anonymous population, else `requires plus: Monoid[T]` would answer
    /// `[Monoid = …]` too and one slot would take two contradicting bindings.
    pub(super) named: bool,
    /// Where the goal comes from. The two `requires` levels store their spec in
    /// different SHAPES (see [`goal_from_op_requires_entry`]) and the dispatch slot has
    /// no entry at all, so the decoder rides with the slot rather than being re-chosen.
    pub(super) source: CalleeSlotSource,
}

pub(super) enum CalleeSlotSource {
    /// An OP-scoped `requires` clause — a bare application.
    OpRequires(RequiresEntry),
    /// The enclosing sort's `requires` — a `SortView`.
    SortRequires(RequiresEntry),
    /// A body-less spec op's own dispatch target; its goal comes from the subst.
    Dispatch,
}

/// WI-841 — the requirement slots a call bracket on `fn_sym` may select. THREE
/// sources, matching where a requirement a call must answer can be declared:
///
///  * the OPERATION's own `requires` (WI-448) — spec goals only; a VALUE precondition
///    (`requires neq(b, 0)`, WI-539) shares the clause list and is no slot, and its
///    owner is [`is_value_precondition_clause`], CALLED rather than re-derived;
///  * its ENCLOSING SORT's `requires`, which is the channel a Direct call's dictionary
///    is actually built from (`build_concrete_dispatch_dict`) and what §5.3's
///    construction-site selection binds;
///  * for a body-less SPEC op, the spec ITSELF — `Desc.describe[Desc = W](x)` has no
///    `requires` of its own, and the thing selected is the dispatching dictionary,
///    `requirements[0]` (§4.2, "a direct spec-op call is the same case").
///
/// ONE walk, because BOTH consumers need it — rung (2)'s candidate set
/// ([`resolve_call_type_arg_targets`]) and the binding-precise validation
/// ([`selection_goals`]). They were two walks, and had already drifted: only one
/// filtered value preconditions, while a doc comment asserted they could not disagree.
pub(super) fn callee_requirement_slots(kb: &mut KnowledgeBase, fn_sym: Symbol) -> Vec<CalleeSlot> {
    let mut out: Vec<CalleeSlot> = Vec::new();
    let op_entries: Vec<RequiresEntry> = op_requires_entries(kb, fn_sym)
        .into_iter()
        .filter(|e| !is_value_precondition_clause(kb, &e.spec))
        .collect();
    push_slots(
        kb,
        fn_sym,
        op_entries,
        CalleeSlotSource::OpRequires,
        &mut out,
    );
    // Same kind gate as `call_bracket_scopes`: a FREE operation's "parent" is its
    // NAMESPACE. Its requires/named-slot indexes happen to be empty today, so the gate
    // changes nothing — but two functions written against the SAME call disagreeing
    // about what that symbol is, is how a later index turns into a silent wrong list.
    // WI-956: it is now literally the same gate, `impl_parent_sort_of_op`.
    if let Some(parent) = impl_parent_sort_of_op(kb, fn_sym) {
        // WI-869: the DECLARED `requires` chain, deliberately NOT the dictionary chain
        // (`provider_dict_chain`) the layout readers use. This list is the set of slots
        // a CALL-SITE BRACKET can name (058 §4.5/§4.7), and a provision's `:- goals`
        // condition has no binder syntax and so no name — the tail is a bare list of
        // spec instantiations. Nothing positional rides on this list either: it feeds
        // selection validation, never a dictionary index, so the two chains disagreeing
        // here cannot shift a slot. Pinning a provider for a provision's condition from
        // a call site is a further increment, not a silent omission.
        let sort_entries = direct_requires_chain(kb, parent);
        push_slots(
            kb,
            parent,
            sort_entries,
            CalleeSlotSource::SortRequires,
            &mut out,
        );
        // The spec-op's own dispatch target. Only for a BODY-LESS spec op: a member
        // with a body is called directly and dispatches nothing.
        if lookup_spec_op_dispatch(kb, fn_sym).is_some() {
            out.push(CalleeSlot {
                spec: parent,
                named: false,
                source: CalleeSlotSource::Dispatch,
            });
        }
    }
    out
}

/// WI-841 — tag `entries` (all of ONE owner's) with whether each is NAMED, and append.
///
/// Named-ness is decided by MULTISET-matching the owner's recorded slots BY SPEC, not
/// by the recorded POSITION: the position indexes a list this side does not hold (see
/// [`KnowledgeBase::named_requirement_slots`] — at sort level the typer's list is the
/// FACT order, a permutation of source order). WHICH entry of a same-spec pair gets
/// tagged is therefore arbitrary, and that is sound only because it is UNOBSERVABLE:
/// an [`InstanceSelection`] is spec-keyed, so nothing downstream can tell the two
/// apart, and the only thing read off the tag is the COUNT that rung (2)'s ambiguity
/// gate needs. Said out loud because it is load-bearing and looks like an oversight.
fn push_slots(
    kb: &KnowledgeBase,
    owner: Symbol,
    entries: Vec<RequiresEntry>,
    wrap: fn(RequiresEntry) -> CalleeSlotSource,
    out: &mut Vec<CalleeSlot>,
) {
    // A recorded slot whose `spec_base` failed to decode would be dropped from this
    // multiset AND unreachable through `named_slot_spec` — so its binder would bind as
    // a plain parameter selecting nothing WHILE its spec short name stayed answerable
    // for the very slot the author named: the double-binding the tag exists to
    // prevent, silently, twice. The converter already refuses a binder whose type is
    // no spec, so this is an internal inconsistency rather than a user error.
    debug_assert!(
        kb.named_requirement_slots(owner)
            .iter()
            .all(|s| s.spec_base.is_some()),
        "WI-841: a named requirement slot of {} has no decoded spec base",
        kb.qualified_name_of(owner),
    );
    let mut named: Vec<Symbol> = kb
        .named_requirement_slots(owner)
        .iter()
        .filter_map(|s| s.spec_base)
        .collect();
    for entry in entries {
        let spec = entry.required_sort;
        // `same_sort_canonical`, not raw `==`: the two symbols come from DIFFERENT
        // decoders (the loader's `spec_base_functor` / `head_functor` vs
        // `push_op_requires_clause_term`), and a raw compare that missed would tag a
        // NAMED slot anonymous — after which rung (2) answers for a slot the author
        // already named, silently, which is what the tag exists to prevent.
        let is_named = match named.iter().position(|s| same_sort_canonical(kb, *s, spec)) {
            Some(i) => {
                named.remove(i);
                true
            }
            None => false,
        };
        out.push(CalleeSlot {
            spec,
            named: is_named,
            source: wrap(entry),
        });
    }
}

/// WI-20260911-TX0G6 — validate ONE WRITTEN requirement-slot binding at the site that
/// wrote it: 058 §3.5's call-site checks, with one owner for BOTH of proposal 035's
/// bracket spellings — the callee's (`SortedSet.empty[O = W]()`, [`seed_op_type_args`])
/// and the companion receiver's (`SortedSet[O = W].empty()`, [`seed_receiver_type_args`]).
///
/// ONE OWNER, because the two spellings are one call and were given two verdicts.
/// Only the callee leg ran these checks; the receiver leg left check 1 and the
/// no-sort-head refusal to the σ-read producer (WI-20260911-6B67S) and had no check 3
/// anywhere. MEASURED before this: `SortedSet[T = String, O = ConcOrd].empty()` loaded
/// where `SortedSet.empty[T = String, O = ConcOrd]()` was refused. Both legs now call
/// this, so they agree by construction, not because two mechanisms happen to render
/// the same bytes.
///
/// Returns the witness the binding SELECTS, or `None` when it selects nothing:
///  * A VALUE NAMING ONE OF THE ENCLOSING DECLARATION'S PARAMETERS FORWARDS (`None`).
///    `[O = OE]` written inside a sort declaring `requires OE: WeakOrd[E]` says "whatever
///    my caller's `OE` is", §7.1's form. The binding is also a TYPE ARGUMENT
///    (`binds_a_parameter`), so the σ-read producer reads that same variable back and
///    forwards it ([`is_type_param_value`]). MEASURED before TX0G6: the callee spelling
///    refused it with "R.OE does not provide WeakOrd", while the receiver spelling loaded
///    and ran the caller's `ByLength` order.
///    WHETHER THE FORWARD IS SOUND IS DECIDED WHERE IT IS ANSWERED, not here
///    (WI-20260923-WN9P8). A forward is answered by the frame's dictionary FOR that
///    parameter ([`binder_frame_slot`]): its own named slot, or a requirement that binds a
///    carrier's slot to it. A parameter with neither is refused there, with the message the
///    type channel gives for the same binding. TX0G6 gated this on "is the value a named
///    slot", which was conservative in one direction. It also refused
///    `SortedSet[T = E, O = OE]` inside a sort that `requires PersistentCollection[C =
///    SortedSet[T = E, O = OE], …]`, a sound forward the bare spelling ran. An ANONYMOUS
///    slot (rung 2) binds no parameter, so nothing downstream reads its value. Forwarding
///    there would DROP the written text and let the ordinary route answer, so it keeps
///    check 1's refusal.
///  * A value with NO SORT HEAD (a literal, an arrow, a tuple) names no provider, so it
///    is refused (`SelectionValueNotASort`) rather than dropped into the type-parameter
///    half with the slot called bound.
///  * A WITNESS gets [`validate_instance_selection`], which owns the order of checks 1
///    and 3.
///
/// NOT THE TYPE CHANNEL. A slot bound in a parameter's, a result's or a `let`'s TYPE
/// reaches [`selections_from_slot_bindings`] with no spelling here, and runs check 1
/// only. Its doc records why check 3 is not a type's.
///
/// `concrete` is the §1.1 set, built at the FIRST witness and reused: it is a scan of
/// every `SortInfo` fact, and one bracket may bind several slots.
fn validate_written_selection(
    kb: &mut KnowledgeBase,
    fn_sym: Symbol,
    spec_sort: Symbol,
    value: &Value,
    binds_a_parameter: bool,
    concrete: &mut Option<std::collections::HashSet<Symbol>>,
    span: Option<Span>,
) -> Result<Option<Symbol>, TypeError> {
    if binds_a_parameter && view_is_abstract_type_param(kb, value) {
        return Ok(None);
    }
    let witness = selection_witness_sym(kb, value).ok_or(TypeError::SelectionValueNotASort {
        span,
        op: fn_sym,
        spec: spec_sort,
    })?;
    let concrete = concrete.get_or_insert_with(|| crate::kb::load::sorts_with_constructors(kb));
    validate_instance_selection(kb, fn_sym, spec_sort, witness, concrete, span)?;
    Ok(Some(witness))
}

/// WI-841 (058 §4.4) — validate one explicit selection at the site that wrote it.
///
/// Check 3 first, because it is a refusal of the WHOLE spelling rather than a
/// complaint about this witness: where the provider is CONCRETE (a sort with
/// constructors), its values carry their own sort and value-directed dispatch is
/// already deciding (§1.1 — the very exemption the witness-coherence grouping
/// applies, read through its owner `sorts_with_constructors` so the two cannot
/// drift). An explicit witness there could only agree redundantly or contradict
/// silently, so §4.4 says refuse, do not prefer.
///
/// `concrete` is the §1.1 set, passed in rather than recomputed: it answers in BULK (a
/// scan of every `SortInfo` fact) and is built ONCE per written bracket by the caller.
///
/// NOT `KnowledgeBase::sort_has_constructors`, which exists and which
/// `carrier_is_abstract_spec` calls — the two are DIFFERENT criteria, not two spellings
/// of one: this set reads `SortInfo.constructors`, that predicate scans for
/// `Entity`-kind children of the sort's qualified name. §1.1's exemption is the FORMER
/// (`check_provider_operations`' `concrete.contains(&p.carrier)`), so that is the one to
/// share; using the per-sort predicate here would silently answer a different question.
/// Membership is probed BOTH raw and canonical because the set is keyed on the raw
/// `SortInfo.name` symbol while the witness arrives from a resolved call-site
/// reference — the existing consumer probes raw, so probing only the canonical form
/// could miss. WI-843 gave that probe ONE owner ([`is_value_directed_provider`]),
/// shared with the tier-3 diagnostic: the two must agree about which providers a
/// bracket may name, or the message advertises what this check refuses.
///
/// Check 1 is BASE-level here: does `witness` provide `spec` at all. The
/// BINDING-precise half — "whose spec view unifies with the goal" — is [`resolve`]'s
/// step 0, which filters the goal's own candidate set to the pinned impl and so
/// answers it exactly, at the one place the goal exists. The split is deliberate:
/// this rung owns the message for the two typos worth naming both halves for (a
/// non-provider, and a provider of a DIFFERENT spec); step 0 owns the case where the
/// witness provides the spec but not at these bindings, where the goal must be
/// rendered to say anything useful.
///
/// Check 2 ("the slot exists on the callee") is [`resolve_call_type_arg_targets`] —
/// a key that names no slot never becomes a selection.
///
/// CHECK 3's CRITERION IS THE NAMED SORT'S, and that is DECIDED rather than inherited
/// (WI-20260911-TX0G6, 2026-09-23; kernel-language §5.4, proposal 058 §3.5). The test is
/// "the witness has constructors". The reason for it — the VALUE directs the dispatch —
/// holds where the witness IS its provision's carrier: `[WeakOrd = Pair]` on two pairs
/// answers what the bare call answers. It does not hold for a concrete witness of ANOTHER
/// carrier, which no argument ever is. Measured with this check switched off,
/// `[WeakOrd = ConcOrd]` on two `String`s answers ConcOrd's order and not the bare
/// call's, and a NAMED slot bound to `ConcOrd` orders by it. The type channel, which
/// never runs this check, honours `O = ConcOrd` the same way.
///
/// Narrowing the test to "is the witness the arguments' own sort" was offered and
/// DECLINED: the rule is kept readable off the declaration, and such a sort is made
/// selectable by declaring it without constructors. So for that shape the refusal is a
/// rule about what may be WRITTEN, and [`TypeError::ValueDirectedSelection`]'s message
/// gives its reason conditionally rather than claiming the selection is redundant.
pub(super) fn validate_instance_selection(
    kb: &mut KnowledgeBase,
    fn_sym: Symbol,
    spec_sort: Symbol,
    witness: Symbol,
    concrete: &std::collections::HashSet<Symbol>,
    span: Option<Span>,
) -> Result<(), TypeError> {
    // Check 1 FIRST. Check 3's message asserts that `witness` IS a provider of `spec`
    // and that the value therefore decides — both false for a sort that provides
    // nothing, and MEASURED: `[Monoid = Conc]` on a constructor-bearing `Conc` with no
    // provision reported "Conc is a CONCRETE provider of Monoid", telling the author
    // their typo was a coherence rule. Ordering check 3 first was justified as "a
    // refusal of the WHOLE spelling", which only holds once the witness provides.
    check_witness_provides_spec(kb, fn_sym, spec_sort, witness, span)?;
    if is_value_directed_provider(kb, concrete, witness) {
        return Err(TypeError::ValueDirectedSelection {
            span,
            op: fn_sym,
            witness,
            spec: spec_sort,
        });
    }
    Ok(())
}

/// §4.4 CHECK 1 ALONE — does `witness` provide `spec_sort` anywhere at all.
///
/// Its own function because WI-870 gave it a second caller and check 3 did NOT get
/// one: a slot of a witness is a dictionary slot the typer resolves, with no value to
/// direct it, so the value-directed refusal has nothing to say there
/// ([`witness_value_slot_selections`] argues it). Sharing the check that IS common
/// makes that split structural — a change to check 1's criterion cannot reach one
/// caller and miss the other, which is how the two would drift about what "provides"
/// means.
fn check_witness_provides_spec(
    kb: &KnowledgeBase,
    fn_sym: Symbol,
    spec_sort: Symbol,
    witness: Symbol,
    span: Option<Span>,
) -> Result<(), TypeError> {
    if impl_sorts_providing_spec(kb, spec_sort)
        .iter()
        .any(|s| same_sort_canonical(kb, *s, witness))
    {
        return Ok(());
    }
    Err(TypeError::WitnessDoesNotProvide {
        span,
        op: fn_sym,
        witness,
        spec: spec_sort,
        at_bindings: false,
    })
}

/// WI-839: the call-site bracket bindings this application wrote, or `None` when it
/// wrote none (and for a non-`Apply` occurrence, which carries no such channel).
pub(super) fn call_type_args_of(
    occ: &Rc<NodeOccurrence>,
) -> Option<&[(Option<Symbol>, crate::eval::value::Value)]> {
    match &occ.kind {
        NodeKind::Expr {
            expr: Expr::Apply { type_args, .. },
            ..
        } if !type_args.is_empty() => Some(type_args),
        _ => None,
    }
}

/// WI-20260829-W6JH0 — the form-(3) COMPANION RECEIVER's type on this call, if it wrote
/// one (`Map[K = String, V = Int64].empty()`). The twin of [`call_type_args_of`] on the
/// channel beside it.
pub(super) fn call_recv_type_of(occ: &Rc<NodeOccurrence>) -> Option<&crate::eval::value::Value> {
    match &occ.kind {
        NodeKind::Expr {
            expr: Expr::Apply { recv_type, .. },
            ..
        } => recv_type.as_ref(),
        _ => None,
    }
}

/// WI-841 (058 §4.2) — what ONE call-site bracket binding names.
#[derive(Clone, Copy, Debug)]
enum CallTypeArgTarget {
    /// Rule (1) landed on an ordinary declared type parameter — the operation's or
    /// its enclosing sort's. Today's meaning, unchanged.
    Param(Var),
    /// Rule (1) landed on a parameter that is a NAMED REQUIREMENT SLOT's binder. Its
    /// value is a WITNESS, so the binding does both jobs: it pins the parameter (the
    /// witness becomes part of the type — §4.7's `SortedSet[T = String, O = ByLength]`)
    /// and it selects the provider for that slot.
    NamedSlot(Var, Symbol),
    /// Rule (2) — a spec SHORT NAME, unambiguous among the callee's anonymous slots.
    /// A gated shorthand for the same selection; there is no parameter to pin.
    AnonSlot(Symbol),
}

impl CallTypeArgTarget {
    /// The type-parameter variable to unify the written value into, if any.
    pub(super) fn param(self) -> Option<Var> {
        match self {
            CallTypeArgTarget::Param(v) | CallTypeArgTarget::NamedSlot(v, _) => Some(v),
            CallTypeArgTarget::AnonSlot(_) => None,
        }
    }

    /// The SPEC of the requirement slot this binding selects a provider for, if any.
    fn slot_spec(self) -> Option<Symbol> {
        match self {
            CallTypeArgTarget::NamedSlot(_, s) | CallTypeArgTarget::AnonSlot(s) => Some(s),
            CallTypeArgTarget::Param(_) => None,
        }
    }
}

/// WI-839/WI-841: match each call-site bracket binding to what it names — returning
/// one target per binding, PARALLEL TO `type_args`. Every binding lands on a target of
/// its OWN or the call is refused; nothing is skipped, which is why the result can be
/// zipped positionally, and NO SLOT IS BOUND TWICE.
///
/// Named keys resolve in the §4.2 order:
///   1. a declared TYPE PARAMETER — matched by SYMBOL IDENTITY (`n == name_sym`),
///      because both sides are the bare spelling: a key lowers to a bare interned
///      `Symbol` ("the param label … NOT a caller-scope value", `build_call_type_args`)
///      and `op.type_params` holds `kb.intern("T")` (WI-708). `declared` spans the
///      operation's scope and its enclosing sort's ([`call_bracket_scopes`]).
///   2. a requirement's SPEC SHORT NAME among the callee's remaining ANONYMOUS slots.
///      This one cannot match by identity — its candidates are the slots' CANONICAL,
///      qualified spec symbols — so it is a NAME LOOKUP, `same_label`'s sanctioned
///      family 2, and **the "unambiguous" clause IS the gate that makes it sound**:
///      without it this is the short-name identity comparison WI-672 deleted.
///
/// A QUALIFIED key never reaches rung 2 and is not resolved: it is refused with the
/// rung-1 diagnostic, exactly as it is today (measured — `idy[Id.T = Int64]` is
/// `unknown type-param 'Id.T'`). Three reasons, in §4.2's order of force: rule (1)'s
/// key is unresolvable IN PRINCIPLE (`T` is a binder of the callee, visible in no
/// scope), so a ladder mixing them would rank a label against a reference and
/// resolve-then-fall-back is a fallback; a resolved key would make selection depend on
/// the CALLER's imports, while the supply path takes no scope at all; and it buys no
/// expressiveness, since every selection a short name cannot express is written with
/// the §4.7 named slot, which puts it under rule (1). Gating rung 2 on a bare key also
/// keeps `same_label`'s own `debug_assert` — which fires on a partially-qualified pair
/// — out of reach.
///
/// Every one of the four refusals is a binding the author WROTE that would otherwise
/// have meant nothing:
///   * a named key matching no parameter and no slot — `NoSuchTypeParam`;
///   * a key matching two or more slots — `AmbiguousRequirementKey` (rung 2's gate);
///   * the same key twice — `DuplicateCallTypeArg`. Both copies resolve to one var, so
///     the second unification contradicts the first and `unify_types`' verdict is
///     discarded at the caller. The guard WI-805 / WI-808 / WI-809 already put on tuple
///     labels, entity fields and named ARGUMENT lists; this list had none;
///   * a positional with no slot LEFT — `ExcessCallTypeArgs`. "Left", not "declared":
///     `idy[T = Int64, String]` over-applies a one-param callee, and measuring the
///     positionals against `declared.len()` called that within budget while the
///     positional silently re-targeted the slot the named key had taken.
///
/// POSITIONAL bindings stay rung (1) only. A requirement slot has no position a caller
/// could count to — the two lists it might index (`op_requires_entries` and the
/// enclosing sort's) are separate, and the sort-level one is the FACT order at every
/// typer-side reader — so a positional selection would be a coordinate nobody can
/// read off the source. Selection is written by NAME or not at all.
fn resolve_call_type_arg_targets(
    kb: &KnowledgeBase,
    type_args: &[(Option<Symbol>, crate::eval::value::Value)],
    declared: &[(Symbol, Var)],
    positional_limit: usize,
    slots: &[CalleeSlot],
    fn_sym: Symbol,
    span: Option<Span>,
) -> Result<Vec<CallTypeArgTarget>, TypeError> {
    // Which declared slots a NAMED key claims. Collected up front because a positional
    // must skip them wherever it sits in the list — the surface convention is
    // positional-first, but nothing in the grammar enforces it.
    let mut taken = vec![false; declared.len()];
    let mut named_targets: Vec<(Symbol, CallTypeArgTarget)> = Vec::new();
    for (name_opt, _) in type_args.iter() {
        let Some(name_sym) = name_opt else { continue };
        if let Some(idx) = declared.iter().position(|(n, _)| n == name_sym) {
            if std::mem::replace(&mut taken[idx], true) {
                return Err(TypeError::DuplicateCallTypeArg {
                    span,
                    op: fn_sym,
                    name: *name_sym,
                });
            }
            let var = declared[idx].1;
            // A parameter that IS a named slot's binder selects as well as pins. Read
            // off the slot record by BINDER, so the two facts about the name — that it
            // is a parameter and which requirement it names — come from the two places
            // that own them.
            let target = named_slot_spec(kb, fn_sym, *name_sym)
                .map_or(CallTypeArgTarget::Param(var), |spec| {
                    CallTypeArgTarget::NamedSlot(var, spec)
                });
            named_targets.push((*name_sym, target));
            continue;
        }
        // Rung 2. A QUALIFIED key is not a slot name — it is refused below with the
        // rung-1 message, which is what it already gets today.
        let written = kb.local_name_of(*name_sym);
        let matched: Vec<Symbol> = if written.contains('.') {
            Vec::new()
        } else {
            slots
                .iter()
                .filter(|s| !s.named && same_label(kb, *name_sym, s.spec))
                .map(|s| s.spec)
                .collect()
        };
        match matched.len() {
            0 => {
                return Err(TypeError::NoSuchTypeParam {
                    span,
                    op: fn_sym,
                    name: *name_sym,
                })
            }
            1 => {
                if named_targets.iter().any(|(n, _)| n == name_sym) {
                    return Err(TypeError::DuplicateCallTypeArg {
                        span,
                        op: fn_sym,
                        name: *name_sym,
                    });
                }
                named_targets.push((*name_sym, CallTypeArgTarget::AnonSlot(matched[0])));
            }
            _ => {
                return Err(TypeError::AmbiguousRequirementKey {
                    span,
                    op: fn_sym,
                    name: *name_sym,
                    slots: matched
                        .iter()
                        .map(|s| kb.qualified_name_of(*s).to_string())
                        .collect(),
                })
            }
        }
    }
    // Over the operation's OWN parameters, matching what a positional may reach.
    let free = taken.iter().take(positional_limit).filter(|t| !**t).count();

    let mut targets = Vec::with_capacity(type_args.len());
    let mut next_free = 0;
    for (name_opt, _) in type_args.iter() {
        let target = match name_opt {
            // Re-found rather than carried over as an index: the pass above records
            // slot OCCUPANCY, and threading indices out of it would be a second list to
            // keep aligned with this one for no gain — a bracket is a handful of keys.
            Some(name_sym) => named_targets
                .iter()
                .find(|(n, _)| n == name_sym)
                .map(|(_, t)| *t)
                .expect("named key resolved in the pass above"),
            None => {
                while next_free < positional_limit && taken[next_free] {
                    next_free += 1;
                }
                match declared
                    .get(next_free)
                    .filter(|_| next_free < positional_limit)
                {
                    Some((_, v)) => {
                        taken[next_free] = true;
                        CallTypeArgTarget::Param(*v)
                    }
                    None => {
                        return Err(TypeError::ExcessCallTypeArgs {
                            span,
                            op: fn_sym,
                            given: type_args.iter().filter(|(n, _)| n.is_none()).count(),
                            free,
                        })
                    } // (`free` counts the operation's own free slots — see below.)
                }
            }
        };
        targets.push(target);
    }
    Ok(targets)
}

/// WI-841 (058 §4.4 check 1) — the BINDING-PRECISE half of witness validation, run at
/// the call site once `subst` is complete: for each goal this call's selections will
/// be applied to, the pinned witness must be among the goal's own candidates.
///
/// AT THE SITE, not at each consumer, and that is the point. A requirement slot is
/// served by one of three routes — the parent sort's dictionary build, the spec-op
/// dispatch, or (for an OP-SCOPED `requires`) value-direction at eval, which does not
/// read the call's selections (WI-822 LEG 1 gave that chain a dictionary channel, but
/// the body reads it only where value-direction cannot serve the call — see
/// [`op_scoped_defer_location`]). Measured: without this
/// check, a witness that provides the spec at OTHER bindings was refused by the
/// spec-op route, loaded clean and died `Internal` on the dictionary route, and was
/// silently IGNORED on the value-directed one. One site, one verdict.
///
/// Refuses only when the goal HAS candidates and none is the pinned witness. A goal
/// with no candidates at all is under-determined here (an abstract element inside a
/// generic body) and says nothing about the pin — its own route reports it. That
/// asymmetry is what keeps this from false-refusing a correct polymorphic call.
///
/// TWO LIMITS, stated here rather than left to a test comment:
///
///  * this is the COARSE σ mode (`collect_provides_candidates(.., None)`), while
///    `resolve`'s step 0 filters under the call's own σ. Coarse admits a superset, so
///    this rung can only ever under-refuse — never refuse a call step 0 would accept —
///    which is the safe direction for a check whose job is to catch what the other
///    routes cannot report at all.
///  * on the VALUE-DIRECTED route a selection is **not honoured at all**: `selections`
///    never reach eval, so `requirements_for_value_directed_impl` resolves with an
///    empty scope and no pin. This was first written here as "unobservable before 058
///    phase 3b, since with one provider the searched answer IS the pinned one" — which
///    was FALSE and never measured. Driven: with `AddM` and `AnyM` both answering,
///    `probe[Monoid = AddM](2, 3)` computed **99**, `AnyM`'s answer, in a program that
///    loaded. So it is refused above whenever two or more providers answer, and
///    accepted only where the pin provably cannot differ. WI-822 LEG 1 gave the
///    op-scoped chain a dictionary channel and this stayed: the channel exists and its
///    call-site supply honours the pin, but the BODY reads it only where
///    value-direction cannot serve the call (see [`op_scoped_defer_location`]).
pub(super) fn check_selection_bindings(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    fn_sym: Symbol,
    selections: &[InstanceSelection],
    span: Option<Span>,
) -> Result<(), TypeError> {
    if selections.is_empty() {
        return Ok(());
    }
    for sel in selections {
        for goal in selection_goals(kb, subst, fn_sym, sel.spec_sort) {
            let candidates = collect_provides_candidates(kb, &goal, None);
            if candidates.is_empty() {
                continue;
            }
            if !candidates
                .iter()
                .any(|c| same_sort_canonical(kb, c.impl_sort, sel.witness))
            {
                return Err(TypeError::WitnessDoesNotProvide {
                    span,
                    op: fn_sym,
                    witness: sel.witness,
                    spec: sel.spec_sort,
                    // EVERY producer establishes this now, which is what makes the
                    // literal honest. It used to read "reached only past
                    // `validate_instance_selection`" and name that one caller — true of
                    // the BRACKET producer and FALSE of the σ-READ one
                    // ([`selections_from_slot_bindings`]), which ran check 1 on a
                    // witness's NESTED slots and on none of its top-level ones.
                    // WI-20260911-6B67S: a witness providing NOTHING was therefore told
                    // it "provides WeakOrd, but not at the bindings this call needs",
                    // through the RECEIVER bracket and — with no bracket written anywhere
                    // — through an ARGUMENT whose type carries the slot.
                    //
                    // FIXED AT THE PRODUCER, not here. Making this rung ASK was tried and
                    // is the worse shape: it leaves the invariant false and buys one
                    // consumer a true message, while `selections_from_slot_bindings`'
                    // OTHER caller (the eta path, which runs no `check_selection_bindings`
                    // at all) keeps an unchecked selection. The producer now runs check 1
                    // itself, so every selection reaching this loop has passed it and
                    // `true` is the only thing this branch can mean.
                    at_bindings: true,
                });
            }
        }
    }
    Ok(())
}

/// WI-841 — the goals a selection of `spec_sort` at a call to `fn_sym` will be
/// applied to, at the call's own bindings.
///
/// Reads [`callee_requirement_slots`] — the SAME enumeration rung (2)'s candidate set
/// reads — rather than re-walking the three sources. It was a second walk, and the two
/// had already drifted (only one filtered value preconditions) while a doc comment
/// asserted they could not disagree. One walk is the enforcement; a comment was not.
fn selection_goals(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    fn_sym: Symbol,
    spec_sort: Symbol,
) -> Vec<SortGoal> {
    let slots: Vec<CalleeSlot> = callee_requirement_slots(kb, fn_sym)
        .into_iter()
        .filter(|s| same_sort_canonical(kb, s.spec, spec_sort))
        .collect();
    let mut goals: Vec<SortGoal> = Vec::new();
    for slot in slots {
        // WI-1091 — EVERY SLOT'S ROUTE CAN NOW THREAD A SELECTION, so this walk no
        // longer answers a second question alongside the goal.
        //
        // It used to carry a `threaded` flag, false for `CalleeSlotSource::OpRequires`,
        // and `check_selection_bindings` turned that into `TypeError::
        // UnthreadableSelection` wherever two providers answered. The claim behind it was
        // measured and was true: an op-scoped requirement was served by value-directed
        // dispatch, which never sees `selections`, so `probe[Monoid = AddM](2, 3)`
        // computed 99 — the provider the author did not name — and refusing beat
        // computing that. WI-1091 changed the placement rather than the claim: a body
        // call licensed by its enclosing operation's own `requires` now READS that slot,
        // and the call-site supply has honoured the bracket since WI-822 LEG 1
        // ([`build_op_scoped_dicts`] threads `selected` into [`build_dep_projection`]).
        // The refusal and its `TypeError` variant went with the flag rather than being
        // left as a condition that can no longer hold — `wi841_call_site_selection_test::
        // an_op_scoped_selection_decides_and_the_value_shows_it` drives the 5/5/99 that
        // replaced it.
        let goal = match slot.source {
            // Formed as `dispatch_spec_op_cached` forms it. No carrier: the
            // receiver-carrier classification runs further down, and this check only
            // asks whether the witness is AMONG the candidates — a carrier can only
            // narrow that set, never admit a witness it excludes.
            CalleeSlotSource::Dispatch => Some(sort_goal_from_subst(kb, subst, spec_sort, None)),
            // The two levels are decoded by DIFFERENT readers because they are stored
            // in different SHAPES — see [`goal_from_op_requires_entry`].
            CalleeSlotSource::SortRequires(entry) => {
                let concrete = substituted_entry(kb, &entry, subst);
                goal_from_requires_entry(kb, &concrete)
            }
            CalleeSlotSource::OpRequires(entry) => {
                let concrete = substituted_entry(kb, &entry, subst);
                goal_from_op_requires_entry(kb, &concrete)
            }
        };
        goals.extend(goal);
    }
    goals
}

/// WI-841 — a `requires` entry with the call-site bindings substituted in, so its
/// goal is the one THIS call must answer.
fn substituted_entry(
    kb: &mut KnowledgeBase,
    entry: &RequiresEntry,
    subst: &Substitution,
) -> RequiresEntry {
    RequiresEntry {
        required_sort: entry.required_sort,
        spec: substitute_spec_via_subst(kb, &entry.spec, subst),
        supply: entry.supply,
    }
}

/// WI-841 — the goal an OP-SCOPED `requires Monoid[T = HT]` clause states.
///
/// Deliberately NOT [`goal_from_requires_entry`], and the difference is not
/// cosmetic: that one decodes a `SortView`, which is the shape a SORT-level
/// requirement's `spec` FIELD carries, and for the BARE APPLICATION an op-scoped
/// clause is (`push_op_requires_clause_term` reads the clause's own head functor AS
/// the spec base — which a `SortView`'s head never is) it falls into the
/// "nullary sort" arm and returns NO bindings at all. A goal with no bindings is
/// matched by EVERY provider, so routing an op-scoped clause through it would make
/// the selection check pass vacuously — worse than not running it, because it reads
/// as covered. Measured: a witness providing the spec at other bindings was accepted
/// at an op-scoped call and silently ignored.
///
/// The binding FILTER is the same one — `is_type_param_binding` — so the two readers
/// agree on which named arguments are type parameters and which are op bindings.
///
/// **POSITIONALS COUNT, and reading only named args made this vacuous for the
/// stdlib's own spelling.** `requires Eq[T]` (`prelude/list.anthill:58`) and
/// `requires Ring[F]` (`algebra.anthill`) bind POSITIONALLY; measured, the named
/// spelling `requires Monoid[T = HT]` refused a wrong-bindings pin while the
/// positional twin `requires Monoid[HT]` loaded clean — the exact failure mode this
/// reader exists to close, on the more common spelling. Positionals fill the params
/// no named binding took, in declaration order, which is the idiom
/// `check_provider_operations` and `requirement_ranges_over_owner_tparams` already
/// use for the same bare-application shape.
///
/// THE FORK IS DOCUMENTED HERE, NOT OWNED. `RequiresEntry.spec` has two shapes and
/// FOUR readers that disagree about the bare one: `unwrap_spec_view` drops its
/// bindings, `entry_type_param_bindings` rejects it structurally, and
/// `requirement_ranges_over_owner_tparams` reads it fully. The deeper fixes are to
/// normalize at the producer (`push_op_requires_clause_term` emitting the `SortView`
/// shape the sort path emits) or to make `unwrap_spec_view`'s bare arm return its
/// named args — the latter is one line and would incidentally fix `entries_cover`,
/// where an op-scoped `requires Monoid[T = HT]` currently decodes to empty bindings
/// and so vacuously covers ANY `Monoid[…]` dep. Both are wider than this ticket and
/// carry real regression surface across the requires-forwarding predicates.
pub(super) fn goal_from_op_requires_entry(
    kb: &mut KnowledgeBase,
    entry: &RequiresEntry,
) -> Option<SortGoal> {
    let (mut bindings, positional) = op_requires_application_bindings(kb, entry)?;
    for (name, val) in positional {
        // The BARE short name: `goal_binding_value` matches a goal key against a
        // candidate's by RESOLVED SHORT NAME (with a symbol-identity fast path),
        // so the two need only render alike.
        let key = kb.intern(&name);
        bindings.push((key, val));
    }
    Some(SortGoal {
        spec_sort: entry.required_sort,
        bindings,
        carrier: None,
    })
}

/// WI-841 — the SPEC of the requirement slot named `binder` on `fn_sym` or on its
/// enclosing sort, or `None` when `binder` is an ordinary type parameter. Both scopes,
/// for the same reason rule (1) spans both: a sort's named slot is bindable at a call
/// on its member (§5.3's construction site) as well as in a type application.
fn named_slot_spec(kb: &KnowledgeBase, fn_sym: Symbol, binder: Symbol) -> Option<Symbol> {
    // WI-870 gave "the slot named `binder` on `owner`" its own reader; this is that
    // reader over the callee's two scopes, so the two cannot disagree about which
    // declaration a binder names.
    let find = |owner: Symbol| named_requirement_slot_of(kb, owner, binder)?.spec_base;
    find(fn_sym).or_else(|| impl_parent_of_op(kb, fn_sym).and_then(find))
}

/// WI-841 — the WITNESS SORT a bracket binding's value names, or `None` when the value
/// is not a sort at all. A witness may be written with type arguments
/// (`[Monoid = ListM[O = MyEq]]`, §4.5), so the HEAD is what identifies it.
fn selection_witness_sym(kb: &KnowledgeBase, value: &Value) -> Option<Symbol> {
    // `sort_functor_of_view` IS the two admissible cases — a bare sort, or a
    // parameterized one whose BASE identifies the witness (a witness may carry type
    // arguments, §4.5). Every other `TypeHead` is not a sort, and saying so here is
    // the point: a second, coarser head read would hand the diagnostic an internal
    // wrapper name as though it were the witness. MEASURED for one of them — `[Monoid
    // = 42]` lowers to a WI-302 denoted value, which reported
    // `TypeExtractor.Denoted does not provide Monoid`.
    sort_functor_of_view(kb, value)
}

/// WI-329 (proposal 045 §5.6) — HANDLER DISCHARGE, the inference half: bind each of the
/// callee's still-unbound flexible row tails to the RESIDUAL its callback arguments
/// force, once every argument has been unified.
///
/// A handler is `(body: () -> X @ {K, ρ}) -> X @ {ρ}`, so the call's row IS `ρ` and `ρ`
/// must come out as `body`'s row minus `K`. Ordinary unification already delivers that
/// whenever the body DOES perform `K`: the declared row's extras are then empty and
/// `unify_effect_rows`' closed/open arm binds `ρ := only_a`. It delivers nothing when the
/// body does NOT perform `K` — a pure body, or the outer of two handlers for the same
/// label — because the declared `K` has no counterpart in the actual row, which is not an
/// EQUALITY, and that arm refuses without binding. Callback conformance is SUBTYPING, not
/// equality (`validate_arg_against_param` owns the verdict; the arg loops discard unify's
/// boolean), so such a call is admissible and `ρ` is simply underdetermined by that one
/// argument.
///
/// WHY THIS IS A SEPARATE PASS AND NOT A BINDING INSIDE THAT ARM. `ρ` is constrained by
/// EVERY parameter that mentions it, and the answer is their UNION. Binding per-argument
/// inside the relation takes the first argument's least solution and CLOSES the tail, so
/// a later argument with a real contribution is refused — measured on `two[Rho](a: () ->
/// Int64 @ {Error[Int64], Rho}, b: () -> Int64 @ {Rho})` at a pure `a` and a `{Clock}`
/// `b`, which stopped loading. Running once, after both arg loops, makes the result
/// order-independent and leaves `unify_effect_rows` a clean equality that does not leak
/// bindings on refusal.
///
/// DELIBERATELY NARROW — every skip below leaves the tail unbound, which is the
/// pre-existing behavior (`check_unconstrained_type_params` then reports it), never a
/// wrong binding:
///   * a tail already bound by unification, or a RIGID one (a forall-Skolem is not ours
///     to solve — WI-336);
///   * a declared row with no tail (closed: nothing to infer) or with TWO (a row UNION,
///     `{E, EffP}` — which lower bound belongs to which tail is not decidable here;
///     WI-20260820-RDNS4 carries that question one level up);
///   * an actual row that is itself OPEN or carries `- e` absents — those are the shapes
///     the unify/subtype arms reason about with their own tail machinery.
///
/// The residual is [`cover_present_labels`]'s `only_a`: the actual's present labels that
/// no declared present label covers. That is exactly "the body's row minus the handled
/// labels", computed by the same relation the subtype path uses, so the two cannot drift.
pub(super) fn infer_discharged_row_tails(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    op: &OperationInfoFull,
    pairs: &[(Value, Value)],
) {
    if op.type_params.is_empty() || pairs.is_empty() {
        return;
    }
    // Cheap gate: nothing to solve unless some declared type param is still a bare var.
    // (The same probe `check_unconstrained_type_params` makes, so the pass runs only on
    // the calls that would otherwise be refused for an unconstrained parameter.)
    let any_unbound = op.type_params.iter().any(|(_, var)| {
        let t = type_param_var_term(kb, *var);
        let resolved = walk_view(kb, subst, &TermIdView(t));
        resolved_var(kb, &resolved).is_some()
    });
    if !any_unbound {
        return;
    }

    // Lower bounds per tail, accumulated across every callback parameter naming it.
    let mut lower: Vec<(TermId, Vec<Value>)> = Vec::new();
    for (declared, actual) in pairs {
        if !type_head_is_callable(kb, declared) {
            continue;
        }
        let Some((_, _, Some(d_eff))) = arrow_parts(kb, declared) else {
            continue;
        };
        let d_row = canonical_effects_row(kb, &d_eff);
        let Some((d_present, d_tails, _)) = decompose_effect_row(kb, subst, &d_row) else {
            continue;
        };
        if d_tails.len() != 1 {
            continue;
        }
        let tail = walk_type(kb, subst, d_tails[0]);
        if !matches!(kb.get_term(tail), Term::Var(Var::Global(_))) {
            continue;
        }
        let Some((_, _, Some(a_eff))) = arrow_parts(kb, actual) else {
            continue;
        };
        let a_row = canonical_effects_row(kb, &a_eff);
        let Some((a_present, a_tails, a_absent)) = decompose_effect_row(kb, subst, &a_row) else {
            continue;
        };
        if !a_tails.is_empty() || !a_absent.is_empty() {
            continue;
        }
        let (only_a, _) = cover_present_labels(kb, subst, &a_present, &d_present);
        match lower.iter().position(|(t, _)| *t == tail) {
            Some(i) => {
                for l in only_a {
                    let dup = lower[i]
                        .1
                        .iter()
                        .any(|x| resolved_labels_equal(kb, subst, x, &l));
                    if !dup {
                        lower[i].1.push(l);
                    }
                }
            }
            None => lower.push((tail, only_a)),
        }
    }

    for (tail, labels) in lower {
        // Re-read: `cover_present_labels` unifies as it pairs, so an earlier iteration
        // may already have bound this tail. Binding a second time would contradict.
        let t = walk_type(kb, subst, tail);
        if !matches!(kb.get_term(t), Term::Var(Var::Global(_))) {
            continue;
        }
        // The verdict is DISCARDED, and these are the refusals it can carry — `t` is a
        // `Var::Global` by the gate above and `final_tail` is `None`, so the not-bindable
        // and non-Var arms cannot fire, leaving: a `lacks` violation (WI-328), a
        // denoted-bearing (`Value::Node`) extra label (deferred at `bind_row_tail` as
        // WI-342 P4-B), a prelude-less KB, the occurs check, and a σ contradiction. Each
        // leaves `tail` unbound, and the symptom the user then sees is
        // `check_unconstrained_type_params`' "type parameter 'Rho' is unconstrained" —
        // accurate about the state, silent about the cause. Conservative rather than
        // wrong: the pass never claims a residual it could not bind.
        bind_row_tail(kb, subst, t, &labels, None);
    }
}

/// WI-270 — after seeding from `[bindings]`, expected, and arg
/// unification, every declared type-param must resolve to a non-Var
/// term. An unresolved Var means the caller can't recover the return
/// type's concrete shape; surface `UnconstrainedTypeParam` with the
/// param's name so the user can pin it via `op[T = …](…)`.
pub(super) fn check_unconstrained_type_params(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    op: &OperationInfoFull,
    fn_sym: Symbol,
    span: Option<Span>,
) -> Result<(), TypeError> {
    if op.type_params.is_empty() {
        return Ok(());
    }
    for (name, var) in &op.type_params {
        let var_term = type_param_var_term(kb, *var);
        // Carrier-agnostic resolve over [`TermView`]: `walk_view` returns a
        // `Value`, so a var bound to a `Value::Node` (a WRITTEN effect row
        // `E = {Modify[p]}` threaded into an op's `Eff` param by the same-sort
        // arg-unification, WI-393) is SURFACED, not lost. The term-only
        // `walk_type`/`walk_type_deep` cannot: their `TermId` return has nowhere
        // to put a non-`Term` carrier, so they keep the var and a row-bound
        // effect param was falsely flagged unconstrained. A genuinely unbound
        // param still resolves to a bare var.
        let resolved = walk_view(kb, subst, &TermIdView(var_term));
        if resolved_var(kb, &resolved).is_some() {
            return Err(TypeError::UnconstrainedTypeParam {
                span,
                op: fn_sym,
                type_param: *name,
            });
        }
    }
    Ok(())
}

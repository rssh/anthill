//! Reading provisions: carrier parameters and bindings, provisions of a spec, and
//! spec-operation suppliers per carrier.

use super::*;

/// WI-450 — the concrete SORT the spec's carrier param (its first type parameter)
/// is bound to in a provision's `spec_view` (`Combiner[T = Tag]` ⇒ `Tag`), or
/// `None` for a bare / carrier-less provision or a non-sort binding. Used by witness
/// coherence to tell a WITNESS (carrier ≠ provider sort) from a fact / self-provider
/// (carrier IS the provider).
///
/// WI-856 — "sort" here means SORT-LIKE: a SORT, or a FREE-STANDING entity, which is
/// its own type ([`KnowledgeBase::is_free_standing_entity`] — the same pair
/// [`check_bare_ref`] uses to decide that a bare name DENOTES A TYPE). So
/// `sort W provides PartialEq[T = binding]` over a namespace-level `entity binding(…)`
/// is a bona-fide witness. Reading only `SymbolKind::Sort` made this answer `None`,
/// and the caller then read the provision as a SELF-provider keyed on `W` — the
/// witness's `eq` was filed under the witness instead of the carrier and silently
/// never dispatched, with the load clean. Measured: 0 → 1 solution on the witness arm
/// of the WI-856 test pair.
///
/// Using that helper rather than a hand-rolled `kind == Entity && !constructor` also
/// makes this set EQUAL BY CONSTRUCTION to the carrier domain the eq index walks:
/// both bottom out in the entity-field-type registry
/// ([`crate::kb::load::eq_dispatch_carrier_domain`] via `eq_derive::composite_sorts`,
/// which is `entity_field_type_functors`). Accepting a carrier here that the index
/// cannot enumerate would recreate the very asymmetry WI-856 exists to close.
///
/// A sort-NESTED entity stays rejected — a variant is not a carrier in its own right
/// (its type is the parent sort), and admitting one would mint a SECOND carrier bucket
/// keying the very same constructor, where a rival `eq` could hide from the
/// per-carrier ambiguity check instead of colliding with it.
pub(super) fn provision_carrier_sort(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    spec_view: &Value,
) -> Option<Symbol> {
    provision_carrier_binding(kb, spec_sort, spec_view).map(|(_, base)| base)
}

/// WI-1076 — WHICH declared type parameter of `spec_sort` is its CARRIER: the first one
/// in declaration order that some declared operation TAKES AS A PARAMETER
/// (`Iterable.iterator(c: C)` ⇒ `C`). `None` when no operation takes any of them, which
/// is a spec with no carrier parameter at all — `Stream`, whose operations receive on
/// `Stream` itself and whose `T` appears only in return and callback types.
///
/// "TAKES" IS WIDER THAN "RECEIVES ON", AND IT IS THE RULE — decided, not shipped as an
/// approximation of something narrower (WI-1077 option (c), user 2026-08-11). Every
/// reader of this predicate should treat its answer as the language's, and the two
/// shapes where the wider reading shows (below) as intended behaviour rather than as a
/// fix someone owes. `docs/kernel-language.md` §5.1 and proposal 058 §3.6 say the same.
///
/// THE PREDICATE IS "RECEIVES ON A PARAMETER", NOT "RECEIVES ON ITSELF", and the
/// difference is a real program. [`spec_is_self_representing`] asks whether ANY
/// operation self-receives, which is the right question for its own callers and the
/// wrong one here: a spec may do BOTH — declare a carrier parameter its operations
/// receive on AND take itself in some other operation (`peek(c: C)` beside
/// `joinTwo(a: Holder, b: Holder)`). Gating on self-representation discarded such a
/// spec's explicit `C = Box` binding, filed its witness's dictionary under the witness
/// instead of the carrier, and refused a program that had loaded — measured on exactly
/// that fixture, which is why the question is asked of the PARAMETER.
///
/// It DOES weaken the positional assumption it replaced — a spec whose carrier parameter
/// is not written first (`sort S { sort Element = ?; sort C = ?; operation f(c: C) }`)
/// now answers `C`, where the old read answered `Element` — but only while no operation
/// takes the earlier parameter. Add `has(c: C, e: Element)` and it answers `Element`
/// again, MEASURED. That is the same gap as the paragraph below, reached from the
/// carrier-parameterized side.
///
/// WHERE THE WIDER READING SHOWS, and it is the rule rather than a defect (WI-1077).
/// "Takes a parameter of type `P`" does not separate a RECEIVER from an ACCEPTED
/// ARGUMENT, so a spec that receives on itself AND accepts its own element reads that
/// element as the carrier and files its provisions there. `Set.insert(s: Set, x: T)` and
/// `Map.put(m: Map, key: K, value: V)` are that shape. No stdlib provision of either
/// exists — `wi1077_accepts_vs_receives_test` supplies the fixture, against a `Feeder`
/// twin that differs ONLY in returning its element instead of taking one and therefore
/// files at the provider.
///
/// NARROWING IT IS NOT AVAILABLE, which is why the decision went the way it did. Eval
/// separates the two with [`provision_binds_param_to_carrier`], which is
/// provision-relative and cannot be asked here without circularity; asking
/// [`spec_is_self_representing`] instead refuses a program that loads (the paragraph
/// above); and a declaration that SAYS which parameter is the carrier — a marker, or a
/// `spec` keyword — is new surface that is not being added. Where the reuse is
/// ACCIDENTAL the repair is the declaration, as the next paragraph describes.
///
/// ONE INSTANCE OF IT WAS NOT A LIMIT BUT A BUG IN THE DECLARATION, and that is the
/// preferred repair wherever it applies. `LogicalStream.pure` read `pure(x: T) ->
/// LogicalStream`, reusing the SORT's parameter for a value it merely lifts. As
/// `pure[A](x: A) -> LogicalStream[A, {}]` the question stops being asked, and
/// `Relation provides LogicalStream` reads its provider. Prefer fixing such a
/// declaration over widening this predicate: it makes the illegal state unrepresentable
/// instead of inferring around it, and the bare return was independently losing the
/// argument's type.
///
/// IT WAS WRONG FROM THE FIRST DAY, not a victim of its vintage. An earlier draft of
/// this note blamed the age — `pure` was written 2026-02-23 and stdlib's first OPERATION
/// type parameter landed 2026-06-10 (WI-424) — but that is not why. A shared LOGICAL
/// VARIABLE says the same thing and needed nothing new: `pure(x: ?A) -> LogicalStream[?A,
/// {}]` type-checks today, and its neighbour `mplus(a: LogicalStream{T = ?A}, b: …)` was
/// written that way IN THE SAME COMMIT. Types are terms and they unify (§4.4), so
/// operation-level polymorphism was always expressible; `pure` simply did not use it.
///
/// THE FAILURE MODE IS THE SAFE ONE, and that is why this predicate was chosen over the
/// stricter [`spec_is_self_representing`], which closes `LogicalStream` and was
/// MEASURED to refuse a program that loads: a spec declaring BOTH a carrier parameter
/// and a self-receiving operation had its explicit `C = Box` binding discarded and the
/// load failed with a `requires Holder[…]` mismatch. Answering "carrier parameter" when
/// the truth is "self-representing" leaves a provision where it already was; answering
/// "self-representing" when the spec HAS a carrier parameter throws a written binding
/// away. Only one of those can break a working program.
///
/// THAT SAFETY ARGUMENT IS ABOUT THE CONSUMERS IT WAS WRITTEN FOR, and WI-20260829-XZMGC
/// added one it does not cover. `subtype_provider_view` uses this answer to decide which
/// composed binding to take OUT of a provider view and replace with the actual's own type
/// — where a wrong answer is not "a provision left where it was" but a WRONG VALUE
/// substituted for a correct one. MEASURED, found by /code-review: with `operation touch(c:
/// Spec, x: P)` this predicate answers `P`, the ACCEPTED ARGUMENT (which is the rule, not a
/// slip — see the paragraphs above), and a `Carrier[T = Int64]` reaching `Spec` through an
/// intermediate was refused at `Spec[P = Int64]` with its whole type compared against
/// `Int64`. That reader therefore does NOT rely on this answer alone: it also requires the
/// composed value to be the intermediate's own self-naming ([`composed_self_reference`]),
/// which a mis-identified element parameter's value is not. A NEW consumer owes the same
/// second gate — this predicate answers "which parameter an operation takes", and that is
/// not by itself "which parameter names the carrier".
///
/// Keyed and computed on the CANONICAL sort symbol: `operations_of_sort` re-filters on
/// raw symbol equality and answers empty for a twin copy, where the parameter list
/// beside it (`sort_type_params_as_pairs` → `type_param_syms_of`) canonicalizes — so an
/// uncanonicalized read would give one relation two answers depending on which spelling
/// a provision was written with. Memoized on `kb.spec_carrier_param_cache`, since the
/// walk builds an `OperationInfoFull` per declared operation.
pub(super) fn spec_carrier_param(kb: &KnowledgeBase, spec_sort: Symbol) -> Option<Symbol> {
    let canon = kb.canonical_sort_sym(spec_sort);
    if let Some(cached) = kb.spec_carrier_param_cache.borrow().get(&canon) {
        return *cached;
    }
    // Every type-param VarId any declared operation receives on, in one pass over the
    // operations — the dual of `self_receiver_param_index`, which matches a parameter
    // typed as the SORT where this matches one typed as a PARAMETER of it.
    let received: std::collections::HashSet<VarId> =
        crate::kb::op_requirements::operations_of_sort(kb, canon)
            .iter()
            .filter_map(|&op| lookup_operation_info_full(kb, op))
            .flat_map(|info| {
                info.params
                    .iter()
                    .filter_map(|(_, pty)| declared_type_param_vid(kb, pty))
                    .collect::<Vec<_>>()
            })
            .collect();
    let answer = sort_type_params_as_pairs(kb, canon)
        .iter()
        .map(|(s, _)| *s)
        .find(|&p| type_param_global_var(kb, p).is_some_and(|v| received.contains(&v)));
    kb.spec_carrier_param_cache
        .borrow_mut()
        .insert(canon, answer);
    answer
}

/// WI-1102 — WHICH type parameter of `spec` the carrier goes in, on a two-rung ladder.
/// ONE owner, because two readers ask it and a disagreement between them is a wrong
/// sentence rather than a missing one (see [`carrier_has_provision_row`], whose verdict
/// picks which of `UnprovidedProvision`'s two sentences is rendered).
///
/// Rung 1 is [`spec_carrier_param`] — the param some declared OPERATION receives on.
/// Rung 2 is a SOLE type parameter, which is that carrier by construction: there is no
/// other slot for a binding to mean. Rung 2 is gated on the spec not being
/// SELF-REPRESENTING (WI-614's [`spec_is_self_representing`], the established reader for
/// exactly that shape) — the OTHER reason rung 1 answers `None`, and the one where the
/// sole parameter is the ELEMENT and not the carrier: reading it as the carrier is
/// WI-1076's measured defect, seven stdlib provisions filed at the type VARIABLE `T`.
/// The two `None`s must be told apart here because only one of them licenses rung 2.
/// MEASURED over stdlib + host bindings: fourteen sorts reach rung 2, and the
/// sole parameter is the carrier in every one — `Eq`, `NonEq`, `Monad`, `DelayMonad`,
/// `BoundedLattice`, `Modify`, `Effect`, `EffectsRuntime`, `Modifiable`, `Option`,
/// `StoredRef`, `Monad.M`, and the two `realization.runtime` dictionaries. Every
/// self-representing stdlib spec (`Stream`, `FiniteStream`, `LogicalStream`) carries a
/// second parameter and so never reached rung 2 anyway; the gate is what keeps a
/// USER-written single-parameter one — `sort C { sort T = ?; operation head(c: C) -> T }`
/// — from being read as though `T` carried the provision.
///
/// A multi-parameter spec with no receiving operation falls through to `None` and is NOT
/// refused: the diagnostic's whole content is "this sort lacks this provision" and there
/// is no non-arbitrary way to say which sort that is.
pub(super) fn spec_carrier_param_or_sole(kb: &KnowledgeBase, spec_sort: Symbol) -> Option<Symbol> {
    if let Some(p) = spec_carrier_param(kb, spec_sort) {
        return Some(p);
    }
    // Canonical on both reads, as `spec_carrier_param` is internally: an ALIAS symbol of
    // the spec owns no operations and no type params, so an uncanonical ask would find
    // neither a self-receiver nor a sole parameter and answer rung 2 for every spec.
    let canon = kb.canonical_sort_sym(spec_sort);
    if spec_is_self_representing(kb, canon) {
        return None;
    }
    let tps = sort_type_params_as_pairs(kb, canon);
    (tps.len() == 1).then(|| tps[0].0)
}

/// [`provision_carrier_sort`] before it throws the WRITTEN term away: the value bound to
/// the spec's carrier param AND the sort-like base that value names, as one answer.
///
/// One function so the filter — the base must be a SORT or a free-standing entity — is
/// applied to the view and to the symbol together. A caller that took the raw binding on
/// its own would accept `Spec[T = OwnParam]`, whose binding names a TYPE PARAM and whose
/// dispatch carrier is therefore the provider, not the param (WI-859 folds exactly that
/// shape into the self-provider kind).
///
/// WI-860 — the BINDING is read over `TermView` rather than through
/// [`unwrap_spec_view_value`], which drops any binding it cannot read as a `TermId`:
/// right for its own callers, and wrong here for the reason
/// [`witness_dispatch_carrier_value`] records. Only the binding — the view's SortView
/// discriminant and the bound value's base still go through the shared owners
/// ([`view_is_sort_view`], [`spec_view_base`]), which read the same on both carriers.
///
/// WI-1076 — THE CARRIER PARAMETER IS THE ONE THE OPERATIONS RECEIVE ON, asked through
/// [`spec_carrier_param`]; `None` when there is none, which is a SELF-REPRESENTING spec
/// (`Stream.splitFirst(s: Stream)`) whose first parameter is the ELEMENT type. Taking
/// the first parameter unconditionally filed seven stdlib provisions —
/// `List`/`FiniteStream`/`MappedStream`/`FilteredStream`/`LogicalStream` `provides
/// Stream[T]`, `List provides FiniteStream[T]`, `Relation provides LogicalStream[T]` —
/// at the type VARIABLE `T`, classifying each carrier as a WITNESS for it, so
/// `self_provides(List, Stream)` was false and 058 §3.6 inferred no default row from any
/// of them. Loading clean throughout, which is why it needed its own ticket.
///
/// `None` is the right answer rather than "the provider": this function reports the
/// CARRIER-PARAM BINDING, of which a self-representing spec has none. A witness for one
/// is not merely absent from the corpus but UNSAYABLE — dispatch is directed by the
/// receiver value's own sort, there being no parameter position that could name a
/// carrier, so a sort claiming such a spec is claiming to BE one.
///
/// WHAT EACH CALLER MAKES OF `None`, audited rather than assumed: the `dispatch_carrier`
/// builtin mints the PROVIDER, [`witness_dispatch_carrier_value`] declines the witness
/// kind (so 058 §3.6 infers the default row), and the dot-call witness match declines.
/// [`requires_edge_is_carrier_preserving`] is the one that reads it differently — as
/// "not carrier-preserving" — and that is correct for the same reason: an edge
/// `requires SelfRepSpec[…]` has no carrier parameter to bind the receiver's carrier to,
/// which is exactly the constraint-style case that function rejects. It already applies
/// the same rule from the other side, refusing outright when the RECEIVER is
/// self-representing.
pub(super) fn provision_carrier_binding(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    spec_view: &Value,
) -> Option<(Value, Symbol)> {
    // Bindings live on the `SortView(base, …named)` wrapper alone, asked through the one
    // owner of that discriminant: a bare spec reference (`provides Store`) carries named
    // args nowhere, and reading them off some other functor would invent a carrier.
    // FIRST because it is the cheap gate: this is read per provision on the dot-call
    // receiver probe, and the carrier-param question below walks the spec's operations.
    if !view_is_sort_view(kb, spec_view) {
        return None;
    }
    let carrier_param = spec_carrier_param(kb, spec_sort)?;
    provision_binding_at_param(kb, carrier_param, spec_view)
}

/// [`provision_carrier_binding`] once the carrier PARAMETER is decided — the half that
/// reads a binding off a spec view and filters it to a sort-like base.
///
/// Split out for WI-1102, which needs the same read at a param chosen on a different
/// ladder ([`spec_carrier_param_or_sole`]). The split is deliberately at the param and
/// not at the ladder: pushing the fallback INTO `provision_carrier_binding` would move
/// it under every one of that function's readers — the dot-call receiver probe, 058
/// §3.6's default rows, the `dispatch_carrier` builtin — and WI-1076 measured what
/// happens when those read a first parameter that is not a carrier.
pub(super) fn provision_binding_at_param(
    kb: &KnowledgeBase,
    carrier_param: Symbol,
    spec_view: &Value,
) -> Option<(Value, Symbol)> {
    let carrier_short = short_name_of(kb.local_name_of(carrier_param));
    // The param's OWN symbol first, short name only as the fallback — `goal_binding_value`'s
    // two-rung ladder, and here it is also what keeps the common case allocation-free:
    // `named_keys` collects a `Vec`, `named_arg` does not.
    let val = match spec_view.named_arg(kb, carrier_param) {
        Some(item) => item.to_value(),
        None => {
            let key = spec_view
                .named_keys(kb)
                .into_iter()
                .find(|k| short_name_of(kb.local_name_of(*k)) == carrier_short)?;
            spec_view.named_arg(kb, key)?.to_value()
        }
    };
    spec_view_base(kb, &val)
        .filter(|&s| {
            matches!(kb.kind_of(s), Some(crate::intern::SymbolKind::Sort))
                || kb.is_free_standing_entity(s)
        })
        .map(|s| (val, s))
}

/// WI-20260913-KXNEX — A WRITTEN `provides` CLAUSE MUST NAME A CARRIER. For each
/// clause the loader recorded, if the spec it names HAS a carrier parameter
/// ([`spec_carrier_param`]) and the clause binds no value at that parameter, refuse.
///
/// WHAT IT IS FOR: value-directed dispatch reads a provision's carrier off its
/// BINDINGS, so a clause that binds everything EXCEPT the carrier parameter names no
/// carrier at all — and until this check that loaded clean and died at the first call.
/// MEASURED (WI-20260830-7MK73): `sort LiveLlm { operation complete(self: LiveLlm, …);
/// provides Llm[E = {External}] }` loaded, and a `summarize(llm, …)` whose body is
/// `llm.complete(p)` failed `OperationBodyMissing { name: "guardians.Llm.complete" }`
/// against a provider that implements `complete`. Writing `C = LiveLlm` fixed it with
/// no other change, at four sites.
///
/// WHY IT WAS SILENT — TWO READERS, ONE `None`. The typer's provider-keyed reading
/// accepted the clause (`LiveLlm`'s `E = {External}` reached callers' rows throughout);
/// dispatch's carrier-keyed reading needs the carrier parameter bound and found
/// nothing. [`provision_carrier_binding`] answers `None` for both, and its own doc
/// audits the disagreement: the `dispatch_carrier` builtin mints the PROVIDER while the
/// witness reader and the dot-call match DECLINE. This check does not reconcile those
/// readings — it removes the shape that makes them differ for a clause an author wrote.
///
/// IT ASKS [`spec_carrier_param`] AND NOT [`spec_carrier_param_or_sole`], and that is
/// load-bearing rather than incidental. The defect is exactly "dispatch reads `None`
/// where the author meant a carrier", and dispatch reads through the FORMER. Asking the
/// two-rung ladder would refuse clauses over specs whose sole parameter dispatch never
/// treats as the carrier — a diagnostic about a reading nothing performs.
///
/// WHAT STAYS LEGAL, each for its own reason:
///   * a spec with NO carrier parameter (§5.1's `sort List provides Stream[T, {}]`) —
///     `spec_carrier_param` answers `None`, there is no parameter to demand, and the
///     provision records its provider. This covers the self-representing specs
///     (`Stream`, `FiniteStream`, `LogicalStream`) that WI-1076 is about.
///   * a WITNESS (`sort WrapperNonEq { provides NonEq[T = Wrapper] }`) — it binds the
///     carrier parameter explicitly, which is the very thing demanded here.
///   * a provision binding the carrier to one of the PROVIDER'S OWN TYPE PARAMETERS
///     (`sort List[T] { provides Ord[T = List[T = T]] }`). Hence "bound at all" and not
///     [`provision_binding_at_param`]'s sort-like base: that filter answers `None` for a
///     type-param binding too (WI-859 folds the shape into the self-provider kind), and
///     reusing it here would refuse the stdlib.
///   * DERIVED and composed rows — `eq_derive::run`'s, `derive_forwarded_provisions`' —
///     which are not in this registry at all, because it holds what authors wrote.
///
/// Runs over the loader's drained registry rather than the provision relation, and
/// [`crate::kb::WrittenProvidesClause`] says why.
pub(crate) fn check_provision_names_carrier(
    kb: &KnowledgeBase,
    clauses: &[crate::kb::WrittenProvidesClause],
) -> Vec<crate::kb::load::LoadError> {
    let mut errors = Vec::new();
    for clause in clauses {
        let Some(carrier_param) = spec_carrier_param(kb, clause.spec) else {
            continue;
        };
        if written_spec_binds_param(kb, clause.spec, &clause.spec_view, carrier_param) {
            continue;
        }
        errors.push(crate::kb::load::LoadError::ProvisionNamesNoCarrier {
            spec: kb.qualified_name_of(clause.spec).to_string(),
            carrier_param: short_name_of(kb.local_name_of(carrier_param)).to_string(),
            provider: kb.qualified_name_of(clause.provider).to_string(),
            site: crate::kb::load::render_decl_site(kb, clause.span),
        });
    }
    errors
}

/// WI-20260913-KXNEX — does a spec reference AS WRITTEN bind `param` to ANYTHING?
///
/// "To anything" is the question the carrier check needs, and no established reader
/// answers it: [`provision_binding_at_param`] additionally filters the bound value to a
/// sort-like base, which is right for "which sort is the carrier" and wrong for "did the
/// author say" — a binding naming the provider's own type parameter fails that filter
/// while being perfectly written down.
///
/// BOTH SPELLINGS OF A BINDING, because a clause may use either. Named args are matched
/// on the parameter's own symbol and then on its short name, [`provision_binding_at_param`]'s
/// two-rung ladder, for the same reason: the two sides reach here through different
/// decoders and the short name is what both spell alike. POSITIONAL args are mapped onto
/// the declared parameters not already bound by name — the mapping `check_provider_requires`
/// performs over the same shape, and without it `provides VectorSpace[Vec3, Float]` would
/// read as binding nothing and be refused for writing its carrier first. MEASURED both
/// ways: with `C` declared first `provides Spec[Impl]` loads, and with the spec's OTHER
/// parameter declared first the same clause is refused, naming `C`.
///
/// THE TWO BRANCHES ASK SLIGHTLY DIFFERENT QUESTIONS, which is deliberate and is the
/// direction that cannot break a working program. The positional branch is restricted to
/// DECLARED type parameters by construction (it walks them); the named branch asks only
/// whether a binding carries that KEY, and does not additionally verify through
/// [`is_type_param_binding`] that the key names a type parameter of this spec. Gating it
/// was weighed and rejected: that helper resolves `<spec qn>.<name>`, so a provision
/// naming its spec through an ALIAS could fail the lookup and have a written binding
/// thrown away — a FALSE REFUSAL of a program that loads. What the looser reading can
/// cost is the opposite and smaller: a non-type-param binding whose key happens to share
/// the carrier parameter's short name would be read as the carrier, and the diagnostic
/// would be missed rather than wrongly raised. That shape needs one spec to own two
/// declarations at one qualified name, which the symbol table does not admit (WI-997).
fn written_spec_binds_param(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    spec_view: &Value,
    param: Symbol,
) -> bool {
    let want = short_name_of(kb.local_name_of(param));
    let named: Vec<Symbol> = spec_view.named_keys(kb);
    if named
        .iter()
        .any(|k| *k == param || short_name_of(kb.local_name_of(*k)) == want)
    {
        return true;
    }
    let ViewHead::Functor { pos_arity, .. } = spec_view.head(kb) else {
        return false;
    };
    // A `SortView` wrapper carries the spec base in `pos_args[0]`; a bare parameterized
    // term does not. The same skip `check_provider_requires` makes, on the same
    // discriminant ([`view_is_sort_view`], the one owner of it).
    let skip = usize::from(view_is_sort_view(kb, spec_view));
    let positionals = pos_arity.saturating_sub(skip);
    if positionals == 0 {
        return false;
    }
    // Declaration order, minus whatever a named binding already pinned — so a mixed
    // `Spec[V = Vec3, Float]` assigns its positional to the next FREE parameter, which is
    // the rule the requires-coverage decoder applies to this same shape.
    sort_type_params_as_pairs(kb, kb.canonical_sort_sym(spec_sort))
        .iter()
        .map(|(p, _)| short_name_of(kb.local_name_of(*p)))
        .filter(|n| {
            !named
                .iter()
                .any(|k| short_name_of(kb.local_name_of(*k)) == *n)
        })
        .take(positionals)
        .any(|n| n == want)
}

/// WI-431: the OPERATION symbol an instance fact binds for `op_short` among a
/// provision's `SortView` `bindings` (`pure = optionPure` ⇒ `optionPure`), or
/// `None` if `op_short` is not bound to an operation. The op-valued binding IS
/// the dictionary entry that backs the spec op — read at the fact-coverage check
/// (loader) and at spec-op dispatch (eval) through this one accessor. The bound
/// value's base symbol is read via `provides_spec_base_sym` (the same
/// op-discriminator [`sort_view_substitution`](crate::kb::load) uses, which also
/// unwraps a `SortView`-wrapped parameterized value); a type-valued binding
/// (`F = Option`, a `Sort`) yields `None`, so a plain type-only provision
/// (`provides Stream[T = X]`) never matches.
fn instance_fact_op_in_bindings(
    kb: &KnowledgeBase,
    bindings: &[(Symbol, TermId)],
    op_short: &str,
) -> Option<Symbol> {
    bindings.iter().find_map(|(key, value)| {
        if short_name_of(kb.qualified_name_of(*key)) != op_short {
            return None;
        }
        binding_op_symbol(kb, *value)
    })
}

/// WI-431: the OPERATION symbol an instance-fact binding `value` denotes
/// (`pure = optionPure` ⇒ `optionPure`), or `None` when the binding is not
/// op-valued (a type binding `F = Option`, a `Sort`). The single op-discriminator
/// shared by fact-coverage (rule 1), eval dispatch (increment 2), and coherence
/// (rule 2): a binding backs a spec op iff its base symbol — read via
/// `provides_spec_base_sym`, which also unwraps a parameterized `SortView` — is an
/// `Operation`. Folding all three callers through this one predicate keeps them
/// from disagreeing about what an op-valued binding is.
pub(crate) fn binding_op_symbol(kb: &KnowledgeBase, value: TermId) -> Option<Symbol> {
    crate::kb::load::provides_spec_base_sym(kb, value)
        .filter(|s| matches!(kb.kind_of(*s), Some(crate::intern::SymbolKind::Operation)))
}

/// WI-431 coherence (rule 2): true iff the provision's spec view binds AT LEAST
/// ONE operation — i.e. it is an INSTANCE FACT supplying a dictionary, not a
/// type-only provision (`provides Stream[T = X]`). Only instance facts
/// participate in dictionary coherence: a type-only provision contributes no
/// dispatch target, so it can never be the ambiguous one (and an existing
/// `provides` / type-only `fact` is never over-rejected).
pub(super) fn provision_binds_any_op(kb: &KnowledgeBase, spec_view: TermId) -> bool {
    match unwrap_spec_view(kb, spec_view) {
        Some((_, bindings)) => bindings
            .iter()
            .any(|(_, value)| binding_op_symbol(kb, *value).is_some()),
        None => false,
    }
}

/// WI-431 loader coverage: true iff the provision's spec view binds `op_short`
/// to an operation — the instance-fact backing for that spec op.
pub(super) fn op_bound_in_instance_fact(
    kb: &KnowledgeBase,
    spec_view: TermId,
    op_short: &str,
) -> bool {
    match unwrap_spec_view(kb, spec_view) {
        Some((_, bindings)) => instance_fact_op_in_bindings(kb, &bindings, op_short).is_some(),
        None => false,
    }
}

/// WI-431 dispatch: the operation backing spec op `op_short` for `carrier`
/// through an instance fact `SortProvidesInfo(carrier, Spec[…, op_short = op])`.
/// The dispatch fallback when `carrier` owns no `op_short` of its own — a
/// retroactive instance binds the op in the fact instead of on the carrier.
///
/// STILL SINGLE-ROUTE after WI-842's §4.9 sweep, and deliberately so at both of its
/// remaining callers — the value-directed chain that used to head them left for
/// [`spec_op_suppliers_for_carrier`]:
///   * [`resolve_op_target`] resolves an op WITHIN a dictionary's own functor — a
///     provider already selected by `resolve_inner` → `pick_most_specific`, the one
///     consumer that CAN raise a use-site ambiguity. It selects an op, not a provider,
///     so §4.9's rule does not reach it;
///   * `check_apply`'s higher-kinded arm reads only the FACT route for a carrier it
///     has just discharged. Two op-binding facts for one carrier are
///     [`crate::kb::load::LoadError::AmbiguousInstanceFact`] at load and STAY so under
///     phase 3b, whose coexistence is gated on every candidate being NAMEABLE (§4.3)
///     and an instance fact has no name.
pub(crate) fn instance_fact_op_binding(
    kb: &KnowledgeBase,
    carrier: Symbol,
    spec_sort: Symbol,
    op_short: &str,
) -> Option<Symbol> {
    let bindings = provider_spec_view_bindings(kb, carrier, spec_sort)?;
    instance_fact_op_in_bindings(kb, &bindings, op_short)
}

/// WI-1098 — every CARRIER any provision of `spec_sort` names, canonical.
///
/// NOT [`sort_provides`], and the difference is the whole reason this exists (WI-1069:
/// a provision records a PROVIDER and a CARRIER, and "same provision" is not "same
/// statement"). `sort_provides` asks "does THIS sort's own declaration provide", keyed
/// on `sort_ref`; a WITNESS names its carrier only in the spec's `T` binding
/// (`sort WrapperNonEq { provides NonEq[T = Wrapper] }` files under `WrapperNonEq`), so
/// the carrier answers `false` to that question while being fully spoken for. This
/// answers the carrier's question instead, through [`witness_dispatch_carrier`] — the
/// same owner the eq-dispatch index reads, so the two cannot disagree about which sort
/// a provision is ABOUT.
///
/// The one caller is `eq_derive`'s Total classification, which must not derive a claim
/// over a carrier somebody has already made one about. MEASURED before the guard: a
/// `provides NonEq[T = Wrapper]` witness left `Wrapper` seeded Total, so the derivation
/// asserted `provides Eq[Wrapper]` — reflexivity of an equality the author had
/// explicitly witnessed as non-reflexive — and `check_eq_noneq_exclusive` could not see
/// the contradiction either, because it groups by `sort_ref` too.
pub(crate) fn provision_carriers_of_spec(kb: &KnowledgeBase, spec_sort: Symbol) -> Vec<Symbol> {
    provisions_of_spec(kb, spec_sort)
        .map(|(provider, spec_t, _)| {
            // `None` = the provision's carrier IS the provider (a self-provision, an
            // instance fact, or a bare one naming no other sort) — that function's own
            // documented contract.
            witness_dispatch_carrier(kb, spec_sort, provider, spec_t).unwrap_or(provider)
        })
        .map(|c| kb.canonical_sort_sym(c))
        .collect()
}

/// Every `SortProvidesInfo` provision OF `spec_sort`, decoded once into
/// `(provider sort, the provision's `SortView` term, its type-param bindings)`.
///
/// The shared substrate of the multi-candidate walks
/// ([`collect_spec_op_suppliers_by_carrier`], [`spec_op_suppliers_for_carrier`]),
/// which differ only in whether they bucket every carrier or filter to one. It used
/// to be spelled twice — eleven identical lines — which is the shape that produced
/// WI-838's cross-kind blind spot in the first place (two copies of one criterion,
/// kept in step by hand).
///
/// Reads the WI-660 `by_spec_base` bucket via [`provides_rids_by_spec`] rather than
/// every provision fact, and keeps the per-fact canonical re-filter that bucket's
/// contract requires (its no-index fallback returns EVERY provides fact, which is
/// what both readers see today — `build_eq_dispatch_index` runs before
/// `build_provides_index`, and `eq_derive::run`'s caller nulls the index first).
pub(super) fn provisions_of_spec(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
) -> impl Iterator<Item = (Symbol, TermId, SmallVec<[(Symbol, TermId); 2]>)> + '_ {
    let spec_canon = kb.canonical_sort_sym(spec_sort);
    provisions_from_rids(kb, spec_canon, provides_rids_by_spec(kb, spec_canon))
}

/// WI-20260829-K0E8T — the DECODE half of [`provisions_of_spec`], over rids the caller
/// has already fetched with [`provides_rids_by_spec`].
///
/// Split out for the one caller that must SEE the bucket before it decides to walk it:
/// [`witness_provides_admissibly`]'s gate, which is entered on the failure path of every
/// bare↔bare compatibility check and whose bucket is empty at 1263 of 1267 stdlib-load
/// entries. Going through [`provisions_of_spec`] would make it canonicalize the spec a
/// second time (an FQN string hash — that function's own first statement) and
/// canonicalize the ACTUAL before it knows there is anything to compare it against. One
/// decoder still, not two: this IS the body, and `provisions_of_spec` is now the
/// canonicalize-and-fetch wrapper around it.
pub(super) fn provisions_from_rids(
    kb: &KnowledgeBase,
    spec_canon: Symbol,
    rids: Vec<crate::kb::RuleId>,
) -> impl Iterator<Item = (Symbol, TermId, SmallVec<[(Symbol, TermId); 2]>)> + '_ {
    rids.into_iter().filter_map(move |rid| {
        if !kb.is_fact(rid) {
            return None;
        }
        // A value-fact `SortProvidesInfo` (denoted-bearing spec) is skipped:
        // occurrence-based provides lookup is gated effect-expressions-as-types
        // work, and `fact_head_named_args` is `None` rather than panicking on it.
        let named = kb.fact_head_named_args(rid)?;
        let sr = get_named_arg(kb, &named, "sort_ref")?;
        let provider = crate::kb::load::sort_ref_functor(kb, sr)?;
        let spec_t = get_named_arg(kb, &named, "spec")?;
        let (base, bindings) = unwrap_spec_view(kb, spec_t)?;
        (kb.canonical_sort_sym(base) == spec_canon).then_some((provider, spec_t, bindings))
    })
}

/// WI-837 — how a spec op's impl reaches a carrier. The three routes are written in
/// three different syntaxes, so a diagnostic that lists candidates must say which is
/// which for the author to know what to delete — and only the witness has a name to
/// quote (an instance fact has none, proposal 058 §4.3, which is why
/// [`crate::kb::load::LoadError::MixedProviderKinds`] is its own variant).
#[derive(Clone, Copy)]
pub(crate) enum SupplyRoute {
    /// The carrier's OWN member (`Set.eq`) — the genuine override, WI-616.
    Own,
    /// A retroactive INSTANCE FACT's op-valued binding (`fact PartialEq[T = C,
    /// eq = cEq]` ⇒ `cEq`), WI-431 / WI-625 gap 2.
    Fact,
    /// A WITNESS SORT's own member (`sort CEq provides PartialEq[T = C]` with
    /// `CEq.eq`), WI-450.
    Witness(Symbol),
}

impl SupplyRoute {
    /// WI-1027 — could `resolve_inner`'s provision arbitration have WEIGHED this supplier
    /// against a rival? The predicate [`arbitrate_unarbitrated_supplier_tie`] turns into a
    /// verdict, kept here and EXHAUSTIVE so a fourth route cannot inherit an answer by
    /// silence — the whole cost of getting it wrong is refusing correct programs at load,
    /// which is what the six-fixture measurement in that function's doc discovered.
    ///
    /// The mechanism, per route, because it is a fact about the DISPATCH PATH and not
    /// about the syntax each route is written in:
    ///
    ///   * [`Self::Witness`] — TRUE. The provision is a candidate, and
    ///     `resolve_at_goal`'s `sort_ops_lookup(impl_sort, op_short)` projects it to the
    ///     witness's own member, which IS this supplier. Nothing is lost, so tier 1,
    ///     tier 2 and `DispatchOutcome::Ambiguous` all see it.
    ///   * [`Self::Own`] — FALSE. It contributes no provision at all
    ///     (`build_sort_ops_table` pass 1 records the carrier's member whatever the
    ///     provisions say), so it is never a distinguishable candidate. It can still WIN,
    ///     by being what the lookup returns when the chosen provision is carrier-keyed —
    ///     winning without ever having been weighed is exactly the defect.
    ///   * [`Self::Fact`] — FALSE, and for a different reason worth keeping apart: the
    ///     provision IS weighed, but `collect_provides_candidates` drops op-valued
    ///     bindings and the `sort_ops_lookup` projection returns a same-named member of
    ///     the carrier in preference to the binding. Lossy projection, not absence. If
    ///     that projection is ever taught to consult the binding, this arm becomes TRUE
    ///     and must be changed with it.
    pub(crate) fn weighed_by_provision_arbitration(&self) -> bool {
        match self {
            SupplyRoute::Witness(_) => true,
            SupplyRoute::Own | SupplyRoute::Fact => false,
        }
    }
}

/// WI-837 — ONE supplier of a spec op's impl for a carrier.
#[derive(Clone, Copy)]
pub(crate) struct SpecOpSupplier {
    /// The operation to dispatch to.
    pub(crate) target: Symbol,
    pub(crate) route: SupplyRoute,
}

impl SpecOpSupplier {
    /// WI-861 — the PROVIDER this supplier belongs to, which is what 058 §3.6's default
    /// rows name. The three routes map two ways and the split is the route's own:
    ///
    ///   * [`SupplyRoute::Witness`] carries the witness sort — a different sort from the
    ///     carrier by the definition of a witness ([`witness_dispatch_carrier`]).
    ///   * [`SupplyRoute::Own`] and [`SupplyRoute::Fact`] both belong to the CARRIER: an
    ///     own member is the carrier's own text, and a carrier-keyed instance fact's
    ///     `sort_ref` IS the carrier (`provision_supplier`'s `None` arm keys it there).
    ///
    /// THE TWO COLLAPSING IS LOAD-BEARING, not an approximation. A default names a
    /// provider, and a carrier's own member beside its own instance fact's binding is one
    /// provider saying two things — so both map to one symbol,
    /// [`crate::kb::defaults::default_among`] sees two hits, and the refusal stands. That is
    /// WI-1027's fixture 2 and it must not be broken by a rung that arbitrates between a
    /// provider and itself.
    pub(crate) fn provider(&self, carrier: Symbol) -> Symbol {
        match self.route {
            SupplyRoute::Own | SupplyRoute::Fact => carrier,
            SupplyRoute::Witness(w) => w,
        }
    }

    /// Render this candidate for an ambiguity diagnostic, naming its ROUTE.
    /// `op_short` is the spec op's short name, so the fact leg can echo the binding
    /// the author actually wrote (`eq = cEq`).
    pub(crate) fn render(&self, kb: &KnowledgeBase, op_short: &str) -> String {
        let target = kb.qualified_name_of(self.target);
        match self.route {
            SupplyRoute::Own => format!("the carrier's own member '{}'", target),
            SupplyRoute::Fact => {
                format!("an instance fact binding `{} = {}`", op_short, target)
            }
            // "supplying", not "its own member": a witness may name the impl either
            // as its own member or as an op-valued binding in the provision itself.
            SupplyRoute::Witness(w) => format!(
                "witness sort '{}' (supplying '{}')",
                kb.qualified_name_of(w),
                target
            ),
        }
    }
}

/// WI-837 — bucket EVERY provision of `spec_sort` that supplies spec op `spec_op`
/// (short name `op_short_sym`), of EITHER provider kind, under its CANONICAL DISPATCH
/// CARRIER. Appends into a caller-owned map so a caller sweeping several specs
/// (`PartialEq` then `Eq`) gets ONE dedup-by-target rule across the whole sweep:
/// two provisions naming one operation are one dictionary, not a conflict.
///
/// Keyed by dispatch carrier rather than answering one carrier at a time because a
/// provision's supplier is a function of the PROVISION — the carrier is what the
/// provision NAMES, not an input to reading it. Asking per carrier re-walks every
/// provision per sort, which MEASURED as this ticket's entire first-cut cost.
///
/// The multi-candidate dual of the SELECTING reader [`instance_fact_op_binding`]
/// (carrier-keyed, first fact wins). Proposal 058 §4.9's hardening rule is that a
/// read which SELECTS goes loud on the second candidate, and that one cannot: it
/// stops at its first hit and never sees the witness kind at all. Consumer: the
/// semantic-eq dispatch index ([`crate::kb::load::EqDispatchIndex`]) — the one reader
/// with no later site to complain from, since equality dispatches from unification
/// where no instance can be selected — so it consumes this and refuses at LOAD.
/// WI-842's per-call reader [`spec_op_suppliers_for_carrier`] shares the
/// classification but not the bucketing, and refuses at the READ.
///
/// The witness leg reads the provider's own member through [`carrier_own_op`], NOT
/// the deleted `witness_op_for_carrier`'s bare `sort_ops_lookup`: pass 2 of the sort-ops build
/// records the SPEC op itself under the short name for every provision that does not
/// override it, so a witness which merely INHERITS a defaulted `eq` would otherwise
/// report `PartialEq.eq` as its impl — and keying the eq index to the `SemEq` builtin
/// is an unbounded regress, not a dispatch. Filtering it agrees with the value-directed
/// route rather than diverging from it: a witness with no own member leaves the index
/// unkeyed, so `eq` answers structurally, exactly as running the inherited default does.
pub(crate) fn collect_spec_op_suppliers_by_carrier(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    spec_op: Symbol,
    op_short_sym: Symbol,
    out: &mut std::collections::HashMap<Symbol, SmallVec<[SpecOpSupplier; 2]>>,
) {
    for (provider, spec_t, bindings) in provisions_of_spec(kb, spec_sort) {
        let Some((carrier_canon, supplier)) = provision_supplier(
            kb,
            spec_sort,
            spec_op,
            op_short_sym,
            provider,
            spec_t,
            &bindings,
        ) else {
            continue;
        };
        push_supplier_deduped(kb, out.entry(carrier_canon).or_default(), supplier);
    }
}

/// WI-837 — how ONE provision supplies spec op `spec_op`, and to WHICH canonical
/// dispatch carrier. `None` when that provision supplies no impl of the op.
///
/// The ONE OWNER of the per-provision classification, read by both multi-candidate
/// walks: [`collect_spec_op_suppliers_by_carrier`] (all carriers at once, for the
/// load-time eq index) and [`spec_op_suppliers_for_carrier`] (one carrier, for the
/// per-call value-directed dispatch). Extracted at WI-842 rather than copied: the
/// two walks answering "who supplies this" differently is the shape that produced
/// WI-838's cross-kind blind spot, and the criterion has three delicate legs.
pub(super) fn provision_supplier(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    spec_op: Symbol,
    op_short_sym: Symbol,
    provider: Symbol,
    spec_t: TermId,
    bindings: &[(Symbol, TermId)],
) -> Option<(Symbol, SpecOpSupplier)> {
    let op_short = kb.local_name_of(op_short_sym);
    // KIND 2 — WITNESS SORT (WI-450): the dispatch carrier is what the provision
    // binds to the spec's carrier param, not the provider. `witness_dispatch_carrier`
    // is the ONE owner of what counts as a witness, shared with the load-time
    // coherence grouping so they cannot disagree; it returns `None` for a provider
    // that IS its own carrier, which is exactly KIND 1's case.
    //
    // KIND 1 — carrier-keyed INSTANCE FACT (WI-431): the dispatch carrier is the
    // provision's own `sort_ref`. The loader DERIVES a namespace-level
    // `fact Spec[T = Carrier, …]`'s `sort_ref` from the carrier binding, so this
    // covers both that shape and a carrier's own `provides Spec[…, eq = op]` block.
    match witness_dispatch_carrier(kb, spec_sort, provider, spec_t) {
        // A WITNESS may name the impl EITHER WAY, so both legs are read: usually
        // as its own MEMBER (`sort W provides Spec[T = C]` with `W.op`), but
        // `sort W provides Spec[T = C, op = f]` also loads today and BINDS it.
        // Reading only the member leg dropped that provision on a silent
        // `continue` — its written `op = f` never keyed the index and equality
        // answered structurally with no diagnostic from anywhere.
        Some(c) => carrier_own_op(kb, provider, spec_op, op_short_sym)
            .or_else(|| instance_fact_op_in_bindings(kb, bindings, op_short))
            .map(|target| {
                (
                    c,
                    SpecOpSupplier {
                        target,
                        route: SupplyRoute::Witness(provider),
                    },
                )
            }),
        // A carrier-keyed provision supplies only what it BINDS. Its
        // `carrier_own_op` is the CARRIER's own member — route 1's business, and
        // attributing it to the provision here would let a `provides Spec[T = C]`
        // block shadow a sibling `fact Spec[T = C, op = f]`'s binding, hiding the
        // very second candidate this walk exists to surface.
        None => instance_fact_op_in_bindings(kb, bindings, op_short).map(|target| {
            (
                kb.canonical_sort_sym(provider),
                SpecOpSupplier {
                    target,
                    route: SupplyRoute::Fact,
                },
            )
        }),
    }
}

/// WI-837 — append `cand` unless the bucket already holds its operation. Dedup is by
/// CANONICAL target: one qualified name can be interned under several Symbols (the
/// reason `canonical_sym` exists, and why the eq index keys entries under both
/// spellings), so a raw compare would let ONE operation reached through two interned
/// copies read as two candidates — refusing a correct program. Two provisions naming
/// one operation are one dictionary, not a conflict.
pub(crate) fn push_supplier_deduped(
    kb: &KnowledgeBase,
    bucket: &mut SmallVec<[SpecOpSupplier; 2]>,
    cand: SpecOpSupplier,
) {
    let target_canon = kb.canonical_sym(cand.target);
    if !bucket
        .iter()
        .any(|e| kb.canonical_sym(e.target) == target_canon)
    {
        bucket.push(cand);
    }
}

/// WI-842 — EVERY supplier of spec op `spec_op` for ONE carrier, from all three
/// routes, deduplicated by target. The per-carrier dual of
/// [`collect_spec_op_suppliers_by_carrier`]: same classification
/// ([`provision_supplier`]), same dedup, asked of one carrier because the caller is
/// the PER-CALL value-directed dispatch and has no whole-KB pass to hang an index on.
///
/// Proposal 058 §4.9's hardening rule — a read that SELECTS a provider's op goes
/// LOUD on the second candidate — is why this returns the whole list. It replaces
/// eval's `own .or_else(instance_fact_op_binding) .or_else(witness_op_for_carrier)`
/// chain, whose three `or_else` legs could not see past their first hit; the two
/// first-match readers that chain called (`witness_op_for_carrier` /
/// `witness_provision`) are DELETED rather than left beside this, so the first-match
/// witness read cannot come back.
///
/// ROUTE ORDER is the chain's own precedence (own member, then provisions in
/// `provides_rids_by_spec` order), so a single-candidate carrier resolves exactly
/// what it resolved before — the change is confined to what happens at a SECOND one.
///
/// It costs the chain's short-circuit: an `own` hit no longer skips the provision
/// walk, because skipping it is precisely how a second candidate stayed invisible.
/// The walk is over ONE spec's `provides_rids_by_spec` bucket, and MEASURED across
/// the suite's heaviest binary (1833 stdlib-loading tests, 592 value-directed
/// dispatches) the difference is inside the noise: 63.2 s → 63.7 s.
pub(crate) fn spec_op_suppliers_for_carrier(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    carrier: Symbol,
    spec_op: Symbol,
    op_short_sym: Symbol,
) -> SmallVec<[SpecOpSupplier; 2]> {
    let carrier_canon = kb.canonical_sort_sym(carrier);
    let mut out: SmallVec<[SpecOpSupplier; 2]> = SmallVec::new();
    // ROUTE 1 — the carrier's OWN member, the genuine override (WI-616).
    if let Some(target) = carrier_own_op(kb, carrier, spec_op, op_short_sym) {
        out.push(SpecOpSupplier {
            target,
            route: SupplyRoute::Own,
        });
    }
    // ROUTES 2 and 3 — a provision supplies it (instance fact / witness sort).
    for (provider, spec_t, bindings) in provisions_of_spec(kb, spec_sort) {
        let Some((c, supplier)) = provision_supplier(
            kb,
            spec_sort,
            spec_op,
            op_short_sym,
            provider,
            spec_t,
            &bindings,
        ) else {
            continue;
        };
        if c == carrier_canon {
            push_supplier_deduped(kb, &mut out, supplier);
        }
    }
    out
}

/// WI-652 — op symbols that have an EQUATIONAL definition `op(args) = rhs`
/// (guarded or not): the rule's head is `eq(op(args), rhs)`, so collect each LHS
/// head functor. Must walk ALL rules, not `rules_by_functor`: WI-139 unindexes
/// equational rules from the functor index (they're cite-required), so a functor
/// walk would miss every one. `is_equation` is likewise unusable — it rejects
/// guarded equations (`rule head(?s) = … :- …`), which are real definitions.
/// Sole consumer: [`check_eq_override_backing`]'s [`eq_override_backed`] (its
/// `eq=` leg) — WI-818 removed the other reader; [`op_backed`] no longer counts
/// any rule shape as backing.
pub(super) fn collect_eq_defined_ops(kb: &KnowledgeBase) -> std::collections::HashSet<Symbol> {
    let mut eq_defined: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    for rid in kb.live_rule_ids() {
        let Value::Term { id: head, .. } = *kb.rule_head_value(rid) else {
            continue;
        };
        if !crate::kb::load::is_equational_head(kb, head) {
            continue;
        }
        if let Term::Fn { pos_args, .. } = kb.get_term(head) {
            if let Some(&lhs) = pos_args.first() {
                if let Some(op) = head_functor_sym(kb, lhs) {
                    eq_defined.insert(op);
                }
            }
        }
    }
    eq_defined
}

/// WI-652 — is the carrier's own `eq` override backed? Sole probe of
/// [`carrier_has_unbacked_eq_override`].
///
/// WI-818 narrowed [`op_backed`] to EXECUTABLE backing only (body │ builtin) and
/// with it took away this helper's second caller, so the two flags that used to
/// select between them (`allow_builtin`, `RuleBacking`) are gone — each had one
/// reachable setting left. The legs kept here are the eq guard's own, and they are
/// deliberately NOT [`op_backed`]'s:
///   - the BUILTIN leg stays dropped — admitting `PartialEq.eq`'s builtin-ness
///     would mask exactly the empty `Map.eq` override this guard exists to catch;
///   - the `eq=` leg stays admitted — a carrier backing `eq` via an equational
///     `eq(?a, ?b) = rhs` (invisible to the general-clause probe, unindexed by
///     WI-139) must not be flagged spuriously. This does not unmask Map, whose
///     equational `get`-rewrite law contributes `get` (its LHS head), never
///     `Map.eq`, to [`collect_eq_defined_ops`];
///   - the RULE leg stays tightened to a GENERAL catch-all clause (all-var
///     positional head), so Map's compound-headed `get`-rewrite law under `Map.eq`
///     does not read as backing.
///
/// That this guard still counts rules while `op_backed` no longer does is not a
/// drift: it asks a DIFFERENT question. `op_backed` asks "can the evaluator run
/// this?"; this asks "did the author leave an override empty?" — a rule is
/// evidence of authorship either way.
pub(super) fn eq_override_backed(
    kb: &KnowledgeBase,
    op: Symbol,
    eq_defined: &std::collections::HashSet<Symbol>,
) -> bool {
    op_has_runnable_body(kb, op)
        || eq_defined.contains(&op)
        || kb
            .rules_by_functor_iter(op)
            .any(|r| !kb.is_fact(r) && rule_is_general_eq_clause(kb, r, op))
}

/// True iff the operation `op_short` (declared by the provided spec, as
/// `spec_op`) is backed for carrier `X`. See [`check_provider_operations`] for
/// the backing kinds. Conservative: any one source suffices.
///
/// MATCHED BY SHORT NAME, and that is still all this function asks. Whether the
/// member so matched actually FITS the spec operation — arity, parameter types and
/// order, return type — is [`check_member_signature`]'s question (WI-20260822-1MAGR),
/// asked in [`check_override_refinement`] and asked exactly where this function's
/// spec-op candidate contributes nothing, i.e. where the member is the only backing
/// there is. The two are not a drift: this one asks "can the evaluator run something
/// under this name for this carrier", and that one asks "is what it would run the
/// operation the provision claims".
///
/// WI-818 — "backed" means **EXECUTABLE**: a runnable body, or a builtin. A RULE
/// does not count, and that is the whole point of the ticket.
///
/// A spec is ABSTRACT, and so is an operation it only declares. A `rule` on the
/// spec (`rule head(?s) = fst(?p) :- splitFirst(?s) = some(?p)`) is a LAW relating
/// that abstract operation to another — it says what `head` MEANS, not how to
/// compute it for any particular carrier. The implementation is the PROVIDER's
/// job. This check exists to enforce exactly that obligation on a concrete
/// carrier, so admitting a law as if it discharged the obligation made the check
/// certify something it had not verified: the program loaded clean and then died
/// at run time with `UnknownOperation`, because the evaluator can only dispatch to
/// a body or a builtin — it cannot run a rule.
///
/// MEASURED, and the stdlib was the proof: with the rule legs admitted,
/// `List`/`MappedStream`/`FilteredStream` all passed this check for
/// `Stream.head`/`tail`/`headOption` while `head(cons(7, nil))` failed at run time
/// with `UnknownOperation { "head" }` — no user code involved. Dropping the rule
/// legs turns those three carriers × three operations into the load errors they
/// always should have been, which is why this change ships WITH executable
/// backing for them: default BODIES over `splitFirst` on the Stream spec (the
/// WI-362 pattern `isEmpty` already used, `tail`'s row gaining the guarded
/// `Error[EmptyStream]` it always incurred) plus `List`'s own `head`/
/// `headOption` overrides (WI-444).
///
/// This does NOT make the laws pointless: they remain the specification `head`
/// is proved against, and `Stream`'s own default BODIES (`isEmpty`/`takeN`/
/// `collect`, the WI-362 pattern) still back their ops — a spec-level default
/// body is runnable, so a carrier may still inherit it and supply nothing.
pub(super) fn op_backed(
    kb: &mut KnowledgeBase,
    carrier: Symbol,
    carrier_qn: &str,
    spec_op: Symbol,
    op_short: &str,
    host_realized: bool,
) -> bool {
    // Candidate definition symbols: the spec op itself, the carrier's resolved
    // op (own override or inherited spec default, via `sort_ops`), and the
    // carrier's own op by QN. NO namespace-level candidate: that leg existed
    // for the relational-rule shape (head functor `{namespace}.op`), which
    // WI-818 made non-backing — and a namespace-level operation BODY at
    // `{ns}.{op_short}` must not count either, because no dispatch table
    // (`sort_ops`, instance-fact binding, witness sort) can ever route a
    // spec-op call to it: counting it certified programs that loaded clean and
    // died at run time with `OperationBodyMissing` (measured; the review probe
    // is pinned as `ns_level_body_is_not_backing`).
    let mut cands: SmallVec<[Symbol; 4]> = SmallVec::new();
    cands.push(spec_op);
    let short_sym = kb.intern(op_short);
    if let Some(t) = kb.sort_ops_lookup(carrier, short_sym) {
        cands.push(t);
    }
    if let Some(s) = kb.try_resolve_symbol(&format!("{carrier_qn}.{op_short}")) {
        cands.push(s);
    }
    // WI-818: the EXECUTABLE kinds, and only those. A rule under `c` — whether an
    // equational law (`eq(op(args), rhs)`) or a relational clause
    // (`op(args, r) :- body`) — is not something the evaluator can dispatch to, so
    // it no longer reads as backing. WI-876 added the `operation_map` leg to the
    // shared [`op_is_executable`], so a member realized by the host counts here for
    // the SAME reason a builtin does — for a candidate that IS the carrier's.
    //
    // THE SPEC OP IS A WEAKER CANDIDATE, and deliberately so (WI-931). A default
    // BODY or a resolver BUILTIN on it is code every provider genuinely runs, so
    // either backs the carrier. A HOST MAPPING on it does not:
    // [`KnowledgeBase::is_host_mapped_op`] is a flat set with no carrier dimension,
    // so counting it would certify EVERY carrier of the spec the moment ONE
    // `operation_map` named the spec's own member. That is WI-876's defect A — the
    // half that being genuinely polymorphic does NOT answer, since it is about a
    // load-time claim rather than a wrong answer at run time.
    //
    // MEASURED on the first cut of `rustland/anthill-stl/anthill/persistence.anthill`:
    // with the spec-level `operation_map` counted here, an arbitrary
    // `entity ZzNotAStore(v: Int64)` claiming `fact NonMonotonicStore[ZzNotAStore]`
    // LOADED CLEAN, as did a reinstated `SqlStore` that no host implements.
    //
    // Keyed on the SYMBOL, not on which slot it arrived in: `sort_ops_lookup`'s
    // inherited-default leg returns the spec's own member for a carrier that
    // overrides nothing, so the spec op reaches the carrier slot too and a
    // position-based test would be bypassed by the very case it exists to catch
    // (measured — the first fix was position-based and changed nothing).
    //
    // A mapping says the OPERATION has an implementation; it never says a given
    // CARRIER is realized. That second question has its own declaration — an
    // `anthill.realization.Implementation` fact, which
    // [`check_provider_operations`] consults before it ever reaches this function.
    let spec_op_canon = kb.canonical_sym(spec_op);
    if cands.iter().any(|&c| {
        if kb.canonical_sym(c) == spec_op_canon {
            kb.is_builtin(c) || op_has_runnable_body(kb, c)
        } else {
            op_is_executable(kb, c)
        }
    }) {
        return true;
    }
    // WI-880 — the SPEC-LEVEL mapping, admitted for a HOST-REALIZED carrier and for
    // no other. It is the leg the paragraph above refuses in general, and the two
    // rules are not in tension: the objection there is that a flat mapping set has no
    // carrier dimension, so counting it unconditionally certifies every carrier of the
    // spec. `host_realized` IS that carrier dimension — an
    // `anthill.realization.Implementation` fact naming this carrier, the program's own
    // declaration that a host artifact realizes it — and the two claims compose
    // exactly: the artifact realizes the carrier, the mapping says the operation has a
    // host implementation, so this carrier's operation is implemented.
    //
    // THIS IS WHAT THE WHOLESALE SKIP USED TO DO, minus the part that was wrong. It is
    // what keeps `anthill.persistence.filesystem.FileStore` loading: its six storage
    // operations are genuinely polymorphic (one rust function per operation, resolving
    // the store VALUE to its registered mirror), so `persistence.anthill` maps them
    // once on the SPEC and there is no per-backend function to name — measured, the
    // three filesystem backends are the whole population that needs this leg, and
    // without it they lose `retract`/`update`/`retrieve`.
    //
    // `ZzNotAStore` STAYS REFUSED, which is the WI-931 measurement this must not undo:
    // an arbitrary `entity ZzNotAStore(v: Int64)` claiming `fact
    // NonMonotonicStore[ZzNotAStore]` has no `Implementation` fact, so `host_realized`
    // is false and the spec mapping is not offered to it.
    host_realized && kb.is_host_mapped_op(spec_op)
}

/// Top functor symbol of a term head — a `Fn` functor, or a bare `Ref`/`Ident`.
pub(super) fn head_functor_sym(kb: &KnowledgeBase, tid: TermId) -> Option<Symbol> {
    match kb.get_term(tid) {
        Term::Fn { functor, .. } => Some(*functor),
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

/// Qualified name an `Implementation.target` field points at — a `String`
/// literal (`emit_implementation_fact`'s shape) or a sort reference.
pub(super) fn impl_target_qn(kb: &KnowledgeBase, target: TermId) -> Option<String> {
    match kb.get_term(target) {
        Term::Const(Literal::String(s)) => Some(s.clone()),
        Term::Ref(s) | Term::Ident(s) => Some(kb.qualified_name_of(*s).to_string()),
        Term::Fn { functor, .. } => Some(kb.qualified_name_of(*functor).to_string()),
        _ => None,
    }
}

/// Build the `requires` sub-goals for the provider-side check (WI-356).
/// Walks `spec`'s **direct** `requires`, instantiating each clause at the
/// provision's σ. WI-857 made this the producer of the dictionary's SPEC HALF too
/// ([`dict_sub_goals`]) — one walk for the check and the dictionary, so a
/// requirement the load verified is the requirement the dictionary carries. Distinct
/// from [`candidate_provider_sub_goals`] (the resolver's
/// impl-side template) in that σ is keyed by short **name**, not symbol: the
/// stdlib shorthand `requires Eq[T]` stores the binding value as the
/// *required* spec's own param (`Eq.T`), tied to the enclosing param only by
/// the shared short name `T`; a symbol-keyed substitution (what the resolver
/// uses, where the requires values reference the impl's *own* params) never
/// reaches it. Matching by name grounds `Eq[T] → Eq[T=Int]` from an
/// `Ord[T=Int]` provision. A requires-param the provision leaves unbound
/// stays as its original type-param ref — the caller (`check_provider_requires`)
/// inspects each goal and only resolves the *fully concrete* ones precisely,
/// falling back to a base-level existence check otherwise (the unbound shape
/// can't be matched against ground facts — see `dispatch_values_match`). The
/// carrier never discriminates here (WI-350): these are by-binding sub-goals,
/// so `carrier` is `None`.
pub(super) fn provider_requires_subgoals(
    kb: &mut KnowledgeBase,
    spec: Symbol,
    sigma: &[(String, TermId)],
) -> Vec<SortGoal> {
    let chain = direct_requires_chain(kb, spec);
    let mut out: Vec<SortGoal> = Vec::with_capacity(chain.len());
    for entry in &chain {
        let required = entry.required_sort;
        let Some((_, entry_bindings)) = unwrap_spec_view_value(kb, &entry.spec) else {
            // WI-857: KEEP THE SLOT, exactly as `candidate_provider_sub_goals` does —
            // this walk is now positional (it produces the dictionary's spec half, not
            // only the load check's goals), so dropping an entry would shift every
            // later slot into it.
            //
            // But the slot is a GUESS: a bindings-free goal is one every provider
            // matches, so it is RESOLVABLE, and resolving is the concern — not
            // indexing. In `check_provider_requires` (which shares this walk) empty
            // bindings make `concrete` vacuously true, so a previously-skipped entry
            // would now be resolved and could raise a load error; in the provider half
            // an unresolvable one fails the whole dispatch. MEASURED UNREACHABLE: a
            // probe on this branch across the `anthill-core` suite hit it ZERO times —
            // a `requires` clause's spec is always a `SortView`, a bare ref or an
            // ident. The assert says so, and fires if that ever stops being true,
            // rather than letting a guessed goal decide a load.
            debug_assert!(
                false,
                "WI-857: `requires {}` has no readable spec head — the dictionary slot \
                 for it is a bindings-free guess",
                kb.qualified_name_of(required),
            );
            out.push(SortGoal {
                spec_sort: required,
                bindings: SmallVec::new(),
                carrier: None,
            });
            continue;
        };
        let r_qn = kb.qualified_name_of(required).to_string();
        let mut bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        for (k, v) in &entry_bindings {
            if !is_type_param_binding(kb, *k, &r_qn) {
                continue;
            }
            let nv = subst_requires_value(kb, *v, sigma);
            bindings.push((*k, nv));
        }
        out.push(SortGoal {
            spec_sort: required,
            bindings,
            carrier: None,
        });
    }
    out
}

/// The term shapes a `requires`-clause binding value uses to spell a bare NAME:
/// the canonical `Ref(S)` / `Ident(S)`, and the nullary `Fn{S}` that `convert_term`
/// emits for a bare name. ONE owner, because two readers must agree on it —
/// [`subst_requires_value`], which substitutes σ at exactly these shapes, and
/// `check_use_site_requires_eq`, which reads the RAW (unsubstituted) binding back to
/// name the container parameter in its diagnostic. If they disagreed, the diagnostic
/// would silently fall back to naming the spec's parameter instead of the
/// container's. The WI-511 `Fn{c}` → `Ref(c)` flip is exactly the kind of change
/// that would otherwise have to be applied to both by hand.
///
/// [`type_ctor_view`] (WI-1048) reads the same equivalence and then some — it also
/// admits an APPLIED `Fn`, because there a bare name and an application of it are
/// the same constructor with one side eliding its arguments. It is deliberately not
/// expressed in terms of this function: the question there is "which constructor",
/// not "is this a bare name".
pub(super) fn requires_bare_name_sym(kb: &KnowledgeBase, v: TermId) -> Option<Symbol> {
    match kb.get_term(v) {
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => Some(*functor),
        _ => None,
    }
}

/// Substitute σ into one `requires`-clause binding value (by short name);
/// leave anything σ doesn't ground unchanged. Recurses through `Fn`
/// children (`List[T]`, `Pair[A, B]`).
fn subst_requires_value(kb: &mut KnowledgeBase, v: TermId, sigma: &[(String, TermId)]) -> TermId {
    if let Some(s) = requires_bare_name_sym(kb, v) {
        return map_requires_name(kb, s, v, sigma);
    }
    match kb.get_term(v).clone() {
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => {
            let mut changed = false;
            let new_pos: SmallVec<[TermId; 4]> = pos_args
                .iter()
                .map(|t| {
                    let nt = subst_requires_value(kb, *t, sigma);
                    if nt != *t {
                        changed = true;
                    }
                    nt
                })
                .collect();
            let new_named: SmallVec<[(Symbol, TermId); 2]> = named_args
                .iter()
                .map(|(k, t)| {
                    let nt = subst_requires_value(kb, *t, sigma);
                    if nt != *t {
                        changed = true;
                    }
                    (*k, nt)
                })
                .collect();
            if !changed {
                return v;
            }
            kb.alloc(Term::Fn {
                functor,
                pos_args: new_pos,
                named_args: new_named,
            })
        }
        _ => v,
    }
}

/// σ-ground a bare name in a `requires` value by short name; otherwise keep
/// it as-is. See [`provider_requires_subgoals`].
fn map_requires_name(
    kb: &KnowledgeBase,
    s: Symbol,
    orig: TermId,
    sigma: &[(String, TermId)],
) -> TermId {
    let short = kb.local_name_of(s);
    sigma
        .iter()
        .find(|(n, _)| n == short)
        .map_or(orig, |(_, val)| *val)
}

/// True iff `value` mentions any abstract type-parameter anywhere in its
/// structure — a `Var`, a `Ref`/`Ident` to a `sort T = ?` param, or that
/// param as a nullary `Fn` functor (the `make_name_term` shape the loader
/// emits for a bare name, e.g. the unbound `E` left by `requires
/// Iterable[…, E = Effect]`). Used to decide whether a σ-instantiated
/// `requires` goal is concrete enough to resolve precisely against ground
/// facts, vs. falling back to the base-level existence check (WI-356).
pub(super) fn contains_type_param(kb: &KnowledgeBase, value: TermId) -> bool {
    if is_type_param_value(kb, value) {
        return true;
    }
    match kb.get_term(value) {
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => {
            // A `Fn` functor that is itself a param (`Fn{Effect}` nullary, or a
            // param used as a head) makes the value abstract.
            if is_sort_param_symbol(kb, *functor) {
                return true;
            }
            let pos: SmallVec<[TermId; 4]> = pos_args.clone();
            let named: SmallVec<[(Symbol, TermId); 2]> = named_args.clone();
            pos.iter().any(|t| contains_type_param(kb, *t))
                || named.iter().any(|(_, t)| contains_type_param(kb, *t))
        }
        _ => false,
    }
}

/// WI-20260822-1TKN0 — the carrier-neutral twin of [`contains_type_param`], for a
/// reader that holds an effect label rather than a `TermId`.
///
/// NOT A CONVENIENCE WRAPPER. [`contains_type_param`] takes a `TermId`, so its
/// callers reach it through `matches!(v, Value::Term { .. })` — a CARRIER test
/// standing in for an ABSTRACTNESS test. The two questions are not the same one:
/// a denoted effect label (`Modify[c]`) rides a `Value::Node` because it carries
/// an occurrence, not because it is parametric, and the override-refinement
/// effects leg read that carrier as "cannot decide" and fail-opened the WHOLE
/// ROW — an `Eff2` the leg refuses on its own went unreported the moment a
/// `Modify[c]` sat beside it in the same row (measured; see
/// `a_modify_target_does_not_mask_a_named_effect_widening`).
///
/// Mirrors [`TermView::bears_opaque`]'s shape for the same reason it exists: a
/// reader that asks the structure cannot drift when a carrier is added.
/// On the `TermId` carrier this decides exactly what [`contains_type_param`]
/// decides, arm for arm — `Var` ⇒ abstract, `Ref`/`Ident` ⇒
/// [`is_sort_param_symbol`], a functor head that is itself a param ⇒ abstract
/// (which subsumes the nullary-`Fn` name shape), else recurse.
///
/// An `Opaque` head answers ABSTRACT: it presents no structure, so nothing here
/// can establish it is concrete, and "cannot decide" is the fail-open direction
/// this leg takes everywhere else.
pub(super) fn view_contains_type_param<V: TermView>(kb: &KnowledgeBase, v: &V) -> bool {
    match v.head(kb) {
        ViewHead::Var(_) => true,
        ViewHead::Ident(s) => is_sort_param_symbol(kb, s),
        ViewHead::Functor {
            functor, pos_arity, ..
        } => {
            if functor.is_some_and(|f| is_sort_param_symbol(kb, f)) {
                return true;
            }
            (0..pos_arity).any(|i| {
                v.pos_arg(kb, i)
                    .is_some_and(|a| view_contains_type_param(kb, &a))
            }) || v.named_keys(kb).into_iter().any(|k| {
                v.named_arg(kb, k)
                    .is_some_and(|a| view_contains_type_param(kb, &a))
            })
        }
        ViewHead::Opaque => true,
        ViewHead::Const(_) | ViewHead::Bottom => false,
    }
}

/// WI-20260822-1TKN0 — does this effect label carry a DENOTED value-in-type
/// (`Modify[c]`, whose target is a PLACE) anywhere?
///
/// ONE READER, and it asks about ALIGNMENT, not about comparability: a label with
/// a denoted target NAMES a place, so it is the shape `align_effect_label` must
/// rewrite into the spec's parameter vocabulary — which is why
/// `wants_result_alignment` in [`check_override_refinement`] consults it. A
/// `Modify[result]` names the result binder, so an override restating the spec's
/// own row verbatim needs the binder aligned even with no contract clause between
/// the two ops (`MutableStack.new` over `MutableCollection.new`).
///
/// IT NO LONGER MARKS ANYTHING UNDECIDABLE. Until WI-20260823-39AD2 this also
/// gated a fail-open: a denoted target facing a spec `Modify` over a resource TYPE
/// could not be compared, because `types_compatible` relates two denoteds by
/// EQUALITY (`unify_denoted_view`) and a place is not equal to a type. That shape
/// is now unreachable — a `Modify` target is a PLACE on both sides
/// ([`check_modify_targets`] refuses a type target at its declaration), so equality
/// after alignment is the EXACT relation, and the gate was deleted rather than
/// replaced by the type-vs-place implication it seemed to want.
///
/// Deliberately `Denoted` ONLY, not "any value-in-type": an `ExprCarried`
/// projection (`s.E`) is a rigid type-level neutral that
/// [`expr_carried_zeta`] already relates exactly, and the stdlib's
/// `FiniteStream.splitFirst` override is compared through it today.
pub(super) fn view_bears_denoted<V: TermView>(kb: &KnowledgeBase, v: &V) -> bool {
    if matches!(type_head(kb, v), TypeHead::Denoted) {
        return true;
    }
    match v.head(kb) {
        ViewHead::Functor { pos_arity, .. } => {
            (0..pos_arity).any(|i| v.pos_arg(kb, i).is_some_and(|a| view_bears_denoted(kb, &a)))
                || v.named_keys(kb).into_iter().any(|k| {
                    v.named_arg(kb, k)
                        .is_some_and(|a| view_bears_denoted(kb, &a))
                })
        }
        _ => false,
    }
}

/// WI-20260822-1TKN0 — is this effect label a `Modify` (the frame-condition
/// marker, kernel-language.md §5.6)? Keyed on the SYMBOL via
/// [`ViewHead::functor_sym`], which reads the head off both the bare `Ref(Modify)`
/// and the applied `Modify[T = …]` spellings, and cannot collide with a
/// same-named user sort the way a qualified-name string match can.
///
/// `modify` is resolved ONCE by the caller and threaded in — this runs per effect,
/// per operation, per provision, and the enclosing check already counts its
/// qualified-name lookups (see `wants_result_alignment`'s cost note). `None` (no
/// `Modify` declared at all — a KB loaded without the prelude) answers `false` for
/// every label, the same verdict a per-call resolve would give.
pub(super) fn effect_is_modify<V: TermView>(
    kb: &KnowledgeBase,
    e: &V,
    modify: Option<Symbol>,
) -> bool {
    modify.is_some() && e.head(kb).functor_sym() == modify
}

/// True iff `short` names a type-parameter (vs an op) of the spec at
/// `spec_qn`. Determined by checking whether `<spec_qn>.<short>`
/// resolves to a SortAlias-bearing symbol — only spec params do.
pub(super) fn is_type_param_binding(kb: &KnowledgeBase, short: Symbol, spec_qn: &str) -> bool {
    type_param_sym_of_binding(kb, short, spec_qn).is_some()
}

/// WI-431 (B): if `short` (a provision binding key) names a type parameter of the
/// spec `spec_qn`, return the RESOLVED spec-parameter symbol — the one the spec
/// operations' types actually reference (`Combiner.combine`'s `Ref(Combiner.T)`)
/// — so a σ keyed on it actually substitutes. The raw binding key can be a
/// different `Symbol` copy (resolved in the fact's scope), against which
/// `substitute_impl_params_alloc`'s `Symbol`-equality match is a silent no-op.
pub(super) fn type_param_sym_of_binding(
    kb: &KnowledgeBase,
    short: Symbol,
    spec_qn: &str,
) -> Option<Symbol> {
    // `local_name_of` borrows from `kb`, which is only read here — no `to_string()`
    // needed to build the qualified name (this runs per binding key, per cover
    // walk, on the dispatch path).
    let qn = format!("{spec_qn}.{}", kb.local_name_of(short));
    let s = kb.try_resolve_symbol(&qn)?;
    resolve_sort_alias(kb, s).map(|_| s)
}

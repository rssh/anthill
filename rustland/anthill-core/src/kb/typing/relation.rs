//! Relations as values: typing a relation reference, its projection, rename and column
//! access, from the columns of its clauses.

use super::*;

/// WI-714 (proposal 052) C3 — synthesize the `Relation[T]` type a BARE rule
/// reference denotes. `T` is the named tuple of the relation's free head parameters
/// in declaration order (**`Unit`** for zero — a boolean/membership relation), each
/// column typed at the **lub** of that
/// head parameter across the relation's clauses (WI-287 `join_types`; a disjoint
/// pair with no lub is a load error, never a silent widen to `Term`). `sym` is a
/// rule label or head functor (the caller gates on `SymbolKind::Goal | Rule`).
///
/// The access-effect row `E ⊇ {Error}` is threaded through the `provides` edge; it
/// is not pinned on the sort here (Typing §3) — a follow-up increment.
pub(super) fn relation_reference_type(
    kb: &mut KnowledgeBase,
    sym: Symbol,
    span: Option<Span>,
    occ: &Rc<NodeOccurrence>,
    site: Option<CitationSite<'_>>,
) -> Result<Value, TypeError> {
    let mut columns = relation_columns_across_clauses(kb, sym, span)?;
    let Some(site) = site else {
        return relation_type_from_columns(kb, sym, columns, occ.span, span);
    };
    let opened = open_citation_params(kb, sym, &mut columns);
    let mut subst = Substitution::new();
    let rigid = body_rigids(kb, site.env);
    if let Some((owner, params)) = &opened {
        seed_citation_params(kb, &mut subst, occ, sym, span, *owner, params, site.env, &rigid)?;
    }
    let column_types: Vec<(Symbol, Value)> =
        columns.iter().map(|c| (c.name, c.ty.clone())).collect();
    let ty = relation_type_from_columns(kb, sym, columns, occ.span, span)?;
    let ty = settle_citation_type(kb, &rigid, &mut subst, sym, span, opened, site.expected, ty)?;
    // S2 — the bare citation's implicit arguments: no column is bound, so each read is
    // routed over the columns' own types at this citation. QUEUED, not computed — see
    // [`PendingCitationRoutes`].
    queue_citation_routes(kb, site.env, occ, sym, column_types, Vec::new(), subst);
    Ok(ty)
}

/// WI-20260911-5G28A S1 — WHERE a citation is typed, for the step that reads its sort's
/// parameters: the environment (which sort's member the citation is written in) and the
/// type its consumer passed down, if any. Built only for a citation in FUNCTIONAL code —
/// an operation or `const` body. A rule body unifies types at run time (WI-622's rule for
/// an operation's parameter, which the rule-body walk skips for the same reason), so its
/// citations keep the relation's own variables and pass `None`.
pub(super) struct CitationSite<'a> {
    pub(super) env: &'a TypingEnv,
    pub(super) expected: Option<&'a Value>,
}

/// WI-20260911-5G28A S1 — one type parameter of the cited relation's ENCLOSING SORT, as
/// one citation sees it: a variable of its own, fresh per citation.
pub(super) struct CitationParam {
    /// The declared parameter, qualified.
    param: Symbol,
    /// The sort's canonical variable for it — the one the relation's clauses mention.
    canonical: VarId,
    /// This citation's variable, which replaced `canonical` in every column type.
    var: VarId,
}

/// WI-20260911-5G28A S1 — OPEN the enclosing sort's parameters for ONE citation: every
/// parameter a column type mentions gets a fresh variable, substituted for the sort's
/// canonical one in every column. `None` when the relation is not declared in a sort with
/// parameters, or when no column mentions one.
///
/// WHY: a relation declared in `sort Wrap[T]` types a column `?x: Wrap[T = T]` at the
/// SORT's canonical `T` — one variable shared by every clause and every citation. It is
/// neither a wildcard nor something a citation may bind, so a citation that said which
/// instance it meant was refused against it: `Wrap[T = Colour].dom.head.x` returned as
/// `Wrap[T = Colour]` reported `got Wrap[T = ?T]`, and `Wrap.dom(wrap(red()))` "argument
/// binding column `x` has an incompatible type" (060-implementation §7.3, defect (2)). An
/// operation call has the same parameters and never had the problem, because it
/// instantiates them per call; this is that instantiation, for a citation.
///
/// ONE VARIABLE PER PARAMETER FOR THE WHOLE CITATION, across the relation's clauses — the
/// columns arrive here already lubbed across them, so a clause cannot pin its own copy.
fn open_citation_params(
    kb: &mut KnowledgeBase,
    sym: Symbol,
    columns: &mut [ClauseColumn],
) -> Option<(Symbol, Vec<CitationParam>)> {
    let owner = impl_parent_sort_of_op(kb, sym)?;
    let pairs = sort_type_params_as_pairs(kb, owner);
    let mut renaming = Substitution::new();
    let mut params: Vec<CitationParam> = Vec::new();
    for (param, var_term) in pairs.iter() {
        // WI-954: a published parameter's variable IS a `Var::Global` term — the loader
        // allocates it from a `VarId`, so there is no other shape to skip.
        let Term::Var(Var::Global(canonical)) = kb.get_term(*var_term) else {
            unreachable!("a published type parameter's canonical variable is a Var::Global term");
        };
        let canonical = *canonical;
        if !columns.iter().any(|c| occurs_in_view(kb, canonical, &c.ty)) {
            continue;
        }
        let var = kb.fresh_var(*param);
        let var_term = kb.alloc(Term::Var(Var::Global(var)));
        renaming.bind_term(kb, canonical, var_term);
        params.push(CitationParam {
            param: *param,
            canonical,
            var,
        });
    }
    if params.is_empty() {
        return None;
    }
    for c in columns.iter_mut() {
        c.ty = walk_type_deep_value(kb, &renaming, &c.ty);
    }
    Some((owner, params))
}

/// WI-20260911-5G28A S1 — what a citation says about its sort's parameters BEFORE its
/// arguments are read, in the order an operation call takes the same sources (Path 1 in
/// `check_apply_iter`): the RECEIVER BRACKET first — the written instance beats an
/// implicit one — then, for a citation written in a member of the relation's own sort,
/// the ENCLOSING INSTANCE (WI-424's sibling rule: inside `sort Wrap[T]`, `dom` means this
/// instance's `dom`). Applied arguments and the expected type reach the variables later,
/// through the same σ.
///
/// The bracket is read by [`receiver_bracket_entries`], the reader an operation call's
/// receiver uses, so `Wrap[T = Colour].dom` and `Wrap[T = Colour].op()` cannot read one
/// bracket two ways. It binds only a parameter the columns mention: a bracket that fills
/// nothing is not refused here (060-implementation §7.3, D4).
///
/// A BRACKET VALUE IS READ IN THE BODY'S OWN TERMS ([`body_rigids`]): `Wrap[T = X].dom`
/// written in `operation g[X]` means THIS body's `X`, a rigid that unifies with itself
/// alone. MEASURED: bound to `X`'s variable instead, the citation loaded both as the
/// declared `Wrap[T = X]` and as `Wrap[T = Colour]` or `Wrap[T = Y]` — the variable
/// unified with whatever the return check offered it.
#[allow(clippy::too_many_arguments)]
fn seed_citation_params(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    occ: &Rc<NodeOccurrence>,
    sym: Symbol,
    span: Option<Span>,
    owner: Symbol,
    params: &[CitationParam],
    env: &TypingEnv,
    rigid: &Substitution,
) -> Result<(), TypeError> {
    if let Some(rt) = call_recv_type_of(occ).cloned() {
        // A BRACKET ON ANOTHER SORT BINDS NOTHING HERE, and saying nothing about it would
        // be a silent drop of written text: the author named an instance, and a pin from an
        // argument or the expected type could then load the citation at some OTHER one.
        // Unreached by the corpus — `Sort[…].rel` resolves `rel` in `Sort`'s own scope, and
        // `sort_application_parts` reads an alias as its underlying sort — so this is the
        // loud form of an invariant, not a diagnostic anyone is expected to meet.
        let base = sort_application_parts(kb, &rt)
            .filter(|(base, _)| same_sort_canonical(kb, *base, owner));
        let Some((_, written)) = base else {
            return Err(TypeError::Other {
                site: TypeError::here(),
                span,
                context: TypeErrorContext::Rule {
                    name: sym,
                    field: RuleField::Whole,
                },
                expected: format!(
                    "a receiver bracket on `{}`, the sort that declares `{}`",
                    kb.qualified_name_of(owner),
                    kb.qualified_name_of(sym),
                ),
                actual: format!("`{}`, which binds none of its parameters", type_display_name_value(kb, &rt)),
            });
        };
        for entry in receiver_bracket_entries(kb, owner, &written) {
            if let Some(p) = params.iter().find(|p| p.param == entry.param) {
                let value = walk_type_deep_value(kb, rigid, &entry.value);
                // A FRESH variable, minted for this citation alone: nothing has bound it and
                // the value cannot mention it, so the bind cannot fail — and if it ever did,
                // the author would be told a parameter they WROTE is undetermined.
                let bound = bind_resolved(kb, subst, p.var, value);
                assert!(bound, "binding a citation's fresh parameter variable");
            }
        }
    }
    let same_sort = env
        .enclosing_sort()
        .is_some_and(|enclosing| same_sort_canonical(kb, enclosing, owner));
    if same_sort {
        for p in params {
            if subst.resolve_as_value(p.var).is_some() {
                continue;
            }
            if let Some((_, instance_rigid)) = env
                .enclosing_instance_param_rigids()
                .iter()
                .find(|(canonical, _)| *canonical == p.canonical)
            {
                subst.bind_term(kb, p.var, *instance_rigid);
            }
        }
    }
    Ok(())
}

/// WI-20260911-5G28A S1 — the last source, then the verdict. The type the consumer passed
/// down pins what the bracket, the arguments and the enclosing instance left open —
/// `operation g() -> Relation[T = (x: List[T = Letter]), …] = List.domain` — adopted only
/// if the whole type unifies, so a mismatch is left for the ordinary expected-type check to
/// report rather than half-applied here. Then any parameter still free is REFUSED: the
/// relation value would carry a variable its consumer cannot recover, which is WI-270's
/// rule for an operation's parameter (`check_unconstrained_type_params`), applied at the
/// citation — LOCALLY, as WI-270 applies it: a consumer further up the chain that passes no
/// expected type down (`Wrap.dom.head.x` against the return) does not count, exactly as it
/// does not for `Option.none().isEmpty()`.
///
/// The expected type is read in the body's own terms, as the bracket is
/// ([`seed_citation_params`]): a parameter it names pins the citation to that parameter's
/// rigid, which nothing else can then unify with.
#[allow(clippy::too_many_arguments)]
fn settle_citation_type(
    kb: &mut KnowledgeBase,
    rigid: &Substitution,
    subst: &mut Substitution,
    sym: Symbol,
    span: Option<Span>,
    opened: Option<(Symbol, Vec<CitationParam>)>,
    expected: Option<&Value>,
    ty: Value,
) -> Result<Value, TypeError> {
    let Some((owner, params)) = opened else {
        return Ok(ty);
    };
    if let Some(expected) = expected {
        let expected = walk_type_deep_value(kb, rigid, expected);
        let mut trial = subst.clone();
        if unify_types(kb, &mut trial, &ty, &expected) {
            *subst = trial;
        }
    }
    for p in &params {
        let var_term = kb.alloc(Term::Var(Var::Global(p.var)));
        if resolved_var(kb, &walk_view(kb, subst, &TermIdView(var_term))).is_some() {
            return Err(TypeError::UnconstrainedCitationParam {
                span,
                relation: sym,
                sort: owner,
                type_param: p.param,
            });
        }
    }
    Ok(walk_type_deep_value(kb, subst, &ty))
}

/// The body's type-parameter variables mapped to their RIGIDS (`env.param_rigids()`, the
/// map `rigidify_op_type_params` built when the body's check began), as a substitution: how
/// a type WRITTEN in this body — a bracket value, the declared return passed down as the
/// expected type — is read in the body's own terms.
fn body_rigids(kb: &mut KnowledgeBase, env: &TypingEnv) -> Substitution {
    let mut rigid = Substitution::new();
    for (param_var, rigid_term) in env.param_rigids() {
        rigid.bind_term(kb, *param_var, *rigid_term);
    }
    rigid
}

/// WI-20260911-WT8WG — the citation-site diagnostic for a `<Sort>.domain` that was
/// MINTED but never given a clause, or `None` when `sym` is not such a name.
///
/// A SORT WITH NO DOMAIN is why it exists since WI-20260925-SHED7, which gave the
/// parameterised sort its value face (the case this was written for): a sort whose field
/// nothing can fill has a minted `.domain` and no `fill` behind it, and its citation says
/// so. The name is minted in pass 1, before the derivation can decline
/// (`load::mint_domain_value_face_name`) — without it there is nothing to attach a reason
/// to, and the author gets "no such member `domain`": true, and useless.
fn domain_value_face_refusal(
    kb: &KnowledgeBase,
    sym: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    let qn = kb.qualified_name_of(sym).to_string();
    let sort_qn = qn.strip_suffix(".domain")?;
    let sort = kb.try_resolve_symbol(sort_qn)?;
    // TWO RECORDS, TWO QUESTIONS, and the message must not merge them. The first says
    // "the domain EXISTS, the name does not" — the sort's `fill` was derived under an
    // internal name because something else holds this one. The second says the sort has
    // NO domain at all (a field nothing can fill), which is `sort_domain_decline_reason`'s
    // own answer. Saying "has a domain" in that second case would be false, so the two get
    // their own sentence.
    let (has_domain, reason) = match kb.domain_value_face_decline_reason(sort) {
        Some(reason) => (true, reason),
        None => (false, kb.sort_domain_decline_reason(sort)?),
    };
    Some(TypeError::Other {
        site: TypeError::here(),
        span,
        context: TypeErrorContext::Rule {
            name: sym,
            field: RuleField::Whole,
        },
        expected: format!("`{qn}`, the derived domain of sort `{sort_qn}`, as a relation"),
        actual: if has_domain {
            format!("sort `{sort_qn}` has a domain but no `.domain` to cite it by: {reason}")
        } else {
            format!("sort `{sort_qn}` has no derived domain, so no `.domain` to cite: {reason}")
        },
    })
}

/// WI-20260902-4NEKZ — THE DOTTED NAME a LOADER-BUILT `field_access` chain spells, when
/// every segment of it is already resolved.
///
/// A paren-less `ns.rel` in a rule-body VALUE slot keeps its `field_access` chain: 719FJ
/// collapses such a citation only in a LOGICAL position, because a data slot holds a term
/// whose spelling is its identity and `fact holds(ns.rel)` must build the term the goal
/// `holds(ns.rel)` searches for. So the chain reaches the typer whole, and the typer used
/// to walk into its LEAVES.
///
/// PROVENANCE FIRST, AND IT IS THE LOADER'S ANSWER RATHER THAN A SHAPE TEST. Every level
/// must carry [`NodeOccurrence::is_dot_chain`] — the parse term's `is_minted` bit, which
/// `load::dotted_citation_name` gates on for the same reason (WI-20260901-92VA4: a
/// HAND-WRITTEN `field_access(a, b)` is a call to whatever that name denotes at that
/// scope, not the desugaring of a dot). Without it this recognizer read a written
/// `anthill.reflect.field_access(ns, rel)` as the name `ns.rel` and let the program LOAD
/// CLEAN — a SILENT ACCEPTANCE, worse than the noisy refusal it replaced, found by
/// `/code-review` on this ticket's own first cut. It cannot be recovered by shape:
/// measured, with a one-segment receiver the two forms reach the typer as identical
/// nodes — same functor, a resolved `Ref` receiver and a bare `Ident` selector in both.
///
/// AND THEN NO SCOPE IS CONSULTED, which is what makes the rest a read rather than a
/// second resolution ladder: the loader re-routes the chain LEVEL BY LEVEL, so each
/// receiver segment already carries its FULLY-QUALIFIED symbol and only the final field is
/// a bare intern. Measured on all three citation forms — `zzls.inner.rel` (absolute),
/// `inner.rel` written inside `zzls2` (relative), and `..zzls3.inner.rel` (marked
/// absolute) — the receiver leaf is `Ref` with qualified name `zzls.inner` /
/// `zzls2.inner` / `zzls3.inner` in each. Joining that with the field's SHORT name
/// therefore reproduces the name the author wrote, wherever they wrote it.
///
/// `None` the moment a segment does NOT resolve (an `Expr::Ident` root or receiver), so a
/// chain naming nothing keeps whatever the ordinary path says about it.
fn loader_chain_dotted_name(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> Option<String> {
    match occ.as_expr()? {
        Expr::Ref(sym) => Some(kb.qualified_name_of(*sym).to_string()),
        Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        } if occ.is_dot_chain()
            && named_args.is_empty()
            && pos_args.len() == 2
            && kb.try_resolve_symbol(dt::qualified(dt::FIELD_ACCESS)) == Some(*functor) =>
        {
            let base = loader_chain_dotted_name(kb, &pos_args[0])?;
            // BOTH LEAF SPELLINGS. A resolved intermediate segment is a `Ref` and the
            // final field is an `Ident` (the bare intern of the written word); the SHORT
            // name is taken in either case, since `base` already carries the qualification.
            let field = match pos_args[1].as_expr()? {
                Expr::Ref(f) | Expr::Ident(f) => short_name_of(kb.local_name_of(*f)).to_string(),
                _ => return None,
            };
            Some(format!("{base}.{field}"))
        }
        _ => None,
    }
}

/// WI-20260902-4NEKZ — the RELATION a dotted paren-less citation in a rule-body value slot
/// cites, or `None` when this node is not such a citation.
///
/// WHAT IT REPAIRS, measured on the delivered WI-20260902-VNWAW tree — `rule dRel(1) :-
/// zzf2.inner.rel = 7` beside `rule rel(1) :- base(1)`:
///
///   6:19: type mismatch in zzf2.name:  expected resolved name, got unresolved
///   6:19: type mismatch in inner.name: expected resolved name, got unresolved
///   6:19: type mismatch in rel.name:   expected resolved name, got unresolved
///
/// THREE errors at ONE span, each blaming a segment of a name that RESOLVES, because
/// [`check_bare_ref`] was reached once per leaf and a namespace has no value reading. The
/// ONE-SEGMENT spelling of the same program says the true thing — one error, `eq.b
/// (op-arg): expected Relation[…], got Int64` — and so does the OPERATION-BODY spelling of
/// the dotted one, because `Loader::try_qualified_rule_ref` collapses the chain there.
///
/// SO THE FIX IS THE TYPER'S AND NOT THE LOADER'S, and that is a measurement, not a
/// preference. Collapsing the chain in a rule-body value slot would fell
/// `wi_719fj_dotted_paren_less_citation_test::a_data_slot_still_stores_the_chain_on_both_sides_of_a_match`:
/// the FACT's argument is a TERM built by `convert_term` (which keeps the chain) while the
/// rule body is an OCCURRENCE, so rewriting one side alone stops them matching — WI-756's
/// rule, and the whole reason 719FJ gated its collapse on a logical position. Reading the
/// chain here changes no term.
///
/// IT IS NOT A LIE ABOUT THE VALUE, checked rather than assumed: measured, `?t <=> ns.rel`
/// and the one-segment `?t <=> rel` BOTH bind the name (`Ref(rel)`) at run time, neither
/// builds a `Relation` value. So typing the chain as `Relation[T]` says exactly what the
/// one-segment spelling already says in the same position — which is the parity this
/// ticket is about — and does not invent a reading for one spelling only.
///
/// SCOPE — A RULE, AND NOTHING ELSE. A chain naming a constructor, a sort, a namespace, an
/// entity, or nothing at all is left exactly as it was: measured, the OPERATION body
/// reports those five identically to the rule body (2-3 per-segment errors each), so they
/// are a SHARED, wider defect in [`check_bare_ref`]'s fall-through message and not this
/// spelling's — **WI-20260902-40KSW** owns them. Only the RULE row diverged between the two
/// positions, and it is the only one this closes.
///
/// The precedence — the WHOLE chain first, a member of a shorter prefix second — is
/// `Loader::try_qualified_rule_ref`'s, quoted: "that ordering is what makes `Queen.find`
/// the relation itself rather than member `find` of a relation `Queen`".
pub(super) fn dotted_citation_relation(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
) -> Option<Symbol> {
    let name = loader_chain_dotted_name(kb, occ)?;
    let sym = kb.try_resolve_symbol(&name)?;
    kb.cites_a_relation(sym).then_some(sym)
}

/// The NULLARY OPERATION a dotted paren-less name in a rule-body value slot calls
/// (`Box.zero`), or `None` — [`dotted_citation_relation`]'s twin for the one other kind
/// that has a value reading there. The resolver makes the call where it reduces the chain
/// as an operand (`reduce_dot_value`); this is the typer's half of the same reading, so
/// `0 = Box.zero` types as `0 = seven` does instead of walking into its segments.
pub(super) fn dotted_citation_nullary_op(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
) -> Option<Symbol> {
    let name = loader_chain_dotted_name(kb, occ)?;
    let sym = kb.try_resolve_symbol(&name)?;
    crate::kb::op_info::is_nullary_operation(kb, sym).then_some(sym)
}

/// WI-714 (proposal 052) — the APPLIED citation position: a rule NAME applied to
/// arguments (`queens(board)`, `queryTwoParams(x: 3)`). Each supplied argument
/// **binds** a COLUMN — a positional arg by column ordinal (arg `i` ↦ the i-th
/// column), a named arg by column name (`x: 3` ↦ column `x`; rule params are
/// positional-with-names) — which **subtracts** that column, narrowing `T` (§8.3
/// partial-entity expansion). A supplied argument's type must be compatible with its
/// column's type (a loud error otherwise). The remaining free columns synthesize `T`
/// exactly as the bare form does.
///
/// Binding is on the relation's dedup'd COLUMNS (its schema), not the raw head slots,
/// so it matches what the user sees typed: a nonlinear head column binds as one
/// parameter, and a ground head slot before a free var doesn't block positional
/// binding (see [`resolve_relation_arg_columns`]).
///
/// Eval re-derives the applied form via `kind_of(functor)` (its `Expr::Apply` rule
/// arm), so no `CallClass` mark is written; the SAME [`resolve_relation_arg_columns`]
/// binding plan over the SAME [`rule_head_var_slots`] enumeration drives the eval-side
/// splicing, keeping the two in lockstep.
pub(super) fn relation_reference_type_applied(
    kb: &mut KnowledgeBase,
    sym: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
    span: Option<Span>,
    occ: &Rc<NodeOccurrence>,
    site: CitationSite<'_>,
) -> Result<Value, TypeError> {
    let mut columns = relation_columns_across_clauses(kb, sym, span)?;
    // WI-20260911-5G28A S1 — the enclosing sort's parameters, opened for THIS citation and
    // seeded from its bracket / enclosing instance BEFORE the arguments bind columns, so an
    // argument meets `Wrap[T = ?t]` (a variable it can pin) or `Wrap[T = Colour]` (a type
    // it is checked against) rather than the sort's shared canonical `T`.
    let opened = open_citation_params(kb, sym, &mut columns);
    let arg_err = |kb: &KnowledgeBase, msg: String| TypeError::Other {
        site: TypeError::here(),
        span,
        context: TypeErrorContext::Rule {
            name: sym,
            field: RuleField::Whole,
        },
        expected: "supplied arguments that bind the relation's free columns".to_string(),
        actual: format!("{} (relation `{}`)", msg, kb.qualified_name_of(sym)),
    };
    // The relation's ordered, dedup'd COLUMN NAMES (a nonlinear head var is ONE
    // column). Binding operates on these, so `bound[i]` is the column the i-th supplied
    // argument (positionals first, then named) binds. A bad arity / unknown param /
    // double-bind is a loud error.
    let mut seen: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    let column_names: Vec<Symbol> = columns
        .iter()
        .map(|c| c.name)
        .filter(|n| seen.insert(*n))
        .collect();
    let named_keys: Vec<Symbol> = named_args.iter().map(|(k, _)| *k).collect();
    let bound = resolve_relation_arg_columns(&column_names, pos_args.len(), &named_keys)
        .map_err(|e| arg_err(kb, e.message(kb)))?;
    // Type-check each supplied argument against the column it binds, threading ONE
    // shared substitution so a column type constrained by an earlier argument is
    // enforced on a later one — for a relation whose head columns share a type
    // variable (`rel(?x, ?y) :- eq(?x, ?y)`, both typed at one `T`), binding `rel(5,
    // "s")` binds `T := Int64` from arg 0, then rejects `"s"` against it. `bound[i]`
    // aligns with the i-th argument, matching how `pos_results` ++ `named_results` index.
    let mut subst = Substitution::new();
    let rigid = body_rigids(kb, site.env);
    if let Some((owner, params)) = &opened {
        seed_citation_params(kb, &mut subst, occ, sym, span, *owner, params, site.env, &rigid)?;
    }
    // S2: the type each bound column takes AT THIS CITATION — its argument's — read by the
    // edge check below, which routes the relation's requirement reads over them.
    let mut bound_types: Vec<(Symbol, Value)> = Vec::with_capacity(bound.len());
    for (i, cname) in bound.iter().enumerate() {
        let col_ty = columns
            .iter()
            .find(|c| c.name == *cname)
            .map(|c| c.ty.clone())
            .expect("a bound column name is one of the relation's columns");
        let arg_res = if i < pos_results.len() {
            &pos_results[i]
        } else {
            &named_results[i - pos_results.len()]
        };
        if let Ok(arg) = arg_res {
            bound_types.push((*cname, arg.ty.clone()));
            // Resolve the column type through the accumulated σ (a correlated
            // column's var may already be pinned by an earlier argument).
            let col_ty = walk_type_deep_value(kb, &subst, &col_ty);
            // An UNCONSTRAINED column (a bare type var — a head param the body pins to
            // no concrete type, e.g. `rel(?x, ?y) :- eq(?x, ?y)`) accepts ANY argument:
            // BIND it to the argument's type (via σ) so a later correlated argument is
            // checked against the pin, and the surviving free columns narrow with it.
            // A CONCRETE column type is checked by subtyping. Binding to an
            // unconstrained column via `types_compatible` alone would spuriously reject
            // (a raw `Var::Global` is not its `TypeVar` wildcard), rejecting the valid,
            // runnable `rel(5)`.
            let ok = if let Some(vid) = resolved_var(kb, &col_ty) {
                bind_resolved(kb, &mut subst, vid, arg.ty.clone())
            } else if type_mentions_flex_var(kb, &col_ty) {
                // WI-20260911-5G28A — A COLUMN WHOSE TYPE *MENTIONS* A VARIABLE IS
                // CORRELATED TOO, and before this ticket only a column that WAS one
                // counted. `rule my_rule(?x: List[T = ?t], ?res: List[T = ?t])` ties its
                // two columns through a variable NESTED in each bound, so the arm above
                // never fires for it and `types_compatible` — a SUBTYPE test, which does
                // not bind — decided the pair. It does not merely fail to pin `?t`: a raw
                // `Var::Global` is `TypeHead::FlexVar`, which carries no dispatch tag, so
                // it is not even the `type_var` WILDCARD and the structural arms REFUSE.
                // MEASURED on b43d9670: all four driving rows — concrete argument,
                // wrong-typed argument, and both rigid ones — came back "argument binding
                // column `x` has an incompatible type", indistinguishable from a genuine
                // mismatch.
                //
                // UNIFY, and the direction is the point: σ is threaded across the
                // arguments of this citation (the loop's own shared `subst`), so a
                // concrete `List[Int64]` pins `?t := Int64` and the surviving free column
                // `res` walks out as `List[Int64]`; a RIGID `List[T = op.x.T]` pins `?t`
                // to that neutral, so `-> List[T = x.T]` is accepted and `-> List[T =
                // y.T]` refused by ordinary σ-equality of one projection. No receiver
                // re-keying is needed because in a rule the tie IS a variable, not a path.
                //
                // A CONCRETE column keeps `types_compatible` — SUBTYPING is the right
                // relation where nothing is to be pinned, and pinning there would refuse
                // an argument whose type is a legitimate SUBTYPE of the column's.
                //
                // THE SAME READER THE RESOLVER USES, not a second one. `pin_type_vars` is
                // where "match a determined type against a variable-bearing bound, binding
                // what stands opposite each variable" is decided, and the typer's citation
                // and the resolver's goal must not drift about what a bound MEANS. It also
                // brings the subtype FALLBACK with it: `unify_types` alone (this arm's
                // first cut) refused an argument whose type is a legitimate subtype of the
                // column's, since unification is not subsumption — found by `/code-review`.
                pin_type_vars(kb, &mut subst, &arg.ty, &col_ty)
            } else {
                types_compatible(kb, &mut subst, &arg.ty, &col_ty)
            };
            if !ok {
                return Err(arg_err(
                    kb,
                    format!(
                        "argument binding column `{}` has an incompatible type",
                        kb.local_name_of(*cname)
                    ),
                ));
            }
        }
    }
    // Subtract the bound columns (BY NAME — every slot of a nonlinear column goes): the
    // remaining free columns narrow `T`, resolved through σ so a column correlated with
    // a bound one carries its now-pinned type (`rel(5)` → `Relation[Int64]`, not an
    // unresolved var).
    let column_types: Vec<(Symbol, Value)> =
        columns.iter().map(|c| (c.name, c.ty.clone())).collect();
    let free: Vec<ClauseColumn> = columns
        .into_iter()
        .filter(|c| !bound.contains(&c.name))
        .map(|mut c| {
            c.ty = walk_type_deep_value(kb, &subst, &c.ty);
            c
        })
        .collect();
    let ty = relation_type_from_columns(kb, sym, free, occ.span, span)?;
    let ty = settle_citation_type(kb, &rigid, &mut subst, sym, span, opened, site.expected, ty)?;
    queue_citation_routes(kb, site.env, occ, sym, column_types, bound_types, subst);
    Ok(ty)
}

/// WI-20260911-5G28A S2 — a citation's EDGE CHECK, captured at the citation and run later.
///
/// LATER BECAUSE THE READS DO NOT EXIST YET. An operation body is typed before any rule
/// body (`type_check_sorts`: the sort loop and the free operations, then
/// `type_rule_bodies`), and a rule's `?d = require[X]` becomes a routable read —
/// `find_dictionary(spec, op, witness…, out: ?d)` — only when
/// `record_find_dictionary_grounding` picks its witness, which needs the rule bodies
/// typed. MEASURED: routed at the citation, `cmp`'s read was still the one-argument
/// `find_dictionary(WeakOrd[T], out: ?d)` and nothing could say which column carries
/// `WeakOrd`. So everything the check reads AT the citation is captured here — the column
/// types, each bound column's argument type, the citation's σ, and the caller's frame chain
/// and rigids — and [`settle_citation_routes`] runs it once the sweep has rewritten every
/// read, stamping the result on the very occurrence captured here (a citation's node is
/// handed back unchanged by its typer arm, so the stored body holds it).
#[derive(Clone)]
pub(crate) struct PendingCitationRoutes {
    occ: Rc<NodeOccurrence>,
    relation: Symbol,
    column_types: Vec<(Symbol, Value)>,
    bound_types: Vec<(Symbol, Value)>,
    subst: Substitution,
    chain: DictChain,
    param_rigids: Vec<(VarId, TermId)>,
}

fn queue_citation_routes(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    relation: Symbol,
    column_types: Vec<(Symbol, Value)>,
    bound_types: Vec<(Symbol, Value)>,
    subst: Substitution,
) {
    kb.pending_citation_routes.push(PendingCitationRoutes {
        occ: Rc::clone(occ),
        relation,
        column_types,
        bound_types,
        subst,
        chain: env.enclosing_frame_chain().clone(),
        param_rigids: env.param_rigids().to_vec(),
    });
}

/// WI-20260911-5G28A S2 — run every queued citation edge check ([`PendingCitationRoutes`])
/// and stamp the routes it finds. AFTER `record_find_dictionary_grounding`, which is what
/// makes the reads routable; drains the queue, so a later pass cannot see a stale entry.
pub(super) fn settle_citation_routes(kb: &mut KnowledgeBase) {
    for pending in std::mem::take(&mut kb.pending_citation_routes) {
        let routes = citation_requirement_routes(
            kb,
            &pending.chain,
            &pending.param_rigids,
            pending.relation,
            &pending.column_types,
            &pending.bound_types,
            &pending.subst,
        );
        if !routes.is_empty() {
            pending.occ.set_op_dicts(routes);
        }
    }
}

/// WI-20260911-5G28A S2 — the cited relation's IMPLICIT ARGUMENTS at this citation: one
/// route per requirement READ of its clauses (clause after clause, read after read — the
/// layout [`requirement_read_counts`] indexes), each an IR term the caller's frame
/// evaluates to the dictionary that read is to receive, or `None` where this edge has none
/// to give and the read derives its own at run time, exactly as it did before.
///
/// WHY, measured: `viaRule[A](x: A, y: A) requires WeakOrd[T = A] = cmp(x, y).head.c` over
/// `rule cmp(?a, ?b, ?c) :- ?d = require[WeakOrd[T]], WeakOrd.compare(?a, ?b, ?c)`,
/// called `[WeakOrd = Descending]`, answered `Int64`'s own `-1` where `Descending` gives
/// `4`: the citation built its query from the head alone, the caller's dictionary stayed
/// in the caller's frame, and the clause re-derived at the value's type
/// (`wi_5g28a_rule_dictionary_test`). A rule body cannot choose a provider itself, so the
/// caller's dictionary is the only route its choice has into the rule.
///
/// EACH READ IS ROUTED THE WAY THE RUNTIME WOULD DERIVE IT, from types instead of values:
/// its witness arguments are typed from the citation's columns — an argument's own type
/// where one binds the column, the column's σ-resolved type otherwise, a fresh variable for
/// a witness that is no column at all — then [`witness_sort_goal`] / [`anchor_sort_goal`]
/// build the goal the resolver's `fetch_dictionary` builds, and [`resolve`] answers it
/// against the CALLER's frame chain under the edge's σ (so a rigid `A` meets the caller's
/// `requires WeakOrd[T = A]` through `param_rigids`, WI-821's σ-class agreement). The tree
/// becomes IR by [`emit_tree_as_projection`], the emitter an operation call's own routes use:
/// `FromScope` a read of the caller's slot, a construction a `Dictionary(…)`. A resolution
/// that cannot fill a slot routes nothing — it fails (WI-20260925-4ZZKZ), where it used to
/// hand back a tree with a marker slot that had to be filtered out here.
fn citation_requirement_routes(
    kb: &mut KnowledgeBase,
    chain: &DictChain,
    param_rigids: &[(VarId, TermId)],
    sym: Symbol,
    column_types: &[(Symbol, Value)],
    bound_types: &[(Symbol, Value)],
    subst: &Substitution,
) -> SmallVec<[Option<TermId>; 2]> {
    let Some(fd) = find_dictionary_symbol(kb) else {
        return SmallVec::new();
    };
    let qn = kb.qualified_name_of(sym).to_string();
    let rids = kb.rule_ids_by_qn(&qn);
    let mut routes: SmallVec<[Option<TermId>; 2]> = SmallVec::new();
    let mut any = false;
    for rid in rids {
        let slots = rule_head_var_slots(kb, rid);
        let body: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
        for node in &body {
            if requirement_read_out(kb, fd, node).is_none() {
                continue;
            }
            let Some(Expr::Apply {
                pos_args,
                named_args,
                ..
            }) = node.as_expr()
            else {
                unreachable!("a requirement read is an application");
            };
            let route = route_requirement_read(
                kb,
                chain,
                param_rigids,
                pos_args,
                named_args,
                &slots,
                column_types,
                bound_types,
                subst,
            );
            any |= route.is_some();
            routes.push(route);
        }
    }
    if any {
        routes
    } else {
        SmallVec::new()
    }
}

/// One read's route for [`citation_requirement_routes`] — `pos_args` is the read's
/// `[spec, op, witness…]`, and `named_args` carries a SLOT read's `slot: k`.
#[allow(clippy::too_many_arguments)]
fn route_requirement_read(
    kb: &mut KnowledgeBase,
    chain: &DictChain,
    param_rigids: &[(VarId, TermId)],
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    slots: &[(SlotKey, Symbol, u32)],
    column_types: &[(Symbol, Value)],
    bound_types: &[(Symbol, Value)],
    subst: &Substitution,
) -> Option<TermId> {
    let spec_sort = occ_head_symbol(&pos_args[0])?;
    let op_functor = occ_head_symbol(&pos_args[1])?;
    let bracket = requirement_bracket(kb, &Value::Node(Rc::clone(&pos_args[0])));
    let mut arg_types: Vec<Value> = Vec::with_capacity(pos_args.len().saturating_sub(2));
    for witness in &pos_args[2..] {
        let column = match witness.as_expr() {
            Some(Expr::Var(Var::DeBruijn(d))) => {
                slots.iter().find(|(_, _, di)| di == d).map(|(_, name, _)| *name)
            }
            _ => None,
        };
        let ty = column.and_then(|name| {
            bound_types
                .iter()
                .find(|(n, _)| *n == name)
                .map(|(_, t)| t.clone())
                .or_else(|| {
                    column_types
                        .iter()
                        .find(|(n, _)| *n == name)
                        .map(|(_, t)| walk_type_deep_value(kb, subst, t))
                })
        });
        let ty = match ty {
            Some(t) => t,
            None => {
                let name = kb.intern("witness");
                let v = kb.fresh_var(name);
                Value::term(kb.alloc(Term::Var(Var::Global(v))))
            }
        };
        arg_types.push(ty);
    }
    // WI-20260925-P7VP4 — a SLOT read is routed from its callee's own chain entry.
    if let Some(k) = slot_read_index(kb, named_args) {
        return op_slot_route(kb, chain, param_rigids, subst, op_functor, k, &arg_types);
    }
    // WI-20260925-SHED7 — a `SortDomain` read is routed from the TYPE, never by a search.
    if is_sort_domain_spec(kb, spec_sort) {
        let ty = arg_types.first()?.clone();
        let syms = ProjectionSyms::resolve(kb)?;
        return sort_domain_route(kb, chain, param_rigids, subst, spec_sort, &ty, &syms);
    }
    let built = if is_anchor_form(kb, spec_sort, op_functor) {
        anchor_sort_goal(kb, spec_sort, &arg_types, &bracket.written)
    } else {
        witness_sort_goal(kb, spec_sort, op_functor, &arg_types, &bracket.written)
    }?;
    resolve_route(kb, chain, param_rigids, subst, &built.goal)
}

/// The tail every route shares: resolve `goal` against the citing caller's frame `chain` —
/// a rigid element meeting the caller's own `requires` through `param_rigids` — and emit
/// the tree as the projection the citation passes. `None` routes nothing.
fn resolve_route(
    kb: &mut KnowledgeBase,
    chain: &DictChain,
    param_rigids: &[(VarId, TermId)],
    subst: &Substitution,
    goal: &SortGoal,
) -> Option<TermId> {
    let sigma = SigmaCtx {
        subst,
        param_rigids,
    };
    let scope = ResolutionScope {
        available_requires: chain.entries(),
        sigma: Some(&sigma),
        selected: &[],
        sub_goal_requires: &[],
    };
    let ResolutionResult::Resolved(tree) = resolve(kb, goal, &scope) else {
        return None;
    };
    let syms = ProjectionSyms::resolve(kb)?;
    emit_tree_as_projection(kb, chain, &tree, &syms)
}

/// WI-20260925-P7VP4 — the slot index `k` of a SLOT read (`slot: k`), or `None` for any
/// other read.
fn slot_read_index(kb: &KnowledgeBase, named_args: &[(Symbol, Rc<NodeOccurrence>)]) -> Option<usize> {
    let (_, v) = named_args
        .iter()
        .find(|(k, _)| kb.local_name_of(*k) == REQUIREMENT_SLOT_LABEL)?;
    match v.as_expr() {
        Some(Expr::Const(Literal::Int(k))) => usize::try_from(*k).ok(),
        _ => None,
    }
}

/// WI-20260925-P7VP4 — the route of a SLOT read: slot `k` of `op`'s dictionary chain, at the
/// argument types this citation gives the call — the entry the bridge would resolve from the
/// VALUES ([`resolve_bridge_requirements`]), resolved here from the TYPES against the
/// caller's frame chain, so a rigid element meets the caller's own `requires` through
/// `param_rigids` exactly as a written read's does.
///
/// `None` routes nothing, and the slot is then derived from the values as it always was: an
/// entry written at a PROJECTION (δ needs the receiver's value, which a type does not carry)
/// or one these types leave open.
fn op_slot_route(
    kb: &mut KnowledgeBase,
    chain: &DictChain,
    param_rigids: &[(VarId, TermId)],
    subst: &Substitution,
    op: Symbol,
    k: usize,
    arg_types: &[Value],
) -> Option<TermId> {
    let rec = crate::kb::op_info::lookup_operation_info(kb, op)?;
    let entry = op_dict_entries(kb, op).iter().nth(k)?.clone();
    if value_contains_projection(kb, &entry.spec) {
        return None;
    }
    // THE CALLEE'S PARAMETERS ARE WHAT GET PINNED, so each is unified FIRST: a citation's
    // argument type may itself be a variable — the caller's own rigid `A`, which is what
    // meets the caller's `requires` below through `param_rigids` — and a variable-variable
    // unification binds the left one. Arguments first bound the CALLER's variable to the
    // callee's, and the goal named a type the caller holds no entry for (MEASURED: the
    // route came back empty exactly for the rigid citation, and filled for an `Int64` one).
    //
    // An argument type that does not UNIFY with its parameter pins nothing there when it is a
    // SUBTYPE of it — `circle()` for `s: Shape`, which the citation accepted (above:
    // "unification is not subsumption") — and the other parameters still pin the slot; the
    // failed trial's partial bindings are dropped with it. Refusing the whole route there sent
    // the call back to the value's own dictionary where the caller had chosen one.
    let mut pins = Substitution::new();
    for ((_, pty), aty) in rec.params.iter().zip(arg_types) {
        let mut trial = pins.clone();
        if unify_types(kb, &mut trial, pty, aty) {
            pins = trial;
        }
    }
    // THEN EVERY ARGUMENT MUST CONFORM TO ITS PARAMETER AS PINNED — asked once all parameters
    // have pinned, against the pinned type and not the written one (WI-20260925-PRVA2 (e)).
    // Against the WRITTEN `y: A` the subtype test compared `Circle` with the bare parameter and
    // refused: `cmp2[A](x: A, y: A)` cited at `(Shape, Circle)` routed NOTHING, so the slot was
    // derived from the values (`Circle`'s own) where the typer instantiates `A = Shape` for the
    // same call (`Shape`'s). And a pin is not a verdict: `unify_types` answers a mismatch of
    // two sorts with a ONE-WAY subtype test, so at `(Circle, Shape)` it pinned `A = Circle` and
    // accepted the `Shape` beside it — a route for a type one argument is not. That order is
    // refused at load today (the citation's column typing takes `A` from the first argument,
    // and `Shape` is no `Circle`), and it is a route nothing here may produce either way.
    //
    // THE TYPER'S OWN QUESTION, `validate_arg_against_param`, and not a bare
    // `types_compatible`: it walks BOTH sides through the pins — an argument's type is itself a
    // variable where the clause binds it only through another parameter, a body variable's
    // witness pinned to the caller's rigid `A` by the column beside it — and it accepts the
    // conversions an operation-body argument gets (WI-408's some-coercion, the reflect-`Term`
    // escape, a provider-admissible carrier). With the bare relation, `f[A](x: Option[T = A],
    // y: A)` given a bare `Shape` for `x` through a typed column routed nothing where the typer
    // wraps it, and the slot fell back to the value's dictionary. An argument the typer would
    // refuse routes nothing.
    for ((param, pty), aty) in rec.params.iter().zip(arg_types) {
        let mut sigma = pins.clone();
        match validate_arg_against_param(
            kb,
            &mut sigma,
            aty,
            pty,
            None,
            TypeErrorContext::OperationArgument {
                op_name: op,
                param: *param,
            },
            None,
        ) {
            ArgValidation::Ok | ArgValidation::WrapSome { .. } => {}
            ArgValidation::Fail(_) => return None,
        }
    }
    // NOT `substitute_spec_via_subst`, which declines a parameter bound to another TYPE
    // VARIABLE ("the enclosing sort's own `requires` carries it"). Here that variable is the
    // point: it is the citing caller's rigid, and `resolve` below meets the caller's own
    // entry at it through `param_rigids`. Each parameter is WALKED through the pins to its
    // end: a parameter bound to a witness variable a later parameter pinned reads as that
    // pin, not as the variable (a one-step lookup made the route depend on parameter order).
    let spec = rewrite_spec_value(kb, &entry.spec, &|kb, t| {
        rewrite_term_leaves(kb, t, &|kb, t| {
            let param = ref_or_nullary_name(kb.get_term(t))?;
            let var = kb.alloc(Term::Var(Var::Global(type_param_global_var(kb, param)?)));
            match walk_type_deep_value(kb, &pins, &Value::term(var)) {
                Value::Term { id, .. } if id != var => Some(id),
                _ => None,
            }
        })
    });
    let goal = goal_from_requires_entry(
        kb,
        &RequiresEntry {
            spec,
            ..entry
        },
    )?;
    resolve_route(kb, chain, param_rigids, subst, &goal)
}

/// WI-20260925-SHED7 (proposal 060 §2.3) — the route of a `SortDomain` read at the type
/// `ty`, built from the `SortDomain` table: a sort has ONE domain, so nothing is chosen, and
/// a search among providers is exactly what `SortDomain[?]` must never get (its wildcard
/// matches every candidate — X9PB4). The construction is laid out as the typer lays every
/// `SortDomain` dictionary out (`sort_domain_sub_offset`): the slots no `fill` reads — the
/// `Fillable` conversion, the sort's sort-level `requires` — hold an empty bundle, and each
/// condition holds the route of the argument at it. So a citation needs no provision row.
///
/// A TYPE WITH NO ENTRY — a caller's RIGID `X` — is the caller's own evidence, resolved
/// against its frame chain: the one way a rigid's domain reaches a clause (§7.3). `None`
/// where there is none; the read then builds its own from the value at run time.
fn sort_domain_route(
    kb: &mut KnowledgeBase,
    chain: &DictChain,
    param_rigids: &[(VarId, TermId)],
    subst: &Substitution,
    spec: Symbol,
    ty: &Value,
    syms: &ProjectionSyms,
) -> Option<TermId> {
    let ty = walk_type_deep_value(kb, subst, ty);
    let head = match ty.head(kb) {
        ViewHead::Functor {
            functor: Some(f), ..
        } => Some(f),
        ViewHead::Ident(s) => Some(s),
        _ => None,
    };
    // A TYPE ALIAS has its target's domain (`dealias_type`); a bare name is the only form one
    // takes.
    if let Some(h) = head.filter(|&h| kb.sort_domain(h).is_none()) {
        let bare = kb.alloc(Term::Ref(h));
        let target = dealias_type(kb, bare);
        if target != bare {
            return sort_domain_route(kb, chain, param_rigids, subst, spec, &Value::term(target), syms);
        }
    }
    if let Some((head, entry)) = head.and_then(|h| kb.sort_domain(h).cloned().map(|e| (h, e))) {
        let head = kb.canonical_sort_sym(head);
        let mut subs: Vec<TermId> = (0..entry.sub_offset)
            .map(|_| build_dictionary_term(kb, syms, head, &[]))
            .collect();
        for &j in &entry.conditions {
            let arg = crate::kb::fill_derive::condition_arg(kb, &ty, &entry.params[j])?.to_value();
            subs.push(sort_domain_route(kb, chain, param_rigids, subst, spec, &arg, syms)?);
        }
        return Some(build_dictionary_term(kb, syms, head, &subs));
    }
    let built = anchor_sort_goal(kb, spec, &[ty], &[])?;
    resolve_route(kb, chain, param_rigids, subst, &built.goal)
}

/// WI-714 — the free-variable columns of a relation, merged across its clauses:
/// compound-var heads rejected loudly, each column's type the **lub** of that SLOT
/// across every clause (aligned by slot IDENTITY, not free-column index), and a
/// heterogeneous free-slot interface rejected loudly. Shared by the bare
/// ([`relation_reference_type`]) and applied ([`relation_reference_type_applied`])
/// citation positions; before-dedup so the applied form can subtract bound slots.
fn relation_columns_across_clauses(
    kb: &mut KnowledgeBase,
    sym: Symbol,
    span: Option<Span>,
) -> Result<Vec<ClauseColumn>, TypeError> {
    let qn = kb.qualified_name_of(sym).to_string();
    let rids = kb.rule_ids_by_qn(&qn);
    let first = *rids.first().ok_or_else(|| {
        // WI-20260911-WT8WG — a derived `<Sort>.domain` whose clause was NOT derived
        // says WHY, instead of reporting the name as unresolved.
        domain_value_face_refusal(kb, sym, span)
            .unwrap_or(TypeError::UnresolvedName { span, name: sym })
    })?;
    let head_err = |kb: &KnowledgeBase, msg: &str| TypeError::Other {
        site: TypeError::here(),
        span,
        context: TypeErrorContext::Rule {
            name: sym,
            field: RuleField::Whole,
        },
        expected: "a relation with a uniform, simple-variable head interface".to_string(),
        actual: format!("{} (rule `{}`)", msg, kb.qualified_name_of(sym)),
    };
    // WI-714: a COMPOUND head argument that mentions a variable (`some(?x)`) cannot
    // ride verbatim into a runnable query goal (its raw DeBruijn unifies
    // reflexively-only → zero solutions) and its column semantics are unsettled;
    // reject it loudly (per "loud error over silent skip") across every clause. A
    // fully-ground compound (`pair(1, 2)`) is a legitimate filter and passes.
    for &rid in &rids {
        if clause_head_has_compound_var(kb, rid) {
            return Err(head_err(
                kb,
                "a compound head argument (e.g. `some(?x)`) is not yet supported",
            ));
        }
    }
    // WI-714: every clause must share ONE head functor. The relation's runnable query
    // is built from a SINGLE head shape — `functor(?cols)` at the first clause's
    // structure (`build_relation_value`) — and SLD unions the clauses THROUGH that
    // shared functor. Clauses grouped under one LABEL may carry DIFFERENT head
    // functors (`rule L: foo(?x) …` / `rule L: bar(?y) …`); the column fold below
    // would then silently union them in the SCHEMA while eval runs only the first
    // functor's clauses, dropping the rest — a typer/eval divergence. Reject loudly
    // (per "loud error over silent skip"). Keys on the head FUNCTOR, not the label, so
    // an ordinary homogeneous multi-clause relation (and every unlabeled rule, whose
    // clauses share a functor by construction) passes.
    let first_functor = kb.fact_head_term(first).and_then(|t| kb.head_functor(t));
    for &rid in rids.iter().skip(1) {
        if kb.fact_head_term(rid).and_then(|t| kb.head_functor(t)) != first_functor {
            return Err(head_err(
                kb,
                "clauses with differing head functors (one label over multiple head \
                 predicates) are not yet supported",
            ));
        }
    }
    // Columns come from the FIRST clause (the goal is built at its structure); each
    // column's TYPE is the lub of that SLOT across every clause. Alignment is by
    // slot IDENTITY (`SlotKey`), not free-column index — a clause pinning a
    // different slot to a constant shifts the free-column order, so index-alignment
    // would lub unrelated columns. A clause whose free-slot SET differs (a
    // heterogeneous interface) is rejected loudly rather than silently dropped
    // (which would under-approximate the schema — unsound).
    let mut columns = relation_clause_columns(kb, first);
    for &rid in rids.iter().skip(1) {
        let other = relation_clause_columns(kb, rid);
        if !slot_keys_match(&columns, &other) {
            return Err(head_err(
                kb,
                "clauses with differing free-variable slots are not yet supported",
            ));
        }
        for oc in other {
            let Some(c) = columns.iter_mut().find(|c| c.slot == oc.slot) else {
                continue;
            };
            match join_column_types(kb, c.ty.clone(), oc.ty) {
                Some(j) => c.ty = j,
                None => {
                    let cname = c.name;
                    return Err(TypeError::Other {
                        site: TypeError::here(),
                        span,
                        context: TypeErrorContext::Rule {
                            name: sym,
                            field: RuleField::Whole,
                        },
                        expected: "a common column type across relation clauses".to_string(),
                        actual: format!("disjoint types for column `{}`", kb.local_name_of(cname)),
                    });
                }
            }
        }
    }
    Ok(columns)
}

/// WI-714 — the lub of ONE column's type across two clauses, where a clause that
/// leaves the column UNCONSTRAINED contributes no information.
///
/// A clause types a head parameter only where a body goal constrains it (an
/// operation parameter, an entity field). A parameter whose only occurrence is a
/// RULE subgoal gets no type at all — rule subgoals do not type their arguments —
/// so [`relation_clause_columns`] mints it as a fresh raw `Var::Global`. That is the
/// ABSENCE of a type, not a rival type, and it must not veto the lub. [`join_types`]
/// already returns the other side for its own `TypeVar` inference wildcard, but does
/// not recognize a raw `Var::Global` (whose type-dispatch tag is `None`), so it would
/// climb the lattice, find the column incomparable, and report it disjoint.
/// `resolved_var` is the same seam [`relation_reference_type_applied`] uses to spot an
/// unconstrained column (there: accept the argument and narrow to its type).
///
/// This is what makes a RECURSIVE relation citable by name. In
/// `anc(?c, ?e) :- parent(of: ?c, is: ?m), anc(?m, ?e)` the column `e` is typed only
/// by the rule's OWN recursive self-reference, so it is unconstrained in that clause
/// and takes String from the base clause — the fixpoint answer, reached without an
/// assume-then-check iteration precisely BECAUSE a self-reference contributes nothing
/// to begin with. It covers mutual recursion (and a plain rule subgoal) for the same
/// reason, neither of which a self-reference-specific rule would catch.
///
/// Returns the informative side WITHOUT binding, mirroring `join_types`' own wildcard
/// arm, which likewise returns the other side rather than unifying: the columns are
/// lubbed independently, slot by slot, so nothing here should pin one column's type
/// from another's.
///
/// This recognizes ONE spelling of "unconstrained", the raw `Var::Global`, and that is
/// deliberate — WI-741 retired the second. A column left open as an uninstantiated
/// SPEC TYPE PARAMETER (`rule r(?x) :- eq(?x, "root")` typed `?x` at
/// `anthill.prelude.PartialEq.T`, a `Term::Ref` to the parameter symbol) used to reach
/// `join_types` and be reported disjoint against a concrete column, though both
/// clauses plainly meant `String`. [`relation_clause_columns`] now normalizes it into
/// the raw `Var::Global` at the producer, so do NOT add a second recognizer here: a
/// parameter arriving at this function again means the producer stopped normalizing,
/// and the lub is the wrong place to learn it.
fn join_column_types(kb: &mut KnowledgeBase, a: Value, b: Value) -> Option<Value> {
    if resolved_var(kb, &a).is_some() {
        return Some(b);
    }
    if resolved_var(kb, &b).is_some() {
        return Some(a);
    }
    join_types(kb, a, b)
}

/// WI-714 — assemble the `Relation[T = schema, E = {Error}]` value type from a final
/// (post-subtraction) column list: dedup by name (a nonlinear head var is ONE
/// column), `Unit` for zero columns, else the named tuple.
/// Shared by both citation positions.
fn relation_type_from_columns(
    kb: &mut KnowledgeBase,
    sym: Symbol,
    columns: Vec<ClauseColumn>,
    sp: crate::span::SourceSpan,
    span: Option<Span>,
) -> Result<Value, TypeError> {
    // Dedup by column NAME: a nonlinear head variable (`twin(?n, ?n)`) fills two
    // slots but is ONE logical column (same var ⟹ same name) — keep the first.
    let mut seen_names: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
    let columns: Vec<(Symbol, Value)> = columns
        .into_iter()
        .filter(|c| seen_names.insert(c.name))
        .map(|c| (c.name, c.ty))
        .collect();
    let relation_sym = kb
        .try_resolve_symbol("anthill.prelude.Relation")
        .ok_or(TypeError::UnresolvedName { span, name: sym })?;
    // The EFFECT-ROW param `E` is pinned to `{Error}` — running a relation is not pure
    // (search can raise, 026.1 `execute effects Error`), and the `provides LogicalStream[T,
    // E]` edge threads this row so every inherited Stream op types at `{Error}`, not `{}`
    // (Typing §3). Pinned HERE (at the value site), not on the sort — a concrete override on
    // the abstract sort op would widen it (WI-347); the sort threads `E` abstractly.
    let error_row = error_effect_row(kb);
    Ok(assemble_relation_type(
        kb,
        relation_sym,
        &columns,
        error_row,
        sp,
    ))
}

/// WI-714 — the canonical `{Error}` access-effect row (a `present(Error)` effects row), the
/// floor every relation value carries (running a query can raise, 026.1 `execute effects
/// Error`). `None` only if `anthill.prelude.Error` is unresolvable (prelude not loaded).
fn error_effect_row(kb: &mut KnowledgeBase) -> Option<Value> {
    kb.try_resolve_symbol("anthill.prelude.Error").map(|es| {
        let label = kb.make_sort_ref(es);
        Value::term(kb.build_canonical_effects_rows(&[label]))
    })
}

/// WI-714 — assemble `Relation[T = <schema from `columns`>, E = <effect_row>]`. The schema is
/// `Unit` for no columns, else the named tuple keyed by the column symbols in the GIVEN order
/// (NOT re-sorted, so the type's field order matches the runtime materialized row). `effect_row` binds the sort's effect-row param
/// (`sort_param_is_effect_row`) when `Some` — `{Error}` for a fresh relation reference
/// ([`relation_type_from_columns`]). `make_parameterized_type`'s producer flip makes the base
/// sort the functor; `parameterized_value` keeps a ground schema hash-consed and a
/// denoted-bearing one occurrence-carried.
///
/// WI-732: a PROJECTION no longer comes through here. It used to, to re-pin
/// `Relation[T = <projected>, E = <receiver's, FLOORED to {Error} if absent>]` as a typer
/// stamp; `project_run`'s signature now states `E = r.E` directly, as `where_run` /
/// `join_run` do, so the receiver's row THREADS instead of being re-pinned. That floor was
/// load-bearing only for a receiver whose type omits `E` — an under-specified relation type,
/// which already fails the same way when consumed without a projection.
pub(super) fn assemble_relation_type(
    kb: &mut KnowledgeBase,
    relation_sym: Symbol,
    columns: &[(Symbol, Value)],
    effect_row: Option<Value>,
    sp: crate::span::SourceSpan,
) -> Value {
    let schema = relation_schema_type(kb, columns, sp);
    let params = sort_type_params_as_pairs(kb, relation_sym);
    let mut bindings: Vec<(Symbol, Value)> = Vec::with_capacity(params.len());
    let mut schema = Some(schema);
    for (psym, _) in params.iter() {
        let short = short_name_of(kb.local_name_of(*psym)).to_string();
        if sort_param_is_effect_row(kb, relation_sym, &short) {
            if let Some(e) = &effect_row {
                bindings.push((*psym, e.clone()));
            }
        } else if let Some(s) = schema.take() {
            // The first value parameter is the schema `T`.
            bindings.push((*psym, s));
        }
    }
    let base = kb.make_sort_ref(relation_sym);
    parameterized_value(kb, base, &bindings, sp, None)
}

/// WI-731 — what a relation schema's columns ARE, as the parenthetical every "no such
/// column" refusal appends. ONE owner, because there are now two such refusals — the
/// projection's ([`projection_columns`]) and the rename's ([`rename_schema_type`]) — and the
/// EMPTY case is the half that is easy to get wrong twice.
///
/// A ZERO-COLUMN schema gets its own sentence rather than an empty list. It is a reachable
/// operand since WI-20260818-YQB1Y — `Unit` now means zero columns and ONLY zero columns, so
/// a membership relation lands in both refusals for EVERY member — and "(its columns are: )"
/// reads as a rendering bug rather than as the fact that there is nothing there. That was
/// fixed at the projection site and left standing at the rename site one function over, which
/// is why the wording lives here now instead of at either.
fn schema_columns_tail(kb: &KnowledgeBase, fields: &[(Symbol, Value)]) -> String {
    if fields.is_empty() {
        return "it has NONE — a membership relation's schema is `Unit`, which is zero \
                columns, so there is nothing there to name"
            .to_string();
    }
    format!(
        "its columns are: {}",
        fields
            .iter()
            .map(|(f, _)| short_name_of(kb.local_name_of(*f)).to_string())
            .collect::<Vec<_>>()
            .join(", ")
    )
}

/// WI-714 (proposal 052) — PROJECTION `r.(f1, f2)`. The projected `Relation[T', E]`
/// TYPE for selecting `projections` (an ordered `(result-key, source-column-short-name)`
/// map — bare `r.(f)` auto-labels result = source, rename `r.(a: f)` differs) from a
/// relation whose type is `recv_ty`. The receiver's schema `T` (a named tuple, or `Unit`
/// for a membership relation, which has no column to select) supplies each kept column's
/// TYPE; the projected schema is `Unit` for no kept column, else the named tuple keyed by
/// the RESULT keys. The
/// access-effect row `E` threads through unchanged (projection runs no extra search).
/// `None` when the receiver is not a Relation, its schema is not a named tuple, or a
/// source names no column — the caller then falls through (dot dispatch →
/// `DotDispatchNoMatch`; the tuple pre-check → ordinary tuple typing).
fn projection_columns(
    kb: &KnowledgeBase,
    schema: &Value,
    projections: &[(Symbol, String)],
) -> Result<Vec<(Symbol, Value)>, String> {
    // WI-1128: read by the shared [`schema_fields`], phrased here.
    //
    // WI-20260818-YQB1Y — REACHED FROM BOTH SURFACES NOW. It used to be reachable only from a
    // WRITTEN `Project[T, Keep]`, because on the dot surface `r.(f)` 1-collapsed at convert
    // time to `r.f` (§6.8) and a one-column receiver never built a projection at all — so
    // `ages.(age)` fell through to dot dispatch and reported "no such member"
    // (WI-20260818-7X7NK). `.( )` no longer collapses, so a single-member projection over a
    // one-column relation is an ordinary projection and selects `age` by name.
    //
    // WI-20260818-7X7NK — AND THE FAILING DIRECTION REACHES THE DOT SURFACE TOO. The `Err`
    // below used to be dot-surface-unreachable for a different reason than the collapse: a
    // member that names no column does not type as a dot access either, so the FIELD failed
    // one level down and its "no such member" short-circuited the tuple before any projection
    // was recognized. [`projection_column_errors`] calls this ahead of that
    // short-circuit, so the sentence below is what the author of `r.(nosuch)` reads.
    let fields = schema_fields(kb, schema).ok_or_else(|| {
        format!(
            "`Project` cannot select from operand `T`: {}",
            not_a_schema_tail(kb, schema)
        )
    })?;
    // Resolve each source column against the schema by SHORT name — the schema field
    // symbol IS the runtime column symbol (both from `rule_head_var_slots`), so this is
    // the schema's own field lookup (WI-638 mode 3), not a cross-scope compare (WI-672).
    let mut proj_columns: Vec<(Symbol, Value)> = Vec::with_capacity(projections.len());
    for (result_key, source) in projections {
        let col_ty = fields
            .iter()
            .find_map(|(f, t)| (short_name_of(kb.local_name_of(*f)) == *source).then(|| t.clone()))
            .ok_or_else(|| {
                format!(
                    "the projection selects column `{source}`, which the relation's schema \
                     does not have ({})",
                    schema_columns_tail(kb, &fields)
                )
            })?;
        proj_columns.push((*result_key, col_ty));
    }
    Ok(proj_columns)
}

/// WI-732 — the projection's KEEP SPEC, read back out of TYPE position. `Keep` is a
/// named-tuple TYPE whose field name is each RESULT key and whose component is a `denoted`
/// carrying the SOURCE column's name — `Keep = (person: "name", years: "age")` for
/// `r.(person: name, years: age)`. A named tuple is the natural carrier because the keep spec
/// IS a map from result key to source name, and there are no singleton types (WI-759), so the
/// source name reaches type position only as a denoted.
fn keep_spec_projections(
    kb: &KnowledgeBase,
    keep: &Value,
) -> Result<Vec<(Symbol, String)>, String> {
    let TypeExtractor::NamedTuple(fields) = extract_type(kb, keep) else {
        return Err(
            "`Project` operand `Keep` must be a named-tuple type mapping each result \
                    key to its source column name (`Keep = (person: \"name\")`)"
                .to_string(),
        );
    };
    let projections: Vec<(Symbol, String)> = fields
        .iter()
        .map(|(result_key, source)| {
            denoted_name(kb, source)
                .map(|s| (*result_key, s))
                .ok_or_else(|| {
                    format!(
                    "`Project` keep-spec entry `{}` must name its source column as a string in \
                     type position (a `denoted`), which is how a compile-time name reaches a \
                     type argument",
                    short_name_of(kb.local_name_of(*result_key))
                )
                })
        })
        .collect::<Result<_, _>>()?;
    // WI-763 — a duplicate RESULT key. The dot surface rejects this at parse
    // (`validate_projection_labels` on `r.(a: f1, a: f2)`), but a WRITTEN `Keep` does not pass
    // through that check — so the two keys would silently reach `relation_schema_type` and build a
    // schema with two `a` columns, which no field lookup can then answer unambiguously.
    // Checked here so the invariant holds for BOTH surfaces of the same spec rather than only
    // the one that happens to route through the parser.
    // WI-805 added the same rule to the tuple TYPE and the tuple LITERAL
    // (`check_label_unique`), which is where this comment used to say "a named-tuple
    // TYPE carries duplicate field names without complaint". That is now true only of a
    // DERIVED schema — one this code builds — which is exactly what this check covers, and
    // `concat_named_tuple_types` covers for the merging case.
    // INSTRUMENTED, not assumed: a `panic!` on this branch was run against the full workspace
    // suite (3354 tests) and NEVER FIRED. A written `Keep` is a tuple type and so is refused a
    // stage earlier now; a derived one arrives from `concat_named_tuple_types` (which refuses
    // colliding names itself) or from `Project` (which runs this check). So this guard has no
    // live witness and cannot be given one from source today. KEPT anyway: it answers for a
    // producer the parse-stage rule cannot see, and the alternative is a silent duplicate-keyed
    // schema — the exact failure WI-763 measured here.
    // Compared by SHORT name for the same reason `projection_columns` resolves source columns
    // that way: these are one tuple's own field labels, so this is a within-schema field
    // comparison (WI-638 mode 3), not a cross-scope symbol identity (WI-672).
    for (i, (key, _)) in projections.iter().enumerate() {
        let key_name = short_name_of(kb.local_name_of(*key));
        if projections[..i]
            .iter()
            .any(|(k, _)| short_name_of(kb.local_name_of(*k)) == key_name)
        {
            return Err(format!(
                "`Project` keep spec names the result key `{key_name}` twice; each key is a \
                 distinct column of the projected schema, so it must appear once"
            ));
        }
    }
    Ok(projections)
}

/// WI-731 — the SOURCE COLUMN each entry of a `Rename` map names, read out of TYPE position.
///
/// THE CHANNEL, AND WHY IT IS NOT A DENOTED. `Project` carries its sources as `denoted`
/// strings (`Keep = (person: "name")`) because the surface `r.(person: name)` writes a bare
/// member that has no value; `rename`'s surface writes `r.rename(who: r.name)`, whose operand
/// IS a value — the one-column relation `r.name`. So the source name arrives as that
/// relation's SCHEMA, `Relation[T = (name: String)]`, and no denoted is needed.
///
/// THAT ONLY WORKS BECAUSE OF WI-20260818-YQB1Y. Until the schema 1-collapse was dropped,
/// `r.name` typed as `Relation[T = String]` — the column's NAME was nowhere in the type — and
/// a captured source therefore could not reach type position at all. That is the premise this
/// ticket's "blocked on the macro face" note was written on, and dropping the collapse
/// retired it: the ordinary variadic-capture face (proposal 056 §2.1, `fix`'s shape) now
/// carries a column name to the type level, with no compile-time macro and nothing keyed on
/// `rename`'s identity.
///
/// LOUD on every shape that is not exactly one column: a non-relation operand, a whole
/// relation (`r.rename(who: r)` — which column?), and a membership relation (none).
fn rename_map_sources(kb: &KnowledgeBase, map: &Value) -> Result<Vec<(Symbol, String)>, String> {
    let TypeExtractor::NamedTuple(entries) = extract_type(kb, map) else {
        return Err(
            "`Rename` operand `Map` must be the record of renames — each entry `newName: \
             r.oldName`, whose value is the ONE-COLUMN relation naming the source column"
                .to_string(),
        );
    };
    let relation_sym = kb.try_resolve_symbol("anthill.prelude.Relation");
    let mut out: Vec<(Symbol, String)> = Vec::with_capacity(entries.len());
    for (result_key, operand) in entries.iter() {
        let key_name = short_name_of(kb.local_name_of(*result_key));
        let describe = |what: &str| {
            format!(
                "`rename` entry `{key_name}` must name ONE source column as a single-column \
                 relation (`{key_name}: r.oldName`), {what}"
            )
        };
        if sort_functor_of_view(kb, operand) != relation_sym {
            return Err(describe(&format!(
                "but its value is `{}`, which is no relation at all",
                type_display_name_value(kb, operand)
            )));
        }
        let schema = extract_type_param(kb, operand, "T").ok_or_else(|| {
            describe("but its relation type states no schema `T` to read the column name from")
        })?;
        let fields = schema_fields(kb, &schema)
            .ok_or_else(|| describe(&format!("but {}", not_a_schema_tail(kb, &schema))))?;
        match fields.as_slice() {
            [(f, _)] => out.push((*result_key, short_name_of(kb.local_name_of(*f)).to_string())),
            [] => {
                return Err(describe(
                    "but its relation is a MEMBERSHIP relation, which has no column to rename",
                ))
            }
            many => {
                return Err(describe(&format!(
                    "but its relation has {} columns ({}) — project the one first (`{key_name}: \
                     r.{}`)",
                    many.len(),
                    many.iter()
                        .map(|(f, _)| short_name_of(kb.local_name_of(*f)).to_string())
                        .collect::<Vec<_>>()
                        .join(", "),
                    short_name_of(kb.local_name_of(many[0].0)),
                )))
            }
        }
    }
    Ok(out)
}

/// WI-731 — the TYPE of the source column one `Map` entry names, re-read off the same
/// operand [`rename_map_sources`] read the NAME from. Separate because the two answers have
/// different consumers — the name resolves the column, the type CHECKS it — and folding them
/// into one tuple would make every caller carry the half it does not use.
fn rename_source_column_type(kb: &KnowledgeBase, map: &Value, result_key: Symbol) -> Option<Value> {
    let TypeExtractor::NamedTuple(entries) = extract_type(kb, map) else {
        return None;
    };
    let operand = entries
        .iter()
        .find_map(|(k, v)| (*k == result_key).then_some(v))?;
    let schema = extract_type_param(kb, operand, "T")?;
    match schema_fields(kb, &schema)?.as_slice() {
        [(_, ty)] => Some(ty.clone()),
        _ => None,
    }
}

/// WI-731 — the INTERNAL type-level operation behind the `Rename[T, Map]` type constructor:
/// the relation SCHEMA that re-keying `Map`'s columns leaves of schema `T`.
///
/// RENAME IN PLACE, and the result keeps `T`'s ORDER. A renamed column stays where it was;
/// the ellipsis-shaped alternative (renamed columns first) is not merely uglier, it is
/// observable — kernel-language §6.7 says a destructuring binder falls back to the VALUE's
/// own component order where no tuple type is known for the pattern, which is the one reader
/// that would see the difference. (It is NOT a schema-type change: §4.5 makes permutation a
/// subtyping rule, so a permuted named tuple is the same type. That correction is recorded on
/// this ticket; the conclusion survived it, the original reason did not.) The VALUE half
/// moves with this one — `relation_rename` walks the relation's own `columns` in order.
///
/// FOUR REFUSALS, each because the silent reading is a WRONG SCHEMA rather than a crash:
/// a source naming no column of `T`; two entries renaming the SAME source; two entries with
/// the same RESULT key; and a result key colliding with a column that is not itself renamed
/// away. The last is the one worth stating — `(a, b).rename(b: r.a)` would build a schema
/// with two `b` columns, which label distinctness forbids (§4.5) and which no field lookup
/// could then answer.
pub(super) fn rename_schema_type(
    kb: &mut KnowledgeBase,
    t: &Value,
    map: &Value,
    site: &CtorReduceSite,
) -> Result<Value, String> {
    let fields = schema_fields(kb, t).ok_or_else(|| {
        format!(
            "`Rename` cannot re-key operand `T`: {}",
            not_a_schema_tail(kb, t)
        )
    })?;
    let renames = rename_map_sources(kb, map)?;
    let column_names: Vec<String> = fields
        .iter()
        .map(|(f, _)| short_name_of(kb.local_name_of(*f)).to_string())
        .collect();
    // The source column's TYPE must MATCH the column it renames — the same membership+type
    // pair `Without` checks of a captured argument, and the same reason: the `Map` entry
    // states a type, and a `Map` whose type disagrees with `T`'s column is describing a
    // different column than the one it names. It is also the only part of the foreign-source
    // hole (`r.rename(who: other.name)`, which no TYPE can see — a `Relation[T = (name: …)]`
    // states no provenance) that a type CAN close: a foreign source of the same name but a
    // different type is caught here, and only a same-name same-TYPE one reaches the runtime's
    // column-variable check.
    for (result_key, source) in renames.iter() {
        let Some((_, col_ty)) = fields
            .iter()
            .find(|(f, _)| short_name_of(kb.local_name_of(*f)) == source)
        else {
            continue; // named-no-column: reported by its own arm below, with the column list
        };
        let Some(src_ty) = rename_source_column_type(kb, map, *result_key) else {
            continue; // shape already accepted by `rename_map_sources`
        };
        let mut probe = Substitution::new();
        if !types_compatible(kb, &mut probe, &src_ty, col_ty) {
            return Err(format!(
                "`rename` renames column `{source}` from a source column of type `{}`, but \
                 the relation's `{source}` is `{}`. The source must be THIS relation's own \
                 column (`r.{source}`)",
                type_display_name_value(kb, &src_ty),
                type_display_name_value(kb, col_ty),
            ));
        }
    }
    // Resolve each SOURCE against `T` by SHORT name — a schema's field symbols and the ones
    // a rename entry's operand carries are minted in different scopes, so this is the
    // schema's own field lookup (WI-638 mode 3), not a cross-scope symbol compare (WI-672).
    // Same reading `projection_columns` takes, for the same reason.
    for (i, (result_key, source)) in renames.iter().enumerate() {
        if !column_names.iter().any(|c| c == source) {
            return Err(format!(
                "`rename` renames column `{source}`, which the relation's schema does not \
                 have ({})",
                schema_columns_tail(kb, &fields)
            ));
        }
        if let Some((prev_key, _)) = renames[..i].iter().find(|(_, s)| s == source) {
            return Err(format!(
                "`rename` renames column `{source}` twice — to `{}` and to `{}`. A column has \
                 one name in the result, so name it once",
                short_name_of(kb.local_name_of(*prev_key)),
                short_name_of(kb.local_name_of(*result_key)),
            ));
        }
        let key_name = short_name_of(kb.local_name_of(*result_key));
        if renames[..i]
            .iter()
            .any(|(k, _)| short_name_of(kb.local_name_of(*k)) == key_name)
        {
            return Err(format!(
                "`rename` names the result column `{key_name}` twice; each is a distinct column \
                 of the renamed schema, so it must appear once"
            ));
        }
    }
    // The RESULT names, in `T`'s order — a renamed column keeps its position.
    let renamed: Vec<(Symbol, Value)> = fields
        .iter()
        .map(|(f, ty)| {
            let name = short_name_of(kb.local_name_of(*f));
            let key = renames
                .iter()
                .find_map(|(k, s)| (s == name).then_some(*k))
                .unwrap_or(*f);
            (key, ty.clone())
        })
        .collect();
    // A rename onto a name a SURVIVING column already has. Checked over the RESULT rather
    // than over `T`, which is what makes the swap `(a, b).rename(a: r.b, b: r.a)` legal while
    // `(a, b).rename(b: r.a)` is not: the first leaves no duplicate, the second does.
    for (i, (f, _)) in renamed.iter().enumerate() {
        let name = short_name_of(kb.local_name_of(*f));
        if renamed[..i]
            .iter()
            .any(|(g, _)| short_name_of(kb.local_name_of(*g)) == name)
        {
            return Err(format!(
                "`rename` would leave TWO columns named `{name}` — the schema's own `{name}` is \
                 still there. Rename it too, or pick another result name (a schema's column \
                 names are distinct, §4.5)"
            ));
        }
    }
    Ok(relation_schema_type(kb, &renamed, site.sp))
}

/// WI-732 — the INTERNAL type-level operation behind the `Project[T, Keep]` type constructor:
/// the relation SCHEMA that keeping (and renaming) `Keep`'s columns leaves of schema `T`.
/// The third schema member of the family — where `Concat` merges two schemas and `Without`
/// shrinks one by a drop-set, `Project` restricts one to a keep-set — so `project_run` states
/// its own result type instead of the typer stamping it afterwards.
///
/// Shares [`projection_columns`] with the FORWARD dot/tuple recognition, so the direction that
/// decides "this IS a projection" and the direction that re-derives its schema on a re-type
/// are ONE decision procedure and cannot drift (the WI-759 `FieldOf` discipline; the drift
/// WI-758 recorded is what that discipline exists to prevent). The result is `Unit` for no
/// kept column and the named tuple of the kept ones otherwise, exactly as any relation schema
/// is typed — arity one included (WI-20260818-YQB1Y).
pub(super) fn project_schema_type(
    kb: &mut KnowledgeBase,
    t: &Value,
    keep: &Value,
    site: &CtorReduceSite,
) -> Result<Value, String> {
    let projections = keep_spec_projections(kb, keep)?;
    let columns = projection_columns(kb, t, &projections)?;
    Ok(relation_schema_type(kb, &columns, site.sp))
}

/// WI-714 (proposal 052) — synthesize the `project_run(receiver, <spec>)` call for a
/// distribute-dot projection over a relation, and TYPE IT through ordinary operation typing.
/// `project` carries no lambda, so — unlike `where`/`join` — there is no compile-time macro:
/// the typer builds the runtime call directly.
///
/// The projection travels on TWO channels, both built HERE from one `projections` list so
/// they cannot disagree (the WI-759 `field_access` shape — a `String` value argument beside a
/// `Name` denoted type argument):
///  - the VALUE channel — a `Value::Tuple` (result-key ↦ `Str(source-name)`) spliced as a
///    `Term`, the same compile-time→runtime handoff `where`/`join` use, which the runtime
///    `project_run` reads to rebuild the relation's materialized `columns`;
///  - the TYPE channel — the same map as a `Keep` type argument, a named-tuple TYPE whose
///    components are `denoted` source names. This is what makes `project_run`'s declared
///    return `Relation[T = Project[T = r.T, Keep = Keep], E = r.E]` state the projected schema
///    itself. Before WI-732 the signature declared the nominal `-> Relation[T = r.T]` — the
///    UNPROJECTED schema — and the typer stamped the real one over it, so a re-type had to be
///    intercepted by a hatch keyed on `project_run`'s own identity.
///
/// `Keep` is GROUND (hash-consed), not occurrence-carried, for WI-759's measured reason: the
/// return type is term-backed, so the type-param binding resolves through the `TermId` deep
/// σ-walk, which STOPS at a non-`Term` binding (WI-394) and would leave `Keep` an unresolved
/// var — reducing `Project` to a residual on every projection. A keep spec is closed ground
/// data, which is what hash-consing is for. (The `Value`-level walk the apply resolves a
/// return type through now SPLICES such a binding back — `splice_non_term_bindings` — so
/// that stop no longer strands it; ground is kept for the sharing reason, and dropping it is
/// unmeasured.)
///
/// `None` when this is not a projection at all — the receiver is not a `Relation`, or a source
/// names no column — so the caller falls through (dot dispatch → `DotDispatchNoMatch`; the
/// tuple pre-check → ordinary tuple typing). `Some(Err)` is a projection that failed to type,
/// which is LOUD rather than a silent fall-through.
pub(super) fn build_relation_projection(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    flow: &FlowEnv,
    recv_ty: &Value,
    recv_effects: &[Value],
    receiver_node: &Rc<NodeOccurrence>,
    projections: &[(Symbol, String)],
    occ: &Rc<NodeOccurrence>,
) -> Option<Result<TypeResult, TypeError>> {
    // The GATE — is this a projection of a relation at all? Shares `projection_columns` with
    // the `Project` reduction that computes the schema below, so "this IS a projection" and
    // "this is its schema" are one decision procedure over one lookup. The columns it returns
    // are deliberately discarded: the SIGNATURE derives the schema, and re-deriving it here
    // would be the second producer whose drift from the first this shares the lookup to
    // prevent.
    let relation_sym = kb.try_resolve_symbol("anthill.prelude.Relation")?;
    if sort_functor_of_view(kb, recv_ty) != Some(relation_sym) {
        return None;
    }
    let schema = extract_type_param(kb, recv_ty, "T")?;
    projection_columns(kb, &schema, projections).ok()?;

    // The runtime spec: a `Value::Tuple` mapping each RESULT key to its source column
    // NAME (a `Value::Str`), in projection order. `project_run` selects `r`'s column of
    // that source name and re-keys it to the result key.
    let spec_named: Vec<(Symbol, Value)> = projections
        .iter()
        .map(|(k, src)| (*k, Value::Str(src.clone())))
        .collect();
    let spec = Value::Tuple {
        pos: Vec::new().into(),
        named: spec_named.into(),
    };
    let pass = crate::kb::simp_rewrite::simp_pass(kb);
    // Splice the spec as a `Term` carrier (the `project_run` `spec: Term` slot); the
    // `Expr::Spliced` typer arm reads `inferred_type`, so stamp it (as `where`/`join` do).
    let spliced =
        NodeOccurrence::synthesized_expr(Expr::Spliced(spec), Rc::clone(occ), pass, occ.owner);
    let term_ty = Value::term(kb.make_sort_ref_by_name("anthill.reflect.Term"));
    spliced.set_inferred_type(term_ty.clone());
    let project_run = kb.try_resolve_symbol("anthill.prelude.Relation.project_run")?;
    // The keep spec in TYPE position, keyed by the callee's OWN `Keep` type-param symbol read
    // off the declaration — `seed_op_type_args` matches type-argument labels by symbol
    // IDENTITY, and an op-scoped param symbol is not the bare intern of its short name
    // (WI-708). A missing `Keep` parameter is LOUD: falling through would report `no such
    // member` for every projection in every program, naming the user's code instead of the
    // malformed declaration (the `synthesize_field_access` precedent).
    let keep_param = lookup_operation_info_full(kb, project_run).and_then(|op| {
        op.type_params
            .iter()
            .find(|(n, _)| short_name_of(kb.local_name_of(*n)) == PROJECT_KEEP_OPERAND)
            .map(|(n, _)| *n)
    });
    let Some(keep_param) = keep_param else {
        return Some(Err(projection_type_error(
            &TypeErrorContext::OperationReturn {
                op_name: project_run,
                surface: None,
            },
            Some(occ.span.span),
            &format!(
                "`anthill.prelude.Relation.project_run` must declare a `{}` type parameter — \
                 the channel a projection's keep spec travels to type position through",
                PROJECT_KEEP_OPERAND
            ),
        )));
    };
    let keep_fields: Vec<(Symbol, TermId)> = projections
        .iter()
        .map(|(k, src)| {
            let name = kb.alloc(Term::Const(Literal::String(src.clone())));
            (*k, kb.make_denoted(name))
        })
        .collect();
    let keep = Value::term(kb.make_named_tuple_type(&keep_fields));
    let pos_args = vec![Rc::clone(receiver_node), Rc::clone(&spliced)];
    let synth = NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: None,
            functor: project_run,
            pos_args: pos_args.clone(),
            named_args: Vec::new(),
            type_args: vec![(Some(keep_param), keep)],
        },
        Rc::clone(occ),
        pass,
        occ.owner,
    );
    // Type the synthesized call the ordinary way, so the schema comes from the SIGNATURE.
    // The arguments are already typed — the receiver by the caller, the spec by construction —
    // so they are handed over as results rather than re-visited.
    //
    // This RE-ENTERS `check_apply_iter`, which can reach back here via
    // `check_constructor_iter` → `check_tuple_literal_constructor` →
    // `try_relation_projection_tuple`. It takes no `fuel` because it cannot cycle: the callee
    // is `project_run`, which is an operation and not a constructor (so the constructor route
    // is never taken), and both arguments arrive ALREADY TYPED as `pos_results`, so no
    // argument is re-visited and no new tuple literal can be reached. Both properties are
    // structural rather than asserted — if either changes, this needs the `fuel` counter the
    // work-loop's `push_visit` path carries.
    let pos_results = vec![
        Ok(TypeResult {
            ty: recv_ty.clone(),
            env: env.clone(),
            effects: recv_effects.to_vec(),
            node: Rc::clone(receiver_node),
        }),
        Ok(TypeResult {
            ty: term_ty,
            env: env.clone(),
            effects: Vec::new(),
            node: spliced,
        }),
    ];
    Some(check_apply_iter(
        kb,
        env,
        flow,
        &synth,
        project_run,
        &pos_args,
        &[],
        &pos_results,
        &[],
        Some(occ.span.span),
        None,
        // WI-1104: a synthesized `project_run` call standing in for a tuple field — a
        // VALUE wherever the enclosing tuple is written, goal position included.
        NodePos::Value,
        // WI-20260904-50B2K part (c): a synthesized projection shape, not a written
        // body — nothing reads what it solves.
        None,
    ))
}

/// WI-714 — the `(receiver, member-symbol, source-column-short-name)` of a tuple field that
/// is a bare single-column access `rel.c` on a relation VALUE — an `Expr::DotApply {
/// receiver, name }` (the distribute-dot's desugaring over a value receiver, zero call
/// args). `None` for any other field shape — a NON-VALUE receiver, for which `convert.rs`
/// builds `field_access` rather than `dot_apply` — so the tuple falls through to ordinary
/// tuple typing.
///
/// A BARE RULE REF IS NOT ONE OF THOSE, though this said it was. The claim was that a rule
/// ref's members "desugar to `field_access(…, Ident)` and error before reaching here — that
/// form needs a `let` binding first, the WI-443/F1 dot-access limitation `where`/`join`
/// share". MEASURED otherwise on this tree: `person_row.(name)` with no `let` loads and runs,
/// and `person_row.(nosuch)` reaches the WI-20260818-7X7NK diagnostic — which is only
/// reachable through a `Some` from here. The loader's value-rooted re-route
/// (`field_access_root_is_value`, kb/load.rs) converts it to a `DotApply`, and
/// [`projection_receiver_type`]'s `relation_ref_arg_type` rung types the bare ref. The `let`
/// limitation is real for `where`/`join`, whose lambda argument is a different shape; it was
/// carried over to projection, where it does not hold.
///
/// BOTH SPELLINGS OF THE MEMBER, because the two consumers ask different questions of it.
/// The SHORT NAME is the schema lookup key — a relation schema's field symbols and the
/// member written after the dot are minted in different scopes, so the column lookup is a
/// within-schema name compare (WI-638 mode 3), not a symbol identity (WI-672). The SYMBOL is
/// what a DIAGNOSTIC names (WI-20260818-7X7NK): `TypeErrorContext::DotProjection` locates the
/// failure by the member the author wrote, which for a RENAME `r.(a: f)` is `f` and not the
/// result key `a`.
fn relation_column_access_parts(
    kb: &KnowledgeBase,
    field: &Rc<NodeOccurrence>,
) -> Option<(Rc<NodeOccurrence>, Symbol, String)> {
    match field.as_expr()? {
        Expr::DotApply {
            receiver,
            name,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => Some((
            Rc::clone(receiver),
            *name,
            short_name_of(kb.local_name_of(*name)).to_string(),
        )),
        _ => None,
    }
}

/// WI-714 — the `Relation[T]` type of an argument that a SIBLING CALLBACK PARAM projects
/// (`join(r1, r2, cond: (c: r1.T, q: r2.T) -> Bool)`): a let-bound relation var (env), a
/// bare rule reference (a `Relation` value, WI-714 C2, never in the value env), or a
/// computed relation the node already carries stamped (WI-750). Composed from the
/// [`varref_arg_env_type`] / [`relation_ref_arg_type`] readers, env first — a still-flexible
/// env binding is the live one, a stamp only a fallback.
///
/// TWO CONSUMERS, both wanting the same thing — a receiver's `Relation[T]`: the row-lambda
/// hint path ([`known_arg_types_and_staged`]) and the relation-projection recognizer
/// ([`try_relation_projection_tuple`]). WI-762 removed only the recognizer's use of this to
/// find the LOWERED receiver NODE (that now comes from the `DotApply` frame's own record);
/// the TYPE still comes from here, and it must, because the rung ORDER is load-bearing:
/// env FIRST, stamp only as a fallback. A let-bound receiver's env binding is the live,
/// still-refinable one while the stamp is a snapshot, so reading the stamp alone can compute
/// a projected schema from a stale type.
pub(super) fn projection_receiver_type(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    receiver: &Rc<NodeOccurrence>,
) -> Option<Value> {
    varref_arg_env_type(kb, env, receiver)
        .or_else(|| relation_ref_arg_type(kb, receiver))
        .or_else(|| receiver.inferred_type())
}

/// WI-714 (proposal 052) — synthesize the projected relation for the named tuple a
/// MULTI-member distributive projection `r.(f1, f2)` (rename `r.(a: f1, …)`) desugared
/// into (§6.8).
///
/// RECOGNIZED BY PROVENANCE, not by shape (WI-762). `convert.rs` desugars `r.(f1, f2)` to
/// `(f1: r.f1, f2: r.f2)` — a term IDENTICAL to that tuple written by hand — and marks the
/// result. Before the mark this function inferred projection-hood from the fields' shape
/// plus a SOURCE-SPAN comparison of their receivers, which is what told ONE receiver
/// duplicated by the desugaring from two the author wrote. Every field of a marked tuple
/// carries the same receiver BY CONSTRUCTION, so the first field's receiver is THE
/// receiver and there is nothing to compare.
///
/// THE NARROWING THIS MADE DELIBERATE: a HAND-WRITTEN `(name: r.name, age: r.age)` is no
/// longer read as a projection. It is a tuple, and it types as one — a tuple of two
/// independent single-column relations. Proposal 052:182 introduced the shape-based
/// reading explicitly as the stopgap "until `.( )` lands"; `.( )` landed as WI-639, so the
/// stopgap has served its purpose. 052:184-187 states the positive rule that replaces it:
/// projection is the distribute-dot, and anything COMPUTED per row is written functionally
/// with `.map`, which yields a plain `Stream` rather than a `Relation`. Nothing in the
/// corpus relied on the old reading; the one hand-written instance
/// (`wi714_project_two_written_receivers_stay_a_tuple`) asserts the tuple reading, and now
/// gets it structurally rather than by a span compare.
///
/// The gate is a SURFACE FORM, which is what keeps it inside the rule the deleted doc block
/// stated and was the only citation of: "keying a typer decision on a domain op's identity is
/// what the `join` → `Concat` discipline forbids". An operation's identity is an OPEN set the
/// stdlib owns — branching on it means editing the typer to add `leftJoin`. A surface form is
/// a CLOSED set the grammar owns, and branching on it is what an IR variant is for.
///
/// Returns `None` — ordinary tuple typing — when the tuple is not marked, or when a field
/// is not a bare column access. The latter is the NON-VALUE receiver: `convert.rs` builds
/// `field_access` rather than `dot_apply` for it (`is_value_receiver`), and a projection
/// over e.g. a type-level receiver is not a relation projection.
pub(super) fn try_relation_projection_tuple(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    flow: &FlowEnv,
    positional: usize,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    named_results: &[Result<TypeResult, TypeError>],
    occ: &Rc<NodeOccurrence>,
) -> Option<Result<TypeResult, TypeError>> {
    if !matches!(
        occ.as_expr(),
        Some(Expr::Constructor {
            from_projection: true,
            ..
        })
    ) {
        return None;
    }
    // A TOTAL guard, not a `debug_assert`. Both conditions are implied by the mark —
    // `convert.rs` builds the projection tuple with named args only, and never with none —
    // but an assert compiles out, and the release-mode consequence of a violation is that a
    // positional field is SILENTLY DROPPED from the synthesized projection. Falling through
    // to ordinary tuple typing is the safe reading of a shape this function does not
    // understand.
    //
    // WI-20260818-YQB1Y — the floor moved from TWO named args to ONE. `convert.rs` used to
    // 1-collapse `r.(f)` to the scalar `r.f` before any tuple existed, so a marked tuple
    // always had ≥2 fields; it now builds and marks the one-field tuple too, and a
    // single-member projection is recognized HERE rather than falling through to dot
    // dispatch's single-column arm. Both surfaces still agree — `r.f` and `r.(f)` each yield
    // `Relation[T = (f: …)]` — because both end at [`build_relation_projection`].
    if positional > 0 || named_args.is_empty() {
        return None;
    }
    let mut receiver: Option<Rc<NodeOccurrence>> = None;
    let mut projections: Vec<(Symbol, String)> = Vec::with_capacity(named_args.len());
    for (label, field) in named_args {
        let (recv_occ, _member, source) = relation_column_access_parts(kb, field)?;
        match &receiver {
            None => receiver = Some(recv_occ),
            // WI-814 made this WRITABLE — see the note below.
            Some(first) if !views_structurally_equal(kb, first, &recv_occ) => {
                return Some(Err(projection_type_error(
                    &TypeErrorContext::DotProjection { member: *label },
                    Some(occ.span.span),
                    "internal: this tuple is marked as a distributive projection `.( )`, whose \
                     fields share ONE receiver by construction, but its fields' receivers are \
                     structurally different. A rewrite (`@[simp]`) changed one field's receiver \
                     without clearing the mark.",
                )));
            }
            Some(_) => {}
        }
        projections.push((*label, source));
    }
    let receiver = receiver?;
    let columns = projections
        .iter()
        .map(|(_, src)| src.as_str())
        .collect::<Vec<_>>()
        .join(", ");
    // VERIFIED, not assumed (the loop above) — every field shares this receiver, so taking
    // the FIRST field's receiver is sound and not merely licensed by the mark. The hazard
    // the check closes: the mark rides through rewrites (`simp_rewrite::reassemble` carries
    // `from_projection`), so a `@[simp]` rule that rewrote ONE field's receiver would leave a
    // marked tuple whose fields disagree, and this would have projected the first and
    // SILENTLY DROPPED the rest.
    //
    // The comparator is `views_structurally_equal` and there is deliberately NO second one
    // beside it. It became usable here only with WI-814: a computed receiver
    // (`r.where(lambda c -> …)`) nests a LAMBDA in its args, and `Expr::Lambda` used to fall
    // to `occ_head`'s `_ => ViewHead::Opaque` arm, which has no `(Opaque, Opaque)` equal arm
    // — sound for a MATCHING predicate, a false negative as an IDENTITY test, and it
    // rejected all ten `wi714_project` tests. WI-814 gave `Lambda` (and the Pattern-kind
    // `param` it binds) the head its loader-emitted term twin already had.
    //
    // Two other tools were tried and are the wrong shape; recorded so neither is reached for
    // again:
    //  - `occurrence_to_term` (and the memoizing `cached_term` wrapper it then had):
    //    answers a pure question by MUTATING the KB, and that cache "owns the single `+1`
    //    … and never releases it (pin-for-lifetime)", so each comparison pinned a term for
    //    the KB's life. It is also a GOAL-POSITION reifier — an args-bearing
    //    `Expr::DotApply` (`r.where(λ)`) takes its `debug_assert!(false)` arm and yields
    //    `Term::Bottom`, so in RELEASE two DIFFERENT computed receivers would both reify to
    //    ⊥ and compare EQUAL. WI-815 DELIVERED the half of this that was actionable: the
    //    wrapper and its cache are gone, and the one caller that wanted structural identity
    //    (value-fact dedup) reads a `GoalKey` — the same answer this note reached.
    //  - a hand-rolled `for_each_child` walk: a second comparator, diverging on first
    //    contact with a carrier `views_structurally_equal` already handles.
    //
    // WHY AN ERROR AND NOT A FALL-THROUGH to ordinary tuple typing. Divergence here is an
    // INTERNAL INVARIANT VIOLATION (convert.rs built the fields from one receiver), not a
    // program the author could write — an unmarked tuple of two receivers is a tuple and
    // never reaches this function. So the reachable cause is a compiler bug, and the
    // "safe reading of a shape this function does not understand" that the positional guard
    // above takes does not apply: falling through would type a mis-rewritten projection as
    // two independent single-column relations and say nothing.
    let lowered = receiver.lowered_receiver();
    let recv_ty = projection_receiver_type(kb, env, &receiver);
    let (Some(receiver), Some(recv_ty)) = (lowered, recv_ty) else {
        return Some(Err(projection_type_error(
            &TypeErrorContext::DotProjection {
                member: projections[0].0,
            },
            Some(occ.span.span),
            &format!(
                "this is a column projection `({columns})` over ONE receiver, but the \
                 receiver's typed form is not available here, so the projected schema cannot \
                 be computed. Bind the receiver with a `let` first \
                 (`let r = …; r.({columns})`)."
            ),
        )));
    };
    // The receiver's EFFECTS. Every field is a single-column projection of the SAME
    // receiver, and a single-column projection's effects ARE the receiver's (projection
    // adds no search — the dot-dispatch mode threads `recv.effects` through unchanged), so
    // the first typed field carries exactly what a multi-column projection must incur.
    // Reading them here is what lets the receiver be COMPUTED (WI-732): the pre-WI-732
    // leaf-only recognizer could hardcode `&[]` because a let-bound var / bare rule ref is
    // pure, and left threading a computed receiver's effects as an explicit follow-up NOTE.
    //
    // `.expect` rather than a default: `check_constructor_iter` runs `collect_arg_errors`
    // before routing here, so every result is already `Ok` — the file's own idiom for a
    // slot the aggregator has already guaranteed.
    let recv_effects: &[Value] = named_results
        .first()
        .map(|r| r.as_ref().expect("aggregator").effects.as_slice())
        .unwrap_or(&[]);
    build_relation_projection(
        kb,
        env,
        flow,
        &recv_ty,
        recv_effects,
        &receiver,
        &projections,
        occ,
    )
}

/// WI-20260818-7X7NK — the diagnostic for a `.( )` projection that names no column of the
/// relation it projects. Called from the `TypeBuildFrame::Constructor` arm AHEAD of its
/// `collect_arg_errors`, because the defect is that the field's own error arrives first and
/// is about the wrong question — and it arrives THERE, not at `check_constructor_iter`'s own
/// aggregator, which a failing field never reaches.
///
/// THE ROUTE IT REPLACES. `r.(nosuch)` desugars (§6.8) to the marked tuple
/// `(nosuch: r.nosuch)`, so the projection is recognized at the TUPLE
/// ([`try_relation_projection_tuple`]) while `r.nosuch` is typed as an ordinary member
/// access one level down. `nosuch` is no column and no member, so dot dispatch fails and
/// `collect_arg_errors` surfaces "no such member (dot dispatch)" — a TRUE sentence about a
/// question the author did not ask. They wrote a column selection and were told their
/// relation has no METHOD of that name.
///
/// PER FIELD, AND IT REPLACES NOTHING IT DID NOT ANSWER. This returns the projection's
/// COMPLETE error list, in field order, with only the fields it can re-ask rewritten and
/// every other error kept verbatim for the caller to aggregate. It was first written to pick
/// the FIRST failing field and return that one error, and both halves of that were wrong:
/// `r.(takeN, nosuch)` reported `nosuch` through dot dispatch again — the very defect, one
/// coordinate (field order) over, on a surface where the order is the author's arbitrary
/// choice — and `r.(nosuch, takeN)` DROPPED `takeN`'s arity error entirely. Neither is
/// visible to a fixture whose fields all fail the same way, which is why every arm of the
/// first cut agreed with it.
///
/// `None` when nothing was rewritten, so the ordinary aggregator runs unchanged rather than
/// this cloning an identical list.
///
/// THREE GATES, and the order is the whole justification:
///  1. the SURFACE FORM — `Expr::Constructor { from_projection: true }`, the mark
///     `convert.rs` leaves on the desugared tuple (WI-762). A grammar-owned closed set, which
///     is what [`try_relation_projection_tuple`] already keys its typing decision on, so a
///     hand-written `(nosuch: r.nosuch)` is untouched and keeps dot dispatch's message.
///  2. the FIELD's failure is `DotDispatchNoMatch` for that field's OWN member — see below.
///  3. the receiver's SORT is `Relation`. This is the same gate
///     [`build_relation_projection`] uses to decide projection-vs-tuple in the first place —
///     not a new one — and it is inside the standing "nothing keys on an operation's
///     identity" discipline for the reason that discipline exists: an op identity is an OPEN
///     set the stdlib owns, while `Relation` is one kernel sort, named by §6.8 and declared
///     in `stdlib/anthill/prelude/relation.anthill`. Nothing here keys on a Relation
///     OPERATION.
///
/// WHY IT DOES NOT SWALLOW THE MEMBER READING. §6.8 admits ANY member after `.(`, not only
/// a column — `r.(isEmpty)` is the tuple `(isEmpty: Bool)` and stays one. So the message
/// says BOTH things: no column of that name, and no member either.
///
/// WHICH IS WHY THE FIELD'S FAILURE MUST BE `DotDispatchNoMatch` AND NOTHING ELSE. "The
/// field failed" is NOT "the member does not exist", and reading it as such makes the second
/// clause a LIE. MEASURED: `r.(takeN)` fails because `Stream.takeN` needs its `n` argument —
/// the member is reachable, the repair is to supply it — and an unfiltered read reported "no
/// member `takeN` is reachable on it either", destroying the arity error that said what to
/// do. The same shape covers a requirement/coherence refusal, an effect mismatch, and — the
/// sharpest case — `TypeErrorContext::DotProjection`'s OWN first population (WI-759: the
/// member resolves but its type does not), which this very context is shared with.
///
/// `None` per field, too, for a non-`Relation` receiver, and that is not a gap: over an
/// entity or a tuple, `x.(nosuch)` IS a member lookup by §6.8 and dot dispatch's message —
/// which names the receiver's own sort — is the accurate one. The projection is still
/// located, because `convert.rs` mints every distributed accessor with the WHOLE `.( )` span.
pub(super) fn projection_column_errors(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    positional: usize,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    named_results: &[Result<TypeResult, TypeError>],
    occ: &Rc<NodeOccurrence>,
) -> Option<Vec<TypeError>> {
    if !matches!(
        occ.as_expr(),
        Some(Expr::Constructor {
            from_projection: true,
            ..
        })
    ) {
        return None;
    }
    // THE SAME TOTAL GUARD [`try_relation_projection_tuple`] takes, mirrored deliberately: a
    // marked constructor with a POSITIONAL field is a shape the projection path refuses to
    // interpret, so this must not speak for it either. It also bounds what the caller's early
    // return can drop — the frame splits one result list at `pos_args.len()`, so `positional
    // == 0` means there are no positional results beside these, and returning here in their
    // place loses nothing. Both are implied by `convert.rs` building projections named-only;
    // neither is a type-level fact, which is why the recognizer states it as a guard.
    if positional > 0 || named_args.is_empty() {
        return None;
    }
    if named_results.iter().all(|r| r.is_ok()) {
        return None;
    }
    let mut errors: Vec<TypeError> = Vec::new();
    let mut rewrote = false;
    for (idx, result) in named_results.iter().enumerate() {
        let Err(err) = result else { continue };
        match named_args
            .get(idx)
            .and_then(|(_label, field)| projection_column_error(kb, env, field, err, occ))
        {
            Some(rewritten) => {
                errors.push(rewritten);
                rewrote = true;
            }
            None => errors.push(err.clone()),
        }
    }
    rewrote.then_some(errors)
}

/// WI-20260818-7X7NK — ONE field of a marked `.( )` projection, re-asked as the column
/// selection the author wrote. `None` leaves `err` exactly as it is; see
/// [`projection_column_errors`] for what each gate is and why.
fn projection_column_error(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    field: &Rc<NodeOccurrence>,
    err: &TypeError,
    occ: &Rc<NodeOccurrence>,
) -> Option<TypeError> {
    let (receiver, member, source) = relation_column_access_parts(kb, field)?;
    // THE FAILURE'S VARIANT, checked against THIS field's own member. Anything else — an
    // arity error on a member that does exist, a requirement refusal, an unreadable member
    // type — is a failure whose own message is the actionable one, and re-asking it as a
    // column lookup would both destroy that message and assert a falsehood about
    // reachability. The symbol compare cannot itself disable the gate: both sides read
    // `*name` off the SAME `Expr::DotApply` occurrence (the frame binds the member it was
    // pushed for; `relation_column_access_parts` reads it back off this very node), so it is
    // a free conservative guard rather than a second question. The WI-672 short-name hazard
    // lives in the SCHEMA lookup below, which is a short-name compare for that reason.
    if !matches!(err, TypeError::DotDispatchNoMatch { member: m, .. } if *m == member) {
        return None;
    }
    let recv_ty = projection_receiver_type(kb, env, &receiver)?;
    let relation_sym = kb.try_resolve_symbol("anthill.prelude.Relation")?;
    if sort_functor_of_view(kb, &recv_ty) != Some(relation_sym) {
        return None;
    }
    let schema = extract_type_param(kb, &recv_ty, "T")?;
    // The SHARED lookup, not a second one — `projection_columns` is the same decision
    // procedure [`build_relation_projection`] runs to accept a projection and
    // [`project_schema_type`] runs to re-derive its schema, so "this names no column" and
    // its wording cannot drift from them (the WI-759 `FieldOf` discipline). `Ok` here means
    // the column DOES exist while dot dispatch could not reach it as a member, which is not
    // this function's question — that error is left alone.
    let selection = [(member, source.clone())];
    let why = projection_columns(kb, &schema, &selection).err()?;
    Some(projection_type_error(
        &TypeErrorContext::DotProjection { member },
        Some(occ.span.span),
        &format!(
            "{why}. `.( )` admits any other member of the receiver too (spec §6.8), and no \
             member `{source}` is reachable on it either — that second lookup is what the \
             desugared `.{source}` reported."
        ),
    ))
}

/// WI-714 — the identity of a rule-head argument SLOT, stable across a relation's
/// clauses so the cross-clause column lub aligns a slot with ITSELF (not with a
/// free-column index that shifts when a clause pins a different slot to a constant).
/// `pub(crate)` so the eval-side applied builder shares the SAME head-slot enumeration
/// ([`rule_head_var_slots`]) as the typer, keeping the two in lockstep.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum SlotKey {
    Pos(usize),
    Named(Symbol),
}

/// WI-714 — one free-variable column of a relation clause: its head SLOT (for
/// cross-clause alignment), its NAME (the field key for a named slot, else the
/// source variable name), and its inferred TYPE.
pub(super) struct ClauseColumn {
    pub(super) slot: SlotKey,
    pub(super) name: Symbol,
    pub(super) ty: Value,
}

/// WI-714 — the free-variable SLOTS of a rule's head: `(slot, name, debruijn)` in
/// declaration order (positionals first, then named). A head slot holding a bare
/// variable (`Var::DeBruijn`, how rules store head params) is a free slot named by the
/// head parameter — the field key for a named slot, else the source variable name
/// recovered by the reversed DeBruijn `globals[len-1-d]`. Ground / compound slots are
/// omitted (a compound-var slot is rejected upstream by [`clause_head_has_compound_var`]).
///
/// This is the SINGLE source of a relation's head slots, shared by the typer
/// ([`relation_clause_columns`], which attaches column types via `debruijn`) and eval
/// (`build_relation_value`, which splices bound slots / freshens free ones) — so the
/// typed schema and the runtime column set are enumerated identically and cannot
/// drift. An out-of-range reversed-DeBruijn (a malformed head, non-reachable for a
/// well-formed rule) is skipped on BOTH sides, retiring the old typer-`continue`
/// vs eval-`Err` asymmetry.
pub(crate) fn rule_head_var_slots(kb: &KnowledgeBase, rid: RuleId) -> Vec<(SlotKey, Symbol, u32)> {
    let head = match kb.rule_head_value(rid) {
        Value::Term { id, .. } => *id,
        _ => return Vec::new(),
    };
    let globals = kb.rule_globals(rid);
    let n = globals.len();
    let (pos_args, named_args) = match kb.get_term(head) {
        Term::Fn {
            pos_args,
            named_args,
            ..
        } => (pos_args.clone(), named_args.clone()),
        _ => return Vec::new(),
    };
    let mut slots: Vec<(SlotKey, Symbol, u32)> =
        Vec::with_capacity(pos_args.len() + named_args.len());
    for (i, &a) in pos_args.iter().enumerate() {
        if let Term::Var(Var::DeBruijn(d)) = kb.get_term(a) {
            let d = *d;
            if let Some(v) = globals.get(n.wrapping_sub(1).wrapping_sub(d as usize)) {
                slots.push((SlotKey::Pos(i), v.name(), d));
            }
        }
    }
    for &(k, a) in named_args.iter() {
        if let Term::Var(Var::DeBruijn(d)) = kb.get_term(a) {
            slots.push((SlotKey::Named(k), k, *d));
        }
    }
    slots
}

/// WI-714 — the free-variable COLUMNS of one relation clause, in declaration order:
/// [`rule_head_var_slots`] with a TYPE attached to each. The column TYPE is the
/// explicit `?x: T` bound if present, else the type inferred from the var's op-param /
/// entity-field positions (`collect_rule_var_types`, keyed by DeBruijn index), else a
/// fresh type var (an unconstrained column).
///
/// WI-9C2PZ — "ELSE" IS NOW THE WHOLE STORY, because the inferred type is already the
/// right thing. A column typed only by a SPEC operation used to take that spec's own
/// parameter verbatim (`rule named(?x) :- eq(?x, "root")` recorded
/// `anthill.prelude.PartialEq.T`, the symbol every `eq` in the KB shares), which is the
/// ABSENCE of a column type rather than a column type — so WI-741 normalized it here into
/// a variable, minting ONE per distinct PARAMETER SYMBOL so that columns which shared the
/// parameter still shared a variable.
///
/// [`instantiate_declared_type`] now mints that variable at the CALL instead, which is
/// both earlier and sharper: `rule pair_eq(?x, ?y) :- eq(?x, ?y)` still puts both columns
/// on one variable (one call, one instantiation — the correlation
/// `wi714_applied_correlated_columns_reject_contradiction` and
/// `wi714_applied_unconstrained_column_accepts_and_narrows` own), while two INDEPENDENT
/// `eq` calls now get two, which the parameter-keyed mint could not express — it keyed on
/// a symbol shared by every call in the KB. So "unknown" still leaves this function spelled
/// exactly one way, and the normalization that guaranteed it is gone because nothing
/// arrives needing it.
pub(super) fn relation_clause_columns(kb: &mut KnowledgeBase, rid: RuleId) -> Vec<ClauseColumn> {
    let head = match kb.rule_head_value(rid).clone() {
        Value::Term { id, .. } => id,
        _ => return Vec::new(),
    };
    let body_nodes: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
    let (var_types, _contradiction) = collect_rule_var_types(kb, head, &body_nodes);
    // WI-20260911-5G28A — OPEN THIS CLAUSE'S BOUNDS PER CITATION, and that is what makes
    // a TIE between two columns readable at a call site. `rule my_rule(?x: List[T = ?t],
    // ?res: List[T = ?t])` stores both bounds De Bruijn-closed against one frame, so ONE
    // fresh global per citation reaches BOTH columns — the two share a variable the
    // caller's argument can then pin (`relation_reference_type_applied` binds it through
    // σ), and `res` comes back at whatever `x` was.
    //
    // FRESH PER CITATION, not once per clause: two citations of the same rule in one
    // program are two independent instantiations, exactly as two firings are. Reading the
    // stored De Bruijn term directly instead would hand `types_compatible` a bound
    // variable, which it treats as a WILDCARD — measured before this ticket, when the
    // bound rode a shared `Var::Global`: every one of the four driving rows came back
    // "argument binding column `x` has an incompatible type", the concrete and the rigid
    // alike.
    //
    // NOTHING IS MINTED FOR A CLAUSE WITH NO BOUNDS, which is nearly every clause a
    // citation names: the `is_empty` test comes FIRST because this runs once per clause
    // per citation (`relation_columns_across_clauses` folds over all of them), and an
    // earlier cut allocated a whole frame of throwaway `VarId`s before ever looking at
    // `rule_type_bounds`. Found by `/code-review`.
    //
    // Each fresh variable keeps its SLOT's OWN NAME, so a diagnostic rendering a column
    // type says `?x` / `?res` rather than one borrowed placeholder for every slot.
    let stored_bounds = kb.rule_type_bounds(rid).to_vec();
    let type_bounds: Vec<(u32, TermId)> = if stored_bounds.is_empty() {
        Vec::new()
    } else {
        // INDEXED BY DE BRUIJN NUMBER, which is what `term_from_debruijn` reads: slot `k`
        // holds `globals[len - 1 - k]`. A slot holding an enclosing SORT's type parameter
        // (a relational clause's, §7.3 S3(d)) stays that parameter: it opens fresh per
        // ACTIVATION, but at a citation it is the variable S1's `open_citation_params`
        // renames and the bracket pins. MEASURED, built in POSITION order instead the
        // parameter landed in the other slot and every bracket check stopped firing
        // (`wi_5g28a_citation_bracket_test`'s refusals loaded clean) — harmless while
        // every slot was fresh, where only the names came out swapped.
        let globals: Vec<VarId> = kb.rule_globals(rid).to_vec();
        let fresh_frame: Vec<VarId> = globals
            .iter()
            .rev()
            .map(|&v| {
                if kb.is_canonical_type_param_var(v) {
                    v
                } else {
                    kb.fresh_var(v.name())
                }
            })
            .collect();
        stored_bounds
            .into_iter()
            .map(|(i, t)| (i, kb.term_from_debruijn(t, &fresh_frame)))
            .collect()
    };
    let slots = rule_head_var_slots(kb, rid);
    let mut columns: Vec<ClauseColumn> = Vec::with_capacity(slots.len());
    for (slot, name, d) in slots {
        // Split before the chain so the immutable read of `var_types` is finished
        // before the `&mut kb` arms below.
        let inferred = var_types.get(&d).cloned();
        let ty = if let Some((_, t)) = type_bounds.iter().find(|(i, _)| *i == d) {
            Value::term(*t)
        } else if let Some(t) = inferred {
            t
        } else {
            let fresh = kb.fresh_var(name);
            Value::term(kb.alloc(Term::Var(Var::Global(fresh))))
        };
        columns.push(ClauseColumn { slot, name, ty });
    }
    columns
}

/// WI-714 — true iff any top-level rule-head slot is a COMPOUND term mentioning a
/// variable (`some(?x)`, `pair(?a, 1)`). Such a slot cannot ride verbatim into a
/// runnable query goal — its raw DeBruijn would unify reflexively-only and silently
/// yield zero solutions — and its column semantics are unsettled, so a relation
/// reference over it is rejected loudly. A fully-ground compound (`pair(1, 2)`,
/// no variable) is a legitimate filter and returns `false`.
fn clause_head_has_compound_var(kb: &KnowledgeBase, rid: RuleId) -> bool {
    let Some(head) = kb.fact_head_term(rid) else {
        return false;
    };
    let (pos_args, named_args) = match kb.get_term(head) {
        Term::Fn {
            pos_args,
            named_args,
            ..
        } => (pos_args.clone(), named_args.clone()),
        _ => return false,
    };
    let is_compound_var = |kb: &KnowledgeBase, arg: TermId| -> bool {
        // A BARE var slot is a column (fine); anything else is a compound only if it
        // mentions a DeBruijn variable.
        !matches!(kb.get_term(arg), Term::Var(_)) && kb.term_mentions_debruijn(arg)
    };
    pos_args.iter().any(|&a| is_compound_var(kb, a))
        || named_args.iter().any(|&(_, a)| is_compound_var(kb, a))
}

/// WI-714 — the two clauses share the SAME set of free-variable slots (a uniform
/// head interface), so their columns lub slot-for-slot. A differing set (a clause
/// pins a slot the other leaves free, or a differing arity) is a heterogeneous
/// interface the schema synthesis does not yet support.
fn slot_keys_match(a: &[ClauseColumn], b: &[ClauseColumn]) -> bool {
    a.len() == b.len() && a.iter().all(|ca| b.iter().any(|cb| cb.slot == ca.slot))
}

/// WI-714 — why an applied rule reference's supplied arguments don't map cleanly to
/// the relation's free COLUMNS. Rendered to a message by [`Self::message`] and wrapped
/// in a loud `TypeError` (typer) / `EvalError` (eval).
pub(crate) enum RelationArgError {
    /// A positional argument beyond the relation's columns (`edge(?x)` given two
    /// positional args). 0-based index.
    PositionalOutOfRange(usize),
    /// A named argument whose key names no free column.
    UnknownParam(Symbol),
    /// A named argument binding a column a positional argument already bound.
    DoubleBind(Symbol),
}

impl RelationArgError {
    pub(crate) fn message(&self, kb: &KnowledgeBase) -> String {
        match self {
            Self::PositionalOutOfRange(i) => {
                format!("positional argument #{} has no free column to bind", i + 1)
            }
            Self::UnknownParam(k) => format!(
                "named argument `{}` names no free column",
                kb.local_name_of(*k)
            ),
            Self::DoubleBind(k) => format!(
                "named argument `{}` binds a column already bound positionally",
                kb.local_name_of(*k)
            ),
        }
    }
}

/// WI-714 — the binding plan for an APPLIED rule reference: which COLUMN each supplied
/// argument binds. Binding operates on the relation's ordered, dedup'd COLUMNS (its
/// schema) — NOT the raw head slots — so it matches what the user sees typed: a
/// positional argument at index `i` binds `column_names[i]` (the i-th column left to
/// right, skipping ground head slots), and a named argument `k` binds the column named
/// `k` (rule params are positional-with-names — `queryTwoParams(x: 3)` binds param
/// `x`). Returns the bound column NAMES in supplied order (positionals first, then
/// `named_keys` order), so the i-th entry aligns with the i-th supplied argument.
///
/// Column-based (not slot-based) binding is what makes a NONLINEAR head column
/// (`twin(?n, ?n)` → one column `n`) bind as ONE parameter (→ `Relation[Unit]`, not a
/// residual echo column), and a ground head slot before a free var (`ranked(1, ?name)`)
/// positionally bindable (`ranked("alice")` binds the sole `name` column). A positional
/// overrun, an unknown param name, or a double-bind is a loud error. Shared by the
/// typer ([`relation_reference_type_applied`]) and eval (`build_relation_value`) so the
/// schema-subtraction and the runtime column set never diverge.
pub(crate) fn resolve_relation_arg_columns(
    column_names: &[Symbol],
    n_pos: usize,
    named_keys: &[Symbol],
) -> Result<Vec<Symbol>, RelationArgError> {
    let mut bound: Vec<Symbol> = Vec::with_capacity(n_pos + named_keys.len());
    // Positional args bind columns left to right.
    for i in 0..n_pos {
        let name = *column_names
            .get(i)
            .ok_or(RelationArgError::PositionalOutOfRange(i))?;
        bound.push(name);
    }
    // Named args bind the column of the matching name.
    for &k in named_keys {
        if !column_names.contains(&k) {
            return Err(RelationArgError::UnknownParam(k));
        }
        if bound.contains(&k) {
            return Err(RelationArgError::DoubleBind(k));
        }
        bound.push(k);
    }
    Ok(bound)
}

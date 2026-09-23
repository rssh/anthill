//! WI-376: expression-carried projection elimination — receiver paths, projected
//! members and rigid projections.

use super::*;

// ── WI-376: expression-carried projection elimination ──────────

/// WI-1059 — does a type [`Value`] contain a `Var::Rigid` anywhere? The predicate behind
/// ONE invariant: **a skolem minted by the body check may not be written into the stored
/// tree.** Rigids are minted per body check ([`rigidify_op_type_params`], WI-392/WI-424,
/// and [`rigidify_unwritten_sort_params`]), so a stored node holding one is stale as soon
/// as the pass ends — and a second `type_check_sorts` over the same KB then compares last
/// pass's skolem against this pass's, which render identically and are not equal.
///
/// Structural rather than a head test, for the reason [`value_contains_projection`] gives:
/// the rigid that matters sits in a BINDING (`List[T = ?T]`), never at the head.
///
/// WI-1079 — THIS FUNCTION USED TO OPEN WITH ITS OWN CARRIER MATCH, two hand-rolled arms
/// testing `Value::Term{Var::Rigid}` and `Value::Var(Var::Rigid)` before delegating the rest
/// to [`extract_type`]. They were there because `extract_type` could not answer: a bare
/// variable classified as `TypeExtractor::Error`, so the ONE question this predicate asks had
/// to be asked twice, once per carrier, outside the boundary whose job it is. With
/// [`TypeExtractor::Skolem`] the arm below IS the answer, on both carriers and at every depth,
/// and the duplicate is gone. It is the smallest demonstration of what the ticket is for.
pub(super) fn value_contains_rigid(kb: &KnowledgeBase, ty: &Value) -> bool {
    // A FLEX variable is the other half of the distinction this predicate turns on: it is
    // not a skolem, it is what a skolem is minted INSTEAD of, and a stored tree holding one
    // is fine — [`type_any_part`] answers `false` for it, as for every leaf.
    type_any_part(kb, ty, &|te| {
        matches!(te, TypeExtractor::Skolem { .. }).then_some(true)
    })
}

/// WI-20260923-32XFQ — does any PART of type `ty` answer yes? The one walk under the
/// "does this type carry X" predicates read through [`extract_type`] — so a
/// `Value::Node` type is walked exactly as a term is — which each spelled for itself:
/// [`value_contains_rigid`] and [`contains_projection`].
///
/// `probe` is asked of every node FIRST: `Some(answer)` is the answer and STOPS the
/// descent there, `None` descends. The children are every type position a node has —
/// parameterized bindings; an arrow's parameter, result and effects; named-tuple fields;
/// an effect row's inner expression; an expression-carried projection's value; a rigid
/// projection's subject; a ∀'s body AND its context (WI-1083: its binders are flexible by
/// construction, so they are not; WI-20260904-50B2K (c): a constraint is a type, so it
/// is). Every other form is a leaf and answers `false`.
///
/// THE STOP IS WHAT LETS ONE WALK SERVE BOTH, and it is not a formality: the projection
/// walk answers the two projection forms at the node — `x.E` always, `P.Key` per its
/// flag — and so never reaches their children, where the rigid walk (whose probe answers
/// only a skolem) descends through both. Asked through `None`, a projection question
/// would newly look inside a `P.Key`'s subject: an answer changing, which WI-20260923-
/// N3W68 #6 settled by measurement the other way.
pub(super) fn type_any_part(
    kb: &KnowledgeBase,
    ty: &Value,
    probe: &impl Fn(&TypeExtractor) -> Option<bool>,
) -> bool {
    let te = extract_type(kb, ty);
    if let Some(answer) = probe(&te) {
        return answer;
    }
    let within = |v: &Value| type_any_part(kb, v, probe);
    match te {
        TypeExtractor::Parameterized { bindings, .. } => bindings.iter().any(|(_, v)| within(v)),
        TypeExtractor::Arrow {
            param,
            result,
            effects,
            arity: _,
        } => within(&param) || within(&result) || within(&effects),
        TypeExtractor::NamedTuple(fields) => fields.iter().any(|(_, v)| within(v)),
        TypeExtractor::EffectsRows(e) => within(&e),
        TypeExtractor::ExprCarried { value, .. } => within(&value),
        TypeExtractor::RigidTypeProjection { subject, .. } => within(&subject),
        TypeExtractor::PolyType { context, body, .. } => {
            within(&body) || context.iter().any(within)
        }
        TypeExtractor::Skolem { .. }
        | TypeExtractor::FlexVar { .. }
        | TypeExtractor::Denoted(_)
        | TypeExtractor::SortRef(_)
        | TypeExtractor::TypeVar(_)
        | TypeExtractor::Nothing
        | TypeExtractor::Error => false,
    }
}

/// WI-20260909-S8CBV — does this type carry an EXPRESSION-CARRIED projection (`x.E`)
/// specifically, as opposed to any projection?
///
/// [`value_contains_projection`] answers `true` for a `RigidTypeProjection` too (`P.Key`,
/// WI-428) — a TYPE-headed projection that has been writable in a `requires` chain since
/// long before this ticket. The two refusals this ticket adds must not fire on it: each
/// justifies itself as "narrow by construction, a shape no program could write before",
/// and that argument is only true of the `ExprCarried` half. `/code-review` found the
/// wider predicate under both, where it would have taken away a sort-half supply that
/// used to work. So the REFUSALS ask this and the δ eliminations ask the wide one — they
/// are different questions and the narrow one belongs only to the new verdicts.
///
/// NARROW IN WHAT IT COUNTS, NOT IN WHERE IT LOOKS (WI-20260923-N3W68 #6). This predicate
/// used to be its own walk, and it descended only `Parameterized` and `NamedTuple` while
/// the wide one had since learned `Arrow`, `EffectsRows` and `PolyType` (WI-1083, 50B2K).
/// The exclusion above justifies dropping the `RigidTypeProjection` ANSWER, never a
/// shallower walk, and the shallower walk was reachable: `requires Desc[T = {x.E}]` hides
/// its `x.E` in an effect row, so both refusals looked straight past it. MEASURED before
/// the fix — a caller forwarding that requirement (`requires Desc[T = {b.E}] = pick(b)`)
/// and a rule body calling `pick` each LOADED CLEAN and then aborted a debug build with
/// `DeferToRequirement: __req_desc not bound in caller frame`, the exact outcome the two
/// refusals exist to prevent. One walk now answers both questions; they differ in the
/// one arm the exclusion names.
pub(super) fn value_contains_expr_carried(kb: &KnowledgeBase, ty: &Value) -> bool {
    contains_projection(kb, ty, false)
}

/// WI-376: does a type [`Value`] contain an expression-carried projection
/// (`ExprCarried`) anywhere in its structure? Carrier-agnostic (reads via
/// [`extract_type`], so a `Value::Node` parameterized type is walked too). Used both
/// to GATE the per-call elimination (skip the work for the >99% of signatures with no
/// projection) and to DETECT a projection nested inside a denoted-bearing `Value::Node`
/// — which the Node-carrier rewrite does not yet handle, so it is a loud error rather
/// than a silent leak.
///
/// A `RigidTypeProjection` (`P.Key`, WI-428) answers `true` too; the narrower
/// [`value_contains_expr_carried`] is the question that excludes it.
pub(super) fn value_contains_projection(kb: &KnowledgeBase, ty: &Value) -> bool {
    contains_projection(kb, ty, true)
}

/// The one walk behind [`value_contains_projection`] (`rigid_counts`) and
/// [`value_contains_expr_carried`] (not) — see each for its question.
///
/// Both projection forms are answered AT THE NODE, and neither is descended into (see
/// [`type_any_part`]'s stop). The ∀ is walked body and context: an eta'd member's ∀ body
/// carries its receiver projections (`mapElems(xs: List, f: (x: xs.T) -> Dst)`, WI-1083),
/// and this reader DECIDES whether `eliminate_node_projections` is asked to rewrite the
/// node, so a projection hiding in a constraint (WI-20260904-50B2K (c)) would never be
/// eliminated — the assert guarding that path is debug-only. A logical variable of either
/// kind is a leaf: no children to hide a projection in, and not one.
fn contains_projection(kb: &KnowledgeBase, ty: &Value, rigid_counts: bool) -> bool {
    type_any_part(kb, ty, &|te| match te {
        TypeExtractor::ExprCarried { .. } => Some(true),
        TypeExtractor::RigidTypeProjection { .. } => Some(rigid_counts),
        _ => None,
    })
}

/// WI-398: the head parameter symbol of an expression-carried projection's RECEIVER
/// path. A single value reference `Ref(s)` is `s`; a field-access chain `s.f.g` bottoms
/// out in `Ref(s)`, so the head is `s`. Any other shape (not a value-reference path) is
/// `None`. Mirrors the descent in [`resolve_receiver_path_type`], returning the path's
/// bottom symbol rather than its type — the first of [`receiver_path_segs`], which
/// walks the same descent.
fn receiver_path_head_sym(kb: &KnowledgeBase, receiver: &Value) -> Option<Symbol> {
    // A path is never empty when present: its base case is `[head]`.
    receiver_path_segs(kb, receiver).map(|segs| segs[0])
}

/// WI-400 increment C: the full receiver-path SEGMENTS of a projection receiver value, in
/// outermost-head-first order — `Ref(s)` ⟹ `[s]`, `s.provider` (a `DotApply` chain) ⟹
/// `[s, provider]`. The path twin of [`receiver_path_head_sym`] (which returns only the
/// head). `None` for a non-value-reference receiver. Used by the eager-let-alias
/// canonicalization to rewrite a receiver whose head is aliased.
fn receiver_path_segs(kb: &KnowledgeBase, receiver: &Value) -> Option<Vec<Symbol>> {
    if let Some(head) = extract_sort_ref_sym(kb, receiver) {
        return Some(vec![head]);
    }
    if let Value::Node(occ) = receiver {
        if let Some(Expr::DotApply {
            receiver: base,
            name,
            pos_args,
            named_args,
        }) = occ.as_expr()
        {
            if pos_args.is_empty() && named_args.is_empty() {
                let mut segs = receiver_path_segs(kb, &Value::Node(std::rc::Rc::clone(base)))?;
                segs.push(*name);
                return Some(segs);
            }
        }
    }
    None
}

/// WI-400 increment C: the stable receiver PATH a `let`-bound value occurrence denotes,
/// if any. A value reference (`let y = z`) ⟹ `[z]`; a field-access chain
/// (`let y = s.provider`) ⟹ `[s, provider]`. Returns `None` for anything NOT a stable
/// path — a call (`let y = f()`), a literal, a constructor — so an unstable binding mints
/// its OWN neutral receiver rather than aliasing (the §4.1 stability rule). The occurrence
/// twin of [`receiver_path_segs`] (which reads a type-level receiver value).
pub(super) fn stable_receiver_path(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
) -> Option<Vec<Symbol>> {
    // A value reference is an `Expr::VarRef` (an unqualified let/lambda/param binder
    // read) or a `Ref`/`Ident` (a resolved reference); all denote a stable name.
    if let Some(name) = leaf_var_ref(occ) {
        return Some(vec![name]);
    }
    match occ.as_expr()? {
        Expr::DotApply {
            receiver,
            name,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => {
            let name = *name;
            let mut segs = stable_receiver_path(kb, receiver)?;
            segs.push(name);
            Some(segs)
        }
        // WI-509: the typer's `?x.field` rewrite — `field_access(receiver,
        // "field")`. The same stable path as the surface `DotApply`: recurse the
        // receiver and append the field-name segment. Without this, the WI-506
        // effect re-key (which reads the projection HEAD off a `Cell.set` arg to
        // map `Modify[c]` → `Modify[arg]`) loses the head once a field-projection
        // op body is re-typed from its already-rewritten form, surfacing a
        // spurious undeclared `Modify`.
        Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        } if named_args.is_empty()
            && pos_args.len() == 2
            && kb.try_resolve_symbol(dt::qualified(dt::FIELD_ACCESS)) == Some(*functor) =>
        {
            let field_name = match pos_args[1].as_expr() {
                Some(Expr::Const(Literal::String(s))) => s.clone(),
                _ => return None,
            };
            let mut segs = stable_receiver_path(kb, &pos_args[0])?;
            segs.push(kb.intern(&field_name));
            Some(segs)
        }
        _ => None,
    }
}

/// WI-20260823-4GBQV — the PLACE an ARGUMENT names, for the effect re-key: the head
/// symbol a callee's `Modify[<param>]` should be re-keyed ONTO, or `None` when the
/// argument denotes no place at all.
///
/// NOT [`stable_receiver_path`] WIDENED, and the separation is the point. That function
/// answers the WI-400 §4.1 question "what stable path does this `let` binding ALIAS",
/// whose whole job is to return `None` for a call so an unstable binding mints its own
/// neutral receiver. A nullary CONSTRUCTOR is not a stable alias of anything — it is a
/// global constant — so widening it there would change the alias rule for a reader that
/// never asked this question. One source, two questions; this one gets its own name.
///
/// The two shapes, and both are the SAME nullary-name-of-a-value category the loader
/// admits into a `Modify` target ([`KnowledgeBase::is_ambient_resource_name`]):
///   * a stable path — a variable (`Cell.set(k, 1)`), or a field projection whose HEAD
///     is one (`Cell.set(c.rep, 1)` ⟹ `c`, WI-506 coverage). Delegated, unchanged.
///   * a nullary CONSTRUCTOR APPLICATION — `set(counter(), n)`. The paren-less spelling
///     already arrives as `Expr::Ref`/`Ident` and rides the path above (WI-592 records
///     `c ↦ Green` for exactly that); `counter()` parses as an `Expr::Apply` with empty
///     argument lists, which no shape above matches. Both spellings denote one term
///     (the WI-511 `Fn{c,[],[]}`→`Ref(c)` alloc canon), so admitting only one of them
///     would make the idiom depend on its parentheses.
pub(super) fn arg_place_head(kb: &mut KnowledgeBase, occ: &Rc<NodeOccurrence>) -> Option<Symbol> {
    if let Some(head) = stable_receiver_path(kb, occ).and_then(|p| p.into_iter().next()) {
        // GATED AGAINST WHAT THE DECLARATION REFUSES. `stable_receiver_path` answers a
        // different question (§4.1 alias stability) and takes any bare name, CONSTRUCTORS
        // included — so ungated it re-keyed `set(wrap, n)` onto a field-bearing
        // constructor and `set(Slot, n)` onto an eponymous one, minting
        // `Modify[T = wrap]` / `Modify[T = Slot]`: labels whose only lawful declaration is
        // a load error, leaving the program unwritable and the diagnostic pointing at
        // neither problem. A head this predicate rejects falls through to
        // [`unrekeyed_modify_argument`], which names the caller's own expression.
        //
        // The gate is the NEGATIVE test and not "does this name a place" — see
        // [`KnowledgeBase::is_unplaceable_constructor`] for why a binder with no declared
        // kind must stay admitted.
        if kb.is_unplaceable_constructor(head) {
            return None;
        }
        return Some(head);
    }
    nullary_constructor_arg(kb, occ)
}

/// WI-20260823-4GBQV — a call whose argument for a MODIFIED parameter names no PLACE,
/// reported against the CALLER's own expression.
///
/// THE DEFECT THIS REPLACES. `Cell.set` declares `effects Modify[c]`; the re-key rewrites
/// `c` to whatever the argument names. When the argument names nothing —
/// `Cell.set(mk(), 1)` — the label survived un-re-keyed and surfaced far away as
/// `undeclared effect: Modify[T = c]`, naming `Cell.set`'s parameter: a symbol that
/// appears nowhere in the caller's text. Worse where the caller happens to own a
/// parameter spelled `c` too, since the two are different symbols in different scopes and
/// the message then read `expected declared: [Modify[T = c]], got undeclared effect:
/// Modify[T = c]` — the same rendering on both sides of a mismatch.
///
/// THE CONDITION IS THE EFFECT, NOT A PROXY FOR IT: a `Modify` in the atoms that SURVIVED
/// re-keying and guard discharge, whose target still names one of the CALLEE's own
/// parameters. That is what a leak IS — the re-key rewrites exactly the parameters whose
/// arguments named a place, so a callee parameter still standing here got none. Asking
/// instead "does the callee DECLARE a `Modify` over a parameter whose argument named no
/// place" is the same verdict on the bare atoms and the WRONG one on a guarded atom
/// (`{Modify[c] :- g}`): a guard refuted at this call site drops the atom, so it is never
/// incurred, and refusing it would refuse a correct program. Measured both ways —
/// `touch(mk(), false)` under a refuted guard loads, `touch(mk(), true)` is refused.
///
/// WHY A REFUSAL AND NOT A COARSENING. There is no place to coarsen ONTO: `Env` maps
/// resource NAMES to terms (kernel-language.md §5.6), and `mk()`'s result is a fresh
/// value per call, so no name denotes it. The repair is to give it one — `let x = mk()`
/// then `Cell.set(x, 1)`, which re-keys through the ordinary variable arm — and the
/// message prescribes exactly that. (Driven, not assumed: the `let` form loads.)
///
/// REPORTS ONLY WHERE IT CAN POINT. `placeless` carries the argument occurrence per
/// parameter, recorded where the two re-key maps DECLINE, so it is the complement of what
/// they hold rather than a second opinion about which shapes count. A surviving callee
/// parameter with no entry there was given no argument at all — an arity fault another
/// pass reports — and this one stays quiet rather than adding a second message about a
/// call the author has not finished writing.
pub(super) fn unrekeyed_modify_argument(
    kb: &mut KnowledgeBase,
    op: &OperationInfoFull,
    fn_sym: Symbol,
    incurred: &[Value],
    placeless: &HashMap<Symbol, Rc<NodeOccurrence>>,
    span: Option<Span>,
) -> Option<TypeError> {
    let modify = kb.try_resolve_symbol("anthill.prelude.Modify");
    modify?;
    let t = kb.intern("T");
    let label_key = kb.intern("label");
    for e in incurred {
        // Peel here and NOT at the caller: discharge has already run, so a `guarded`
        // wrapper still standing is an atom that IS incurred, and its label is the one to
        // judge. (An `absent` atom is a constraint and carries no `Modify` target of the
        // callee's, so peeling it changes nothing.)
        let label = peel_effect_atom(kb, e, label_key);
        if !effect_is_modify(kb, &label, modify) {
            continue;
        }
        let Some(target) = label.named_arg(kb, t).or_else(|| label.pos_arg(kb, 0)) else {
            continue;
        };
        let Some(param) = denoted_place_head_sym(kb, &target) else {
            continue; // not a place at all — `check_modify_targets` owns that refusal.
        };
        if !op.params.iter().any(|(p, _)| *p == param) {
            continue; // re-keyed onto the caller's own vocabulary, or `result`. Fine.
        }
        let Some(arg) = placeless.get(&param) else {
            continue; // no argument to point at — see the doc.
        };
        let reason = placeless_arg_reason(kb, arg);
        return Some(TypeError::Other {
            site: TypeError::here(),
            span,
            context: TypeErrorContext::OperationArgument {
                op_name: fn_sym,
                param,
            },
            expected: format!(
                "an argument naming a PLACE, because `{}` declares `Modify[{}]` over this \
                 parameter",
                kb.qualified_name_of(fn_sym),
                kb.local_name_of(param),
            ),
            actual: format!("{reason}, so it names no resource."),
        });
    }
    None
}

/// WI-20260823-4GBQV — how to NAME the caller's own argument in [`unrekeyed_modify_-
/// argument`]'s message, and WHY it names no resource. There is no expression printer at
/// this layer, so the shape plus the head name is as close to the author's text as this
/// site can get — and it is the half that matters, since the whole defect was naming the
/// CALLEE's parameter instead.
///
/// TWO REASONS, because they are two different mistakes with two different repairs. A
/// CALL or a construction produces a FRESH value per evaluation, which no name denotes —
/// bind it. A bare NAME that is not a place is a CONSTRUCTOR the declaration side would
/// refuse in the same slot (a field-bearing one, or an eponymous one that is its own sort,
/// WI-926) — there is nothing to bind, the name simply is not a resource. Telling an
/// author to `let`-bind `wrap` would send them to a line whose repair does not load.
fn placeless_arg_reason(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> String {
    const FRESH: &str = "produces a fresh value rather than naming a slot, so the effect \
                         has nothing to be re-keyed onto. Bind it first (`let x = …`) and \
                         pass `x`, or pass a parameter, a field path off one, or a nullary \
                         constructor naming an ambient resource";
    let named = |what: &str, sym: Symbol| {
        format!(
            "the name `{}`, which is {} and not a place — kernel-language.md §5.6 admits a \
             parameter, `result`, a field path off one, a value-producing zero-arg \
             operation, or a NULLARY constructor naming an ambient resource. The same name \
             is refused in a `Modify` target where it is declared, so no row could name \
             this effect either",
            kb.qualified_name_of(sym),
            what,
        )
    };
    let bare = |sym: Symbol| {
        if kb.is_ambient_resource_name(sym) {
            // Not reachable through the place gate — kept loud rather than silent.
            named("not admitted here", sym)
        } else if kb.has_kind(sym, crate::intern::SymbolKind::Sort) {
            named("its own sort (an eponymous constructor)", sym)
        } else if kb.entity_field_names(sym).is_some_and(|f| !f.is_empty()) {
            named("a constructor taking fields", sym)
        } else {
            named("not a value place", sym)
        }
    };
    match occ.as_expr() {
        Some(Expr::Ref(s)) | Some(Expr::Ident(s)) => bare(*s),
        Some(Expr::VarRef { name }) => bare(*name),
        Some(Expr::Apply { functor, .. }) => {
            format!(
                "the call `{}(…)`, which {FRESH}",
                kb.qualified_name_of(*functor)
            )
        }
        Some(Expr::Constructor { name, .. }) => {
            format!(
                "the constructor `{}(…)`, which {FRESH}",
                kb.qualified_name_of(*name)
            )
        }
        // Empty argument lists make it a FIELD ACCESS, not a call — and reaching here at
        // all means its receiver is the unstable half: [`stable_receiver_path`] takes
        // every `.field` chain whose head is a name, so what is left is a projection off
        // a call or a constructor (`wrap(rep: k).rep`).
        Some(Expr::DotApply {
            name,
            pos_args,
            named_args,
            ..
        }) if pos_args.is_empty() && named_args.is_empty() => {
            format!(
                "the field path `.{}`, whose receiver {FRESH}",
                kb.local_name_of(*name)
            )
        }
        Some(Expr::DotApply { name, .. }) => {
            format!("the call `.{}(…)`, which {FRESH}", kb.local_name_of(*name))
        }
        Some(Expr::HoApply { .. }) => format!("an applied function value, which {FRESH}"),
        Some(Expr::Const(_)) => format!("a literal, which {FRESH}"),
        Some(Expr::Match { .. }) => format!("a `match` expression, which {FRESH}"),
        Some(Expr::If { .. }) => format!("an `if` expression, which {FRESH}"),
        Some(Expr::Let { .. }) => format!("a `let` expression, which {FRESH}"),
        // Loud rather than silent: an unnamed shape still reports, and says so.
        _ => format!("this argument expression, which {FRESH}"),
    }
}

/// WI-20260823-4GBQV — the SYMBOL at the HEAD of a `denoted` place (`denoted(Ref(c))` ⟹
/// `c`, `denoted(c.contents)` ⟹ `c`), on either carrier. `None` for a denoted carrying
/// something with no name at its head (a literal) and for a non-denoted type. The symbol
/// twin of [`denoted_name`], which reads the STRING a denoted carries.
///
/// THE HEAD AND NOT THE WHOLE PATH, because that is the resource: `Modify[c]` covers
/// `Modify[c.rep]` (WI-506 / proposal 037's effect-row convention), so the parameter a
/// field path is rooted at is the one an argument re-keys. Reading only the bare `Ref`
/// left `poke(d: Box) effects Modify[d.contents]` leaking `Modify[T = d.contents]` — the
/// callee's own parameter, through a spelling one segment longer than the check looked.
/// Found by `/code-review`.
fn denoted_place_head_sym<V: TermView>(kb: &KnowledgeBase, v: &V) -> Option<Symbol> {
    let TypeExtractor::Denoted(inner) = extract_type(kb, v) else {
        return None;
    };
    match &inner {
        Value::Term { id } => term_place_head_sym(kb, *id),
        Value::Node(occ) => occ_place_head_sym(occ),
        _ => None,
    }
}

/// The head symbol of a term-carried place path — `Ref(c)` / `Ident(c)`, the binder
/// reference `var_ref(name: Ref(c))`, or a `field_access` chain rooted at one. See
/// [`denoted_place_head_sym`].
///
/// NAMES THE FUNCTOR rather than descending into any application's first argument, which
/// is the same gate [`stable_receiver_path`] puts on its own `.field` descent. Ungated,
/// a `denoted` carrying an unrelated application would hand back that application's arg-0
/// head AS THE PLACE — reporting a resource nobody named, or swallowing a real leak behind
/// an arg-0 head that is not a parameter. No fixture reaches it (a `denoted` target should
/// only ever be a place path), so this is the loud-over-silent direction rather than a
/// live bug; `/code-review` raised it.
///
/// WI-20260923-N3W68 (#15) — THE SAME HEADS AS ITS OCCURRENCE TWIN [`occ_place_head_sym`],
/// which reads `Ident` and `VarRef` too; this read a `Ref` alone. The `var_ref` arm is that
/// twin's `Expr::VarRef` in its term spelling ([`KnowledgeBase::make_var_ref_term`], the
/// shape WI-552 emits for a binder). A head this declines is SKIPPED by
/// [`unrekeyed_modify_argument`] — "not a place at all" — so a gap here is a silent pass,
/// not a refusal. MEASURED unreachable before the arms: a probe on the declined shapes and
/// on the consumer's skip fired zero times across the workspace suite.
pub(super) fn term_place_head_sym(kb: &KnowledgeBase, id: TermId) -> Option<Symbol> {
    match kb.get_term(id) {
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        Term::Fn {
            functor, pos_args, ..
        } if !pos_args.is_empty()
            && kb.try_resolve_symbol(dt::qualified(dt::FIELD_ACCESS)) == Some(*functor) =>
        {
            term_place_head_sym(kb, pos_args[0])
        }
        Term::Fn {
            functor,
            named_args,
            ..
        } if kb.try_resolve_symbol("anthill.reflect.Expr.var_ref") == Some(*functor) => {
            var_ref_name_symbol(kb, named_args)
        }
        _ => None,
    }
}

/// The head symbol of an occurrence-carried place path. See [`denoted_place_head_sym`].
fn occ_place_head_sym(occ: &Rc<NodeOccurrence>) -> Option<Symbol> {
    leaf_var_ref(occ).or_else(|| match occ.as_expr()? {
        Expr::DotApply { receiver, .. } => occ_place_head_sym(receiver),
        _ => None,
    })
}

/// WI-20260823-4GBQV — the constructor symbol of a NULLARY constructor application
/// (`counter()`), if that is what `occ` is. See [`arg_place_head`].
///
/// Gated on the SAME [`KnowledgeBase::is_ambient_resource_name`] the loader gates the
/// declaration on, not on `is_constructor_symbol`: a re-key onto a name the declaration
/// cannot spell produces a label no author can declare, which is the un-re-keyed leak in
/// another spelling. The written argument list must be empty too — `wrap()` on a
/// field-bearing entity is an arity error the caller reports, not a place.
///
/// BOTH APPLICATION VARIANTS, and reading only one is how this arrived not working: the
/// loader classifies `counter()` as an [`Expr::Constructor`] once the name is a known
/// entity and as an [`Expr::Apply`] where it is not yet resolved to one, so a match on
/// `Apply` alone left the ticket's own spelling leaking `Modify[T = target]` while the
/// paren-less `counter` (an `Expr::Ref`, the [`stable_receiver_path`] arm) worked.
fn nullary_constructor_arg(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> Option<Symbol> {
    let (functor, pos_args, named_args) = match occ.as_expr()? {
        Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        } => (functor, pos_args, named_args),
        Expr::Constructor {
            name,
            pos_args,
            named_args,
            ..
        } => (name, pos_args, named_args),
        _ => return None,
    };
    (pos_args.is_empty() && named_args.is_empty() && kb.is_ambient_resource_name(*functor))
        .then_some(*functor)
}

/// WI-400 increment C (eager let-alias): rewrite a projection type's receiver to its
/// CANONICAL path BEFORE elimination, when its head is a let-aliased variable — so `y.M`
/// (`let y = z`) carries the same receiver as `z.M` and the ζ arm equates them
/// (`let y = z ⟹ y.M ≡ z.M`, the Scala divergence). A no-op when `aliases` is empty (the
/// common case) or the receiver head is not aliased. Handles the TOP-LEVEL projection
/// (the let-annotation shape `let k: y.M`); a projection NESTED inside a parameterized /
/// denoted type is left unchanged — the same carrier-promotion boundary `eliminate_type_-
/// projections` already documents as a follow-on.
pub(super) fn canonicalize_projection_receivers(
    kb: &mut KnowledgeBase,
    aliases: &HashMap<Symbol, Vec<Symbol>>,
    ty: &Value,
    span: crate::span::SourceSpan,
) -> Value {
    if aliases.is_empty() {
        return ty.clone();
    }
    let TypeExtractor::ExprCarried { value, member } = extract_type(kb, ty) else {
        return ty.clone();
    };
    let Some(segs) = receiver_path_segs(kb, &value) else {
        return ty.clone();
    };
    let (head, fields) = segs.split_first().expect("receiver path is non-empty");
    let Some(canon_head) = aliases.get(head) else {
        return ty.clone();
    };
    // Canonical receiver path = the head's alias path, then the trailing field segments.
    let mut canon_segs = canon_head.clone();
    canon_segs.extend_from_slice(fields);
    build_projection_from_segs(kb, &canon_segs, member, span)
}

/// WI-400 increment C: build a projection type [`Value`] from a receiver path's segments
/// plus the projected `member`, mirroring the loader's two carriers
/// (`try_expr_carried_projection`): a single-segment receiver rides the ground
/// `Fn{ExprCarried, value: Ref(s), member: Ref(M)}` term; a compound receiver rides the
/// `TypeNode::ExprCarried` Node over a `DotApply` chain. `span` is the originating
/// annotation's span (the canonical receiver has no source span of its own); `owner` is
/// `None`.
fn build_projection_from_segs(
    kb: &mut KnowledgeBase,
    segs: &[Symbol],
    member: Symbol,
    span: crate::span::SourceSpan,
) -> Value {
    debug_assert!(!segs.is_empty(), "projection receiver path is non-empty");
    if segs.len() == 1 {
        let receiver_term = kb.alloc(Term::Ref(segs[0]));
        return Value::term(kb.make_expr_carried(receiver_term, member));
    }
    let mut receiver = NodeOccurrence::new_expr(Expr::Ref(segs[0]), span, None);
    for &field in &segs[1..] {
        receiver = NodeOccurrence::new_expr(
            Expr::DotApply {
                receiver,
                name: field,
                pos_args: Vec::new(),
                named_args: Vec::new(),
            },
            span,
            None,
        );
    }
    Value::Node(kb.make_expr_carried_occ(receiver, member, span, None))
}

/// WI-398: collect the receiver-head symbols of every expression-carried projection
/// (`ExprCarried`) in a type [`Value`] — the parameters this type PROJECTS. A single-ref
/// `s.M` contributes `s`; a compound `s.f.M` contributes the chain's bottom head `s`.
/// Carrier-agnostic (walks via [`extract_type`], so a `Value::Node` parameterized type
/// is descended too). Builds the cross-parameter dependency graph in
/// [`param_projection_cycle`].
pub(super) fn collect_projection_receivers(kb: &KnowledgeBase, ty: &Value, out: &mut Vec<Symbol>) {
    match extract_type(kb, ty) {
        TypeExtractor::ExprCarried { value, .. } => {
            if let Some(head) = receiver_path_head_sym(kb, &value) {
                out.push(head);
            }
        }
        TypeExtractor::Parameterized { bindings, .. } => {
            for (_, v) in &bindings {
                collect_projection_receivers(kb, v, out);
            }
        }
        TypeExtractor::Arrow {
            param,
            result,
            effects,
            arity: _,
        } => {
            collect_projection_receivers(kb, &param, out);
            collect_projection_receivers(kb, &result, out);
            collect_projection_receivers(kb, &effects, out);
        }
        TypeExtractor::NamedTuple(fields) => {
            for (_, v) in &fields {
                collect_projection_receivers(kb, v, out);
            }
        }
        TypeExtractor::EffectsRows(e) => collect_projection_receivers(kb, &e, out),
        // WI-428: a rigid type-receiver projection has a TYPE subject, not a value
        // parameter — it contributes no cross-parameter dependency edge.
        TypeExtractor::RigidTypeProjection { .. }
        // A logical variable is a leaf and carries no receiver.
        | TypeExtractor::FlexVar { .. }
        | TypeExtractor::Skolem { .. }
        | TypeExtractor::Denoted(_)
        | TypeExtractor::SortRef(_)
        | TypeExtractor::TypeVar(_)
        | TypeExtractor::Nothing
        | TypeExtractor::Error => {}
        // WI-1083: the receivers a ∀ projects are its body's — quantifying a type
        // hides no projection, and `value_contains_projection` above descends the same
        // child, so the gate and the collector agree on what they can see.
        // WI-20260904-50B2K part (c): the CONTEXT's receivers are collected with the
        // body's — the sibling of the two predicates above, and one owner of the answer.
        TypeExtractor::PolyType { context, body, .. } => {
            collect_projection_receivers(kb, &body, out);
            for c in &context {
                collect_projection_receivers(kb, c, out);
            }
        }
    }
}

/// WI-398: detect a cyclic CROSS-PARAMETER projection in an operation signature. Param
/// `q` depends on param `p` when `q`'s declared type projects `p` via an `ExprCarried`
/// receiver (`q: p.M`, `q: p.f.M`). The synthesis order is a topological order of those
/// edges; a cycle (`f(a: b.T, b: a.T)`, or the length-1 self-projection `f(a: a.T)`) has
/// NO synthesis order, so the signature is ill-formed — a loud error at LOAD per the
/// projection's definitional content (design path-dependent-types.md §6, WI-398).
/// Returns the cyclic parameter symbols (in cycle order) when the dependencies form a
/// cycle, else `None`.
pub(super) fn param_projection_cycle(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
) -> Option<Vec<Symbol>> {
    // Fast path: no parameter type carries a projection ⇒ no edges ⇒ no cycle.
    if !params.iter().any(|(_, t)| value_contains_projection(kb, t)) {
        return None;
    }
    let sym_to_idx: HashMap<Symbol, usize> = params
        .iter()
        .enumerate()
        .map(|(i, (s, _))| (*s, i))
        .collect();
    // prereqs[q] = the param indices q's type projects (its receivers that are params).
    let mut prereqs: Vec<Vec<usize>> = vec![Vec::new(); params.len()];
    for (q, (_, ty)) in params.iter().enumerate() {
        let mut recv: Vec<Symbol> = Vec::new();
        collect_projection_receivers(kb, ty, &mut recv);
        for r in recv {
            if let Some(&p) = sym_to_idx.get(&r) {
                if !prereqs[q].contains(&p) {
                    prereqs[q].push(p);
                }
            }
        }
    }
    // DFS cycle detection (0 = unvisited, 1 = on the current path, 2 = done).
    let mut color = vec![0u8; params.len()];
    let mut stack: Vec<usize> = Vec::new();
    for start in 0..params.len() {
        if color[start] == 0 {
            if let Some(cycle) = dfs_projection_cycle(start, &prereqs, &mut color, &mut stack) {
                return Some(cycle.into_iter().map(|i| params[i].0).collect());
            }
        }
    }
    None
}

/// DFS helper for [`param_projection_cycle`]: returns the cycle (param indices in path
/// order) when a back-edge to a node already on the current path is found.
fn dfs_projection_cycle(
    u: usize,
    prereqs: &[Vec<usize>],
    color: &mut [u8],
    stack: &mut Vec<usize>,
) -> Option<Vec<usize>> {
    color[u] = 1;
    stack.push(u);
    for &v in &prereqs[u] {
        if color[v] == 1 {
            // Back-edge to a node on the current path: the cycle is the stack suffix
            // from v's first occurrence onward.
            let pos = stack
                .iter()
                .position(|&x| x == v)
                .expect("on-path node is on the stack");
            return Some(stack[pos..].to_vec());
        }
        if color[v] == 0 {
            if let Some(cycle) = dfs_projection_cycle(v, prereqs, color, stack) {
                return Some(cycle);
            }
        }
    }
    stack.pop();
    color[u] = 2;
    None
}

/// WI-376: replace every expression-carried projection (`s.T` / `s.Sort`) in a type
/// [`Value`] by projecting the RECEIVER param's argument type. `arg_types` maps each
/// operation parameter symbol to the inferred type of the argument bound to it (built
/// in [`check_apply_iter`]'s argument loops). This is the synthesis-time discharge of
/// the projection constraint — the arguments are already synthesized, so the receiver's
/// static type is known. A projection whose receiver is not an argument-bound
/// parameter, names a member the receiver's concrete sort does not declare, or whose
/// member is not concretely known (a bare / abstract receiver), is a loud
/// [`TypeError`] — never a silent fresh var, which would unsoundly absorb any demand
/// downstream. Non-projection types pass through unchanged.
pub(super) fn eliminate_type_projections(
    kb: &mut KnowledgeBase,
    ty: &Value,
    arg_types: &HashMap<Symbol, Value>,
    arg_syms: Option<&HashMap<Symbol, Symbol>>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<Value, TypeError> {
    match ty {
        Value::Term { id: t, .. } => {
            // WI-475: a TOP-LEVEL single-ref `ExprCarried` (`effects s.E`, or a projection-
            // typed return `-> s.Sort`) may project to a `Value::Node` (e.g. the effect row
            // `{Modify[p]}`) — representable here (the result IS the whole eliminated value),
            // unlike a projection NESTED in a `Term` tree (which `rewrite_term_projections`
            // cannot hold mid-tree). Return the projected `Value` directly so the effect-row
            // / return Node threads to the caller (the undeclared-effect check then fires).
            if matches!(type_head(kb, &TermIdView(*t)), TypeHead::ExprCarried) {
                return eliminate_expr_carried_projection(kb, *t, arg_types, arg_syms, ctx, span);
            }
            Ok(Value::term(rewrite_term_projections(
                kb, *t, arg_types, arg_syms, ctx, span,
            )?))
        }
        Value::Node(occ) => {
            // WI-397: a top-level COMPOUND-receiver projection (`a.b.T`) rides a
            // `TypeNode::ExprCarried` Node carrier (its receiver is a field-access
            // occurrence). Resolve the receiver path's static type and project the
            // member — the Node twin of the `Value::Term` path above.
            if let TypeExtractor::ExprCarried { value, member } = extract_type(kb, ty) {
                return match resolve_compound_projection(kb, &value, member, arg_types, ctx, span)?
                {
                    ProjResult::Grounded(v) => Ok(v),
                    // WI-400: abstract receiver, member declared — keep the original
                    // compound `ExprCarried` Node as the rigid neutral. WI-459 NOTE: unlike
                    // the single-`Ref` `Value::Term` path, this compound (`a.b.T`) neutral is
                    // NOT re-keyed to the caller's argument (`arg_syms` is not threaded into
                    // `resolve_compound_projection`). A forwarded compound projection through
                    // a call therefore stays callee-keyed and fails the ζ identity check —
                    // a LOUD over-rejection (sound, never a wrong accept), not a regression
                    // (the compound path never re-keyed). The WI-447 stdlib threading uses
                    // only single-`Ref` receivers (`s`/`xs`/`rest`); compound-receiver
                    // re-keying is a recorded follow-on.
                    ProjResult::Neutral => Ok(ty.clone()),
                };
            }
            // WI-460: a projection nested INSIDE a denoted-bearing `Value::Node` — e.g.
            // `s.T` in the param of a callback arrow `(x: s.T) -> Bool @ {EffP, -Modify[x]}`,
            // or `l.T` in `Stream[T = l.T, E = {Modify[c]}]` — is rewritten THROUGH the Node
            // carrier rather than bailed: descend the occurrence tree, eliminate each
            // projection child against the receiver's argument type (the same discharge the
            // `Value::Term` path does), and rebuild the carrier with the denoted children
            // (`-Modify[x]`, `Modify[c]`) preserved. A Node with no projection is a plain
            // denoted type, returned as-is. An UNSUPPORTED nested shape (a projection inside a
            // `named_tuple` carrier) still bails loudly in the descent — never a silent leak.
            if value_contains_projection(kb, ty) {
                return eliminate_node_projections(kb, occ, arg_types, arg_syms, ctx, span);
            }
            Ok(ty.clone())
        }
        other => Ok(other.clone()),
    }
}

/// WI-460: eliminate expression-carried projections nested INSIDE a denoted-bearing
/// `Value::Node` carrier — an arrow / parameterized / effect-row occurrence that also
/// carries a `denoted` value-in-type, e.g. the callback param `(x: s.T) -> Bool @
/// {EffP, -Modify[x]}` or `Stream[T = l.T, E = {Modify[c]}]`. The Node twin of
/// [`rewrite_term_projections`]'s recursion into `Term::Fn` children: descend the
/// occurrence tree, route each GROUND (`TypeChild::Interned`) child through
/// `rewrite_term_projections` and each NODE child through this function, then rebuild the
/// carrier with the `make_*_occ` builders. A child that GROUNDS from a Node to a concrete
/// `Term` (a compound `a.b.T` reducing to `Int64`) collapses to `TypeChild::Interned` via
/// [`value_to_type_child`]. `denoted` values (`Modify[c]`, `-Modify[x]`) carry no type
/// projection and are returned untouched. A `named_tuple` carrier holding a projection is
/// NOT yet rewritten (its fields ride a `Value`-carried list the `TypeChild` descent does
/// not reach) — it bails loudly, never leaking an un-eliminated projection.
fn eliminate_node_projections(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    arg_types: &HashMap<Symbol, Value>,
    arg_syms: Option<&HashMap<Symbol, Symbol>>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<Value, TypeError> {
    // Eliminate one structural child: a ground term rewrites via the `Term` path; a Node
    // child recurses (and may collapse Node→Term when a compound projection grounds).
    fn elim_child(
        kb: &mut KnowledgeBase,
        c: &TypeChild,
        arg_types: &HashMap<Symbol, Value>,
        arg_syms: Option<&HashMap<Symbol, Symbol>>,
        ctx: &TypeErrorContext,
        span: Option<Span>,
    ) -> Result<TypeChild, TypeError> {
        match c {
            TypeChild::Interned(t) => Ok(TypeChild::Interned(rewrite_term_projections(
                kb, *t, arg_types, arg_syms, ctx, span,
            )?)),
            TypeChild::Node(n) => {
                let v = eliminate_node_projections(kb, n, arg_types, arg_syms, ctx, span)?;
                Ok(value_to_type_child(kb, &v))
            }
        }
    }
    let sp = occ.span;
    let owner = occ.owner;
    match &occ.kind {
        NodeKind::Type(node) => match node {
            // WI-20260904-02ERR: a variable carries no projection to eliminate — and it
            // leaves through the choke point, not as a bare `Value::Node`.
            TypeNode::Var(_) => Ok(crate::kb::node_occurrence::occurrence_as_type_value(occ)),
            TypeNode::Arrow {
                param,
                result,
                effects,
                arity,
            } => {
                let p = elim_child(kb, param, arg_types, arg_syms, ctx, span)?;
                let r = elim_child(kb, result, arg_types, arg_syms, ctx, span)?;
                let e = elim_child(kb, effects, arg_types, arg_syms, ctx, span)?;
                // WI-791: projection elimination REBUILDS the arrow, so it carries
                // the same arity across. This is the path the ticket named as the
                // reverted wrapper's unconfirmed leak (c): `(x: T) -> R` whose slot
                // BECOMES a tuple once `T`/`xs.T` is projected away. It is a
                // non-event now — eliminating a projection rewrites the param TYPE
                // and never the parameter COUNT.
                let arity = arity.clone();
                Ok(Value::Node(
                    kb.make_arrow_occ_child(p, r, e, arity, sp, owner),
                ))
            }
            TypeNode::Parameterized { base, bindings } => {
                let b = elim_child(kb, base, arg_types, arg_syms, ctx, span)?;
                let mut bs: Vec<(Symbol, TypeChild)> = Vec::with_capacity(bindings.len());
                for (s, c) in bindings {
                    bs.push((*s, elim_child(kb, c, arg_types, arg_syms, ctx, span)?));
                }
                Ok(Value::Node(kb.make_parameterized_occ(b, bs, sp, owner)))
            }
            TypeNode::EffectsRows { effects_expr } => {
                let e = elim_child(kb, effects_expr, arg_types, arg_syms, ctx, span)?;
                Ok(Value::Node(kb.make_effects_rows_occ(e, sp, owner)))
            }
            // A `denoted` value-in-type (`Modify[c]`) carries no type projection, but it
            // DOES carry a callee-parameter reference by VALUE. WI-481: re-key it to the
            // caller's argument via `arg_syms` (the same `param_to_arg_sym` rewrite the
            // projection-free return path applies at the call site), so a `Modify[p]`
            // sitting beside a projection in a MIXED return (`Strm[T = s.T, E = {Modify[p]}]`)
            // is re-keyed here too — not left bearing the callee's `p`. No projection
            // inside ⇒ no neutral receiver to corrupt, so re-key unconditionally when a
            // map is present.
            TypeNode::Denoted { .. } => match arg_syms {
                Some(map) => Ok(Value::Node(
                    crate::kb::node_occurrence::substitute_ref_syms_occ(occ, map),
                )),
                None => Ok(Value::Node(Rc::clone(occ))),
            },
            // A nested COMPOUND projection (`a.b.T`) Node — resolve it exactly as the
            // top-level `ExprCarried` arm of `eliminate_type_projections` does (callee-keyed;
            // the WI-459 re-key is single-`Ref` only, see that arm's note).
            TypeNode::ExprCarried { .. } => {
                if let TypeExtractor::ExprCarried { value, member } =
                    extract_type(kb, &Value::Node(Rc::clone(occ)))
                {
                    match resolve_compound_projection(kb, &value, member, arg_types, ctx, span)? {
                        ProjResult::Grounded(v) => Ok(v),
                        ProjResult::Neutral => Ok(Value::Node(Rc::clone(occ))),
                    }
                } else {
                    // An `ExprCarried` carrier whose `member` is not a ground `Ref` is
                    // malformed (the builders always store a ground `Ref` member). Bail
                    // loudly rather than silently passing the projection through — `value_-
                    // contains_projection` already classified this node as projection-bearing.
                    Err(projection_type_error(
                        ctx,
                        span,
                        "a type projection nested in a denoted-bearing type has a non-Ref \
                         projection member (malformed carrier)",
                    ))
                }
            }
            // WI-714: a projection nested in a `named_tuple` carrier — the two-row `join`
            // lambda's param type `(c: r1.T, q: r2.T)`. Its `fields` ride a `Value`-carried
            // list (not `TypeChild` children), so the structural descent above does not
            // reach them; instead READ the fields (`extract_type`), eliminate each field's
            // TYPE (the full dispatcher, so a `Term`-carried single-ref projection `r1.T`
            // and a `Node`-carried one both resolve), and REBUILD the named tuple. An
            // operand projection that cannot resolve still bails loudly inside the per-field
            // elimination — never a silent leak.
            TypeNode::NamedTuple { .. } => {
                let fields = match extract_type(kb, &Value::Node(Rc::clone(occ))) {
                    TypeExtractor::NamedTuple(f) => f,
                    _ => {
                        return Err(projection_type_error(
                            ctx,
                            span,
                            "a named-tuple type carrier did not extract as a named tuple",
                        ))
                    }
                };
                let mut reduced: Vec<(Symbol, Value)> = Vec::with_capacity(fields.len());
                for (name, fty) in fields {
                    let f = eliminate_type_projections(kb, &fty, arg_types, arg_syms, ctx, span)?;
                    reduced.push((name, f));
                }
                Ok(named_tuple_value(kb, &reduced, sp, owner))
            }
            // WI-1083: eliminate inside the quantified body and REBUILD the ∀ —
            // the eta arrow of a member whose signature projects its receiver
            // (`mapElems(xs: List, f: (x: xs.T) -> Dst)`) carries projections under
            // the binders. Elimination rewrites TYPES, never binders, so the binder
            // list crosses unchanged.
            TypeNode::PolyType {
                binders,
                context,
                body,
            } => {
                let b = elim_child(kb, body, arg_types, arg_syms, ctx, span)?;
                // WI-20260904-50B2K part (c): the context crosses UNCHANGED, and that is
                // correct only while it is empty — a constraint is a TYPE, so a projection
                // inside one would need eliminating exactly as the body's does.
                //
                // AND THIS NODE IS NOW ROUTED HERE *BECAUSE OF* THE CONTEXT: the same change
                // widened `value_contains_projection` to look inside it, and that predicate
                // is the one that DECIDES whether a node is handed to this function. So a
                // context-borne projection arrives here by design, and a `debug_assert`
                // alone would carry it un-eliminated into a stored type in release — the
                // silent-in-release shape `check_bare_ref` was corrected for two passes ago.
                // Loud, through the same helper the malformed-`ExprCarried` arm above uses.
                // /code-review found it.
                // THE QUESTION IS WHETHER THE *CONTEXT* HOLDS A PROJECTION, not whether it
                // is non-empty — the first cut asked the second and asserted the first in
                // its own message. What ROUTES a node here is `value_contains_projection`,
                // which the BODY alone satisfies (an eta'd member's ∀ body carrying
                // `(x: xs.T)` is the shape its doc names), so a projection-free context
                // beside a body projection the line above just eliminated would be refused,
                // and told the author the projection was somewhere it is not. A
                // projection-free context passes through unchanged and correctly.
                // /code-review found it.
                if value_list_elements(kb, context)
                    .iter()
                    .any(|c| value_contains_projection(kb, c))
                {
                    return Err(projection_type_error(
                        ctx,
                        span,
                        "a type projection sits in a `PolyType` context, which the \
                         elimination does not yet rewrite (WI-20260904-50B2K part (c))",
                    ));
                }
                Ok(Value::Node(kb.make_poly_type_occ(
                    binders.clone(),
                    context.clone(),
                    b,
                    sp,
                    owner,
                )))
            }
        },
        NodeKind::EffectExpr(node) => match node {
            EffectExprNode::Merge { left, right } => {
                let l = elim_child(kb, left, arg_types, arg_syms, ctx, span)?;
                let r = elim_child(kb, right, arg_types, arg_syms, ctx, span)?;
                Ok(Value::Node(kb.make_merge_occ(l, r, sp, owner)))
            }
            EffectExprNode::Present { label } => {
                let l = elim_child(kb, label, arg_types, arg_syms, ctx, span)?;
                Ok(Value::Node(kb.make_present_occ(l, sp, owner)))
            }
            EffectExprNode::Guarded { label, guard } => {
                // Only the label participates in projection elimination (type-param
                // substitution in the effect label); the guard is carried through
                // unchanged (conservatively-present metadata, no discharge in phase 1).
                let l = elim_child(kb, label, arg_types, arg_syms, ctx, span)?;
                Ok(Value::Node(kb.make_guarded_occ(
                    l,
                    guard.clone(),
                    sp,
                    owner,
                )))
            }
            EffectExprNode::Absent { label } => {
                let l = elim_child(kb, label, arg_types, arg_syms, ctx, span)?;
                Ok(Value::Node(kb.make_absent_occ(l, sp, owner)))
            }
            EffectExprNode::Open { tail } => {
                let t = elim_child(kb, tail, arg_types, arg_syms, ctx, span)?;
                Ok(Value::Node(kb.make_open_occ(t, sp, owner)))
            }
            EffectExprNode::EmptyRow => Ok(Value::Node(Rc::clone(occ))),
        },
        // A non-type / non-effect occurrence (Expr / Pattern) in a type position is not a
        // projection carrier — return as-is (defensive; the descent never targets one).
        _ => Ok(Value::Node(Rc::clone(occ))),
    }
}

/// WI-397: resolve a COMPOUND-receiver projection (`a.b.T`) — the receiver `value`
/// is a field-access occurrence (`Value::Node`), not a single value reference.
/// Resolve the receiver path's static type, then project the `member` off it. The
/// Node twin of the single-`Ref` path in [`rewrite_term_projections`].
fn resolve_compound_projection(
    kb: &mut KnowledgeBase,
    receiver: &Value,
    member: Symbol,
    arg_types: &HashMap<Symbol, Value>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<ProjResult, TypeError> {
    let (recv_ty, recv_decl_sort) = resolve_receiver_path_type(kb, receiver, arg_types, ctx, span)?;
    let member_str = kb.local_name_of(member).to_owned();
    project_type_member(kb, &recv_ty, &member_str, recv_decl_sort, ctx, span)
}

/// Resolve the static TYPE of a field-access receiver path occurrence (WI-397). A
/// single value reference `Ref(s)` is the type of the argument bound to param `s`;
/// a field access `base.field` is the type of `field` in the (recursively resolved)
/// `base` type. Any other shape is a loud error (never a silent fresh var).
///
/// WI-400: also returns the **declaring sort** of an ABSTRACT result — the sort whose
/// `requires` chain lends an abstract type-parameter result its interface (`s.provider :
/// P` resolves to `(P-var, Some(State))`, since `State` declares the field `provider : P`
/// and `State requires DataProvider[P]`). `None` for a concrete result.
fn resolve_receiver_path_type(
    kb: &mut KnowledgeBase,
    receiver: &Value,
    arg_types: &HashMap<Symbol, Value>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<(Value, Option<Symbol>), TypeError> {
    // Innermost head: a value reference `Ref(s)` (the DotApply chain bottoms out in
    // it). The receiver is the argument bound to param `s` — a top-level reference, not a
    // field projection, so no declaring sort is attached here.
    if let Some(head) = extract_sort_ref_sym(kb, receiver) {
        let ty = arg_types.get(&head).cloned().ok_or_else(|| {
            projection_type_error(
                ctx,
                span,
                &format!(
                    "type projection receiver '{}' is not an argument-bound parameter of this call",
                    kb.local_name_of(head),
                ),
            )
        })?;
        return Ok((ty, None));
    }
    // A field access `base.field` — a `DotApply` with no call args. Resolve `base`,
    // then project `field`'s type off it.
    //
    // WI-819: read through `TermView`, so the SAME code serves both carriers. This
    // arm used to match `Value::Node(occ)` + `Expr::DotApply` structurally, which
    // meant a compound receiver was resolvable only when the annotation happened
    // to ride the Node carrier — and once a `let`'s annotation moved onto its
    // pattern TERM, the identical type arrived here as a `Value::Term` and was
    // refused. WI-814 gave `Expr::DotApply` and its `dot_apply` term twin ONE view
    // head with the same three keys, which is exactly what makes the neutral read
    // possible: `head` / `named_arg` see through either carrier, so the verdict no
    // longer depends on which one the type is written on (WI-425).
    if let Some(dot_sym) = kb.try_resolve_symbol(dt::qualified(dt::DOT_APPLY)) {
        let is_dot = matches!(
            receiver.head(kb),
            ViewHead::Functor { functor: Some(f), .. } if f == dot_sym
        );
        if is_dot {
            let (k_receiver, k_name, k_args) =
                (kb.intern("receiver"), kb.intern("name"), kb.intern("args"));
            // A bare field access carries an EMPTY `args` list — ABSENT, or the
            // `nil` constructor, which heads as a bare `Ref` (WI-436 / WI-511:
            // a nullary constructor is stored as `Ref(c)`). Anything else — a
            // `cons` spine (a method CALL `s.f(x)`, not a type path) OR an
            // unresolved reflection `?args` Var — is NOT a bare access. The Var
            // case is spelled out rather than folded into a "not a Functor" test:
            // that test admitted it silently, and treating a call with unknown
            // arguments as a field path is the kind of quiet acceptance CLAUDE.md
            // rules out.
            let nil_sym = kb.try_resolve_symbol("anthill.prelude.List.nil");
            let args_empty = match receiver.named_arg(kb, k_args) {
                None => true,
                Some(a) => matches!(
                    (a.head(kb), nil_sym),
                    (
                        ViewHead::Functor {
                            functor: Some(r),
                            pos_arity: 0,
                            named_arity: 0,
                        },
                        Some(n),
                    ) if r == n
                ),
            };
            let base = receiver.named_arg(kb, k_receiver).map(|b| b.to_value());
            let field = receiver
                .named_arg(kb, k_name)
                .and_then(|n| extract_sort_ref_sym(kb, &n));
            if let (true, Some(base), Some(field)) = (args_empty, base, field) {
                let (base_ty, _) = resolve_receiver_path_type(kb, &base, arg_types, ctx, span)?;
                return resolve_field_type(kb, &base_ty, field, ctx, span);
            }
        }
    }
    Err(projection_type_error(
        ctx,
        span,
        "type projection receiver is not a value-reference field path (`s.field…`)",
    ))
}

/// Resolve field `field_sym`'s type given a receiver's sort type (WI-397): find the
/// receiver sort's constructor declaring the field, take its declared field type,
/// and substitute the receiver's type-args — the same subst pattern field types use
/// (design path-dependent-types.md §1 step 2). A receiver with no concrete sort, or
/// a field no constructor declares, is a loud error.
///
/// WI-400: returns `(field-type, declaring-sort)`. The declaring sort is `Some(sort_sym)`
/// when the field's resolved type is ABSTRACT (no concrete sort functor — an unbound
/// type-parameter of `sort_sym`), so `project_type_member` can read its declared
/// interface off `sort_sym`'s `requires` chain; `None` for a concrete field type.
pub(super) fn resolve_field_type(
    kb: &mut KnowledgeBase,
    recv_ty: &Value,
    field_sym: Symbol,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<(Value, Option<Symbol>), TypeError> {
    let sort_sym = sort_functor_of_view(kb, recv_ty).ok_or_else(|| {
        projection_type_error(
            ctx,
            span,
            &format!(
                "cannot access field '{}' on a receiver with no concrete sort",
                kb.local_name_of(field_sym),
            ),
        )
    })?;
    // The receiver's type-arg substitution is the same for every constructor.
    let subst = build_pattern_subst(kb, recv_ty, sort_sym);
    // Collect the field's resolved type from EVERY constructor that declares it, so the
    // result is INDEPENDENT of `constructors_of_sort`'s (HashMap) iteration order. Field
    // access on a multi-variant sort is well-defined only when all variants agree on the
    // field's type; a divergence is a LOUD error, never an order-dependent pick.
    let mut resolved: Option<Value> = None;
    // WI-490: `field_constructors_of_sort` adds a free-standing entity's own
    // symbol, whose `entity_field_types` carries the fields that
    // `constructors_of_sort` (parent-keyed, empty for such an entity) misses.
    for ctor in kb.field_constructors_of_sort(sort_sym) {
        // Scope the `entity_field_types` borrow so the `&mut kb` subst call below is
        // free; `continue` to the next constructor if this one lacks the field.
        let declared = {
            let Some(fields) = kb.entity_field_types(ctor) else {
                continue;
            };
            match fields.iter().find(|(f, _)| *f == field_sym) {
                Some((_, d)) => d.clone(),
                None => continue,
            }
        };
        let this = match &subst {
            Some(s) => walk_pattern_field_type_deep(kb, s, &declared),
            None => declared,
        };
        match &resolved {
            None => resolved = Some(this),
            Some(prev) if views_structurally_equal(kb, prev, &this) => {}
            Some(_) => {
                return Err(projection_type_error(
                    ctx,
                    span,
                    &format!(
                        "field '{}' is declared with differing types across the constructors of \
                     '{}'; a compound projection off it is ambiguous",
                        kb.local_name_of(field_sym),
                        kb.qualified_name_of(sort_sym).to_owned(),
                    ),
                ));
            }
        }
    }
    let resolved = resolved.ok_or_else(|| {
        projection_type_error(
            ctx,
            span,
            &format!(
                "type '{}' has no field '{}'",
                kb.qualified_name_of(sort_sym).to_owned(),
                kb.local_name_of(field_sym),
            ),
        )
    })?;
    // The field's resolved type is an ABSTRACT type-parameter of `sort_sym` (an unbound
    // `sort P = ?` left as a logic var, not a concrete sort / arrow / tuple) iff it is a
    // bare type-param value. Then `sort_sym`'s `requires` chain is what lends it an
    // interface for a downstream projection (`s.provider : P`, `State requires
    // DataProvider[P]`). A concrete field type carries no declaring sort.
    let decl_sort = match &resolved {
        Value::Term { id: t, .. } if is_type_param_value(kb, *t) => Some(sort_sym),
        // WI-1059: the SAME abstract parameter, wearing its receiver path. Once an
        // unwritten slot is materialized ([`rigidify_unwritten_sort_params`]) the receiver
        // is `State[P = s.P]`, so `build_pattern_subst` resolves the field `provider : P`
        // through that binding and `resolved` arrives as the projection `s.P` rather than
        // the bare param `Ref(P)`. It denotes exactly what it did before — THIS instance's
        // `P` — so `sort_sym` is still the sort whose `requires` chain lends it an
        // interface. Without this the receiver reads as "abstract with no concrete sort"
        // and `s.provider.K` stops forming its neutral (measured: wi376, wi399, wi400,
        // wi430). Gated on the member NAMING one of `sort_sym`'s declared parameters, so an
        // ordinary field projection is untouched.
        _ if projected_param_of_sort(kb, &resolved, Some(sort_sym)).is_some() => Some(sort_sym),
        _ => None,
    };
    Ok((resolved, decl_sort))
}

/// WI-475: project a single-ref `ExprCarried` term (`s.M`) against the receiver's
/// argument type, returning the eliminated type as a `Value` — which MAY be a
/// `Value::Node` (e.g. `s.E` projecting to a Modify-bearing effect row `{Modify[p]}`,
/// or `s.Sort` of a denoted-bearing argument). A Node result is only representable at
/// the TOP level of an eliminated type (an effect-row / return type that IS the whole
/// projected value); [`eliminate_type_projections`] returns it directly there, while
/// [`rewrite_term_projections`] (rebuilding a `Term` tree) can use only the `Value::Term`
/// case. Shared by both so the projection + WI-459 re-keying logic lives in one place.
fn eliminate_expr_carried_projection(
    kb: &mut KnowledgeBase,
    t: TermId,
    arg_types: &HashMap<Symbol, Value>,
    arg_syms: Option<&HashMap<Symbol, Symbol>>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<Value, TypeError> {
    let TypeExtractor::ExprCarried { value, member } = extract_type(kb, &TermIdView(t)) else {
        return Ok(Value::term(t));
    };
    // A single value reference `Ref(s)` (classified as `SortRef`) is the common
    // receiver and is resolved below.
    //
    // WI-819: a COMPOUND receiver (`s.cell.T`, a field-access path) is delegated
    // to `resolve_compound_projection` — the SAME resolver the `Value::Node` arm
    // of `eliminate_type_projections` uses for the same shape. It used to be a
    // loud error here, on the stated ground that "a compound receiver is rejected
    // at load, so this is defensive"; that was true only because a compound
    // projection could reach this function on the NODE carrier alone. Once a
    // `let`'s annotation rides its pattern term (WI-819), the identical type
    // arrives here as a `Value::Term`, and refusing it made the answer depend on
    // WHICH CARRIER the annotation happened to have — a carrier-dependent
    // verdict, which is the thing carrier-neutrality exists to prevent (WI-425).
    // Delegating makes the two carriers agree; it can only turn a former error
    // into the answer the Node carrier already gave, never accept more than that
    // arm does.
    let Some(receiver) = extract_sort_ref_sym(kb, &value) else {
        return match resolve_compound_projection(kb, &value, member, arg_types, ctx, span)? {
            ProjResult::Grounded(v) => Ok(v),
            // Abstract receiver with the member declared: keep the original
            // `ExprCarried` as the rigid neutral, exactly as the Node arm does.
            ProjResult::Neutral => Ok(Value::term(t)),
        };
    };
    let arg_ty = match arg_types.get(&receiver) {
        Some(v) => v.clone(),
        None => {
            return Err(projection_type_error(
                ctx,
                span,
                &format!(
                    "type projection receiver '{}' is not an argument-bound parameter of this call",
                    kb.local_name_of(receiver),
                ),
            ));
        }
    };
    let member_str = kb.local_name_of(member).to_owned();
    // Single-ref receiver: the arg's inferred type (a concrete sort, or a bound
    // type-param). No abstract-type-param declaring sort is in hand here (that arises
    // only on the compound field-projection path) — `None`.
    match project_type_member(kb, &arg_ty, &member_str, None, ctx, span)? {
        // Term OR Node — the caller decides whether a Node is representable in its position.
        ProjResult::Grounded(v) => Ok(v),
        // WI-400: the receiver is abstract but the member is declared — the rigid
        // NEUTRAL (path-identity). WI-459: RE-KEY its receiver from the callee's formal
        // parameter to the CALLER's argument value-reference when this is a call-site
        // elimination (`arg_syms` present) and the argument is a simple value reference.
        // The projection stayed abstract precisely because the argument's TYPE did not
        // bind the member (`sfd(xs)` with the bare `xs : List`), so the receiver VALUE
        // is exactly that argument — `sfd.xs.T` is definitionally `collectd.xs.T`. The
        // grounded arm above never reaches here, so a member the argument's type DID bind
        // (the recursive `collectd(rest)`, where `rest : List[T = xs.T]` δ-reduces `T`
        // to `xs.T`) keeps its δ-reduced value un-re-keyed. A non-value-ref argument has
        // no `arg_syms` entry → left as the callee-keyed neutral (deferred-receiver
        // follow-on). Re-forming `ExprCarried{Ref(arg_sym), member}` here is what makes
        // the SAME definitional projection compare EQUAL under the non-decomposing ζ arm
        // (WI-400) instead of two identically-printed-yet-distinct neutrals.
        ProjResult::Neutral => Ok(Value::term(match arg_syms.and_then(|m| m.get(&receiver)) {
            Some(&arg_sym) => {
                let recv_term = kb.alloc(Term::Ref(arg_sym));
                kb.make_expr_carried(recv_term, member)
            }
            None => t,
        })),
    }
}

/// Recursive term rewrite for [`eliminate_type_projections`]: an `ExprCarried` head is
/// projected and replaced; any other `Fn` is rebuilt only if a child changed; leaves
/// pass through.
fn rewrite_term_projections(
    kb: &mut KnowledgeBase,
    t: TermId,
    arg_types: &HashMap<Symbol, Value>,
    arg_syms: Option<&HashMap<Symbol, Symbol>>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<TermId, TypeError> {
    // WI-428: a rigid type-receiver projection (`P.Key` / `MemStore.Key`) — validated
    // and δ-grounded (or kept as the rigid neutral) against the declaring sort's
    // `requires` chain / the subject's own manifest bindings; no `arg_types` receiver
    // lookup (the subject is a TYPE, not a value parameter).
    if matches!(type_head(kb, &TermIdView(t)), TypeHead::RigidProjection) {
        let TypeExtractor::RigidTypeProjection {
            sort,
            subject,
            member,
        } = extract_type(kb, &TermIdView(t))
        else {
            return Ok(t);
        };
        return match resolve_rigid_projection(kb, sort, &subject, member, ctx, span)? {
            ProjResult::Grounded(Value::Term { id: pt, .. }) => Ok(pt),
            ProjResult::Grounded(_) => Err(projection_type_error(
                ctx,
                span,
                "type projection resolved to a non-term carrier, which is not yet supported",
            )),
            ProjResult::Neutral => Ok(t),
        };
    }
    if matches!(type_head(kb, &TermIdView(t)), TypeHead::ExprCarried) {
        // WI-475: a single-ref `ExprCarried` (`s.M`) projects to a `Value` that MAY be a
        // Node carrier (e.g. `s.E` → a Modify-bearing effect row `{Modify[p]}`). A Node
        // cannot be embedded mid-`Term`-tree, so it is representable only at the TOP level
        // (`eliminate_type_projections` handles that and returns the Node `Value`). Reaching
        // here means the `ExprCarried` is NESTED inside a larger `Term` — a Node result
        // there is the genuine follow-on (loud, never silently dropped).
        return match eliminate_expr_carried_projection(kb, t, arg_types, arg_syms, ctx, span)? {
            Value::Term { id: pt, .. } => Ok(pt),
            _ => Err(projection_type_error(
                ctx,
                span,
                "type projection resolved to a non-term carrier, which is not yet supported",
            )),
        };
    }
    // Recurse into `Fn` children, rebuilding only if a child changed. Index-based so
    // each child is read (a `Copy` `TermId`) before the `&mut kb` recursive call and
    // written after — no borrow of the owned (cloned) arg vectors across the call.
    if let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = kb.get_term(t).clone()
    {
        let mut changed = false;
        let mut new_pos = pos_args;
        for i in 0..new_pos.len() {
            let nc = rewrite_term_projections(kb, new_pos[i], arg_types, arg_syms, ctx, span)?;
            if nc != new_pos[i] {
                new_pos[i] = nc;
                changed = true;
            }
        }
        let mut new_named = named_args;
        for i in 0..new_named.len() {
            let nc = rewrite_term_projections(kb, new_named[i].1, arg_types, arg_syms, ctx, span)?;
            if nc != new_named[i].1 {
                new_named[i].1 = nc;
                changed = true;
            }
        }
        if changed {
            return Ok(kb.alloc(Term::Fn {
                functor,
                pos_args: new_pos,
                named_args: new_named,
            }));
        }
    }
    Ok(t)
}

/// WI-400: outcome of projecting a member off a receiver's type. A projection either
/// **grounds** (δ — the receiver's type makes the member manifest, `List[Int64].T =
/// Int64`) or **stays neutral** (the receiver's type is abstract — a bare type-parameter
/// the receiver leaves unbound, or an abstract type-variable receiver — but the member
/// *is* declared on the receiver's interface, so the projection is a well-formed RIGID
/// type keyed by `receiver` + `member`). A neutral is NOT an error: it is the
/// abstract-stays-poly form (WI-376), usable by path-identity (the ζ arm of
/// [`unify_types`]). The caller keeps the ORIGINAL `ExprCarried` for a neutral — already
/// the canonical form — rather than reconstructing it.
pub(super) enum ProjResult {
    /// The member is manifest: the projected type.
    Grounded(Value),
    /// The receiver is abstract but the member is declared on its interface: keep the
    /// projection as a rigid neutral.
    Neutral,
}

/// Project a single type member (`T`, `E`, `Sort`, …) off the receiver's argument
/// type for [`rewrite_term_projections`].
///
/// `recv_decl_sort` is the sort whose `requires` chain lends an ABSTRACT type-variable
/// receiver its declared interface — supplied by [`resolve_field_type`] when the
/// receiver's type resolved to an (abstract) type-parameter of that sort (`s.provider : P`
/// ⟹ `State`, since `State requires DataProvider[P]`). `None` for a concrete receiver or
/// where no declaring sort is in hand; then an abstract member that is not a declared
/// type-parameter cannot be confirmed and is a loud error.
pub(super) fn project_type_member(
    kb: &mut KnowledgeBase,
    arg_ty: &Value,
    member: &str,
    recv_decl_sort: Option<Symbol>,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<ProjResult, TypeError> {
    // WI-381: resolve a defined-type / alias receiver to its underlying shape first, so
    // every projection reads off the resolved structure (`sort IntStream =
    // Stream[T = Int]` ⟹ project off `Stream[T = Int]`), never the opaque alias — which
    // declares no members, so `s.T` would spuriously fail. A non-alias / opaque /
    // parametric receiver is left unchanged.
    let resolved_recv: Value = match extract_type(kb, arg_ty) {
        TypeExtractor::SortRef(s) => match resolve_alias_shape(kb, s) {
            Some(shape) => Value::term(shape),
            None => arg_ty.clone(),
        },
        _ => arg_ty.clone(),
    };
    let arg_ty = &resolved_recv;
    // `s.Sort` — the whole parameterized sort of the receiver (captures every
    // parameter, wide-sort safe).
    if member == "Sort" {
        return Ok(ProjResult::Grounded(arg_ty.clone()));
    }
    // Concrete: the receiver's type binds the member directly (`List[Int].T = Int`).
    if let Some(p) = extract_type_param(kb, arg_ty, member) {
        return Ok(ProjResult::Grounded(p));
    }
    // The member is not concretely bound. WI-400 (abstract-stays-poly, co-delivering
    // WI-376): a projection off an abstract receiver no longer errors — it STAYS NEUTRAL
    // (a rigid type keyed by receiver + member, compared by the ζ arm of `unify_types`),
    // PROVIDED the member is DECLARED on the receiver's interface. Distinguish:
    //
    //   - a CONCRETE-sort receiver with the member as a declared-but-UNBOUND type
    //     parameter (`peek(l: List) -> l.T`, bare `List` — `T` is `List`'s param, just
    //     not pinned) ⟹ neutral;
    //   - an abstract TYPE-VARIABLE receiver whose declared interface (the enclosing
    //     sort's `requires Spec[recv]`) provides the member (`s.provider.K` where
    //     `s.provider : P` and `State requires DataProvider[P]`, `K` a member of
    //     DataProvider) ⟹ neutral, via [`abstract_var_declares_member`];
    //   - a member NO interface declares (a typo, `l.Nonesuch`) ⟹ a LOUD error.
    //
    // Minting an unconstrained var here (instead of a neutral) would be unsound — it
    // would absorb any demand downstream (`peek(l)` usable as both `Int64` and `String`);
    // the neutral cannot, since the ζ arm only equates it with an IDENTICAL neutral.
    if let Some(s) = sort_functor_of_view(kb, arg_ty) {
        if kb
            .type_params_of_sort(s)
            .iter()
            .any(|d| d.as_str() == member)
        {
            return Ok(ProjResult::Neutral);
        }
        // WI-376 (cross-sort provider DIVERGENT member name): the receiver's sort does not
        // declare `member` ITSELF, but may PROVIDE a spec that declares it under a
        // different carrier-side name (`List provides Iterable[List[T], T]` ⟹ Iterable's
        // `Element` maps to `List`'s `T`). Map `member` through the provides binding to the
        // carrier-side type and ground/neutralize THAT against the receiver — so one
        // signature written in the spec's vocabulary (`c.Element`) grounds on a concrete
        // carrier (`List[T = Int64].Element = Int64`) and stays neutral on a bare one.
        if let Some(r) = project_via_provided_spec(kb, arg_ty, s, member) {
            return r;
        }
        return Err(projection_type_error(
            ctx,
            span,
            &format!(
                "type '{}' has no member '{member}'",
                kb.qualified_name_of(s).to_owned(),
            ),
        ));
    }
    // No concrete sort: an abstract type-variable receiver (a sort type-parameter, e.g.
    // `s.provider : P` — opened to a logic var whose source identity is erased). Neutral
    // iff the param's DECLARED INTERFACE provides the member — the `requires Spec[param]`
    // bounds on the sort that DECLARES the param (`recv_decl_sort`, supplied by
    // `resolve_field_type`). Each such `Spec` lends the param its members
    // (`State requires DataProvider[P]` ⟹ `P` has DataProvider's `K`). A member no bound
    // declares (or no declaring sort in hand) is a loud error, never a silent neutral.
    if let Some(decl_sort) = recv_decl_sort {
        // WI-430: carrier-precise neutral formation. The abstract receiver IS one of
        // `decl_sort`'s type-parameters (`s.provider : P`); only a `requires` bound whose
        // CARRIER is THIS param lends it the member. Consulting the whole `requires` chain
        // (the pre-WI-430 behavior) over-accepts a member projection off the WRONG param
        // when a sort has several params each carrying their own `requires` (`State[P, Q]
        // requires DataProvider[P], OtherProvider[Q]` would wrongly accept `s.provider.M`,
        // `M` being `Q`'s member, off the `P`-typed `s.provider`). Match the receiver's
        // carrier key — the var-id all the param's spellings share (WI-428 `SubjectKey`) —
        // against each bound, the `ExprCarried`-side counterpart of `resolve_rigid_-
        // projection`'s candidate filter (`spec_mentions_key`).
        let carrier_key = match arg_ty {
            Value::Term { id: t, .. } => subject_key_of_term(kb, *t),
            _ => None,
        }
        // WI-1059: a materialized slot spells the parameter as the projection `s.P`, whose
        // head is `ExprCarried` and so has no subject key of its own. Key it by the
        // PARAMETER it names — `<decl_sort>.P`'s alias var, the identity every other
        // spelling of that parameter already resolves to (see [`sym_subject_key`]). This
        // keeps WI-430's carrier precision: `s.P` and `s.Q` key to different params, so a
        // `requires` bound carrying `Q` still does not lend its member to a `P`-typed
        // receiver. It deliberately does NOT distinguish `s.P` from `t.P` — both ARE
        // `State.P`, and which RECEIVER a neutral projects off is the ζ arm's question,
        // decided by comparing receivers structurally, not this bound lookup's.
        .or_else(|| {
            projected_param_of_sort(kb, arg_ty, Some(decl_sort)).map(|p| sym_subject_key(kb, p))
        });
        if let Some(key) = carrier_key {
            if abstract_member_declared_by_requires(kb, decl_sort, key, member) {
                return Ok(ProjResult::Neutral);
            }
        }
        return Err(projection_type_error(
            ctx,
            span,
            &format!(
                "no `requires` bound on '{}' whose carrier is this abstract type parameter \
             declares a member '{member}'; cannot project '{member}'",
                kb.qualified_name_of(decl_sort).to_owned(),
            ),
        ));
    }
    Err(projection_type_error(
        ctx,
        span,
        &format!("cannot project '{member}' off an abstract receiver with no concrete sort",),
    ))
}

/// WI-400/430: does ANY `requires Spec[…]` bound on `decl_sort` lend the abstract type
/// parameter identified by `carrier_key` the member `member`? Consults `decl_sort`'s whole
/// (transitive) `requires` chain, accepting iff some entry [`requires_entry_lends_member`]
/// — i.e. declares `member` AND carries `carrier_key`. The `ExprCarried` neutral-formation
/// gate for an abstract-receiver projection (`s.provider.K`, `s.provider : P` an abstract
/// type-parameter of `decl_sort`); design path-dependent-types.md §1, §4.1.
fn abstract_member_declared_by_requires(
    kb: &mut KnowledgeBase,
    decl_sort: Symbol,
    carrier_key: SubjectKey,
    member: &str,
) -> bool {
    requires_chain(kb, decl_sort)
        .iter()
        .any(|entry| requires_entry_lends_member(kb, entry, carrier_key, member))
}

/// WI-400/428/430 — THE carrier-precise candidate predicate: does a single `requires`
/// entry lend `member` to the type parameter identified by `carrier_key`? Both halves must
/// hold: (a) the required spec DECLARES `member` as one of its type-parameters
/// (`DataProvider` declares `K`), and (b) the spec application MENTIONS `carrier_key` among
/// its binding values — so the bound's carrier IS this param. `requires DataProvider[P]`
/// auto-completes (WI-359 loader normalization) to a named binding carrying `P`, which
/// [`spec_mentions_key`] reads; a positional carrier never survives to here.
///
/// Shared by the two pure-filter sites — the `ExprCarried` neutral gate
/// ([`abstract_member_declared_by_requires`], WI-430) and [`resolve_rigid_projection`]'s
/// rigid-projection candidate collection (WI-428) — so the carrier-precision rule has ONE
/// source of truth: both decide the same soundness question (which bound's carrier is this
/// subject), and a refinement to either half must move both at once.
/// (`ground_rigid_projection_if_concrete` calls the two component checks SEPARATELY — it
/// needs the carrier-mention outcome on its own to drive a self-carrier fallback — so it is
/// deliberately not routed through this helper.)
///
/// NB `spec_mentions_key` matches `carrier_key` in ANY top-level binding value, not strictly
/// the spec's carrier slot — the documented WI-428 conservative reading (a param mentioned
/// as a non-carrier binding still licenses); exact carrier-slot precision is the §5.3
/// normalization end-state, shared with the rigid path.
fn requires_entry_lends_member(
    kb: &KnowledgeBase,
    entry: &RequiresEntry,
    carrier_key: SubjectKey,
    member: &str,
) -> bool {
    kb.type_params_of_sort(entry.required_sort)
        .iter()
        .any(|d| d.as_str() == member)
        && spec_mentions_key(kb, &entry.spec, carrier_key)
}

/// WI-376 (cross-sort provider divergent member name): project `member` off a CONCRETE
/// receiver `recv_ty` (sort `recv_sort`) that does not declare `member` itself but PROVIDES
/// a spec that does — under a possibly-different carrier-side name. Reads the carrier's
/// `provides Spec[…]` binding for the spec's `member` parameter (`List provides
/// Iterable[List[T], T]` ⟹ Iterable's `Element` ↦ `List`'s `T`), then grounds that
/// carrier-side type against the receiver's own type-args (`build_pattern_subst`, the same
/// substitution field-type resolution uses). A binding that grounds to a concrete type is
/// `Grounded`; one still resting on an unbound carrier parameter (a BARE receiver) stays
/// `Neutral` — abstract-stays-poly, exactly as a direct unbound type-param would. Returns
/// `None` when no provided spec declares `member` (the caller then surfaces the loud
/// no-member error). First provided spec that declares `member` wins (a member shared
/// across two provided specs is left to a later disambiguation pass, mirroring
/// `find_spec_op_for_provided_sort`).
fn project_via_provided_spec(
    kb: &mut KnowledgeBase,
    recv_ty: &Value,
    recv_sort: Symbol,
    member: &str,
) -> Option<Result<ProjResult, TypeError>> {
    // `directly_provided_specs` dedups CANONICALLY, where this walk's own copy used to dedup
    // raw — and drops nothing this loop could reach: every step below reads `spec`
    // canonically (`type_params_of_sort`, `provider_spec_view_bindings`), so a second,
    // raw-different copy of a spec already tried answers exactly as the first did.
    for spec in directly_provided_specs(kb, recv_sort) {
        if !kb
            .type_params_of_sort(spec)
            .iter()
            .any(|d| d.as_str() == member)
        {
            continue;
        }
        let Some(bindings) = provider_spec_view_bindings(kb, recv_sort, spec) else {
            continue;
        };
        let Some((_, carrier_val)) = bindings
            .iter()
            .find(|(p, _)| kb.local_name_of(*p) == member)
            .copied()
        else {
            continue;
        };
        let is_effect_member = matches!(
            type_head(kb, &Value::term(carrier_val)),
            TypeHead::EffectsRows
        );
        // Ground the carrier-side type (`List`'s `T`) against the receiver's type-args, so
        // a concrete `List[T = Int64]` grounds `Element` to `Int64`; a bare `List` leaves
        // it an unbound `T` ⟹ neutral.
        let grounded = match build_pattern_subst(kb, recv_ty, recv_sort) {
            Some(s) => walk_pattern_field_type_deep(kb, &s, &Value::term(carrier_val)),
            None => Value::term(carrier_val),
        };
        let is_ground = resolved_type_is_ground(kb, &grounded);
        // WI-484 (vs WI-396): an EFFECT-row member projects via `provides` ONLY when the
        // provision WROTE a GROUND row (`List provides Stream[T, {}]` ⟹ `l.E = {}`).
        // Reading back a written, ground effect is sound — it is NOT the "silent pure
        // default" WI-396 excluded (reconstructing `{}` for an UNwritten effect). A
        // non-ground / unwritten effect binding still skips → loud missing-member,
        // preserving WI-396 for the case it actually guarded.
        if is_effect_member && !is_ground {
            continue;
        }
        // Grounded ONLY when the result is FULLY concrete (deep `resolved_type_is_ground`,
        // not a head-only check): a structured binding still resting on an unbound carrier
        // param (`Element = Pair[A, B]` on a bare receiver) stays NEUTRAL, never a Grounded
        // type that would absorb demand downstream. A non-Term carrier is conservatively
        // neutral too.
        return Some(if is_ground {
            Ok(ProjResult::Grounded(grounded))
        } else {
            Ok(ProjResult::Neutral)
        });
    }
    None
}

/// WI-383: the `requires`-clause specs of an OPERATION, decoded to `RequiresEntry`s —
/// the op-type-param analogue of [`requires_chain`] (which reads a SORT's
/// `SortRequiresInfo`). An op type-param `getV.T` is lent its members by the operation's
/// OWN `requires Spec[C = T]` clause, stored on `OperationInfo.requires`. Each spec
/// application becomes one entry (`required_sort` = the spec base functor).
///
/// LIMITATION (vs the sort path): this reads the op's DIRECT requires only — it does NOT
/// transitively close (a member declared by a *transitively* required spec, e.g.
/// `requires Ord[T]` lending `Eq`'s members, is not reached). The candidate filter
/// then finds no bound, so the projection is conservatively rejected (sound — never a
/// wrong ground type). Transitive op-requires lending is deferred (no motivating driver).
/// WI-20260919-HXGXF — does ANY requirement in the loaded program name `spec`?
///
/// The demand gate for `type_value_derive`: deriving a `TypeValue` row for every sort
/// grows the provider relation by 77% and costs ~113ms per load, of which only 5ms is the
/// derivation itself — the rest is every downstream pass walking a bigger relation
/// (measured with `ANTHILL_LOAD_TIMING=1`, 3-run averages). Nothing requires `TypeValue`
/// yet, so without this gate the whole cost is paid for evidence no one asks for.
///
/// BOTH LEVELS, because a requirement can be written at either and the gate is only sound
/// if it sees both: a sort-level `requires` rides a `SortRequiresInfo` fact, an
/// operation-level one rides `OperationInfo.requires` and emits no such fact. Checking
/// only the relation would have missed exactly the spelling this feature's own tests use
/// (`operation tv[B](…) requires TypeValue[T = B]`).
///
/// SHORT-CIRCUITS on the first hit, so the cost falls on the case where the answer is NO
/// — which is the case the gate exists to make cheap, and is why the sort-level relation
/// scan (one pass, no per-sort lookups) is tried first.
///
/// MEASURED at ~23ms on a ~940ms stdlib load when the answer is NO, dominated by one
/// `lookup_operation_info` per operation. That is the price of not paying the ~113ms the
/// unconditional derivation costs, and the net against baseline is within run-to-run
/// noise. A pre-filter on the fact's own `requires` field would cut most of it and was
/// tried; it is left out because the emptiness test wants a carrier-agnostic list read
/// and the saving is below the measurement floor here.
///
/// This is a gate, not an analysis: it answers "does anyone ask?", not "which carriers do
/// they ask about". The precise question needs the concrete bindings at call sites, which
/// only exist after the typer — and this pass must run before it.
pub(crate) fn any_requirement_names_spec(kb: &KnowledgeBase, spec: Symbol) -> bool {
    let canon = kb.canonical_sort_sym(spec);
    if let Some(req_sym) = kb.try_resolve_symbol("anthill.reflect.SortRequiresInfo") {
        for rid in kb.rules_by_functor(req_sym) {
            if !kb.is_fact(rid) {
                continue;
            }
            let head = kb.rule_head_value(rid);
            if let Some(v) = crate::kb::op_info::head_field_value(kb, &head, "spec") {
                if spec_base_functor(kb, &v).is_some_and(|b| kb.canonical_sort_sym(b) == canon) {
                    return true;
                }
            }
        }
    }
    // The operation-level half, over the `OperationInfo` RELATION rather than over a list
    // of sorts. A first cut walked `eq_derive::composite_sorts`, which is the
    // ENTITY-BEARING sorts — and so missed every operation of a sort that declares no
    // entity, which is exactly the shape this feature's own tests use (`sort D` holding
    // only operations). Measured: three of five acceptance rows went red because the gate
    // never opened for them.
    //
    // Decoded through the SAME reader the dictionary layout uses
    // (`op_requires_entries`), so the gate and the consumer cannot disagree about what a
    // clause names — a conjunction `requires A, B` in particular, which lowers to one
    // `conjunction(..)` value and would hide both specs from a shape test.
    let Some(op_info_sym) = kb.try_resolve_symbol("anthill.reflect.OperationInfo") else {
        return false;
    };
    for rid in kb.rules_by_functor(op_info_sym) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head_value(rid);
        let Some(name_tid) = crate::kb::op_info::head_field_term(kb, &head, "name") else {
            continue;
        };
        let op = match kb.get_term(name_tid) {
            Term::Ref(s) | Term::Ident(s) => *s,
            Term::Fn { functor, .. } => *functor,
            _ => continue,
        };
        if op_requires_entries(kb, op)
            .iter()
            .any(|e| kb.canonical_sort_sym(e.required_sort) == canon)
        {
            return true;
        }
    }
    // WI-20260921-28TAT — THE THIRD SPELLING: a PROVISION CONDITION,
    // `provides ErrorTag[T = T] :- TypeValue[T = T]`. A condition is a requirement in
    // every sense that matters here — it is a goal the resolver must discharge to select
    // the instance — but it rides a `ProvidesConditionInfo` fact and so is named by
    // NEITHER relation above: not `SortRequiresInfo` (it is not the sort's own clause)
    // and not `OperationInfo.requires` (no operation declares it).
    //
    // MEASURED, and it is the failure this leg exists to stop. With `Error.reify
    // requires ErrorTag[T = T1]` and `Error provides ErrorTag[T = T] :- TypeValue[T = T]`
    // the ONLY demand for `TypeValue` in the whole program is that condition. The gate
    // answered NO, `type_value_derive` emitted no rows at all, and every `ErrorTag`
    // resolution in the program then failed on its own condition — including
    // `ErrorTag[T = Boom]` at a call that pins `Boom` outright. It failed SILENTLY: an
    // unresolved op-scoped dep is a `None` slot, so the boundary simply stopped narrowing
    // and 23 call sites went unevidenced with nothing printed.
    //
    // The gate's own doc says it answers "does anyone ask?"; a condition asks. Scanning
    // the relation directly rather than through `provision_conditions`, which is
    // CARRIER-keyed and would need a sort to ask about — the question here is
    // program-wide.
    if let Some(cond_sym) = kb.try_resolve_symbol("anthill.reflect.ProvidesConditionInfo") {
        for rid in kb.rules_by_functor(cond_sym) {
            let Some((_, _, condition)) = decoded_condition_row(kb, rid) else {
                continue;
            };
            if condition_names_spec(kb, &condition, canon) {
                return true;
            }
        }
    }
    false
}

/// WI-20260921-28TAT — does this provision condition name `canon`?
///
/// THROUGH [`spec_base_functor`], NOT [`push_op_requires_clause`]. The two clause
/// channels have DIFFERENT SHAPES and the first cut used the wrong one: an op-`requires`
/// clause is a bare `Fn{spec, bindings}`, so its head functor IS the spec, while a
/// provision condition arrives in `SortView` shape, whose head functor is
/// `anthill.reflect.SortView` and whose spec sits at positional 0. MEASURED: read with
/// the bare-application reader, all 21 stdlib condition facts answered
/// `anthill.reflect.SortView` — including `Error provides ErrorTag :- TypeValue` — so
/// the leg was present, ran, and matched nothing.
///
/// A CONJUNCTION (`:- Eq[T], TypeValue[T]`) lowers to one `conjunction(..)` value whose
/// own functor would hide both specs, so it is flattened rather than shape-tested.
fn condition_names_spec(kb: &KnowledgeBase, condition: &Value, canon: Symbol) -> bool {
    if let Some(base) = spec_base_functor(kb, condition) {
        if kb.canonical_sort_sym(base) == canon {
            return true;
        }
    }
    // The conjunction case: `conjunction(a, b)` carries its conjuncts as children, each
    // itself a `SortView`.
    let Value::Term { id, .. } = condition else {
        return false;
    };
    let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = kb.get_term(*id)
    else {
        return false;
    };
    if kb.local_name_of(*functor) != "conjunction" {
        return false;
    }
    let kids: Vec<TermId> = pos_args
        .iter()
        .copied()
        .chain(named_args.iter().map(|(_, t)| *t))
        .collect();
    kids.iter()
        .any(|a| condition_names_spec(kb, &Value::term(*a), canon))
}

pub(super) fn op_requires_entries(kb: &KnowledgeBase, op_sym: Symbol) -> Vec<RequiresEntry> {
    let Some(rec) = crate::kb::op_info::lookup_operation_info(kb, op_sym) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for v in &rec.requires {
        // WI-662: preserve a denoted op-`requires` clause too (was `if let
        // Value::Term` — dropping `Value::Node` clauses for want of a `TermId`).
        push_op_requires_clause(kb, v, &mut out);
    }
    out
}

/// Decode one operation `requires` clause into [`RequiresEntry`]s. A multi-goal
/// clause (`requires A, B`) lowers to `conjunction(A, B)` (load's `convert_clause_list`),
/// so flatten it into its conjuncts — otherwise the conjunction functor would mask both
/// specs and silently drop them. A single spec application is itself one entry; a clause
/// with no resolvable spec functor carries no projectable members (skipped — it can never
/// satisfy the member-declared + mentions-subject candidate filter regardless).
///
/// WI-662: a ground clause takes the byte-identical `TermId` walk; a denoted
/// `Value::Node` clause (`requires Foo[E = Modify[c]]`) is decoded via `TermView`
/// — an op-`requires` clause is a bare `Fn{spec, bindings}`, so the base sort IS
/// the head functor (not `spec_base_functor`'s positional-0 SortView shape).
pub(super) fn push_op_requires_clause(
    kb: &KnowledgeBase,
    clause: &Value,
    out: &mut Vec<RequiresEntry>,
) {
    if let Value::Term { id, .. } = clause {
        push_op_requires_clause_term(kb, *id, out);
        return;
    }
    match clause.head(kb) {
        ViewHead::Functor {
            functor: Some(f),
            pos_arity,
            ..
        } if kb.local_name_of(f) == "conjunction" => {
            for i in 0..pos_arity {
                if let Some(child) = clause.pos_arg(kb, i) {
                    push_op_requires_clause(kb, &child.to_value(), out);
                }
            }
        }
        // Match the ground `push_op_requires_clause_term` exactly: a FUNCTOR head at
        // any arity — the bare spelling included, since WI-20260902-CZJ2N — becomes an
        // entry; an `Ident` (or functor-less) head is skipped (WI-662).
        ViewHead::Functor {
            functor: Some(f), ..
        } => {
            out.push(RequiresEntry {
                required_sort: f,
                spec: clause.clone(),
                // An OP-scoped `requires` is always inbound: only a SORT can carry
                // the `provides` clause that self-supplies one.
                supply: SupplySource::Required,
            });
        }
        _ => {}
    }
}

/// WI-662: the ground `TermId` walk under [`push_op_requires_clause`].
fn push_op_requires_clause_term(kb: &KnowledgeBase, tid: TermId, out: &mut Vec<RequiresEntry>) {
    match kb.get_term(tid) {
        Term::Fn {
            functor, pos_args, ..
        } if kb.local_name_of(*functor) == "conjunction" => {
            let conjuncts: Vec<TermId> = pos_args.iter().copied().collect();
            for c in conjuncts {
                push_op_requires_clause_term(kb, c, out);
            }
        }
        Term::Fn { functor, .. } | Term::Ref(functor) => {
            out.push(RequiresEntry {
                required_sort: *functor,
                spec: Value::term(tid),
                supply: SupplySource::Required,
            });
        }
        _ => {}
    }
}

/// WI-428: resolve a RIGID type-receiver projection (`P.Key` / `MemStore.Key`) at an
/// elimination site — the formation-validation rules of design §5.3, run in the typer
/// (where the `requires` chain is complete regardless of source order), not the loader
/// (which only classifies).
///
///   - **Concrete / bare sort subject** (`sort == subject`, e.g. `MemStore.Key`): must
///     δ-ground fully via [`project_type_member`] (a manifest binding, an alias shape,
///     or a provided spec's binding). A declared-but-unbound member (`Storage.Key` —
///     the spec sort itself) is the `T#K` carrier-conflation and is LOUDLY rejected:
///     a type-keyed neutral over a bare spec would equate the members of two distinct
///     carriers.
///   - **Rigid type-parameter subject** (`P.Key`): carrier-precise bound lookup — the
///     candidates are the `requires` entries of the declaring sort that DECLARE the
///     member AND MENTION the subject param among their binding values. No candidate →
///     loud error; several → loud ambiguity error (so `(var, member)` determines the
///     bound uniquely — the §5.3 deferred-equivalent identity); exactly one →
///     δ-THROUGH-THE-BOUND when the entry binds the member (`requires Storage[C = P,
///     Key = String]` ⟹ `P.Key = String`), else the projection stays the rigid NEUTRAL
///     (compared by the ζ arm of [`expr_carried_zeta`]).
pub(super) fn resolve_rigid_projection(
    kb: &mut KnowledgeBase,
    decl_sort: Symbol,
    subject: &Value,
    member: Symbol,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Result<ProjResult, TypeError> {
    let member_str = kb.local_name_of(member).to_owned();
    let Value::Term {
        id: subject_term, ..
    } = subject
    else {
        return Err(projection_type_error(
            ctx,
            span,
            "rigid type projection subject is not a sort / type-parameter reference",
        ));
    };
    let key = subject_key_of_term(kb, *subject_term).ok_or_else(|| {
        projection_type_error(
            ctx,
            span,
            "rigid type projection subject is not a sort / type-parameter reference",
        )
    })?;
    // Concrete / bare sort subject: keyed by the declaring-sort symbol itself (the
    // loader's `sort slot == var slot` discriminator).
    if let SubjectKey::Sym(subject_sym) = key {
        if same_sort_canonical(kb, subject_sym, decl_sort) {
            let recv = Value::term(kb.make_sort_ref(subject_sym));
            return match project_type_member(kb, &recv, &member_str, None, ctx, span)? {
                // WI-391: a ground member projects to the canonical `Ref(s)` shape (the
                // producer no longer emits a nullary `Fn{s}` binding here).
                ProjResult::Grounded(v) => Ok(ProjResult::Grounded(v)),
                ProjResult::Neutral => {
                    let sort_name = kb.qualified_name_of(subject_sym).to_owned();
                    let short = kb.local_name_of(subject_sym).to_owned();
                    Err(projection_type_error(
                        ctx,
                        span,
                        &format!(
                            "'{short}.{member_str}' is not manifest: '{sort_name}' declares \
                         '{member_str}' but does not bind it — a projection off the spec sort \
                         itself would conflate distinct carriers; project off a value \
                         (`s.{member_str}`) or a `requires`-bounded type parameter \
                         (`P.{member_str}`)",
                        ),
                    ))
                }
            };
        }
    }
    // Rigid type-parameter subject: carrier-precise bound lookup, keyed by the
    // canonical SubjectKey (the param's alias-var id — stable across the param's
    // symbol registrations and the deep walk's alias resolution / rigidification).
    // WI-383: when the subject is an OPERATION type-parameter, the licensing bound is
    // the operation's OWN `requires Spec[C = T]` clause (on `OperationInfo.requires`),
    // NOT a sort-level `SortRequiresInfo` chain — so consult the op's requires there.
    let chain = if kb.kind_of(decl_sort) == Some(crate::intern::SymbolKind::Operation) {
        op_requires_entries(kb, decl_sort)
    } else {
        requires_chain(kb, decl_sort)
    };
    // WI-428/430: the carrier-precise candidate filter — the SAME `requires_entry_lends_-
    // member` predicate the `ExprCarried` neutral gate uses (one source of truth for which
    // bound's carrier is this subject).
    let candidates: Vec<&RequiresEntry> = chain
        .iter()
        .filter(|e| requires_entry_lends_member(kb, e, key, &member_str))
        .collect();
    match candidates.as_slice() {
        [] => {
            // WI-383 SELF-CARRIER (implicit licensing): an OPERATION type-param projection
            // `T.member` whose op has NO `requires` bound mentioning the subject is
            // SELF-LICENSED — the obligation "the carrier bound to T has member `member`"
            // is forwarded, discharged at a concrete call against the carrier's OWN
            // declared `sort <member>` (ground_rigid_projection_if_concrete's self-carrier
            // arm). It stays the rigid NEUTRAL here. A bound that DOES mention the subject
            // but fails to declare `member` is a typo (or a sort-type-param projection),
            // not self-carrier → keep the loud error.
            let is_op = kb.kind_of(decl_sort) == Some(crate::intern::SymbolKind::Operation);
            let mentions_subject = chain.iter().any(|e| spec_mentions_key(kb, &e.spec, key));
            if is_op && !mentions_subject {
                Ok(ProjResult::Neutral)
            } else {
                Err(projection_type_error(
                    ctx,
                    span,
                    &format!(
                    "no `requires` bound on '{}' mentioning '{}' declares a member '{member_str}'; \
                     cannot project '{}.{member_str}'",
                    kb.qualified_name_of(decl_sort).to_owned(),
                    type_display_name_value(kb, subject),
                    type_display_name_value(kb, subject),
                ),
                ))
            }
        }
        [entry] => match spec_binding_value(kb, &entry.spec, &member_str) {
            // δ-through-the-bound. The stored application is AUTO-COMPLETED: an
            // unwritten member's binding is a placeholder ref to the SPEC'S OWN param
            // (`Key = Storage.Key`) — only THAT binding means "bound-open" (the rigid
            // NEUTRAL). Any other leaf is a user-written binding and grounds: a
            // concrete sort (`Key = String`), an opaque nominal (`Key = Token`), or a
            // sibling param of the declaring sort (`Key = K` — grounds to `K`'s ref,
            // resolved by the ordinary alias machinery downstream).
            Some(v) => {
                let binding_key = subject_key_of_term(kb, v);
                let placeholder_key = spec_member_param_key(kb, entry.required_sort, &member_str);
                let is_placeholder = match (binding_key, placeholder_key) {
                    (Some(b), Some(p)) => subject_keys_equal(kb, b, p),
                    // The spec's own param symbol is not identifiable: conservatively
                    // treat a var-keyed leaf as the placeholder (sound — stays rigid).
                    (Some(SubjectKey::Var(_)), None) => true,
                    _ => false,
                };
                // A binding to ANOTHER param of the DECLARING sort (`Key = K`, the
                // carrier `C = P` included) stays rigid too: cross-param δ needs the
                // rigid-substitution coherence of the call/body world (increment B) —
                // grounding to the sibling's bare ref here mis-compares against the
                // rigidified forms the signature walk produces. Sound: at most
                // over-rejection, never a wrong ground type.
                let is_sibling_param = binding_key.is_some_and(|b| {
                    kb.type_params_of_sort(decl_sort).iter().any(|p| {
                        spec_member_param_key(kb, decl_sort, p)
                            .is_some_and(|k| subject_keys_equal(kb, b, k))
                    })
                });
                if is_placeholder || is_sibling_param {
                    Ok(ProjResult::Neutral)
                } else {
                    match normalize_spec_binding_type(kb, v) {
                        Some(ty) => Ok(ProjResult::Grounded(Value::term(ty))),
                        None => Err(projection_type_error(
                            ctx,
                            span,
                            &format!(
                                "'{}.{member_str}' is bound by its `requires` application to \
                             a structured type; δ through a structured bound binding is \
                             not yet supported",
                                type_display_name_value(kb, subject),
                            ),
                        )),
                    }
                }
            }
            // No binding slot at all: the projection is the rigid neutral.
            None => Ok(ProjResult::Neutral),
        },
        _ => Err(projection_type_error(
            ctx,
            span,
            &format!(
                "ambiguous projection '{}.{member_str}': several `requires` bounds on '{}' \
             mentioning it declare '{member_str}'; multi-bound projection is not yet \
             supported",
                type_display_name_value(kb, subject),
                kb.qualified_name_of(decl_sort).to_owned(),
            ),
        )),
    }
}

/// WI-428: the [`SubjectKey`] of a spec's OWN member param (`Storage.Key`) — the
/// identity the requires-tree's auto-completed placeholder binding carries for an
/// unwritten member. `None` when the spec's param symbol is not registered under the
/// expected qualified name.
fn spec_member_param_key(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    member: &str,
) -> Option<SubjectKey> {
    let qn = format!("{}.{member}", kb.qualified_name_of(spec_sort));
    let sym = *kb.symbols.by_qualified_name.get(&qn)?;
    Some(sym_subject_key(kb, sym))
}

/// WI-428: the canonical identity KEY of a rigid-projection subject / a
/// `requires`-binding leaf. A type-parameter (`sort P = ?`) is keyed by its ALIAS-VAR
/// id: the deep walks resolve a param `Ref` into that var (possibly rigidified by
/// WI-392/424), and the `requires` bindings may name a different symbol registration
/// of the same param — the var id is the one identity all spellings share. A
/// non-alias sort is keyed by its symbol (compared via [`same_sort_canonical`]).
#[derive(Clone, Copy)]
pub(super) enum SubjectKey {
    Var(u32),
    Sym(Symbol),
}

/// WI-1059 — if `ty` is a projection `⟨r⟩.M` whose member `M` names a DECLARED type
/// parameter of `sort_sym`, the qualified symbol of that parameter (`<sort_sym>.M`).
///
/// The reader for one fact: a materialized unwritten slot spells its parameter as the
/// projection off the value that carries it ([`rigidify_unwritten_sort_params`]), so
/// `State`'s `P` reaches the projection machinery as `s.P` instead of `Ref(P)`. It is the
/// same parameter — a different SPELLING of it, exactly as `type_param_global_var` bridges
/// the short and op-scoped spellings — and the two sites that must not be fooled by the
/// change of spelling are [`resolve_field_type`]'s declaring-sort verdict and
/// [`project_type_member`]'s carrier key.
///
/// `None` for a non-projection, for a projection off a member that is not a parameter (an
/// ordinary field), and when `sort_sym` is absent.
fn projected_param_of_sort(
    kb: &KnowledgeBase,
    ty: &Value,
    sort_sym: Option<Symbol>,
) -> Option<Symbol> {
    let sort_sym = sort_sym?;
    let TypeExtractor::ExprCarried { member, .. } = extract_type(kb, ty) else {
        return None;
    };
    // WI-954: "is `M` a declared parameter of `sort_sym`" and "which symbol is it" were
    // two questions asked of two different tables; the owner's own declaration list
    // answers both at once.
    kb.type_param_sym_of(sort_sym, short_name_of(kb.local_name_of(member)))
}

pub(super) fn subject_key_of_term(kb: &KnowledgeBase, t: TermId) -> Option<SubjectKey> {
    match kb.get_term(t) {
        Term::Var(Var::Global(v) | Var::Rigid(v)) => Some(SubjectKey::Var(v.raw())),
        _ => spec_binding_head_sym(kb, t).map(|s| sym_subject_key(kb, s)),
    }
}

fn sym_subject_key(kb: &KnowledgeBase, s: Symbol) -> SubjectKey {
    if let Some(target) = resolve_sort_alias(kb, s) {
        if let Term::Var(Var::Global(v) | Var::Rigid(v)) = kb.get_term(target) {
            return SubjectKey::Var(v.raw());
        }
    }
    SubjectKey::Sym(s)
}

pub(super) fn subject_keys_equal(kb: &KnowledgeBase, a: SubjectKey, b: SubjectKey) -> bool {
    match (a, b) {
        (SubjectKey::Var(x), SubjectKey::Var(y)) => x == y,
        (SubjectKey::Sym(x), SubjectKey::Sym(y)) => same_sort_canonical(kb, x, y),
        _ => false,
    }
}

/// WI-428: does a `requires` spec application mention the subject KEY among its
/// TOP-LEVEL binding values (`requires Storage[C = P]` mentions `P`)? Nested mentions
/// (`Storage[C = List[P]]`) are not yet read — the candidate filter is conservative
/// (an unmentioned subject surfaces the loud no-bound error, never a silent pick).
pub(super) fn spec_mentions_key(kb: &KnowledgeBase, spec: &Value, key: SubjectKey) -> bool {
    // WI-662: ground fast path — byte-identical to the pre-WI-662 term read.
    if let Value::Term { id, .. } = spec {
        let Term::Fn { named_args, .. } = kb.get_term(*id) else {
            return false;
        };
        return named_args.iter().any(|(_, v)| {
            subject_key_of_term(kb, *v).is_some_and(|k| subject_keys_equal(kb, k, key))
        });
    }
    // Denoted spec — check each binding's subject key via TermView. A denoted
    // binding value (`Value::Node`) has no term subject key (`subject_key_of_term`
    // is term-only), so it contributes no match — the deferred parametric-effect
    // boundary, consistent with the ground path.
    spec.named_keys(kb).into_iter().any(|k| {
        spec.named_arg(kb, k)
            .and_then(|it| it.as_term_id())
            .and_then(|v| subject_key_of_term(kb, v))
            .is_some_and(|sk| subject_keys_equal(kb, sk, key))
    })
}

/// The head symbol of a `requires`-application binding VALUE leaf — `Ref(s)` (a
/// type-param binding, `make_sort_ref`), a NULLARY `Fn{s}` (a plain sort name via
/// `name_to_sort_term`), or an `Ident(s)`: [`view_ref_symbol`], the one bare-name reader
/// since c1872e94. A structured binding (a nested application) is not a leaf → `None`.
///
/// WI-20260923-N3W68 (#13) — this was its own match, and it differed from
/// [`view_ref_symbol`] twice: it did not read an `Ident`, and it fell back to
/// [`extract_sort_ref_sym`] for "the deep `sort_ref(name: Ref(s))`", a form [`type_head`]
/// does not recognize (it reads as `Parameterized { base: sort_ref }`, and nothing mints
/// it since WI-361) — so the fallback answered `None` for every term the arms above had
/// not. MEASURED, neither difference was reachable: a probe on both fired zero times
/// across the workspace suite. The delegation removes the second reader, not a behaviour
/// any corpus sees.
pub(super) fn spec_binding_head_sym(kb: &KnowledgeBase, v: TermId) -> Option<Symbol> {
    view_ref_symbol(kb, &TermIdView(v))
}

/// The binding VALUE a `requires` application carries for `member`, when bound
/// (`requires Storage[C = P, Key = String]` binds `Key`).
pub(super) fn spec_binding_value(kb: &KnowledgeBase, spec: &Value, member: &str) -> Option<TermId> {
    // WI-662: ground fast path — byte-identical to the pre-WI-662 term read.
    if let Value::Term { id, .. } = spec {
        let Term::Fn { named_args, .. } = kb.get_term(*id) else {
            return None;
        };
        return named_args
            .iter()
            .find(|(p, _)| kb.local_name_of(*p) == member)
            .map(|(_, v)| *v);
    }
    // Denoted spec — the member's binding via TermView, when it is a ground term.
    // A denoted binding value has no `TermId`; callers treat `None` as "not a
    // projectable member" (the deferred parametric-effect boundary).
    let key = spec
        .named_keys(kb)
        .into_iter()
        .find(|k| kb.local_name_of(*k) == member)?;
    spec.named_arg(kb, key).and_then(|it| it.as_term_id())
}

/// Normalize a `requires`-binding value LEAF to the plain TYPE shape (`Ref(s)`). A
/// structured binding has no plain normalization yet → `None` (the caller surfaces a
/// loud not-yet-supported error, never a silently wrong shape).
pub(super) fn normalize_spec_binding_type(kb: &mut KnowledgeBase, v: TermId) -> Option<TermId> {
    let s = spec_binding_head_sym(kb, v)?;
    if matches!(kb.get_term(v), Term::Ref(_)) {
        return Some(v);
    }
    Some(kb.alloc(Term::Ref(s)))
}

/// WI-20260909-S8CBV — the sentence a FAILED δ contributes to a requirement refusal.
///
/// Both projection-carrying sites (the bridge and [`build_op_scoped_dicts`]) let an
/// un-eliminable spec ride on, so a δ FAILURE and a δ NEUTRAL reach the same "still a
/// projection" verdict below. They are different faults — a member the receiver's sort
/// does not declare, versus a receiver this call leaves abstract — and reporting them
/// with one sentence told the author their ARGUMENTS were wrong when the REQUIREMENT
/// was. `/code-review` drove it. Every projection failure is raised through
/// [`projection_type_error`], whose `actual` is the sentence; anything else renders
/// generically rather than silently as nothing.
pub(super) fn delta_failure_text(e: &TypeError) -> String {
    match e {
        TypeError::Other { actual, .. } => actual.clone(),
        _ => "the projection could not be eliminated at this call".to_owned(),
    }
}

/// A loud [`TypeError`] for an ill-formed / unsupported type projection.
/// WI-399: the error context is now THREADED (was hardcoded `OperationReturn`) so a
/// projection eliminated at a non-call site reports the right place — a `let`-binding
/// annotation (`LetBinding`), not a phantom operation return. The op-call callers
/// (`check_apply_iter`) still pass `OperationReturn`, preserving their message.
/// WI-510: `#[track_caller]` so the `here()` origin threads through to the real
/// call site rather than collapsing all 10+ callers to this helper's own line.
///
/// (This doc and the attribute sat above [`delta_failure_text`] from WI-20260909-S8CBV,
/// which inserted that function between them and this one — so the attribute tracked a
/// function that builds no error, and every projection error's origin was this helper's
/// own line. `projection_error_origin_test` drives the attribute where it belongs.)
#[track_caller]
pub(super) fn projection_type_error(
    ctx: &TypeErrorContext,
    span: Option<Span>,
    msg: &str,
) -> TypeError {
    TypeError::Other {
        site: TypeError::here(),
        span,
        context: ctx.clone(),
        expected: "a well-formed type projection".to_owned(),
        actual: msg.to_owned(),
    }
}

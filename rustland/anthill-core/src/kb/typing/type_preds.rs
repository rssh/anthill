//! Predicates over types: groundness, type variables, and a few recognizers.

use super::*;

/// True iff `value` references an abstract type-parameter — directly as a
/// `Term::Var`, or as a `Term::Ref` / `Term::Ident` to a sort-level type-param
/// symbol (the loader signal for `sort T = ?`).
pub(crate) fn is_type_param_value(kb: &KnowledgeBase, value: TermId) -> bool {
    match kb.get_term(value) {
        Term::Var(_) => true,
        Term::Ref(sym) | Term::Ident(sym) => is_sort_param_symbol(kb, *sym),
        // WI-359: a bare param name also surfaces as a nullary `Fn` (the
        // `make_name_term` shape — e.g. an enclosing sort's open param
        // captured into a `requires` SortView). Treat `Fn{param}` like
        // `Ref(param)` so defer-to-requirement matching and candidate
        // leniency see it as the wildcard it is.
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => is_sort_param_symbol(kb, *functor),
        _ => false,
    }
}

/// WI-387 (FIX 3) — true iff `tid` is a fully-ground type value: no logic var
/// and no sort-parameter reference ANYWHERE in its structure. The recursive
/// dual of [`is_type_param_value`] (which tests only the head). A carrier's
/// provider-fact binding that is ground (the written empty row `{}` for a pure
/// carrier's `Stream.E`) COVERS its spec param in the abstract/requires-coverage
/// check, whereas a binding that mentions a type-param (`Stream.T ↦ List.T`, or
/// a nested `C = List[T]`) stays abstract and still demands a `requires`.
pub(super) fn type_value_is_ground(kb: &KnowledgeBase, tid: TermId) -> bool {
    type_value_is_ground_g(kb, tid, false)
}

/// WI-1059 — "GROUND" MEANT TWO THINGS, and a skolem is the value that separates them.
///
/// * `rigid_ok = false` — CONCRETE: mentions no type parameter. This is WI-387 FIX 3's
///   question ("does this provider-fact binding COVER its spec param, or does it stay
///   abstract and still demand a `requires`?"), and a `Var::Rigid` is abstract — it IS the
///   enclosing sort's type parameter, skolemized.
/// * `rigid_ok = true` — DETERMINED: nothing is left for a later pass to decide. This is
///   WI-385's question at [`validate_arg_against_param`] ("may this pair be checked, or is
///   conformance still someone else's to settle?"), and a skolem is fully determined — it
///   unifies with nothing but itself, so no later pass could decide it and "leave it to
///   dispatch" leaves it to nobody.
///
/// The two were ONE predicate, answering `false` for every var kind, and the conflation is
/// exactly why WI-1059's second leak survived: `feed[E](s: Stream[T = Int64, E = E]) =
/// takes_pure(s)` was rigidified by WI-392 all along and STILL loaded, because the rigid
/// made the pair non-ground and the gate returned `Ok` without checking anything. Under
/// `rigid_ok` the pair reaches `types_compatible`, whose row arm refuses it at
/// `bind_row_tail` (WI-336: a rigid tail is not bindable) — the refusal WI-392 always
/// intended and never reached.
///
/// MEASURED, and the reason this is a split rather than a one-line flip: answering `true`
/// for BOTH consumers breaks `wi606_unqualified_dispatch_return_threading_test` — a
/// `requires FiniteCollection[C = S, …]` on the enclosing sort stops covering its abstract
/// parameter once that parameter's skolem reads as concrete, and the coverage check demands
/// a `requires` the source already wrote.
pub(super) fn type_value_is_ground_g(kb: &KnowledgeBase, tid: TermId, rigid_ok: bool) -> bool {
    type_view_is_ground_g(kb, &TermIdView(tid), rigid_ok)
}

/// WI-20260904-B1KFS — THE SAME QUESTION, ASKED THROUGH [`TermView`] SO EVERY CARRIER ANSWERS
/// IT THE SAME WAY.
///
/// **CARRIER-NEUTRAL MEANS `Fn{Map, K = Bool}` AND ITS `Value::Entity` TWIN CANNOT ANSWER
/// DIFFERENTLY**, and until this they did: the hash-consed spelling got the structural walk
/// and the `Value::Entity` spelling got [`resolved_type_is_ground_g`]'s `_ => false`, i.e.
/// "not ground" — which at this gate's callers means SKIP THE CHECK. One type, two answers,
/// and the disagreeing one silently withholds a type check.
///
/// The two spellings are not exotic: `KnowledgeBase::fn_value` builds the `Entity` for ANY
/// application with a non-leaf child, so a type carrying an occurrence child IS an
/// `Entity` — which is exactly what `KnowledgeBase::reify` hands back, and exactly why
/// routing a type position's σ through `reify` reported ZERO errors on a wrong program
/// (WI-20260903-H054K measured that and routed around it; this removes the reason it had
/// to). Censused at delivery: **0** `Value::Entity`s reach this gate across 36 binaries and
/// 6 376 tests, so this is a HARDENING and not a live fix — no existing row moves. What
/// drives it is the carrier-agreement property itself, asserted directly:
/// `tests::groundness_gate_carrier_agreement_test`.
///
/// TWO SIBLINGS STILL DISAGREE and are **WI-20260904-B1KFS**, not fixed here:
/// [`type_display_name_value`] renders this same type `"Map[K = Bool]"` as a term and `"Map"`
/// as an entity — the bindings dropped from a user-facing diagnostic — and
/// [`walk_type_deep_value_g`]'s `other => other.clone()` never σ-resolves an entity-carried
/// type's inner vars, which is the mistake WI-441 records having already made and fixed for
/// `Value::Node`. Both are measured there; the display one is a merge of two hand-kept
/// renderers rather than an arm, which is why it is a ticket.
///
/// ONE WALK, not a third: [`type_value_is_ground_g`] is now a thin delegate, so the
/// `TermId` reading and the `Value` reading cannot drift the way they just did.
fn type_view_is_ground_g<V: TermView>(kb: &KnowledgeBase, v: &V, rigid_ok: bool) -> bool {
    match v.head(kb) {
        ViewHead::Var(Var::Rigid(_)) => rigid_ok,
        ViewHead::Var(_) => false,
        ViewHead::Const(_) | ViewHead::Bottom => true,
        ViewHead::Ident(sym) => !is_sort_param_symbol(kb, sym),
        // A NULLARY functor is the bare sort reference (WI-20260902-CZJ2N retired the
        // separate `Ref` head), so `Ref(S)` and `Fn{S, …}` are one arm — as they were in the
        // term walk this replaces, whose `Ref | Ident` and `Fn` arms asked the same question
        // of the functor symbol.
        ViewHead::Functor {
            functor,
            pos_arity,
            named_arity: _,
        } => {
            if functor.is_some_and(|f| is_sort_param_symbol(kb, f)) {
                return false;
            }
            (0..pos_arity).all(|i| {
                v.pos_arg(kb, i)
                    .is_some_and(|c| type_view_is_ground_g(kb, &c, rigid_ok))
            }) && v.named_keys(kb).iter().all(|k| {
                v.named_arg(kb, *k)
                    .is_some_and(|c| type_view_is_ground_g(kb, &c, rigid_ok))
            })
        }
        // A carrier with no structure to read — a closure, a stream, a `ParseAux`. It is not
        // a type and cannot be judged one; `false` withholds the verdict, which is what the
        // term walk's `ParseAux` arm already answered.
        ViewHead::Opaque => false,
    }
}

/// WI-385: groundness of a substitution-RESOLVED type `Value` — the gate for
/// argument / field type validation. Only a fully-concrete declared type
/// checked against a fully-concrete actual type may fail; a type-parameter
/// position (`T`) or an unresolved inference var (`?_` / `Value::Var`) stays
/// UNCHECKED. This is what keeps the validation from false-positiving on the
/// pervasive polymorphic signatures (`add(a: T, b: T)`, `some(value: T)`,
/// `cons(head: T, …)`): those param/field types resolve to a sort-param or a
/// still-free var, whose conformance the spec-op dispatch / return-conformance
/// path settles, not this check. EVERY carrier is judged — see
/// [`resolved_type_is_ground_g`]; this doc used to promise that a non-`Term`
/// carrier returned `false` (skip), which stopped being true at WI-470.
pub(super) fn resolved_type_is_ground(kb: &KnowledgeBase, v: &Value) -> bool {
    resolved_type_is_ground_g(kb, v, false)
}

/// WI-1059 — [`resolved_type_is_ground`] at the DETERMINED reading: a `Var::Rigid` counts.
/// See [`type_value_is_ground_g`] for why the two readings are different questions and
/// which consumer asks which. Used at the [`validate_arg_against_param`] gate only.
pub(super) fn resolved_type_is_determined(kb: &KnowledgeBase, v: &Value) -> bool {
    resolved_type_is_ground_g(kb, v, true)
}

/// The shared body of [`resolved_type_is_ground`] (`rigid_ok = false`, CONCRETE) and
/// [`resolved_type_is_determined`] (`rigid_ok = true`, DETERMINED) — the two readings
/// [`type_value_is_ground_g`] documents. Three arms, by carrier: a hash-consed type through
/// [`type_value_is_ground_g`]; an occurrence through [`node_type_is_ground_g`], which keeps
/// its own arm for the type-specific judgments it names; and every other carrier through
/// the shared view walk [`type_view_is_ground_g`] (which is where the old `_ => false`
/// went — one type, one answer, whatever carrier it rides in on).
fn resolved_type_is_ground_g(kb: &KnowledgeBase, v: &Value, rigid_ok: bool) -> bool {
    match v {
        Value::Term { id: t, .. } => type_value_is_ground_g(kb, *t, rigid_ok),
        // WI-470: an occurrence-primary type (the flipped arrow / row / parameterized
        // form) is ground exactly when its spine carries no free type-var / sort-param
        // / row-tail leaf — the same predicate `type_value_is_ground` applies to the
        // hash-consed twin, walked structurally so a flipped GROUND arrow reads as
        // ground (and is WI-385-checked) instead of being skipped as "non-Term".
        // THE OCCURRENCE CARRIER KEEPS ITS OWN ARM, and not because a view cannot reach it:
        // three of its judgments are TYPE-SPECIFIC rather than structural, and a view walk
        // would silently answer all three differently — a `denoted`'s CLOSEDNESS (which
        // additionally refuses a binder-local param reference, WI-470), a `PolyType` being a
        // schema rather than a determined type (WI-1083), and a guarded effect atom whose
        // GUARD is deliberately not read (WI-478). Those are deferrals with named owners,
        // not the missing arm this ticket removed.
        Value::Node(occ) => node_type_is_ground_g(kb, occ, rigid_ok),
        // EVERY OTHER CARRIER through the shared view walk — `Value::Entity` and
        // `Value::Tuple` (a type application whose child is not leaf-lowering), the scalar
        // carriers of a §4.5 value-in-type, `Value::SymbolRef`, `Value::Var`. This was
        // `_ => false`, which is where one type got two answers depending on the carrier it
        // rode in on. See [`type_view_is_ground_g`].
        other => type_view_is_ground_g(kb, other, rigid_ok),
    }
}

/// WI-470: groundness of a `Value::Node`-carried type, walking the occurrence
/// `Type`/`EffectExpression` spine directly (no interning / materialization, so it
/// stays on the immutable `&KnowledgeBase` `resolved_type_is_ground` runs on).
/// Carrier-symmetric with the hash-consed twin [`type_value_is_ground`]: a ground
/// `TypeChild` defers to it (which rejects `Var` / sort-param leaves — so a row's
/// open `tail` Var makes the row non-ground), a poisoned child recurses, and a
/// `denoted` is ground iff its carried value has no free logical var (the same
/// answer `type_value_is_ground(make_denoted(value))` gives). Nothing is skipped:
/// every form's true groundness is computed.
/// WI-1059 — threading the DETERMINED-vs-CONCRETE reading
/// ([`type_value_is_ground_g`]) through the occurrence carrier. Threaded rather than left at
/// the concrete reading because
/// both carriers must key alike (WI-1016): a rigid nested in a `Value::Node` row tail is
/// the SAME skolem as one in the hash-consed twin, and a gate that admits one and skips the
/// other decides the same program two ways.
fn node_type_is_ground_g(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>, rigid_ok: bool) -> bool {
    let child_ground = |c: &TypeChild| match c {
        TypeChild::Interned(t) => type_value_is_ground_g(kb, *t, rigid_ok),
        TypeChild::Node(n) => node_type_is_ground_g(kb, n, rigid_ok),
    };
    match &occ.kind {
        NodeKind::Type(tn) => match tn {
            // WI-20260904-02ERR: THE SAME TWO ANSWERS `type_view_is_ground_g` gives a
            // `ViewHead::Var` — a rigid skolem is ground iff this gate says rigids count, a
            // flex `Global` never is. The carrier must not change the verdict (WI-20260904-B1KFS
            // is the ticket for exactly this class of two-carriers-two-answers bug).
            TypeNode::Var(Var::Rigid(_)) => rigid_ok,
            TypeNode::Var(_) => false,
            // WI-470: a denoted (value-in-type) is ground for THIS gate iff its value
            // is CLOSED — see [`denoted_value_is_closed`]. A closed denoted
            // (`Vector[Int64, 3]`, `Modify[store]`) is conformance-checked; a var-bearing
            // (`Vector[Int64, ?n]`) or binder-relative (`Modify[c]`, `c` a callback param)
            // denoted is deferred to the validator that can decide it (unification /
            // the alignment-aware `validate_callback_effect_row`). Nothing is skipped.
            TypeNode::Denoted { value } => denoted_value_is_closed(kb, value),
            TypeNode::Parameterized { base, bindings } => {
                child_ground(base) && bindings.iter().all(|(_, c)| child_ground(c))
            }
            TypeNode::EffectsRows { effects_expr } => child_ground(effects_expr),
            // WI-791: `arity` is a ground `Const(Int)` by construction and so cannot
            // change this verdict; it is checked anyway so the walk stays total over
            // the node's children.
            TypeNode::Arrow {
                param,
                result,
                effects,
                arity,
            } => {
                child_ground(param)
                    && child_ground(result)
                    && child_ground(effects)
                    && child_ground(arity)
            }
            TypeNode::ExprCarried { value, member } => child_ground(value) && child_ground(member),
            TypeNode::NamedTuple { fields } => list_records_to_pairs(kb, fields, "name", "type")
                .iter()
                .all(|(_, t)| resolved_type_is_ground_g(kb, t, rigid_ok)),
            // WI-1083 — A ∀ IS A SCHEMA, NOT A DETERMINED TYPE, so it is not ground:
            // this gate asks "is enough of this type known to judge it", and a
            // `PolyType` answers "not until it is instantiated". Every consumer DOES
            // instantiate first ([`instantiate_poly_type`]), so this arm reports on a
            // carrier that escaped instantiation, where withholding a verdict is the
            // conservative answer rather than a skipped check.
            TypeNode::PolyType { .. } => false,
        },
        NodeKind::EffectExpr(en) => match en {
            EffectExprNode::Merge { left, right } => child_ground(left) && child_ground(right),
            EffectExprNode::Present { label } | EffectExprNode::Absent { label } => {
                child_ground(label)
            }
            // WI-478: phase-1 ground-ness mirrors `present` — only the label counts.
            // The guard is conservatively-present metadata not used in resolution
            // (decompose ignores it), so its goal vars don't make the row non-ground.
            EffectExprNode::Guarded { label, .. } => child_ground(label),
            // An open row carries a row-tail Var ⇒ not ground.
            EffectExprNode::Open { tail } => child_ground(tail),
            EffectExprNode::EmptyRow => true,
        },
        // Not a type occurrence (an Expr/Pattern/RuleHead node never stands in a
        // type slot here) — conservatively unground (skip), as before.
        _ => false,
    }
}

/// WI-470: is a `denoted`'s carried VALUE closed — i.e. decidable by the generic
/// closed-type conformance check? Closed iff the value occurrence has NO free
/// logical var and NO reference to a binder-local parameter (`SymbolKind::Param`).
/// The non-closed shapes each route to the validator that CAN decide them, so
/// nothing is skipped:
///   * a free `Var` (`Vector[Int64, ?n]`) → inference (`unify_types`), not this gate;
///   * a binder-local param ref (`Modify[c]`, `c` the callback's OWN param) → the
///     label is meaningful only up to BINDER ALIGNMENT, which the generic structural
///     comparison cannot perform — `validate_callback_effect_row` owns it (it builds
///     the actual↔declared place map and compares aligned), so the generic gate must
///     defer rather than reject the alpha-equivalent `Modify[c]` vs `Modify[a]`;
///   * a closed value (`Vector[Int64, 3]` literal, `Modify[store]` global resource)
///     → IS closed → ground → conformance-checked here.
/// (A `denoted` always poisons to `Value::Node`, so it reaches the gate only through
/// [`node_type_is_ground`], never the term-side `type_value_is_ground` — the
/// param-relative refinement lives on the one carrier it flows through.)
pub(super) fn denoted_value_is_closed(kb: &KnowledgeBase, value: &Rc<NodeOccurrence>) -> bool {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(value)];
    while let Some(occ) = stack.pop() {
        match occ.as_expr() {
            // Any logic var ⇒ not closed — matching the term-side `type_value_is_ground`,
            // which rejects every `Term::Var` (Global = inference, deferred to unify;
            // DeBruijn/Rigid are not concrete either).
            Some(Expr::Var(_)) => return false,
            // A value-PLACE reference (op/callback param, result, field, let-local) is
            // binder-relative — meaningful only up to BINDER ALIGNMENT, which the generic
            // structural compare cannot do — so it is NOT closed; the alignment-aware
            // `validate_callback_effect_row` owns it. `is_value_place` is the shared
            // set the loader's `symbol_is_value_place` uses (no drift — the CallbackParam
            // own-param case `Modify[a]` is the one this gate must defer).
            Some(Expr::Ref(s)) | Some(Expr::Ident(s))
                if kb.kind_of(*s).is_some_and(|k| k.is_value_place()) =>
            {
                return false;
            }
            // A bare local-binder read (`?x` — a let/lambda binder) is binder-relative too.
            Some(Expr::VarRef { .. }) => return false,
            // A literal / global ref (Sort/Entity/Operation) / compound value — recurse
            // children (a field-path receiver may still reach a value-place ref).
            Some(e) => for_each_child(e, |c| stack.push(Rc::clone(c))),
            // A denoted's value is always an `Expr` occurrence; a non-`Expr` here is a
            // construction bug — surface it (loud) and conservatively defer, rather than
            // silently judging it closed.
            None => {
                debug_assert!(
                    false,
                    "denoted value occurrence is not an Expr: {:?}",
                    occ.kind
                );
                return false;
            }
        }
    }
    true
}

/// WI-385: is this resolved type the reflect `Term` sort (`anthill.reflect.Term`)?
/// The value↔Term boundary is a CONVERSION, not subtyping. Reflection
/// (value → Term) is TOTAL — every value has a Term representation
/// (`as_term[E](e) -> Term`, WI-406) — so ANY `actual` type conforms to a
/// declared `Term`. (Reification, Term → value, is PARTIAL and stays explicit
/// via the `term_as_entity` family, so the reverse is NOT accepted by the
/// validation.) `Term` is representation-specific, NOT a top type — keying the
/// type lattice on it would make it the universal default on every term (see the
/// note in `stdlib/anthill/prelude/sort.anthill`) — so this acceptance lives in
/// the WI-385 validation, never in `types_compatible` / the subtype relation.
pub(crate) fn is_reflect_term_type<V: TermView>(kb: &KnowledgeBase, ty: &V) -> bool {
    // `type_head` reads only the head (no binding materialization), enough here.
    matches!(type_head(kb, ty),
        TypeHead::SortRef(s) if kb.qualified_name_of(s) == "anthill.reflect.Term")
}

/// WI-385: is this resolved type an `anthill.prelude.Option` — bare `Option` or
/// applied `Option[T = …]`? The element peel for the WI-408 some-coercion
/// (`pub(crate)`: the loader's fact-field wrap tests field types with it).
pub(crate) fn is_option_type<V: TermView>(kb: &KnowledgeBase, ty: &V) -> bool {
    match type_head(kb, ty) {
        TypeHead::Parameterized { base } => kb.qualified_name_of(base) == "anthill.prelude.Option",
        TypeHead::SortRef(s) => kb.qualified_name_of(s) == "anthill.prelude.Option",
        _ => false,
    }
}

/// WI-1096: is this resolved type a VARIABLE — a declared type parameter (`T`), an
/// engine flex var, or a skolem — rather than a type that names something?
///
/// The distinction is which of two questions a declared type answers. A concrete type
/// says WHAT this position holds; a variable says only that the position is generic,
/// which is the same information an ABSENT declaration carries. The list-literal
/// lowering (`Loader::convert_term_with_expected`) is the caller and needs exactly
/// that: it declines to lower `[…]` where the declaration names another collection,
/// and must NOT decline where the declaration names nothing at all. `entity Box(v: T)`
/// and `Option.some(value: T)` are the two shapes that made this necessary — reading
/// their `T` as "some non-List type" left the literal flat and reproduced the WI-1096
/// wrong answer one field deep.
///
/// `pub(crate)`: the loader is the only reader, like [`is_option_type`] beside it.
pub(crate) fn is_type_variable<V: TermView>(kb: &KnowledgeBase, ty: &V) -> bool {
    matches!(
        type_head(kb, ty),
        TypeHead::TypeVar(_) | TypeHead::FlexVar(_) | TypeHead::Skolem(_)
    )
}

/// WI-20260911-5G28A — the `VarId` this type IS, when it is a variable a pin may BIND;
/// `None` otherwise.
///
/// TWO EXCLUSIONS, and both were `/code-review` findings on this ticket's own first cut,
/// where the gate asked [`is_type_variable`] — which names all THREE variable spellings —
/// while the pin could only ever bind one of them:
///
///  * a reflect `TypeVar` and a `Skolem` are variables, and are NOT bindable here. A
///    `Skolem` is a rigid unknown (it equals only an identical neutral) and a `TypeVar` is
///    the reflect placeholder; neither has a `VarId` this σ may write. Admitting them to
///    the gate and then failing to bind them turned a SUSPEND into a `Refuted` — a verdict
///    on an open variable, which is exactly what WI-067 forbids and what
///    [`pin_bound_from_value`]'s own doc promises not to do.
///  * a SORT's canonical type-parameter variable ([`KnowledgeBase::is_canonical_type_param_var`])
///    is a `Var::Global` like any other, so `type_head` reports it as a `FlexVar` and the
///    pin would happily bind it. It must not: `F` in a rule written inside
///    `sort Lib { sort F = ? }` is a projection off the RECEIVER's instance, decided by
///    whoever instantiates `Lib`, and binding it from one value would pin the receiver's
///    parameter for the whole resolution. It is the same exclusion the frame admission
///    makes, asked here in the pin's own terms.
///
/// Everything excluded falls through to [`type_bound_verdict`], which suspends on it
/// exactly as it did before this ticket.
pub(super) fn bindable_type_var<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Option<VarId> {
    match type_head(kb, ty) {
        TypeHead::FlexVar(vid) if !kb.is_canonical_type_param_var(vid) => Some(vid),
        _ => None,
    }
}

/// WI-20260911-5G28A — does this type MENTION a variable a pin may bind, at any depth?
///
/// The question [`resolved_var`] asks one level up: that one is "IS this type a
/// variable" (a whole-variable column), this one "is there a bindable variable IN it"
/// (`List[T = ?t]`, `Map[K = ?k, V = Int64]`). A rule head ties two columns through the
/// SECOND shape, and the applied-citation checker needs the distinction to choose
/// between pinning (bind the variable, narrow the surviving columns) and subtyping
/// (nothing to pin).
///
/// Children are walked through the VIEW's positional and named arities, because a sort
/// parameter rides as a NAMED argument (WI-361: `List[T = ?t]` is `Fn{List, T: ?t}`) and
/// a positional-only walk would answer `false` for the very shape this exists to catch.
pub(super) fn type_mentions_flex_var<V: TermView>(kb: &KnowledgeBase, ty: &V) -> bool {
    if bindable_type_var(kb, ty).is_some() {
        return true;
    }
    let ViewHead::Functor {
        pos_arity,
        named_arity,
        ..
    } = ty.head(kb)
    else {
        return false;
    };
    for i in 0..pos_arity {
        if ty
            .pos_arg(kb, i)
            .is_some_and(|a| type_mentions_flex_var(kb, &a))
        {
            return true;
        }
    }
    if named_arity > 0 {
        for key in ty.named_keys(kb) {
            if ty
                .named_arg(kb, key)
                .is_some_and(|a| type_mentions_flex_var(kb, &a))
            {
                return true;
            }
        }
    }
    false
}

/// WI-722: is this resolved type EXACTLY an occurrence type — a bare
/// `anthill.reflect.NodeOccurrence` or reflect `Expr`? A CONTAINER of one
/// (`Option[NodeOccurrence]`, `List[NodeOccurrence]`) is deliberately NOT — only
/// a directly spliceable occurrence counts (proposal 043.1 §3.1), so a runtime
/// reflect op like `operation_body -> Option[NodeOccurrence]` is never misread as
/// a macro. Mirrors [`is_reflect_term_type`]; `NodeOccurrence`/`Expr` are
/// non-parametric, so only the bare `SortRef` head matches.
pub(crate) fn is_occurrence_type<V: TermView>(kb: &KnowledgeBase, ty: &V) -> bool {
    matches!(type_head(kb, ty),
        TypeHead::SortRef(s)
            if matches!(kb.qualified_name_of(s),
                "anthill.reflect.NodeOccurrence" | "anthill.reflect.Expr"))
}

/// WI-722: is `op` a compile-time MACRO — a syntax→syntax operation whose EVERY
/// parameter type AND result type is an occurrence type ([`is_occurrence_type`])?
/// A macro appearing as the head of a fired `@[simp]` rule's RHS is EVALUATED at
/// compile time over its argument occurrences, and the occurrence it returns is
/// spliced as the rewrite result (proposal 043.1). There is NO marker — the
/// signature classifies it, and the SAME op is an ordinary function at a runtime
/// call site, a macro only as a `@[simp]` RHS.
///
/// Both conditions carry weight (043.1 §3.1): every argument being an occurrence
/// is 043 §4.2's argument-domain rule (the macro is fed the matched pattern-var
/// occurrences, so a value parameter would type-mismatch); the result being
/// EXACTLY an occurrence — not a container of one — is what makes it spliceable,
/// separating a macro from a compile-time guard reader (`min_sort(occ) -> Sort`:
/// expr in, value out).
pub fn is_macro(kb: &KnowledgeBase, op: Symbol) -> bool {
    let Some(info) = lookup_operation_info_full(kb, op) else {
        return false;
    };
    // At least one parameter: a macro is FED the matched pattern-var occurrences
    // (043 §4.2's argument-domain rule assumes ≥1 occurrence arg), so a nullary
    // occurrence-returning op is a constructor-like value, not a macro — it is not
    // silently evaluated at compile time nor subjected to the purity gate.
    !info.params.is_empty()
        && is_occurrence_type(kb, &info.return_type)
        && info.params.iter().all(|(_, t)| is_occurrence_type(kb, t))
}

/// WI-385: the base/head sort symbol of a ground type — `S` for a bare `S`, the
/// base `S` for an application `S[…]`; `None` for a structural form (arrow,
/// named_tuple, …). Used to test provider admissibility against a bare spec.
pub(super) fn type_base_sort_view<V: TermView>(kb: &KnowledgeBase, ty: &V) -> Option<Symbol> {
    match type_head(kb, ty) {
        TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => Some(s),
        _ => None,
    }
}

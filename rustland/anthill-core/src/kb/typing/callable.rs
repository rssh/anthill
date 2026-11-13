//! Callable shapes: the `Function` spec recognizer, arrow parts, conformance errors, and
//! what an application of a function value meets (the application match).

use super::*;

/// The qualified name of the stdlib sort that spells a function type at the
/// surface — the ONE place `kb::typing` spells it (WI-802). NOT crate-wide:
/// `eval`'s `runtime_carrier_sort` names it too, as one row of its value→carrier
/// table, where it is a PRODUCER rather than a recognizer.
pub(super) const FUNCTION_SPEC_QNAME: &str = "anthill.prelude.Function";

/// WI-802: the ONE recognizer for the stdlib `Function[A, B, E]` sort — the
/// surface spelling of the typer's canonical `arrow` (see [`arrow_parts`]).
/// Three sites hand-compared the name before; what regresses if that returns is
/// pinned by `wi802_function_spec_owner_tests` in `typing/tests.rs`. Same
/// discipline as [`crate::intern::positional_label`] for `_N` (WI-790).
///
/// Identity by QUALIFIED name, never by last segment — a bare top-level
/// `sort Function` is a DIFFERENT sort (spec §8.6, cf. [`same_qname`]).
/// `qualified_name_of` returns the short name for an unresolved symbol, which a
/// dotted literal cannot equal, so an unresolved `Function` is correctly not
/// recognized.
///
/// Takes the APPLIED head's `base` symbol rather than a `&V: TermView`, so —
/// unlike its siblings [`is_option_type`] / [`is_reflect_term_type`] — it has no
/// bare-`SortRef` arm. That is the pre-existing rule, stated rather than left
/// implicit in the signature: `Function` is parametric and every consumer here
/// wants its `B` (see [`function_spec_parts`]), so an unapplied `sort_ref`
/// `Function` names no result type and is not a callable.
pub(super) fn is_function_spec(kb: &KnowledgeBase, base: Symbol) -> bool {
    kb.qualified_name_of(base) == FUNCTION_SPEC_QNAME
}

/// Is this type's HEAD a callable — an `arrow`, or the applied `Function[A, B, E]`
/// spelling? The cheap gate for the sites that only need to know WHETHER a type is a
/// callback slot, not what its parts are: it reads the functor symbol off
/// [`type_head`] and stops, where [`arrow_parts`] interns five child keys and
/// materializes the children (for a `Parameterized` head, two `Vec`s plus a `Value`
/// clone per binding) before its caller throws them away.
///
/// ONE owner for two callers — [`validate_callback_effect_row`], which routes a callback
/// argument to the row check and so asks about THE SLOT's head, and
/// [`type_contains_callable`], the structural sibling that asks this at every node. Those
/// two must agree on what a callable IS; where they differ is only WHERE they ask, which
/// each site's own doc states.
///
/// DELIBERATELY WIDER THAN `arrow_parts(..).is_some()`, which additionally requires the
/// parts to materialize — it yields `None` for a `Function` head that binds no `B`
/// ([`function_spec_parts`]) and for an `arrow` whose children fail to read. Both are
/// callables by head, and for a gate whose `true` means "hands off" the head is the
/// right question; treating a malformed callable as non-callable is what would hand it
/// to a relation that is not its owner.
pub(super) fn type_head_is_callable<V: TermView>(kb: &KnowledgeBase, ty: &V) -> bool {
    match type_head(kb, ty) {
        TypeHead::Arrow => true,
        TypeHead::Parameterized { base } => is_function_spec(kb, base),
        _ => false,
    }
}

/// Does a callable appear ANYWHERE in this type — at the head, or nested inside a sort
/// application's bindings (`List[T = Function[A = X, B = Int64]]`)?
///
/// The STRUCTURAL sibling of [`type_head_is_callable`], which it asks at every node. The
/// two questions have genuinely different owners and neither generalizes the other:
/// [`validate_callback_effect_row`] routes THE SLOT, so the head is exactly its question;
/// [`validate_arg_against_param`]'s WI-836 deep-retry must not change any arrow ACCEPTANCE
/// decision, and `types_compatible` DECOMPOSES a sort application down to
/// `arrow_compatible_view` — so a nested callable is judged by the arrow relation just as a
/// top-level one is, and a head test would withhold the retry from exactly the shapes that
/// were measured and from none of the others.
///
/// MEASURED (2026-07-28): with only the head test, `take[X](l: List[T = Function[A = X, B =
/// Int64]], w: X)` applied to a list of a 2-parameter operation's eta arrow — which loads
/// clean before WI-836 — was newly REFUSED, as was the `Option[T = Function[…]]` twin. The
/// head test is not a cheaper approximation of this one; it is the wrong question here.
///
/// Runs on the DEEP-WALKED value, so it also catches a callable σ INTRODUCES that the
/// shallow reading never showed (`List[T = X]` with `X := (Int64) -> Bool`).
///
/// ONE ANSWER PER TYPE, whichever carrier it rides. An application with a child on another
/// carrier is an entity (`KnowledgeBase::fn_value`), and is read as its term twin is: its
/// head, else any child's, each child on its own carrier. It answered `true` — "a carrier
/// this cannot read" — and that withheld the argument check from a type applied to one that
/// holds a value: `Bag.merge(a, b)` over a `Bag[T = Foo[T = Int64, N = 3]]` and a `Bag[T =
/// Foo[T = String, N = 3]]` loaded (MEASURED). A leaf — a variable, a name, a literal — is
/// no callable on any spelling, as its term is not.
pub(super) fn type_contains_callable(kb: &KnowledgeBase, v: &Value) -> bool {
    match v {
        Value::Term { id: t, .. } => term_contains_callable(kb, *t),
        Value::Node(occ) => node_contains_callable(kb, occ),
        other => {
            type_head_is_callable(kb, other)
                || match other.head(kb) {
                    ViewHead::Functor { pos_arity, .. } => {
                        view_any_child(kb, other, pos_arity, |c| {
                            type_contains_callable(kb, &c.to_value())
                        })
                    }
                    _ => false,
                }
        }
    }
}

/// [`type_contains_callable`] over a hash-consed type term: this node's head, else any
/// argument's. Structurally the dual of [`type_value_is_ground`], which walks the same
/// spine for the other predicate this gate reads.
pub(super) fn term_contains_callable(kb: &KnowledgeBase, tid: TermId) -> bool {
    term_any_subterm(kb, tid, &|t, _| type_head_is_callable(kb, &TermIdView(t)))
}

/// [`type_contains_callable`] over an occurrence-carried type, walking the same
/// `Type`/`EffectExpression` spine as [`node_type_is_ground`] so the two verdicts see the
/// same children. An `Arrow` node answers `true` at its head via
/// [`type_head_is_callable`]; every other form recurses.
fn node_contains_callable(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> bool {
    if type_head_is_callable(kb, &Value::Node(Rc::clone(occ))) {
        return true;
    }
    let child = |c: &TypeChild| match c {
        TypeChild::Interned(t) => term_contains_callable(kb, *t),
        TypeChild::Node(n) => node_contains_callable(kb, n),
    };
    match &occ.kind {
        NodeKind::Type(tn) => match tn {
            // WI-20260904-02ERR: a bare variable is not an arrow. If σ later binds it to
            // one, the check runs again on the substituted type.
            TypeNode::Var(_) => false,
            // A denoted carries a VALUE, not a type spine — no callable type inside it.
            TypeNode::Aliased { stands_for, .. } | TypeNode::Defaulted { stands_for, .. } => {
                child(stands_for)
            }
            TypeNode::Denoted { .. } => false,
            TypeNode::Parameterized { base, bindings } => {
                child(base) || bindings.iter().any(|(_, c)| child(c))
            }
            TypeNode::EffectsRows { effects_expr } => child(effects_expr),
            TypeNode::Arrow { .. } => true,
            // A projection's RECEIVER is a value path, not a type, as the groundness walk reads
            // it ([`node_type_is_ground`]): a field path's (`t.a.T`) rides this carrier as a
            // `DotApply` chain, which the arm below took for a callable, so a parameter typed
            // through a field-path projection was withheld from the argument check — `agree(t.a,
            // u.b)` over `agree[A](p: Box[T = A], q: Box[T = A])` loaded, where its
            // single-reference twin `agree(p, q)` refuses `q` (MEASURED).
            TypeNode::ExprCarried { member, .. } => child(member),
            TypeNode::NamedTuple { fields } => list_records_to_pairs(kb, fields, "name", "type")
                .iter()
                .any(|(_, t)| type_contains_callable(kb, t)),
            // WI-1083: quantifying a callable does not stop it being one — `∀A. (x: A)
            // -> A` IS the type of a function value, which is the whole reason the
            // form exists. The binders are variables and carry no callable.
            //
            // WI-20260904-50B2K part (c): the CONTEXT is read with the body, the fourth of
            // the four predicates the typer widened. A constraint's type arguments can be
            // arrows (`Additive[T = (x: Int64) -> Int64]`), so an arrow answering `true` in
            // the body and `false` in a constraint is the same walk giving one type two
            // answers. /code-review found the one I missed.
            TypeNode::PolyType { context, body, .. } => {
                child(body)
                    || value_list_elements(kb, context)
                        .iter()
                        .any(|c| type_contains_callable(kb, c))
            }
        },
        // An effect row's labels are not callables; recurse anyway so the walk stays
        // total over the node's children rather than assuming a shape.
        NodeKind::EffectExpr(en) => match en {
            EffectExprNode::Merge { left, right } => child(left) || child(right),
            EffectExprNode::Present { label }
            | EffectExprNode::Absent { label }
            | EffectExprNode::Guarded { label, .. } => child(label),
            EffectExprNode::Open { tail } => child(tail),
            EffectExprNode::EmptyRow => false,
        },
        // Not a type occurrence — conservatively "might be" (withhold), matching
        // `node_type_is_ground`'s conservative arm for the same carrier.
        _ => true,
    }
}

/// WI-802: the ONE reader of a `Function[A, B, E]`'s type-parameter bindings —
/// `(A, B, E)`, borrowed from `bindings`. `None` unless `base` is the
/// [`is_function_spec`] sort AND it binds a result `B`; `A` and `E` stay
/// optional (the source may omit either — an applied `Function[A, B]` that
/// states no `E` is effect-polymorphic).
///
/// Owns the `"A"`/`"B"`/`"E"` binding names alongside the sort recognizer, so
/// [`arrow_parts_extracted`] and [`function_spec_param_type`] agree on what
/// counts as a callable by construction rather than by each restating it.
/// Binding keys match by SHORT name via [`same_label`]'s rule: this is a lookup
/// within an established same-sort gate (`base` is already known to be
/// `Function`), not an identity comparison.
///
/// Returns BORROWED parts so [`function_spec_param_type`], which wants only `A`,
/// need not CLONE `B` and `E` — WI-798 split that path apart precisely to stop
/// re-cloning bound types. It does still LOOK UP all three (a scan of a ≤3-entry
/// binding list); it is the `Rc` traffic, not the lookup, that WI-798 was about.
///
/// Three separate `find` passes rather than one loop over `bindings`, so a
/// DUPLICATE key keeps `find`'s first-wins reading. Fusing them would silently
/// flip that to last-wins — see WI-805, where duplicate-label disagreement
/// between two readers is an open defect, not a free choice.
pub(super) fn function_spec_parts<'b>(
    kb: &KnowledgeBase,
    base: Symbol,
    bindings: &'b [(Symbol, Value)],
) -> Option<(Option<&'b Value>, &'b Value, Option<&'b Value>)> {
    if !is_function_spec(kb, base) {
        return None;
    }
    let find = |name: &str| {
        bindings
            .iter()
            .find(|(p, _)| kb.local_name_of(*p) == name)
            .map(|(_, v)| v)
    };
    let result = find("B")?;
    Some((find("A"), result, find("E")))
}

/// Decompose a callable type into `(param, result, effects-row)` — carrier-
/// agnostic over [`TermView`], outputs owned [`Value`]s (WI-361/WI-342: input
/// `TermView`, output `Value`; never re-grounds, so a `Value::Node` callback
/// arrow with a denoted-bearing effect flows through losslessly).
///
/// The typer's canonical function type is `arrow(param, result, effects)`; the
/// stdlib surface type `Function[A, B, E]` is the *same* type — `arrow` is its
/// shorthand (`A` = param, `B` = result, `E` = effects). Both decompose here so
/// a `Function`-typed operation parameter is callable
/// (`operation map(l, f: Function[A, B]) = ... f(h) ...`) just like a
/// lambda-bound arrow. `param` is `None` when the source omits it; the effects
/// row is `None` when omitted (a bare `Function` without `E` → polymorphic).
/// The third element is the RAW effects child — a canonical `effects_rows(...)`
/// for an arrow, or a `Function.E` binding that may still be a legacy
/// `List[Type]` (pre-WI-331); callers normalize/flatten as they need via
/// [`canonical_effects_row`] / [`effect_row_present_values`]. Returns `None` for
/// non-callable types. (WI-289)
pub(super) fn arrow_parts<V: TermView>(
    kb: &mut KnowledgeBase,
    ty: &V,
) -> Option<(Option<Value>, Value, Option<Value>)> {
    let extracted = extract_callable_type(kb, ty);
    arrow_parts_extracted(kb, &extracted)
}

/// The callable `ty` with `row` for its effect row — the arrow's `effects`, the `Function`'s
/// `E`; its parameters, result and binders as they were. `None` for a type that is no callable,
/// and for a `Function` that writes no `E`, whose row is no part of it to replace.
pub(super) fn callable_with_row(kb: &mut KnowledgeBase, ty: &Value, row: &Value) -> Option<Value> {
    callable_with(kb, ty, None, Some(row))
}

/// … and with `result` for its result — the arrow's, the `Function`'s `B`.
pub(super) fn callable_with_result(kb: &mut KnowledgeBase, ty: &Value, result: &Value) -> Option<Value> {
    callable_with(kb, ty, Some(result), None)
}

/// The callable `ty` rebuilt on the form it was written in, `result` and `row` in place of its
/// own where given.
fn callable_with(kb: &mut KnowledgeBase, ty: &Value, result: Option<&Value>, row: Option<&Value>) -> Option<Value> {
    let (sp, owner) = site_of(ty);
    match extract_callable_type(kb, ty) {
        TypeExtractor::Arrow {
            param,
            result: own_result,
            effects,
            binders,
        } => Some(arrow_value(
            kb,
            &param,
            result.unwrap_or(&own_result),
            row.unwrap_or(&effects),
            binders,
            sp,
            owner,
        )),
        TypeExtractor::Parameterized { base, mut bindings } if is_function_spec(kb, base) => {
            for (key, value) in [("B", result), ("E", row)] {
                if let Some(value) = value {
                    let b = bindings.iter_mut().find(|(p, _)| kb.local_name_of(*p) == key)?;
                    b.1 = value.clone();
                }
            }
            let base_ref = kb.make_sort_ref(base);
            Some(parameterized_value(kb, base_ref, &bindings, sp, owner))
        }
        _ => None,
    }
}

/// WI-798: classify a value that is about to be read AS A CALLABLE. The
/// pre-intern is the reason this exists rather than a bare [`extract_type`]:
/// `extract_type` reads an `arrow`'s param/result/effects children and a
/// `Function`'s A/B/E bindings through `kb.lookup_symbol`, so a `Value::Node`
/// carrier's named-child lookups return `None` — silently degrading the callee to
/// [`TypeExtractor::Error`] — unless the child keys already exist in a minimal KB
/// (the term builders intern them; cf. WI-361 slice 4's `base`).
///
/// Any site hoisting one classification for the callable readers must go through
/// HERE, not `extract_type`: hoisting a bare extraction above the first
/// `arrow_parts` call would move it in front of the interning it depends on.
pub(super) fn extract_callable_type<V: TermView>(kb: &mut KnowledgeBase, ty: &V) -> TypeExtractor {
    for key in ["param", "result", "effects", "base"] {
        kb.intern(key);
    }
    extract_type(kb, ty)
}

/// Is `ty` a function type — an arrow or a `Function[…]` — read without interning, for a
/// diagnostic that has the KB shared. The keys [`extract_callable_type`] interns exist once
/// any function type has been written, which a loaded program's types have been.
pub(super) fn type_is_callable(kb: &KnowledgeBase, ty: &Value) -> bool {
    arrow_parts_extracted(kb, &extract_type(kb, ty)).is_some()
}

/// The decode half of [`arrow_parts`], over an ALREADY-CLASSIFIED callee
/// (WI-798). Split out so a caller that has classified the callee once — see
/// [`extract_callable_type`] — can read its parts without paying for a second
/// classification. [`arrow_parts`] keeps its carrier-taking signature for the
/// many single-shot callers that have no extraction to share.
pub(super) fn arrow_parts_extracted(
    kb: &KnowledgeBase,
    ty: &TypeExtractor,
) -> Option<(Option<Value>, Value, Option<Value>)> {
    // Borrowed, cloning only the three children handed back: a whole-extractor
    // clone here would re-copy the binding vector this split exists to stop
    // rebuilding.
    match ty {
        TypeExtractor::Arrow {
            param,
            result,
            effects,
            binders: _,
        } => Some((Some(param.clone()), result.clone(), Some(effects.clone()))),
        TypeExtractor::Parameterized { base, bindings } => {
            let (param, result, effects) = function_spec_parts(kb, *base, bindings)?;
            Some((param.cloned(), result.clone(), effects.cloned()))
        }
        _ => None,
    }
}

/// WI-801: the ONE renderer for "`actual` does not conform to `declared`" at a
/// site that has both types in hand — a [`TypeError::TypeMismatch`], except where the
/// disagreement is a provider's value at a spec, which says what it is. The three channels
/// — the op-ARGUMENT, the let-ANNOTATION and the op-RETURN — all route here.
///
/// WI-20260824-Q0093 hangs one more thing on that: `actual_node` is the occurrence
/// `actual` is the type OF, so a rejected proposal-055 type value can name what it
/// IS (`got Type (Cell[V = Int64])`, `got Type (u)`, design §8) — see
/// [`TypeError::TypeMismatch::quoted`]. Being the shared renderer is exactly why it
/// belongs here: one place to fill, and the four channels above cannot answer it
/// differently.
pub(super) fn conformance_error(
    kb: &mut KnowledgeBase,
    declared: Value,
    actual: Value,
    span: Option<Span>,
    context: TypeErrorContext,
    actual_node: Option<&Rc<NodeOccurrence>>,
) -> TypeError {
    if let Some(err) = provider_at_a_spec_type_error(kb, &declared, &actual, span, &context) {
        return err;
    }
    TypeError::TypeMismatch {
        site: TypeError::here(),
        span,
        context,
        expected: declared,
        quoted: quoted_type_value(kb, actual_node, &actual),
        actual,
    }
}

/// WI-20261005-KSSA4 — the mismatch of a PROVIDER'S VALUE against a spec that has a carrier
/// parameter, said as what it is. `None` for any other pair.
///
/// `operation viaDefaulted(w: Tagger)` given a `B`, where `B provides Tagger[C = B]`: the
/// provision lets `Tagger`'s operations be used on a `B`; it does not make a `B` a `Tagger`
/// ([`spec_has_carrier_param`]). The bare `expected Tagger, got B` is true and says none of
/// that — nor the two spellings that do ask for "any value whose sort provides `Tagger`".
/// Asked on the refusal path only, where the relation has already answered.
fn provider_at_a_spec_type_error(
    kb: &KnowledgeBase,
    declared: &Value,
    actual: &Value,
    span: Option<Span>,
    context: &TypeErrorContext,
) -> Option<TypeError> {
    let spec = sort_functor_of_view(kb, declared)?;
    let param = spec_over_parameter(kb, spec)?;
    let mut provider = sort_functor_of_view(kb, actual)?;
    // An entity's provision is its parent sort's, as the relation reads it.
    while !carrier_is_an_instance(kb, provider, spec) {
        provider = kb.strict_parent_sort(provider)?;
    }
    let (expected, got) = render_mismatch_pair(kb, declared, actual);
    Some(TypeError::Other {
        span,
        context: context.clone(),
        expected,
        actual: format!(
            "{got} — {}",
            provider_is_not_the_spec_note(kb, spec, param, provider, context),
        ),
        site: TypeError::here(),
    })
}

/// What a refusal of a provider's value at a spec over a parameter says, and the spelling
/// that asks for a provider AT THE POSITION REFUSED. A parameter can be typed by the member
/// or by a bound; a field has no member sugar, and is typed by a parameter of its sort the
/// sort requires the spec of; a result or a binding holds one value, of its own sort — a
/// bound there would be the caller's to choose, and the value would not meet it.
pub(super) fn provider_is_not_the_spec_note(
    kb: &KnowledgeBase,
    spec: Symbol,
    param: Symbol,
    provider: Symbol,
    context: &TypeErrorContext,
) -> String {
    let spec_name = kb.qualified_name_of(spec);
    let param_name = short_name_of(kb.local_name_of(param));
    let provider = kb.qualified_name_of(provider);
    let repair = match context {
        TypeErrorContext::OperationArgument { .. } => format!(
            "Type this position `{spec_name}.{param_name}`, or by a type parameter `P` \
             under `requires {spec_name}[{param_name} = P]`"
        ),
        TypeErrorContext::EntityField { .. } => format!(
            "Type the field by a parameter `P` of its sort, and write `requires \
             {spec_name}[{param_name} = P]` on the sort"
        ),
        _ => format!("Type it `{provider}`, the sort the value is of"),
    };
    format!(
        "`{spec_name}` is a spec over its parameter `{param_name}`: `{provider}` provides \
         it, so its operations may be used on a value of `{provider}`, and that does not \
         make the value a `{spec_name}`. {repair}"
    )
}

/// WI-20261005-KSSA4 — the refusal of a value TYPED AT A SPEC where an operation receives on
/// its sort's parameter: `Tagger.tagIn(w)` over `w: Tagger`, against `tagIn(x: C)`. `None`
/// for every other receiver.
///
/// A value typed at `Tagger` is not a value of a sort that provides `Tagger`; `C` is. Read
/// as one, the call fixed `C` at the type `Tagger` itself, a dictionary for `Tagger`'s own
/// `requires` could be built at no carrier, and the body read a frame nothing had filled
/// (MEASURED: `viaDefaulted(w: Tagger) = Tagger.tagIn(w)` loaded and died "`__req_tag` not
/// bound in caller frame"). The receiver's type may be the callee's own spec or any other
/// that has a carrier parameter: neither is a carrier.
pub(super) fn spec_typed_value_at_carrier_error(
    kb: &KnowledgeBase,
    callee_sort: Symbol,
    carrier_param: Symbol,
    recv_ty: &Value,
    span: Option<Span>,
    context: TypeErrorContext,
) -> Option<TypeError> {
    let typed_at = sort_functor_of_view(kb, recv_ty)?;
    let typed_at_param = spec_over_parameter(kb, typed_at)?;
    let typed_at_name = kb.qualified_name_of(typed_at);
    let typed_at_param = short_name_of(kb.local_name_of(typed_at_param)).to_owned();
    Some(TypeError::Other {
        span,
        context,
        expected: format!(
            "{}.{}",
            kb.qualified_name_of(callee_sort),
            short_name_of(kb.local_name_of(carrier_param)),
        ),
        actual: format!(
            "{got} — `{typed_at_name}` is a spec over its parameter `{typed_at_param}`: a \
             value typed at it is not a value of a sort that provides it. Type the value \
             `{typed_at_name}.{typed_at_param}`, or by a type parameter `P` under `requires \
             {typed_at_name}[{typed_at_param} = P]`",
            got = type_display_name_value(kb, recv_ty),
        ),
        site: TypeError::here(),
    })
}

/// WI-20260824-Q0093 (`docs/design/055-implementation.md` §8) — what a mismatch quotes
/// after `got Type`, for [`TypeError::TypeMismatch::quoted`]: the VALUE when the rejected
/// expression is a type value — `got Type (Cell[V = Int64])`, and `(Int64)` for
/// `Box[V = Int64].V` — and otherwise, when its type is `Type`, the expression AS WRITTEN —
/// `got Type (u)` after `let u = Cell[Int64]`, `got Type (idT(Cell))`. `None` for an
/// expression of another type, and for a check with no occurrence to ask.
///
/// A `Type` a call returned, or a parameter, or a name a `let` bound, has no value known at
/// this position; what the author wrote is always there.
///
/// The value is printed through [`TermPrinter::print_occurrence`], which writes a type
/// value in its source spelling (brackets and `=`). The expression is the SOURCE TEXT at
/// the occurrence's span, its whitespace runs made one space so a multi-line `match`
/// reads on one line: the printer writes what a body was lowered to — `xs.head()` as
/// `head(xs)`, `tyOf()` as `tyOf`. `None` where the span holds no text — a source
/// registered with none, a span a pass minted empty.
pub(super) fn quoted_type_value(
    kb: &KnowledgeBase,
    node: Option<&Rc<NodeOccurrence>>,
    actual: &Value,
) -> Option<String> {
    let mut node = node?;
    // THROUGH THE WRAPPERS WHOSE TYPE IS ALREADY THEIR CHILD'S, and only those. A `let`
    // reports its CONTINUATION's type (`TypeBuildFrame::LetFinal`) and an in-body `proof`
    // its continuation's too ("the proof is transparent to types",
    // `TypeBuildFrame::ProofStmt`) — so the rejected `Type` came from the child, and the
    // child is what is quoted, not the block around it.
    while let Some(Expr::Let { body, .. } | Expr::Proof { body, .. }) = node.as_expr() {
        node = body;
    }
    if matches!(node.as_expr(), Some(Expr::TypeValue { .. })) {
        return Some(crate::persistence::print::TermPrinter::new(kb).print_occurrence(node));
    }
    let type_sym = kb.try_resolve_symbol("anthill.prelude.Type")?;
    if sort_functor_of_view(kb, actual) != Some(type_sym) {
        return None;
    }
    let site = node.span;
    let (_, text) = kb.sources.provenance(site.source)?;
    let written = text.get(site.span.start as usize..site.span.end as usize)?;
    let quoted = written.split_whitespace().collect::<Vec<_>>().join(" ");
    (!quoted.is_empty()).then_some(quoted)
}

/// WI-20260824-Q0093 (`docs/design/055-implementation.md` §3, the `conditionals` and
/// `matching` rows) — THE DESTINATION CHECK OF A BOOLEAN POSITION: an `if` condition and
/// a `match` arm guard.
///
/// THE FINDING THIS ARM IS. Q0093 asks each `ValueExpression` family for a negative
/// destination "where the family admits one", and design §3 says of the conditional row
/// that a type value is admitted there because "ordinary typing rejects `Type` as a
/// Boolean condition". Measured, ordinary typing rejected NOTHING there: the condition's
/// type was computed and dropped on the floor, so `if Cell then … else …` loaded — and so
/// did `if "x" then …` and `if 1 then …`, which is the control that says this is not a
/// proposal-055 regression but a slot that never had a check. The `match` guard is the
/// same hole written twice: its own site said "No `Bool` hint (matching how `if` treats
/// its condition)", and a hint is not a check. Both slots are checked here, through ONE
/// predicate, so the two cannot drift apart again.
///
/// BORROWED, NOT INVENTED. The judgement is [`validate_arg_against_param`] — the same
/// predicate an ARGUMENT gets against a declared parameter — so the groundness gate and
/// the boundary conversions are the ones already in force elsewhere rather than a second
/// opinion about what conforms. A `Bool` destination can never take the WI-408
/// some-coercion (it is not an `Option[T]`), so that arm is reported as the mismatch it
/// is rather than silently accepted.
///
/// WHAT THAT PREDICATE REFUSES HERE THAT NOTHING REFUSED BEFORE — three shapes, each
/// measured with the check backed out, because "it used to load" is only half a fact and
/// the other half is what it then DID. Found by `/code-review`, whose reading of the two
/// tolerances named above was right and is corrected here:
///
///  * a RELATION-VALUED condition or guard — `if warm(c) then …` over `rule warm(?c) :- …`
///    — is refused at load. With the check backed out it loads and then fails at EVAL:
///    `EvalError::TypeMismatch { expected: "Bool", got: "Relation" }` for the `if`, and
///    `Internal("deliver: parent frame had no awaiting state")` for the guard (measured
///    before WI-20260913-2858G changed where a nested run stops, so the guard's run-time
///    failure may read differently now; the load-time refusal is unaffected). So this is
///    the runtime's own rule, moved one phase earlier and given a span, not a spelling
///    taken away — which is what CLAUDE.md's "know about errors early" asks for.
///  * a reflect-`Term` condition (`operation f(t: Term) = if t then …`). The `Term`
///    tolerance is ONE-DIRECTIONAL — it fires when the DECLARED side is `Term`, and here
///    the declared side is `Bool` — so it does not reach this position. Backed out, it
///    fails at eval like the relation above.
///  * a RIGID type parameter (`operation f[T](c: T) = if c then …`, reported `got ?T`).
///    A `Var::Rigid` is DETERMINED since WI-1059, so the groundness gate does not defer
///    it, and the refusal is the one §8.1 already states for a body that pins a parameter
///    its signature quantified: measured, the same value in an ARGUMENT slot
///    (`sink(c)` with `sink(b: Bool)`) is refused with the identical `expected Bool, got
///    ?T`. That pairing is asserted rather than asserted-about, in
///    `wi_q0093_type_value_occurrence_matrix_test`. It DOES cost a program that ran:
///    `poly(true)` evaluated before, and the repair is to write the parameter `c: Bool`.
///
/// σ is FRESH and discarded: this asks a question ABOUT the condition, and a binding made
/// while answering it belongs to no call.
pub(super) fn boolean_position_error(
    kb: &mut KnowledgeBase,
    ty: &Value,
    node: Option<&Rc<NodeOccurrence>>,
    span: Option<Span>,
    construct: &'static str,
    slot: &'static str,
) -> Option<TypeError> {
    let context = TypeErrorContext::BooleanPosition { construct, slot };
    // `try_`, not the interning form: `make_sort_ref_by_name` falls through to a bare
    // `intern` for a name nothing declares, which in a KB without the prelude would mint a
    // PHANTOM `Bool` and compare every condition against an unresolved sort — reporting
    // `expected Bool, got Bool`. The `Expr::Const` arm asks the same question the same way
    // and raises rather than inventing a sort; this says so out loud too, because a
    // destination check with no destination cannot be run and must not be skipped in
    // silence (found by `/code-review`).
    let Some(bool_tid) = kb.try_make_sort_ref_by_name("anthill.prelude.Bool") else {
        return Some(TypeError::Other {
            site: TypeError::here(),
            span,
            context,
            expected: "the prelude's `Bool` sort, so this position's destination can be \
                       checked"
                .to_string(),
            actual: "a knowledge base that declares no `anthill.prelude.Bool`".to_string(),
        });
    };
    let bool_ty = Value::term(bool_tid);
    let mut subst = Substitution::new();
    match validate_arg_against_param(kb, &mut subst, ty, &bool_ty, span, context.clone(), node) {
        ArgValidation::Ok => None,
        ArgValidation::Fail(e) => Some(e),
        ArgValidation::WrapSome { .. } => Some(TypeError::TypeMismatch {
            site: TypeError::here(),
            span,
            context,
            expected: bool_ty,
            quoted: quoted_type_value(kb, node, ty),
            actual: ty.clone(),
        }),
    }
}

/// The row of the callable `ty` whose effects child [`arrow_parts`] read as `row`, as the row
/// relations take it: an ARROW's `effects` child is a row already and is handed on as it is; a
/// `Function`'s `E` binding is whatever was written there, read as the row it denotes
/// ([`canonical_effects_row`]). Canonicalizing an arrow's child too would build a row out of a
/// shape no arrow is minted with — a bare variable on a hand-built arrow in a KB with no
/// prelude, where building one is a panic (`types_compatible_bootstrap_safe_when_prelude_not_-
/// registered`).
pub(super) fn callable_row<V: TermView>(kb: &mut KnowledgeBase, ty: &V, row: Value) -> Value {
    if matches!(type_head(kb, ty), TypeHead::Arrow) {
        row
    } else {
        canonical_effects_row(kb, &row)
    }
}

/// Normalize a raw effects-row [`Value`] (the third element of [`arrow_parts`])
/// into a canonical `effects_rows(...)` carrier the row machinery
/// ([`subtype_effect_rows`] / [`unify_effect_rows`]) consumes. An arrow's
/// `effects` child and a `Value::Node` row are already canonical and pass
/// through untouched; a `Function.E` BINDING (a `TermId` carrier) is whatever was written
/// there, and each spelling is the row it denotes:
///
///  * a legacy `List[Type]` — its elements, flattened;
///  * a bare `EffectExpression` (`merge(…)`, `open(…)`) — itself, wrapped;
///  * ANYTHING ELSE IS ONE ELEMENT: a bare row variable or row-parameter reference is the OPEN
///    row `{E}`, a bare label the row holding it — as the braced spelling builds them
///    ([`KnowledgeBase::build_canonical_effects_rows`], whose `row_tail_var_of` reads a
///    sort-level `Ref(S.E)` too).
///
/// The last case used to be flattened as a list too, and a non-list flattens to NOTHING: the
/// prelude's own `Function[A, B, E]` slot read as the closed EMPTY row whatever `E` was bound
/// to, so `Function.apply(inc, 41)` over a raising `inc` was refused "(a closed row)", and
/// since the validator judges fields and call results (WI-20260929-0RP29) so was every
/// effectful one of those (MEASURED: programs that ran). On the ACTUAL side the same reading
/// made a `Function[…, E = Error[Foo]]`-typed callback pure.
pub(super) fn canonical_effects_row(kb: &mut KnowledgeBase, row: &impl TermView) -> Value {
    let effects_rows_sym = kb.try_resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows");
    match row.as_bind_value() {
        BindValue::Term(t) => {
            let is_canonical = matches!(
                (kb.get_term(t), effects_rows_sym),
                (Term::Fn { functor, .. }, Some(er)) if *functor == er
            );
            if is_canonical {
                Value::term(t)
            } else if value_is_bare_effect_expr(kb, &Value::term(t)) {
                wrap_bare_effect_expr_as_row(kb, &Value::term(t))
            } else if term_is_list(kb, t) {
                let flat = list_to_vec(kb, t);
                Value::term(kb.build_canonical_effects_rows(&flat))
            } else {
                Value::term(kb.build_canonical_effects_rows(&[t]))
            }
        }
        // The same readings on another carrier, asked of the type: a row as it stands, a
        // bare row expression wrapped, a LABEL the row holding it. Taken as "always the
        // canonical occurrence form", a label that rode an occurrence was handed on as
        // the row, and read as a row it holds nothing: applying `f: Function[A = Int64, B
        // = Int64, E = Error[String]]` charged nothing, and the slot admitted no callback
        // that raises (MEASURED, over `E = Error[Oops]` with `sort Oops = String`).
        BindValue::Value(v) => {
            if matches!(type_head(kb, &v), TypeHead::EffectsRows) {
                v
            } else if value_is_bare_effect_expr(kb, &v) {
                wrap_bare_effect_expr_as_row(kb, &v)
            } else {
                row_holding_label(kb, &v).unwrap_or(v)
            }
        }
        // An effects row is never carried as a deferred query path; the empty
        // row is a safe (unreachable) fallback.
        BindValue::Path(_) => Value::term(kb.build_canonical_effects_rows(&[])),
    }
}

/// Is `t` a list spine — `nil` or a `cons` cell — as [`list_to_vec`] reads one?
fn term_is_list(kb: &KnowledgeBase, t: TermId) -> bool {
    match kb.get_term(t) {
        Term::Fn { functor, .. } => matches!(kb.local_name_of(*functor), "nil" | "cons"),
        Term::Ref(sym) | Term::Ident(sym) => kb.local_name_of(*sym) == "nil",
        _ => false,
    }
}

/// Flatten a raw effects-row [`Value`] into its present effect labels (plus an
/// open-row tail var, matching the ground `effects_rows_to_flat_list` and the
/// WI-341 `Value` path) — the carrier-agnostic effects a call site incurs.
/// Carrier-agnostic; a `Value::Node` row's occurrence labels are never
/// re-grounded. A legacy `List[Type]` binding's elements ARE the labels.
pub(super) fn effect_row_present_values(kb: &mut KnowledgeBase, row: &impl TermView) -> Vec<Value> {
    match row.as_bind_value() {
        // Ground carrier: the established flat-list walk (exact pre-WI-361
        // behavior; its non-wrapper fallback also handles a legacy `List[Type]`
        // Function.E binding pre-WI-331). A bare row expression is no list, and is read
        // through the view as on any other carrier.
        BindValue::Term(t) if !value_is_bare_effect_expr(kb, &TermIdView(t)) => {
            effects_rows_to_flat_list(kb, t).into_iter().map(Value::term).collect()
        }
        _ => row_present_values_by_view(kb, row),
    }
}

/// The effects APPLYING a callable with this effects child incurs: [`effect_row_present_values`]
/// of the binding read as the row it DENOTES ([`canonical_effects_row`]). A `Function.E` binding
/// is whatever was written there — a bare row parameter is the open row `{E}`, a bare label the
/// row holding it — and the argument check admits a callback into the slot by exactly that
/// reading; flattened as it stands, both read as NO effect (a non-list flattens to nothing), so
/// applying `f: Function[A, B, E = E]` charged nothing for the `boom` the slot had admitted, and a
/// raising callback's effect left a pure `main` (MEASURED: review 9).
///
/// EXCEPT AN UNWRITTEN `E`, which charges nothing, as on every build: read off a value (`f.E`,
/// what [`rigidify_unwritten_sort_params`] fills a parameter's own unwritten slot with in the
/// body; a written `E = s.E` likewise), a flexible variable, or a rigid that is no DECLARED
/// parameter's (none of the body's `param_rigids` — the slot of a `Function[A, B]` nested in
/// another type, minted per occurrence: `some(f)` out of an `Option[T = Function[A = Int64, B =
/// Int64]]`). A row parameter the author wrote is a declaration's, rigid in the body, and is
/// charged. `Function[A, B]` is polymorphic in its row (kernel-language.md §4.4, as §8.1 reads an
/// unwritten parameter; user decision 2026-10-03), so applying one should charge it — but that
/// refuses every operation applying such a value ("undeclared effect: f.E" / "?E", MEASURED: the
/// suite's own `wi_2tmb5` / `wi_5nszy` programs and 131 rows in all), since no operation can
/// declare `effects {f.E}` for a callable parameter (MEASURED: every build). Proposal 069
/// settles it the other way (WI-20261003-QV5W5, superseding WI-20261003-H7KFV): `Function`
/// declares `E` with `default {}`, so an omitted `E` is the empty row and this exception goes —
/// an effectful callback is refused at the CALL, and `Function[A, B, ?]` is the open spelling.
pub(super) fn callable_effect_present_values(
    kb: &mut KnowledgeBase,
    row: &Value,
    param_rigids: &[(VarId, TermId)],
) -> Vec<Value> {
    // Asked of the binding through the view, so a slot reads the same on every carrier.
    let unwritten = match row.head(kb) {
        ViewHead::Var(Var::Global(_)) => true,
        ViewHead::Var(rigid @ Var::Rigid(_)) => !param_rigids
            .iter()
            .any(|(_, r)| matches!(kb.get_term(*r), Term::Var(v) if *v == rigid)),
        _ => matches!(extract_type(kb, row), TypeExtractor::ExprCarried { .. }),
    };
    if unwritten {
        return Vec::new();
    }
    let canonical = canonical_effects_row(kb, row);
    effect_row_present_values(kb, &canonical)
}

/// A row's present labels plus its open-row tails, read through the view on any carrier — an
/// `effects_rows` wrapper or the bare expression a bound row variable walks to; an occurrence's
/// labels are never re-grounded (WI-341).
///
/// The labels as written, an uninhabitable row's (`{e, -e}`) too: that row is refused where it
/// is stated, and its labels are not dropped from what applying it incurs. A row that does not
/// decompose — an unknown functor in the algebra — is a construction bug, loud in a debug build
/// as the term walk's is ([`effects_rows_to_flat_list`]).
fn row_present_values_by_view(kb: &mut KnowledgeBase, row: &impl TermView) -> Vec<Value> {
    let subst = Substitution::new();
    match decompose_effect_row_raw(kb, &subst, row) {
        Some((mut present, tails, _absent)) => {
            present.extend(tails.into_iter().map(Value::term));
            present
        }
        None => {
            debug_assert!(false, "an effect row that does not decompose");
            Vec::new()
        }
    }
}

/// WI-307 v1a: flatten an `effects_rows(EffectExpression)` Type into the
/// pre-v1a `Vec<TermId>` shape: concrete labels followed by an optional
/// row-tail `Var`. Inverse of `KnowledgeBase::build_canonical_effects_rows`.
///
/// **Structural walk** — visits the EffectExpression algebra via a stack
/// (no shape assumption about `merge` associativity). Each node dispatches
/// by short functor name:
///   - `empty_row`         → terminate this branch
///   - `present(label)`    → push `label` to `out`
///   - `absent(label)`     → skip (v1a presence-only; the flat-list shape
///                          has no slot for absences, lacks-constraints
///                          land with v1b)
///   - `open(tail)`        → push `tail` (the row-tail Var) to `out`
///   - `merge(left, right)`→ stack both subtrees
///   - bare `Term::Var`    → push as tail (`effects_rows(?expr)` whose inner
///                          is an unbound Var; without this the row decodes
///                          to an empty flat list and effects silently vanish.)
///
/// **Non-wrapper tolerance** — when `ty` is not an `effects_rows` term, the
/// function falls back to `list_to_vec(kb, ty)` for back-compat with the
/// legacy List[Type] shape that still lives in OperationInfo.effects and
/// parameterized E bindings until those slots migrate. A `debug_assert`
/// surfaces the case in dev builds so any unexpected non-wrapper reaching
/// this site is easy to spot during migration.
pub(crate) fn effects_rows_to_flat_list(kb: &KnowledgeBase, ty: TermId) -> Vec<TermId> {
    // Unwrap effects_rows; non-wrapper inputs flow through legacy list_to_vec.
    // The fallback path is intentional during the migration window, but
    // surface unexpected shapes in dev builds so silent data-loss doesn't
    // accumulate.
    //
    // Dispatch via Symbol identity (code-review #5) rather than short-name
    // compare so a user-defined `effects_rows` entity in another namespace
    // isn't misrouted here.
    // WI-493: unwrap the `effects_rows(…)` wrapper via the single shared tolerance
    // (matched by qualified symbol, so a same-short-named functor elsewhere is not
    // misrouted here). A ground wrapper's inner is always a `Value::Term`.
    let expr = match effects_rows_inner(kb, &TermIdView(ty)) {
        Some(Value::Term { id: e, .. }) => e,
        // Not a well-formed `effects_rows` wrapper — a legacy unwrapped `List`
        // (OperationInfo.effects, Function[E] with a legacy List binding) or a
        // transient pre-`make_arrow_type` term flows through the flat-list walk,
        // as before. (A malformed wrapper, never produced by `make_effects_rows_*`,
        // also lands here rather than tripping a debug-assert.)
        _ => return list_to_vec(kb, ty),
    };

    // Structural walk over the EffectExpression algebra (any associativity).
    let mut out: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = vec![expr];
    while let Some(node) = stack.pop() {
        match kb.get_term(node) {
            // Bare Var inside effects_rows is an open-row tail
            // (`effects_rows(?expr)`). Treat
            // as if wrapped in `open(tail = ?expr)` — pushing it to `out`
            // keeps the row-tail visible to downstream readers.
            Term::Var(_) => out.push(node),
            Term::Fn {
                functor,
                named_args,
                ..
            } => {
                let name = kb.local_name_of(*functor);
                match name {
                    "empty_row" => {}
                    "present" => {
                        if let Some(label) = get_named_arg(kb, named_args, "label") {
                            out.push(label);
                        }
                    }
                    // WI-478: a guarded atom is CONSERVATIVELY PRESENT (no discharge
                    // in phase 1) — surface its label exactly like `present`, dropping
                    // the `guard`. So a guarded effect propagates / is satisfiable like
                    // the unconditional one until discharge (WI-067) lands.
                    "guarded" => {
                        if let Some(label) = get_named_arg(kb, named_args, "label") {
                            out.push(label);
                        }
                    }
                    "absent" => {
                        // v1a presence-only — lacks-constraint slot lands w/ v1b.
                    }
                    "open" => {
                        if let Some(tail) = get_named_arg(kb, named_args, "tail") {
                            out.push(tail);
                        }
                    }
                    "merge" => {
                        // Push right first so left is visited first (LIFO).
                        // The walk is shape-agnostic: nested merges in
                        // either subtree are descended structurally rather
                        // than peeked at the head — non-canonical
                        // associativity no longer drops payload.
                        if let Some(r) = get_named_arg(kb, named_args, "right") {
                            stack.push(r);
                        }
                        if let Some(l) = get_named_arg(kb, named_args, "left") {
                            stack.push(l);
                        }
                    }
                    _ => {
                        // Unknown functor inside an EffectExpression payload
                        // — likely an upstream construction bug. Surface in
                        // dev builds; tolerate in release (caller decides).
                        debug_assert!(
                            false,
                            "unexpected functor in EffectExpression walk: {}",
                            name
                        );
                    }
                }
            }
            // WI-511: a 0-ary effect constructor (`empty_row`) is stored as the
            // canonical `Ref` form after the alloc flip; the closed empty row
            // carries no atoms — same as the `Fn{empty_row}` arm above.
            Term::Ref(s) if kb.local_name_of(*s) == "empty_row" => {}
            // Term::Ref / Const / Ident / Bottom inside an EffectExpression
            // are ill-typed — surface in dev, ignore in release.
            _ => {
                debug_assert!(false, "unexpected term shape in EffectExpression walk");
            }
        }
    }
    out
}

/// Result + effects of a callable type (`arrow` or `Function[A, B, E]`), used
/// when applying a function value — `f(x)` yields the result type. Carrier-
/// agnostic over [`TermView`] (WI-361/WI-342): a ground `TermId` arrow and a
/// `Value::Node` callback arrow (a denoted-bearing effect like `Modify[a]`)
/// take one path — the result is the `Value` carrier and the effects are the
/// row's present labels (plus an open-row tail var), the occurrence never
/// re-grounded. Folds the former TermId / `_value` twins into one.
///
/// WI-798: takes the callee ALREADY CLASSIFIED (via [`extract_callable_type`],
/// whose pre-intern this read depends on) so that the application path — which
/// goes on to ask the SAME value for its parameter slots and binder names — pays
/// for one classification instead of three. The lambda-hint caller has nothing to
/// share and simply classifies at its own call site, as it did before.
///
/// `param_rigids` (the body's, [`TypingEnv::param_rigids`]) says whether a rigid row binding is a
/// DECLARED parameter's — see [`callable_effect_present_values`].
pub(super) fn extract_function_type_parts(
    kb: &mut KnowledgeBase,
    fn_type: &TypeExtractor,
    param_rigids: &[(VarId, TermId)],
) -> Option<(Value, Vec<Value>)> {
    let (_, result, eff) = arrow_parts_extracted(kb, fn_type)?;
    let effects = eff
        .map(|row| callable_effect_present_values(kb, &row, param_rigids))
        .unwrap_or_default();
    Some((result, effects))
}

/// What an application of a function value meets: the function's `A`, read by the
/// APPLICATION MATCH (kernel-language §4.4) — a TOTAL answer, so that "nothing to check" is a
/// named outcome rather than an anonymous fallthrough. Both spellings, `arrow` and
/// `Function[A, B, E]`, are read alike: every arrow is a `Function`, and no parameter count
/// stands beside `A`.
pub(super) enum ApplicationTarget {
    /// `A` is a tuple, its components in `A`'s order: a positional argument meets the component
    /// at its position, a named one the component with its label, each component once. A
    /// one-component or empty tuple is no special case.
    Tuple(Vec<(Symbol, Value)>),
    /// `A` is one value, not a tuple: the one argument is `A` (`(v: Int64) -> R`'s binder name
    /// is no part of its type, so `f(v: 1)` is refused).
    Whole(Value),
    /// `A` is a variable not yet bound — an un-annotated lambda's `?param`: the arguments say
    /// what it is.
    Var(Value),
    /// The type binds no `A` at all (a `Function` without one). The one genuine absence,
    /// silent by design.
    NoVerdict,
}

/// The [`ApplicationTarget`] of a callee ALREADY CLASSIFIED by [`extract_callable_type`]
/// (WI-798: the application path reads one extraction for its result, its effects and this).
/// `A` is read through σ, so a variable an earlier argument pinned is the type it was pinned
/// to.
pub(super) fn application_target(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    fn_type: &TypeExtractor,
) -> ApplicationTarget {
    let Some((Some(a), _, _)) = arrow_parts_extracted(kb, fn_type) else {
        return ApplicationTarget::NoVerdict;
    };
    let a = walk_type_deep_value(kb, subst, &a);
    match extract_type(kb, &a) {
        TypeExtractor::NamedTuple(fields) => ApplicationTarget::Tuple(fields),
        TypeExtractor::FlexVar { .. } | TypeExtractor::TypeVar(_) => ApplicationTarget::Var(a),
        TypeExtractor::Error => ApplicationTarget::NoVerdict,
        _ => ApplicationTarget::Whole(a),
    }
}

/// The components a call through a value of type `callee` names its arguments by
/// (kernel-language §4.4, "A lambda's binder names name its arguments"): `A`'s own labels, or —
/// where `A` is positional, a lambda's own tuple — the binder names its arrow records at those
/// positions. The names are no part of the type: only the application match of a call of this
/// value reads them, and the tuple the call hands over stays positional. A position whose binder
/// is no single name keeps its positional label. An arrow recording one binder for a tuple of
/// several components (a lambda of one binder taking the whole tuple) names no component.
pub(super) fn components_named_by_binders(
    kb: &mut KnowledgeBase,
    callee: &Value,
    fields: Vec<(Symbol, Value)>,
) -> Vec<(Symbol, Value)> {
    if !is_positional_tuple_names(kb, &fields) {
        return fields;
    }
    match arrow_own_binders(kb, callee) {
        Some(binders) if binders.len() == fields.len() => fields
            .into_iter()
            .zip(binders)
            .map(|((label, ty), binder)| match binder {
                Some(binder) => {
                    let name = short_name_of(kb.local_name_of(binder)).to_owned();
                    (kb.intern(&name), ty)
                }
                None => (label, ty),
            })
            .collect(),
        _ => fields,
    }
}

/// The components of a function type's `A` when `A` is a tuple — the parameter list a call
/// through a value of this type names its arguments by. `None` for a function whose `A` is no
/// tuple, and for a type that is no function.
pub(super) fn function_param_tuple(kb: &mut KnowledgeBase, ty: &Value) -> Option<Vec<(Symbol, Value)>> {
    let (Some(a), _, _) = arrow_parts(kb, ty)? else {
        return None;
    };
    named_tuple_field_pairs(kb, &a)
}

/// How many parameters a callable WRITTEN at a slot has — the one fact about it its type does
/// not state (kernel-language §4.4: `((a: A, b: B)) -> R` and `(a: A, b: B) -> R` are one type,
/// while `get_a(t: (a: A, b: B))` and `two(a: A, b: B)` are two callables).
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum CallableParams {
    /// One parameter, or one binder: the callable takes the whole tuple as its value.
    One,
    /// Any other count, its own tuple the list of its parameters (a lambda's carries no labels).
    Many,
}

impl CallableParams {
    /// An operation taken as a value: its signature's parameter list — the one eval's
    /// `spread_eta_args` reads the count off, so the two cannot disagree on it.
    pub(super) fn of_operation(kb: &KnowledgeBase, op: Symbol) -> Self {
        let info = crate::kb::op_info::lookup_operation_info(kb, op).unwrap_or_else(|| {
            panic!(
                "`{}` taken as a function value has no signature record",
                kb.qualified_name_of(op)
            )
        });
        if info.params.len() == 1 {
            CallableParams::One
        } else {
            CallableParams::Many
        }
    }
}

/// A callable WRITTEN at a function-typed slot — an operation or a lambda — as the slot reads
/// it: rule 6 of proposal 002 (kernel-language §4.4, "A callable where a function type is
/// expected"). TOTAL, so "the slot does not say yet" is a named outcome.
pub(super) enum CallableAtSlot {
    /// The callable re-expressed at the slot's `A`, as the type it has from here on: `A`'s
    /// components in `A`'s order and with `A`'s labels, each the type of the parameter that
    /// takes it, with the callable's own result and row — so a function value keeps the mapping
    /// it was minted at, and every later relation reads it as the slot's. `slot_labels` is what
    /// an operation value carries to take the positional tuple an application hands it
    /// (`Value::OpRef::spread_labels`): for several parameters `A`'s labels in `A`'s order, which
    /// map each parameter to its component (`slot_components_of_params`); for one parameter the
    /// labels it relabels the tuple to.
    AtSlot {
        ty: Value,
        slot_labels: Option<Rc<[Symbol]>>,
    },
    /// The slot's `A` is not known yet (a variable a later argument may pin): the callable
    /// keeps its own type, and the match waits for `A`.
    Waits,
    /// `A` does not reach the callable's tuple — two components meeting three parameters, a
    /// tuple its one parameter does not accept, several parameters at a non-tuple `A`. The
    /// callable keeps its own type, which the conformance relation then refuses with both types
    /// in the message.
    Refused,
}

/// [`CallableAtSlot`] for the callable whose own type is `own_ty` — an arrow over its own tuple,
/// an operation's parameters (`two(a: Int64, b: Int64)` has `(a: Int64, b: Int64)`) or a
/// lambda's pattern (`lambda (a: Int64, b: Int64)` has `(Int64, Int64)`, no labels) — at the
/// slot `slot_ty`, read through σ.
///
/// * ONE parameter: the slot hands it the whole tuple, which is data to it, so `A` meets the
///   parameter's type by the TUPLE MATCH — a component the parameter does not name is dropped
///   (`age_of(p: (age: Int64))` stands where `A = (age: Int64, name: String)`).
/// * SEVERAL: the components meet the parameters by label where the two tuples carry the same
///   labels, by position otherwise ([`crate::kb::call_form::slot_components_of_params`], the
///   owner eval reads too), and the counts must agree — the application match. The arrow's own
///   binders are reordered with the components, so a row label over parameter `x` stays over
///   the component `x` takes (the callback row check aligns by position).
pub(super) fn callable_at_slot(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    own_ty: &Value,
    params: CallableParams,
    slot_ty: &Value,
) -> CallableAtSlot {
    let Some((Some(own_a), own_result, Some(own_row))) = arrow_parts(kb, own_ty) else {
        return CallableAtSlot::Refused;
    };
    let Some((slot_a, _, _)) = arrow_parts(kb, slot_ty) else {
        return CallableAtSlot::Refused;
    };
    let Some(slot_a) = slot_a else {
        return CallableAtSlot::Waits;
    };
    let slot_a = walk_type_deep_value(kb, subst, &slot_a);
    let own_binders = match extract_callable_type(kb, own_ty) {
        TypeExtractor::Arrow { binders, .. } => binders,
        _ => None,
    };
    let (sp, owner) = site_of(own_ty);
    let slot_fields = match extract_type(kb, &slot_a) {
        TypeExtractor::FlexVar { .. } | TypeExtractor::TypeVar(_) | TypeExtractor::Error => {
            return CallableAtSlot::Waits;
        }
        TypeExtractor::NamedTuple(fields) => Some(fields),
        _ => None,
    };
    match params {
        CallableParams::One => {
            // Bind what the parameter's type leaves open (an instantiated `T`) before the
            // judgement; the boolean is the relation's, not this unify's — EQUALITY refuses the
            // width the tuple match admits. On a TRIAL σ, kept only where the callable meets the
            // slot: a refused one must not leave the call's variables pinned to its types.
            let mut trial = subst.clone();
            let _ = unify_types(kb, &mut trial, &own_a, &slot_a);
            // `A`'s components meet the parameter's tuple as an application's arguments do: a
            // POSITIONAL `A` by position (`take2(get_a)`, `(Int64, Int64)` reaching `(a: Int64,
            // b: Int64)` — the value is relabelled where it is taken, `Value::at_tuple_labels`),
            // a labelled one by label, a component the parameter's type does not name dropped as
            // the tuple match drops it.
            let meets = match (&slot_fields, named_tuple_field_pairs(kb, &own_a)) {
                (Some(slot), Some(own))
                    if is_positional_tuple_names(kb, slot) && !is_positional_tuple_names(kb, &own) =>
                {
                    slot.len() == own.len()
                        && slot
                            .iter()
                            .zip(&own)
                            .all(|((_, s), (_, o))| types_compatible(kb, &mut trial, s, o))
                }
                _ => types_compatible(kb, &mut trial, &slot_a, &own_a),
            };
            if !meets {
                return CallableAtSlot::Refused;
            }
            *subst = trial;
            let ty = arrow_value(kb, &slot_a, &own_result, &own_row, own_binders, sp, owner);
            // What the parameter reads the positional tuple an application hands it by: the
            // slot's labels where the slot names its components, its own type's where the slot
            // is positional (`get_a(t: (a: Int64, b: Int64))` at `(Int64, Int64)`), none where
            // neither names any.
            let named = |f: &Option<Vec<(Symbol, Value)>>| -> Option<Rc<[Symbol]>> {
                f.as_ref()
                    .filter(|f| !f.is_empty() && !is_positional_tuple_names(kb, f))
                    .map(|f| f.iter().map(|(l, _)| *l).collect())
            };
            let slot_labels = named(&slot_fields).or_else(|| named(&named_tuple_field_pairs(kb, &own_a)));
            CallableAtSlot::AtSlot { ty, slot_labels }
        }
        CallableParams::Many => {
            let Some(slot_fields) = slot_fields else {
                return CallableAtSlot::Refused;
            };
            // An operation of other than one parameter has the tuple of its parameters for `A`
            // (`()` for none), as its eta arrow is built.
            let own_fields = named_tuple_field_pairs(kb, &own_a)
                .expect("a callable of several parameters has a tuple for its `A`");
            let own_names: Vec<&str> = own_fields
                .iter()
                .map(|(l, _)| short_name_of(kb.local_name_of(*l)))
                .collect();
            let slot_names: Vec<&str> = slot_fields
                .iter()
                .map(|(l, _)| short_name_of(kb.local_name_of(*l)))
                .collect();
            let Some(takes) = crate::kb::call_form::slot_components_of_params(&own_names, &slot_names)
            else {
                return CallableAtSlot::Refused;
            };
            // `takes[j]` is the component parameter `j` takes; read the other way round, the
            // parameter at each component.
            let mut at_component: Vec<usize> = vec![0; takes.len()];
            for (j, &i) in takes.iter().enumerate() {
                at_component[i] = j;
            }
            let fields: Vec<(Symbol, Value)> = slot_fields
                .iter()
                .zip(&at_component)
                .map(|((label, _), &j)| (*label, own_fields[j].1.clone()))
                .collect();
            let param = named_tuple_value(kb, &fields, sp, owner);
            let binders = own_binders.map(|b| {
                // An arrow's binders are its own parameters by position (the `Arrow` entity's
                // doc), so there is one for each component the parameters were mapped to.
                let places = value_list_elements(kb, &b);
                assert_eq!(
                    places.len(),
                    at_component.len(),
                    "an arrow's binders are one per parameter: {} binders beside {} parameters",
                    places.len(),
                    at_component.len(),
                );
                let reordered = at_component.iter().map(|&j| places[j].clone()).collect();
                crate::kb::load::build_value_list(kb, reordered)
            });
            let ty = arrow_value(kb, &param, &own_result, &own_row, binders, sp, owner);
            let slot_labels = slot_fields.iter().map(|(l, _)| *l).collect();
            CallableAtSlot::AtSlot { ty, slot_labels: Some(slot_labels) }
        }
    }
}

/// The param type of a callable (`arrow` or `Function[A, B, E]`), used to type a
/// lambda's parameter from the checking direction (an expected `Function[A, B]`
/// tells us the param is `A`). Carrier-agnostic over [`TermView`], `Value` out.
pub(super) fn extract_function_param_type<V: TermView>(
    kb: &mut KnowledgeBase,
    fn_type: &V,
) -> Option<Value> {
    arrow_parts(kb, fn_type)?.0
}

/// Ord component types of a `named_tuple(fields: [TypeField(name,
/// type), …])` type. Used to bind a tuple-destructuring pattern's
/// sub-patterns positionally (`lambda (a, b) -> ...` checked against
/// `Function[(A, B), R]` types `a: A`, `b: B`). Returns `None` for a
/// non-tuple type.
/// Component types of a named-tuple type, in field order, carrier-agnostically
/// (WI-342 env data-flow): reads via [`extract_type`] so a `Value::Node` tuple (a
/// component that is a denoted-bearing lambda arrow) is handled too, and yields
/// each component as a carrier-agnostic [`Value`]. A non-tuple type yields `None`.
pub(super) fn named_tuple_field_types<V: TermView>(
    kb: &KnowledgeBase,
    ty: &V,
) -> Option<Vec<Value>> {
    named_tuple_field_pairs(kb, ty).map(|f| f.into_iter().map(|(_, v)| v).collect())
}

/// As [`named_tuple_field_types`], KEEPING each component's name — the form that
/// discards them is this one plus a projection, not the other way round.
///
/// WI-803 needs the names: `bind_and_label_pattern` types binder `i` from
/// component `i` AND records that component's label on the pattern, so the matcher
/// can fetch it by name from a value that may order its components differently.
pub(super) fn named_tuple_field_pairs<V: TermView>(
    kb: &KnowledgeBase,
    ty: &V,
) -> Option<Vec<(Symbol, Value)>> {
    match extract_type(kb, ty) {
        TypeExtractor::NamedTuple(fields) => Some(fields),
        _ => None,
    }
}

/// Extract the variable name symbol from a `var_pattern`.
/// WI-511 (WI-348): reads the `Pattern` occurrence directly — its var name is
/// already a `Symbol`, no `pattern_to_term` lowering.
pub(super) fn extract_pattern_var_name(pattern: &Rc<NodeOccurrence>) -> Option<Symbol> {
    match pattern.as_pattern()? {
        Pattern::Var { name, .. } => Some(*name),
        _ => None,
    }
}

/// Extract a named type parameter from a parameterized type, carrier-agnostically
/// (WI-342 S3a): reads via [`extract_type`] so a `Value::Node` parameterized (a
/// denoted-bearing binding) is handled too, and returns the binding as a
/// carrier-agnostic [`Value`]. WI-361: a parameterized type is `Fn{S, named}`
/// (base sort = functor, bindings = named args), so the lookup is over those
/// bindings — `extract_type_param(List[T = Int], "T") → Some(Value::Term(Int))`.
pub(crate) fn extract_type_param<V: TermView>(
    kb: &KnowledgeBase,
    ty: &V,
    param: &str,
) -> Option<Value> {
    if let TypeExtractor::Parameterized { bindings, .. } = extract_type(kb, ty) {
        bindings
            .into_iter()
            .find(|(s, _)| kb.local_name_of(*s) == param)
            .map(|(_, v)| v)
    } else {
        None
    }
}

//! Callable shapes: the `Function` spec recognizer, arrow parts and arity, conformance
//! errors, and positional argument expectations.

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
/// shallow reading never showed (`List[T = X]` with `X := (Int64) -> Bool`). Conservative
/// on a carrier it cannot read: a non-`Term`/`Node` value answers `true` (withhold), since
/// "might contain a callable" must not license the widening.
pub(super) fn type_contains_callable(kb: &KnowledgeBase, v: &Value) -> bool {
    match v {
        Value::Term { id: t, .. } => term_contains_callable(kb, *t),
        Value::Node(occ) => node_contains_callable(kb, occ),
        _ => true,
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
            TypeNode::Denoted { .. } => false,
            TypeNode::Parameterized { base, bindings } => {
                child(base) || bindings.iter().any(|(_, c)| child(c))
            }
            TypeNode::EffectsRows { effects_expr } => child(effects_expr),
            TypeNode::Arrow { .. } => true,
            TypeNode::ExprCarried { value, member } => child(value) || child(member),
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
    for key in ["param", "result", "effects", "arity", "base"] {
        kb.intern(key);
    }
    extract_type(kb, ty)
}

/// The decode half of [`arrow_parts`], over an ALREADY-CLASSIFIED callee
/// (WI-798). Split out so a caller that has classified the callee once — see
/// [`extract_callable_type`] — can read its parts without paying for a second
/// classification. [`arrow_parts`] keeps its carrier-taking signature for the
/// many single-shot callers that have no extraction to share.
fn arrow_parts_extracted(
    kb: &KnowledgeBase,
    ty: &TypeExtractor,
) -> Option<(Option<Value>, Value, Option<Value>)> {
    // Borrowed, cloning only the three children handed back: a whole-extractor
    // clone here would re-copy the binding vector this split exists to stop
    // rebuilding.
    match ty {
        // WI-791: `arity` is deliberately NOT returned here. This decomposition is
        // shared with `Function[A, B, E]`, which states no arity, so a caller that
        // needs one is asking a question only an `arrow` can answer and must ask it
        // separately via [`arrow_arity`]. Folding it into this tuple would hand
        // every `Function` consumer an absence to invent a default for.
        TypeExtractor::Arrow {
            param,
            result,
            effects,
            arity: _,
        } => Some((Some(param.clone()), result.clone(), Some(effects.clone()))),
        TypeExtractor::Parameterized { base, bindings } => {
            let (param, result, effects) = function_spec_parts(kb, *base, bindings)?;
            Some((param.cloned(), result.clone(), effects.cloned()))
        }
        _ => None,
    }
}

/// WI-791: an arrow's declared PARAMETER-LIST LENGTH, carrier-agnostic. `None`
/// when the type states none — which is NOT a defensive fallback but the one
/// meaningful absence in the system:
///
///   * a `Function[A, B, E]` (the stdlib surface spelling [`arrow_parts`] also
///     decomposes) carries no arity binding and cannot: its `A` is the ONE
///     argument `apply(f, x: A)` passes, so `Function[(T, T), Bool]` denotes both
///     the single-tuple-argument reading and the eta arrow of a 2-parameter op,
///     and has denoted both since WI-775. An arrow-vs-`Function` check therefore
///     compares parameter DATA types by name and asks nothing about arity;
///   * anything that is not a callable type at all.
///
/// Every `arrow` the engine mints states its arity — the three producers that
/// know it ([`operation_as_function_value`], the loader's `TypeExpr::Arrow` arm,
/// the `LambdaBody` frame) all pass it, and the rebuild sites transplant it — so
/// a `None` from an `arrow` head means the term is malformed, and the callers
/// below treat that as "not comparable" rather than inventing a count.
/// `arity_key` is passed in already interned: the sole caller reads two arrows in
/// a row on the hot conformance path and should pay one symbol lookup, not two.
pub(super) fn arrow_arity<V: TermView>(
    kb: &KnowledgeBase,
    ty: &V,
    arity_key: Symbol,
) -> Option<usize> {
    match named_child_value(kb, ty, arity_key)? {
        Value::Term { id, .. } => const_usize_of(kb, id),
        _ => None,
    }
}

/// WI-801: `A`'s COMPONENT COUNT, as [`arity_admitted_at_function_slot`] reads it
/// — `Some(Some(n))` for a tuple type of `n` components, `Some(None)` for a known
/// NON-tuple (one indivisible value), and `None` for a type that states neither
/// yet.
///
/// The outer `None` is the load-bearing one. A rigid type parameter, an
/// unresolved projection, a free inference var — a generic
/// `operation ap[T](f: Function[A = T, B = R])` must stay unconstrained, since a
/// component count is exactly what instantiation supplies. Gating on
/// [`resolved_type_is_ground`] rather than on the [`extract_type`] shape is what
/// separates "not a tuple" from "not yet known": both fall out of the match's
/// `_` arm, and only the first may be read as "one value".
fn function_param_component_count(kb: &mut KnowledgeBase, a: &Value) -> Option<Option<usize>> {
    if !resolved_type_is_ground(kb, a) {
        return None;
    }
    match extract_type(kb, a) {
        TypeExtractor::NamedTuple(fields) => Some(Some(fields.len())),
        _ => Some(None),
    }
}

/// WI-801: `(A's components, the callback's arity)` when `actual`'s arity is NOT
/// one a DECLARED `Function[A, B, E]` slot can apply — the half of the conformance
/// question [`arrow_arity`]'s `None` leaves open.
///
/// "A `Function` states no arity" is true and was taken to mean nothing about
/// arity is decidable here. It is not: `A` states a component count, and the slot
/// reaches exactly two call counts (one whole `A`, or `A`'s components spread), so
/// exactly two arities can stand in it. Everything else typechecks and traps —
/// measured: a 3-binder lambda at a 2-component `A` loaded clean and trapped
/// `ArityMismatch { expected: 3, got: 2 }`.
///
/// Why the LAMBDA spelling alone needed this. An op reference's eta arrow carries
/// its parameter list as a CONCRETE tuple type, so a wrong count already fails the
/// PARAM comparison its callers run (`validate_arrow_param_result`,
/// `arrow_function_compatible`) — `got (_1: Int64, _2: Int64, _3: Int64) -> Int64`.
/// An unannotated lambda ADOPTS the expected `A` as its param type (the
/// `Expr::Lambda` visit case), so its param matches `A` by construction and its
/// arity is the ONLY quantity left that can disagree — free-floating, and until
/// now unread.
///
/// Yields the two counts — `(A's components, the callback's arity)` — so the
/// DIAGNOSTIC can name them; see [`function_slot_arity_error`] on why a generic
/// type mismatch cannot. `None` is NO VERDICT, never a guess, whenever either
/// side is silent: `declared` stating an arity means it is an `arrow`, whose own
/// equality check owns the comparison; `actual` stating none means it is not a
/// callable this can count; an `A` that is not yet known states no component
/// count, and a generic callback slot must stay unconstrained.
fn function_slot_arity_counts<D: TermView, A: TermView>(
    kb: &mut KnowledgeBase,
    declared: &D,
    actual: &A,
    arity_key: Symbol,
) -> Option<(Option<usize>, usize)> {
    if arrow_arity(kb, declared, arity_key).is_some() {
        return None;
    }
    let a_arity = arrow_arity(kb, actual, arity_key)?;
    let (Some(d_param), _, _) = arrow_parts(kb, declared)? else {
        return None;
    };
    function_slot_arity_counts_for(kb, &d_param, a_arity)
}

/// WI-801: the verdict with `A` ALREADY IN HAND — for a caller that has extracted
/// it, so the check costs no second [`arrow_parts`]. That matters at
/// [`arrow_function_compatible`], which runs per arrow-vs-`Function` comparison
/// including the ones that SUCCEED, and already holds `A` as its `b_param`;
/// re-deriving it there was a full `extract_callable_type` (five interns plus an
/// `extract_type`) for a value sitting in scope.
pub(super) fn function_slot_arity_counts_for(
    kb: &mut KnowledgeBase,
    a: &Value,
    a_arity: usize,
) -> Option<(Option<usize>, usize)> {
    let components = function_param_component_count(kb, a)?;
    if crate::kb::call_form::arity_admitted_at_function_slot(components, a_arity) {
        return None;
    }
    Some((components, a_arity))
}

/// WI-1087: at a `Function[A, B, E]` slot given a callback of `a_arity` parameters,
/// is `A` being read as the callback's PARAMETER LIST rather than as one argument's
/// DATA type?
///
/// A `Function` slot admits exactly two call counts (WI-801,
/// [`arity_admitted_at_function_slot`]): ONE whole `A`, or `A`'s components SPREAD.
/// Under the first, `A` is the argument's data type and relates BY NAME — WI-775's
/// rule, and the reason a permuted `(b, a)` still satisfies `(a, b)` there. Under
/// the SECOND, `A`'s components ARE the callback's parameters, applied positionally,
/// and the relation owed is [`TupleAlign::PARAM_LIST`]'s.
///
/// The two rules were in outright conflict before this ticket, and the by-name one
/// won by default at both conformance sites. An operation's eta arrow always spells
/// its parameter list with the synthetic `_1.._n` (an arrow drops its binder names,
/// WI-783), so a by-name comparison refuses EVERY spread WI-801 admits — leaving that
/// second reading reachable only for a LAMBDA, which ADOPTS `A` as its param type and
/// so matches it by construction. Measured: two programs byte-identical but for
/// whether `A`'s components carry user labels, `Function[A = (Int64, Int64)]` given a
/// 2-parameter operation evaluating to -7 while `Function[A = (acc: …, x: …)]` was
/// refused. The positional spelling passed only because its labels COINCIDE with the
/// synthetic escape, and eval reads no label at all.
///
/// ARITY 1 IS NOT THIS READING even when `A` has one component: there the two call
/// counts coincide, `A` is the sole parameter's TYPE, and a tuple in that position is
/// DATA (WI-791). Kept out explicitly rather than left to fall out of the count, so
/// this predicate answers the same question [`unify_arrow_params`] and
/// [`arrow_params_compatible`] ask of an arrow.
///
/// NARROW BY DECISION (user, 2026-08-12). This does not make a named tuple relatable
/// to a positional one in general — proposal 004 rule 4 and §4.5 stand. It says only
/// that `A` in the spread reading is not a data tuple in the first place.
pub(super) fn function_slot_reads_a_as_param_list(
    kb: &mut KnowledgeBase,
    a: &Value,
    a_arity: usize,
) -> bool {
    a_arity != 1 && function_param_component_count(kb, a) == Some(Some(a_arity))
}

/// WI-1087: the mapping an eta'd operation needs to be SPREAD correctly at the slot
/// it is lifted into — `A`'s component labels in declared order, or `None` when the
/// slot does not read `A` as a parameter list.
///
/// WHY THE VALUE CANNOT DERIVE THIS. In the spread call form `f(t)`, the callee's
/// parameter `i` is `A`'s component `i` — that is what
/// [`function_slot_reads_a_as_param_list`] established, positionally — while the
/// tuple `t` conforms to `A` BY NAME and may present its components in another order,
/// since WI-803 made `<:` on a data tuple order-free. The operation's own parameter
/// names are unrelated to `A`'s (`sub2(a, b)` at `A = (acc, x)`), so nothing at the
/// apply site can recover which component each parameter wants. Measured without it:
/// `f((x: 10, acc: 3))` answering 7 where the labels say `3 - 10`.
///
/// ONLY AT A `Function` SLOT, and that is not a narrowing but the whole reachable set:
/// an `arrow` slot states its arity, so a one-argument call against a 2-parameter one
/// is an arity error long before any spread. The spread call form exists only where
/// the slot states no arity.
///
/// READ AS WRITTEN, not through σ, and the case that makes the difference is the one
/// that needs nothing: an `A` spelled as a VARIABLE (`apT[T](f: Function[A = T], t:
/// T)`) binds to the argument's OWN tuple type, so `A`'s declared order IS the value's
/// source order and reading it in source order is already right — `wi787_eta_spread_-
/// named_tuple_test` is four rows of exactly that. What a written-out `A` adds is an
/// order INDEPENDENT of the value's, which is precisely when the mapping is needed.
pub(super) fn function_slot_spread_labels(
    kb: &mut KnowledgeBase,
    sym: Symbol,
    expected: &Value,
) -> Option<std::rc::Rc<[Symbol]>> {
    let arity_key = kb.intern("arity");
    // An `arrow` slot states an arity and never spreads — see above.
    if arrow_arity(kb, expected, arity_key).is_some() {
        return None;
    }
    let (Some(a), _, _) = arrow_parts(kb, expected)? else {
        return None;
    };
    let arity = lookup_operation_info_full(kb, sym)?.params.len();
    if !function_slot_reads_a_as_param_list(kb, &a, arity) {
        return None;
    }
    let fields = named_tuple_fields(kb, &a);
    // The predicate above already agreed on the count; the equality is what lets the
    // reader zip without a length test of its own.
    (fields.len() == arity).then(|| fields.into_iter().map(|(s, _)| s).collect())
}

/// WI-1088: at a `Function`/`Function` pairing, do the two `A`s name the SAME
/// components in a DIFFERENT ORDER?
///
/// WHY A PERMUTATION MUST BE REFUSED HERE AND ONLY HERE. A `Function[A, B, E]` slot
/// admits TWO readings of `A` (WI-801) and the VALUE at it may be applied under
/// either, at a call site this pairing cannot see:
///
///  * the WHOLE-`A` reading — `A` is one argument's DATA type, related BY NAME and
///    order-free since WI-803, because the consumer reads components by label;
///  * the SPREAD reading — `A` IS the callback's parameter list, applied
///    POSITIONALLY, where order is identity (WI-782, §4.5).
///
/// `A` at a `Function` slot has to satisfy BOTH, so the admissible relation is their
/// INTERSECTION, and on the ORDER axis that intersection is
/// [`TupleOrder::Preserved`]. The by-name relation alone took the first reading's
/// answer for a pairing the second also has an opinion about.
///
/// WHAT IT COST, measured on the WI-1087 tree, loading clean and running:
///
/// ```text
/// operation inner(g: Function[A = (x: Int64, acc: Int64), B = Int64]) -> Int64 = g((acc: 3, x: 10))
/// operation outer(f: Function[A = (acc: Int64, x: Int64), B = Int64]) -> Int64 = inner(f)
/// inner(sub2) => 7      -- `inner`'s own `A` says parameter 1 <- `x`
/// outer(sub2) => -7     -- the MINT site's `A` won; `inner`'s declared `A` is not the mapping used
/// ```
///
/// The mapping a spread reads is pinned where the value is MINTED
/// ([`Value::OpRef::spread_labels`], and `Pattern::Tuple.labels` for the lambda
/// spelling — both spellings measured identically, so WI-784 holds and this is not a
/// WI-1087 regression). Re-typing at a second slot cannot move it: an `OpRef` in
/// flight is a value, and the slot it flows through is not a re-mint. So either the
/// second slot's `A` agrees with the first on order, or one of the two declarations
/// is silently not the mapping used — which is the class of wrong answer WI-1087 was
/// filed to close, one hop away.
///
/// ONLY `Function` vs `Function`, which is what the two `None` arities gate. Every
/// other pairing already answers the order question elsewhere and must not be moved:
/// an ARROW states its arity, so at the spread arity [`arrow_params_compatible`]
/// relates the lists under [`TupleAlign::PARAM_LIST`] (order Preserved already), and
/// at arity 1 the whole-`A` reading is the only one the value admits — a
/// one-parameter callable receives the tuple and reads it by label, so order-free is
/// correct there. The arrow-SLOT mirror keeps the by-name reading WI-1085 measured.
///
/// AND A PERMUTATION ONLY — not "the labels differ". A label SET disagreement is the
/// by-name relation's own refusal and renders as the ordinary mismatch; this
/// predicate speaks for the one case that relation ACCEPTS and the parameter-list
/// reading does not. Width and names are left exactly as WI-775/§4.5 have them: the
/// order axis is the one the measurement above names, and tightening the other two
/// on this pairing would refuse programs nothing has measured.
///
/// THE CALLER READS `A` THROUGH [`function_spec_parts`], which yields nothing for a
/// `Function` that binds no `B` — and that is the right reader here rather than a hole
/// this predicate should route around. MEASURED: a `Function[A = …]` slot with no `B` is
/// not a callback slot at all, so the spread this guard protects cannot occur behind it.
/// `inner(g: Function[A = (x, acc)]) -> Int64 = g(…)` is refused with `expected Int64,
/// got g.B`, and passing a 2-parameter operation into such a slot is refused before that
/// with `expected Function[A = (x: Int64, acc: Int64)], got Int64` — the eta lift needs
/// the result type. So the pairing this skips is one that cannot reach a spread, and
/// asking a SECOND, `B`-free question about what a `Function` is would be the one-name-
/// two-questions defect rather than a widening.
pub(super) fn function_pairing_permutes_a(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    d_arity: Option<usize>,
    a_arity: Option<usize>,
    declared_a: &Value,
    actual_a: &Value,
) -> bool {
    if d_arity.is_some() || a_arity.is_some() {
        return false;
    }
    // σ-RESOLVED HERE, so the two call sites cannot hand this different operands while
    // both claim to consult "the same predicate" — the drift a review caught before it
    // was live. [`validate_arrow_param_result`] had already walked its pair;
    // [`parameterized_compatible_view`] passes the `A` bindings as `extract_type` read
    // them, and `named_tuple_fields` answers EMPTY for a variable, so an `A` that σ has
    // bound to a named tuple would have made this answer `false` — an under-refusal, and
    // a silent one. Owning the walk is what makes the two sites' claim true rather than
    // nearly true; walking an already-walked value is an identity.
    let labels = |kb: &mut KnowledgeBase, ty: &Value| -> Vec<Symbol> {
        let resolved = walk_type_deep_value(kb, subst, ty);
        named_tuple_fields(kb, &resolved)
            .into_iter()
            .map(|(s, _)| s)
            .collect()
    };
    // A non-tuple `A` (and one σ leaves unknown) has NO fields, so the sequence test
    // answers `false` on its own — no second gate to keep in step with
    // [`function_param_component_count`]. Likewise `|A| <= 1`: a sequence of at most one
    // label cannot differ from itself by order alone. The DECLARED side is read first
    // and short-circuits, so a `Function` slot whose `A` is a bare type (the common
    // higher-order shape) pays one walk rather than two.
    let d = labels(kb, declared_a);
    if d.is_empty() {
        return false;
    }
    let a = labels(kb, actual_a);
    if d == a {
        return false;
    }
    // BY `Symbol` IDENTITY, which is what [`align_named_tuple_slots`] compares labels by
    // — deliberately the same keying as the relation this narrows, not a second opinion
    // about when two labels are one label. Two `A`s whose labels interned to DIFFERENT
    // symbols never reach here as a permutation, because that walk would not have matched
    // them up either and the pairing is refused by name (see [`TupleOrder::Free`] on the
    // Symbol-vs-short-name split, which predates this and bounds both sides alike).
    let sorted = |v: &[Symbol]| {
        let mut k: Vec<u32> = v.iter().map(|s| s.index()).collect();
        k.sort_unstable();
        k
    };
    sorted(&d) == sorted(&a)
}

/// WI-801: the ONE renderer for "`actual` does not conform to `declared`" at a
/// site that has both types in hand — a [`TypeError::TypeMismatch`], except where
/// the disagreement is an ARITY, which [`function_slot_arity_error`] renders as
/// itself.
///
/// It has to be a renderer shared by the FAILURE paths rather than a check run
/// ahead of them. The two sites that DECIDE the arity case —
/// [`arrow_function_compatible`] and [`validate_arrow_param_result`] — cannot SAY
/// it: the first is inside `types_compatible` and returns `bool`, so the pair is
/// not in scope where the verdict is reached. Running the check at the ENTRY of
/// every conformance test instead was measured at 1383 invocations to serve 9,
/// each paying a `kb.intern` the surrounding code deliberately hoists — and it
/// still reached only ONE of the three channels that render this error. The three
/// are the op-ARGUMENT, the let-ANNOTATION and the op-RETURN; all now route here.
///
/// WI-20260824-Q0093 hangs one more thing on that: `actual_node` is the occurrence
/// `actual` is the type OF, so a rejected proposal-055 type value can name what it
/// DENOTES (`got Type (Cell[V = Int64])`, design §8) — see
/// [`TypeError::TypeMismatch::denoted`]. Being the shared renderer is exactly why it
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
    if let Some(err) = function_slot_arity_error(kb, &declared, &actual, span, &context) {
        return err;
    }
    TypeError::TypeMismatch {
        site: TypeError::here(),
        span,
        context,
        expected: declared,
        denoted: denoted_type_value(kb, actual_node),
        actual,
    }
}

/// WI-20260824-Q0093 (`docs/design/055-implementation.md` §8) — the SURFACE a rejected
/// occurrence denotes, when it is a proposal-055 classified type value, for
/// [`TypeError::TypeMismatch::denoted`]. `None` for every other expression, and for a
/// check with no occurrence to ask.
///
/// Keyed on the CLASSIFICATION ([`Expr::TypeValue`]), never on "the type came out as
/// `Type`": a `Type`-valued expression that is not a written type — a call returning one,
/// a variable holding one — denotes nothing at this source position, and a message
/// inventing a surface for it would name a sort the author did not write.
///
/// Printed through [`TermPrinter::print_occurrence`], which is the writer that already
/// owes this shape its SOURCE spelling (`Cell[V = Int64]`, brackets and `=`, per its own
/// `Expr::TypeValue` arm) — so the message quotes text that would load back as what was
/// written, rather than a debug form. No interning: the occurrence is read as it stands,
/// which is what CLAUDE.md's note asks of a transient term on a diagnostic path.
pub(super) fn denoted_type_value(
    kb: &KnowledgeBase,
    node: Option<&Rc<NodeOccurrence>>,
) -> Option<String> {
    let mut node = node?;
    // THROUGH THE WRAPPERS WHOSE TYPE IS ALREADY THEIR CHILD'S, and only those. A `let`
    // reports its CONTINUATION's type (`TypeBuildFrame::LetFinal`) and an in-body `proof`
    // its continuation's too ("the proof is transparent to types",
    // `TypeBuildFrame::ProofStmt`) — so where the rejected `Type` came from the child,
    // the denotation does too, and stopping at the wrapper would print `got Type` about a
    // type value standing in plain sight. Every other expression form contributes
    // something of its own to the type it reports (a lambda's arrow, a tuple's components)
    // and is NOT descended: its `actual` already shows the `Type` in the position that
    // carries it, and naming one component's denotation as the whole expression's would be
    // a different claim.
    loop {
        node = match node.as_expr() {
            Some(Expr::TypeValue { .. }) => {
                return Some(crate::persistence::print::TermPrinter::new(kb).print_occurrence(node))
            }
            Some(Expr::Let { body, .. }) | Some(Expr::Proof { body, .. }) => body,
            _ => return None,
        };
    }
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
            denoted: denoted_type_value(kb, node),
            actual: ty.clone(),
        }),
    }
}

/// WI-801: the arity disagreement at a `Function[A, B, E]` slot, rendered as
/// ITSELF rather than as a structural type mismatch. `None` when the arities
/// agree or nothing is decidable — see [`function_slot_arity_counts`].
///
/// A generic mismatch cannot state this one. A callback's arrow carries `A` as
/// its `param`, because an unannotated lambda ADOPTS the expected type (the
/// `Expr::Lambda` visit case), so both sides print the SAME parameter list and
/// only the unprinted `arity` child differs. The measured text was `expected
/// Function[A = (_1: Int64, _2: Int64), B = Int64], got (_1: Int64, _2: Int64) ->
/// Int64` — true, useless, and the expected-X-got-X shape WI-795 exists to keep
/// out. The remedy is WI-795's: render the PAIR that actually differs. The printer
/// is deliberately NOT the place to fix it — its arrow rendering is a faithful
/// round trip, and an arity/param-count disagreement is a shape it is not meant
/// to spell.
///
/// Names BOTH admissible counts, because `Function` admits two readings and a
/// reader who has just been refused needs to know which ones were open — the same
/// discipline the count diagnostic in [`positional_arg_expectations`] follows,
/// including its collapse at ONE (where the two readings coincide, so offering a
/// choice between 1 and 1 would read as a formatting bug). The two messages stay
/// separate strings deliberately: that one counts call ARGUMENTS and this one
/// callback PARAMETERS, and a shared wording would have to lie about one of them.
pub(super) fn function_slot_arity_error<D: TermView, A: TermView>(
    kb: &mut KnowledgeBase,
    declared: &D,
    actual: &A,
    span: Option<Span>,
    context: &TypeErrorContext,
) -> Option<TypeError> {
    let arity_key = kb.intern("arity");
    let (components, a_arity) = function_slot_arity_counts(kb, declared, actual, arity_key)?;
    // At a NON-tuple `A`, and at a 1-component one, the two readings coincide on
    // 1 — offering a choice between 1 and 1 would read as a formatting bug.
    let expected = match components {
        Some(n) if n != 1 => format!(
            "a callback of 1 parameter (taking the whole argument type) or {n} (its \
             components spread)",
        ),
        _ => "a callback of 1 parameter — this function's argument type has no \
              components to spread"
            .to_string(),
    };
    Some(TypeError::Other {
        site: TypeError::here(),
        span,
        context: context.clone(),
        expected,
        actual: format!(
            "a callback of {a_arity} parameter{}",
            if a_arity == 1 { "" } else { "s" },
        ),
    })
}

/// Normalize a raw effects-row [`Value`] (the third element of [`arrow_parts`])
/// into a canonical `effects_rows(...)` carrier the row machinery
/// ([`subtype_effect_rows`] / [`unify_effect_rows`]) consumes. An arrow's
/// `effects` child and a `Value::Node` row are already canonical and pass
/// through untouched; only a legacy `List[Type]` `Function.E` binding (a
/// `TermId` carrier) is flattened and re-canonicalized.
pub(super) fn canonical_effects_row(kb: &mut KnowledgeBase, row: &impl TermView) -> Value {
    let effects_rows_sym = kb.try_resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows");
    match row.as_bind_value() {
        // Ground carrier: a canonical `effects_rows(...)` passes through; a
        // legacy `List[Type]` (Function.E pre-WI-331) is flattened + re-
        // canonicalized so the row machinery sees one shape.
        BindValue::Term(t) => {
            let is_canonical = matches!(
                (kb.get_term(t), effects_rows_sym),
                (Term::Fn { functor, .. }, Some(er)) if *functor == er
            );
            if is_canonical {
                Value::term(t)
            } else {
                let flat = list_to_vec(kb, t);
                Value::term(kb.build_canonical_effects_rows(&flat))
            }
        }
        // A `Value::Node` effects row is always the canonical occurrence form.
        BindValue::Value(v) => v,
        // An effects row is never carried as a deferred query path; the empty
        // row is a safe (unreachable) fallback.
        BindValue::Path(_) => Value::term(kb.build_canonical_effects_rows(&[])),
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
        // Function.E binding pre-WI-331).
        BindValue::Term(t) => effects_rows_to_flat_list(kb, t)
            .into_iter()
            .map(Value::term)
            .collect(),
        // `Value::Node` carrier: decompose the occurrence row into its present
        // labels (plus an open-row tail), the occurrence never re-grounded
        // (WI-341) — matching the former `extract_function_type_parts_value`.
        _ => {
            let subst = Substitution::new();
            match decompose_effect_row(kb, &subst, row) {
                Some((mut present, tails, _absent)) => {
                    for tail_tid in tails {
                        present.push(Value::term(tail_tid));
                    }
                    present
                }
                None => Vec::new(),
            }
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
///   - bare `Term::Var`    → push as tail (matches the shape the WI-320
///                          bridge fact emits: `effects_rows(?expr)` whose
///                          inner is an unbound Var. Without this, the
///                          bridge head decodes to an empty flat list and
///                          effects silently vanish.)
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
            // Bare Var inside effects_rows is an open-row tail (e.g. the
            // WI-320 bridge fact head shape `effects_rows(?expr)`). Treat
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
pub(super) fn extract_function_type_parts(
    kb: &mut KnowledgeBase,
    fn_type: &TypeExtractor,
) -> Option<(Value, Vec<Value>)> {
    let (_, result, eff) = arrow_parts_extracted(kb, fn_type)?;
    let effects = eff
        .map(|row| effect_row_present_values(kb, &row))
        .unwrap_or_default();
    Some((result, effects))
}

/// WI-783: the DECLARED PARAMETER LIST of a callable type — `(acc: T, x: U)` of
/// `(acc: T, x: U) -> R` — as `(binder-name, type)` pairs in declaration order.
/// This is what resolves a NAMED argument at a function-VALUE application
/// (`f(x: 10, acc: 3)`) to a parameter slot, the way a named operation's
/// `op.params` does for a direct call.
///
/// `None` means "this callee's type records no parameter names", which is NOT
/// the same as "no parameters" (`Some(vec![])`) — the caller must then reject
/// named arguments rather than guess, since it can neither order them nor tell a
/// valid label from a typo. Three shapes deliberately yield `None`:
///
///  - A ONE-parameter arrow. `(v: Int64) -> Int64` extracts its param as the
///    bare `Int64`: the binder name `v` is dropped when the arrow type is built,
///    so it is simply not recoverable here (measured — this is a property of the
///    arrow representation, not of this function).
///  - `Function[A, B, E]`. WI-775 settled that `A` is the ARGUMENT's data type —
///    what flows to `apply(f, x: A)` — so a named-tuple `A` is ONE tuple-typed
///    argument, not a two-slot parameter list. Reading binder names off it would
///    re-conflate the two positions WI-775 split apart.
///  - A param that is not a named tuple at all (a type variable, a projection).
///
/// Gating on [`TypeExtractor::Arrow`] — not on [`arrow_parts`], which maps both
/// spellings onto one `param` — is what keeps the `Function` case out.
///
/// The former KNOWN AMBIGUITY here is CLOSED by WI-791: an arrow taking ONE
/// tuple-typed parameter used to carry the same `named_tuple` param an
/// n-parameter list does, so this read the former as an n-slot list and resolved
/// `f(a: 1, b: 2)` against a DATA tuple's component names. The arrow now records
/// its `arity`, and arity one lands on the first `None` case above — those names
/// are the tuple's components, reachable as `f((a: 1, b: 2))`, and are not
/// parameter labels.
///
/// WI-798: takes the callee's ALREADY-EXTRACTED type rather than its carrier —
/// see [`positional_arg_expectations`] on what a second classification costs.
/// Both of this function's callers sit on a path that has just classified the
/// same value.
pub(super) fn arrow_declared_param_list(
    kb: &KnowledgeBase,
    fn_type: &TypeExtractor,
) -> Option<Vec<(Symbol, Value)>> {
    let (param, arity) = match fn_type {
        TypeExtractor::Arrow { param, arity, .. } => (param, *arity),
        _ => return None,
    };
    // WI-791: only a real parameter LIST carries binder names to resolve against.
    if arity == 1 {
        return None;
    }
    match extract_type(kb, param) {
        // The list holds exactly `arity` slots by construction at every producer.
        // It is not re-checked here: this reader only needs the binder NAMES, and
        // a disagreement means an ill-formed arrow, which the conformance relation
        // rejects on its own — asserting it here would turn that type error into a
        // panic.
        TypeExtractor::NamedTuple(fields) => Some(fields),
        _ => None,
    }
}

/// WI-788: what a positional application must check its arguments against — a
/// TOTAL answer, so that "nothing to check" is a named outcome rather than an
/// anonymous fallthrough.
///
/// The three-way split exists because the two callable spellings fail
/// differently. An `arrow` states its arity, so a count disagreement is decidable
/// there. A `Function[A, B, E]` states none — WI-775 settled that `f(3, 10)` and
/// `f((3, 10))` are both legal at that slot — so no count can be REQUIRED of it,
/// only OBSERVED at the call; and when its `A` is not yet a known tuple, nothing
/// about the components is statable at all. Collapsing that last case into the
/// same `None` as "not a callable" is what left the `Function` slot checking
/// nothing (WI-788): the absence was real, but unnamed, so it read as "handled".
pub(super) enum ArgExpectations {
    /// Check argument `i` against slot `i`; the count is already agreed.
    ///
    /// WI-801: `gather` carries `A` when these arguments are `A`'s COMPONENTS
    /// spread across the call at a `Function[A, B, E]` slot, and the call must
    /// therefore be normalized into ONE whole-`A` tuple before eval — see
    /// [`gather_spread_args_into_tuple`]. `None` everywhere else: at an `arrow`
    /// slot the arguments are genuine separate parameters, and at a `Function`
    /// slot given ONE argument the call is already in whole-`A` form.
    ///
    /// It carries `A` ALONE; the component LABELS the rewrite needs are `slots`'
    /// own keys, taken by the consumer. Carrying them here too would store the
    /// same extraction twice — and re-deriving them from `A` downstream is the
    /// `extract_type`-per-application the typer's WI-798 notes exist to prevent.
    Slots {
        slots: Vec<(Symbol, Value)>,
        gather: Option<Value>,
    },
    /// The supplied count cannot be right. `expected` describes what would be.
    CountMismatch { expected: String },
    /// The callee's argument type is not known well enough to state anything.
    /// The one GENUINE absence here — distinct from a count or type disagreement,
    /// and the only case that is silent by design.
    NoVerdict,
}

/// WI-788: the sole reader behind the positional argument check, covering BOTH
/// callable spellings so the two cannot drift into checking different things.
///
/// `positional` and `total` differ only for an `arrow`: it resolves LABELS to
/// slots, so a labelled argument occupies one and the count must include it. A
/// `Function` has no declared binder names to resolve a label against, so a label
/// there is rejected outright by [`arrow_declared_param_list`]'s `None` path in
/// the caller — counting it here as well would report the same mistake twice.
///
/// WI-798: `fn_type` arrives ALREADY EXTRACTED. The two readers below are
/// disjoint on the variant — [`TypeExtractor::Arrow`] vs `Parameterized` — so
/// classifying the callee once and handing both the result loses no dispatch,
/// while each `extract_type` it removes costs a head classify plus a fresh
/// binding vector with every bound type cloned into it. This runs per
/// application.
pub(super) fn positional_arg_expectations(
    kb: &mut KnowledgeBase,
    fn_type: &TypeExtractor,
    declared: Option<&[(Symbol, Value)]>,
    positional: usize,
    total: usize,
) -> ArgExpectations {
    if let Some(slots) = arrow_positional_param_slots(kb, fn_type, declared) {
        // ARITY FIRST. A call whose count is wrong has no slot-wise correspondence
        // to report against, and eval refuses it outright (`spread_eta_args`
        // demands an exact count), so the verdict must be ONE arity error rather
        // than a cascade of mis-aligned type mismatches — or, worse, silence when
        // the truncated prefix happens to typecheck.
        if total != slots.len() {
            return ArgExpectations::CountMismatch {
                expected: format!(
                    "{} argument{} — the parameter list this function value declares",
                    slots.len(),
                    if slots.len() == 1 { "" } else { "s" },
                ),
            };
        }
        return ArgExpectations::Slots {
            slots,
            gather: None,
        };
    }
    let Some(param_ty) = function_spec_param_type(kb, fn_type) else {
        // Neither spelling — a type variable, a projection, a malformed callee.
        // Not a callable this check can read, so it states nothing.
        return ArgExpectations::NoVerdict;
    };
    // A LABELLED argument at a `Function` slot is always an error — there are no
    // declared binder names to bind it to — and the caller reports exactly that,
    // naming the offending label. Counting labelled arguments here would compare
    // `A`'s component count against the POSITIONAL count only, and the caller
    // renders `actual` from the TOTAL, so a fully-labelled call produced a
    // self-contradictory "expected … or 2 …, got 2 arguments" that also preempted
    // the accurate diagnostic. Two currencies; say nothing and let the precise
    // error through.
    if total != positional {
        return ArgExpectations::NoVerdict;
    }
    // ONE argument IS `A`; N arguments are `A`'s components spread across the
    // call. Both are legal (WI-775), so the count is read, not required.
    //
    // DYNAMIC TWIN: eval's `spread_eta_args` / `gather_closure_arg` pivot on the
    // CALLEE's own arity (`params.len()` / `Pattern::binder_arity`), whereas this
    // pivots on `A`'s component count. The two coincide exactly when the callback
    // conforms to `Function[A, …]`, which the arrow/lambda conformance check
    // establishes separately — see `Pattern::binder_arity` (kb/node_occurrence.rs)
    // on why the quantities the two sides agree on must be kept in view.
    if positional == 1 {
        return ArgExpectations::Slots {
            slots: vec![(kb.intern(&positional_label(0)), param_ty)],
            // Already the whole-`A` form; nothing to normalize.
            gather: None,
        };
    }
    match extract_type(kb, &param_ty) {
        TypeExtractor::NamedTuple(fields) if fields.len() == positional => {
            // WI-801: THE spread form. The typer is the only party that can act
            // on it — the gather needs `A`'s component LABELS, which are erased
            // by the time eval runs — so it normalizes the call to `f((a: …, b:
            // …))` here rather than leaving eval to guess a spelling.
            //
            // This fires at every count but ONE, including ZERO: `f()` at
            // `Function[A = (), B]` reaches a 1-binder callback as a Gather of
            // zero arguments and trapped exactly as `f(1, 2)` did. Arity one is
            // the sole count that is already whole, and it returned above.
            ArgExpectations::Slots {
                slots: fields,
                gather: Some(param_ty),
            }
        }
        TypeExtractor::NamedTuple(fields) => ArgExpectations::CountMismatch {
            // At component count ONE the two readings coincide — the lone
            // argument is both "the tuple" and "its only component spread" — so
            // offering a choice between 1 and 1 would read as a formatting bug.
            expected: if fields.len() == 1 {
                "1 argument".to_string()
            } else {
                format!(
                    "1 argument (the tuple itself) or {} (its components spread)",
                    fields.len(),
                )
            },
        },
        // `A` is not a tuple TYPE — a rigid type parameter, a projection, anything
        // unresolved. The spread form is a claim about `A`'s COMPONENTS, and a type
        // with no known components neither satisfies nor refutes it. A generic
        // `operation ap[A](f: Function[A, R])` whose body spreads `f(x, y)` reaches
        // eval and is checked by the matcher against the closure's real binder count.
        _ => ArgExpectations::NoVerdict,
    }
}

/// WI-788: the single argument type `A` of the stdlib `Function[A, B, E]`
/// spelling, and ONLY that spelling — `None` for a real `arrow`, which states an
/// arity and is checked through [`arrow_positional_param_slots`], and `None` for
/// everything else.
///
/// The two are deliberately disjoint rather than one reader: an `arrow` can be
/// asked how many slots it has, a `Function` cannot (WI-775 settled that its `A`
/// is the ONE argument `apply(f, x: A)` passes, so `f(3, 10)` and `f((3, 10))`
/// are both legal at a `Function` slot). Folding them together would hand the
/// arity-checking caller an absence to invent a default for — which is exactly
/// how the `Function` slot ended up checking NOTHING.
///
/// WI-798: reads `A` out of the bindings the CALLER's extraction already built,
/// rather than delegating to [`arrow_parts`] — that would classify the same value
/// a second time, re-allocating the binding vector and re-cloning every bound
/// type. The disjointness above is what makes one extraction safe to share: this
/// arm fires only on `Parameterized`, its peer reader only on `Arrow`. Nothing
/// here interns, which is why `kb` is shared rather than `&mut`.
fn function_spec_param_type(kb: &KnowledgeBase, fn_type: &TypeExtractor) -> Option<Value> {
    match fn_type {
        TypeExtractor::Parameterized { base, bindings } => {
            function_spec_parts(kb, *base, bindings).and_then(|(param, _, _)| param.cloned())
        }
        _ => None,
    }
}

/// WI-792: the POSITIONAL parameter SLOTS of a callable type — one
/// `(name, type)` per parameter, in declaration order. A positional application
/// checks argument `i` against slot `i`, and must supply exactly `len()` of them.
///
/// The POSITIONAL peer of [`arrow_declared_param_list`], differing from it in
/// exactly one place, deliberately: an arity-ONE arrow. That reader returns
/// `None` there because the arrow representation DROPS a lone binder's name, so a
/// LABEL has nothing to resolve against. A positional argument needs no name —
/// the sole parameter's type IS the `param` slot — so it is checkable here, and
/// reported against the synthetic position `_1`. That synthetic name is for the
/// DIAGNOSTIC only: nothing resolves a label through this list, so minting one
/// cannot make `f(_1: 5)` start binding at arity one.
///
/// `None` means the callee's type STATES NO ARITY, and that absence is
/// load-bearing rather than defensive. A `Function[A, B, E]` carries no arity and
/// cannot: WI-775 settled that its `A` is the ONE argument `apply(f, x: A)`
/// passes, so `f(3, 10)` and `f((3, 10))` are BOTH legal at a `Function` slot
/// (`operations_and_lambdas_are_interchangeable_in_both_application_forms`) and
/// neither a count nor a slot-wise type check can be stated over it. Gating on
/// [`TypeExtractor::Arrow`] — not on [`arrow_parts`], which maps both spellings
/// onto one `param` — is what keeps `Function` out; reading that `A` as a single
/// parameter would read `f(3, 10)` as two arguments against one slot and refuse
/// a program the runtime handles by design.
///
/// WI-798: reads the extraction its caller already performed — see
/// [`positional_arg_expectations`] on why sharing one costs no dispatch — and
/// takes `declared` as the caller's ONE [`arrow_declared_param_list`] reading,
/// rather than deriving its own. That the two readers agree on the slots is the
/// point of the arm below; taking the same list makes them agree by construction
/// instead of by both walking to the same answer.
fn arrow_positional_param_slots(
    kb: &mut KnowledgeBase,
    fn_type: &TypeExtractor,
    declared: Option<&[(Symbol, Value)]>,
) -> Option<Vec<(Symbol, Value)>> {
    match fn_type {
        // Arity ONE: the sole parameter's TYPE is the slot, and the arrow dropped
        // the binder name, so the position stands in for it. `declared` is `None`
        // here BY DESIGN — this is the one place the two readers diverge — so it
        // is deliberately not consulted.
        TypeExtractor::Arrow {
            param, arity: 1, ..
        } => Some(vec![(kb.intern(&positional_label(0)), param.clone())]),
        // Every other arity: the parameter list IS the slot list, which is exactly
        // what [`arrow_declared_param_list`] already read for the caller.
        TypeExtractor::Arrow { .. } => {
            let slots = declared.map(|d| d.to_vec());
            // A non-arity-1 `arrow` carries its list as a `named_tuple` at every
            // producer THAT KNOWS ITS PARAMETER TYPE — a NULLARY one carries the EMPTY
            // tuple, measured, so zero reaches this arm as `Some(vec![])` and its
            // applications ARE arity-checked. Anything else is a malformed arrow, and
            // returning `None` for it would SILENTLY DISABLE the whole argument check at
            // that call — precisely the WI-791 failure mode, where a hand-built arrow
            // missing a child left two tests green while covering nothing. Loud where it
            // can be: under test, the only place such a term exists.
            //
            // THE ONE PRODUCER THAT DOES NOT KNOW IT, and this assert used to claim it
            // away (WI-20260904-50B2K). An UN-ANNOTATED BINDER LIST mints its arrow with
            // `arity` = the WRITTEN binder count and `param` = whatever the type ladder
            // could supply, and rung 3 supplies a variable — `lambda_written_arity`'s own
            // comment says so in as many words ("`param_type` cannot supply it — an
            // unannotated lambda's is a fresh type var"). So the two comments
            // CONTRADICTED each other and this one was the wrong half: driven,
            // `let g = lambda (a, b) -> a  g((a: 1, b: 2))` aborted a debug build here,
            // and its ANNOTATED twin `lambda (a: Int64, b: Int64)` aborted identically —
            // per-binder annotations are read one level down, so the arrow's param is a
            // variable either way and the mint form is not what decides it.
            //
            // AN UNDETERMINED PARAM IS A WITHHOLDING, NOT A MALFORMED TERM, and `None` is
            // the same answer the rest of the typer gives for one: `validate_arg_against_
            // param`'s "everything above this line treats 'not ground' as 'not mine to
            // decide'". There is no parameter list to check against yet, and inventing
            // one would invent its LABELS — which WI-803 takes from the EXPECTED type,
            // never from the binder names. Making the arrow's param a real
            // `named_tuple` of per-component variables is the deeper repair (it would
            // also let one unification at a use site solve every component at once); it
            // is a change to what a binder-list lambda's param type IS, so it is
            // WI-20260904-34J8Z and not this assert.
            debug_assert!(
                slots.is_some() || arrow_param_is_undetermined(kb, fn_type),
                "WI-792: an `arrow` of arity != 1 must carry its parameter list as a \
                 `named_tuple`; a term reaching here without one is malformed and would \
                 silently skip the argument check (build it with `make_arrow_type` / \
                 `make_arrow_occ`)",
            );
            slots
        }
        _ => None,
    }
}

/// WI-20260904-50B2K — is an arrow's parameter type UNDETERMINED, so that no parameter
/// list can be read off it yet?
///
/// The one legitimate reason [`arrow_positional_param_slots`] finds no `named_tuple` at
/// arity != 1: a lambda's arity is its WRITTEN binder count and its param type comes from
/// a ladder whose bottom rung is a variable, so the two can disagree while the term is
/// perfectly well formed. Everything else reaching that arm without a list IS malformed.
///
/// BOTH UNDETERMINED FORMS, because rung 3 has minted each in turn: `TypeVar` is the
/// inert placeholder it minted before WI-20260904-50B2K and still mints for a type nobody
/// can name, `FlexVar` is the inference variable it mints now. `Skolem` is deliberately
/// NOT here — a rigidified parameter is DETERMINED (opaque, but decided), so an arrow
/// whose param is one and whose arity says "list" really is malformed.
fn arrow_param_is_undetermined(kb: &KnowledgeBase, fn_type: &TypeExtractor) -> bool {
    let TypeExtractor::Arrow { param, .. } = fn_type else {
        return false;
    };
    matches!(
        extract_type(kb, param),
        TypeExtractor::TypeVar(_) | TypeExtractor::FlexVar { .. }
    )
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

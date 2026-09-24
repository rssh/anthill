//! WI-578 — value-level type computation (`value_type_term`), `@[simp]` guards, and
//! `find_dictionary` / type-bound verdicts.

use super::*;

// ── WI-578 — value-level type computation (`value_type_term`) ─────────────────
//
// `value_type_term(value, env)` (`env` = `kb` + `subst`) computes a runtime value's
// type-term, SUPERSEDING `min_sort_of_value` (which returned `None` on exactly the
// constructed values that matter). It reads the value through `TermView` — ONE
// carrier-agnostic walk, so a constructor reached as `Value::Entity` or as a
// hash-consed `Value::Term` types identically. (The M3 per-instance `Value::ty`
// cache + its `typed` producer were built but never wired in, and were removed as
// dead code; the type is recomputed on demand or read from an occurrence's
// `inferred_type`.)

/// WI-578 — reconstruct a constructor's parent-sort type-param bindings from a
/// field-unified substitution. Recovers each type-param's short name and the logic
/// `Var` it indirects to, then reads that var out of `subst`. An unbound param rides
/// as a fresh `?_` type-var (WI-384 — keep the sort's full param arity, never drop).
/// Extracted from [`check_constructor_iter`] so the value-level typer reuses this from
/// ONE source; the WI-516 occurrence-lowering is load-bearing — see the inline note.
///
/// WI-954 — THE ALIAS WALK IS GONE, and with it a two-source (index-or-scan) shape.
/// This used to recover the parameter set by decoding `SortAlias` FACTS: an O(1)
/// `SortAliasIndex.by_parent` read once `build_sort_alias_index` had run, and a live
/// scan of every `SortAlias` fact in the load-time window before it had — two data
/// sources whose disagreement was WI-955's subject, joined by a shared decoding rule
/// so they could not drift again. The declaration is now published directly, so there
/// is one source, no pre-index window, and no rule to share: the parameters come from
/// the owner and their variables from the map.
///
/// AND THE INDEX HALF WAS SILENTLY WRONG ACROSS LOAD PHASES. `by_parent`'s read had no
/// fallback-on-miss — the same hazard `resolve_sort_alias` documents for `by_sym`,
/// which `load_phase_inner` resets the index at every phase START to avoid — but a
/// caller running AFTER a phase completes reads whatever that phase's type-check built.
/// MEASURED on `wi946_belongs_to_readers_test`'s stdlib-then-source KB: the index held
/// 102 entries and the source's own `Crate.T` was not among them, so
/// `reconstruct_sort_params(Crate)` answered "no parameters" and `Boxed(5)` typed as a
/// bare `Ref(Crate)` instead of `Crate[T = Int64]`. That test recorded the bare answer
/// as a measurement with an instruction to revisit it if it ever changed; it changed
/// here, and the two spellings it compares still agree.
///
/// NOT [`sort_type_params_as_pairs`], which answers the same set: it is MEMOIZED with
/// no invalidator, and this runs in the load-time value-typing window where a
/// half-loaded sort's parameter list would poison every type-check-time reader. It also
/// keys by the QUALIFIED parameter symbol, where the type built here needs the BARE one
/// (`make_parameterized_type`'s named-arg key convention, WI-708/WI-726).
pub(super) fn reconstruct_sort_params(
    kb: &mut KnowledgeBase,
    parent_sym: Symbol,
    subst: &Substitution,
) -> Vec<(Symbol, TermId)> {
    // Collected under the shared borrow, then interned: `kb.intern` needs `&mut kb`.
    let declared: Vec<(String, VarId)> = kb
        .type_param_syms_of(parent_sym)
        .iter()
        .filter_map(
            |&p| match kb.get_term(published_param_var(kb, parent_sym, p)?) {
                Term::Var(Var::Global(v)) => Some((kb.local_name_of(p).to_string(), *v)),
                _ => None,
            },
        )
        .collect();
    let params: Vec<(Symbol, VarId)> = declared
        .into_iter()
        .map(|(short, vid)| (kb.intern(&short), vid))
        .collect();
    let mut param_bindings: Vec<(Symbol, TermId)> = Vec::with_capacity(params.len());
    for (param_sym, vid) in params {
        // WI-384: an unbound param becomes a `type_var` WILDCARD (not a bare logic
        // `Var`) so the built type keeps the sort's full param arity while staying
        // compatible with whatever the use-site declares. WI-516: a `Value::Node`-carried
        // binding is lowered to a Term so the reconstructed type KEEPS it rather than
        // dropping it.
        let bound_type = match subst.resolve_as_value(vid) {
            Some(Value::Term { id: bound_type, .. }) => *bound_type,
            Some(other) => {
                let other = other.clone();
                match value_to_term(kb, &other) {
                    Ok(t) => t,
                    Err(e) => {
                        debug_assert!(
                            false,
                            "WI-516: param `{}` bound to un-lowerable carrier {}: {e:?}",
                            kb.local_name_of(param_sym),
                            other.type_name(),
                        );
                        let name = kb.intern("?_");
                        kb.make_type_var(name)
                    }
                }
            }
            None => {
                let name = kb.intern("?_");
                kb.make_type_var(name)
            }
        };
        param_bindings.push((param_sym, bound_type));
    }
    param_bindings
}

/// WI-20260826-JSFHG — does this expected type's HEAD name a constructor (an entity),
/// rather than a sort? The one question [`check_constructor_iter`] asks of its checking
/// direction before deciding which symbol to classify the application at.
///
/// Reads the head form-agnostically ([`type_head`]) so a bare `Colour.red` and a
/// parameterized `Option.some[T = Int64]` answer alike, and asks
/// [`KnowledgeBase::strict_parent_sort`] — the STRICT one, so an eponymous entity
/// (`sort Box { entity Box(..) }`), whose classification is already its own symbol, is
/// not an entity for this purpose and takes the unchanged path.
pub(super) fn type_head_names_an_entity<V: TermView>(kb: &KnowledgeBase, ty: &V) -> bool {
    let head = match type_head(kb, ty) {
        TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => s,
        _ => return false,
    };
    kb.strict_parent_sort(head).is_some()
}

/// WI-20260826-JSFHG — does a constructor name appear ANYWHERE in this type, at the head or
/// nested inside a binding (`List[T = Colour.red]`)?
///
/// THE STRUCTURAL SIBLING of [`type_head_names_an_entity`], and the two have genuinely
/// different owners in the same way [`type_head_is_callable`] and
/// [`type_contains_callable`] do. The head question is the CLASSIFICATION's: what a
/// constructor application is classified at is decided by the head of the type asked for,
/// and nothing deeper. This one is the AGGREGATE-LITERAL hint's: `[red(v: 1)]` in a
/// `List[T = Colour.red]` slot carries its variant one level down, so a head test would
/// withhold the hint from exactly the shape it exists for.
///
/// Conservative on a carrier it cannot walk — a `Value::Node` (an arrow, a denoted) answers
/// by its head alone. Withholding a hint there costs nothing: a hint is an inference aid,
/// and a slot the walk cannot read is not a variant slot.
pub(super) fn type_mentions_an_entity(kb: &KnowledgeBase, v: &Value) -> bool {
    if type_head_names_an_entity(kb, v) {
        return true;
    }
    match v {
        Value::Term { id, .. } => term_mentions_an_entity(kb, *id),
        _ => false,
    }
}

/// [`type_mentions_an_entity`] over a hash-consed type term — this node's head, else any
/// argument's. The same spine [`term_contains_callable`] walks, for the same reason.
fn term_mentions_an_entity(kb: &KnowledgeBase, tid: TermId) -> bool {
    term_any_subterm(kb, tid, &|t, _| {
        type_head_names_an_entity(kb, &TermIdView(t))
    })
}

/// WI-20260826-JSFHG — the hint one COMPONENT of a tuple literal takes from the tuple's own
/// expected type, looked up by LABEL.
///
/// The named-tuple peer of the `element_hint` a `[…]` push derives from `expected`'s `T`:
/// a tuple literal carries no constructor of its own, so its components' declared types are
/// the expected tuple's fields and nothing else names them. Positional components are
/// matched through [`crate::intern::positional_label`], the `_N` convention's owner, rather
/// than by index — the expected tuple's field list is positional-then-named, so an index
/// would silently pair a positional component with a named field once both are present.
///
/// GATED ON THE COMPONENT TYPE MENTIONING A CONSTRUCTOR, which keeps this hint's population
/// the empty one every other part of this ticket rests on: a tuple type whose components
/// are ordinary sorts pushes nothing and its components type exactly as they did.
pub(super) fn tuple_component_expected(
    kb: &KnowledgeBase,
    expected: &Option<Value>,
    label: &str,
) -> Option<Value> {
    let exp = expected.as_ref()?;
    let ty = named_tuple_fields(kb, exp)
        .into_iter()
        .find(|(s, _)| kb.local_name_of(*s) == label)
        .map(|(_, t)| t)?;
    type_mentions_an_entity(kb, &ty).then_some(ty)
}

/// WI-20260826-JSFHG — is this argument a TUPLE literal, whose components the checking
/// direction reaches one level DOWN rather than at the head?
///
/// Its surface form is an `Expr::Constructor{TupleLiteral}` (the WI-462 shape), which
/// [`arg_is_constructor_application`] also answers `true` for — so this MUST be asked first,
/// or the tuple is judged by its own head (a `named_tuple`, never an entity) and takes no
/// hint at all.
///
/// LIST AND SET LITERALS HAVE THEIR OWN PREDICATE BESIDE THIS ONE
/// ([`seq_literal_kind`], consumed by [`seq_slot_arg_hint`]), and the split is worth
/// keeping rather than merging: they are
/// not tuples, and JSFHG had to EXCLUDE them for a reason that has since been repaired.
/// A first cut of that ticket included them here and `takeReds([blue(v: 1)])` against a
/// `List[T = Colour.red]` slot LOADED CLEAN, because a hinted literal took `element_hint`
/// as its element type unconditionally and never consulted what the elements typed as —
/// so the hint did not check the literal, it OVERWROTE it. WI-20260826-7JDWY closed that
/// hole ([`seq_literal_element_type`]) and the arm is restored.
///
/// The tuple path never had the hole — measured on the same shape,
/// `takePair((a: blue(v: 1), b: 2))` was refused `expected (a: red, …), got (a: blue, …)`
/// throughout.
pub(super) fn arg_is_tuple_literal(kb: &KnowledgeBase, arg: &Rc<NodeOccurrence>) -> bool {
    matches!(
        &arg.kind,
        NodeKind::Expr {
            expr: Expr::Constructor { name, .. },
            ..
        } if kb.qualified_name_of(*name) == dt::qualified(dt::TUPLE_LITERAL)
    ) || matches!(
        &arg.kind,
        NodeKind::Expr {
            expr: Expr::TupleLit { .. },
            ..
        }
    )
}

/// WI-20260826-7JDWY — is this argument a LIST or SET literal, whose ELEMENTS the checking
/// direction reaches one level down?
///
/// BOTH CARRIERS, for the reason [`seq_literal_element_type`] records: a source `[…]` in an
/// argument arrives as an `Expr::Constructor{ListLiteral}` (the un-lowered form — the
/// loader only lowers to a `cons`/`nil` spine in a rule / fact data slot whose declaration
/// names a `List`), while the `Expr::ListLit` shape comes from the term→occurrence build.
/// A predicate that knew only one of them would push the hint on one spelling of the same
/// program.
///
/// IT IS ASKED AFTER [`arg_is_constructor_application`], not before, and that is safe
/// rather than intended: `variant_slot_arg_hint` runs first in every chain and its
/// constructor arm answers `true` for the `ListLiteral` form — but it then asks
/// [`type_head_names_an_entity`] of a `List[T = …]` head, which names a sort, so it
/// declines and control reaches here. An earlier version of this note claimed the opposite
/// ordering; `/code-review` read the chains and found it false. It matters because
/// reordering `seq_slot_arg_hint` ABOVE `variant_slot_arg_hint` is what a reader would do
/// on the strength of the old claim — harmless today, and not a thing to rely on.
fn seq_literal_kind(kb: &KnowledgeBase, arg: &Rc<NodeOccurrence>) -> Option<SeqLiteral> {
    match &arg.kind {
        NodeKind::Expr {
            expr: Expr::Constructor { name, .. },
            ..
        } => {
            let qn = kb.qualified_name_of(*name);
            if qn == dt::qualified(dt::LIST_LITERAL) {
                Some(SeqLiteral::List)
            } else if qn == dt::qualified(dt::SET_LITERAL) {
                Some(SeqLiteral::Set)
            } else {
                None
            }
        }
        NodeKind::Expr {
            expr: Expr::ListLit(_),
            ..
        } => Some(SeqLiteral::List),
        NodeKind::Expr {
            expr: Expr::SetLit(_),
            ..
        } => Some(SeqLiteral::Set),
        _ => None,
    }
}

/// WI-20260826-JSFHG / WI-20260828-5NSZY — the hint a slot declared `List[T = X]` /
/// `Set[T = X]` pushes down to a LITERAL argument, so the literal's elements are typed
/// against `X` (`seq_element_expected` in [`visit_type`]) and then CHECKED against it
/// ([`seq_literal_element_type`]).
///
/// **SPLIT OUT OF [`variant_slot_arg_hint`]**, which is about §8.2's classification and had
/// been carrying this because the variant case was the first that needed it. The two ask
/// different questions of different types — that one whether the SLOT mentions an entity,
/// this one what the ELEMENT is — and a reader looking for "why does my list literal get an
/// expected type" was reading a function named for variants.
///
/// **THE GATE IS ON THE DECLARED ELEMENT, and admits two shapes**, each with its own item
/// and its own rows:
///
///  - it MENTIONS AN ENTITY (WI-20260826-JSFHG, restored by WI-20260826-7JDWY once the
///    elements were checked rather than overwritten): `takeReds([red(v: 1)])` against
///    `List[T = Colour.red]` drives, and `takeReds([blue(v: 1)])` is refused naming `blue`.
///  - it is CALLABLE BY HEAD (WI-20260828-5NSZY): `head_apply([inc], 41)` against
///    `List[T = Function[A = Int64, B = Int64]]` was REFUSED where its desugared twin
///    `head_apply(cons(inc, nil()), 41)` returned 42 — one program, two verdicts by
///    spelling. A bare operation name needs an arrow to lift against, and this is the only
///    thing that carries one into a literal. [`type_head_is_callable`] is
///    [`arrow_slot_arg_hint`]'s own predicate, borrowed so "is this slot callable" has one
///    answer wherever it is asked.
///
/// 5NSZY WITHHELD THE SECOND deliberately, and said why: a hinted literal took its element
/// type from the hint without reading the elements, so pushing one would have traded a
/// correct refusal for a silent accept. WI-20260826-7JDWY removed that, which is what makes
/// this admissible now rather than a re-litigation of a settled decision.
///
/// THE ELEMENT IS READ THROUGH [`declared_element_type`], so the slot's collection must
/// match the literal's own surface: a `[…]` in a `Set[T = X]` slot is a shape disagreement
/// and gets nothing, which is the rule the check itself follows.
pub(super) fn seq_slot_arg_hint(
    kb: &KnowledgeBase,
    arg: &Rc<NodeOccurrence>,
    param_type: Option<&Value>,
) -> Option<Value> {
    let pt = param_type?;
    let kind = seq_literal_kind(kb, arg)?;
    let element = declared_element_type(kb, kind, Some(pt))?;
    (type_mentions_an_entity(kb, &element) || type_head_is_callable(kb, &element))
        .then(|| pt.clone())
}

/// WI-578 — the shared build-finish tail of constructor typing. Given the field-
/// unified `subst` (its bindings pinned the parent sort's type-params), produce the
/// constructor's result type-term: the bare `Ref(Sort)` when no param survives (an
/// empty `subst`, a free-standing entity with no parent sort, or a non-`Fn` parent),
/// else `Sort[params]` via [`reconstruct_sort_params`] +
/// [`KnowledgeBase::make_parameterized_type`]. [`check_constructor_iter`] (wrapping the
/// result in a `TypeResult`) and [`constructor_value_type`] BOTH call this so the
/// occurrence-typer and the value-typer build the SAME type from ONE source — a
/// second, drifting notion of type is exactly what the typed-value substrate must
/// avoid (`docs/design/constrained-term-substrate.md`).
///
/// WI-20260826-JSFHG — `classify_sym` is the symbol the result type is HEADED at, and it
/// is the caller's decision rather than this function's: the value-typer, which has no
/// checking direction to read, always passes the parent (`parent_sort.unwrap_or(ctor)`),
/// while [`check_constructor_iter`] passes the CONSTRUCTOR when its `expected` names one
/// (§8.2). `parent_sort` stays a separate argument because the PARAMS are always the
/// parent's — a constructor declares none of its own — so `Option.some[T = Int64]` is
/// this function building `some` over `Option`'s reconstructed `T`.
///
/// THE TWO TYPERS STILL BUILD FROM ONE SOURCE. They differ only where the occurrence
/// typer has a hint the value typer structurally cannot have, which is the pre-existing
/// shape of the WI-384 expected-seed below — not a second notion of what a constructor's
/// type IS.
pub(super) fn finish_constructor_type(
    kb: &mut KnowledgeBase,
    classify_sym: Symbol,
    parent_sort: Option<Symbol>,
    subst: &Substitution,
) -> Value {
    let classify_type = kb.make_sort_ref(classify_sym);
    if subst.bindings.is_empty() {
        return Value::term(classify_type);
    }
    // A symbol with no registered sort at all has nothing to walk; its own symbol
    // is the type, so the simple `classify_type` sort_ref stands (which for this arm IS
    // the constructor's own symbol — WI-20260826-JSFHG renamed the variable that used to
    // be spelled `parent_type` here). WI-946: this arm
    // used to catch the free-standing / eponymous entity too, on the reasoning
    // that it has "no type params to discover" — false for an eponymous
    // PARAMETRIC sort (`sort Box { sort T = ?; entity Box(v: T) }`), whose params
    // are declared on the very symbol the entity shares. Both callers now pass
    // the TOTAL belongs-to, so that shape walks its own params here.
    let Some(parent_sym) = parent_sort else {
        return Value::term(classify_type);
    };
    let param_bindings = reconstruct_sort_params(kb, parent_sym, subst);
    if param_bindings.is_empty() {
        Value::term(classify_type)
    } else {
        Value::term(kb.make_parameterized_type(classify_type, &param_bindings))
    }
}

/// WI-578 — a fresh `?_` type-variable wildcard: the TOTAL fallback for an
/// under-determined type (an unbound var with no recorded bound, an opaque carrier).
/// Sound — a `type_var` reads as compatible-with-anything in the unify/subtype
/// dispatch, so an imprecise type never wrong-FIRES a guard (the M6 flounder posture).
fn fresh_type_var(kb: &mut KnowledgeBase) -> Value {
    let name = kb.intern("?_");
    Value::term(kb.make_type_var(name))
}

/// WI-578 — the prelude sort a literal constant inhabits, as a `Ref(S)` type-term.
pub(super) fn literal_sort(kb: &mut KnowledgeBase, lit: &Literal) -> Value {
    let name = match lit {
        Literal::Int(_) => "Int64",
        Literal::BigInt(_) => "BigInt",
        Literal::Float(_) => "Float",
        Literal::Bool(_) => "Bool",
        Literal::String(_) => "String",
    };
    Value::term(kb.make_sort_ref_by_name(name))
}

/// WI-611 — the result type of a SELF-RETURNING spec op applied over a CONCRETE
/// receiver carrier. A container spec op whose declared return IS its enclosing
/// (self) sort — `insert(s: Set, x: T) -> Set`, `put(m: Map, …) -> Map`,
/// `union(a: Set, b: Set) -> Set` — produces a carrier of the SAME concrete sort
/// as its self-receiver argument: `insert(intBag, x)` is an `IntBag`, not the
/// abstract `Set`. [`constructor_value_type`] would otherwise read the operation
/// head as a bare `Ref(insert)` (an op has no entity fields), so a nested `@[simp]`
/// guard on the enclosing law — `member(?x, insert(?s, ?x)) <=> true`, whose
/// carrier argument is this `insert(…)` subterm — sees a non-provider head and
/// SUSPENDS (`sort_provides(Set, Set)` is not reflexive; the WI-596 nested gap).
/// Refining the subterm to the receiver's concrete carrier lets
/// `sort_provides(IntBag, Set)` hold and the nested law fire, WITHOUT changing the
/// `insert` functor (so the law's inner pattern still matches — the catch-22 the
/// override route could not escape). cf WI-350 (carrier-aware dispatch), WI-461
/// (bare self-receiver identity body).
///
/// `None` (keep the structural default) unless ALL hold: `op_sym` is a body-less
/// spec op (the dispatch notion the guard uses — [`lookup_spec_op_dispatch`]); its
/// declared return's sort head IS the spec sort itself (self-returning —
/// `member -> Bool` is NOT, so an outer `member` subterm keeps typing as `Bool`);
/// it has a self-receiver parameter ([`self_receiver_param_index`]); and that
/// argument's already-computed type is a CONCRETE provider of the spec (distinct
/// from the abstract spec sort, which keeps the declared self return — there is no
/// sharper carrier to name). The refined type is the receiver argument's OWN type:
/// the result carrier IS the receiver carrier.
fn self_return_spec_op_result_type(
    kb: &KnowledgeBase,
    op_sym: Symbol,
    pos_child_types: &[Value],
) -> Option<Value> {
    let spec_sort = lookup_spec_op_dispatch(kb, op_sym)?;
    let rec = crate::kb::op_info::lookup_operation_info(kb, op_sym)?;
    // Self-returning: the declared return's sort head is the enclosing spec sort.
    let ret_head = sort_functor_of_view(kb, &rec.return_type)?;
    if kb.canonical_sort_sym(ret_head) != kb.canonical_sort_sym(spec_sort) {
        return None;
    }
    // The self-receiver argument carries the result's carrier.
    let idx = self_receiver_param_index(kb, &rec.params, spec_sort)?;
    let recv_ty = pos_child_types.get(idx)?;
    let carrier = carrier_sort_of_value(kb, recv_ty)?;
    // Refine only for a CONCRETE provider — an abstract receiver (`carrier` is the
    // spec sort itself) keeps the declared self return, and a non-provider is never
    // refined to a sort it does not satisfy (never fabricate a providing head).
    if kb.canonical_sort_sym(carrier) == kb.canonical_sort_sym(spec_sort)
        || !sort_provides(kb, carrier, spec_sort)
    {
        return None;
    }
    Some(recv_ty.clone())
}

/// WI-578 — the result type-term of a constructor application, given its children's
/// already-computed types. The value-level analog of [`check_constructor_iter`]'s
/// build core MINUS the error-producing field VALIDATION (`value_type_term` is
/// TOTAL): look up
/// the constructor's parent sort + declared field types, unify each child type
/// against its field's declared type into a fresh substitution (pinning the sort's
/// type-params), then [`reconstruct_sort_params`] + build `Sort[params]` (or the bare
/// `Ref(Sort)`). An unregistered constructor / free-standing entity yields its own
/// bare sort ref. Never `None`.
fn constructor_value_type(
    kb: &mut KnowledgeBase,
    ctor_sym: Symbol,
    pos_child_types: &[Value],
    named_child_types: &[(Symbol, Value)],
) -> Value {
    // WI-578 — mirror check_constructor_iter's seq/tuple-literal special-casing (the
    // typer-side check_tuple_literal_constructor / check_seq_literal_constructor): an
    // un-desugared `(...)` / `[...]` / `{...}` is loaded as a TupleLiteral / ListLiteral
    // / SetLiteral entity whose DECLARED type has no element field, so the field-driven
    // path below mistypes it as `Ref(TupleLiteral)` / `Ref(ListLiteral)` instead of
    // `Unit` / a named tuple / `List[T]` / `Set[T]`. Route to the aggregate / sequence
    // type so the value-typer and the occurrence-typer agree (no drift — the whole
    // point of the typed-value substrate).
    if kb.qualified_name_of(ctor_sym) == dt::qualified(dt::TUPLE_LITERAL) {
        return tuple_value_type(kb, pos_child_types.to_vec(), named_child_types.to_vec());
    }
    if kb.qualified_name_of(ctor_sym) == dt::qualified(dt::LIST_LITERAL) {
        return seq_literal_value_type(kb, SeqLiteral::List, pos_child_types);
    }
    if kb.qualified_name_of(ctor_sym) == dt::qualified(dt::SET_LITERAL) {
        return seq_literal_value_type(kb, SeqLiteral::Set, pos_child_types);
    }

    // WI-946: the TOTAL belongs-to — the value-typer twin of the same collapse
    // `check_constructor` makes, so the two keep producing one type from one
    // source (the WI-578 no-drift tie `finish_constructor_type` exists for).
    let parent_sort = kb.sort_of_constructor(ctor_sym);
    let parent_type = kb.make_sort_ref(parent_sort.unwrap_or(ctor_sym));
    let field_types = match kb.entity_field_types(ctor_sym) {
        Some(ft) => ft.to_vec(),
        // Not a registered constructor. WI-611: it may be a self-returning spec op
        // (`insert`/`put`/`union`), which types as its concrete receiver carrier so
        // a nested `@[simp]` law's carrier argument reads a provider and can fire.
        // Gated here (the non-constructor branch) so the common constructor path
        // never pays the operation-info scan. Otherwise the value's type is its own
        // bare sort.
        None => {
            if let Some(refined) = self_return_spec_op_result_type(kb, ctor_sym, pos_child_types) {
                return refined;
            }
            return Value::term(parent_type);
        }
    };
    let mut subst = Substitution::new();
    // Field-unify (named by field name, then positional by index) — pins the parent
    // sort's type-params from the children (the check_constructor_iter WI-384 order).
    for (field_sym, declared_type) in &field_types {
        if let Some((_, child_ty)) = named_child_types.iter().find(|(s, _)| s == field_sym) {
            unify_types(kb, &mut subst, child_ty, declared_type);
        }
    }
    for (i, child_ty) in pos_child_types.iter().enumerate() {
        if let Some((_, declared_type)) = field_types.get(i) {
            unify_types(kb, &mut subst, child_ty, declared_type);
        }
    }
    finish_constructor_type(kb, parent_sort.unwrap_or(ctor_sym), parent_sort, &subst)
}

/// WI-578 — the type-term of an anonymous aggregate (a tuple / `Unit`) from its
/// children's types: `Unit` for the empty case, else a `named_tuple` with positional
/// components under the `_1.._n` convention (WI-442) plus any named components. The
/// synthetic span is unused unless a child type is a `Value::Node` (denoted-poisoned),
/// which a runtime tuple's ground component types are not.
fn tuple_value_type(
    kb: &mut KnowledgeBase,
    pos_types: Vec<Value>,
    named_types: Vec<(Symbol, Value)>,
) -> Value {
    if pos_types.is_empty() && named_types.is_empty() {
        return Value::term(kb.make_sort_ref_by_name("Unit"));
    }
    let mut fields: Vec<(Symbol, Value)> = Vec::with_capacity(pos_types.len() + named_types.len());
    for (i, cty) in pos_types.into_iter().enumerate() {
        let name = kb.intern(&positional_label(i));
        fields.push((name, cty));
    }
    for (k, cty) in named_types {
        fields.push((k, cty));
    }
    let span = crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);
    named_tuple_value(kb, &fields, span, None)
}

/// WI-578 — the value-level analog of [`check_seq_literal_constructor`]: type an
/// un-desugared `[...]` / `{...}` (a `ListLiteral` / `SetLiteral` entity, which has no
/// element field) as `base[T = elem]`. The value path has no checking-direction
/// `expected`, so it reads the elements only. [`parameterized_value`] carries a
/// `Value::Node` element type (a denoted-poisoned element) losslessly.
///
/// WI-20260829-WBXGX — THE ELEMENTS ARE JOINED, not read off the first one. This is the
/// no-declaration arm of [`seq_literal_element_type`] on the value carrier, and it had
/// been left behind: a runtime `ListLiteral(1, "a")` answered `List[T = Int64]`, a
/// `String` inside a type that says `Int64` — the very defect the ticket closed on the
/// other three carriers, in the one place a value can be inspected at runtime. Found by
/// `/code-review`, which read the "one owner" claim beside this function and checked it.
///
/// A CLASH FLOUNDERS TO `?_` RATHER THAN ERRORING, and that is the difference from the
/// occurrence path rather than an oversight: a runtime value EXISTS, so there is no
/// program to refuse — the honest answer to "what type is this heterogeneous list" is that
/// it is under-determined. That is the M6 / WI-067 convention the typer already follows
/// for a cyclic or over-deep value ([`TYPE_DEPTH_CAP`]): under-determined suspends, never
/// crashes. An empty literal floundered here already, for the same reason.
pub(super) fn seq_literal_value_type(
    kb: &mut KnowledgeBase,
    kind: SeqLiteral,
    pos_child_types: &[Value],
) -> Value {
    let mut joined: Option<Value> = None;
    for cty in pos_child_types {
        joined = match joined {
            None => Some(cty.clone()),
            Some(acc) => combine_element_types(kb, &acc, cty),
        };
        if joined.is_none() {
            break;
        }
    }
    let t_val = joined.unwrap_or_else(|| fresh_type_var(kb));
    // WI-20260826-7JDWY: through [`seq_literal_type`], the one owner of "which symbol is a
    // literal typed at" — this site open-coded the same three calls behind the same
    // `base_name: &str` the [`SeqLiteral`] enum was introduced to remove, so it was the
    // fourth carrier the "one owner" claim had omitted (found by `/code-review`). A
    // synthetic span, as before: a runtime value has no source position.
    let span = crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);
    seq_literal_type(kb, kind, t_val, span, None)
}

/// WI-578 — the type-term of a value-level logic variable. Navigates its σ-binding
/// (M6 "binding is navigation"): a bound var derefs to its value and types THAT; an
/// unbound var reads its declared bound from the constraint store (Step-1), else a
/// fresh `?_`. The deref is a CYCLE-GUARDED loop — the SLD bind path is not
/// occurs-checked, so σ can carry a cyclic var spine; on a revisit we flounder (`?_`)
/// rather than loop (M6 / WI-067: an under-determined type suspends, never crashes).
/// WI-578 — depth bound for the [`value_type_term`] structural recursion.
/// A runtime value can be DEEP (a long `cons` list) or CYCLIC (`?x := cons(1, ?x)` —
/// the SLD bind path is not occurs-checked), either of which would otherwise recurse
/// unboundedly on the Rust stack. At the cap we flounder to a `?_` type-var (M6 /
/// WI-067: under-determined suspends, never crashes) — SOUND, and for the dominant
/// deep case (a homogeneous list) LOSSLESS, because each `cons`'s own head re-pins the
/// element type at every level, so the bound only ever truncates the *innermost*
/// subterm's type. (An unbounded-precision iterative walk, like the typer's worklist,
/// is the follow-up; the cap is the crash-safety floor.)
const TYPE_DEPTH_CAP: usize = 512;

fn var_type_term(kb: &mut KnowledgeBase, subst: &Substitution, vid: VarId, depth: usize) -> Value {
    let mut cur = vid;
    let mut seen: std::collections::HashSet<VarId> = std::collections::HashSet::new();
    // The resolved chain in visit order — `seen` cycle-guards; `chain` gives the
    // WI-595 refinement below a DETERMINISTIC constraint order (a `HashSet`
    // iteration order would make a multi-constraint refine vary run-to-run).
    let mut chain: Vec<VarId> = Vec::new();
    loop {
        if !seen.insert(cur) {
            return fresh_type_var(kb);
        }
        chain.push(cur);
        let bound = match subst.resolve_as_value(cur) {
            Some(b) => b.clone(),
            None => {
                // Unbound: its declared bound from the constraint store. A `Type`
                // constraint payload may be a reified GUARD (`subsort(typeof(?x), T)`)
                // or any carrier, not a clean sort/type — so return only the first that
                // is a real type-term (has a sort head), else `?_`. This both honors the
                // "least DECLARED sort" contract (like the superseded `store_sort_bound`)
                // AND keeps `value_type_term`'s output a `Term`/`Node` type-term (a raw
                // guard / non-type carrier would trip `named_tuple_value`'s `expect_term`).
                let constraints = subst.type_constraints_of(cur);
                for c in constraints {
                    if sort_functor_of_view(kb, &c).is_some() {
                        return c;
                    }
                }
                return fresh_type_var(kb);
            }
        };
        // CARRIER-AGNOSTIC var detection (WI-578 fix): a var→var binding is carried as
        // `Value::Term { Term::Var }` (the dominant resolver carrier), `Value::Node`, or
        // `Value::Var` — read it through `index_var` so the cycle-guarded LOOP follows
        // the whole spine. Matching only `Value::Var` would defeat the guard (the spine
        // would re-enter via the structural recursion with a FRESH `seen`).
        if let Some(Var::Global(next)) = bound.index_var(kb) {
            cur = next;
            continue;
        }
        // The bound value's OWN type is authoritative (M3: binding reads the
        // value's carrier). WI-595: SHARPEN an under-determined value type with the
        // carrier var's declared store bound — `?x: List[Int64]` bound to `nil`
        // reads `List[?]` from the value, and meeting the `List[Int64]` bound
        // recovers the element type. The refine is PINNED to the value's own sort
        // head: a meet is applied ONLY when it keeps `value_ty`'s head (sharpening
        // type-params), NEVER when it would CHANGE the head. A subsort bound
        // (`List` → `NonEmptyList`) must not move the head — `meet_types` returns the
        // subsort there, and firing on that head would run a law valid only for the
        // subsort against a value the head says it is not (the binding's conformance
        // is the bind-time check's job, not the type read's). A headless value stays
        // headless (suspend is sound — never fabricate a head from an unverified
        // bound). The head check also drops an incomparable bound (it meets to
        // `nothing`, a different head). Chain in visit order for determinism.
        // (never NAF-decide; WI-067).
        let mut value_ty = value_type_term_d(kb, subst, &bound, depth);
        let value_head = sort_functor_of_view(kb, &value_ty);
        if value_head.is_some() {
            for &v in &chain {
                for c in subst.type_constraints_of(v) {
                    if sort_functor_of_view(kb, &c).is_none() {
                        continue;
                    }
                    let refined = meet_types(kb, value_ty.clone(), c);
                    // WI-769: head equality CANONICALLY — the parameterized
                    // meet constructs on the canonical base Symbol, so a raw
                    // `==` against a twin-copy value head (WI-617) would read
                    // the SAME sort as a changed head and silently skip the
                    // sharpen. A genuinely different sort still refuses.
                    let same_head = match (sort_functor_of_view(kb, &refined), value_head) {
                        (Some(r), Some(v)) => same_sort_canonical(kb, r, v),
                        _ => false,
                    };
                    if same_head {
                        value_ty = refined;
                    }
                }
            }
        }
        return value_ty;
    }
}

/// WI-578 — the positional children's type-terms. Each child is materialized to an
/// owned `Value` ([`ViewItem::to_value`]) so the short `&kb` read-borrow drops before
/// the `&mut kb` recursion — the carrier-agnostic walk pattern.
pub(super) fn child_types_pos(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    v: &Value,
    pos_arity: usize,
    depth: usize,
) -> Vec<Value> {
    let mut out = Vec::with_capacity(pos_arity);
    for i in 0..pos_arity {
        // Materialize first (drops the `&kb` read-borrow) so the recursion can take
        // `&mut kb`. `pos_arity` (from `head`) and `pos_arg(i)` are two reads of the
        // same value that MUST agree; a `None` at `i < pos_arity` is a carrier
        // inconsistency — surface it loudly and keep a `?_` PLACEHOLDER so the result
        // stays index-aligned with `field_types` (a silent drop-and-shift would bind
        // every later child to the WRONG declared field — the "loud over silent" rule).
        let child: Option<Value> = v.pos_arg(kb, i).map(|item| item.to_value());
        match child {
            Some(c) => out.push(value_type_term_d(kb, subst, &c, depth)),
            None => {
                debug_assert!(
                    false,
                    "value_type_term: pos_arity {pos_arity} but pos_arg({i}) is None"
                );
                out.push(fresh_type_var(kb));
            }
        }
    }
    out
}

/// WI-578 — the named children's `(key, type-term)`s; see [`child_types_pos`]. A
/// missing key (vs `named_keys`) is index-safe here (matched by symbol downstream),
/// but still kept as a loud `?_` placeholder rather than silently dropped.
fn child_types_named(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    v: &Value,
    depth: usize,
) -> Vec<(Symbol, Value)> {
    let keys = v.named_keys(kb);
    let mut out = Vec::with_capacity(keys.len());
    for k in keys {
        let child: Option<Value> = v.named_arg(kb, k).map(|item| item.to_value());
        match child {
            Some(c) => out.push((k, value_type_term_d(kb, subst, &c, depth))),
            None => {
                debug_assert!(
                    false,
                    "value_type_term: named_keys lists a key with no named_arg"
                );
                out.push((k, fresh_type_var(kb)));
            }
        }
    }
    out
}

/// WI-578 — the type-term of a runtime [`Value`], computed at the boundary. TOTAL and
/// CARRIER-AGNOSTIC: it reads the value through [`TermView`] (`head`/`pos_arg`), so a
/// constructor reached as a `Value::Entity` or as a hash-consed `Value::Term` types
/// identically (the one read path — WI-342/348). An under-determined part rides as a
/// `?_` type-var, never `None` — the totality that SUPERSEDES `min_sort_of_value`.
/// Returns the type as a `Value` type-term (the shape an occurrence's
/// `inferred_type` holds: `Ref(S)` / `Fn{S, named}` / denoted).
pub fn value_type_term(kb: &mut KnowledgeBase, subst: &Substitution, v: &Value) -> Value {
    value_type_term_d(kb, subst, v, 0)
}

fn value_type_term_d(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    v: &Value,
    depth: usize,
) -> Value {
    // A typed source occurrence carries its type in `inferred_type`; honor it before
    // a structural recompute.
    if let Value::Node(occ) = v {
        if let Some(t) = occ.inferred_type() {
            return t;
        }
    }
    // Bound the structural recursion (deep / cyclic values) — see TYPE_DEPTH_CAP.
    if depth >= TYPE_DEPTH_CAP {
        return fresh_type_var(kb);
    }
    match v.head(kb) {
        ViewHead::Const(lit) => literal_sort(kb, &lit),
        ViewHead::Var(Var::Global(vid)) => var_type_term(kb, subst, vid, depth),
        // A De Bruijn / Rigid var has no runtime σ-binding to read here.
        ViewHead::Var(_) => fresh_type_var(kb),
        // A bare 0-ary constructor (`nil`) reaches the `Functor` arm below at arity
        // 0 since WI-20260902-CZJ2N, where `constructor_value_type(kb, c, &[], &[])`
        // is exactly what its own arm computed.
        ViewHead::Functor {
            functor: Some(functor),
            pos_arity,
            ..
        } => {
            let pos_types = child_types_pos(kb, subst, v, pos_arity, depth + 1);
            let named_types = child_types_named(kb, subst, v, depth + 1);
            constructor_value_type(kb, functor, &pos_types, &named_types)
        }
        // An anonymous aggregate: `Unit` (0-ary) or a tuple → named_tuple type.
        ViewHead::Functor {
            functor: None,
            pos_arity,
            ..
        } => {
            let pos_types = child_types_pos(kb, subst, v, pos_arity, depth + 1);
            let named_types = child_types_named(kb, subst, v, depth + 1);
            tuple_value_type(kb, pos_types, named_types)
        }
        // Bare identifier / bottom / opaque handle — no structural type to read.
        ViewHead::Ident(_) | ViewHead::Bottom | ViewHead::Opaque => fresh_type_var(kb),
    }
}

/// WI-283 — the type-directed firing guard for `@[simp]` rewriting.
///
/// A `@[simp]` rule's guard is its explicit `:- …` *plus* the `requires` of
/// its enclosing sort (proposal 043 §4.1). When the rule is scoped to a
/// **parametric (spec) sort** — its redex functor is a *spec op*, e.g.
/// `Numeric.add` — that law holds only for carriers that *satisfy* the
/// sort. So the rule fires only where the **carrier** arguments' least
/// sorts (read via [`sort_functor_of_view`] over each occurrence's
/// `inferred_type`) provide the spec; otherwise firing would rewrite
/// where the requirement is unmet (unsound — it would erase an ill-typed
/// call, or apply a law that doesn't hold for that carrier).
///
/// The carrier arguments are the parameters declared with the spec sort's
/// own type-parameter — `add(a: T, b: T)` → both `a` and `b`;
/// `scale(v: T, k: Int)` → just `v`; `bar(k: Int, x: T)` → just `x`. Using
/// a positional shortcut (`pos_args[0]`) instead would test the wrong
/// argument whenever the carrier is not the leading parameter — wrongly
/// firing where a *non-carrier* arg's type happens to provide the spec.
///
/// Returns `true` (fire) when the redex functor is **not** a spec op — a
/// concrete top-level identity (`transpose(transpose(?m)) = ?m`); the
/// functor symbol already pins the sort, so structural match is sound —
/// **or** it is a spec op with ≥1 carrier argument and every carrier's
/// least sort provides the spec. Returns `false` (don't fire) when the
/// signature is unavailable, a carrier argument is missing, its type is
/// unresolved (a free type var — satisfaction undecidable), or it does not
/// provide the spec.
///
/// MUST STAY SIDE-EFFECT-FREE and rid-independent (a pure function of `kb` +
/// `redex`). WI-655 relies on this: `simp_rewrite::try_fire` now ELIDES this
/// guard entirely for a node whose functor matches no `@[simp]` rule (it can't
/// fire), and memoizes one passing verdict across the sibling rules under a
/// matched functor. A diagnostic push / telemetry / cache-mutation added here
/// would make firing observably depend on whether a functor happened to match —
/// a silent divergence, since both paths still return the same `bool`.
pub fn simp_fire_guard_holds(kb: &KnowledgeBase, redex: &NodeOccurrence) -> bool {
    let (functor, pos_args) = match redex.as_expr() {
        Some(Expr::Apply {
            functor, pos_args, ..
        }) => (*functor, pos_args),
        Some(Expr::Constructor { name, pos_args, .. }) => (*name, pos_args),
        _ => return true,
    };
    // A non-spec-op functor is a concrete monomorphic identity whose functor
    // already pins the sort, so a structural match is sound → fire (guard-free).
    let Some(spec_sort) = lookup_spec_op_dispatch(kb, functor) else {
        return true;
    };
    // WI-578: each carrier argument's sort head is read from the typer-pushed
    // `inferred_type` (was `min_sort`, removed) on its occurrence. A carrier
    // supplied by name (no positional slot) reads as `None` → don't fire — the
    // `@[simp]` matcher does not match a positional rule LHS against a named-arg
    // redex either, so such a redex never reaches a fire regardless.
    // The `@[simp]` firing decision is two-valued (fire / don't) — a
    // non-`Fire` outcome (`DontFire` or an under-determined `Suspend`) is "don't
    // fire this rewrite"; WI-300's guard consumes the third state directly.
    matches!(
        simp_guard_holds_core(kb, functor, spec_sort, |i| {
            pos_args
                .get(i)
                .and_then(|a| a.inferred_type())
                .and_then(|t| sort_functor_of_view(kb, &t))
        }),
        FindDictOutcome::Fire
    )
}

/// WI-283 / WI-292 — the shared spec-op firing decision for `@[simp]` rewriting,
/// parameterized over how each positional argument's carrier sort head is read.
/// Both the typer ([`simp_fire_guard_holds`]) and the resolver
/// ([`simp_requires_guard_holds`]) share this core for the *which-argument-
/// carries-the-spec* decision, so they cannot disagree on that. They DO feed it
/// different sort readers — the typer the per-occurrence `inferred_type`, the
/// resolver a structural [`value_type_term`] under an empty subst — so for a
/// given carrier they can still differ on *whether* it provides the spec (e.g. a
/// constraint-typed unbound var the typer resolves but the resolver reads as
/// headless). Each individual firing stays sound (it fires only when its own
/// reader says the carrier provides); the divergence is a completeness gap, not
/// unsoundness.
///
/// `spec_sort` is `functor`'s already-resolved dispatch sort
/// ([`lookup_spec_op_dispatch`]); each caller resolves it once and applies its
/// OWN non-spec-op default (the typer fires a non-spec-op monomorphic identity,
/// the resolver leaves its requires-guarded rule skipped), so this core handles
/// only the spec-op case and never re-dispatches. Returns `true` (fire) when the
/// spec op has ≥1 carrier argument and every carrier's sort head provides the
/// spec. Returns `false` (don't fire)
/// when the signature is unavailable, a carrier argument's sort head is unknown
/// (`arg_carrier_sort` returns `None`: a missing positional slot, an unresolved
/// type, or a headless type — under-determined, never NAF-decided; WI-067), or
/// it does not provide the spec. The carrier arguments depend on the sort's
/// shape (WI-596): for a carrier-parameter typeclass they are the parameters
/// declared with the spec sort's own type-parameter (`add(a: T, b: T)` → both
/// `a` and `b`; `scale(v: T, k: Int)` → just `v`); for a self-representing
/// container (some parameter is typed with the sort itself) they are the
/// sort-typed parameters (`member(x: T, s: Set)` → just `s`), and the content
/// type-parameter arguments (`x: T`) carry no obligation.
/// WI-596 — is `spec_sort` a *self-representing* container over `params` (some
/// parameter is typed with the spec sort itself, e.g. `member(x: T, s: Set)`)?
/// Such a sort names its carrier by the SORT, not by a type-parameter, so the
/// carrier arguments are the sort-typed ones and its type-parameters are content.
/// Shared by [`simp_guard_holds_core`] and [`op_has_spec_carrier_param`] so they
/// classify carriers identically.
pub(super) fn spec_self_represented_by(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    spec_sort: Symbol,
) -> bool {
    params.iter().any(|(_n, pty)| {
        carrier_sort_of_value(kb, pty).is_some_and(|s| same_sort_canonical(kb, s, spec_sort))
    })
}

/// WI-596 — does parameter type `param_type` CARRY spec `spec_sort` (so that its
/// argument's runtime type decides the instance)? For a carrier-parameter
/// typeclass (`PartialEq.eq(a: T, b: T)`) the carriers are the type-param-typed
/// parameters; for a self-representing container (`Set.member(x: T, s: Set)`) they
/// are the sort-typed parameters (and the content `x: T` carries no obligation).
/// The per-parameter half of [`simp_guard_holds_core`]'s carrier decision,
/// factored out so the WI-300 witness selector applies the SAME rule.
pub(super) fn param_is_spec_carrier(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    type_params: &[String],
    self_representing: bool,
    param_type: &Value,
) -> bool {
    match carrier_sort_of_value(kb, param_type) {
        Some(s) if self_representing => same_sort_canonical(kb, s, spec_sort),
        Some(s) => type_params
            .iter()
            .any(|tp| tp.as_str() == kb.local_name_of(s)),
        None => false,
    }
}

/// WI-300 — does `functor` (a spec op of `spec_sort`) have at least one carrier
/// parameter, i.e. can a call to it ground the spec's instance from its arguments?
/// A nullary or all-content op (`Monoid.unit() -> T`, `Numeric.fromInt(n: Int)`)
/// has none: its arguments never determine the carrier, so it cannot serve as a
/// WI-300 requirement witness (the witness scan must skip it, else the guard
/// permanently `DontFire`s — [`simp_guard_holds_core`] leaves `checked_carrier`
/// false with no carrier argument). Uses the SAME carrier rule as the guard.
pub(super) fn op_has_spec_carrier_param(
    kb: &KnowledgeBase,
    functor: Symbol,
    spec_sort: Symbol,
) -> bool {
    let Some(rec) = crate::kb::op_info::lookup_operation_info(kb, functor) else {
        return false;
    };
    let type_params = kb.type_params_of_sort(spec_sort);
    let self_representing = spec_self_represented_by(kb, &rec.params, spec_sort);
    rec.params
        .iter()
        .any(|(_n, pty)| param_is_spec_carrier(kb, spec_sort, &type_params, self_representing, pty))
}

pub(super) fn simp_guard_holds_core(
    kb: &KnowledgeBase,
    functor: Symbol,
    spec_sort: Symbol,
    arg_carrier_sort: impl Fn(usize) -> Option<Symbol>,
) -> FindDictOutcome {
    // The caller has already resolved `functor`'s spec sort (one
    // `lookup_spec_op_dispatch` per firing decision, shared with its own
    // non-spec-op default) and passes it in — a non-spec-op functor never
    // reaches here. Without the signature we can't tell which arguments carry the spec,
    // so we can't verify the law applies — don't fire.
    let Some(rec) = crate::kb::op_info::lookup_operation_info(kb, functor) else {
        return FindDictOutcome::DontFire;
    };
    let type_params = kb.type_params_of_sort(spec_sort);

    // WI-596 — two shapes of spec sort name their carrier differently, and the
    // "which argument carries the spec" decision must follow the shape (see
    // [`param_is_spec_carrier`] / [`spec_self_represented_by`]):
    //
    //   * A pure carrier-parameter typeclass (`Magma`, `Eq`, `Numeric`) names its
    //     carrier BY a type-parameter — `op2(a: T, b: T)` — so its instances ARE
    //     the type-param values (`fact Magma[T = Int64]` ⇒ `Int64` provides
    //     `Magma`). The carrier arguments are the type-param-typed ones.
    //   * A self-representing container (`Set`, `Map`, `List`, `Stream`) names its
    //     carrier by the SORT ITSELF — `insert(s: Set, x: T)`, `get(m: Map, …)` —
    //     and its type-parameters (`T`, `K`/`V`) are CONTENT (element / key /
    //     value), NOT required to provide the sort. Only the sort-typed arguments
    //     carry an obligation.
    let self_representing = spec_self_represented_by(kb, &rec.params, spec_sort);

    let mut checked_carrier = false;
    for (i, (_param_name, param_type)) in rec.params.iter().enumerate() {
        // Only CARRIER arguments decide the instance; a content argument's
        // under-determination is irrelevant, so it is never read here (this is
        // what keeps the guard from over-suspending on an unbound content arg).
        if !param_is_spec_carrier(kb, spec_sort, &type_params, self_representing, param_type) {
            continue;
        }
        // The carrier argument's sort head, read by the caller's reader. Split the
        // three outcomes (never NAF-decide an under-determined carrier; WI-067):
        match arg_carrier_sort(i) {
            Some(carrier) if sort_provides(kb, carrier, spec_sort) => checked_carrier = true,
            // Ground carrier that does not provide the spec → don't fire.
            Some(_) => return FindDictOutcome::DontFire,
            // Headless / missing carrier (under-determined) → suspend, don't decide.
            None => return FindDictOutcome::Suspend,
        }
    }
    if checked_carrier {
        FindDictOutcome::Fire
    } else {
        FindDictOutcome::DontFire
    }
}

/// WI-292 — the RESOLVER-side type-satisfaction check for a requires-guarded
/// `@[simp]` redex: the counterpart of [`simp_fire_guard_holds`] that reads each
/// argument's carrier sort from [`value_type_term`], sharing the carrier decision
/// ([`simp_guard_holds_core`]).
///
/// WI-641 Phase 2 — CARRIER-NEUTRAL: the redex arrives as a `&Value`, so its
/// positional carrier arguments are read in their own carrier. A `Value::Node`
/// child carries its type in `inferred_type` (WI-578) — which `value_type_term`
/// honors — so the resolver reads the SAME per-occurrence type the typer's
/// [`simp_fire_guard_holds`] does, and the two phases can no longer disagree on a
/// requires-guarded Node redex (the former version reified the whole redex to a
/// term, discarding those carried types and interning a transient). A term child
/// stays a structural recompute (unchanged).
///
/// This is only the *type* half of the resolver's firing decision; the caller
/// ([`crate::kb::resolve::KnowledgeBase::fire_simp_equation`]) gates it behind the
/// `@[simp]`/`@[unfold]` tag (`equation_is_directional_rewrite` — a non-directional
/// law like `add_comm` must never fire) and `equation_is_requires_guarded`.
/// Returns `true` only for a body-less SPEC-OP redex whose carrier arguments
/// provide the spec; a non-`Fn` redex or a non-spec-op (a concrete / defaulted
/// op) returns `false`. A container-sort rule (`Set.member`) is left skipped two
/// ways: it is not `@[simp]`-tagged AND its carrier is an *element* whose type does
/// not provide the container (so even when it reaches the carrier check it fails).
///
/// `value_type_term` consults `subst` only for variable heads; the resolver
/// passes the frame σ (WI-595), so a constraint-typed carrier var is decidable
/// where the store determines it and reads headless (`None` → don't fire)
/// otherwise. Sound (a σ never fabricates a providing sort), conservatively
/// incomplete on a still-unbound carrier (never NAF-decide; WI-067).
pub(crate) fn simp_requires_guard_holds(
    kb: &mut KnowledgeBase,
    redex: &Value,
    subst: &Substitution,
) -> bool {
    let (functor, pos_arity) = match redex.head(kb) {
        ViewHead::Functor {
            functor: Some(f),
            pos_arity,
            ..
        } => (f, pos_arity),
        // A non-`Fn` redex (a bare const / var / nullary ref / anonymous
        // aggregate) is not a spec-op application the type dispatch can decide —
        // keep a requires-guarded rule with such an LHS skipped (don't fire).
        _ => return false,
    };
    // Only a (body-less) spec-op redex is decidable here: its carrier arguments'
    // types select the dispatch. Resolve the spec sort FIRST so a non-spec-op (a
    // defaulted op, or an op in a non-parametric sort) requires-guarded rule stays
    // skipped — the resolver's conservative default — rather than firing; the
    // resolved `spec_sort` is then threaded into the shared core (one dispatch,
    // not two).
    let Some(spec_sort) = lookup_spec_op_dispatch(kb, functor) else {
        return false;
    };
    // Each positional argument's carrier sort head, read CARRIER-NEUTRALLY: pull
    // the child as a `Value` (Node child → occurrence, term child → `Value::term`)
    // and type it via `value_type_term`. Collected first because `value_type_term`
    // needs `&mut kb` (it may intern sort refs), so it runs BEFORE the
    // immutable-`kb` core call. Only positional carriers are considered — as in
    // the typer's `simp_fire_guard_holds` (a named-arg carrier never matches a
    // positional rule LHS anyway).
    let mut arg_sorts: Vec<Option<Symbol>> = Vec::with_capacity(pos_arity);
    for i in 0..pos_arity {
        // Own the child out (`to_value`) before the mutable `value_type_term`
        // borrow so the immutable `pos_arg` view is dropped first.
        let child: Option<Value> = redex.pos_arg(kb, i).map(|it| it.to_value());
        let sort = match child {
            Some(c) => {
                let ty = value_type_term(kb, subst, &c);
                sort_functor_of_view(kb, &ty)
            }
            None => None,
        };
        arg_sorts.push(sort);
    }
    matches!(
        simp_guard_holds_core(kb, functor, spec_sort, |i| arg_sorts
            .get(i)
            .copied()
            .flatten()),
        FindDictOutcome::Fire
    )
}

/// WI-1040 — the named-argument label under which a `find_dictionary` goal carries
/// its OUTPUT slot: the clause variable the resolved dictionary binds to.
///
/// A NAMED arg, not a positional one, and that is the whole reason acceptance (f)
/// ("`requires(X)` behaves exactly as before") holds structurally: the converter's
/// idempotence gate, the typer sweep's, and the resolver arm's argument reads are
/// all POSITIONAL, so a goal without an `out` is byte-identical to what WI-300
/// delivered. `out` is present iff the surface said `require[…]`.
///
/// ONE FORM, ONE OWNER (the WI-900 rule): the sweep always emits the extended
/// shape; `requires(X)` IS the no-`out` case, not a second encoding. No persistence
/// migration exists — a rewritten rule body is an in-memory contract between the
/// sweep and the resolver arm, re-elaborated from source on every load.
pub(crate) const REQUIREMENT_OUT_LABEL: &str = "out";

/// WI-300 — the three-way outcome of a rule-body `requires(X)` guard (the
/// desugared `find_dictionary` goal). Three-way *by construction* (never
/// NAF-decide, WI-519 / WI-067): the guard RESOLVES the requirement — it does not
/// decide it false when the binding is under-determined.
pub(crate) enum FindDictOutcome {
    /// Every carrier is ground and provides the spec → the rule fires.
    Fire,
    /// A ground carrier has no provider → the rule does not fire (sound: a
    /// well-typed use would carry the instance).
    DontFire,
    /// A carrier type is under-determined → suspend as residual; retry once the
    /// binding is determined.
    Suspend,
}

/// WI-300 — evaluate a rule-body requirement guard at the current binding. The
/// typer sweep ([`record_find_dictionary_grounding`]) rewrote the surface
/// `requires(X)` into `find_dictionary(X_base, op_functor, op_arg…)`, choosing a
/// body call to one of X's operations as the WITNESS whose carrier arguments
/// decide the instance — exactly the redex a `@[simp]` rule fires on
/// ([`simp_requires_guard_holds`]). Here we read each witness argument's carried
/// type ([`value_type_term`], WI-578) → nominal sort head, then share the WI-596
/// carrier decision with the `@[simp]` resolver guard ([`simp_guard_holds_core`]):
/// a carrier-parameter typeclass (`Eq`) checks the type-param arguments, a
/// self-representing container (`Set`) checks the sort-typed arguments. An
/// under-determined CARRIER (no nominal sort head — unbound / headless) SUSPENDS,
/// never decides the guard false. An under-determined NON-carrier (content)
/// argument does not suspend: like `simp_requires_guard_holds`, each argument's
/// sort head rides as an `Option` and only the carrier indices are consulted, so
/// an unbound element beside a ground carrier still decides `Fire`.
pub(crate) fn find_dictionary_guard(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    op_functor: Symbol,
    arg_vals: &[Value],
    // WI-20260913-J38VE: the written bracket, read off slot 0 once by
    // [`requirement_bracket`]. The GUARD uses only its projected member — it builds no
    // [`SortGoal`], so there is no slot for a written binding to fill.
    bracket: &RequirementBracket,
) -> FindDictOutcome {
    let arg_types = match projected_arg_types(kb, subst, arg_vals, bracket.project) {
        Ok(t) => t,
        Err(outcome) => return outcome,
    };
    // THE ANCHOR FORM'S NO-`out` PATH — and it is the CHECK TIER's only consumer.
    //
    // `/code-review` found this branch unreachable and it was: the anchor emitted
    // `goal: None` for the no-`out` case, so no anchor-form goal without `out` was ever
    // stored, and every one with `out` routed through `read_dictionary_into`. It is
    // reachable now because the check tier emits its goal like the bind tier does —
    // which is what makes `requires(X)` and `require[X]` one relation instead of two.
    // Driven by `wi_qmfc5…::the_check_tier_emits_the_same_goal_the_bind_tier_does` and
    // the three soundness rows beside it.
    if is_anchor_form(kb, spec_sort, op_functor) {
        return anchor_guard(kb, spec_sort, &arg_types);
    }
    guard_over_arg_types(kb, spec_sort, op_functor, &arg_types)
}

/// WI-20260909-S8CBV gate (1) — [`witness_arg_types`], with δ applied to the CARRIER
/// when the bracket projected one. `Err` carries the three-valued verdict the caller must
/// return unchanged.
///
/// ONE PLACE, because the guard and the fetch must see the SAME carrier type or a goal
/// could be guarded on the receiver and fetched on its member. That pairing is the same
/// one [`fetch_dictionary`] already states for `is_anchor_form`, one question over.
///
/// A CARRIER THAT DOES NOT YET BIND THE MEMBER SUSPENDS, never `DontFire`. The rule body
/// may be entered before the head variable is bound, and deciding the guard false there
/// would silently drop a clause that is merely not ready — WI-067's discipline, which
/// [`anchor_guard`] applies to a headless carrier for the identical reason.
fn projected_arg_types(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    arg_vals: &[Value],
    project: Option<Symbol>,
) -> Result<Vec<Value>, FindDictOutcome> {
    let mut arg_types = witness_arg_types(kb, subst, arg_vals);
    let Some(member) = project else {
        return Ok(arg_types);
    };
    // NO CARRIER AT ALL, with a projection to apply — a shape nothing emits: the anchor
    // is what produces a projected goal and it always writes exactly one carrier slot.
    // Loud in debug and a DELAY in release, the repo's rule for an unreachable defect,
    // and NOT the `DontFire` a first cut wrote here: deciding the guard false would drop
    // the clause silently, which is the very thing this function's own rule forbids
    // three lines down. `/code-review` found the contradiction.
    let Some(first) = arg_types.first() else {
        debug_assert!(
            false,
            "projected find_dictionary goal with no carrier argument"
        );
        return Err(FindDictOutcome::Suspend);
    };
    match project_carried_member(kb, first, member) {
        Some(projected) => {
            arg_types[0] = projected;
            Ok(arg_types)
        }
        None => Err(FindDictOutcome::Suspend),
    }
}

/// Each witness argument's CARRIED TYPE (`value_type_term`, WI-578) — the same
/// total type reader `simp_requires_guard_holds` uses. Read whole and kept whole:
/// the head constructor is what selects a provider row, and the type ARGUMENTS are
/// what a sub-dictionary fetch needs, so collapsing to the head here would throw
/// away half of what [`fetch_dictionary`] must pass on. Needs `&mut kb` (it may
/// intern sort refs), so it runs before any immutable-`kb` walk.
fn witness_arg_types(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    arg_vals: &[Value],
) -> Vec<Value> {
    arg_vals
        .iter()
        .map(|v| value_type_term(kb, subst, v))
        .collect()
}

/// The WI-300 guard decision over already-read carried types. A headless argument
/// rides as `None`; [`simp_guard_holds_core`] decides Fire/DontFire/Suspend from
/// only the CARRIER indices (a headless carrier ⇒ Suspend).
fn guard_over_arg_types(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    op_functor: Symbol,
    arg_types: &[Value],
) -> FindDictOutcome {
    let arg_sorts: Vec<Option<Symbol>> = arg_types
        .iter()
        .map(|t| sort_functor_of_view(kb, t))
        .collect();
    simp_guard_holds_core(kb, op_functor, spec_sort, |i| {
        arg_sorts.get(i).copied().flatten()
    })
}

/// WI-20260909-S8CBV gate (1) — the MEMBER a `require` bracket's carrier projects, read
/// off the stored spec instance (`Desc[T = p.E]` ⟹ `E`), or `None` for every bracket
/// that names a type directly.
///
/// The bracket's already-extracted `base` and `bindings` are passed in rather than the
/// instance: [`requirement_bracket`] is the one owner of that walk, and this is one of
/// its two readers.
///
/// THE CARRIER PARAMETER'S BINDING, WHICH IS THE QUESTION THE ANCHOR ASKS. A first cut
/// took the first projected binding it found anywhere in the instance, and
/// `/code-review` named the defect: [`written_projection_anchor`] reads the binding AT
/// [`spec_carrier_param_or_sole`], so two readers were deriving one fact by two rules and
/// could disagree — `require[Two[A = Leaf, B = p.E]]` has the anchor select `A = Leaf` as
/// an ordinary sort while this function projected `B`'s `E` off `Leaf`, which binds no
/// `E`, suspending forever on a clause that should never have projected at all.
///
/// NO ROW MOVES, and that is stated rather than left to be assumed. The two rules can
/// differ only on a bracket carrying TWO bindings, which needs a spec with two type
/// parameters.
///
/// THE ORIGINAL MEASUREMENT'S PREMISE HAS EXPIRED, and re-measuring beat inheriting it.
/// It read: on a two-parameter spec every admissible spelling RESIDUALIZES, so the rules
/// cannot be told apart. WI-20260913-J38VE closed exactly that — a multi-parameter spec
/// now grounds through the typed-head anchor and ANSWERS — so the old sentence would have
/// been a reason that had stopped being true while still reading as evidence.
///
/// RE-MEASURED 2026-09-13 AFTER J38VE, on the disagreeing shape built for it: a
/// two-parameter spec with a CONCRETE carrier binding and a PROJECTED sibling
/// (`require[Two[A = Red, B = p.E]]` under `?x: Red, p: Box`), at a provider binding the
/// sibling abstractly AND at one binding it concretely. Both rules answer NOTHING on
/// both, and the whole `wi_s8cbv` / `wi_qmfc5` / `wi_j38ve` set is green under the naive
/// rule. The reason is now one step earlier and is structural rather than incidental: a
/// projection at a NON-carrier element does not survive to a fetch at all — it needs a
/// typed head root, a typed head takes the ANCHOR route, and the anchor pins the carrier
/// from the head binding — so the binding this function would disagree about is one
/// [`written_element`] declines anyway. So this is still one derivation replacing two.
///
/// THE PROJECTION TEST RUNS FIRST, AND IT IS THE CHEAP ONE. This is called for EVERY
/// `find_dictionary` goal, and the overwhelming majority of brackets project nothing —
/// so the binding scan (which the caller's `extract_type` already paid for) decides
/// those, and [`spec_carrier_param_or_sole`] is asked only where a projection is
/// actually present.
///
/// THAT ORDERING IS A CORRECTION, not a micro-optimization. An earlier draft called
/// the predicate unconditionally and its own doc claimed the cost was one memoized
/// lookup; `/code-review` measured otherwise — only `spec_carrier_param` is cached, and
/// its MISS path calls `spec_is_self_representing`, which builds an `OperationInfoFull`
/// per declared operation. For a self-representing spec, or a multi-parameter one with
/// no receiving op, that was an uncached operation scan on the per-goal resolver path,
/// where `builtin_find_dictionary` previously did no symbol lookup at all.
fn requirement_projection_member(
    kb: &KnowledgeBase,
    base: Symbol,
    bindings: &[(Symbol, Value)],
) -> Option<Symbol> {
    if !bindings
        .iter()
        .any(|(_, v)| matches!(extract_type(kb, v), TypeExtractor::ExprCarried { .. }))
    {
        return None;
    }
    let carrier = spec_carrier_param_or_sole(kb, kb.canonical_sort_sym(base))?;
    let (_, written) = bindings.iter().find(|(k, _)| same_label(kb, *k, carrier))?;
    match extract_type(kb, written) {
        TypeExtractor::ExprCarried { member, .. } => Some(member),
        _ => None,
    }
}

/// WI-20260913-J38VE — WHAT THE AUTHOR WROTE, read off the emitted goal's slot 0 (the
/// spec instance WI-20260909-51W18 retains there) ONCE, for the two readers that need it.
///
/// ONE READER OF SLOT 0, TWO FACTS. `extract_type` on that value is what yields both the
/// projected member and the written bindings, and asking for them separately would walk
/// the instance twice and — worse — put one bracket under two derivations, the defect
/// `/code-review` already named inside [`requirement_projection_member`] itself. So the
/// resolver reads the bracket once and hands this struct down both the guard path (which
/// uses only [`Self::project`]) and the fetch path (which uses both).
///
/// EMPTY IS A REAL ANSWER, not an absence to be papered over: `require[Desc]` binds
/// nothing, and every reader of [`Self::written`] must behave exactly as it did before
/// this struct existed when the bracket names no element. That is what makes
/// `require[Desc]` and `require[Desc[T = Leaf]]` distinguishable at the fetch — the
/// distinction S1's retention created and nothing on this path could yet see.
pub(crate) struct RequirementBracket {
    /// The member a PROJECTED carrier names (`Desc[T = p.E]` ⟹ `E`), `None` for every
    /// bracket that names a type directly — WI-20260909-S8CBV gate (1).
    pub(crate) project: Option<Symbol>,
    /// The bracket's bindings as written, `(param, value-type)`. Keys are matched by
    /// LOCAL NAME downstream, as every other reader of a spec-parameter key is.
    pub(crate) written: Vec<(Symbol, Value)>,
}

/// WI-20260913-J38VE — read the `require` bracket off the goal's slot 0.
///
/// READ AT THE RESOLVER, because that is where the instance is. The emitted goal carries
/// the instance whole in slot 0 (WI-20260909-51W18's retention) and the carrier VARIABLE
/// in slot 2; the projected member is the one piece that cannot ride slot 2, since that
/// slot holds the value whose type is about to be read.
///
/// CARRIER-BLIND, through `extract_type`: the instance reaches here as a σ-walked
/// `Value`, which may be a term or an occurrence depending on the path that stored it.
///
/// A NON-`Parameterized` INSTANCE IS THE BARE SPELLING, not a defect — `require[Desc]`
/// stores `Ref(Desc)` — so it answers the empty bracket rather than declining.
pub(crate) fn requirement_bracket(kb: &KnowledgeBase, instance: &Value) -> RequirementBracket {
    let TypeExtractor::Parameterized { base, bindings } = extract_type(kb, instance) else {
        return RequirementBracket {
            project: None,
            written: Vec::new(),
        };
    };
    RequirementBracket {
        project: requirement_projection_member(kb, base, &bindings),
        written: bindings,
    }
}

/// WI-20260909-S8CBV gate (1) — δ AT FIRE TIME: project `member` off the carrier's
/// CARRIED TYPE (`Box[E = Red]` at `E` ⟹ `Red`).
///
/// THIS IS THE `fetch` ROW OF `requirement-channel.md` §2.1's table, not a typing
/// operation — the invariant that "run time performs no typing operations" is about
/// inference, unification and selection, and this is a member read off a type that has
/// already been read. `x.E` names WHICH carried type the fetch should look at; the fetch
/// itself is unchanged.
///
/// `None` when the type does not bind that member — an unbound or headless carrier, or a
/// member the receiver's sort does not declare. The caller must SUSPEND on it rather than
/// decide the guard false: at the moment a rule body is entered the head variable may
/// simply not be bound yet, which is the same three-valued discipline
/// [`anchor_guard`] already applies to a headless carrier (WI-067).
fn project_carried_member(kb: &KnowledgeBase, ty: &Value, member: Symbol) -> Option<Value> {
    let TypeExtractor::Parameterized { bindings, .. } = extract_type(kb, ty) else {
        return None;
    };
    bindings
        .iter()
        .find(|(k, _)| same_label(kb, *k, member))
        .map(|(_, v)| v.clone())
}

/// WI-20260909-QMFC5 — is this rewritten goal the TYPED-HEAD ANCHOR form rather than the
/// witness one?
///
/// The two forms share one relation and one argument layout: slot 1 holds the WITNESS OP
/// in one and the SPEC BASE in the other. Asking whether that symbol is a SORT is the
/// discriminator the shapes already carry — a spec op is an `Operation`, so the two can
/// never be confused and no kernel symbol had to be minted to tell them apart. The
/// equality is belt to that brace: the anchor emitter writes the spec base into BOTH
/// slots, so a sort there that is not this goal's own spec is a shape nothing produces.
///
/// `has_kind`, NOT `kind_of`. Symbol categories are a SET and `kind_of` reports only the
/// FIRST-DECLARED one — its own doc says to ask `has_kind` "whenever the question is 'can
/// this name serve as an X'", which is exactly this question. MEASURED with `kind_of`: a
/// program declaring `namespace test.Desc` before `sort Desc` answered `Namespace` here,
/// so an anchored goal was routed down the WITNESS path with a sort in the op slot, found
/// no signature, and the clause SILENTLY answered nothing where the same program without
/// that namespace answered `7`. The same desync WI-20260824-Q0093 found once already.
pub(super) fn is_anchor_form(kb: &KnowledgeBase, spec_sort: Symbol, slot1: Symbol) -> bool {
    slot1 == spec_sort && kb.has_kind(slot1, crate::kb::SymbolKind::Sort)
}

/// WI-20260909-QMFC5 — the anchor form's guard: does the carrier VALUE's carried type
/// provide the spec?
///
/// [`simp_guard_holds_core`] is BYPASSED rather than generalized, and that is the point
/// of the second path: its whole job is reading an op's params to learn which arguments
/// carry the spec (WI-596's two shapes), and the anchor has one argument which IS the
/// carrier by construction. So the question collapses to one [`sort_provides`] — the same
/// oracle the witness path reaches through the shared core, asked directly.
///
/// Three-valued exactly as the witness path is: a headless carried type SUSPENDS and is
/// never NAF-decided (WI-067), because the head variable may simply not be bound yet.
fn anchor_guard(kb: &KnowledgeBase, spec_sort: Symbol, arg_types: &[Value]) -> FindDictOutcome {
    let Some(ty) = arg_types.first() else {
        // No carrier argument at all. The emitter always writes one, so this is a
        // malformed goal rather than an undecided one — don't fire.
        return FindDictOutcome::DontFire;
    };
    match sort_functor_of_view(kb, ty) {
        // BOTH CHANNELS, and the pairing with the load site is the point.
        // [`carrier_provides_spec`] is the documented owner of "does this carrier supply
        // this spec" — a sort's own out-edges PLUS a provision another sort declares FOR
        // it (`sort Rival provides Desc[T = Leaf]`, WI-1043). A bare [`sort_provides`]
        // here is blind to the second, and `/code-review` drove both faces of that:
        // asking only `sort_provides` at the LOAD site refuses a witness-supplied carrier
        // outright, while asking only it HERE lets the clause load and then answer
        // nothing. Widening one end alone just moves which face you get, so the two move
        // together — that is why this line and `anchor_grounding`'s selection cite each
        // other rather than each carrying its own copy of the predicate.
        Some(carrier) if carrier_provides_spec(kb, carrier, spec_sort) => FindDictOutcome::Fire,
        Some(_) => FindDictOutcome::DontFire,
        None => FindDictOutcome::Suspend,
    }
}

/// WI-1016 — THE ONE KEY SPELLING every producer of a spec-parameter binding must use:
/// the bare short-name symbol when one is registered, else the spec-qualified parameter.
///
/// Written out at three sites (the anchor's pinned binding, `witness_sort_goal`'s pinned
/// loop, and the shared wildcard tail), which is two too many for a rule whose whole
/// content is "both carriers key alike" — a producer that spelled it differently put one
/// slot under two `Symbol`s, latent for exactly as long as every reader compared by local
/// name. `/code-review` asked for one owner; this is it.
///
/// `fallback` is what stands in when the spec-qualified name does not resolve. It differs
/// per caller and is therefore passed rather than chosen here: the pinned producers fall
/// back to the parameter symbol they already hold, while the wildcard tail declines to
/// synthesize at all and never reaches this function.
fn spec_param_key(kb: &KnowledgeBase, spec_qn: &str, short: &str, fallback: Symbol) -> Symbol {
    let qualified = kb
        .try_resolve_symbol(&format!("{spec_qn}.{short}"))
        .unwrap_or(fallback);
    kb.try_resolve_symbol(short).unwrap_or(qualified)
}

/// WI-20260909-QMFC5 — the anchor form's [`SortGoal`]: the carrier's carried type pinned
/// at the spec's carrier PARAMETER, with the rest wildcarded by the shared tail.
///
/// WHICH PARAMETER, WITHOUT AN OP. [`spec_carrier_param_or_sole`] (WI-1102 over WI-1076)
/// is the op-INDEPENDENT owner of that question — the param some declared operation
/// receives on, else a sole parameter gated on not-self-representing. It answers `None`
/// for a SELF-REPRESENTING spec, which needs no parameter at all: there the carrier is
/// the SORT, and the goal's [`SortGoal::carrier`] discriminant takes it, exactly as
/// [`witness_sort_goal`]'s self-representing branch does from the same value.
///
/// THE SECOND GATE THAT PREDICATE'S DOC DEMANDS is at the LOAD site
/// ([`anchor_grounding`]), not here: it answers "which parameter an operation takes",
/// which "is not by itself which parameter names the carrier", and the load-time check
/// can name the sort and the spec in a located refusal where this one could only delay.
pub(super) fn anchor_sort_goal(
    kb: &mut KnowledgeBase,
    spec_sort: Symbol,
    arg_types: &[Value],
    // WI-20260913-J38VE — the written bracket's bindings, for the shared tail.
    written: &[(Symbol, Value)],
) -> Option<WitnessGoal> {
    let carrier_ty = arg_types.first()?.clone();
    if spec_is_self_representing(kb, kb.canonical_sort_sym(spec_sort)) {
        let carrier = sort_functor_of_view(kb, &carrier_ty).map(|sort| GoalCarrier {
            sort,
            args: receiver_type_args(kb, &carrier_ty),
        });
        return Some(sort_goal_with_wildcards(
            kb,
            spec_sort,
            SmallVec::new(),
            carrier,
            written,
        ));
    }
    let param = spec_carrier_param_or_sole(kb, spec_sort)?;
    let tid = type_value_as_term(kb, &carrier_ty)?;
    // One key spelling for every producer — see [`spec_param_key`].
    let short = kb.local_name_of(param).to_string();
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();
    let key = spec_param_key(kb, &spec_qn, &short, param);
    let mut bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    bindings.push((key, tid));
    Some(sort_goal_with_wildcards(
        kb, spec_sort, bindings, None, written,
    ))
}

/// WI-1040 — the outcome of READING a rule-body requirement for its VALUE, the
/// mode `require[X]` adds to WI-300's check-only guard.
///
/// Staged per `docs/design/requirement-channel.md` §2.1: **after the typing pass,
/// run time performs no typing operations**. What happens here is a table read —
/// the carried types decide which already-selected provider row applies — and a
/// composition of the rows the conditional provisions name. No inference, no type
/// unification, no instance selection.
pub(crate) enum FindDictFetch {
    /// The guard did not fire, so there is nothing to fetch: its own three-way
    /// verdict stands, unchanged from the no-`out` path.
    Guard(FindDictOutcome),
    /// The dictionary: `Dictionary(sub₀ … subₙ₋₁, impl: S)`.
    ///
    /// **ONE REPRESENTATION** (`requirement-channel.md` §9, which settles §10 item
    /// 2). This is not "the SLD form" of a dictionary — it is THE form. WI-1045
    /// retired the eval-side arena, so an operation call's frame holds this very
    /// value: the two sides do not merely compare equal through a view, they are
    /// built by ONE producer ([`dictionary_of_tree`]) and the crossing converts
    /// nothing.
    ///
    /// STORAGE IS NOT PART OF THE SHAPE, and this deliberately does not intern:
    /// a conditional provision composes over type arguments, so the distinct
    /// dictionaries follow the carried types that actually occur — a family with no
    /// static bound, where interning (which never frees) is the wrong default. It
    /// rides as an ordinary structured `Value`, which unifies and indexes
    /// identically (CLAUDE.md's Representation note: matching and indexing key on
    /// structural `DiscrimKey`s, never on `TermId` identity).
    Fetched(Value),
    /// The guard fired but no single row could be produced here. `detail` names
    /// what was asked for and what came back.
    Undecided { detail: String },
    /// Two rows for one carried type. A DEFECT, not a semantics (§4): overlap is
    /// refused at typing/load, so reaching this means the coherence machinery let
    /// one through. The caller is expected to be loud about it in debug and to
    /// degrade to "cannot decide" in release, never to pick one.
    Defect { detail: String },
}

/// WI-1040 — read a rule-body requirement for its VALUE: run WI-300's guard, and
/// where it fires, FETCH the provider tree for `spec_sort` at the witness
/// arguments' carried types.
///
/// The guard half is shared with [`find_dictionary_guard`] verbatim (one carrier
/// decision, one set of carried types), so the `out` and no-`out` readings of one
/// goal can never disagree about whether the requirement holds — they differ only
/// in whether the dictionary is also produced.
///
/// `resolve` runs with an EMPTY scope and no σ, exactly as
/// [`resolve_bridge_requirements`] does and for the same reason: a rule clause has
/// no caller frame whose slots could satisfy this by forwarding, so a slot can only
/// resolve by CONSTRUCTION (`Leaf`/`Conditional`), never `FromScope`. And no
/// SELECTION — 058 §3.3 puts rule bodies out of scope for the bracket channel.
pub(crate) fn fetch_dictionary(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    spec_sort: Symbol,
    op_functor: Symbol,
    arg_vals: &[Value],
    // WI-20260913-J38VE — the written bracket; see [`find_dictionary_guard`]. Here BOTH
    // halves are read: the projected member picks which carried type to look at, and the
    // written bindings fill the spec elements the witness call does not name.
    bracket: &RequirementBracket,
    // WI-20260911-5G28A S2 — may a RANKING answer a tie? [`DefaultRung::Consult`] when the
    // read BINDS its dictionary (nobody chose, so 058 §3.2's default fills the silence);
    // [`DefaultRung::Unranked`] when it CHECKS a supplied one, where proposal 060 §4 lets
    // only a UNIQUE local row veto it — a default among rivals answers "which provider
    // wins", not "which one the caller chose" (WI-20260922-ATFGH's reading).
    rung: DefaultRung,
) -> FindDictFetch {
    let arg_types = match projected_arg_types(kb, subst, arg_vals, bracket.project) {
        Ok(t) => t,
        Err(outcome) => return FindDictFetch::Guard(outcome),
    };
    // WI-20260909-QMFC5 — one relation, two grounding paths. The guard and the goal are
    // chosen together from the same discriminant, so an anchored goal can never be
    // guarded one way and fetched the other.
    let anchored = is_anchor_form(kb, spec_sort, op_functor);
    let verdict = if anchored {
        anchor_guard(kb, spec_sort, &arg_types)
    } else {
        guard_over_arg_types(kb, spec_sort, op_functor, &arg_types)
    };
    match verdict {
        FindDictOutcome::Fire => {}
        other => return FindDictFetch::Guard(other),
    }
    let built = if anchored {
        anchor_sort_goal(kb, spec_sort, &arg_types, &bracket.written)
    } else {
        witness_sort_goal(kb, spec_sort, op_functor, &arg_types, &bracket.written)
    };
    let Some(WitnessGoal {
        goal,
        from_carried_types,
    }) = built
    else {
        // TWO PATHS, TWO SENTENCES. The witness form's failure IS a missing op signature;
        // the anchor form has no op at all, and on it `op_functor == spec_sort`, so the
        // shared message told the author that `Desc` "has no recorded signature" —
        // pointing them at an operation that does not exist.
        return FindDictFetch::Undecided {
            detail: if anchored {
                format!(
                    "the typed head binding's carried type cannot be read as a term, so \
                     it cannot say which of `{}`'s parameters the carrier fills",
                    kb.qualified_name_of(spec_sort),
                )
            } else {
                format!(
                    "`{}` has no recorded signature, so the witness arguments' carried \
                     types cannot say which of `{}`'s parameters they bind",
                    kb.qualified_name_of(op_functor),
                    kb.qualified_name_of(spec_sort),
                )
            },
        };
    };
    let scope = ResolutionScope {
        available_requires: &[],
        sigma: None,
        selected: &[],
        sub_goal_requires: &[],
    };
    match resolve_with_rung(kb, &goal, &scope, rung) {
        ResolutionResult::Resolved(tree) => match dictionary_of_tree(kb, &tree) {
            Some(d) => FindDictFetch::Fetched(d.into_value()),
            None => FindDictFetch::Undecided {
                detail: "cannot build a dictionary value here: either the resolved tree \
                         names a caller slot (a rule clause has none, and this \
                         resolution ran with an empty scope, so `FromScope` should be \
                         unreachable), or this KB never loaded \
                         `anthill.realization.runtime.Dictionary`"
                    .into(),
            },
        },
        ResolutionResult::Ambiguous { goal_text, tie, .. } => {
            let detail = format!(
                "two providers answer `{goal_text}` at run time: {}",
                tie.candidates
                    .iter()
                    .map(|s| kb.qualified_name_of(*s).to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
            );
            // WI-20260830-X9PB4 — A TIE IS ONLY A DEFECT WHEN THE CARRIED TYPES DECIDED
            // THE WHOLE GOAL. `Defect`'s contract is "overlap is refused at typing/load,
            // so reaching this means the coherence machinery let one through", and that
            // reading needs the goal to be decided ENTIRELY by those types. Where an
            // element came from anywhere else — WI-20260830-X9PB4's synthesized wildcard,
            // or WI-20260913-J38VE's written bracket — two providers may tie for a reason
            // the call never constrained, which is no overlap and no defect, so the honest
            // verdict is "cannot decide" and the caller delays. Both sources are MEASURED
            // as debug aborts on legal programs; see [`WitnessGoal`].
            //
            // AND A TIE WITH THE RANKINGS WITHHELD IS NO DEFECT EITHER: it is 058 §3.3's
            // named-instance case — rivals at one carrier, which the language admits — and
            // the goal only asked whether a UNIQUE row exists to check a supplied
            // dictionary against (WI-20260911-5G28A S2).
            if from_carried_types && rung == DefaultRung::Consult {
                FindDictFetch::Defect { detail }
            } else {
                FindDictFetch::Undecided { detail }
            }
        }
        // The guard said the carrier PROVIDES the spec and instance synthesis then
        // found no tree. The two readers are not the same oracle — `sort_provides`
        // sees a WI-450 witness-sort provision and a denoted/value-fact provision
        // that `resolve`'s candidate collection does not — so this is a reachable
        // COMPLETENESS gap, not an invariant break, and is deliberately not a
        // `debug_assert`: firing on those shapes would reject programs that run
        // correctly today whenever nothing reads the dictionary.
        //
        // Reported as UNDECIDED (⇒ the caller delays), not as failure: `out` is
        // present, so this clause asked to be PASSED a dictionary, and answering
        // "no solution" would be exactly the silent skip a delay refuses to be.
        ResolutionResult::NoMatch {
            goal_text, hint, ..
        } => FindDictFetch::Undecided {
            detail: format!("no provider answers `{goal_text}` ({hint})"),
        },
        ResolutionResult::Cyclic { path, .. } => FindDictFetch::Undecided {
            detail: format!(
                "the provider chain re-enters its own goal: {}",
                path.join(" → ")
            ),
        },
    }
}

/// WI-1040 — the [`SortGoal`] a witness call's carried types denote: which of the
/// spec's parameters each CARRIER argument binds, read through the same
/// carrier decision the guard uses ([`param_is_spec_carrier`] /
/// [`spec_self_represented_by`]), so the goal and the guard cannot disagree about
/// which argument carries the spec.
///
/// The two spec shapes bind differently, and that is WI-596's distinction applied
/// once more rather than re-derived: a carrier-PARAMETER typeclass (`Desc.describe(x:
/// T)`) names its carrier BY a type-parameter, so the argument's carried type is the
/// BINDING; a SELF-REPRESENTING container (`Set.member(x: T, s: Set)`) names its
/// carrier by the sort itself, where no binding is pinned and the argument's sort
/// head is the [`SortGoal::carrier`] discriminant instead (WI-350).
///
/// `None` only when the operation has no recorded signature — the same condition
/// under which the guard itself declines.
///
/// WHAT READS THIS, censused because WI-20260830-X9PB4 widened what it emits: ONE
/// caller, [`fetch_dictionary`], which itself has ONE — `read_dictionary_into`, the
/// `out` arm of `builtin_find_dictionary`. So this producer is reached only from
/// `require[X]` / `?d = require[X]`; WI-300's check-only `requires(X)` takes
/// [`find_dictionary_guard`], which builds no [`SortGoal`] at all and is untouched by
/// anything decided here.
///
/// AND THE OTHER PRODUCER OF A [`SortGoal`] STILL OMITS, which is the right question to
/// ask (raised by /code-review) and is answered by measurement rather than by symmetry.
/// [`sort_goal_from_subst`] — the typer's, feeding `dispatch_spec_op_cached`,
/// `CalleeSlotSource::Dispatch` and the receiver-carrier path — drops a spec param σ
/// does not resolve. It is NOT the same question:
///
///  * There an unresolved param is a FLEX VAR the typer may still pin; here nothing
///    more will ever arrive, because the goal is rebuilt from runtime values at the
///    moment the goal runs.
///  * The compile-time route has a mechanism this one does not — an un-pinnable SLOT
///    becomes WI-857's `Unavailable` marker inside a dictionary that still gets built.
///    `fetch_dictionary`'s goal IS the whole dictionary, so there is no slot to mark.
///
/// MEASURED rather than argued, on the shape this ticket is about: the same spec, the
/// same provision (`Leaf provides Desc[T = Leaf[N], Note = N]`) and the same carrier,
/// dispatched with NO `require` at all, answers `Int(7)` on the typer path — so the two
/// producers are not observably in disagreement about it. Whether they should be one
/// producer anyway is a separate question with its own population, recorded here and
/// not credited to this ticket.
pub(super) fn witness_sort_goal(
    kb: &mut KnowledgeBase,
    spec_sort: Symbol,
    op_functor: Symbol,
    arg_types: &[Value],
    // WI-20260913-J38VE — the written bracket's bindings, for the shared tail. The loop
    // below is UNTOUCHED by them: an element a witness parameter names is pinned from the
    // call's CARRIED TYPE, and a written binding that disagrees with a carried type is a
    // question the load site owns ([`anchor_grounding`]'s refusal), not one to re-answer
    // here with the opposite precedence.
    written: &[(Symbol, Value)],
) -> Option<WitnessGoal> {
    let rec = crate::kb::op_info::lookup_operation_info(kb, op_functor)?;
    let type_params = kb.type_params_of_sort(spec_sort);
    let self_representing = spec_self_represented_by(kb, &rec.params, spec_sort);
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();
    let mut bindings: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
    let mut carrier: Option<GoalCarrier> = None;
    // NO `from_carried_types` LOCAL: the flag is owned by [`sort_goal_with_wildcards`],
    // which is the only thing that can CLEAR it (it is what mints the wildcards and what
    // reads the written bracket). One left behind here would tell a reader this function
    // still tracks the value that decides Defect-vs-Undecided when the callee does.
    for (i, (_pname, pty)) in rec.params.iter().enumerate() {
        if !param_is_spec_carrier(kb, spec_sort, &type_params, self_representing, pty) {
            continue;
        }
        let Some(arg_ty) = arg_types.get(i).cloned() else {
            continue;
        };
        if self_representing {
            // WI-20260828-EKWDC: the carrier's own type ARGUMENTS come off the very
            // value its sort was read from. This producer and the dispatch one
            // ([`receiver_carrier`]) must build the SAME goal for one program — a
            // carrier here that carried only its sort would instantiate the provider's
            // `requires` chain in the declaration scope, which is the defect.
            carrier = carrier.or_else(|| {
                sort_functor_of_view(kb, &arg_ty).map(|sort| GoalCarrier {
                    sort,
                    args: receiver_type_args(kb, &arg_ty),
                })
            });
            continue;
        }
        // The parameter's declared type IS one of the spec's type-parameters
        // (`param_is_spec_carrier` just said so); its short name is the binding key.
        let Some(param_sym) = carrier_sort_of_value(kb, pty) else {
            continue;
        };
        let short = kb.local_name_of(param_sym).to_string();
        // The key spelling `resolve` matches provider heads against — [`spec_param_key`].
        let key = spec_param_key(kb, &spec_qn, &short, param_sym);
        let Some(tid) = type_value_as_term(kb, &arg_ty) else {
            continue;
        };
        if bindings.iter().all(|(k, _)| *k != key) {
            bindings.push((key, tid));
        }
    }
    // WI-20260830-X9PB4 — THE SPEC'S REMAINING ELEMENTS RIDE AS WILDCARDS, and they must
    // ride rather than be OMITTED because the two readings are opposite ones.
    //
    // `FiniteCollection.size(c: C)` names `C` and no other element, so the loop above
    // built `FiniteCollection[C = List[T = String]]` for
    // `require[FiniteCollection[C = List[T = String]]]` — `Element` simply absent. An
    // ABSENT type param is DISCRIMINATING at [`collect_provides_candidates`] ("a concrete
    // `T = Int` on `fact Eq[T = Int]` … else every concrete `Eq` impl would match a bare
    // `Eq` goal"), so `List provides FiniteCollection[C = List[T], Element = T, E = {}]`
    // was rejected on the element the goal never had an opinion about: ZERO candidates,
    // `NoMatch`, `Undecided`, and the woven call delayed where the plain spelling
    // answered `Int(2)`.
    //
    // A PRESENT-BUT-ABSTRACT one is the leniency WI-507 already established for exactly
    // this shape, and its own doc names it: "a carrier-only `clear(c)` pins only the
    // carrier `C`, so the spec's sibling `Element` arrives as `Ref(Sort.Element)` —
    // matches any impl-param binding WITHOUT constraining it: the concrete carrier
    // already pins the shared impl param `T`, and this sibling is whatever that pinning
    // implies via the provider's `provides` fact". That is this goal, one producer over:
    // the carrier is concrete and the sibling is not. `goal_from_requires_entry` gets the
    // same shape for free — a written `requires Iterable[C = C, Element = Element, E = E]`
    // spells every element — and this producer, which rebuilds the goal from the WITNESS
    // CALL rather than from the written bracket, is the one that has to synthesize them.
    //
    // AND THE WILDCARD IS THE LAST RESORT, NOT THE FIRST. The tail below mints one only
    // for an element NOBODY NAMED — WI-20260913-J38VE gave it the written bracket, so an
    // element the author spelled is pinned from what they wrote. The synthesis is still
    // right for the rest, because a witness-grounded goal is built from the call's
    // argument types and the author may have written no bracket at all.
    //
    // THE HISTORY, BECAUSE TWO REASONS EXPIRED HERE IN A ROW. This comment once read
    // "because `lower_require` STRIPS the bracket's type arguments"; WI-20260909-51W18
    // deleted that strip and the bracket rides whole on slot 0. It then read that closing
    // the gap "means READING slot 0, which is a `fetch_dictionary` signature change" —
    // and that is what J38VE did. The gap it named was the author writing
    // `Cap[P = Int64]`, the provider binding `P = Int64`, and the clause delaying anyway
    // because the written binding was replaced by a wildcard here.
    //
    // NOT A WEAKER MATCH: a wildcard is refused against a CONCRETE candidate binding
    // (`fact Eq[T = Int64]` at a wildcard `T` still fails `dispatch_values_match`), so
    // the coherence rule the strict reject protects — wi325 / wi237 — is untouched. What
    // it admits is a candidate whose value for the element is its OWN parameter, which
    // is universally quantified and therefore cannot discriminate anything.
    //
    // EFFECT-ROW PARAMS ARE LEFT OUT, deliberately: an omitted row is ALREADY
    // non-discriminating at the matcher (`sort_param_is_effect_row` skips it there, for
    // WI-387/WI-714's reason — "a row is the observation effect, not carrier identity"),
    // so that question has an owner and a wildcard here would take it away from it and
    // answer it differently.
    //
    // MEASURED, on a purpose-built fixture, because the WHOLE 3934-test binary passes
    // with this guard removed and a green corpus is therefore no evidence about it:
    // `provides Walk[C = Src, E = Error]` — a provision writing a CONCRETE non-empty row
    // — keeps answering `require[Walk[C]]` with the guard and STOPS with it dropped, its
    // `?d` falling to one indefinite solution, because `Ref(Walk.E)` reaches
    // `dispatch_values_match` against the written `Error` and the two sort symbols
    // differ. The `E = {}` sibling is unmoved either way, which is what makes that a
    // measurement rather than an un-drivable fixture.
    // `wi_x9pb4_require_dictionary_element_test::an_effect_row_element_is_left_to_its_
    // own_owner` drives both arms.
    Some(sort_goal_with_wildcards(
        kb, spec_sort, bindings, carrier, written,
    ))
}

/// WI-20260909-QMFC5 — the SHARED tail of every [`SortGoal`] this tier builds: fill the
/// spec's remaining elements with wildcards and assemble.
///
/// Extracted from [`witness_sort_goal`] verbatim when the typed-head anchor became a
/// SECOND producer of the pinned set. The wildcard rule and its `synthesized` flag are
/// subtle enough (see below, and [`WitnessGoal`]) that a copy is a copy that drifts —
/// and the flag decides whether a resolution TIE reads as a defect or as "cannot decide",
/// which is a verdict neither producer may answer differently.
fn sort_goal_with_wildcards(
    kb: &mut KnowledgeBase,
    spec_sort: Symbol,
    mut bindings: SmallVec<[(Symbol, TermId); 2]>,
    carrier: Option<GoalCarrier>,
    // WI-20260913-J38VE — what the author WROTE, for the elements the carrier does not
    // pin. See the loop body.
    written: &[(Symbol, Value)],
) -> WitnessGoal {
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();
    let mut from_carried_types = true;
    for short in kb.type_params_of_sort(spec_sort) {
        if sort_param_is_effect_row(kb, spec_sort, &short) {
            continue;
        }
        if bindings
            .iter()
            .any(|(k, _)| kb.local_name_of(*k) == short.as_str())
        {
            continue;
        }
        // `type_params_of_sort` just listed this name, so the qualified symbol is
        // expected to resolve; a miss leaves the element ABSENT, which is exactly the
        // pre-ticket reading, and is the same `continue` the sibling goal producer
        // [`sort_goal_from_subst`] takes on the same lookup. Not made loud here because
        // that would be a NEW refusal on a shape neither producer has ever seen fail —
        // the two must keep answering one way.
        let Some(qualified) = kb.try_resolve_symbol(&format!("{spec_qn}.{short}")) else {
            continue;
        };
        // The same key spelling the pinned loop uses, so a wildcard and a pinned binding
        // are keyed alike — [`spec_param_key`], reached with the qualified symbol this
        // arm has already proved resolves.
        let key = spec_param_key(kb, &spec_qn, &short, qualified);
        // REACHING HERE IS ITSELF THE TIE VERDICT, so it is set ONCE rather than in each
        // arm below. This tail fills an element the producer above did not pin — from the
        // bracket or from a wildcard — and NEITHER is a carried type, which is the whole
        // of what [`WitnessGoal::from_carried_types`] asks. Set after the three `continue`s
        // above, which leave their elements ABSENT and are not this tail filling anything.
        from_carried_types = false;
        // WI-20260913-J38VE — THE AUTHOR'S OWN BINDING BEATS A MINTED WILDCARD, and the
        // wildcard's justification is exactly why: it stands in for an element NOBODY
        // NAMED. Where the bracket names one, there is nothing to stand in for — and
        // minting anyway is not neutral, because a wildcard is REFUSED against a
        // provider's concrete binding (`Red provides Sp[C = Red, P = Int64]`), so the
        // synthesis actively DESTROYED the one fact that could have selected a row. That
        // is not a corner: it is every spec with a second element, since a spec op names
        // only the carrier and the shared tail therefore wildcards all the rest.
        if let Some(tid) = written_element(kb, written, &short) {
            bindings.push((key, tid));
            continue;
        }
        // The spec's OWN parameter symbol as the value — `is_type_param_value`'s
        // wildcard, the same term a written `requires Spec[Element = Element]` clause
        // carries for an element its author did not pin.
        let wildcard = kb.alloc(Term::Ref(qualified));
        bindings.push((key, wildcard));
    }
    WitnessGoal {
        goal: SortGoal {
            spec_sort,
            bindings,
            carrier,
        },
        from_carried_types,
    }
}

/// WI-20260913-J38VE — the written bracket's value for one spec element, as a goal term,
/// or `None` when the bracket says nothing DISCRIMINATING about it and the caller must
/// mint its wildcard instead.
///
/// BY LOCAL NAME, which is how every other reader of a spec-parameter key asks: the
/// bracket's keys come off the stored instance and the caller's `short` off
/// `type_params_of_sort`, and [`spec_param_key`] exists precisely because the two can be
/// different `Symbol`s for one parameter.
///
/// A POSITIVE TEST, not a list of exclusions: only a NAMED TYPE — a sort, or a sort
/// applied to arguments — can pin an element, and everything else takes the mint path.
/// Written that way round because the values a bracket can carry are a growing set
/// ([`TypeExtractor`] has nine variants) and a new one must default to the PRE-TICKET
/// behaviour, not to being pinned as though it were a type.
///
/// LOWERED THROUGH [`value_to_term`], NOT [`type_value_as_term`], and the difference is a
/// wrong answer rather than a missing one. `type_value_as_term` returns the term id only
/// for a `Value::Term` and otherwise falls to `sort_functor_of_view(…)` — the bare SORT
/// HEAD, arguments discarded — and MEASURED, a written binding always arrives as a
/// `Value::Node`, so EVERY applied element took that path. `Box[E = Leaf]` became `Box`,
/// which both failed to match a provider's applied binding AND matched one it should not:
/// `require[Sp[P = Box[E = Other]]]` selected the `Box[E = Leaf]` row. WI-390's converter
/// is the documented owner of exactly this ("the one converter to use where a
/// value-in-type may ride — e.g. a `requires`/`provides` spec"), and it is total: `Err`
/// only for the opaque runtime handles, which take the mint path here like anything else
/// this function cannot name. Found by `/code-review` on this ticket's own diff; driven by
/// `wi_j38ve…::an_applied_written_element_pins_what_the_author_actually_wrote`.
///
/// THE CARRIER SITE IS STILL LOSSY AND IS NOT TOUCHED HERE. [`anchor_sort_goal`] and
/// [`witness_sort_goal`] lower their carrier through `type_value_as_term`, and that
/// predates this ticket: their value is a CARRIED TYPE read off a runtime value, not an
/// author-written one, and moving it is a change to which rows every existing anchor
/// selects. Recorded rather than folded in.
///
/// The two shapes that would otherwise be silently wrong, named so the test is read as
/// deliberate rather than incidental:
///
///  * A PROJECTION (`Desc[T = p.E]`) is not a type — it names WHICH carried type to look
///    at, and WI-20260909-S8CBV gate (1) has already applied it to the carrier argument
///    ([`projected_arg_types`]). Pinning `p.E` itself would put a projection in the goal
///    where a sort belongs, and no provider head matches that.
///  * A value naming a TYPE PARAMETER is the wildcard SPELLED OUT (`requires
///    Spec[Element = Element]`, WI-507's leniency) — a `SortRef`, so the positive test
///    admits it and [`is_type_param_value`] is what turns it away. Taking the mint path
///    is not merely equivalent in the goal: it is what leaves
///    [`WitnessGoal::from_carried_types`] cleared, and a pin that set it would turn a
///    legal program's ambiguity into a debug abort.
///
/// NEITHER EXCLUSION IS DRIVEN TO A DIFFERENT ANSWER, and that is stated rather than
/// implied by a test name. MEASURED 2026-09-13: a projected element reaches here only
/// where the producer above did not already pin it, and every spelling of that — a
/// projection at a NON-carrier element of a two-parameter spec, on both the anchor and
/// the witness route — is REFUSED AT LOAD first ("head bound(s) — Box — provide no
/// `Sp`"), because a projection needs a typed head root and a typed head takes the anchor
/// route. A written type-parameter name is DROPPED upstream by WI-20260909-51W18's rule
/// (`require[Cap[P = P]]` stores no binding at all), and a head-introduced type variable
/// resolves to its GUARD-GIVEN BOUND (`T = Desc`, not a parameter reference —
/// `wi_51w18…::a_head_introduced_type_variable_resolves_inside_the_bracket`). So both
/// lines are written for the value they carry if those upstream rules move, and a
/// back-out of either changes no row today.
fn written_element(
    kb: &mut KnowledgeBase,
    written: &[(Symbol, Value)],
    short: &str,
) -> Option<TermId> {
    let value = written
        .iter()
        .find(|(k, _)| kb.local_name_of(*k) == short)?
        .1
        .clone();
    if !matches!(
        extract_type(kb, &value),
        TypeExtractor::SortRef(_) | TypeExtractor::Parameterized { .. }
    ) {
        return None;
    }
    let tid = crate::kb::node_occurrence::value_to_term(kb, &value).ok()?;
    if is_type_param_value(kb, tid) {
        return None;
    }
    Some(tid)
}

/// WI-20260830-X9PB4 — [`witness_sort_goal`]'s answer, and WHETHER EVERY ELEMENT OF IT
/// CAME OFF A CARRIED TYPE.
///
/// The flag exists because one downstream verdict turns on it and nothing else can
/// recover it. `fetch_dictionary` maps a resolution TIE to
/// [`FindDictFetch::Defect`] — "overlap was typing/load's to refuse, so reaching this
/// means the coherence machinery let one through", loud in debug. That reading holds
/// only while the goal is decided ENTIRELY by the carried types the resolver read: a tie
/// then really is two providers claiming one carried type. A goal carrying an element
/// from any OTHER source is not decided entirely by them — two providers may tie for a
/// reason the call never constrained, which is no defect at all — so that tie is
/// [`FindDictFetch::Undecided`] instead, and the call delays.
///
/// MEASURED, and it is a regression X9PB4 introduced and then closed rather
/// than a hypothetical: `Carrier provides MidA` + `Carrier provides MidB`, each
/// `provides Spec[C = Mid?, Note = <its own N>]`, made
/// `require[Spec[C]], Spec.probe(carrier(), ?r)` fire
/// `debug_assert!(false, "find_dictionary: two providers answer …")` — an abort in
/// every debug build, on a program with no overlap. With the wildcard loop backed out
/// the same program answered ONE INDEFINITE solution. Driven by
/// `wi_x9pb4_require_dictionary_element_test::a_tie_on_a_synthesized_element_delays_
/// rather_than_reporting_a_defect`.
///
/// WI-20260913-J38VE — AND A WRITTEN ELEMENT CLEARS IT TOO, which is the same regression
/// one source over and was MEASURED on the very fixture above. Spell the element the
/// author had left to the wildcard — `require[Spec[C = Carrier, Note = Int64]]` — and a
/// first cut that kept the flag SET aborted:
/// `find_dictionary: two providers answer `Spec[C = Carrier, Note = Int64]` at run time:
/// MidA, MidB`. Note that the tie is on `C` and has nothing to do with `Note`: pinning an
/// element does not make an unrelated tie into overlap, and the flag is deliberately the
/// COARSE question ("did anything but a carried type decide this goal") rather than an
/// attribution of the tie. Driven by
/// `wi_j38ve_written_bracket_fetch_test::a_tie_a_written_element_does_not_cause_stays_a_
/// delay`, whose control is the same program at the bare spelling.
pub(super) struct WitnessGoal {
    pub(super) goal: SortGoal,
    /// True iff EVERY element of this goal was read off a CARRIED TYPE — the witness
    /// call's argument types, or the anchor's head binding. False as soon as one element
    /// came from anywhere else: a minted wildcard, or (WI-20260913-J38VE) the author's
    /// written bracket.
    from_carried_types: bool,
}

/// WI-1040 — a resolved provider tree as the dictionary.
///
/// THE ONE PRODUCER, for both sides of the crossing (WI-1045). The eval side had
/// its own copy of this walk (`Interpreter::port_resolved_tree`) that differed
/// only in building an arena handle; with one representation there is nothing to
/// differ in, so that copy now delegates here and the two crossings cannot spell
/// one tree two ways.
///
/// Built in WI-1019's shape: the sub-dictionaries are POSITIONAL children (slot `k`
/// is the k-th entry of the WI-857 dictionary layout, so the order is the identity)
/// and the impl carrier is the one named child. WI-857's `Unavailable` marker
/// becomes a childless dictionary over the `NoProvider` marker, exactly as
/// `emit_tree_as_projection` spells it — every use of
/// that slot is refused at the read (`resolve_op_target_checked`), so carrying the
/// absence stays loud.
///
/// `None` when the tree names a caller slot — `FromScope` cannot arise from the
/// empty-scope resolution this is called on, and answering `None` rather than
/// inventing a slot name keeps that true — or when the KB has no
/// `anthill.realization.runtime.Dictionary` to name.
pub(crate) fn dictionary_of_tree(
    kb: &mut KnowledgeBase,
    tree: &ResolvedRequiresNode,
) -> Option<Dictionary> {
    // WI-865: `&mut`, because the marker is now minted PER ABSENCE — the one thing a
    // single hoisted marker symbol could not express. Same walk, same shape; the
    // symbol in a marker slot is the one `emit_tree_as_projection` mints for the same
    // node, so the two producers still spell one tree one way.
    fn build(kb: &mut KnowledgeBase, tree: &ResolvedRequiresNode) -> Option<Dictionary> {
        let (impl_sort, subs): (Symbol, Vec<Dictionary>) = match tree {
            ResolvedRequiresNode::Leaf { impl_sort, .. } => (*impl_sort, Vec::new()),
            ResolvedRequiresNode::Unavailable {
                spec_sort,
                why,
                below,
            } => (
                absence_marker_sym(
                    kb,
                    AbsenceRecord::Slot {
                        spec: *spec_sort,
                        why: why.clone(),
                        below: *below,
                    },
                ),
                Vec::new(),
            ),
            ResolvedRequiresNode::Conditional {
                impl_sort,
                sub_resolutions,
                ..
            } => (
                *impl_sort,
                sub_resolutions
                    .iter()
                    .map(|s| build(kb, s))
                    .collect::<Option<Vec<_>>>()?,
            ),
            ResolvedRequiresNode::FromScope { .. } => return None,
        };
        Dictionary::build(kb, impl_sort, subs)
    }
    build(kb, tree)
}

/// A carried type as a `TermId`, for the `TermId`-keyed [`SortGoal::bindings`].
/// `value_type_term` already answers in the term carrier for every type it
/// computes structurally; the fallback re-mints the nominal head for a type that
/// arrived on another carrier, which is exactly the granularity the guard decided
/// on. `None` for a headless type — its caller (`witness_sort_goal`) skips such a
/// binding for its own reasons.
///
/// WI-20260908-PW9A0: this used to read "the guard would have suspended on it", which
/// tied the `None` to [`type_bound_verdict`]'s old non-nominal test. That test is gone
/// and the two were never the same question anyway — this one is about a CARRIER, that
/// one about a type's determinacy.
fn type_value_as_term(kb: &mut KnowledgeBase, ty: &Value) -> Option<TermId> {
    match ty {
        Value::Term { id, .. } => Some(*id),
        other => sort_functor_of_view(kb, other).map(|s| kb.alloc(Term::Ref(s))),
    }
}

/// WI-582 — the resolver-side firing guard for EXPLICIT typed rule patterns
/// (`?x: T`), under the carrier-neutral one-way `match_view` firing (simp
/// rewriter convergence). `match_view_oneway` binds each opened rule global
/// (`fresh[db_index]`) directly to the redex child it matched, so the bound for
/// DeBruijn slot `db_index` is checked against `msubst[fresh[db_index]]` (its
/// CARRIED type via `value_type_term`, WI-578) — no synthetic-`u32::MAX - n`
/// decode. Three-valued (WI-067): a VARIABLE on either side suspends (don't fire);
/// a refuted conformance skips; empty bounds (an untyped rule) trivially hold.
pub(crate) fn typed_pattern_bounds_hold(
    kb: &mut KnowledgeBase,
    rid: crate::kb::RuleId,
    msubst: &Substitution,
    fresh: &[VarId],
) -> bool {
    let bounds = kb.rule_type_bounds(rid).to_vec();
    if bounds.is_empty() {
        return true;
    }
    for (db_index, bound_tid) in bounds {
        let Some(&gvid) = fresh.get(db_index as usize) else {
            return false; // no opened global for the bound slot → cannot decide
        };
        let Some(matched) = msubst.bindings.get(&gvid).cloned() else {
            return false; // the bound var did not match → cannot decide
        };
        // WI-20260911-5G28A — OPEN THE BOUND against the same `fresh` globals the head
        // was opened with. A bound's own type variables are frame slots since this
        // ticket and the stored term is De Bruijn-closed, so reading it raw would ask
        // `types_compatible` about a `DeBruijn(k)` — a variable, hence a permanent
        // `Suspend`, hence a rewrite that never fires. A var-free bound (every bound the
        // rewrite route carries in the corpus) opens to itself.
        let bound_tid = kb.term_from_debruijn(bound_tid, fresh);
        // COLLAPSE, deliberately: a rewrite has two outcomes, so `Suspend` and
        // `Refuted` are both "don't fire" here. The goal reader (WI-742) keeps
        // them apart — that is the whole reason the decision is factored out.
        if type_bound_verdict(kb, msubst, &matched, bound_tid) != TypeBoundVerdict::Holds {
            return false;
        }
    }
    true
}

/// WI-742 — the three-valued answer to "does this value's CARRIED type satisfy
/// this declared bound", the one decision behind both readings of a `?x: T`
/// annotation: WI-582's rewrite guard ([`typed_pattern_bounds_hold`], which
/// collapses it to a bool) and proposal 060 §2's generated `domain(?x, T)` body
/// goal (which needs all three).
///
/// ONE PREDICATE, TWO READERS — not two implementations. The equational and
/// relational readings of the annotation must agree on what it MEANS
/// (`kernel-language.md` §5.3: "the same carried-type decision when `?x` is
/// bound"); a second copy of these four steps is a copy that drifts.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TypeBoundVerdict {
    /// The carried type conforms — keep the binding / fire.
    Holds,
    /// The carried type is determined and does NOT conform — fail this binding.
    Refuted,
    /// Undecidable HERE, not false: one of the two sides is a VARIABLE, so the
    /// relation would answer about everything rather than about this pair. Never
    /// NAF-decided (WI-067) — the rewrite reader declines to fire, the goal reader
    /// suspends and is re-asked by rotation.
    ///
    /// It used to mean "or the bound is not nominal" as well, which is a much wider
    /// set and the wrong one: an arrow or a tuple is a fully determined type that
    /// [`types_compatible`] has an arm for, so withholding on it left rows the guard
    /// exists to reject standing as conditional answers. See [`type_bound_verdict`].
    Suspend,
}

/// [`TypeBoundVerdict`] for one `(value, declared bound)` pair.
///
/// The carried type is [`value_type_term`] (WI-578) — the value's full stored
/// type term, never collapsed to a head symbol. Conformance is the ordinary
/// [`types_compatible`], which is subsort for a nominal sort bound and `provides`
/// for a spec bound; both read load-built relations, so this performs no typing
/// operation in the staging sense (proposal 060's rule).
///
/// WI-20260908-PW9A0 — `domain` RESTRICTS, so the only thing that withholds a verdict
/// is an under-determined SIDE, never a merely non-nominal one. Both guards used to ask
/// `sort_functor_of_view(..).is_none()`, inherited from WI-582 where this returned
/// `bool` for a rewrite and both were `return false` — "don't fire", the safe answer for
/// anything undecided, which loses nothing in a rewrite. WI-742 relabelled them
/// `Suspend` without re-deriving them, and as a GOAL verdict that is a different and
/// stronger claim. MEASURED on a ground fixture with nothing undetermined anywhere: a
/// clause `g(?a: (Int64) -> Int64, ?b)` over two rows of concrete lists returned BOTH as
/// conditional answers — value bound, its type known, the bound known, and no verdict —
/// where the arrow arm of [`types_compatible`] refutes both outright. The `named_tuple`
/// arm is the same story, and its holding direction now works too: a `(x: Int64)` bound
/// keeps a `(x: 1)` row, drops a `(x: true)` one, and drops a list.
///
/// BOTH SIDES, not just the bound. Narrowing only the bound would fix the refutations
/// and leave the one case that should HOLD still suspended: the value side's guard
/// demands a nominal CARRIED type, so an actual function value against an arrow bound
/// would never be admitted.
pub(crate) fn type_bound_verdict(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    value: &Value,
    bound_tid: TermId,
) -> TypeBoundVerdict {
    type_bound_verdict_view(kb, subst, value, &Value::term(bound_tid))
}

/// WI-743 — [`type_bound_verdict`] over a bound READ THROUGH THE VIEW rather than
/// handed in as a `TermId`.
///
/// The `TermId` front is right for WI-742's generated guard, whose bound IS an interned
/// term the loader resolved and the typer spliced. It is wrong for the derived
/// `domain_member` relation's leaf arm, where the type arrives as an ordinary GOAL
/// ARGUMENT — bound by unifying the caller's `List[T = String]` against the derived
/// clause's `List[T = ?T]`, so it rides whatever carrier that unification produced.
/// MEASURED: demanding `Value::Term` there reported a malformed-goal Error on
/// `rule text(?w: List[T = String]) :- ?w <=> ["ab"]` — the element type arrived as a
/// `Value::Node` occurrence and the row came back conditional instead of definite.
///
/// `Value` AND NOT A GENERIC `TermView`, which is what an earlier draft took and what
/// `/code-review` caught: making it generic forced [`type_is_undetermined`] generic too,
/// which replaced its `Value::Term` carrier match with `as_bind_value` — and that
/// UNWRAPS A SPLICED NODE to its interned term and walks it, so a type the predicate
/// used to call determined became undetermined and a definite row became conditional.
/// A `Value` is already a `TermView`, so the leaf arm's carrier reaches
/// `types_compatible` with no change to what either predicate decides.
pub(crate) fn type_bound_verdict_view(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    value: &Value,
    bound: &Value,
) -> TypeBoundVerdict {
    let ty = value_type_term(kb, subst, value);
    // WI-20260908-PW9A0 — SUSPEND IS FOR AN UNDER-DETERMINED SIDE, NOT FOR A NON-NOMINAL
    // ONE, and either side may be the undetermined one. `domain` RESTRICTS: where both
    // sides are determined types there is a verdict, and withholding one leaves a row
    // the guard was written to reject standing as a conditional answer.
    if type_is_undetermined(kb, &ty) || type_is_undetermined(kb, bound) {
        return TypeBoundVerdict::Suspend; // WI-067 — never NAF-decide an open variable
    }
    if types_compatible(kb, &mut Substitution::new(), &ty, bound) {
        TypeBoundVerdict::Holds
    } else {
        TypeBoundVerdict::Refuted
    }
}

/// WI-20260911-5G28A — what a `domain` goal can say about a bound that MENTIONS A TYPE
/// VARIABLE, read in mode **(in, out)**: the value is the INPUT and the type is the
/// OUTPUT, because a value's type is FUNCTIONALLY DETERMINED by the value
/// ([`value_type_term`], WI-578).
///
/// WHY THIS EXISTS. A bound like `List[T = ?t]` reaches [`type_bound_verdict`] with a
/// free `?t`, and that predicate's whole rule (WI-067, WI-20260908-PW9A0) is that an
/// open variable never gets a verdict — so it SUSPENDS, for good, whatever the value is.
/// MEASURED on b43d9670: `my_rule([1, 2], ?r)` answered `?r = [1, 2]` as a CONDITIONAL,
/// carrying `domain([1, 2], List(T: ?t))` twice as an undischarged residual. The value
/// was ground, its type was `List[T = Int64]`, and nothing read it — the bound PARKED
/// instead of deciding.
///
/// AND IT IS A PIN, NOT A VERDICT, which is why it is a separate answer rather than a
/// fourth `TypeBoundVerdict`. WI-067's rule is intact: nothing here decides an open
/// variable. It INSTANTIATES one, from the only thing that can determine it, and then
/// ordinary conformance applies to the instantiated pair. The alternative — letting the
/// goal enumerate the free type over every derived domain — opens one choice point per
/// sort in the KB and was measured at WT8WG item 7 as 20 rows for a `nest` clause whose
/// body binds its variable outright and can have at most ONE answer.
pub(crate) enum TypeBoundPin {
    /// The bound mentions no type variable — this reading does not apply, and the
    /// ordinary [`type_bound_verdict`] owns the pair.
    NotApplicable,
    /// The value's type pins the bound's variables. `pin` is merged into the caller's σ,
    /// so it is visible to every later goal — that is what makes a rule's two columns a
    /// TIE rather than two independent checks. `bound` is the SAME bound resolved through
    /// that pin, handed back so a caller that must re-ask a question ABOUT the type
    /// (`builtin_domain_leaf`'s "does a structural clause own this call") asks it of the
    /// pinned type rather than of the variable it started with.
    Pinned { pin: Substitution, bound: Value },
    /// The value's type is determined and cannot satisfy the bound under ANY pin
    /// (`[1, 2]` against `List[T = ?t]` where σ already holds `?t := String`).
    Refuted,
    /// The value's own type is not determined yet, so it cannot pin anything. Re-asked
    /// by rotation, exactly as [`TypeBoundVerdict::Suspend`] is.
    Suspend,
}

/// [`TypeBoundPin`] for one `(value, bound)` pair — the (in, out) read.
///
/// `unify_types`, not `types_compatible`: the point is to BIND, and the subtype relation
/// treats a variable as a wildcard and binds nothing. The σ handed back is fresh, so a
/// failed unification leaves the caller's own σ untouched (the discipline
/// `types_compatible`'s doc states for its threading callers).
pub(crate) fn pin_bound_from_value(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    value: &Value,
    bound: &Value,
) -> TypeBoundPin {
    if !type_mentions_flex_var(kb, bound) {
        return TypeBoundPin::NotApplicable;
    }
    let ty = value_type_term(kb, subst, value);
    // THE VALUE'S OWN TYPE MUST BE DETERMINED, and this is the same question
    // [`type_bound_verdict_view`] asks of it — an under-determined input cannot pin an
    // output. Without it a value whose carried type is itself a variable would unify the
    // bound with a variable and call that a decision.
    if type_is_undetermined(kb, &ty) {
        return TypeBoundPin::Suspend;
    }
    let mut pin = Substitution::new();
    // WALK THE BOUND THROUGH σ FIRST. A tie is only a tie if the SECOND column sees what
    // the FIRST pinned: `my_rule(?x: List[T = ?t], ?res: List[T = ?t])` checks `?x`,
    // binds `?t := Int64` into the caller's σ, and the `?res` goal must then read `?t`
    // as `Int64` and REFUTE a `["a"]` — not re-bind it to `String`.
    let bound = walk_type_deep_value(kb, subst, bound);
    if pin_type_vars(kb, &mut pin, &ty, &bound) {
        let bound = walk_type_deep_value(kb, &pin, &bound);
        TypeBoundPin::Pinned { pin, bound }
    } else {
        TypeBoundPin::Refuted
    }
}

/// WI-20260911-5G28A — MATCH a determined type against a bound, binding the bound's type
/// VARIABLES to what stands opposite them. One-way, and that is the mode: the value's type
/// is the INPUT and the bound's variables the OUTPUTS.
///
/// NOT [`unify_types`], and the difference is a carrier. `unify_types` recognises a
/// variable through [`resolved_var`], whose occurrence arm reads a **`TypeNode::Var`** —
/// the carrier a TYPE occurrence uses. A source-written `domain(?x, List[T = ?e])` lowers
/// its bound as an ordinary **`Expr`** occurrence, so `?e` arrives as `Expr::Var(Global)`,
/// `resolved_var` answers `None`, and the structural arms compare a variable against
/// `Letter` and REFUSE. MEASURED: `rule varBound(?x) :- ?x <=> [a()], domain(?x,
/// List[T = ?e])` answered 0 rows — a refutation, where WI-067's rule is that an open
/// variable never gets a verdict, let alone that one. (WI-20260911-WT8WG hit the same
/// carrier from the other side and answered it with a DELAY; this reads it instead.)
///
/// So the variable test here is [`type_head`]'s own `FlexVar`, which is carrier-neutral by
/// construction — the same reader `view_has_type_variable` uses for the same shape — and
/// widening `resolved_var` is deliberately NOT the repair: that predicate answers for
/// every unifier in the typer, and an `Expr::Var` is a VALUE variable everywhere except a
/// type position. Here the position is a type by construction.
///
/// A SUBTREE WITH NO VARIABLE IN IT FALLS TO [`types_compatible`], so the parts the author
/// pinned keep the SUBTYPE relation they would have had; only the variable positions are
/// bound. A variable that is already pinned (an earlier column of the same tie) is CHECKED
/// against what stands opposite it rather than re-bound — that is what makes
/// `my_rule([1, 2], ["a"])` refute.
pub(super) fn pin_type_vars(
    kb: &mut KnowledgeBase,
    pin: &mut Substitution,
    ty: &Value,
    bound: &Value,
) -> bool {
    if let Some(vid) = bindable_type_var(kb, bound) {
        let ty_val = walk_type_deep_value(kb, pin, ty);
        return match pin.resolve_as_value(vid).cloned() {
            Some(prev) => types_compatible(kb, pin, &ty_val, &prev),
            None => bind_resolved(kb, pin, vid, ty_val),
        };
    }
    if !type_mentions_flex_var(kb, bound) {
        return types_compatible(kb, pin, ty, bound);
    }
    let (
        ViewHead::Functor {
            functor: bf,
            pos_arity: bp,
            named_arity: bn,
        },
        ViewHead::Functor {
            functor: tf,
            pos_arity: tp,
            named_arity: tn,
        },
    ) = (bound.head(kb), ty.head(kb))
    else {
        return false;
    };
    // SAME HEAD, SAME SHAPE — or this is not a PIN at all, and the question falls back to
    // the relation it would have had.
    //
    // THE FALLBACK IS NOT BELT-AND-BRACES, it is what keeps SUBTYPING (`/code-review` on
    // this ticket's first cut). The structural descent below is exact equality on the head
    // and the arities, where `type_bound_verdict_view` used `types_compatible` — which
    // honours `nothing`-is-bottom and nominal widening. Without the fallback, a value whose
    // type is a strict subtype with a different head, or `Nothing` (a body ending in
    // `Error.raise`), came back `Refuted` where it used to HOLD — and since
    // `expand_unwritten_type_params` now turns every bare `?x: List` into `List[T = ?t]`,
    // that narrowing would have reached bounds no author changed.
    //
    // NOTHING IS PINNED ON THAT PATH, which is the honest outcome: a subtype relation that
    // is not a structural match supplies no value for the variable, and inventing one would
    // be inventing an answer. `pin` is threaded in, so a partial bind made before the
    // mismatch can survive into the `types_compatible` call — that is the same
    // early-return-on-false discipline `types_compatible`'s own doc states for its
    // threading callers, and the caller discards σ on `false`.
    if bf != tf || bp != tp || bn != tn {
        return types_compatible(kb, pin, ty, bound);
    }
    for i in 0..bp {
        let (Some(b), Some(t)) = (bound.pos_arg(kb, i), ty.pos_arg(kb, i)) else {
            return types_compatible(kb, pin, ty, bound);
        };
        let (b, t) = (b.to_value(), t.to_value());
        if !pin_type_vars(kb, pin, &t, &b) {
            return false;
        }
    }
    // BY SHORT NAME, not by `Symbol` identity, and that is the neighbour's own rule:
    // `parameterized_compatible_view` matches a binding with
    // `short_name_of(kb.local_name_of(*p)) == short` for exactly this reason. The two sides
    // of a comparison reach their parameter keys through different resolutions — a rule's
    // stored bound and an operation parameter's filled slot both spell `T` and can carry
    // two `Symbol`s for it. MEASURED with raw-symbol lookup: the RIGID rows
    // (`op(x: List, y: List) -> List[T = x.T]`) fell out of the named loop on the very
    // first key, took the `types_compatible` fallback, and were refused at the column bind
    // — while the CONCRETE row, whose argument type came from the same place as its column
    // type, passed. Found by this ticket's own suite after `/code-review`'s fix landed.
    let ty_keys: Vec<Symbol> = ty.named_keys(kb);
    for key in bound.named_keys(kb) {
        let short = short_name_of(kb.local_name_of(key)).to_string();
        let t_key = ty_keys
            .iter()
            .copied()
            .find(|k| short_name_of(kb.local_name_of(*k)) == short);
        let (Some(b), Some(t)) = (
            bound.named_arg(kb, key),
            t_key.and_then(|k| ty.named_arg(kb, k)),
        ) else {
            return types_compatible(kb, pin, ty, bound);
        };
        let (b, t) = (b.to_value(), t.to_value());
        if !pin_type_vars(kb, pin, &t, &b) {
            return false;
        }
    }
    true
}

/// WI-20260908-PW9A0 — is this type a VARIABLE, the one thing
/// [`type_bound_verdict`] must withhold judgment on?
///
/// The predicate borrows [`types_compatible`]'s own: its `type_var` arm is a WILDCARD
/// returning `true`, so a variable on either side makes the relation say "compatible"
/// about everything, which is not a verdict. `FlexVar` is an open inference variable and
/// means the same; `Skolem` is included conservatively — a rigid variable has no arm
/// either, so deciding it would rest on the `_ => false` catch-all rather than on a rule.
///
/// EVERY OTHER SHAPE IS DETERMINED and gets a real answer: `arrow` and `named_tuple` have
/// their own subtyping arms, and a shape with no arm falls to `false`, which for a bound
/// the value does not satisfy is the RIGHT answer — the guard restricts.
fn type_is_undetermined(kb: &KnowledgeBase, ty: &Value) -> bool {
    if !type_head_is_decidable(kb, ty) {
        return true;
    }
    match ty {
        Value::Term { id, .. } => type_term_has_variable(kb, *id),
        // A `Value::Node` carrier is a value-in-type occurrence; its own head was
        // tested above and its children are occurrences rather than type terms, so
        // there is nothing further to walk here.
        _ => false,
    }
}

/// WI-20260908-PW9A0 — does this type's HEAD have a decision procedure in
/// [`types_compatible`] that means something for a `domain` guard?
///
/// AN ALLOWLIST, NOT A DENYLIST, and that is the whole design. The obvious spelling is
/// "withhold on the shapes that cannot be judged", which requires enumerating them —
/// and every shape left off that list silently acquires a VERDICT it never had. There
/// are seven such shapes here, `/code-review` found them one at a time, and each is a
/// different wrong answer: `nothing` is a subtype of everything, so it would HOLD
/// against every bound and fire every typed pattern on a value that cannot exist;
/// `expr_carried` / `rigid_type_projection` are rigid unknowns that `expr_carried_zeta`
/// actively REFUSES against a concrete type, silently dropping rows that should have
/// floundered loudly; `poly_type` is named in `type_dispatch_name_view` precisely so it
/// "must never MATCH `arrow`" — a deliberate non-answer, not a claim of non-conformance;
/// and `Error` is reserved for malformed user input (WI-391), where a quiet "does not
/// conform" is the silent skip this repo's rules forbid.
///
/// So the question is asked the other way round. The four shapes below are the ones a
/// bound is written in and `types_compatible` genuinely relates — nominal (`bare_sort_
/// compatible`, `parameterized_compatible_view`) and structural (`arrow_compatible_view`,
/// `named_tuple_compatible`). EVERYTHING ELSE SUSPENDS, which is exactly what it did
/// before this ticket, so the widening is confined to the two structural shapes it is
/// FOR — and those two have driven rows either way (hold, refute, and refute on a nested
/// field). A shape added to `TypeHead` later withholds by default and has to be admitted
/// deliberately, rather than picking up a verdict by omission.
fn type_head_is_decidable<V: TermView>(kb: &KnowledgeBase, ty: &V) -> bool {
    matches!(
        type_head(kb, ty),
        TypeHead::SortRef(_)
            | TypeHead::Parameterized { .. }
            | TypeHead::Arrow
            | TypeHead::NamedTuple
    )
}

/// WI-20260908-PW9A0 — [`type_is_undetermined`]'s recursion over a hash-consed type
/// term's ARGUMENTS.
///
/// NOT `KnowledgeBase::value_is_ground`, and the difference is the whole point:
/// groundness is a question about the TERM, determinacy is a question about the TYPE,
/// and a type variable is a perfectly GROUND term that denotes an unknown type.
/// MEASURED — for `f((x: ?y))` against a `(x: Int64)` bound the carried type is
/// `named_tuple(x: <type var>)`, and `value_is_ground` answers `true` for it, so routing
/// this question through that owner admitted exactly the row it was meant to withhold.
///
/// A type's arguments are its `Term::Fn` children on both spellings — a parameterized
/// type IS `Fn{base, named bindings}` (WI-361, there is no `parameterized(..)` wrapper),
/// a `named_tuple`'s fields and an `arrow`'s parts ride the same way — so one child walk
/// covers every shape rather than a per-shape list that a new form could fall out of.
fn type_term_has_variable(kb: &KnowledgeBase, t: TermId) -> bool {
    // [`is_type_variable`], NOT [`type_head_is_decidable`] — the two ask different
    // questions and this walk wants the second-order one. MEASURED by trying the
    // allowlist here: an ARROW's children include its EFFECTS ROW, which is not a shape
    // a bound is written in and so is not on the allowlist, so every arrow bound
    // withheld and the two rows this ticket exists to fix went back to suspending. What
    // a child must not be is a WILDCARD — the thing that makes `types_compatible` answer
    // `true` about everything — and that is a variable.
    term_any_subterm(kb, t, &|t, _| is_type_variable(kb, &TermIdView(t)))
}

/// named_tuple(fields: [...]) <: named_tuple(fields: [...])
/// Width subtyping: actual may have more fields than expected.
/// Depth subtyping: each expected field's type must be a supertype of actual's.
/// WI-342: the sole `named_tuple` subtyping, carrier-agnostic over [`TermView`].
/// NAME-KEYED width subtyping: every `expected` component must appear in
/// `actual` with a compatible type, and `actual`'s extras — dropped from
/// ANYWHERE — are not observed (WI-804). Order is not part of `<:`; the
/// order-PRESERVING scan is an interim holding permutation back until
/// destructuring binds by label, NOT a claim that `<:` is ordered. The
/// equal-arity variant, which lets a named-binder callback arrow's contravariant
/// param check accept a multi-param op's eta arrow, belongs to
/// [`arrow_params_compatible`] (WI-775) as [`TupleAlign::PARAM_LIST`].
pub(super) fn named_tuple_compatible<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &B,
) -> bool {
    named_tuple_compatible_as(kb, subst, actual, expected, TupleAlign::DATA)
}

/// [`named_tuple_compatible`] with the alignment stated explicitly — `PARAM_LIST`
/// only from [`arrow_params_compatible`], where the tuples are parameter lists.
fn named_tuple_compatible_as<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &B,
    mode: TupleAlign,
) -> bool {
    let actual_fields = named_tuple_fields(kb, actual);
    let expected_fields = named_tuple_fields(kb, expected);
    match align_named_tuple_slots(kb, &actual_fields, &expected_fields, mode) {
        Some(slots) => aligned_pairs(&slots, &actual_fields, &expected_fields)
            .all(|(act_type, exp_type)| types_compatible(kb, subst, act_type, exp_type)),
        None => false,
    }
}

/// WI-775: the subtyping twin of [`unify_arrow_params`] — a `<:` between two
/// arrow PARAMETER LISTS. WI-782: the alignment is POSITIONAL with equal arity
/// (no by-name rung), admitted when the names line up or one side carries the
/// synthetic `_1.._n` convention. See [`align_named_tuple_slots`].
///
/// Argument order is `sub <: super`, exactly as [`types_compatible`] takes it,
/// and this function does NOT perform the contravariant swap — the CALLER does,
/// passing the expected arrow's param list as `sub`. Hence the neutral names:
/// at the two arrow call sites `sub` is bound to the EXPECTED arrow's params.
/// Do not "fix" that by swapping the forwarded arguments; it would invert arrow
/// subtyping silently.
pub(super) fn arrow_params_compatible<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    sub: &A,
    sup: &B,
    arity: usize,
) -> bool {
    // NOTE the deliberate asymmetry with [`unify_arrow_params`], which walks
    // before classifying: there, a bound-var param slot would fall through to
    // `unify_types` and be REJECTED under name alignment, so walking restores
    // the pre-WI-775 verdict. Here the fallthrough is `types_compatible`, whose
    // `type_var` arm is a wildcard returning `true` — the pre-WI-775 verdict
    // already. Walking would make this path STRICTER than it has ever been, on
    // inputs no measurement covers, so it stays unwalked.
    // WI-791: at arity one the slot is the sole parameter's TYPE, not a list —
    // fall through to `types_compatible`, which relates a tuple there as the DATA
    // it is (by name, width-subtyping). See `unify_arrow_params` for the two
    // measured programs this restores.
    if arity != 1 && both_named_tuples(kb, sub, sup) {
        return named_tuple_compatible_as(kb, subst, sub, sup, TupleAlign::PARAM_LIST);
    }
    types_compatible(kb, subst, sub, sup)
}

// ── Unified type checking ──────────────────────────────────────

//! Constructor applications: tuple and sequence literals, provision projections for
//! spec arguments, and `check_constructor_iter`.

use super::*;

/// Tuple-literal special case routed from `check_constructor_iter`:
/// empty tuple → `Unit`; populated tuple → `named_tuple` whose fields
/// are `_0, _1, …` for positional args and the source label for named
/// args.
fn check_tuple_literal_constructor(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    flow: &FlowEnv,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
    expected: Option<Value>,
    occ: &Rc<NodeOccurrence>,
) -> Result<TypeResult, TypeError> {
    if pos_results.is_empty() && named_results.is_empty() {
        let unit_ty = kb.make_sort_ref_by_name("anthill.prelude.Unit");
        return Ok(TypeResult::pure(unit_ty, env.clone(), Rc::clone(occ)));
    }

    // WI-714 (proposal 052) — the tuple a distribute-dot `r.(f1, f2)` desugared into is a
    // PROJECTION of `r`, not a tuple of `r`'s columns. Recognized by the mark `convert.rs`
    // left on it (WI-762), since the desugared term is identical to the hand-written tuple;
    // anything unmarked falls through to ordinary tuple typing unchanged.
    //
    // Runs FIRST for a reason that survives the provenance change: every `rel.c` field types
    // cleanly ON ITS OWN, as an independent single-column projection (WI-714's fourth
    // dot-dispatch mode), so a pass that ran after them would have already committed to the
    // tuple-of-relations reading. The ordering picks the whole-tuple reading over the
    // field-by-field one — it is NOT, as this comment once said, about the fields failing.
    //
    // NOTE the `collect_arg_errors` below is redundant: `check_constructor_iter` runs the
    // same aggregation before routing here, so every result is already `Ok` on entry (which
    // is what lets the recognizer treat a missing typed field as impossible rather than as a
    // case to retreat from). Kept as the local restatement of that invariant.
    if let Some(r) = try_relation_projection_tuple(
        kb,
        env,
        flow,
        pos_results.len(),
        named_args,
        named_results,
        occ,
    ) {
        return r;
    }

    collect_arg_errors(pos_results.iter().chain(named_results.iter()))?;

    // Collect (field label, result) eagerly — interning the positional `_i`
    // labels here releases the `kb` borrow before the `named_tuple_value` build
    // below also needs `&mut kb` (WI-342).
    // WI-355: 1-based positional names `_1`, `_2`, … (spec §4.5) so the tuple
    // value's type unifies (by name) against a tuple-typed / arrow param.
    let mut labeled: Vec<(Symbol, &TypeResult)> = Vec::new();
    for (i, r) in pos_results.iter().enumerate() {
        labeled.push((
            kb.intern(&positional_label(i)),
            r.as_ref().expect("aggregator"),
        ));
    }
    for ((name, _), r) in named_args.iter().zip(named_results.iter()) {
        labeled.push((*name, r.as_ref().expect("aggregator")));
    }

    // WI-462: thread the EXPECTED tuple component types into the elements. A component's
    // inferred type can be a free var (`cons(h, t)` over a bare `xs : List` binds `h` to a
    // fresh `?_`); the declared return `(xs.T, …)` carries the real type, but the later
    // conformance check (`types_compatible`) does NOT bind a var — it only subtype-checks,
    // and a raw `Var::Global` is not a wildcard there. So unify each element's type against
    // its expected component, binding the free var (`h ⟹ xs.T`), then walk it into the built
    // tuple type. (A `pair(h, t)` constructor threads this way for free — its build seeds
    // the expected; a tuple literal has no constructor to do so.) No / non-tuple expected
    // leaves the inferred types unchanged — as does an expected the conformance relation
    // will refuse anyway (WI-800): the correspondence is that relation's own.
    let exp_fields: Vec<(Symbol, Value)> = match &expected {
        Some(e) if matches!(extract_type(kb, e), TypeExtractor::NamedTuple(_)) => {
            named_tuple_fields(kb, e)
        }
        _ => Vec::new(),
    };
    // WI-342: carrier-agnostic field types (carry a `Value::Node` field). This IS the list
    // the tuple type is built from, so threading writes through it rather than into a
    // parallel copy — and it is the same list conformance reads back off that type.
    let mut tuple_fields: Vec<(Symbol, Value)> = labeled
        .iter()
        .map(|(label, r)| (*label, r.ty.clone()))
        .collect();
    let mut tsubst = Substitution::new();
    thread_expected_tuple_fields(kb, &mut tsubst, &mut tuple_fields, &exp_fields);
    // Effects merge in a SECOND pass. They used to interleave with the threading, one
    // component at a time; the two are independent and the split is safe, which is worth
    // stating rather than leaving to be re-derived: threading's substitution is the local
    // `tsubst` and never reaches effect merging, and both only ever ADD to `kb`, whose
    // terms are hash-consed by structure — so allocation ORDER is not observable.
    let mut effects: Vec<Value> = Vec::new();
    for (_, r) in &labeled {
        merge_effects_into(kb, &mut effects, &r.effects);
    }
    let tuple_ty = named_tuple_value(kb, &tuple_fields, occ.span, occ.owner);
    Ok(TypeResult {
        ty: tuple_ty,
        env: env.clone(),
        effects,
        node: Rc::clone(occ),
    })
}

/// WI-20260826-7JDWY — WHICH COLLECTION-LITERAL SURFACE is being typed.
///
/// The `T` of a `List` and the `T` of a `Set` are the same question, asked of two
/// surfaces, so one owner answers both and only the prelude sort and the word in the
/// diagnostic differ. It replaces a `base_name: &str` parameter that could be handed any
/// string at all — the two call sites of [`check_seq_literal_constructor`] each passed a
/// literal, and nothing tied that string to the literal surface the caller had matched on.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum SeqLiteral {
    List,
    Set,
}

impl SeqLiteral {
    /// The prelude sort a literal of this surface is typed at.
    pub(super) fn base_name(self) -> &'static str {
        match self {
            SeqLiteral::List => "anthill.prelude.List",
            SeqLiteral::Set => "anthill.prelude.Set",
        }
    }

    /// The word the element diagnostic names the construct by
    /// ([`TypeErrorContext::CollectionElement`]).
    pub(super) fn construct(self) -> &'static str {
        match self {
            SeqLiteral::List => "list",
            SeqLiteral::Set => "set",
        }
    }
}

/// WI-20260826-7JDWY — THE ELEMENT TYPE A POSITION DECLARES FOR A `[…]` / `{…}`, or `None`
/// where it declares none.
///
/// The `T` binding of an expectation whose HEAD is a collection — `anthill.prelude.List` or
/// `anthill.prelude.Set`. The head test is a correction `/code-review` found: reading `T`
/// off any expectation at all meant an unrelated type parameter was pushed down and then
/// BLAMED ON AN ELEMENT. Measured, `operation mk() -> Option[T = List[T = Int64]] = [1]`
/// reported `list.element 1 … expected List[T = Int64], got Int64` — an "expected" lifted
/// off `Option`'s parameter, about a list that is not in the program. The VERDICT was right
/// either way (the container mismatch is refused on both sides); the message named the
/// wrong thing, and a diagnostic that blames an element must be reading that element's own
/// declaration.
///
/// THE LITERAL'S OWN SORT, not "either collection" — the narrowing `/code-review` asked
/// for, and the same complaint as the head test itself. §4.6's "a `[…]` written in a
/// `Set[T = X]` position is left as it stands" is about the LOADER's lowering; at the typer
/// a `[…]` is always `List`-typed, so a `Set`-headed expectation is a SHAPE disagreement
/// and its `X` is not this literal's element type. Reading it as one made
/// `-> Set[T = Int64] = [1, "x"]` report `(collection-element)` — the tag that says a
/// declaration named `Int64` — when nothing declared anything about this literal's
/// elements. It is refused either way and by the elements either way (they have no join);
/// what changes is that the tag stops claiming a declaration that does not exist.
///
/// A head that is anything else declares nothing about ELEMENTS, so the literal types from
/// its elements and is checked as a whole where it is consumed — the reading it had before
/// this ticket, and the one whose message names the container.
///
/// ONE OWNER BECAUSE TWO SITES MUST AGREE: [`visit_type`] pushes this down as each
/// element's own `expected`, and [`seq_literal_element_type`] CHECKS each element against
/// it. Computed differently, an element would be typed under an expectation it is not then
/// judged by, or judged by one it never saw.
pub(super) fn declared_element_type(
    kb: &KnowledgeBase,
    kind: SeqLiteral,
    expected: Option<&Value>,
) -> Option<Value> {
    let exp = expected?;
    let base = match type_head(kb, exp) {
        TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => s,
        _ => return None,
    };
    if kb.qualified_name_of(base) != kind.base_name() {
        return None;
    }
    extract_type_param(kb, exp, "T")
}

/// WI-285 / WI-289 / WI-20260826-7JDWY — THE ELEMENT TYPE AND EFFECTS OF A COLLECTION
/// LITERAL, and the ONE place that rule is stated.
///
/// **THREE CARRIERS, ONE RULE.** A `[…]` / `{…}` reaches the typer as an
/// `Expr::ListLit` / `Expr::SetLit` occurrence ([`TypeBuildFrame::ListLit`] /
/// [`TypeBuildFrame::SetLit`], WI-285) or as an un-lowered
/// `constructor(ListLiteral | SetLiteral, …)` ([`check_seq_literal_constructor`],
/// WI-289). The rule about what its elements type at is one rule, and it had been
/// written out three times. WI-20260826-7JDWY is what that cost: the ticket named the
/// build frames as the site to fix, and MEASURED REACHABILITY says they are nearly inert.
/// Instrumented over the whole workspace suite, the two frames are entered **4** times,
/// every one of them with NO declared element type to overwrite; the constructor carrier
/// is entered **964** times, **605** of them with a declaration, covering **13693**
/// elements. The defect the ticket describes is real at all three, but a repair made only
/// where it was named would have compiled, reviewed clean, and changed nothing an author
/// can write.
///
/// **THE HINT IS WHAT THE POSITION DECLARES, AND THE ELEMENTS ARE CHECKED AGAINST IT.**
/// Before this ticket `element_hint` was taken as the element type unconditionally and
/// the elements were walked only to merge effects, so a hint did not CHECK the literal,
/// it OVERWROTE it: `operation mk() -> List[T = Int64] = ["x"]` loaded clean and
/// `List.head(mk())` answered `Str("x")` from a slot the signature types `Int64`. The
/// judgement here is [`validate_arg_against_param`] — the same relation an argument gets
/// against a declared parameter — so the groundness gate and the boundary conversions are
/// the ones already in force elsewhere and not a second opinion about what conforms.
///
/// **THE HINT IS STILL THE ELEMENT TYPE WHEN IT CONFORMS, WHICH IS NOT THE SAME AS
/// "PREFER THE ELEMENTS".** `-> List[T = Colour] = [red(v: 1), blue(v: 2)]` must keep
/// working: its elements type at two different constructors and only the declared
/// `Colour` covers both, so a repair that took the elements' own types would have to
/// invent a join. The declaration is the answer; the elements are the check.
///
/// **A `WrapSome` IS REPORTED, NOT INSERTED — AND THAT IS A DECISION, NOT AN OBSTACLE.**
/// A bare `T` in a `List[T = Option[T]]` literal is the WI-408 coercion's shape, and every
/// position that takes it rebuilds the argument occurrence around a synthesized `some(…)`.
/// An earlier version of this note claimed this position STRUCTURALLY could not — that its
/// node is returned unrebuilt — and `/code-review` showed that false: the `occ` handed to
/// [`check_seq_literal_constructor`] is already a `reassemble_children` of its typed
/// element results, and both build frames reassemble too, so a wrapped child would
/// propagate exactly as it does at an argument.
///
/// What actually decides it is that inserting the wrap is a NEW capability with an EMPTY
/// population — measured, zero elements in the workspace corpus reach this arm — while
/// what it replaces is a program that LOADED and left the element bare at runtime.
/// Reporting is the loud outcome and needs no census; inserting would need one, and a
/// second decision about whether a collection element should coerce at all. The message is
/// the pair (`expected Option[T = Int64], got Int64`), from which the remedy is the
/// explicit `some(…)` — it does not spell that out, which is a diagnostic shortfall and
/// the one thing here worth improving later.
///
/// The FIRST non-conforming element is reported, at ITS OWN span — a `TypeResult` carries
/// one error, the same shape `collect_arg_errors` imposes on every other child group.
/// WI-20260829-WBXGX — did this join ERASE a parameterization rather than combine one?
///
/// [`join_parameterized_same_base`] falls back to the BARE base sort when a binding cannot
/// be combined, so `Option[T = Int64] ⊔ Option[T = String]` is `Option` — and a bare sort
/// CONFORMS TO EVERY INSTANTIATION. As a literal's element type that launders exactly what
/// this ticket exists to catch: found by `/code-review`,
/// `takeOpts([some(1), some("x")])` against `List[T = Option[T = Int64]]` loaded, and so did
/// the REVERSED spelling, which was refused before the join went in. Order-independence
/// bought by making the refusing order accept is not the order-independence this ticket
/// wanted.
///
/// A SOUND UPPER BOUND IS NOT A SOUND ELEMENT TYPE, and the difference is what each is for.
/// A branch join answers "what can this expression be", where the bare `Option` is honest
/// and nothing further is claimed. A literal's element type is then compared against a
/// DECLARATION, and there the erasure passes a `String` into an `Int64` slot. So the
/// erasure is refused HERE and left alone in [`compute_branch_join_type`], where the same
/// fallback is reachable through `if` — MEASURED, not assumed
/// (`an_if_join_still_erases_and_that_is_not_this_tickets_hole` pins it) — because that is
/// the branch join's own question and its own item.
/// WI-20260829-WBXGX — the element type of a literal so far, extended by one more element:
/// their JOIN, or `None` where they have none THAT IS USABLE AS AN ELEMENT TYPE.
///
/// One owner so the occurrence path ([`seq_literal_element_type`]) and the value path
/// ([`seq_literal_value_type`]) cannot come to disagree about what "these elements have a
/// common type" means — they differ only in what they DO with the `None`, which is the one
/// thing that genuinely differs between a program and a runtime value.
///
/// IT IS JUST [`join_types`], and that is the finding rather than an omission. It briefly
/// carried two things of its own — an identity fast path and a filter rejecting a join that
/// ERASED a parameterization — and both belonged in the lattice: the fast path because
/// every caller wants it, the filter because `Option[T = Int64] ⊔ Option[T = String] = S`
/// was not a defect of literals but of the LUB (see [`SameBaseCombine::NoCombination`]).
/// Fixing them there also closed the `if`/`match` twin, which the literal-local version
/// could not reach and had to record as a known gap.
pub(super) fn combine_element_types(
    kb: &mut KnowledgeBase,
    acc: &Value,
    next: &Value,
) -> Option<Value> {
    join_types(kb, acc.clone(), next.clone())
}

pub(super) fn seq_literal_element_type(
    kb: &mut KnowledgeBase,
    kind: SeqLiteral,
    element_hint: Option<Value>,
    elements: &[Result<TypeResult, TypeError>],
) -> Result<(Value, Vec<Value>), TypeError> {
    let mut effects: Vec<Value> = Vec::new();
    // WI-342: keep the element type carrier-agnostic so a `Value::Node` element (e.g. a
    // list of effectful lambdas) is CARRIED, not re-grounded.
    let mut inferred: Option<Value> = None;
    for (index, r) in elements.iter().enumerate() {
        // The caller has already surfaced any `Err` child (`collect_arg_errors`).
        let r = r.as_ref().expect("aggregator");
        match &element_hint {
            Some(hint) => {
                let context = TypeErrorContext::CollectionElement {
                    construct: kind.construct(),
                    index,
                    source: ElementTypeSource::Declared,
                };
                // The ELEMENT's own span, not the literal's — with three elements the
                // literal's span names the whole `[…]` and leaves the reader counting.
                let span = Some(r.node.span.span);
                let mut subst = Substitution::new();
                match validate_arg_against_param(
                    kb,
                    &mut subst,
                    &r.ty,
                    hint,
                    span,
                    context.clone(),
                    Some(&r.node),
                ) {
                    ArgValidation::Ok => {}
                    ArgValidation::Fail(e) => return Err(e),
                    // See the `WrapSome` paragraph above: reported, not inserted.
                    ArgValidation::WrapSome { declared } => {
                        return Err(TypeError::TypeMismatch {
                            site: TypeError::here(),
                            span,
                            context,
                            expected: declared,
                            denoted: denoted_type_value(kb, Some(&r.node)),
                            actual: r.ty.clone(),
                        })
                    }
                }
            }
            // WI-20260829-WBXGX — NO DECLARATION, SO THE ELEMENTS DECIDE: the element type
            // is the JOIN of them, and the first element with no join is refused at its own
            // span. Before this it was element ONE's type and the rest rode free, so
            // `takeInts([1, "a"])` against `List[T = Int64]` LOADED CLEAN with a `String` in
            // an `Int64` slot — while `takeInts(["a", 1])`, the same two elements in the
            // other order, was refused. Order-dependence was the tell.
            //
            // THE JOIN, NOT A SUBTYPE TEST AGAINST ELEMENT ONE, and the ticket prescribed
            // the latter on the ground that "anthill has no join today". It has one:
            // [`join_types`], which [`compute_branch_join_type`] already gives `if` and
            // `match` arms — the neighbouring construct that asks this exact question of
            // several expressions at once. A subtype test against element one would have
            // KEPT an order-dependence, only a different one: `[r, c]` with `r: Colour.red`
            // and `c: Colour` would refuse while `[c, r]` loads. MEASURED, not predicted —
            // built that alternative and ran the pair; see
            // `wi_wbxgx_collection_literal_element_join_test`, whose order-independence rows
            // are what separates the two repairs.
            //
            // THE WIDENING DIRECTION IS INERT ON THIS CORPUS: instrumented over the whole
            // workspace suite before the change, 4 literals reach this comparison at all and
            // every one CLASHES; none widens. THAT IS A CENSUS OF WHAT EXISTS, NOT A SAFETY
            // ARGUMENT — `/code-review` was right to separate the two. What an author can
            // write reaches the widening immediately, and one shape of it is a FAIL-OPEN
            // that [`join_erases_a_parameterization`] now refuses; read the census as "no
            // corpus program's type moved", which is all it says.
            None => match inferred.take() {
                None => inferred = Some(r.ty.clone()),
                Some(acc) => match combine_element_types(kb, &acc, &r.ty) {
                    Some(joined) => inferred = Some(joined),
                    None => {
                        return Err(TypeError::TypeMismatch {
                            site: TypeError::here(),
                            span: Some(r.node.span.span),
                            context: TypeErrorContext::CollectionElement {
                                construct: kind.construct(),
                                index,
                                source: ElementTypeSource::Siblings,
                            },
                            expected: acc,
                            denoted: denoted_type_value(kb, Some(&r.node)),
                            actual: r.ty.clone(),
                        })
                    }
                },
            },
        }
        merge_effects_into(kb, &mut effects, &r.effects);
    }
    let element = element_hint.or(inferred).unwrap_or_else(|| {
        // WI-20260904-50B2K — DELIBERATELY STILL A `type_var`, FLIPPED AND MEASURED INERT.
        // An EMPTY literal has no element to infer FROM, so the census that put `?T` in the
        // "to be inferred, must commit" column had it in the wrong one: its type is
        // genuinely unconstrained, which is part (c)'s question.
        //
        // The flip to `Term::Var(Var::Global(..))` was BUILT and run over the whole
        // `wi_tests` binary: 4127/0, and byte-identical diagnostics on every shape that
        // could tell the two apart. Both readings accept the same programs for OPPOSITE
        // reasons — the inert form is compatible-with-anything, the variable is NON-GROUND
        // so the check is withheld — and a shape mismatch is refused under both, because
        // the head (`List` / `Set`) is concrete and `nominal_head_mismatch` decides on the
        // head whatever the binding is:
        //
        //     let xs = []  … used as List[Int64] AND as List[String]   loads, both
        //     addI([], 1)  where addI declares Int64                   refused, both
        //
        // A CHANGE WITH NO WITNESS IS NOT A FIX (CLAUDE.md: a branch you cannot drive), so
        // it is not made. What DOES change here is part (c)'s job: generalizing `[]` to
        // `∀T. List[T]` replaces this mint, and until then the inert form is the closest
        // thing to that ∀ the typer has.
        //
        // MEASURED REACHABILITY, as WI-20260904-50B2K measured it PER CARRIER before the
        // three were merged here: EIGHT reaches across the whole `wi_tests` binary, every
        // one of them through the constructor carrier and none through either build frame.
        let fresh = kb.intern("?T");
        Value::term(kb.make_type_var(fresh))
    });
    Ok((element, effects))
}

/// WI-393 — the literal's own type, `List[T = elem]` / `Set[T = elem]`, at the QUALIFIED
/// prelude sort.
///
/// A bare `"List"` / `"Set"` interns a symbol whose qualified name is itself, which
/// `canonical_sort_sym` (keyed on qualified name) never folds onto the prelude sort — so a
/// literal consumed as a `Stream` (`collect([1, 2, 3])`) failed the carrier provider
/// lookup that a written `List[T]` parameter passes. One owner, so the three literal
/// carriers cannot come to disagree about which symbol they are typed at — the value-level
/// [`seq_literal_value_type`] included, which is the FOURTH and was open-coding these three
/// calls until `/code-review` read the "one owner" claim beside it.
pub(super) fn seq_literal_type(
    kb: &mut KnowledgeBase,
    kind: SeqLiteral,
    element: Value,
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Value {
    let base = kb.make_sort_ref_by_name(kind.base_name());
    let t_sym = kb.intern("T");
    parameterized_value(kb, base, &[(t_sym, element)], span, owner)
}

/// Type a `ListLiteral` / `SetLiteral` that reached the constructor checker
/// (un-desugared `[...]` / `{...}`) as `base[T = elem]`. Mirrors the `Expr::ListLit` /
/// `Expr::SetLit` build frames — [`seq_literal_element_type`] is the ONE owner all three
/// share, and it is where the element type is decided and, where the position declares
/// one, CHECKED (WI-20260826-7JDWY). (WI-289)
///
/// THIS IS THE CARRIER A SOURCE LITERAL ACTUALLY ARRIVES ON, which the census in
/// [`seq_literal_element_type`] measures. The loader lowers `[…]` to a `cons`/`nil` spine
/// only where a declaration names a `List` in a rule / fact data slot (§4.6, WI-1096), so
/// an operation body's literal stays a `constructor(ListLiteral, …)` and reaches here —
/// which is why fixing only the build frames the ticket named would have changed nothing
/// an author can write.
pub(super) fn check_seq_literal_constructor(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    pos_results: &[Result<TypeResult, TypeError>],
    expected: Option<Value>,
    occ: &Rc<NodeOccurrence>,
    kind: SeqLiteral,
) -> Result<TypeResult, TypeError> {
    // Defensive (the constructor checker already surfaced arg errors before
    // routing here): never `.expect` an `Err` element result.
    collect_arg_errors(pos_results.iter())?;
    let element_hint = declared_element_type(kb, kind, expected.as_ref());
    let (t_val, effects) = seq_literal_element_type(kb, kind, element_hint, pos_results)?;
    let seq_type = seq_literal_type(kb, kind, t_val, occ.span, occ.owner);
    Ok(TypeResult {
        ty: seq_type,
        env: env.clone(),
        effects,
        node: Rc::clone(occ),
    })
}

/// WI-594: is `member` (a short type-parameter name of `sort`) an EFFECT-ROW
/// parameter (`effects E = ?`) rather than an ordinary sort parameter (`sort T =
/// ?`)? The loader desugars `effects E = ?` to a `requires EffectsRuntime[Effects
/// = E]` kind-anchor (WI-320), a DIRECT requires of the declaring sort; a sort
/// parameter carries none. So `member` is an effect row iff `sort`'s OWN
/// (direct) requires has an `EffectsRuntime` entry whose `Effects` binding names
/// `member`. Used to decide whether a bare receiver's self-projection threads the
/// member as a bare projection (`s.T`) or as the single-label effect row `{s.E}`
/// (see [`bare_spec_arg_self_projection`]).
///
/// The chain is the DIRECT one, not the transitive `requires_chain`: a TRANSITIVELY
/// required spec's own `effects A` anchor would otherwise leak into `sort`'s chain
/// and — combined with the short-name match — misclassify `sort`'s own `sort A`
/// parameter as an effect row whenever the short names collide. Within a single
/// sort's direct params the short names are unique, so the short-name compare is
/// exact here (and more robust than symbol identity, which can differ across the
/// param's registrations).
pub(super) fn sort_param_is_effect_row(kb: &mut KnowledgeBase, sort: Symbol, member: &str) -> bool {
    let Some(effects_runtime) = effects_runtime_sym(kb) else {
        return false;
    };
    for entry in direct_requires_chain(kb, sort) {
        if !same_sort_canonical(kb, entry.required_sort, effects_runtime) {
            continue;
        }
        if let Some(v) = spec_binding_value(kb, &entry.spec, "Effects") {
            if let Some(head) = spec_binding_head_sym(kb, v) {
                if short_name_of(kb.local_name_of(head)) == member {
                    return true;
                }
            }
        }
    }
    false
}

/// WI-20260923-32XFQ — the constructor field a receiver projection threads into: `(spec
/// base, its bindings)` when the declared field type APPLIES a spec (`Stream[Src, ES]`),
/// else `None` — a bare-sort field has no params to thread, and a structural field (arrow /
/// row) is not a receiver slot. The prologue [`bare_spec_arg_self_projection`],
/// [`carrier_arg_provision_projection`] and [`bare_spec_arg_provision_projection`] each
/// spelled.
fn applied_spec_field(
    kb: &KnowledgeBase,
    declared_field_type: &Value,
) -> Option<(Symbol, Vec<(Symbol, Value)>)> {
    match extract_type(kb, declared_field_type) {
        TypeExtractor::Parameterized { base, bindings } if !bindings.is_empty() => {
            Some((base, bindings))
        }
        _ => None,
    }
}

/// WI-20260923-32XFQ — a value threaded into the field's `member_short` binding: an
/// EFFECT-ROW parameter binds a single-label ROW (`{s.E}`) — the field's effect param is a
/// row TAIL, and a projection inside a row is an ATOM (`present`), which is how the
/// source-written `{s.E, EffP}` return wraps it — while a SORT parameter binds the value
/// bare. A value already a row is kept as read (a provision may store it pre-wrapped), and
/// so is a non-term carrier. The one wrap the three receiver projections each spelled.
fn effect_row_param_value(
    kb: &mut KnowledgeBase,
    field_base: Symbol,
    member_short: &str,
    val: Value,
) -> Value {
    if !sort_param_is_effect_row(kb, field_base, member_short) {
        return val;
    }
    match &val {
        Value::Term { id, .. } if !is_effects_rows_term(kb, *id) => {
            Value::term(kb.build_canonical_effects_rows(&[*id]))
        }
        _ => val,
    }
}

/// WI-594: the SELF-PROJECTION of a bare spec-typed receiver argument flowing
/// into a constructor field whose declared type applies the SAME spec.
///
/// A bare receiver `s: Stream` (no type-args written) carries its element and its
/// effect row as the projections `s.T` / `s.E` — both equally. But its argument
/// type, read from the env, is the bare sort ref `Stream`, which carries NEITHER.
/// Unifying that bare ref against a parameterized field type `source: Stream[Src,
/// ES]` therefore binds NOTHING — the field's own params stay free. The element
/// only ever appeared to thread because a SIBLING field's declared type wrote the
/// projection (`mapped`'s transform `fn: (Src) -> T`, fed `f: (x: s.T) -> Dst`,
/// pins `Src = s.T`); the effect row, written nowhere a value flows through, was
/// left an unresolved `??_` (and then the provided `Stream[E = {ES, EF}]` could
/// not match the declared `Stream[E = {s.E, EffP}]` return).
///
/// When the argument IS such a bare receiver and the field type applies the same
/// base, rebuild the argument's type as the receiver's self-projection `B[p =
/// s.p, …]` — keyed by the FIELD's own binding symbols so the ordinary
/// [`unify_parameterized_view`] arm threads every param (element AND effect)
/// symmetrically, and with each member interned from the binding's short name so
/// the formed `s.E` is the SAME `ExprCarried` the signature wrote. Returns `None`
/// (caller keeps the bare type, behaviour unchanged) unless the field is
/// parameterized over the argument's bare sort and the argument occurrence is a
/// simple value reference (so a clean `Ref(s)` projection head exists).
fn bare_spec_arg_self_projection(
    kb: &mut KnowledgeBase,
    declared_field_type: &Value,
    arg: &TypeResult,
) -> Option<Value> {
    // The field must APPLY a spec (`Stream[Src, ES]`); a bare-sort field has no
    // params to thread, and a structural field (arrow / row) is not a receiver slot.
    let (field_base, bindings) = applied_spec_field(kb, declared_field_type)?;
    // Recover the receiver head from a simple value reference; a compound or
    // non-reference argument has no single projectable receiver.
    let recv = leaf_var_ref(&arg.node)?;
    // The argument must be a BARE receiver at that same base — either spelling
    // ([`bare_receiver_sort`], which owns that shape test and its WI-1059 half). An
    // already-applied argument (`s: Stream[S, EffS]`) threads through the ordinary arm
    // unchanged.
    //
    // WI-1059, and why the MATERIALIZED spelling has to answer here: it is the same
    // receiver, so it must thread the same way — in particular the effect-row param must
    // still bind the single-label ROW `{s.E}` rather than the bare projection, which is
    // the whole point of the loop below. MEASURED: without it, `mapped(s, f)` built
    // `MappedStream[ES = s.E, …]` where the provider view wants `ES = {s.E}`, and
    // `bare_map`'s declared `Stream[E = {s.E, EffP}]` return stopped conforming (wi594).
    // CANONICAL, not raw `Symbol`: one logical sort carries different `Symbol` ids across
    // import scopes ([`provider_spec_view_bindings`] documents that it does). A raw compare
    // declines here whenever the field type was resolved in another scope than the argument,
    // and [`bare_spec_arg_provision_projection`] — which excludes the self case canonically —
    // declines it too, so the receiver would thread NOWHERE and leak `??_`: the very WI-594
    // symptom, reintroduced by a spelling. Both sides ask the same question, so both ask it
    // the same way.
    if bare_receiver_sort(kb, &arg.ty, recv).map(|s| kb.canonical_sort_sym(s))
        != Some(kb.canonical_sort_sym(field_base))
    {
        return None;
    }
    let (span, owner) = (arg.node.span, arg.node.owner);
    let base_ref = kb.make_sort_ref(field_base);
    let mut proj_bindings: Vec<(Symbol, Value)> = Vec::with_capacity(bindings.len());
    for (field_key, _) in &bindings {
        // Member interned from the binding's SHORT name (`Stream.E` ⟹ `E`) so the
        // formed `s.E` matches the source-written projection (loaded via the same
        // short intern in `try_expr_carried_projection`).
        let member_short = short_name_of(kb.local_name_of(*field_key)).to_owned();
        let member_sym = kb.intern(&member_short);
        let recv_term = kb.alloc(Term::Ref(recv));
        let proj = kb.make_expr_carried(recv_term, member_sym);
        // An EFFECT-ROW param (`Stream`'s `effects E`) binds a single-label ROW
        // `{s.E}`, not the bare projection. The field's effect param is a row TAIL,
        // and a projection in a row is an ATOM (`present`) — the source-written
        // `{s.E, EffP}` return wraps it exactly so. Binding the row keeps the
        // provision's `{ES, EF}` structurally a present-atom + tail, matching the
        // declared return. A SORT param threads the bare projection (`Src = s.T`).
        let proj_val = effect_row_param_value(kb, field_base, &member_short, Value::term(proj));
        // Key by the FIELD's binding symbol so `unify_parameterized_view`'s
        // by-symbol param match threads it.
        proj_bindings.push((*field_key, proj_val));
    }
    Some(parameterized_value(
        kb,
        base_ref,
        &proj_bindings,
        span,
        owner,
    ))
}

/// The SORT a value argument stands for when it is a BARE SPEC-TYPED RECEIVER `recv` —
/// the shape gate shared by [`bare_spec_arg_self_projection`] (WI-594) and
/// [`bare_spec_arg_provision_projection`] (WI-20260828-MDWEW). `None` for anything else,
/// which is what keeps both projections off a genuinely-applied argument.
///
/// TWO SPELLINGS of the same receiver, and both must answer, because which one reaches a
/// constructor field depends on where the value came from:
///   * the BARE sort ref `Stream`, the type an argument declared `s: Stream` reads as
///     outside an operation body;
///   * the same receiver with its unwritten slots MATERIALIZED — `Stream[T = s.T, E =
///     s.E]`, what [`rigidify_unwritten_sort_params`] makes of `s: Stream` INSIDE the body
///     (WI-1059). Recognized by SHAPE — every binding is this receiver's own projection of
///     that very parameter — so an argument that genuinely wrote its type-args
///     (`s: Stream[Int64, {}]`) is not mistaken for a bare one and threads through the
///     ordinary [`unify_parameterized_view`] arm unchanged.
fn bare_receiver_sort(kb: &KnowledgeBase, arg_ty: &Value, recv: Symbol) -> Option<Symbol> {
    if let Some(s) = extract_sort_ref_sym(kb, arg_ty) {
        return Some(s);
    }
    match extract_type(kb, arg_ty) {
        TypeExtractor::Parameterized { base, bindings } => (!bindings.is_empty()
            && bindings
                .iter()
                .all(|(k, v)| is_self_projection_of(kb, v, recv, *k)))
        .then_some(base),
        _ => None,
    }
}

/// WI-1059 — is `v` exactly `⟨recv⟩.<key>`, the projection [`rigidify_unwritten_sort_params`]
/// fills an unwritten slot with? The SHAPE test that lets a materialized receiver be
/// recognized as the bare one it spells out — see [`bare_spec_arg_self_projection`].
pub(super) fn is_self_projection_of(
    kb: &KnowledgeBase,
    v: &Value,
    recv: Symbol,
    key: Symbol,
) -> bool {
    let TypeExtractor::ExprCarried { value, member } = extract_type(kb, v) else {
        return false;
    };
    extract_sort_ref_sym(kb, &value) == Some(recv)
        && short_name_of(kb.local_name_of(member)) == short_name_of(kb.local_name_of(key))
}

/// True iff `t` is already an `effects_rows(EffectExpression)` Type — so an
/// effect-row provision value read pre-wrapped from a provider source is not
/// double-wrapped by [`carrier_arg_provision_projection`].
fn is_effects_rows_term(kb: &KnowledgeBase, t: TermId) -> bool {
    matches!(type_head(kb, &TermIdView(t)), TypeHead::EffectsRows)
}

/// WI-599 — the per-param values a bare carrier argument supplies for the spec
/// `field_base`, keyed by `field_base`'s param SHORT names. The binding source
/// behind [`carrier_arg_provision_projection`].
///
/// The supported case is the spec-METHOD one: an op `op(c: C, …)` ON the spec,
/// where the argument's carrier `arg_carrier` IS the enclosing spec's carrier
/// param and the enclosing spec IS `field_base` (`FiniteCollection.map`'s
/// `c : C`). The provision is the spec's own self-type — each param maps to
/// itself (`C↦C, Element↦Element, E↦E`), so the constructed sort threads the
/// spec's abstract params onto the field's. The spec's params are RIGIDIFIED
/// while the body is checked (`op.sort_param_rigids`), so each param's value is
/// its rigid form — not the pre-rigidify Global var `sort_type_params_as_pairs`
/// returns — or it would not unify with the sibling field's argument (which
/// references the body's rigid vars).
///
/// (A free op licensing `c` through an ambient `requires FiniteCollection[C = C2,
/// …]` is NOT handled here: this function answers only for the spec-method face —
/// the shape the stdlib thin `FiniteCollection.map`/`filter` use — and returns
/// `None` at the `enclosing_sort() == field_base` gate for anything else. WI-942
/// removed the reason this used to give, which was that the op's own type params
/// are `Ref`s "that do not resolve to the body's rigid vars": they do resolve now,
/// through `TypingEnv::param_rigids`. What is missing is the wiring, not the
/// information — this site reads the sort prefix, which by construction holds no
/// op param.)
pub(super) fn carrier_provision_short_bindings(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    arg_carrier: &str,
    field_base: Symbol,
) -> Option<Vec<(String, Value)>> {
    let spec = env.enclosing_sort()?;
    if kb.canonical_sort_sym(spec) != kb.canonical_sort_sym(field_base) {
        return None;
    }
    let params = sort_type_params_as_pairs(kb, spec);
    let (carrier_param, _) = params.first()?;
    if short_name_of(kb.local_name_of(*carrier_param)) != arg_carrier {
        return None;
    }
    let rigids = env.enclosing_instance_param_rigids().to_vec();
    Some(
        params
            .iter()
            .map(|(p, t)| {
                let val = match kb.get_term(*t) {
                    Term::Var(Var::Global(vid)) => rigids
                        .iter()
                        .find(|(v, _)| v == vid)
                        .map(|(_, r)| *r)
                        .unwrap_or(*t),
                    _ => *t,
                };
                (
                    short_name_of(kb.local_name_of(*p)).to_owned(),
                    Value::term(val),
                )
            })
            .collect(),
    )
}

/// WI-20260828-MDWEW — is every TYPE-PARAMETER leaf of `t` a parameter of `sort` ITSELF?
///
/// The CALLER-SIDE guard [`substitute_carrier_params`] cannot supply, and the reason it lives
/// here rather than there: that function is shared, and its leaf join is [`typaram_ref_vid`] →
/// [`type_param_vid_in_sort`], which resolves a symbol by its LOCAL NAME anchored to the sort.
/// A FOREIGN sort's parameter whose short name COLLIDES with one of `sort`'s is therefore
/// rewritten to `sort`'s own value — and the groundness gate downstream then sees a settled
/// term and passes it, so the clause or provision licenses a binding it never made.
///
/// MEASURED by `/code-review` at BOTH call sites, and the pair is the whole point: with
/// `Foreign` declaring `X` and `Element`, a clause `Element = Foreign.X` was refused while
/// `Element = Foreign.Element` LOADED CLEAN — two rows differing only by a short-name
/// coincidence. `T`, `E`, `C`, `Element` collide routinely across the prelude, so the
/// colliding row is the common one.
///
/// The question asked is "does this parameter BELONG to `sort`", answered by the leaf's
/// DECLARING SCOPE rather than by symbol identity: one sort's parameter can be registered
/// under several symbols ([`type_param_vid_in_sort`] exists because it can), and all of them
/// are declared in that sort's own scope, where a foreign sort's are not. A leaf that is not
/// a type parameter at all (a concrete sort, a literal, a rigid) is not this question and
/// passes.
fn param_leaves_belong_to_sort(kb: &KnowledgeBase, t: TermId, own_params: &[Symbol]) -> bool {
    let belongs = |kb: &KnowledgeBase, sym: Symbol| -> bool {
        if !is_sort_param_symbol(kb, sym) {
            return true;
        }
        let scope = kb.symbols.declaring_scope(sym);
        scope.is_some()
            && own_params
                .iter()
                .any(|p| kb.symbols.declaring_scope(*p) == scope)
    };
    match kb.get_term(t) {
        Term::Ref(sym) | Term::Ident(sym) => belongs(kb, *sym),
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } => {
            let functor = *functor;
            let kids: Vec<TermId> = pos_args
                .iter()
                .copied()
                .chain(named_args.iter().map(|(_, a)| *a))
                .collect();
            belongs(kb, functor)
                && kids
                    .iter()
                    .all(|c| param_leaves_belong_to_sort(kb, *c, own_params))
        }
        _ => true,
    }
}

/// WI-20260828-MDWEW — the AMBIENT-`requires` face of [`carrier_provision_short_bindings`],
/// the one its own doc named as missing.
///
/// The spec-METHOD face above answers when the op is ON the field's spec, so the spec's own
/// parameters ARE the provision. An op on a DIFFERENT sort — `FiniteCollection.map`'s
/// `mapped(c, f)`, whose field is typed on `Iterable` — has no such self-type, and its
/// argument `c : C` is a bare type parameter with no carrier sort to read a `provides` off.
/// The statement "`C` provides `Iterable`, with these params" is one level out, in the
/// ENCLOSING SORT's own `requires Iterable[C = C, Element = Element, E = E]`. This reads it.
///
/// It is the CONSTRUCTION-side twin of [`enclosing_requires_licensing_clause`] (which does
/// the same lookup for DISPATCH), and it borrows that function's two load-bearing rules:
///
///   * THE CLAUSE MUST BE ABOUT THIS ARGUMENT. `requires Iterable[C = P]` says nothing about
///     an argument typed by a different parameter `Q`, so the clause's own CARRIER binding is
///     resolved and compared against the argument's — by VarId IDENTITY, through the body
///     rigids. A short-name compare would pair two unrelated `C`s, and a clause may write
///     another sort's parameters into the slots and PERMUTE them.
///   * EVERY ENCLOSING PARAMETER IN A VALUE IS RESOLVED TO ITS BODY RIGID, however deep, and
///     what is still undetermined after that makes the whole clause decline. A `requires`
///     clause is stored against the pre-rigidify parameter forms while the body references
///     the rigids, so a clause value naming an enclosing parameter must cross that bridge or
///     it will not unify with the sibling field's argument — and a COMPOUND value carries
///     those forms in its leaves, which is why the substitution is a walk and not a lookup.
///     A GROUND value (`requires Eq[T = Int64]`) survives it and binds verbatim.
///
/// The carrier parameter is the spec's FIRST type parameter — the same convention, and the
/// same fail-CLOSED limitation, that [`enclosing_requires_licensing_clause`] gate 1 states.
pub(super) fn enclosing_requires_provision_bindings(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    arg_id: TermId,
    field_base: Symbol,
) -> Option<Vec<(String, Value)>> {
    let encl = env.enclosing_sort()?;
    let rigids = env.enclosing_instance_param_rigids().to_vec();
    if rigids.is_empty() {
        return None;
    }
    // The argument's own parameter, by IDENTITY: it reaches here as that parameter's body
    // rigid, and the rigid table is the only exact map back to the parameter it stands for.
    let arg_pvid = rigids.iter().find(|(_, r)| *r == arg_id).map(|(v, _)| *v)?;
    let encl_params = sort_type_params_as_pairs(kb, encl).to_vec();
    let encl_param_syms: Vec<Symbol> = encl_params.iter().map(|(p, _)| *p).collect();
    let spec_params = sort_type_params_as_pairs(kb, field_base).to_vec();
    let (carrier_param, _) = spec_params.first()?;
    let carrier_pvid = type_param_vid_in_sort(kb, field_base, *carrier_param)?;

    // A clause value → the enclosing parameter's VarId. SYMBOL IDENTITY against the sort's
    // own registrations (cf. `enclosing_requires_licensing_clause`'s `rigid_of`), never a
    // name join: a clause may name another sort's parameters and permute them.
    let clause_param_vid = |kb: &KnowledgeBase, t: TermId| -> Option<VarId> {
        match kb.get_term(t) {
            Term::Ref(sym) => {
                let sym = *sym;
                encl_params
                    .iter()
                    .find(|(p, _)| *p == sym)
                    .and_then(|(_, pty)| match kb.get_term(*pty) {
                        Term::Var(Var::Global(v)) => Some(*v),
                        _ => None,
                    })
            }
            Term::Var(Var::Global(v)) => Some(*v),
            _ => None,
        }
    };

    // The sort's OWN clauses, not the flattened chain: a TRANSITIVELY required spec's
    // clause is written in THAT sort's parameters, which resolve to none of the enclosing
    // sort's rigids — so reading one would either be rejected by the gate below or, worse,
    // bind a foreign variable. The dispatch-side twin reads `direct_requires` for the same
    // reason.
    for entry in direct_requires(kb, encl) {
        if kb.canonical_sort_sym(entry.required_sort) != kb.canonical_sort_sym(field_base) {
            continue;
        }
        let Some((_base, clause_bindings)) = unwrap_spec_view_value(kb, &entry.spec) else {
            continue;
        };
        // Clause binding ↦ the spec parameter it is FOR, by VarId identity (the clause's
        // keys and the spec's declared parameters are resolved in two scopes).
        let bound_for = |kb: &KnowledgeBase, want: VarId| -> Option<TermId> {
            clause_bindings
                .iter()
                .find(|(p, _)| type_param_vid_in_sort(kb, field_base, *p) == Some(want))
                .map(|(_, t)| *t)
        };
        // THE CLAUSE MUST BE ABOUT THIS ARGUMENT.
        let Some(cval) = bound_for(kb, carrier_pvid) else {
            continue;
        };
        if clause_param_vid(kb, cval) != Some(arg_pvid) {
            continue;
        }
        let mut out: Vec<(String, Value)> = Vec::with_capacity(spec_params.len());
        for (p, _) in spec_params.iter() {
            // A spec parameter the clause leaves unwritten is OMITTED, not guessed: the
            // caller `?`-declines the whole projection when the field binds a parameter this
            // provision does not name, so a partial clause refuses loudly instead of
            // threading some params and leaking the rest.
            let Some(pvid) = type_param_vid_in_sort(kb, field_base, *p) else {
                continue;
            };
            let Some(v) = bound_for(kb, pvid) else {
                continue;
            };
            // A leaf naming a FOREIGN sort's parameter is not this clause's to determine, and
            // the substitution below would silently claim it whenever its short name collides
            // with one of `encl`'s ([`param_leaves_belong_to_sort`] states the measurement).
            if !param_leaves_belong_to_sort(kb, v, &encl_param_syms) {
                return None;
            }
            // EVERY enclosing parameter in the value crosses to its BODY RIGID, however deep.
            // A `requires` clause is stored against the PRE-RIGIDIFY forms while the body
            // references the rigids, and a COMPOUND value (`Element = Option[T = Other]`, a
            // row `E = {ES}`) carries those forms in its LEAVES. Resolving only a bare
            // `Ref`/`Var` and binding anything else as read left those leaves free, and the
            // sibling field then bound them to whatever the call supplied — `/code-review`
            // MEASURED a program loading clean whose clause said `Option[T = Other]` while
            // its callback took `Option[T = Element]`, two INDEPENDENT parameters of the
            // enclosing sort. That is granting a licence and binding a wrong rigid together,
            // the hazard the dispatch-side twin's gate-1 doc names. The SHALLOW spelling of
            // that same disagreement was already refused, so the deep one was a hole in an
            // otherwise-closed door.
            let bound = substitute_carrier_params(kb, v, encl, &rigids);
            // DETERMINED AFTER SUBSTITUTION, or the clause supplies NOTHING. A leaf that
            // named no enclosing parameter survives substitution unchanged: a concrete sort
            // is determined and binds verbatim (`requires Eq[T = Int64]`), while a foreign
            // sort's parameter (`Element = Other.X`) or a leftover pre-rigidify var is a
            // variable this clause does not decide — and binding one is what made it unify
            // as if free. Fail-CLOSED for the whole clause, not per param: a half-read
            // provision would thread some params and leak the rest, which reads as working.
            if !type_value_is_ground_g(kb, bound, true) {
                return None;
            }
            // Keyed by SHORT NAME because that is [`carrier_provision_short_bindings`]'
            // contract with its one caller, and safe there: these are the parameters of ONE
            // sort, whose short names are unique by construction. The JOINS above are all
            // by VarId; only this output key is a name.
            out.push((
                short_name_of(kb.local_name_of(*p)).to_owned(),
                Value::term(bound),
            ));
        }
        return Some(out);
    }
    None
}

/// WI-20260829-70XVH — every TYPE PARAMETER inside a stored `requires` value, crossed to
/// the BODY RIGID the operation is being checked at. `None` when one of them is a parameter
/// this body does not hold.
///
/// The IDENTITY-KEYED twin of [`substitute_carrier_params`] + [`param_leaves_belong_to_sort`],
/// which the two sort faces need as a pair because their leaf join is by LOCAL NAME anchored
/// to a sort, and so can claim a FOREIGN sort's parameter whose short name collides (that
/// function's doc carries the measurement). Here the join is the leaf's own canonical
/// variable ([`type_param_global_var`]) against `rigids`, which IS the list of parameters in
/// scope for this body — a foreign parameter is simply absent from it, so "is this ours" and
/// "what is its rigid" have ONE answer and cannot disagree.
///
/// Fail-CLOSED, and the caller propagates that to the whole clause: a half-crossed provision
/// would thread some params and leave the rest free for the sibling field to bind, which is
/// granting a licence and binding a wrong rigid together.
fn substitute_body_rigids(
    kb: &mut KnowledgeBase,
    tid: TermId,
    rigids: &[(VarId, TermId)],
) -> Option<TermId> {
    // The PRE-RIGIDIFY parameter VARIABLE a row tail carries (`{ES}` lowers to
    // `open[tail = Var]`, the tail anonymous — cf. `substitute_carrier_params` (1b)).
    // A `Rigid` is accepted only when it is one THIS body holds, by the same identity test
    // as every other join here: a stored `requires` is built at LOAD time and rigids are
    // minted at CHECK time, so nothing can reach that arm today — but "already this body's
    // own skolem" is an assumption, and left unenforced a FOREIGN body's skolem would pass
    // the caller's `rigid_ok` groundness gate and be threaded into the field type, which is
    // the granting-a-licence-and-binding-a-wrong-rigid hazard the sibling's doc names.
    // (`/code-review`.) Any other var is undetermined and this clause does not decide it.
    if let Term::Var(v) = kb.get_term(tid) {
        return match v {
            Var::Global(g) => {
                let g = *g;
                rigids.iter().find(|(rv, _)| *rv == g).map(|(_, r)| *r)
            }
            Var::Rigid(_) => rigids.iter().any(|(_, r)| *r == tid).then_some(tid),
            _ => None,
        };
    }
    if let Term::Ref(sym) | Term::Ident(sym) = kb.get_term(tid) {
        let sym = *sym;
        return match type_param_global_var(kb, sym) {
            Some(vid) => rigids.iter().find(|(rv, _)| *rv == vid).map(|(_, r)| *r),
            // Not a type parameter at all (`Int64`, a concrete sort): binds verbatim.
            None => Some(tid),
        };
    }
    // Any other compound: recurse into children, preserving the functor. A functor that is
    // ITSELF a parameter is left alone and refused downstream by the caller's groundness
    // gate (`type_value_is_ground_g` tests the functor), so nothing is claimed silently.
    //
    // CROSS EVERY CHILD FIRST, and only then rebuild. `map_fn_children` allocates as soon as
    // any child changed, and `TermStore::alloc` increments the refcount ON A HIT — so
    // rebuilding at a level this reader is about to DECLINE would pin a term nobody holds,
    // once per call, on a store that has a free list (`/code-review`). The `?` here returns
    // before any allocation at this level.
    if let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = kb.get_term(tid).clone()
    {
        let mut new_pos: SmallVec<[TermId; 4]> = SmallVec::with_capacity(pos_args.len());
        for a in &pos_args {
            new_pos.push(substitute_body_rigids(kb, *a, rigids)?);
        }
        let mut new_named: SmallVec<[(Symbol, TermId); 2]> =
            SmallVec::with_capacity(named_args.len());
        for (k, a) in &named_args {
            new_named.push((*k, substitute_body_rigids(kb, *a, rigids)?));
        }
        if new_pos[..] == pos_args[..] && new_named[..] == named_args[..] {
            return Some(tid);
        }
        return Some(kb.alloc(Term::Fn {
            functor,
            pos_args: new_pos,
            named_args: new_named,
        }));
    }
    Some(tid)
}

/// WI-20260829-70XVH — the OPERATION's own `requires` face of
/// [`carrier_arg_provision_projection`]: the third and last declaration the statement
/// "this carrier provides that spec" can be written on.
///
/// [`carrier_provision_short_bindings`] answers when the op is ON the field's spec, and
/// [`enclosing_requires_provision_bindings`] when the ENCLOSING SORT requires it. Both read
/// a SORT's declaration, and are therefore blind to the shape this one is for: an operation
/// whose receiver is its OWN type parameter rather than its sort's carrier, carrying the
/// clause itself — `gmap[Sc, S, …](s: Sc, …) requires Walk[C = Sc, Element = S, …]`. Such an
/// operation may sit in no sort at all, or (the stdlib shape) in the DATA sort it constructs,
/// whose own parameters say nothing about `Sc`.
///
/// WI-599 EXCLUDED IT AND NAMED A REASON THAT HAS SINCE EXPIRED — "op.rigidify not on env,
/// requires-entry `Ref`s don't resolve to body rigids". WI-942 put the operation's OWN
/// parameters into [`TypingEnv::param_rigids`], so a clause `Ref` resolves through
/// [`type_param_global_var`] to a canonical var this body holds a rigid for; what was left
/// was the wiring, which is this function.
///
/// The two load-bearing rules [`enclosing_requires_provision_bindings`] states hold here
/// unchanged — THE CLAUSE MUST BE ABOUT THIS ARGUMENT, and EVERY PARAMETER IN A VALUE
/// CROSSES TO ITS BODY RIGID or the whole clause declines — and both joins are by VarId
/// identity. Two reads DIFFER, both because the clause is the OPERATION's:
///
///   * [`TypingEnv::param_rigids`] IN FULL, not the sort prefix. §5.3 lets an op-level clause
///     name the operation's own type parameters as well as its enclosing sort's, one list —
///     and the argument this face exists for is always one of the operation's own, which the
///     prefix view excludes by construction.
///   * the clause is decoded by [`op_requires_entry_carrier_map`], NOT
///     [`unwrap_spec_view_value`]. An op-level `requires` is stored as the bare application
///     `Fn{Spec, …}` rather than a `SortView` wrapper, and the SortView decoder reads a bare
///     application as the NO-BINDINGS case — it would hand back an empty map, and this face
///     would then answer for a clause it never read.
pub(super) fn op_requires_provision_bindings(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    arg_id: TermId,
    field_base: Symbol,
) -> Option<Vec<(String, Value)>> {
    let rigids = env.param_rigids().to_vec();
    if rigids.is_empty() {
        return None;
    }
    let spec_params = sort_type_params_as_pairs(kb, field_base).to_vec();
    let (carrier_param, _) = spec_params.first()?;
    let carrier_pvid = type_param_vid_in_sort(kb, field_base, *carrier_param)?;

    // [`TypingEnv::op_requires`] is the LICENCE list — every clause the operation wrote,
    // value preconditions included (see its setter). Only a SPEC requirement can say a
    // carrier provides anything, so the precondition filter is this reader's own question and
    // not an inherited one; the sort-symbol test below would drop them anyway, and stating it
    // keeps a precondition whose functor happens to be a sort's name from ever being read as
    // a provision.
    for entry in env.op_requires().to_vec() {
        if is_value_precondition_clause(kb, &entry.spec)
            || kb.canonical_sort_sym(entry.required_sort) != kb.canonical_sort_sym(field_base)
        {
            continue;
        }
        let clause = op_requires_entry_carrier_map(kb, &entry);
        // Clause binding ↦ the spec parameter it is FOR, by VarId identity (the clause's
        // keys and the spec's declared parameters are resolved in two scopes).
        let bound_for = |kb: &KnowledgeBase, want: VarId| -> Option<TermId> {
            clause
                .iter()
                .find(|(p, _)| type_param_vid_in_sort(kb, field_base, *p) == Some(want))
                .map(|(_, t)| *t)
        };
        // THE CLAUSE MUST BE ABOUT THIS ARGUMENT. `requires Walk[C = P]` says nothing about
        // an argument typed by a different parameter `Q`; crossing the clause's own carrier
        // binding to its body rigid and comparing TERM IDENTITY against the argument's is
        // that question asked exactly. (A short-name compare would pair two unrelated `C`s,
        // and a clause may write another sort's parameters into the slots and permute them.)
        let Some(cval) = bound_for(kb, carrier_pvid) else {
            continue;
        };
        if substitute_body_rigids(kb, cval, &rigids) != Some(arg_id) {
            continue;
        }
        let mut out: Vec<(String, Value)> = Vec::with_capacity(spec_params.len());
        for (p, _) in spec_params.iter() {
            // A spec parameter the clause leaves unwritten is OMITTED, not guessed: the
            // caller `?`-declines the whole projection when the field binds a parameter this
            // provision does not name.
            let Some(pvid) = type_param_vid_in_sort(kb, field_base, *p) else {
                continue;
            };
            let Some(v) = bound_for(kb, pvid) else {
                continue;
            };
            let bound = substitute_body_rigids(kb, v, &rigids)?;
            // DETERMINED AFTER THE CROSSING, or the clause supplies NOTHING — the same
            // fail-closed verdict, and for the same reason, as the sort face states.
            if !type_value_is_ground_g(kb, bound, true) {
                return None;
            }
            out.push((
                short_name_of(kb.local_name_of(*p)).to_owned(),
                Value::term(bound),
            ));
        }
        return Some(out);
    }
    None
}

/// The type an entity FIELD's supplied argument is INFERRED from (WI-594/WI-599).
///
/// WI-594: a bare spec receiver into a parameterized field threads its element AND effect
/// through its self-projection. WI-599: a bare CARRIER value whose sort merely PROVIDES the
/// field's spec threads through the carrier's provision. WI-20260828-MDWEW: a bare
/// SPEC-typed argument into a field typed on a spec its sort provides threads through THAT
/// provision. Else the raw inferred type.
fn field_arg_type(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    declared_type: &Value,
    r: &TypeResult,
) -> Value {
    bare_spec_arg_self_projection(kb, declared_type, r)
        .or_else(|| carrier_arg_provision_projection(kb, env, declared_type, r))
        .or_else(|| bare_spec_arg_provision_projection(kb, declared_type, r))
        .unwrap_or_else(|| r.ty.clone())
}

/// WI-1059 — VALIDATE one supplied field value against its declared field type: the raw
/// inferred type first, and only on failure the [`field_arg_type`] rebuild.
///
/// STRICTLY ADDITIVE, and that ordering is the whole point. The rebuild exists to feed
/// INFERENCE, and it can name things the raw type does not — a bare `nil` into a
/// `List[T = Int64]` field rebuilds to `List[T = nil.T]`, a neutral that matches nothing.
/// The validation loop used to sidestep that by reading the raw type and relying on the
/// groundness gate to skip whatever needed a rebuild; once a skolem counts as ground
/// ([`type_value_is_ground`]) that skip is gone, and a raw `c : ?C` is refused against the
/// very field the inference loop just threaded it into (`FiniteCollection.map`'s
/// `mapped(c, f)`, measured). Trying the raw type first keeps every value that conformed
/// before conforming; the rebuild only rescues one the raw reading cannot express.
///
/// The retry runs on a CLONED subst committed only on success, so a failed first attempt
/// cannot leak partial bindings into the retry or the caller.
#[allow(clippy::too_many_arguments)]
fn validate_field_arg(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    subst: &mut Substitution,
    r: &TypeResult,
    declared_type: &Value,
    span: Option<Span>,
    ctor_sym: Symbol,
    field_sym: Symbol,
) -> ArgValidation {
    let ctx = TypeErrorContext::EntityField {
        entity: ctor_sym,
        field: field_sym,
    };
    let mut probe = subst.clone();
    let first = validate_arg_against_param(
        kb,
        &mut probe,
        &r.ty,
        declared_type,
        span,
        ctx.clone(),
        Some(&r.node),
    );
    if !matches!(first, ArgValidation::Fail(_)) {
        *subst = probe;
        return first;
    }
    let rebuilt = field_arg_type(kb, env, declared_type, r);
    let mut probe = subst.clone();
    match validate_arg_against_param(
        kb,
        &mut probe,
        &rebuilt,
        declared_type,
        span,
        ctx,
        Some(&r.node),
    ) {
        ArgValidation::Fail(_) => first,
        ok => {
            *subst = probe;
            ok
        }
    }
}

/// WI-599 — a CARRIER-PARAM-spec constructor field fed a carrier VALUE that
/// PROVIDES that spec. The THIN finite-combinator case: `FiniteCollection.map(c,
/// f) = mapped(c, f)`, where `mapped`'s `source` field is typed
/// `Iterable[C = Source, Element = Src, E = ES]` (WI-590) and the argument `c` has
/// the carrier-param type `C` — NOT the spec itself.
///
/// [`bare_spec_arg_self_projection`] (WI-594) threads a bare spec receiver whose
/// argument type IS the field's spec base (`s : Stream` into `Stream[…]`) via the
/// receiver's self-projection `s.T` / `s.E`. Here the argument's type is a
/// DIFFERENT sort (the carrier param) that merely PROVIDES the spec, so that check
/// fails and the field's params (`Source`, `Src`, `ES`) leak as `??_` — the source
/// carrier and its access effect never thread (only the element pins, through the
/// sibling `fn`'s `(x: Src)`).
///
/// When the argument is a bare carrier value whose sort provides the field's spec,
/// rebuild the argument's type as that spec applied to the carrier's own provision
/// (`carrier_provision_short_bindings`) — keyed by the FIELD's binding symbols so
/// the ordinary [`unify_parameterized_view`] arm threads every param (carrier `C`,
/// element AND effect) into the constructed sort's params. An EFFECT-row param's
/// value is wrapped as a single-label row (`{…}`, mirroring WI-594); a sort param
/// stays bare. Returns `None` (caller keeps the raw arg type) unless the field
/// applies a spec, the argument is a bare carrier of a DIFFERENT sort, and a
/// provision is found.
pub(super) fn carrier_arg_provision_projection(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    declared_field_type: &Value,
    arg: &TypeResult,
) -> Option<Value> {
    // The field must APPLY a spec (`FiniteCollection[C = …, …]`).
    let (field_base, bindings) = applied_spec_field(kb, declared_field_type)?;
    // The argument must be a BARE carrier — a type-param value (`c : C`, possibly
    // rigidified) or a bare sort ref — naming a sort OTHER than the field's spec
    // base. (An already-applied `s : Stream[…]` threads through the ordinary arm;
    // a bare `field_base` receiver is WI-594's self-projection job.)
    let Value::Term { id: arg_id, .. } = &arg.ty else {
        return None;
    };
    let arg_carrier = typaram_ref_short_name(kb, *arg_id)?;
    if arg_carrier == short_name_of(kb.qualified_name_of(field_base)) {
        return None;
    }

    // The spec-METHOD face first (the op is ON the field's spec), then the enclosing SORT's
    // ambient `requires`, then the OPERATION's own (WI-20260829-70XVH). Additive in that
    // order: each runs only where the ones before it declined. The three exhaust where the
    // statement "this carrier provides that spec" can be written.
    let provision = carrier_provision_short_bindings(kb, env, &arg_carrier, field_base)
        .or_else(|| enclosing_requires_provision_bindings(kb, env, *arg_id, field_base))
        .or_else(|| op_requires_provision_bindings(kb, env, *arg_id, field_base))?;

    let (span, owner) = (arg.node.span, arg.node.owner);
    let base_ref = kb.make_sort_ref(field_base);
    let mut proj_bindings: Vec<(Symbol, Value)> = Vec::with_capacity(bindings.len());
    for (field_key, _) in &bindings {
        let member_short = short_name_of(kb.local_name_of(*field_key)).to_owned();
        let val = provision
            .iter()
            .find(|(s, _)| *s == member_short)
            .map(|(_, v)| v.clone())?;
        // An EFFECT-ROW param threads as a single-label row (`{c.E}`), matching the
        // source-written provision; a SORT param threads the bare value. A value
        // that is already a row is kept as-is (the requires/provider source may
        // store it pre-wrapped).
        let proj_val = effect_row_param_value(kb, field_base, &member_short, val);
        proj_bindings.push((*field_key, proj_val));
    }
    Some(parameterized_value(
        kb,
        base_ref,
        &proj_bindings,
        span,
        owner,
    ))
}

/// WI-20260828-MDWEW — a BARE SPEC-TYPED argument flowing into a field typed on a
/// DIFFERENT spec that the argument's sort PROVIDES.
///
/// The third face of the same threading question, and the one no existing reader answers:
///
///   * [`bare_spec_arg_self_projection`] (WI-594) wants the field to apply the argument's
///     OWN spec (`s : Stream` into `Stream[Src, ES]`); its `base == field_base` gate fails
///     the moment the field is typed on a spec the argument merely provides.
///   * [`carrier_arg_provision_projection`] (WI-599) wants the argument to be a CARRIER
///     PARAM and reads the provision off the ENCLOSING SORT (`carrier_provision_short_bindings`
///     returns `None` unless `env.enclosing_sort() == field_base`), so a FREE operation is
///     out of its reach entirely.
///
/// Here the argument is a bare `s : Stream` and the field is `source: Iterable[C = Source,
/// Element = Src, E = ES]`. Only `Src` threads, and only by accident — a SIBLING field's
/// arrow (`fn: (Src) -> T`, fed the `(x: s.T) -> Dst` callback) pins it. `Source` and `ES`
/// appear nowhere a value flows through, so they leak `??_` and the constructed carrier's
/// provided row is ungrounded (MEASURED: `Mapped[T = ?Dst, ES = ??_, EF = …, Src = s.Elem,
/// Source = ??_]` against a declared `Seq[Elem = ?Dst, Row = {s.Row, ?EffP}]`).
///
/// The fact that relates the two specs is the argument sort's own provision —
/// `provides Iterable[C = Stream, Element = T, E = E]` — which is written in the ARGUMENT
/// SORT's parameters. So: read that view, then substitute each of those parameters with the
/// receiver's projection of it ([`substitute_carrier_params`], keyed by the sort's canonical
/// param VarIds), and key the result by the FIELD's binding symbols so the ordinary
/// [`unify_parameterized_view`] arm threads every param.
///
/// NAMES ARE NOT THE JOIN, on either side, and both matter:
///   * the projection MEMBER comes from the ARGUMENT SORT's own parameter (`Element ↦
///     Stream.T` becomes `s.T`), never from the field's key — a provision may permute or
///     rename freely (`provides Spec[T = x.S, S = x.T]`), and taking the member from the
///     field key would silently build the transposed type;
///   * the field key ↔ provision key match is by the spec's canonical param VarId
///     ([`type_param_vid_in_sort`]), not by short name — the two key sets are resolved in
///     two different import scopes.
///
/// An EFFECT-ROW param binds the single-label ROW `{s.E}` rather than the bare projection,
/// for WI-594's reason: the field's effect param is a row TAIL and a projection inside a row
/// is an ATOM. A value the provision already stores pre-wrapped is kept as read.
///
/// TWO BOUNDARIES, stated because each is a decline and not an oversight:
///   * ONE HOP. [`provider_spec_view_bindings`] reads the provisions KEYED BY this sort,
///     so a spec reached only transitively (`MappedStream provides Stream`, `Stream
///     provides Iterable`) is not composed here and the caller keeps the raw type. There
///     is no stored fact for a transitive provision to read — it is derived, per reader.
///   * CARRIER-KEYED ONLY. A WITNESS provision (`sort MappedStreamFinite provides
///     FiniteCollection[C = MappedStream[…]]`) is keyed by the witness's own `sort_ref`,
///     so it is not among what this reads for the CARRIER — and that is right: its
///     bindings are written in the WITNESS's binder, not the carrier's, so substituting
///     them against the carrier's parameters would be the wrong namespace (the defect
///     WI-20260828-57MRM's [`witness_instantiation`] exists to avoid).
///   * ONE APPLICATION, INHERITED. [`provider_spec_view_bindings`] MERGES the provisions a
///     carrier writes for one spec by short name and keeps the first value for a repeated
///     param, on the stated grounds that a disagreement is a load error. Where a carrier
///     legitimately provides one spec at SEVERAL applications, that merge is
///     under-determined, and this reader now turns the pick into a constructor field's
///     type. It is the shared reader's property and not one introduced here — both existing
///     callers inherit it — but it is named rather than left silent, because the groundness
///     gate below cannot catch a wrong pick: every candidate is equally ground.
///
/// Returns `None` — caller keeps the raw argument type, behaviour unchanged — unless the
/// field applies a spec, the argument is a bare receiver of a DIFFERENT sort, that sort
/// provides the field's spec, and the provision names every parameter the field binds.
pub(super) fn bare_spec_arg_provision_projection(
    kb: &mut KnowledgeBase,
    declared_field_type: &Value,
    arg: &TypeResult,
) -> Option<Value> {
    // The field must APPLY a spec (`Iterable[C = …, …]`); a bare-sort field has no params
    // to thread, and a structural field (arrow / row) is not a receiver slot.
    let (field_base, bindings) = applied_spec_field(kb, declared_field_type)?;
    // Recover the receiver head from a simple value reference; a compound or
    // non-reference argument has no single projectable receiver.
    let recv = leaf_var_ref(&arg.node)?;
    // A bare receiver of a sort OTHER than the field's spec — an argument at the field's
    // own spec is [`bare_spec_arg_self_projection`]'s job, and answering it here too would
    // route the same shape through two readers.
    //
    // WI-20260828-BH1JZ: WRITTEN TYPE ARGUMENTS COUNT TOO. [`bare_receiver_sort`] answers
    // only for a receiver spelled bare (`b: DBox`) or materialized into all-self-
    // projections (`List[T = xs.T]`); a receiver written `xs: List[T = Int64]` is a
    // parameterized view with a CONCRETE argument and was declined, so the projection
    // never ran for the commonest spelling there is. The σ below is unaffected by which
    // spelling arrived — it maps each of `arg_sort`'s params to the RECEIVER's projection
    // of that param (`xs.T`), which denotes the written argument just as well as an
    // unwritten one. Widened HERE and not inside `bare_receiver_sort`, which
    // [`bare_spec_arg_self_projection`] also reads and whose question is narrower.
    let arg_sort = bare_receiver_sort(kb, &arg.ty, recv).or_else(|| {
        // CONCRETE carriers only. A receiver whose sort is itself an abstract SPEC
        // (`rest : Stream[T = …, E = …]`, the tail `MappedStream.splitFirst` re-wraps)
        // has no carrier of its own to read a provision off; projecting through
        // `Stream provides Iterable` would bind the field's `Source` to the SPEC
        // `Stream` rather than to the tail's real carrier. MEASURED — without this
        // clause the stdlib's own `mapped(rest, fn)` builds
        // `MappedStream[Source = Stream, Src = rest.T, …]` and the file stops loading.
        let base = sort_functor_of_view(kb, &arg.ty)?;
        (!carrier_is_abstract_spec(kb, base)).then_some(base)
    })?;
    if kb.canonical_sort_sym(arg_sort) == kb.canonical_sort_sym(field_base) {
        return None;
    }
    // The relating fact: `arg_sort provides field_base[…]`, in `arg_sort`'s own params.
    //
    // WI-20260828-BH1JZ: DIRECT provision first, then the view COMPOSED through
    // TRANSITIVE provision. `provider_spec_view_bindings` reads `provides` facts whose
    // carrier IS `arg_sort`, so it finds an explicit `provides Iterable[…]` and misses
    // `List`, whose Iterable-ness rides through `Stream` (`List provides Stream`,
    // `Stream provides Iterable`) with no direct fact.
    //
    // THE MISS WAS SILENT, which is why it cost a whole investigation: the caller fell
    // back to the raw `List[T = Int64]`, `unify_types` against `Iterable[C = ?_,
    // Element = ?_, E = ?_]` answered TRUE while binding nothing useful, and the
    // constructed carrier's params — INCLUDING the sibling arrow field's row — stayed
    // free, surfacing far away as `undeclared effect ??_` on the constructing operation.
    //
    // [`transitive_provision_view`] already composes exactly this (its own doc names
    // `List`'s Iterable-ness through `Stream` as the case it is for) and returns the
    // SAME view shape — keyed by spec param, valued in the carrier's own params — which
    // is what the σ below consumes. Its first branch is the direct one, so the `or_else`
    // keeps the hot path off the walk rather than expressing a second policy.
    let view = provider_spec_view_bindings(kb, arg_sort, field_base).or_else(|| {
        let carrier_param = spec_carrier_param(kb, field_base)?;
        let pvid = type_param_vid_in_sort(kb, field_base, carrier_param)?;
        let mut visited: SmallVec<[Symbol; 8]> = SmallVec::new();
        transitive_provision_view(kb, field_base, pvid, arg_sort, &mut visited).map(|(v, _)| v)
    })?;
    // σ: each of `arg_sort`'s parameters ↦ the receiver's projection of THAT parameter.
    //
    // WI-20260828-BH1JZ: a WRITTEN type argument overrides the projection for its own
    // parameter. `xs.T` and `Int64` denote the same thing for a receiver declared
    // `xs: List[T = Int64]`, but only one of them SAYS so here: threading the projection
    // left the sibling arrow field demanding `xs.T -> ?_` against the supplied
    // `Int64 -> Int64`, a mismatch on two spellings of one type. Written arguments are
    // read off the receiver's own type; a parameter it leaves unwritten keeps the
    // projection, which is what a bare receiver supplies for every parameter.
    let mut recv_projections = receiver_param_projections(kb, arg_sort, recv);
    if let TypeExtractor::Parameterized {
        bindings: recv_bindings,
        ..
    } = extract_type(kb, &arg.ty)
    {
        for (k, v) in &recv_bindings {
            let Some(vid) = type_param_vid_in_sort(kb, arg_sort, *k) else {
                continue;
            };
            let Value::Term { id, .. } = v else { continue };
            match recv_projections.iter_mut().find(|(pv, _)| *pv == vid) {
                Some(slot) => slot.1 = *id,
                None => recv_projections.push((vid, *id)),
            }
        }
    }
    let arg_param_syms: Vec<Symbol> = sort_type_params_as_pairs(kb, arg_sort)
        .iter()
        .map(|(p, _)| *p)
        .collect();

    let (span, owner) = (arg.node.span, arg.node.owner);
    let base_ref = kb.make_sort_ref(field_base);
    let mut proj_bindings: Vec<(Symbol, Value)> = Vec::with_capacity(bindings.len());
    // WI-20260828-BH1JZ: the spec's CARRIER parameter is the receiver's own type, by
    // definition, and must not be read off the provision. A self-referential provision
    // writes the SPEC in that slot (`Stream provides Iterable[C = Stream, …]` — `C = Self`
    // spelled with the sort's own name), and composing it through a hop substitutes the
    // intermediate's PARAMS, not that self-reference, so it survives as the literal
    // `Stream`. THE SAME SENTENCE IS THE SUBTYPE RELATION'S RULE (WI-20260829-XZMGC,
    // [`subtype_provider_view`]) — this site stated it first, and measured it.
    // MEASURED: `mapped(xs, inc)` over a `List` inferred
    // `MappedStream[Source = Stream, …]`, and the finiteness witness — gated on
    // `requires FiniteCollection[C = S]` — then asked whether the SPEC `Stream` is a
    // FiniteCollection and got no. Binding it to the receiver's type is right for a
    // direct provision too, where the view already names exactly that carrier.
    // Joined by VID and not by Symbol, for the same reason the provision join below is:
    // the field's binding keys and the spec's own declaration are resolved in two scopes
    // and can be two Symbols for one parameter.
    let field_carrier_vid = spec_carrier_param(kb, field_base)
        .and_then(|cp| type_param_vid_in_sort(kb, field_base, cp));
    for (field_key, _) in &bindings {
        // Identity join on the SPEC's own parameter — the field's binding keys and the
        // provision's are resolved in two scopes and can be two Symbols for one param.
        let key_vid = type_param_vid_in_sort(kb, field_base, *field_key)?;
        if Some(key_vid) == field_carrier_vid {
            proj_bindings.push((*field_key, arg.ty.clone()));
            continue;
        }
        let raw = view
            .iter()
            .find(|(sp, _)| type_param_vid_in_sort(kb, field_base, *sp) == Some(key_vid))
            .map(|(_, v)| *v)?;
        // Same guard, same reason: a provision binding may name a FOREIGN sort's parameter,
        // and the substitution's name-anchored leaf join would claim it as this receiver's
        // whenever the short names collide ([`param_leaves_belong_to_sort`]).
        if !param_leaves_belong_to_sort(kb, raw, &arg_param_syms) {
            return None;
        }
        let val = substitute_carrier_params(kb, raw, arg_sort, &recv_projections);
        // THE CALLER'S GROUNDNESS CHECK [`substitute_carrier_params`]' doc requires, and the
        // reason it leaves an unmatched leaf intact rather than guessing. A provision may
        // bind a spec param to a FOREIGN sort's parameter (`provides Walk[Element = Other.X]`)
        // — nothing in this receiver's σ replaces it, so it survives as a bare parameter ref
        // and would then unify with whatever the sibling field supplies instead of
        // contradicting it. MEASURED by `/code-review`: `Element = Other.X` loaded clean
        // where the concrete twin `Element = Int64` was correctly refused. A partially
        // substituted rebuild is worse than none, so the whole projection declines.
        //
        // `rigid_ok = true` is the DETERMINED reading, which is the question here: a body
        // rigid and a receiver projection (`s.T`) are both settled, and no later pass could
        // decide them — where a leftover parameter ref or free var is exactly what a later
        // pass would wrongly decide.
        if !type_value_is_ground_g(kb, val, true) {
            return None;
        }
        // An EFFECT-ROW param threads as a single-label row (`{s.E}`); a SORT param threads
        // the substituted value bare. A value already stored as a row is kept as read.
        let member_short = short_name_of(kb.local_name_of(*field_key)).to_owned();
        let proj_val = effect_row_param_value(kb, field_base, &member_short, Value::term(val));
        proj_bindings.push((*field_key, proj_val));
    }
    Some(parameterized_value(
        kb,
        base_ref,
        &proj_bindings,
        span,
        owner,
    ))
}

/// WI-20260828-MDWEW — the substitution [`bare_spec_arg_provision_projection`] applies to a
/// provision view: every one of `sort`'s own type parameters, keyed by its canonical
/// `Var::Global` VarId, mapped to the receiver's projection of it (`Stream.T ↦ s.T`).
///
/// Keyed by VarId and not by name because that is what [`substitute_carrier_params`] joins
/// on, and because it is the only hygienic key — `sort T = ?` recurs across every sort in
/// the prelude. The projection's MEMBER, by contrast, must be the parameter's own short
/// name: `s.T` is the source-written spelling, interned through the same short intern
/// `try_expr_carried_projection` loads a written projection with, so the formed term IS the
/// one a signature that writes `s.T` produced.
fn receiver_param_projections(
    kb: &mut KnowledgeBase,
    sort: Symbol,
    recv: Symbol,
) -> Vec<(VarId, TermId)> {
    let params = sort_type_params_as_pairs(kb, sort);
    let mut out = Vec::with_capacity(params.len());
    for (param_sym, _) in params.iter() {
        // A declared parameter with no canonical var is absent from σ, so
        // [`substitute_carrier_params`] leaves that leaf intact and the rebuilt type stays
        // NON-GROUND — which the caller's `type_value_is_ground_g` gate then turns into a
        // DECLINE of the whole projection. It is that gate, not the field unification, that
        // makes this safe: an unsubstituted parameter leaf would otherwise UNIFY with
        // whatever the sibling field supplied instead of contradicting it.
        let Some(vid) = type_param_vid_in_sort(kb, sort, *param_sym) else {
            continue;
        };
        let member_short = short_name_of(kb.local_name_of(*param_sym)).to_owned();
        let member_sym = kb.intern(&member_short);
        let recv_term = kb.alloc(Term::Ref(recv));
        out.push((vid, kb.make_expr_carried(recv_term, member_sym)));
    }
    out
}

/// Non-recursive Constructor checker — peer of `check_apply_iter`.
/// Reads per-arg `TypeResult`s from `pos_results` / `named_results`
/// (pre-computed by the iterative typer) instead of calling
/// `type_check_node` itself. Handles both the surface
/// `constructor(name=…, args=[…])` form and implicit constructor calls
/// (an `Apply` whose functor is a constructor symbol — routed here
/// from `check_apply_iter`).
pub(super) fn check_constructor_iter(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    flow: &FlowEnv,
    ctor_sym: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
    span: Option<Span>,
    expected: Option<Value>,
    occ: &Rc<NodeOccurrence>,
) -> Result<TypeResult, TypeError> {
    let _ = pos_args; // arg-NodeOccurrence references kept for parity with check_apply_iter

    // Surface any sub-expression failure before continuing.
    collect_arg_errors(pos_results.iter().chain(named_results.iter()))?;

    // `()` and `(a, b, …)` parse as a `TupleLiteral` entity and the loader
    // wraps them as `constructor(name: Ref(TupleLiteral), args: …)`. They
    // land here even though they are not user-declared constructors, and
    // the declared `TupleLiteral` entity has no fields, so the field-driven
    // path below would type them as `sort_ref(TupleLiteral)` — which
    // doesn't unify with `Unit` or with a named-tuple type. Route to
    // tuple semantics instead.
    if kb.qualified_name_of(ctor_sym) == dt::qualified(dt::TUPLE_LITERAL) {
        return check_tuple_literal_constructor(
            kb,
            env,
            flow,
            named_args,
            pos_results,
            named_results,
            expected,
            occ,
        );
    }
    // WI-289: `[...]` / `{...}` that wasn't desugared to cons/nil (no
    // expected List/Set type at the use site — e.g. an op body
    // `-> List[T] = [...]`) is loaded as `constructor(name: ListLiteral
    // /SetLiteral, args: …)`. Like `TupleLiteral` above, the declared
    // entity has no element fields, so the field-driven path would type it
    // as `sort_ref(ListLiteral)` and fail the surrounding `List[T]` check.
    // Type it as `List[T = elem]` / `Set[T = elem]`, mirroring the
    // `Expr::ListLit` / `Expr::SetLit` builds. (The body node stays a
    // `constructor(ListLiteral)` for eval/codegen, which handle it.)
    // WI-393: QUALIFIED base names — a bare `"List"`/`"Set"` interns a symbol
    // whose qualified name is itself, which `canonical_sort_sym` never folds onto
    // the prelude sort, so a literal consumed as a Stream (`collect([1,2,3])`)
    // missed the carrier provider lookup. See the `ListLit` build frame.
    if kb.qualified_name_of(ctor_sym) == dt::qualified(dt::LIST_LITERAL) {
        return check_seq_literal_constructor(
            kb,
            env,
            pos_results,
            expected,
            occ,
            SeqLiteral::List,
        );
    }
    if kb.qualified_name_of(ctor_sym) == dt::qualified(dt::SET_LITERAL) {
        return check_seq_literal_constructor(kb, env, pos_results, expected, occ, SeqLiteral::Set);
    }

    // Free-standing entities (declared at namespace level, not nested in a
    // sort block) have no DISTINCT parent sort, but their entity_field_types IS
    // registered — the entity is its own type. Without this, a let-bound
    // `WorkItem(...)` types as `None`, the body's env loses enclosing_sort,
    // and downstream spec-op calls fail dispatch (WI-204 feedback).
    //
    // WI-946: the TOTAL belongs-to, which OWNS that reflexive case — this used to
    // open-code it as `strict(c)` + a `None` arm naming `ctor_sym`, which builds
    // the same `parent_type` but hands `finish_constructor_type` a `None` that
    // short-circuits `reconstruct_sort_params`. For an EPONYMOUS PARAMETRIC sort
    // that lost the build's param bindings: `operation mk(x: Int64) -> Box[T =
    // String] = Box(x)` loaded CLEAN, while the sort-nested spelling of the same
    // declaration was refused `expected Crate[T = String], got Crate[T = Int64]`.
    let parent_sort = kb.sort_of_constructor(ctor_sym);
    let parent_type = kb.make_sort_ref(parent_sort.unwrap_or(ctor_sym));
    // WI-20260826-JSFHG — read BEFORE `expected` is moved into the seed below.
    let expected_names_an_entity = expected
        .as_ref()
        .is_some_and(|exp| type_head_names_an_entity(kb, exp));

    let field_types = match kb.entity_field_types(ctor_sym) {
        Some(ft) => ft.to_vec(),
        None => {
            return Err(TypeError::NoConstructor {
                span,
                name: ctor_sym,
            })
        }
    };

    let mut subst = Substitution::new();
    let mut effects = Vec::new();

    // WI-384: fields unify FIRST so each argument pins its param, THEN the caller
    // `expected` fills only the still-free params (the args-before-expected order of
    // `check_apply_iter`, WI-379). A field that CONTRADICTS `expected` then wins in the
    // built type and the use-site return-conformance check rejects it
    // (`make() -> Option[String] = some(42)` builds `Option[Int]`, rejected) instead of
    // `expected` masking the contradiction. The expected-seed is moved BELOW the field
    // loops (but kept ABOVE the empty-bindings early-return, so 0-arg constructors
    // `nil()` / `Map.empty()` still pick up the hint). Sound only because the build
    // (below) is now robust to a param the fields left unbound — it includes it as a
    // fresh `?_` rather than DROPPING it (which had made `pair(h, t)` build
    // `Pair[B=List]`, losing `A`).

    // WI-342: `declared_type` is a carrier-agnostic `Value` (a value-in-type
    // field rides as `Value::Node`); pass it directly to `unify_types`.
    for (field_sym, declared_type) in &field_types {
        if let Some((idx, _)) = named_args
            .iter()
            .enumerate()
            .find(|(_, (s, _))| s == field_sym)
        {
            if let Ok(ref r) = named_results[idx] {
                let arg_ty = field_arg_type(kb, env, declared_type, r);
                unify_types(kb, &mut subst, &arg_ty, declared_type);
                merge_effects_into(kb, &mut effects, &r.effects);
            }
        }
    }

    for (i, r_opt) in pos_results.iter().enumerate() {
        if let Some((_, declared_type)) = field_types.get(i) {
            if let Ok(r) = r_opt {
                let arg_ty = field_arg_type(kb, env, declared_type, r);
                unify_types(kb, &mut subst, &arg_ty, declared_type);
                merge_effects_into(kb, &mut effects, &r.effects);
            }
        }
    }

    // WI-385: VALIDATE each supplied field value against its declared field type
    // — the FIELD peer of the operation-argument check in `check_apply_iter`. The
    // field unify loops above pin type-params for INFERENCE and DISCARD their
    // boolean, so before this a `fact Counter(n: "hello")` with `entity
    // Counter(n: Int)` loaded clean (a String in an Int field). `validate_arg_-
    // against_param` subtype-checks each supplied field value against its declared
    // type, GATED on groundness (a polymorphic field `some(value: T)` /
    // `pair(fst: A, …)` stays unchecked — the return-conformance path settles it),
    // emitting a loud `TypeMismatch` under the existing `EntityField` context. Run
    // BEFORE the expected-seed and bail before the type is built for a constructor
    // we've proven ill-formed. WI-408: a bare `T` in an `Option[T]` field is
    // accepted by RECORDING a some-coercion, materialized below.
    // WI-1059: this loop judges the SAME type the inference loops above unified —
    // [`field_arg_type`], not the raw `r.ty`. The two used to differ, and the note
    // that stood here said why the difference was harmless: "validation is
    // groundness-gated and a bare-spec receiver (`Stream`) is not ground, so it is
    // skipped here regardless". That was true only while a RIGID counted as
    // non-ground. Once a skolem is ground ([`type_value_is_ground`]), the raw `c : ?C`
    // reaches the check and is refused against the very field the inference loop had
    // just threaded it into — `FiniteCollection.map`'s `mapped(c, f)`, measured. One
    // spelling for both loops is the fix: a rebuild good enough to INFER from is the
    // one to JUDGE against.
    let mut field_type_errors: Vec<TypeError> = Vec::new();
    let mut some_wraps: Vec<(usize, Value)> = Vec::new();
    for (field_sym, declared_type) in &field_types {
        if let Some((idx, _)) = named_args
            .iter()
            .enumerate()
            .find(|(_, (s, _))| s == field_sym)
        {
            if let Ok(ref r) = named_results[idx] {
                match validate_field_arg(
                    kb,
                    env,
                    &mut subst,
                    r,
                    declared_type,
                    span,
                    ctor_sym,
                    *field_sym,
                ) {
                    ArgValidation::Ok => {}
                    ArgValidation::WrapSome { declared } => {
                        some_wraps.push((pos_results.len() + idx, declared));
                    }
                    ArgValidation::Fail(err) => field_type_errors.push(err),
                }
            }
        }
    }
    for (i, r_opt) in pos_results.iter().enumerate() {
        if let Some((field_sym, declared_type)) = field_types.get(i) {
            if let Ok(r) = r_opt {
                match validate_field_arg(
                    kb,
                    env,
                    &mut subst,
                    r,
                    declared_type,
                    span,
                    ctor_sym,
                    *field_sym,
                ) {
                    ArgValidation::Ok => {}
                    ArgValidation::WrapSome { declared } => some_wraps.push((i, declared)),
                    ArgValidation::Fail(err) => field_type_errors.push(err),
                }
            }
        }
    }
    if !field_type_errors.is_empty() {
        return Err(aggregate_errors(field_type_errors));
    }
    // WI-374 (user-decided 2026-06-12): ENFORCE the §3 parametricity tie for
    // CONSTRUCTOR fields — the field loops bind the parent sort's canonical
    // param vars through `T`-typed and bare-self-sort fields, and a
    // conflicting rebind was recorded but never consulted: `cons(head: 1,
    // tail: strList)` built `List[T = Int64]` with a String inside. Same
    // shared gate as the op-call check (per-var details, refinement
    // re-unified, parent's own params only); no rigid exemption — a rigid
    // reaches this subst only through a real field argument, where the
    // conflict is a genuine parametricity violation. Runs BEFORE the
    // expected-seed below, whose contradicting-hint unify is a deliberate
    // ignored no-op.
    if let Some(parent_sym) = parent_sort {
        enforce_member_tie(kb, &subst, parent_sym, ctor_sym, span, &[])?;
    }
    // WI-408: materialize the recorded some-coercions (see check_apply_iter) —
    // every return below reads the (possibly rebuilt) `occ`.
    let rebuilt_occ;
    let occ = if some_wraps.is_empty() {
        occ
    } else {
        rebuilt_occ = wrap_some_children(kb, occ, &some_wraps, pos_results, named_results);
        &rebuilt_occ
    };

    // WI-384 / WI-270: now seed the caller `expected` — it fills params the fields left
    // free (so a 0-arg `nil()` with a `List[Int]` hint still gets `T = Int`), and a
    // contradicting hint does NOT overwrite a field-pinned param: that param already
    // holds a concrete type, so unifying it against the hint just fails and is ignored,
    // leaving the field type in the build (→ use-site rejection of the contradiction).
    // WI-20260826-JSFHG — WHICH SORT THIS APPLICATION IS CLASSIFIED AT (§8.2). Both
    // readings satisfy "a term classified `C₁` is also of sort `S`"; the CHECKING
    // DIRECTION picks. An expected type naming a constructor gets the constructor, so a
    // `Colour.red` parameter / return / field is satisfiable at all; everything else —
    // including the two arms of an `if` joining at a declared `-> Colour` — keeps the
    // parent, which is what lets sibling constructors join.
    //
    // THE EXPECTATION IS NOT ASSUMED: this names OUR OWN `ctor_sym`, never the head the
    // hint carried, so `takeRed(blue(v: 1))` classifies at `blue` and is refused — and
    // the diagnostic now names both variants instead of the parent of a value the
    // compiler knew exactly.
    let classify_sym = if expected_names_an_entity {
        ctor_sym
    } else {
        parent_sort.unwrap_or(ctor_sym)
    };
    if let Some(exp) = expected {
        unify_types(kb, &mut subst, &TermIdView(parent_type), &exp);
    }

    // WI-578 — build the parameterized result type via the shared finish tail, so this
    // occurrence-typer and the value-typer ([`constructor_value_type`]) produce the SAME
    // type from one source (no drift). The field-unified `subst` pinned the params above.
    let ty = finish_constructor_type(kb, classify_sym, parent_sort, &subst);
    Ok(TypeResult {
        ty,
        env: env.clone(),
        effects,
        node: Rc::clone(occ),
    })
}

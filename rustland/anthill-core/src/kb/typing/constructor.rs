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
/// A literal's element type is compared against a DECLARATION, and there the erasure passes
/// a `String` into an `Int64` slot. It was first refused HERE and left alone in
/// [`compute_branch_join_type`], on the reading that a branch join's bare `Option` "is
/// honest and nothing further is claimed". It was not: an open slot is admitted at every
/// instance, so the erased join laundered through `if` as well, and the lattice itself was
/// repaired — the paragraph below, and [`open_slots_said_by`] for the open-beside-said
/// pair (WI-20261001-80ZV8).
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

/// The name of the wildcard an EMPTY literal carries for its element — `[]` is a `List[T =
/// ??T]`. One constant for the mint below and for the reader that tells this wildcard from
/// every other ([`is_empty_literal_element`]): it is the only wildcard that stands for a
/// type NO VALUE has, which is what lets a name close it to the bottom type.
pub(super) const EMPTY_LITERAL_ELEMENT: &str = "?T";

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
        let fresh = kb.intern(EMPTY_LITERAL_ELEMENT);
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
    effects_param_head_is(kb, sort, |kb, head| short_name_of(kb.local_name_of(head)) == member)
}

/// [`sort_param_is_effect_row`] keyed by the parameter's own symbol, for a caller on a hot path
/// that holds one: the two short names are compared in the symbol table, none copied out.
pub(super) fn sort_param_sym_is_effect_row(
    kb: &mut KnowledgeBase,
    sort: Symbol,
    param: Symbol,
) -> bool {
    effects_param_head_is(kb, sort, |kb, head| {
        short_name_of(kb.local_name_of(head)) == short_name_of(kb.local_name_of(param))
    })
}

/// Does `sort`'s own `EffectsRuntime` requirement name, as its `Effects` row, a parameter `is`
/// accepts? The one walk behind [`sort_param_is_effect_row`]'s two keys.
fn effects_param_head_is(
    kb: &mut KnowledgeBase,
    sort: Symbol,
    is: impl Fn(&KnowledgeBase, Symbol) -> bool,
) -> bool {
    let Some(effects_runtime) = effects_runtime_sym(kb) else {
        return false;
    };
    for entry in direct_requires_chain_rc(kb, sort).iter() {
        if !same_sort_canonical(kb, entry.required_sort, effects_runtime) {
            continue;
        }
        if let Some(v) = spec_binding_value(kb, &entry.spec, "Effects") {
            if let Some(head) = spec_binding_head_sym(kb, &v) {
                if is(kb, head) {
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
/// row) is not a receiver slot. The prologue [`bare_spec_arg_self_projection`] and
/// [`bare_spec_arg_provision_projection`] each spelled.
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
///
/// WI-20261001-80ZV8 — AND A ROW VARIABLE IS A ROW ALREADY. Wrapped, `ES` became the
/// one-tail row `{ES}`: the same row in a second spelling, which type unification equates
/// and the resolver's slot reconciliation ([`match_impl_param`]) does not. So a field
/// `Iterable[C = Source, Element = T, E = ES]` fed a `Stream[T = T, E = ES]` produced the
/// goal `Iterable[C = Stream[T, E = ES], …, E = {ES}]`, whose carrier binds the provider's
/// row to `ES` and whose own `E` then offers `{ES}` for the same slot — refused, `no impl
/// matches` (MEASURED, and confirmed from the other side: the same field annotated `ES =
/// {ES}` is refused where `ES = ES` loads — the reconciliation's own limit, which this
/// only stops the constructor from reaching).
///
/// A VARIABLE TERM ONLY. [`KnowledgeBase::row_tail_var_of`] also reads a `Ref` to a sort's
/// row parameter as one, and that spelling keeps the wrap it had: no program brings one
/// here with the carrier named beside it, so changing it would be changing something
/// nothing measures.
pub(super) fn effect_row_param_value(
    kb: &mut KnowledgeBase,
    field_base: Symbol,
    member_short: &str,
    val: Value,
) -> Value {
    if !sort_param_is_effect_row(kb, field_base, member_short) {
        return val;
    }
    match &val {
        Value::Term { id, .. }
            if matches!(kb.get_term(*id), Term::Var(Var::Global(_) | Var::Rigid(_))) =>
        {
            val
        }
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
/// Unifying that bare ref against a parameterized field type `source: Stream[SourceElement,
/// SourceEffects]` therefore binds NOTHING — the field's own params stay free. The element
/// only ever appeared to thread because a SIBLING field's declared type wrote the
/// projection (`mapped`'s transform `fn: (SourceElement) -> T`, fed `f: (x: s.T) -> Dst`,
/// pins `SourceElement = s.T`); the effect row, written nowhere a value flows through, was
/// left an unresolved `??_` (and then the provided `Stream[E = {SourceEffects,
/// TransformEffects}]` could not match the declared `Stream[E = {s.E, EffP}]` return).
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
    // WI-20261001-80ZV8: A CONSTRUCTOR IS NOT A RECEIVER. `nil` and `none` are leaf
    // references too, but each is a CONSTANT whose bare type is all there is to know: no
    // caller will ever say what `nil.T` is, so the projection is a name for nothing and
    // stays stuck for good. Formed anyway, it made `bag(items: nil)` a `Bag[T = nil.T]`,
    // which no declared `Bag[T = T]` admits — `operation empty() -> Self = bag(items:
    // nil)` was refused `expected Bag[T = ?T], got Bag[T = nil.T]` (MEASURED, and the
    // hand-written `-> Bag[T = T]` the same; only the bare `-> Bag`, which claims nothing,
    // loaded). Left out, the slot is open, as it is for `bag(items: List.empty())` or `[]`.
    if kb.is_constructor_symbol(recv) {
        return None;
    }
    // The argument must be a BARE receiver at that same base — either spelling
    // ([`bare_receiver_sort`], which owns that shape test and its WI-1059 half). An
    // already-applied argument (`s: Stream[S, EffS]`) threads through the ordinary arm
    // unchanged.
    //
    // WI-1059, and why the MATERIALIZED spelling has to answer here: it is the same
    // receiver, so it must thread the same way — in particular the effect-row param must
    // still bind the single-label ROW `{s.E}` rather than the bare projection, which is
    // the whole point of the loop below. MEASURED: without it, `mapped(s, f)` built
    // `MappedStream[SourceEffects = s.E, …]` where the provider view wants `SourceEffects =
    // {s.E}`, and `bare_map`'s declared `Stream[E = {s.E, EffP}]` return stopped conforming
    // (wi594). CANONICAL, not raw `Symbol`: one logical sort carries different `Symbol` ids
    // across import scopes ([`provider_spec_view_bindings`] documents that it does). A raw
    // compare declines here whenever the field type was resolved in another scope than the
    // argument, and [`bare_spec_arg_provision_projection`] — which excludes the self case
    // canonically — declines it too, so the receiver would thread NOWHERE and leak `??_`: the
    // very WI-594 symptom, reintroduced by a spelling. Both sides ask the same question, so
    // both ask it the same way.
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
        // provision's `{SourceEffects, TransformEffects}` structurally a present-atom + tail,
        // matching the declared return. A SORT param threads the bare projection
        // (`SourceElement = s.T`).
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
/// double-wrapped by [`effect_row_param_value`].
fn is_effects_rows_term(kb: &KnowledgeBase, t: TermId) -> bool {
    matches!(type_head(kb, &TermIdView(t)), TypeHead::EffectsRows)
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
fn param_leaves_belong_to_sort<V: TermView>(kb: &KnowledgeBase, t: &V, own_params: &[Symbol]) -> bool {
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
    match t.head(kb) {
        ViewHead::Ident(sym) => belongs(kb, sym),
        ViewHead::Functor {
            functor: Some(functor),
            pos_arity,
            ..
        } => {
            belongs(kb, functor)
                && view_all_children(kb, t, pos_arity, |c| {
                    param_leaves_belong_to_sort(kb, c, own_params)
                })
        }
        _ => true,
    }
}

/// WI-20261005-KSSA4 — A CONSTRUCTION MEETS ITS SORT'S REQUIREMENTS WHERE THE VALUE IS BUILT.
///
/// The value carries no dictionary. An operation reached THROUGH it — a member dispatched
/// on the value, an operation of a spec the sort provides — resolves the sort's `requires`
/// from the value itself, at run time ([`crate::eval`]'s value-directed frame), and enters
/// the frame without one where nothing answers. So a value built at an instance the
/// requirement has no supply for is a value no operation of the sort can run on, and the
/// construction is the last site that knows the instance.
///
/// MEASURED, with `MappedStream`'s field typed by its own `Source` and this check absent:
/// `mapped(5, f)` at a return type that pins every parameter loaded clean, was admitted at
/// `s: Stream`, and died `__req_iterable not bound in caller frame` inside
/// `MappedStream.splitFirst`. The field used to be typed at the spec, which refused the `5`;
/// a field typed by the parameter says nothing about the carrier, and the clause is what
/// does.
///
/// SUPPLY IS ASKED THROUGH THE BUILDER A CALL INTO THE SORT ASKS ([`build_concrete_dispatch_
/// dict`]): a provision at the instance, the constructing scope's own `requires`, a declared
/// bracket — and, inside the sort at the instance the scope itself runs at, the scope's own
/// frame. ONE DIFFERENCE, and [`RequirementUse::Construction`] is what tells the builder: a
/// call needs its dictionary now, so an element it leaves open is refused; a construction
/// needs none, and a slot it leaves open — fixed by the call the value is then passed to —
/// is left to that use. What is refused here is a requirement no provision could answer at
/// what the construction did fix ([`some_provision_could_answer`]). A refusal is raised here
/// and not parked: the park exists for a callee whose body is not typed yet, and a
/// construction has none.
///
/// IN VALUE DEFINITIONS: operation bodies and constant initializers (HK87X).
/// A rule's term is matched, not built: an operation reached from that rule
/// resolves its requirements from the bound value or suspends.
fn construction_meets_sort_requires(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    subst: &Substitution,
    ctor_sym: Symbol,
    sort: Symbol,
    span: Option<Span>,
) -> Result<(), TypeError> {
    if (env.enclosing_op().is_none() && env.enclosing_const.is_none())
        || direct_requires_chain_rc(kb, sort).is_empty()
    {
        return Ok(());
    }
    let enclosing_sort = env.enclosing_sort();
    let ctx = SigmaCtx {
        subst,
        param_rigids: env.param_rigids(),
    };
    let another_instance =
        enclosing_sort == Some(sort) && !call_is_at_callers_instance(kb, sort, &ctx);
    let caller_requires = env.enclosing_frame_chain().clone();
    let caller_requires = if another_instance {
        chain_at_callers_instance(kb, &caller_requires, env.param_rigids())
    } else {
        caller_requires
    };
    let refused = |refusal| TypeError::UnsatisfiableRequirement {
        span,
        op: ctor_sym,
        callee_sort: sort,
        usage: RequirementUse::Construction,
        refusal,
    };
    let mut unsuppliable: Option<Box<RequirementRefusal>> = None;
    // No held bracket: a `require[…]` is a rule clause's, not a value definition's.
    build_concrete_dispatch_dict(
        kb,
        None,
        &[],
        subst,
        sort,
        None,
        enclosing_sort,
        &caller_requires,
        env.param_rigids(),
        &[],
        RequirementUse::Construction,
        Some(&mut unsuppliable),
    )
    .map_err(refused)?;
    unsuppliable.map_or(Ok(()), |refusal| Err(refused(refusal)))
}

/// The type an entity FIELD's supplied argument is INFERRED from (WI-594).
///
/// WI-594: a bare spec receiver into a parameterized field threads its element AND effect
/// through its self-projection. WI-20260828-MDWEW: a bare SPEC-typed argument into a field
/// typed on a spec its sort provides — one that is its own carrier, so the argument IS a
/// value of it — threads through THAT provision. Else the raw inferred type.
///
/// A field typed at a spec over a parameter gets no rebuild (WI-20261005-KSSA4): a value
/// of a sort that provides `Iterable` is not an `Iterable`, and is refused there. A field
/// that holds any provider is typed by a parameter of its sort, which the sort's
/// `requires` clause is about ([`bind_sort_params_from_sort_requires_at_construction`]).
fn field_arg_type(kb: &mut KnowledgeBase, declared_type: &Value, r: &TypeResult) -> Value {
    bare_spec_arg_self_projection(kb, declared_type, r)
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
    let rebuilt = field_arg_type(kb, declared_type, r);
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

/// WI-20260828-MDWEW — a BARE argument flowing into a field typed on a spec that the
/// argument's sort PROVIDES and that is its own carrier: `x: Xchg` into `inner: Slot[Left =
/// HL, Right = HR]`, where `Xchg provides Slot[…]` and `Slot`'s operations receive on `Self`.
///
/// The argument IS a `Slot` — a sort that receives on itself is a type of its providers'
/// values — and its provision says at which arguments. [`bare_spec_arg_self_projection`]
/// (WI-594) answers only where the field applies the argument's OWN sort; here it applies
/// another, so unifying the raw type against the field binds nothing and the field's
/// parameters leak `??_`.
///
/// The fact that relates the two is the argument sort's own provision, written in the
/// ARGUMENT SORT's parameters. So: read that view — direct, or composed through the sorts
/// it provides — then substitute each of those parameters with the receiver's projection of
/// it ([`substitute_carrier_params`], keyed by the sort's canonical param VarIds), and key
/// the result by the FIELD's binding symbols so the ordinary [`unify_parameterized_view`]
/// arm threads every param.
///
/// A FIELD TYPED AT A SPEC OVER A PARAMETER IS NOT THIS CASE (WI-20261005-KSSA4). `source:
/// Iterable[C = Source, …]` fed a `Stream` was the shape this was written for: the argument's
/// sort is the `C` of an `Iterable`, not an `Iterable`, and the field refuses it. A field
/// that holds any provider is typed `source: Source` under the sort's `requires Iterable[C =
/// Source, …]`.
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
    // The field must APPLY a spec (`Slot[Left = …, …]`); a bare-sort field has no params
    // to thread, and a structural field (arrow / row) is not a receiver slot.
    let (field_base, bindings) = applied_spec_field(kb, declared_field_type)?;
    // …AND ONE THAT IS ITS OWN CARRIER (WI-20261005-KSSA4). A sort that provides it is then
    // a value of it, and its provision says at which arguments. A spec over a parameter is
    // not that: the argument's sort is its `C`, not the spec, and the field refuses it.
    if spec_has_carrier_param(kb, field_base) {
        return None;
    }
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
    let arg_sort = bare_receiver_sort(kb, &arg.ty, recv)
        .or_else(|| sort_functor_of_view(kb, &arg.ty))?;
    if kb.canonical_sort_sym(arg_sort) == kb.canonical_sort_sym(field_base) {
        return None;
    }
    // The relating fact: `arg_sort provides field_base[…]`, in `arg_sort`'s own params,
    // direct or composed through the sorts it provides.
    let mut visited: SmallVec<[Symbol; 8]> = SmallVec::new();
    let view = transitive_provider_spec_view_bindings(kb, arg_sort, field_base, &mut visited)?;
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
            // On the carrier it rides: a written argument that holds a value (`E =
            // {Modify[k]}`) says its parameter as plainly as one that is a term.
            match recv_projections.iter_mut().find(|(pv, _)| *pv == vid) {
                Some(slot) => slot.1 = v.clone(),
                None => recv_projections.push((vid, v.clone())),
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
    for (field_key, _) in &bindings {
        // Identity join on the SPEC's own parameter — the field's binding keys and the
        // provision's are resolved in two scopes and can be two Symbols for one param.
        let key_vid = type_param_vid_in_sort(kb, field_base, *field_key)?;
        let raw = view
            .iter()
            .find(|(sp, _)| type_param_vid_in_sort(kb, field_base, *sp) == Some(key_vid))
            .map(|(_, v)| v)?;
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
        if !type_is_determined(kb, &val) {
            return None;
        }
        // An EFFECT-ROW param threads as a single-label row (`{s.E}`); a SORT param threads
        // the substituted value bare. A value already stored as a row is kept as read.
        let member_short = short_name_of(kb.local_name_of(*field_key)).to_owned();
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
) -> Vec<(VarId, Value)> {
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
        out.push((vid, Value::term(kb.make_expr_carried(recv_term, member_sym))));
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

    // WI-20261001-80ZV8 — A CONSTRUCTOR IS A CALL: a parameter of its sort that several
    // fields bind takes their join ([`join_repeated_sort_params`]) before the loops below
    // unify in field order, which let the first field decide. `cons(head: c, tail: ss)` over
    // a `Circle` and a `List[T = Shape]` was refused, `cons.tail: expected List[T = Circle],
    // got List[T = Shape]`, where `cons(head: s, tail: cs)` loaded and the literal `[c, s]`
    // joined (MEASURED). The same types the loops unify are the ones joined
    // ([`field_arg_type`]). Asked only where more than one field is supplied, of a sort that
    // has a parameter ([`sort_params_join`]).
    if let Some(sort) = parent_sort
        .filter(|s| pos_results.len() + named_results.len() > 1 && sort_params_join(kb, *s))
    {
        let mut supplied: Vec<(Symbol, Value, Value)> = Vec::new();
        for (i, (field_sym, declared_type)) in field_types.iter().enumerate() {
            let named = named_args
                .iter()
                .position(|(s, _)| s == field_sym)
                .map(|idx| &named_results[idx]);
            for r in named.into_iter().chain(pos_results.get(i)).flatten() {
                let arg_ty = field_arg_type(kb, declared_type, r);
                supplied.push((*field_sym, declared_type.clone(), arg_ty));
            }
        }
        let refs: Vec<(Symbol, &Value, &Value)> =
            supplied.iter().map(|(f, d, a)| (*f, d, a)).collect();
        join_repeated_sort_params(kb, &mut subst, sort, &refs);
    }

    // WI-342: `declared_type` is a carrier-agnostic `Value` (a value-in-type
    // field rides as `Value::Node`); pass it directly to `unify_types`.
    for (field_sym, declared_type) in &field_types {
        if let Some((idx, _)) = named_args
            .iter()
            .enumerate()
            .find(|(_, (s, _))| s == field_sym)
        {
            if let Ok(ref r) = named_results[idx] {
                let arg_ty = field_arg_type(kb, declared_type, r);
                unify_types(kb, &mut subst, &arg_ty, declared_type);
                merge_effects_into(kb, &mut effects, &r.effects);
            }
        }
    }

    for (i, r_opt) in pos_results.iter().enumerate() {
        if let Some((_, declared_type)) = field_types.get(i) {
            if let Ok(r) = r_opt {
                let arg_ty = field_arg_type(kb, declared_type, r);
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
    // WI-20261005-KSSA4 — what the sort's own `requires` clauses say of a parameter no
    // field is typed by, at the carrier the fields fixed. Above the `expected` seeding, as
    // the operation-level reading is: a caller's claim about the result is not evidence
    // about the carrier.
    if let Some(sort) = parent_sort {
        bind_sort_params_from_sort_requires_at_construction(kb, &mut subst, Some(env), sort);
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
    // THE SORT AT ITS OWN PARAMETERS is what meets the expectation (WI-20261001-80ZV8, stage
    // (e)): those parameters' variables are the ones the fields bound above, so unifying the
    // two slot by slot fills exactly the ones still free. It used to be the sort's BARE name,
    // read through the unifier's canonical channel — the one reader that channel had left.
    if let Some(exp) = expected {
        let own = own_application(kb, parent_sort.unwrap_or(ctor_sym));
        unify_types(kb, &mut subst, &TermIdView(own), &exp);
    }
    // The instance is what the fields, the sort's clauses and the expectation fixed, and
    // that is the instance the requirement is owed at: asked above the seeding, a parameter
    // only the expected type says is still open, some provision could answer it, and
    // `-> Hold[E = Other] = vacant()` loads over an `Other` that provides nothing
    // (`wi_kssa4_spec_typed_value_test …a_parameter_only_the_expected_type_fixes_is_judged`).
    if let Some(sort) = parent_sort {
        construction_meets_sort_requires(kb, env, &subst, ctor_sym, sort, span)?;
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

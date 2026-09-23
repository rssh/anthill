//! Polymorphic instantiation and eta: an operation used as a function value, and the
//! dictionaries such a value carries.

use super::*;

/// WI-206: whether `expected` is the reflect `Type` sort — the slot in which a
/// bare sort name denotes the sort itself (`is_modifiable(Cell)`). Resolving
/// `anthill.prelude.Type` can fail on a partial-stdlib KB; that yields `false`
/// (no `Type` slot exists to admit the reading), never a vacuous match against an
/// WI-1083 — ∀-INTRODUCTION for an eta lift: wrap `arrow` in a
/// [`TypeExtractor::PolyType`] over the variables `op`'s signature binds, or hand it
/// back unwrapped when there are none.
///
/// UNWRAPPED WHEN THE SET IS EMPTY, deliberately: `PolyType([], arrow)` and `arrow` are
/// the same type, and minting the wrapper anyway would put a form every reader has to
/// see through on the path of a lift that quantifies nothing. "A `PolyType` has at least one
/// binder" is therefore an invariant, not a convention.
///
/// THE SET IS WIDER THAN "DECLARES `[A]`", which is the widest consequence of this change and
/// is worth stating here rather than leaving to be discovered: [`signature_bound_vars`] also
/// counts a free logical variable written in a parameter type or a `requires`, and the
/// DECLARING SORT's canonical parameter. So a member of a parameterized sort — `SortedSet.
/// insert(s: SortedSet[T = T, O = O], x: T)`, which declares no brackets at all — now lifts to
/// a ∀ where it used to lift to a bare arrow, and each reference gets its own `T`/`O` instead
/// of writing into the sort's canonical channel. That is the intended reading (§5.6: the
/// caller instantiates), and the one place it must NOT be applied is the dictionary pin — see
/// [`poly_type_body`], with the test that measures it.
///
/// The binders come from [`signature_bound_vars`], the one owner — see its doc for why
/// generalizing here rather than at load or at instantiation is what makes this SUBSUME
/// WI-1078's rule instead of contradicting it.
fn generalize_eta_arrow(
    kb: &mut KnowledgeBase,
    sym: Symbol,
    op: &OperationInfoFull,
    arrow: Value,
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Value {
    let binders = signature_bound_vars(kb, sym, &op.params, &op.requires, &op.type_params);
    if binders.is_empty() {
        return arrow;
    }
    let binder_terms: Vec<Value> = binders
        .iter()
        .map(|v| Value::term(type_param_var_term(kb, Var::Global(*v))))
        .collect();
    let binder_list = crate::kb::load::build_value_list(kb, binder_terms);
    let body = value_to_type_child(kb, &arrow);
    // WI-20260904-50B2K part (c): an EMPTY context, so every ∀ this mint builds is exactly
    // the plain one it built before. An OPERATION's constraints are its written `requires`
    // clause, whose owner is `SortRequiresInfo` and whose variables `signature_bound_vars`
    // already quantifies above — moving them here would be a second owner for a fact that
    // HAS one, which is the very objection the entity's doc raises. The context is for the
    // type that has NO declaration site: a lambda's arrow.
    let empty_context = crate::kb::load::build_value_list(kb, Vec::new());
    Value::Node(kb.make_poly_type_occ(binder_list, empty_context, body, span, owner))
}

/// WI-1083 — ∀-ELIMINATION: if `ty` is a [`TypeExtractor::PolyType`], return its body
/// with every binder replaced by a FRESH variable; otherwise `None`, so a caller reads
/// "not a ∀" as an answer rather than as a failure.
///
/// PER REFERENCE, WHICH IS THE WHOLE MECHANISM. The eta gate excluded a
/// type-parameterized operation because "its arrow would carry unfreshened type-param
/// vars that alias across multiple eta-lifts of the same op" — true of an arrow, which
/// has nowhere to write a binder, and false of a ∀, whose binders say exactly which
/// variables to freshen. Each elimination mints its own, so two references to one
/// operation cannot see each other's bindings.
///
/// ONE CALLER, [`check_bare_ref`], and that is a decision the first cut got wrong.
/// Eliminating inside the type RELATIONS (`unify_types` / `types_compatible`) reads as the
/// tidier place and is measurably useless: each relation would mint its own instantiation,
/// so the binding the argument-unify loop makes lands on a variable the conformance check
/// that follows has never seen, and every disagreement stays invisible. The reference is
/// where §5.6's "the caller instantiates" actually happens, and it is the one site where a
/// single instantiation serves every later step. [`poly_type_body`] is the deliberate
/// exception — one reader must see the un-freshened body, and says why.
///
/// The substitution is applied by [`crate::kb::node_occurrence::subst_value_type`] under a
/// scratch [`Substitution`] holding `binder ↦ fresh` — the shared close/open/σ walk, so the
/// freshening reaches every child a σ would rather than a hand-rolled walk that would have
/// to be kept in step with it.
///
/// NOT [`walk_type_deep_value`], which is what the first cut used and which was WRONG HERE
/// for a reason that has since been REPAIRED AT ITS SOURCE: it routes a `Value::Node`
/// through [`rewrite_type_occ_deep`], whose `NamedTuple` arm answered "unchanged" until
/// WI-20260904-02ERR gave it a walking arm. The measurement below is therefore historical —
/// it is why this function uses the shared close/open/σ walk, and that choice still stands
/// on its own ground (one walk, kept in step with σ by construction), but the specific hole
/// it dodges is closed. An eta arrow's parameter LIST is a `named_tuple`, and it rides the
/// Node carrier whenever any parameter's type does (an arrow parameter always does) — so
/// every multi-parameter higher-order operation had its parameter-position binders left
/// SHARED between references, which is precisely the aliasing the deleted gate existed to
/// prevent. MEASURED on the loaded stdlib before the fix: `MappedStream.map` leaked four of
/// its eight binders (`?S`, `?EffS` and the sort's own two), `Iterable.map` two,
/// `FilteredStream.filter` three. Found by review; the unit rows use a ONE-parameter
/// operation, whose parameter is a bare `Term`, and stayed green throughout.
///
/// THAT READING IS HISTORICAL AND ITS SUBJECTS HAVE MOVED: WI-20260829-X13YV re-typed
/// `MappedStream.map` and `FilteredStream.filter` onto their own carriers, so neither
/// declares `?S` or `?EffS` any more and re-running the count on today's stdlib will not
/// reproduce those figures. The measurement is kept because it is what justifies this
/// function's choice of walk, not as a live inventory — `Iterable.map` is the one named
/// operation whose signature is unchanged.
/// WI-20260904-50B2K part (c), step 2 — one ∀-ELIMINATION, with everything its consumers
/// need to dispose of what the schema was carrying.
pub(crate) struct PolyInstantiation {
    /// The body with every binder freshened — the type this occurrence actually has.
    pub(super) ty: Value,
    /// The context, freshened with the body: the constraints this use now OWES.
    pub(super) obligations: Vec<Value>,
    /// `(binder, fresh)` per binder. It is what links an obligation back to the walk that
    /// generalized it — see [`WalkSolutions::note_instantiation`], which keys on this
    /// rather than on the obligations because two values' contexts can name one spec.
    pub(super) binder_map: SmallVec<[(VarId, VarId); 2]>,
}

pub(super) fn instantiate_poly_type<V: TermView>(
    kb: &mut KnowledgeBase,
    ty: &V,
) -> Option<PolyInstantiation> {
    // HEAD FIRST, then the children: `type_head` reads at most the functor symbol, while
    // `extract_type` materializes a fresh child vector with every bound type cloned into it
    // (the cost the typer's WI-798 notes exist to keep off hot paths). Every bare-reference
    // check pays the head classify; only an actual ∀ pays the rest.
    if !matches!(type_head(kb, ty), TypeHead::PolyType) {
        return None;
    }
    let TypeExtractor::PolyType {
        binders,
        context,
        body,
    } = extract_type(kb, ty)
    else {
        return None;
    };
    let mut fresh = Substitution::new();
    let mut binder_map: SmallVec<[(VarId, VarId); 2]> = SmallVec::new();
    for b in &binders {
        // A binder that is not a flexible variable term is a malformed ∀ — the one mint
        // ([`generalize_eta_arrow`]) builds nothing else. LOUD in dev rather than silently
        // dropped, because a dropped binder does not fail: it leaves that variable SHARED
        // between two references, which is exactly the aliasing this function exists to
        // retire, and it would show up as an unrelated type error somewhere else.
        // A binder that is not a flexible variable term is a malformed ∀ — the one mint
        // ([`generalize_eta_arrow`]) builds nothing else. DECLINE THE WHOLE ELIMINATION
        // rather than skip the binder: a skipped one does not fail, it leaves that variable
        // SHARED between two references — the aliasing this function exists to retire — and
        // surfaces later as an unrelated type error. `None` routes to [`check_bare_ref`]'s
        // loud `TypeError`, which is the channel that already exists for exactly this.
        // (Was `debug_assert!` + `continue`, i.e. silent in a release build.)
        let Value::Term { id, .. } = b else {
            return None;
        };
        let Term::Var(Var::Global(vid)) = kb.get_term(*id) else {
            return None;
        };
        let vid = *vid;
        let new_vid = kb.fresh_var(vid.name());
        let new_term = kb.alloc(Term::Var(Var::Global(new_vid)));
        fresh.bind(kb, vid, new_term);
        binder_map.push((vid, new_vid));
    }
    let (instantiated, _) = crate::kb::node_occurrence::subst_value_type(kb, &body, &fresh);
    // WI-20260904-50B2K part (c) — THE CONTEXT IS FRESHENED WITH THE BODY AND HANDED BACK,
    // because ∀-elimination is exactly where a constraint becomes answerable: the binders
    // have just become concrete. Dropping it here would be the fail-open the whole slice
    // exists to avoid, so the obligation is RETURNED and the caller must dispose of it.
    let instantiated_context: Vec<Value> = context
        .iter()
        .map(|c| crate::kb::node_occurrence::subst_value_type(kb, c, &fresh).0)
        .collect();
    Some(PolyInstantiation {
        ty: instantiated,
        obligations: instantiated_context,
        binder_map,
    })
}

/// WI-1083 — a ∀'s BODY WITHOUT FRESHENING, for the one reader that must see the
/// operation's OWN variables: [`attach_eta_dispatch_dict`]'s element-type pin.
///
/// That pin unifies the eta arrow's parameter against the expected one to learn what to
/// build a dictionary for (`List.T := Int64`), and the dictionary's dependencies name
/// the DECLARING SORT's canonical parameters. Handing it an instantiation would bind
/// fresh variables the dependency lookup has never heard of, so a resolvable requirement
/// would go unresolved and the eta would be refused as unsatisfiable — a new refusal for
/// programs that work today.
///
/// Sound because that σ is LOCAL and discarded: it exists to select a witness, never to type
/// the value. The value's type is instantiated separately at the reference
/// ([`check_bare_ref`]) — so the two readings share no bindings and the aliasing the
/// per-reference rule exists to prevent cannot come back through here.
///
/// DRIVEN by `wi844_sorted_set_driver_test::an_etad_op_takes_its_ordering_from_the_expected_-
/// arrow`, which is the ONE test in the suite that fails when this is replaced by
/// [`instantiate_poly_type`]: `SortedSet.insert(s: SortedSet[T = T, O = O], x: T)` names its
/// own sort's parameters, `Ord[T = T]` is keyed by the same canonical variables, and a pin made
/// on fresh ones leaves the requirement "unsatisfiable … (WI-420)". The WI-1083 test file's own
/// attempt at this row does NOT catch it and says so at its site — worth knowing, because the
/// widest consequence of this ticket is exactly the case that row was aimed at: a member of a
/// PARAMETERIZED sort now lifts to a ∀ whether or not it declares `[A]` of its own.
fn poly_type_body<V: TermView>(kb: &mut KnowledgeBase, ty: &V) -> Option<Value> {
    if !matches!(type_head(kb, ty), TypeHead::PolyType) {
        return None;
    }
    match extract_type(kb, ty) {
        // WI-20260904-50B2K part (c) — THE THIRD ∀-READER, AND IT REFUSES RATHER THAN
        // DROPPING. `check_bare_ref` returns a `TypeError` on a non-empty context and
        // `eliminate_node_projections` asserts emptiness; this reader patterned `{ body, .. }`
        // and discarded one WITHOUT A WORD, which in a release build is the wrong accept the
        // whole slice exists to prevent. An eta'd op reference goes through both paths, so
        // step 2 reaches here on its first program. /code-review found it twice — once for
        // the silence, once because a `debug_assert` alone is silence in release.
        //
        // TWO BEHAVIOURS, BOTH DELIBERATE, because the doc first claimed only the second and
        // /code-review asked which one it is. IN A DEBUG BUILD THE ASSERT ABORTS — it is the
        // tripwire that makes whoever writes step 2 handle this reader, the same role
        // `check_bare_ref`'s `TypeError` plays on the other path. IN A RELEASE BUILD IT
        // REFUSES: `None` sends the caller to `arrow_parts(kb, fn_ty)`, which also answers
        // `None` for a ∀, so the element pin does not happen and the dictionary build is
        // handed an empty σ — measured under WI-844 to raise a REFUSAL naming the dep it
        // could not construct. Neither path can accept a program whose constraints were
        // thrown away, which is the property that matters; not pinning is strictly less
        // committed than pinning off a body stripped of its context.
        TypeExtractor::PolyType { context, body, .. } => {
            debug_assert!(
                context.is_empty(),
                "poly_type_body: a ∀ with constraints reached the eta dictionary pin, which \
                 has no way to discharge them",
            );
            if context.is_empty() {
                Some(body)
            } else {
                None
            }
        }
        _ => None,
    }
}

/// `expected` whose own head sort is likewise unresolvable.
pub(super) fn expects_reflect_type(kb: &KnowledgeBase, expected: Option<&Value>) -> bool {
    let Some(exp) = expected else { return false };
    let Some(type_sym) = kb.try_resolve_symbol("anthill.prelude.Type") else {
        return false;
    };
    extract_sort_ref_sym(kb, exp) == Some(type_sym)
}

/// WI-275: the type of an operation referenced as a first-class function value
/// (eta-expansion). `inc(n: Int) -> Int` becomes `Int -> Int`; a
/// multi-param `lt(a: T, b: T) -> Bool` becomes `(T, T) -> Bool` — a positional
/// `_1`/`_2` named-tuple param (the WI-355 tuple convention) so it unifies
/// against a `Function[(T, T), Bool]` slot, matching how a `lambda (a, b) -> ...`
/// is typed and an `f((a, b))` applied. Returns `None` when `sym` is not an eta
/// candidate (no operation, or body-less) so the caller falls back to the
/// return-type reading. A `requires`-carrying op's
/// dispatch dict is resolved + attached separately by `attach_eta_dispatch_dict`
/// (WI-420), which has the `expected` arrow that pins the element type.
///
/// WI-1083 — AN ARROW, OR A ∀ OVER ONE. Whenever the signature binds a variable, the
/// arrow is wrapped by [`generalize_eta_arrow`] and each USE instantiates it, so
/// nothing here is shared between two lifts of one operation.
pub(super) fn operation_as_function_value(
    kb: &mut KnowledgeBase,
    sym: Symbol,
    occ: &Rc<NodeOccurrence>,
) -> Option<Value> {
    // Only eta-lift an operation the runtime can actually run as a function
    // value, keeping the typer's accepted set a subset of the evaluator's: it must
    // have a runnable anthill body — the evaluator's `reduce_var` mints a
    // `Value::OpRef` only for body-having ops, so a body-less builtin / spec
    // declaration would type-check here yet crash at eval as a zero-arg call
    // (`ArityMismatch`). A reference that fails that gate stays a loud type error,
    // not a silent runtime failure.
    if !op_has_runnable_body(kb, sym) {
        return None;
    }
    let op = lookup_operation_info_full(kb, sym)?;
    // WI-700: a NULLARY op is eta-lifted too — to `() -> ret @ row`, a Unit-shaped
    // (empty-`NamedTuple`) param produced by the builder below — so a bare nullary
    // op passed into a callback slot carries its DECLARED effect row into the
    // WI-440/469 conformance checks instead of collapsing to its return type (the
    // pre-WI-700 hole: `ty=Int64 effects=[]`, arrow + row both dropped).
    //
    // WI-1083 DELETED THE SECOND CLAUSE, which read `if !op.type_params.is_empty() {
    // return None }` on the grounds that "its arrow would carry unfreshened type-param
    // vars that alias across multiple eta-lifts of the same op". True of an ARROW, which
    // has nowhere to write a binder; the ∀ this function now mints says which variables
    // to freshen and every use freshens them.
    //
    // AND IT WAS A SOUNDNESS HOLE, NOT ONLY A MISSING CAPABILITY, which is what the
    // clause's own wording hides: refusing the lift did not refuse the PROGRAM, it fell
    // through to `check_bare_ref`'s zero-arg-call reading, which types a bare `idp[A](x:
    // A) -> A` as its return type `?A` — a bare flexible variable that unifies with any
    // expected type at all. MEASURED, each against its monomorphic twin, which is
    // REFUSED in every row: a result-type mismatch (`A -> A` into an `Int64 -> String`
    // slot), an arity mismatch (a 2-parameter operation into a 1-parameter slot) and an
    // effect-row mismatch (`effects {Error}` into `E = {}`) all LOADED CLEAN for a
    // type-parameterized operation. `wi1083_polytype_test` holds all six rows.
    let (span, owner) = (occ.span, occ.owner);
    // WI-1063: the eta arrow's RESULT is a use of the operation's declared return, so it
    // OPENS like every other one. Without this the lift laundered the existential — DRIVEN,
    // `apply_it(widen, s)` with `widen` declared exactly as the ticket's headline program put
    // `{Error}` into a slot declaring `E = {}`, one indirection past the direct call.
    //
    // ONE SKOLEM PER LIFT, NOT PER APPLICATION, and that is a real limit rather than an
    // oversight: an arrow type has nowhere to write `∃`, so whatever goes in the result
    // position is fixed for the VALUE and every application of it reads the same ρ.
    //
    // WI-1083 DID NOT MOVE IT, and the ∀ this function now mints is why the limit is
    // narrower than it looks rather than why it is gone. The two quantifiers are opened by
    // different machinery: a ∀'s binders are WRITTEN (the `PolyType` below carries them)
    // so `instantiate_poly_type` can freshen them per application; an ∃ has no binder node
    // at all (WI-1079 — at a declaration it is implied by the return POSITION), so the ρ
    // minted here is the one this value has. An unbound return variable is exactly a
    // variable `signature_bound_vars` does NOT list, so the two rules partition the
    // signature's variables between them and neither can claim one twice.
    //
    // REFUSING THE LIFT INSTEAD IS REFUTED, and the measurement is worth keeping because the
    // clause above makes it look like the obvious answer (it refuses a type-parameterized op
    // for the sibling aliasing reason). `Function` declares an effect-row parameter, so the
    // perfectly ordinary `build(seed: Int64) -> Function[A = Int64, B = Bool]` leaves a slot
    // unwritten and would be refused too. Control falls through to the zero-arg-call reading,
    // whose result then conforms width-tolerantly to the annotation, and
    // `wi420_eta_of_curried_requires_op_is_loud_type_error` goes from a loud load error to a
    // clean load that crashes at eval — precisely the "typer's accepted set is a subset of the
    // evaluator's" invariant this function opens by stating.
    let return_type = open_existential_return(
        kb,
        impl_parent_sort_of_op(kb, sym),
        sym,
        &op.return_type,
        span,
        owner,
    )
    .unwrap_or_else(|| op.return_type.clone());
    let param = if op.params.len() == 1 {
        op.params[0].1.clone()
    } else {
        let fields: Vec<(Symbol, Value)> = op
            .params
            .iter()
            .enumerate()
            .map(|(i, (_, t))| (kb.intern(&positional_label(i)), t.clone()))
            .collect();
        named_tuple_value(kb, &fields, span, owner)
    };
    // WI-791: the op's OWN parameter count — the arrow's arity is the operation's
    // arity, whatever its sole parameter's type happens to look like. `get_a(t: (a,
    // b))` mints arity 1 even though `param` is a 2-field `named_tuple`, so it no
    // longer passes for the genuinely 2-parameter `(p: A, q: B) -> R`.
    let arrow = make_arrow_value(
        kb,
        &param,
        &return_type,
        &op.effects,
        op.params.len(),
        span,
        owner,
    );
    // WI-1083: ∀ over whatever the signature binds — and the bare arrow unchanged when it
    // binds nothing, which is every operation this function could lift before.
    Some(generalize_eta_arrow(kb, sym, &op, arrow, span, owner))
}

/// WI-700: is `sym` a NULLARY (zero-parameter) operation? Only a nullary op has both
/// a zero-arg-call reading (`ret`) and an eta reading (`() -> ret`) in an arrow-typed
/// slot, so `check_bare_ref` consults this to decide when the return-type reading
/// should win over eta. (Reads the authoritative op record — the same source
/// `operation_as_function_value` used to build the eta arrow.)
pub(super) fn operation_is_nullary(kb: &KnowledgeBase, sym: Symbol) -> bool {
    lookup_operation_info_full(kb, sym).is_some_and(|op| op.params.is_empty())
}

/// WI-420: at a bare-op eta site, resolve the operation's requirement dispatch
/// dict and attach `CallClass::EtaOpRef` to the occurrence so eval captures it on
/// the `Value::OpRef` at mint. `fn_ty` is the op's eta arrow, `expected` the arrow
/// type it is checked against; unifying them pins the op's element type (e.g.
/// `member`'s `List.T := Int` from a `Function[(Int, List[Int]), Bool]` slot),
/// which `build_concrete_dispatch_dict` needs to resolve a concrete dep (`Eq[Int]`
/// from its `fact`) or forward an abstract one the enclosing sort's own `requires`
/// covers (a caller-frame `var_ref`). A requires-free or same-sort op needs no
/// dict (eval forwards the caller's requirements). A cross-sort op whose
/// requirement is neither concretely resolvable nor covered by the enclosing scope
/// is a loud error — the eta analogue of `MissingRequiresForSpecOp` for a direct
/// call.
///
/// WI-700: the `EtaOpRef` marker is now set at EVERY eta site — a requires-carrying
/// op carries `dict = Some(...)`, a requires-free / namespace op carries
/// `dict = None`. Previously the requires-free/namespace cases set NO
/// classification (eval minted the `OpRef` by arity ≥ 1). A NULLARY eta cannot be
/// distinguished from a zero-arg call by arity, so eval reads this marker to decide
/// — hence it must be present even when there is no dict to attach.
pub(super) fn attach_eta_dispatch_dict(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    sym: Symbol,
    occ: &Rc<NodeOccurrence>,
    fn_ty: &Value,
    expected: &Value,
) -> Result<(), TypeError> {
    // WI-1087: computed ONCE, ahead of the five classification branches below, so the
    // mapping cannot be attached on some eta paths and dropped on others. Every branch
    // marks the occurrence; a branch that forgot these labels would silently give the
    // operation spelling a source-order spread while its lambda twin read by name.
    let spread_labels = function_slot_spread_labels(kb, sym, expected);
    // WI-1091 — THE OP HALF, computed before every branch below and for the same reason
    // `spread_labels` is: each branch marks the occurrence and returns, and three of them
    // return before any dictionary is built at all. `List.member` reaches the SECOND of
    // them (`List` declares no `requires`), so an eta of the one stdlib operation with an
    // op-scoped clause was minting a dict-less `OpRef` — which value-direction covered
    // for, and WI-1091's widened placement does not.
    // WI-20260921-28TAT: STAMPED HERE, once, rather than threaded into each of the five
    // `EtaOpRef` constructions below. Same "computed ahead of the branches" discipline as
    // `spread_labels`, now enforced by there being nowhere else to put it — the evidence
    // is a property of this call site, not of which dispatch branch it takes.
    let (subst, selected) =
        eta_op_scoped_dicts(kb, env, sym, fn_ty, expected, Some(occ.span.span), occ)?;
    let Some(parent) = impl_parent_of_op(kb, sym) else {
        // Namespace-level op — no enclosing sort `requires`. WI-700: still MARK the
        // eta (dict None) so a nullary eta mints an `OpRef` at eval (a namespace op
        // like `poke` reaches only this arm). WI-1091: a namespace-level op may still
        // write `requires` of its OWN, so the op half rides even here.
        occ.set_classification(CallClass::EtaOpRef {
            dict: None,
            spread_labels,
        });
        return Ok(());
    };
    // WI-869: the same "does this callee read requirement slots" question the three
    // classification sites ask, through the one owner — and the fourth site that asked
    // it inline. An eta'd op on a carrier whose requirements are all provision
    // conditions would otherwise mint a dict-less `OpRef` for a body that reads them.
    if !op_reads_requirement_slots(kb, sym) {
        // Requires-free SORT — eval forwards the caller's reqs. WI-700: MARK the eta
        // (dict None) regardless, so a nullary eta mints an `OpRef` at eval.
        occ.set_classification(CallClass::EtaOpRef {
            dict: None,
            spread_labels,
        });
        return Ok(());
    }
    // WI-20260923-WN9P8 — and only where the capture IS the forward for every named slot
    // of the sort; otherwise the cross-sort build below answers each slot by its binder.
    if env.enclosing_sort() == Some(parent)
        && frame_serves_callee(env.enclosing_dict_chain(), callee_frame_key(kb, sym))
        && inherit_answers_every_forward(
            kb,
            parent,
            &SigmaCtx {
                subst: &subst,
                param_rigids: env.param_rigids(),
            },
        )
    {
        // Same-sort eta: the op needs its OWN sort's dispatching dict. A DIRECT
        // same-sort call inherits the enclosing frame at eval, but an eta'd
        // `OpRef` ESCAPES to a foreign apply frame (the HOF's), which forwards an
        // empty requirements channel — so the op's `__req_*` would be unbound
        // (a typecheck-clean eval crash). Capture the enclosing frame's
        // `__req_self` (the sort's own dispatching dict, identical to what this
        // op needs) at mint via a `var_ref`, and install it at apply. (WI-420)
        let Some(syms) = ProjectionSyms::resolve(kb) else {
            occ.set_classification(CallClass::EtaOpRef {
                dict: None,
                spread_labels,
            });
            return Ok(());
        };
        let req_self = kb.intern("__req_self");
        let dict = build_req_var_ref(kb, &syms, req_self);
        occ.set_classification(CallClass::EtaOpRef {
            dict: Some(dict),
            spread_labels,
        });
        return Ok(());
    }
    let caller_requires = env.enclosing_dict_chain().clone();
    let callee_provision = op_owner_provision(kb, sym);
    match build_concrete_dispatch_dict(
        kb,
        // The eta route's `Ok(None)` is ALREADY a load error (WI-420), so it has no use
        // for the rule-body verdict — see the parameter's own note.
        None,
        // …and for the same reason no use for route 4: it cannot act on the verdict
        // either way.
        &[],
        &subst,
        parent,
        callee_provision,
        env.enclosing_sort(),
        &caller_requires,
        env.param_rigids(),
        &selected,
        // WI-945: the eta route needs no parked verdict — its `Ok(None)` arm below is
        // ALREADY a load error (WI-420), for the reason that makes the verdict
        // unconditional here: an `OpRef` escapes to a foreign apply frame, so a dict
        // missing at mint is missing for good, whatever the body does with it.
        None,
    ) {
        Ok(Some(dict)) => {
            occ.set_classification(CallClass::EtaOpRef {
                dict: Some(dict),
                spread_labels,
            });
            Ok(())
        }
        // WI-828: the σ-refusal signature (a σ-refused cover / an Ambiguous
        // construction of an unconstrained element) names WHY the eta is
        // unsatisfiable — the bare WI-420 error below told the author neither
        // the refused entry nor the unconstrained element.
        Err(refusal) => Err(TypeError::UnsatisfiableRequirement {
            span: Some(occ.span.span),
            op: sym,
            callee_sort: parent,
            eta: true,
            refusal,
        }),
        Ok(None) => {
            // Cross-sort op with a non-empty direct `requires` chain that we
            // could resolve neither concretely (no `fact`) nor by forwarding
            // from the enclosing scope: unsatisfiable in this eta context.
            let op_qn = kb.qualified_name_of(sym).to_string();
            let parent_qn = kb.qualified_name_of(parent).to_string();
            Err(TypeError::Other {
                site: TypeError::here(),
                span: Some(occ.span.span),
                context: TypeErrorContext::OperationAsFunctionValue { op_name: sym },
                expected: format!(
                    "`{}` used as a function value to have a satisfiable `requires` — \
                     have the enclosing sort `requires` it, or use `{}` at a concrete type",
                    op_qn, op_qn,
                ),
                actual: format!(
                    "unsatisfiable `{}` requirement for bare operation `{}` (WI-420)",
                    parent_qn, op_qn,
                ),
            })
        }
    }
}

/// WI-1091 — an eta site's σ, its selections, and the OPERATION's own `requires` slots
/// built from both, for [`attach_eta_dispatch_dict`].
///
/// THE σ AND THE SELECTIONS WERE ALREADY COMPUTED HERE, inline in the cross-sort arm;
/// this lifts them ahead of every branch because the op half needs them on paths that
/// arm never reaches. That is not a refactor for tidiness — `List.member` is the shape:
/// its `requires Eq[T]` is on the OPERATION while `List` declares none, so it returns at
/// the `op_reads_requirement_slots` guard, three branches before any σ existed.
///
/// The σ is the same pin the sort half takes (the expected arrow against the op's eta
/// arrow, which is what turns `member`'s `List.T` into `Int64`), and `selected` is the
/// same §4.7 channel — so a `[Spec = Witness]` written at the eta reaches an op-scoped
/// slot exactly as it reaches a sort-level one. Building the op half from a DIFFERENT σ
/// would be the two-producers-one-rule defect the typer guards everywhere else.
///
/// WHAT IT COSTS, stated rather than claimed away: the three branches that return early
/// now pay the ∀-read and the arrow unify, which only the cross-sort arm used to. That is
/// the price of ONE producer of σ — computing it in two places is the desync class this
/// file spends most of its comments on — and the build it feeds is already free for the
/// universal case (`build_op_scoped_dicts` returns on a memoized `is_empty()` for an
/// operation that writes no `requires` of its own).
#[allow(clippy::type_complexity)]
fn eta_op_scoped_dicts(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    sym: Symbol,
    fn_ty: &Value,
    expected: &Value,
    span: Option<Span>,
    // WI-20260921-28TAT — the eta occurrence the op half is STAMPED onto. See
    // `NodeOccurrence`'s `op_dicts` field for why it is a stamp and not a `CallClass`
    // field.
    occ: &Rc<NodeOccurrence>,
) -> Result<(Substitution, Vec<InstanceSelection>), TypeError> {
    // Pin the op's element type(s) by unifying its eta arrow against the
    // expected arrow (best-effort: a non-unifiable expected leaves a dep
    // abstract, which `build_concrete_dispatch_dict` then forwards or rejects).
    let mut subst = Substitution::new();
    // Pin the op's element type by unifying the expected and eta-arrow PARAM
    // types (carrier-agnostic via `arrow_parts`: `expected` is a `Function[...]`
    // sort-ref, the eta arrow an `arrow` form — unifying the whole types across
    // those two carriers does not decompose). Concrete-first so a bare self-sort
    // ref (e.g. member's `l: List`) on the op side stays open while the concrete
    // expected param pins the element (`List.T := Int`) — mirroring the direct
    // call's arg-first unify order.
    let exp_param = arrow_parts(kb, expected).and_then(|(p, _, _)| p);
    // WI-1083: read THROUGH a ∀ to its body, un-freshened — see [`poly_type_body`] for
    // why this one reader must see the operation's own variables rather than an
    // instantiation. Without it `arrow_parts` answers `None` for every
    // type-parameterized operation (a ∀ is not an arrow), the pin silently does not
    // happen, and the dictionary build is handed an empty σ.
    let fn_body = poly_type_body(kb, fn_ty);
    let fn_param = match &fn_body {
        Some(body) => arrow_parts(kb, body).and_then(|(p, _, _)| p),
        None => arrow_parts(kb, fn_ty).and_then(|(p, _, _)| p),
    };
    if let (Some(ep), Some(fp)) = (exp_param, fn_param) {
        unify_types(kb, &mut subst, &ep, &fp);
    }
    // WI-841: an ETA'd op reference (`f` passed as a value) carries no call-site
    // BRACKET — there is no call here to write one on.
    //
    // WI-844: but that is only half of §4.7's channel, and this site fills the other
    // half itself — the unify above pins the op's params from the EXPECTED ARROW, so
    // when that arrow names a witness (`(SortedSet[T = String, O = ByLength], String) ->
    // …`) σ already holds it. MEASURED before this: a bare-name eta of `SortedSet.insert`
    // against exactly that arrow refused with "constructing `Ord[T = String]` is
    // ambiguous among providers" — the expected type's `O = ByLength` notwithstanding.
    // The slot read is the same one the direct call uses; only the σ producer differs.
    //
    // No `check_selection_bindings` here, unlike the direct call: a pin that fails to
    // land is already loud from this very build (`RequirementRefusal { pinned }` names
    // the selected witness and the dep), and adding the call-site check would widen
    // what an eta refuses beyond what this ticket measured.
    //
    // GATED BEFORE the record read, not inside: `lookup_operation_info_full` clones
    // every per-field `Vec` of the signature (`op_info_from_signature` — the cost
    // `operation_is_declared` exists to avoid), and `names_any_requirement_slot` is two
    // `Symbol`-keyed index gets. An op that names no slot must not pay the clone.
    let selected = if names_any_requirement_slot(kb, sym) {
        match lookup_operation_info_full(kb, sym) {
            Some(op) => selections_from_slot_bindings(kb, &subst, &op, sym, Vec::new(), span)?,
            None => Vec::new(),
        }
    } else {
        Vec::new()
    };
    // THE COMPOSED CHAIN, and the distinction is the same one the written call site draws
    // (found by /code-review): `build_concrete_dispatch_dict` takes
    // `enclosing_dict_chain` — the SORT half alone, because an INSTANCE dictionary must
    // not forward an op slot — while `build_op_scoped_dicts` takes
    // `enclosing_frame_chain`, since "a callee op slot may forward from the caller's own
    // op slots, which is how an op-scoped requirement relays hop to hop". Reading the
    // sort-only chain here made the eta the one spelling that cannot relay: an operation
    // that itself `requires Eq[T]` can hand its `__req_eq` to a written
    // `List.member(x, l)` and could not hand it to an eta'd `member`, so two spellings of
    // one program disagreed — the defect class this ticket is about.
    //
    // WI-1091: a TIE in the op half is refused here exactly as it is at a written call
    // site — an eta carries no bracket to decide it either, and `attach_eta_dispatch_dict`
    // already turns the sort half's refusal into `UnsatisfiableRequirement { eta: true }`.
    stamp_op_scoped_dicts(
        kb,
        occ,
        &subst,
        sym,
        env.enclosing_frame_chain(),
        env.param_rigids(),
        &selected,
        // WI-1102 parks nothing on the ETA path. An `OpRef` is not an application: the
        // dictionary rides on the VALUE and the slot is read wherever that value is
        // finally applied, which may be a frame this site cannot see. Withholding keeps
        // today's behaviour (eval's own `not bound` raise) rather than refusing a
        // program on a read that may never happen — the bound is stated, not assumed.
        None,
        // WI-20260909-S8CBV: an ETA has NO ARGUMENTS, so there is no receiver whose type
        // could ground a projection — `?f = List.member` names the operation, it does not
        // call it. An empty map makes the δ a no-op here, and the refusal above cannot fire
        // either: the eta's own caller chain is what a forwarded slot reads, exactly as it
        // is for every other dep this path cannot pin.
        &HashMap::new(),
        // WI-20260921-3G1YT — no route 4 on the ETA path, for the same reason it parks
        // nothing here: the slot is read wherever the `OpRef` VALUE is finally applied,
        // which is a frame this site cannot see, so the scope it CAN see is not the one
        // whose contracts would discharge the dep.
        &[],
        span,
        // The OPERATION owns an op-scoped clause, so it is what the refusal must name
        // as the declaration whose requirement could not be supplied — its parent sort
        // did not write it. `eta: true` is this site's alone.
        true,
    )?;
    Ok((subst, selected))
}

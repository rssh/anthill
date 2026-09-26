//! Resolver→eval bridge requirements (`resolve_bridge_requirements`) and the
//! `apply_within` rewrite records.

use super::*;

/// WI-20260925-4ZZKZ — one slot of a frame a VALUE-ONLY route enters: a resolved
/// dictionary, or an ABSENCE the route recorded because the argument values could not
/// decide it (`UnderDetermined`, `NamedSlotNotCarried`, `ParamSlotNotCarried` — each
/// documented at its producer below, with the decision to keep it).
///
/// ITS OWN TYPE, NOT A VARIANT OF [`ResolvedRequiresNode`]. The resolver used to answer a
/// spec-half sub-goal it could not fill with an `Unavailable` node inside the tree, and
/// that is what let an absence cross from the LOAD into run time. It fails the resolution
/// instead now, and the tree type has no node for an absence at all — so "a load-time
/// dictionary with a hole" is unrepresentable rather than merely not produced. What
/// remains is a slot-level fact about a frame this route enters, and only these routes
/// hold one.
pub(crate) enum BridgeSlot {
    Resolved(ResolvedRequiresNode),
    Absent {
        spec_sort: Symbol,
        why: UnavailableWhy,
    },
}

/// WI-625 Layer B (WI-300 Tier B) — the requirement dictionaries an op needs,
/// resolved at the CONCRETE types of its arguments. Two consumers, both of which
/// hold a concrete op and its runtime argument VALUES but no caller dictionary:
///
///  * the resolver→eval bridge ([`crate::kb::KnowledgeBase::bridge_op_to_eval`], the
///    original driver): it bridges a concrete op as an `eq`/`cmp` operand; if the
///    op's parent sort declares `requires Spec[T]` and its body dispatches a
///    (non-builtin) `Spec` op, that dispatch reads the frame's `__req_<spec>`
///    dictionary — which the bridge's empty floor (WI-625 gap 1) does not supply,
///    so the op residualizes;
///  * WI-822 LEG 2, VALUE-DIRECTED DISPATCH: an abstract spec-op call the typer
///    could not pin resolves its impl from the receiver VALUE at runtime
///    (`resolve_spec_op_target_by_value`) and used to enter that impl's frame with
///    the spec call's own (empty) channel — so a CONDITIONAL impl's own `requires`
///    died on the first dictionary read.
///
/// The two differ only in what an unresolvable requirement MEANS — the bridge
/// residualizes (it must not run at all on a wrong answer), while a dispatch enters
/// the frame unsupplied and lets the body's own read raise if it needs one — so they
/// share this one resolution and each maps the outcome itself.
pub(crate) enum BridgeRequirements {
    /// The op's parent sort has no `requires` chain — run with empty dicts (the
    /// gap-1 behavior; a requirement-free body decides).
    NoneNeeded,
    /// Resolved: the parent sort + one slot per entry of its `requires` chain, in
    /// `synth_req_names` order, for the eval bridge to port into `Dictionary`s.
    Resolved(Symbol, Vec<(Symbol, BridgeSlot)>),
    /// A required dictionary is unresolvable at these arg types (NO provider, a
    /// cyclic one, an under-determined carrier, or a signature/spec-binding the
    /// pin cannot read) — the caller must residualize or raise rather than run
    /// with a wrong or missing dict. NOT the ambiguous case; that is
    /// [`Self::Ambiguous`], see there.
    ///
    /// WI-822: `detail` NAMES the requirement and the types it failed at. Both
    /// consumers report it; previously the variant was opaque and each site could
    /// only say "a required dictionary" — which is precisely the unattributable
    /// message WI-822's own investigation had to work around. Built only on this
    /// (immediately-returning) failure edge, never on the resolving path.
    Unresolvable { detail: String },
    /// WI-855 — two or more providers TIE for one `requires` slot at these argument
    /// types ([`ResolutionResult::Ambiguous`]). A VARIANT OF ITS OWN, not a `detail`
    /// string inside `Unresolvable`, because the two carry different verdicts and
    /// each consumer must DECIDE between them rather than print one prose blob: the
    /// dominant unresolvable cause says "these types do not pin a dictionary HERE"
    /// (WI-822 measured that a receiver carrying no element type is ordinary, and
    /// that a body which never reads the slot runs correctly with none), while a tie
    /// says there IS a dictionary to build and nothing picks it. There is no
    /// legitimate "proceed unsupplied" reading of that, so the value-directed
    /// consumer raises on it and enters unsupplied on the rest.
    ///
    /// WI-843 SHARPENED WHAT A TIE MEANS without changing what to do about it. Two
    /// providers of one `(spec, carrier)` are no longer per se incoherent — 058
    /// tier 3 lets NAMEABLE ones coexist and refuses only a use site that selects
    /// none. But this consumer is VALUE-DIRECTED dispatch, which has no bracket
    /// channel (§4.2 puts rule bodies out of scope for selection), so a tie reaching
    /// here still has no answer at this call. What the message may no longer claim
    /// is that the declarations are the defect.
    ///
    /// THE LINE IS NOT EXACTLY "program defect vs pinning failure", and saying so
    /// keeps the next reader from inferring one: `Cyclic` (a `requires` graph that
    /// re-enters its own goal) is a property of the instances too, not of these
    /// argument types, and it stays in `Unresolvable` — not because it belongs
    /// there on principle, but because nothing in the corpus drives it and WI-855
    /// measured only the tie. Splitting it is the same edit, one variant over.
    ///
    /// Carries the DATA (`requirement` = the formatted goal, `candidates` = the tied
    /// provider names) rather than a rendered message: the value-directed consumer
    /// raises it and the bridge suspends on it, so the two need the same facts under
    /// different framing — the SENTENCE has one owner,
    /// [`crate::eval::EvalError::AmbiguousRequirement`]'s `Display`.
    Ambiguous {
        requirement: String,
        candidates: Vec<String>,
        /// WI-1091 — the frame requirement-param name of the slot that tied.
        ///
        /// A CONSUMER THAT SUPPLIES ONLY ONE HALF NEEDS IT, and without it there was no
        /// way to ask: `Interpreter::seed_entry_op_requirements` takes the OP half out of
        /// this resolution and leaves the sort half's stand-ins alone, so a tie in the
        /// SORT half is not its verdict to raise — it is a slot the host entry never
        /// asked about, and raising on it would fail an entry that used to run.
        /// `requirements_for_value_directed_impl` supplies BOTH halves and raises on
        /// either, which is unchanged.
        slot: Symbol,
    },
}

/// WI-456 — what [`resolve_bridge_requirements`] does with a tie at one of the sort's
/// NAMED slots, which the argument values can never pin (see the arm that reads it).
/// Chosen by the consumer, because only one of the three enters a frame whose body may
/// never read the slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum NamedSlotTies {
    /// Value-directed dispatch: record the slot absent and enter; a read is refused.
    RecordAbsent,
    /// The host entry: a SORT-half named tie is reported as under [`Self::Raise`] (the
    /// host serves that half with WI-868's stand-ins and discards what the resolution
    /// says of it), while a TYPE-CARRIED op slot's tie is recorded absent as under
    /// [`Self::RecordAbsent`] — WI-20260922-ATFGH: the host has a spelling for that slot
    /// (`Interpreter::call_with_witnesses`), the marker names it, and a body that never
    /// reads the slot must still run.
    HostEntry,
    /// The SLD bridge: report the tie as before (WI-855) — the bridge delays on it,
    /// which a marker's read would turn into a fault.
    Raise,
}


/// Resolve the requirement dictionaries for a bridged op call over GROUND args (see
/// [`BridgeRequirements`]). Types each argument, unifies it with the op's declared
/// parameter type to pin the parent sort's type-parameters, substitutes those into
/// the parent's `requires` chain, and SLD-resolves each concrete requirement to a
/// provider tree — the runtime dual of the typer's compile-time
/// [`build_concrete_dispatch_dict`]. Sound by construction: [`resolve`] is the same
/// instance-synthesis the typer uses, and anything it can't decide uniquely maps to
/// `Unresolvable` (→ the bridge delays).
///
/// Targets effect-free spec-op providers (`eq`/`cmp`/comparison-style `Combiner`s).
/// The `EffectsRuntime` hazard this paragraph used to describe is GONE (WI-857): the
/// synthetic anchor a provider's effect-row params contribute used to be SKIPPED by
/// the sub-goal walk but counted by `synth_req_names`, so such a provider built a
/// handle short of its own chain; both halves now keep the anchor's slot as a
/// structural leaf, and the producer asserts its count against [`dict_layout`].
pub(crate) fn resolve_bridge_requirements(
    kb: &mut KnowledgeBase,
    op: Symbol,
    args: &[Value],
    named_slot_ties: NamedSlotTies,
) -> BridgeRequirements {
    resolve_bridge_requirements_except(kb, op, args, named_slot_ties, &[])
}

/// [`resolve_bridge_requirements`] with the chain slots at `supplied` left out: the caller
/// already HOLDS a dictionary for each (WI-20260925-P7VP4 — a woven rule-body call carrying
/// its clause's conditions), so a tie or an unpinnable element there is no verdict about
/// the call — the host entry's rule (`seed_entry_requirements`) for the same reason.
pub(crate) fn resolve_bridge_requirements_except(
    kb: &mut KnowledgeBase,
    op: Symbol,
    args: &[Value],
    named_slot_ties: NamedSlotTies,
    supplied: &[usize],
) -> BridgeRequirements {
    let Some(parent) = impl_parent_of_op(kb, op) else {
        return BridgeRequirements::NoneNeeded;
    };
    // WI-822: the `_rc` read, not an owned clone. This is on the per-dispatch path
    // (every value-directed spec-op call reaches it), where the dominant case is a LEAF
    // impl that only needs `is_empty()` — and paying a full `Vec<RequiresEntry>` clone
    // to answer that is the whole cost. Holding the `Rc` alongside `&mut kb` is fine:
    // the arena owns the chain, not the borrow.
    //
    // WI-869: the DICTIONARY chain, because the loop below ZIPS it against
    // `synth_req_names(parent)` — the producer and the namer must read one list. With
    // the declared chain a carrier whose requirements are all provision conditions
    // (`Pair`) answered `NoneNeeded` here and its body was entered with an EMPTY frame
    // while reading the slots its provisions put there. MEASURED: `PartialOrd.gt` on a
    // pair — whose default body value-directs `Ord.compare` to `Pair.compare` —
    // died `__req_ord not bound in caller frame`, while a `compare` the TYPER
    // dispatched worked, because that route fills the frame from `dict_layout`.
    //
    // WI-822 LEG 1: and the OPERATION's own chain after it ([`op_dict_entries`]), for
    // the same reason one level in. These two consumers reach an operation with NO
    // call-site classification at all — the SLD bridge calls it from a rule body, and
    // value-directed dispatch resolves it from a runtime value — so the call-site
    // channel that fills an op-scoped slot never ran, and a body that reads one would
    // die unbound. MEASURED: with the slot in place and this read still sort-only,
    // `anthill.prelude.List.member` (`requires Eq[T]`, the stdlib's only op-scoped
    // clause) died `var_ref(__req_eq) unbound` in every rule body that used it. The
    // arguments are concrete here, so the op half pins exactly as the sort half does.
    let chain = op_dict_entries(kb, op);
    if chain.is_empty() {
        return BridgeRequirements::NoneNeeded;
    }
    // Pin the parent sort's type-parameters from the concrete argument types: unify
    // each ground arg's inferred type with the op's declared parameter type. A
    // parameter typed with the parent sort (`b: Box`) binds `Box`'s params from the
    // arg's type-args (`Box[T = Tag]` ⇒ `Box.T := Tag`); a parameter typed with a
    // sort-param directly (`x: T`) binds it from the arg's own type.
    let Some(rec) = crate::kb::op_info::lookup_operation_info(kb, op) else {
        return BridgeRequirements::Unresolvable {
            detail: format!(
                "`{}` has no recorded signature, so its parameter types cannot pin \
                 `{}`'s requires chain",
                kb.qualified_name_of(op),
                kb.qualified_name_of(parent),
            ),
        };
    };
    // WI-20260909-S8CBV — each parameter's ARGUMENT TYPE, kept alongside the unification,
    // so a requirement written at a PROJECTION off a parameter (`requires Desc[T = x.E]`)
    // can be δ-grounded below. This is `requirement-channel.md` §10 item 4's site: the
    // bridge does its own dispatch-time `unify_types` and never saw a projection path.
    //
    // THE SAME RULE AS THE TYPED CALL SITE, at its second reader.
    // [`build_op_scoped_dicts`] δ-grounds the identical entry from `check_apply_iter`'s
    // `param_to_arg_type`; this route — a rule body calling an operation, which reaches
    // no call-site classification at all — has to build the map itself, from the very
    // types the pinning loop already computes. Two readers of one rule; a second spelling
    // of the discharge would drift from it.
    let entries_have_projection = chain.iter().any(|e| value_contains_projection(kb, &e.spec));
    let (subst, param_arg_types) =
        pin_params_from_args(kb, &rec.params, args, entries_have_projection);
    // One resolved tree per requires slot, keyed by the frame requirement-param name.
    let names = chain.names(kb);
    // WI-822 LEG 1 — where the OP half starts. A failure in the SORT half aborts the
    // whole supply: those slots are what the callee's sort-keyed dictionary layout is
    // measured against, and half of them is not a dictionary. WI-20260830-NX4FD carved
    // ONE case out of that — a slot the argument types leave UNDER-DETERMINED keeps its
    // place as a recorded absence instead of aborting, which serves the same layout
    // rule by a different means (see the `all_pinned` gate below); every other sort-half
    // failure still aborts. A
    // failure in the OP half SKIPS THAT SLOT and keeps the rest, because widening this
    // chain must not be able to take away a sort-half supply that used to work. Without
    // the split, an operation whose own `requires` ranges over a parameter the arguments
    // do not pin (a bracket parameter, a return-only element) would make the entire
    // bridged call `Unresolvable` — where before the widening its sort chain resolved,
    // or was empty and answered `NoneNeeded`. The skipped slot is the same
    // "enter unsupplied, loud at the read" this channel takes everywhere else.
    let sort_len = chain.sort_len();
    let mut trees: Vec<(Symbol, BridgeSlot)> = Vec::with_capacity(chain.len());
    for (i, (entry, name)) in chain.iter().zip(names.iter()).enumerate() {
        if supplied.contains(&i) {
            continue;
        }
        let op_half = i >= sort_len;
        // WI-20260830-DQD5W — the `EffectsRuntime` KIND-ANCHOR keeps its slot as a
        // STRUCTURAL LEAF here too, exactly as [`build_dep_projection`] projects it at
        // compile time and as `check_provider_requires` exempts it. It is synthesized
        // from `effects E = ?` (WI-320) and satisfied by the effect-row machinery, never
        // by a carrier `fact` — so there is nothing to resolve, and `E` is a row
        // PARAMETER that no argument type can pin.
        //
        // WITHOUT THIS THE SORT HALF FAILED THE `all_pinned` GATE and the whole call was
        // `Unresolvable`. MEASURED: bridging `anthill.prelude.Iterable.isEmpty` at a
        // `List` argument suspended with "`anthill.prelude.EffectsRuntime[Effects =
        // anthill.prelude.Iterable.E]` is not fully pinned by the argument types". That
        // gate is right about every OTHER slot — an abstract binding matches ANY
        // provider — and wrong about this one for the reason WI-857 records: the anchor
        // has no provider to pick WRONGLY, so "not pinned" carries no hazard here.
        //
        // The `Leaf` with no bindings is the runtime twin of `build_empty_bundle`'s
        // `Dictionary(impl: EffectsRuntime)`: `dictionary_of_tree` ports it to a
        // sub-dictionary-free `Dictionary` rooted at the anchor, so the slot the
        // [`DictLayout`] halves count is present and positionally exact. WI-857's
        // "one owner for the three readers that must agree about the ANCHOR'S SLOT"
        // now has a fourth, and this is it.
        // WI-20260921-28TAT — and a REFINEMENT clause (`sort Narrow requires Boom`,
        // where `Boom` is a data sort with no type parameter, so nothing can provide it
        // and no member could be reached through a slot held for it). Same treatment,
        // same reason: a leaf that keeps the slot positionally exact.
        if is_effects_runtime(kb, entry.required_sort) {
            trees.push((
                *name,
                BridgeSlot::Resolved(ResolvedRequiresNode::Leaf {
                    impl_sort: entry.required_sort,
                    spec_sort: entry.required_sort,
                    bindings: SmallVec::new(),
                }),
            ));
            continue;
        }
        // WI-20260909-S8CBV — A PROJECTION THAT DID NOT GROUND IS A DELAY, NOT A SKIP.
        //
        // δ turns `Desc[T = x.E]` into the argument's actual member when the receiver's
        // type is known at this call ([`ground_entry_spec`]). When it is NOT — the caller
        // handed `pick` its own abstract parameter, so the receiver is still a variable —
        // the spec rides on with the projection intact and pins nothing.
        //
        // THE OP HALF'S ORDINARY ANSWER TO AN UNPINNED SLOT IS TO SKIP IT (see the
        // `op_half` arms below), and that is right for a slot the callee's BODY may never
        // read. It is WRONG here, and the difference is measured: `operation outer(b: Box)
        // requires Desc[T = b.E] = pick(b)` LOADS, skips the slot, and the body's very
        // first act is to read it — `DeferToRequirement: __req_desc not bound in caller
        // frame`, which is raised as `EvalError::Internal` and trips
        // `bridge_op_to_eval`'s `debug_assert`. A program that loads clean and aborts a
        // debug build is the worst of the three outcomes available here.
        //
        // SO IT IS `Unresolvable`, which the bridge turns into a named SUSPEND and then a
        // residual — the same answer every other requirement this call cannot pin gets,
        // and it NAMES the projection instead of dying about a frame binding. FORWARDING
        // such a dictionary from the caller's own slot is the genuine follow-on (it needs
        // the callee's neutral RE-KEYED to the caller's argument — WI-459's `arg_syms`,
        // which the ζ identity check compares); this refusal is what keeps that gap loud
        // and located rather than latent.
        //
        // NARROW BY CONSTRUCTION: the gate asks whether a projection SURVIVED δ, so it
        // can only fire on a chain entry that carried one — a shape no program could
        // even write before this ticket.
        // NARROW, and gated to the `ExprCarried` half for the reason
        // [`value_contains_expr_carried`] gives: this `return` abandons the WHOLE call,
        // including the SORT half, which the WI-822 LEG 1 note above forbids a widening
        // of this chain from doing. That is acceptable ONLY because the shape it fires on
        // could not be written before this ticket — an argument that is false for a
        // `RigidTypeProjection`, and `/code-review` drove it.
        let concrete_spec = match ground_entry_spec(kb, op, entry, &param_arg_types, &subst) {
            Ok(v) => v,
            Err(detail) => return BridgeRequirements::Unresolvable { detail },
        };
        let concrete = RequiresEntry {
            required_sort: entry.required_sort,
            spec: concrete_spec,
            supply: entry.supply,
        };
        let Some(goal) = goal_from_requires_entry(kb, &concrete) else {
            if op_half {
                continue;
            }
            return BridgeRequirements::Unresolvable {
                detail: format!(
                    "`{}`'s `requires {}` clause carries no readable spec bindings",
                    kb.qualified_name_of(parent),
                    kb.qualified_name_of(entry.required_sort),
                ),
            };
        };
        // SOUNDNESS: only resolve a FULLY-PINNED goal — every one of the spec's
        // type-parameters bound to a fully-GROUND type. An argument that fails to
        // determine a type-param (an empty-collection element, a return-only param)
        // leaves it abstract, and `match_candidate_against_goal` treats an abstract
        // binding as a WILDCARD that matches ANY provider — which would build a WRONG
        // dictionary and let the bridged op mis-decide. Residualize instead.
        // STILL TRUE after WI-824 and WI-20260925-4ZZKZ, which together refuse an
        // abstract element against a STRUCTURED provider head on every path, σ-less
        // included: a bare impl-parameter head (`provides Spec[T = X]`) still accepts it
        // WITHOUT recording (WI-507's sibling wildcard, `match_impl_param`'s σ-less arm),
        // so every generic witness would match. This gate is what keeps an abstract
        // element off them — do not relax one without the other.
        // WI-822 inherits exactly this guarantee for VALUE-DIRECTED DISPATCH, whose
        // WI-824 feedback asks that an op-scoped construction path meeting an
        // ABSTRACT element land on a refusal rather than build a dictionary: it does,
        // HERE, and for this reason. Pinned by
        // `unpinnable_impl_requirement_is_refused_before_it_can_run` (which also
        // measures the OUTER guard: to be unpinnable a requirement must range over a
        // type-param the parameters do not mention, which then fails to cover the
        // body's own dictionary read, so WI-325 refuses the program at LOAD).
        let all_pinned = goal_is_fully_pinned(kb, &goal);
        // WI-1091 — THE OP HALF RESOLVES AN OPEN ELEMENT ANYWAY, and accepts only a
        // UNIQUE answer. The soundness argument above is about a WRONG dictionary being
        // built where the wildcard admits SEVERAL providers; where it admits exactly
        // one, that one is the only dictionary the goal could ever name, so taking it
        // is exact rather than lenient — the same reasoning `check_selection_bindings`
        // makes for its sole-provider acceptance, and the same shape as the tie check
        // one arm down. Two or more still land on `Ambiguous` below and a goal nothing
        // answers on `NoProvider`, both unchanged.
        //
        // MEASURED as the shape that needs it: `G.twice[V, F](a: V) requires
        // VectorSpace[V, F]` entered from the host. The argument pins `V := Vec3` and
        // NOTHING pins `F` — it is a return-position element of the spec, not of the
        // operation's parameters — so the gate skipped the slot, and under WI-1091's
        // widened placement the body's `VectorSpace.vec_add(a, a)` reads it and dies
        // `__req_vectorspace not bound`. `Vec3` has one `VectorSpace` provision, so the
        // open `F` has exactly one answer. `vec3_ops_test::a_generic_consumer_of_vector_
        // space_loads_and_dispatches` and `renamed_op_type_params_are_covered_by_the_
        // operations_own_requires` are the two rows; both are CAPABILITY tests (they
        // assert the doubled vector), not diagnostics.
        //
        // WI-20260830-NX4FD — THE SORT HALF TAKES THE COMPLETION TOO, and where no
        // completion is unique it KEEPS ITS SLOT as a recorded absence instead of
        // aborting the whole call. WI-1091 left it alone saying "its slots are what the
        // callee's dictionary LAYOUT is measured against … widening it is a different
        // question from the one this ticket measured"; that question is settled below,
        // at the arm that places the node, and the LAYOUT argument is what decides HOW:
        // the slot is kept, not skipped.
        //
        // `unpinnable_impl_requirement_is_refused_before_it_can_run` still pins the
        // outer refusal and is UNMOVED — it asserts a LOAD-time verdict (the WI-325
        // ladder refuses a body whose dictionary read no `requires` COVERS), so it
        // never reached this gate.
        //
        // WHAT KEEPS THE WIDENING FROM OPENING A HOLE IS NOT THAT LADDER, and saying so
        // here because the tidy version of this sentence is wrong and was written first:
        // a body whose read IS covered by its sort's `requires` loads fine and can still
        // meet a CALL that does not pin the slot (`G requires VectorSpace[V, F]` with
        // `twice(a: V)`, called at a carrier providing no `VectorSpace` — MEASURED, it
        // loads). The two arms are sound for TWO DIFFERENT reasons, and neither covers
        // the other (raised by /code-review, which read the marker's argument as though
        // it were asserted over both):
        //
        //  * THE MARKER ARM resolves NOTHING, so no dictionary is built at all and
        //    `marker_refusal` refuses any read — the bridge then residualizes exactly
        //    as the whole-call `Unresolvable` used to. Rows: `an_under_determined_slot_
        //    with_no_completion_answers_nothing` (the read happens, the goal answers
        //    nothing) and `spec_op_arity_plus_one_goal_binds_its_result` (the read never
        //    happens — `size(c) = List.length(collect(c))` is same-sort `collect` plus a
        //    concrete `List.length` — so the call that used to be refused now answers).
        // COST, MEASURED, because the cheap bail this replaced was on the path
        // `resolve_bridge_requirements`' own doc calls per-dispatch: across the whole
        // `wi_tests` binary (3924 tests) this function is entered past the empty-chain
        // bail 272 times, and 79 of those reach the completion attempt below. The
        // removed early return saved one `unique_provider_completion` call, 79 times.
        //
        //  * THE COMPLETION ARM DOES resolve, and its soundness is
        //    [`unique_provider_completion`]'s own: the goal it resolves is CONSTRUCTED
        //    and fully pinned, a provider disagreeing on an element the arguments DID
        //    pin is excluded, one that leaves an open element abstract forces `None`
        //    outright, and a SECOND surviving completion forces `None` too. So the
        //    dictionary taken is one the goal genuinely names, not one the wildcard
        //    admitted. DRIVEN on a fixture that can tell exact from guessed:
        //    `a_completion_selects_the_provider_the_pinned_element_names` (two ground
        //    providers, the pinned element selects, and the two rows answer 11 and 22 —
        //    a guess answers one number twice) and `rival_completions_leave_the_slot_
        //    unfilled_rather_than_guess` (nothing pinned, two providers, no answer).
        // Empty scope: neither consumer has a caller frame to read (the bridge has no
        // frame at all; value-directed dispatch reached an impl the caller could not
        // pin, so no caller slot names it), so a slot can only resolve by
        // CONSTRUCTION (`Leaf`/`Conditional`), never `FromScope`.
        // WI-841: and no SELECTION — this runs at eval, from a value-directed
        // dispatch or the SLD bridge, where there is no call-site bracket to read.
        let scope = ResolutionScope {
            available_requires: &[],
            sigma: None,
            selected: &[],
            sub_goal_requires: &[],
        };
        // WI-861 — the chain's two halves have two OWNERS ([`dict_layout`]): the sort's
        // slots then the operation's, so the named-slot question is asked of whichever
        // half `i` falls in. Asking `parent` for an op-half slot would read the wrong
        // declaration's slot list.
        //
        // WI-20260922-ATFGH — …EXCEPT A SLOT WHOSE WITNESS IS IN A TYPE, which is a named
        // slot of the PARAMETER's carrier (`MySet.O`) and not of either owner. Asking the
        // operation answered `Consult` — an operation declares no named slots — so 058
        // §3.2's default rung broke the tie between `ByLength`, `Alphabetical` and
        // `String`'s own ordering in favour of the last, and the host entry built
        // `String`'s dictionary for a set constructed at `ByLength`: one answer at both
        // rival orderings, in silence. That was the whole of the defect. UNRANKED, the
        // search answers only when ONE provider exists, which is exact — the value's
        // construction had to choose a provider of this goal, and there is one — and a
        // tie is the genuine "not carried" case, handled at the arms below. Not merely
        // `Withhold`: specificity is a ranking too ([`DefaultRung::Unranked`]).
        let type_carried = entry.supply.witness_in_argument_type();
        let ranked = rung_for_dep(kb, if op_half { op } else { parent }, goal.spec_sort);
        let rung = if type_carried.is_some() {
            DefaultRung::Unranked
        } else {
            ranked
        };
        // WI-1091 — the OP HALF's open element, COMPLETED FROM THE PROVIDERS when they
        // leave exactly one possibility. See [`unique_provider_completion`].
        let goal = if all_pinned {
            goal
        } else {
            // COUNTED AT THE RANKED RUNG, even for a type-carried slot: a completion is a
            // candidate ELEMENT, and one whose goal has several providers is still a
            // candidate. Counting it under `Unranked` would read its tie as "does not
            // answer" and let a single-provider element win by elimination — a
            // dictionary for an element the arguments never named (found by
            // /code-review). The completed goal is then resolved unranked below.
            match unique_provider_completion(kb, &goal, &scope, ranked) {
                Some(completed) => completed,
                // WI-20260830-NX4FD — THE SORT HALF KEEPS ITS SLOT, AS A RECORDED
                // ABSENCE, where it used to abort the whole call. The soundness
                // argument above is untouched: nothing resolves an under-pinned goal,
                // so no WRONG dictionary is built. What changes is only what an
                // unbuildable slot COSTS — a marker that is loud at the read (WI-857)
                // instead of a residualized call that could not run at all.
                //
                // WI-20260925-4ZZKZ — DECISION: KEPT, a run-time absence loud at the
                // read, and NOT moved to the entry. This used to be argued from the
                // compile-time producer, which placed the same marker in the same slot
                // (WI-857) — that producer is gone: a load-time resolution that cannot fill
                // a slot now fails. The argument that remains is this route's own. It holds
                // argument VALUES, and a value carries no type arguments, so an element the
                // operation's parameters do not mention is not recoverable HERE even where
                // the program determines it — and the typed call sites of the same
                // operations build the same slot with σ, where it is checked (3G1YT's
                // obligation is owed and discharged at LOAD). MEASURED (full workspace,
                // log-only probe): 73 slots in 25 tests, 71 on value-directed dispatch into
                // the stdlib's lazy combinators — `MappedStream`/`FilteredStream.
                // splitFirst`, `Mapped`/`FilteredStreamFinite.collect`, whose sort-level
                // `requires Iterable[C = Source, …]` names a parameter no value carries —
                // and 2 on the SLD bridge (`size` below). None is read: their bodies'
                // inner calls dispatch by value. Refusing at the entry would refuse every
                // `map`/`filter` pipeline evaluated by value, and a slot that IS read is
                // refused naming it.
                //
                // MEASURED, and it is the ticket's acceptance row: `rule spec_len(?n)
                // :- Box(items: ?ls), size(?ls, ?n)` answered `[]` beside a
                // `length(?ls, ?n)` that answered `Int(2)`, because
                // `FiniteCollection.size(c: C)` pins `C` from its argument and mentions
                // neither `Element` nor `E`. `size`'s body is `List.length(collect(c))`
                // — `collect` is a SAME-SORT call and `List.length` is concrete, so the
                // `Iterable` slot is never read and the marker costs nothing.
                //
                // ONE CONSEQUENCE IS NOT DRIVEN, and it is written down rather than
                // credited (raised by /code-review). This resolution's OTHER consumer,
                // `requirements_for_value_directed_impl`, treated a sort-half
                // `Unresolvable` as "enter unsupplied" — it reaches this function only
                // with an EMPTY incoming channel, so nothing that was working is taken
                // away — and now takes the `Resolved` branch instead, which leads the
                // frame with a `__req_self` STAND-IN it previously had no channel for.
                // That is not a marker and does not refuse: a stand-in is
                // `stand_in_requirement`'s "the receiver VALUE may still say which
                // impl", the invitation to the value-directed rescue that makes
                // `interp.call` work on a `requires`-bearing sort at all. It is the
                // right reading for this route — the bridge is an entry with no caller
                // dictionary, exactly like a host entry — but NO ROW HERE DRIVES IT:
                // every fixture in `wi_nx4fd_functional_relation_row_param_test` reaches
                // this through the SLD bridge, and the corpus's 79 sort-half attempts
                // (counted, of 272 calls that reach a non-empty chain in the whole
                // `wi_tests` binary) moved nothing. Driving it needs a value-directed
                // dispatch whose sort half is entirely under-determined; the host-entry
                // route is not it, because `seed_entry_op_requirements` takes the OP
                // half out of this resolution and leaves the sort half's stand-ins
                // alone.
                //
                // NOT THE `other =>` ARM ONE MATCH DOWN, deliberately: that one says
                // "these types do not pin a dictionary HERE" about a goal that was
                // FULLY pinned and still found no provider, which is a claim about the
                // program. This arm is about a goal no provider was ever searched for.
                // Widening that one is a separate question with a separate population.
                None if !op_half => {
                    trees.push((
                        *name,
                        BridgeSlot::Absent {
                            spec_sort: goal.spec_sort,
                            why: UnavailableWhy::UnderDetermined,
                        },
                    ));
                    continue;
                }
                // WI-20260922-ATFGH — a type-carried slot the arguments leave
                // under-determined keeps the slot as its own absence, on every route —
                // the sort half's NX4FD answer one arm up, with the sentence that names
                // `s.O`. A skip would leave the read to die `not bound`, naming nothing.
                // The SLD bridge included, exactly as for NX4FD's sort-half marker: a
                // body that reads it faults, named, where the skip it replaces faulted
                // unnamed — and a body that never reads it answers, as it did.
                None => {
                    if let Some((param, binder)) = type_carried {
                        trees.push((*name, param_slot_marker(goal.spec_sort, param, binder)));
                    }
                    continue;
                }
            }
        };
        let result = resolve_with_rung(kb, &goal, &scope, rung);
        // WI-20260922-ATFGH — A TIE AT A TYPE-CARRIED SLOT IS WI-456'S CASE, NOT WI-855'S:
        // several providers answer the goal, and the value carries no type argument to
        // say which one its construction chose, so the tie says only that the arguments
        // did not pin it. Recorded as the absence that names `s.O`, for every route that
        // ENTERS a frame whose body may never read the slot — value-directed dispatch,
        // the eval gate, and the host entry, whose repair is
        // `Interpreter::call_with_witnesses`.
        //
        // THE SLD BRIDGE KEEPS THE TIE (`NamedSlotTies::Raise`) and reaches the ordinary
        // tie arm below: it delays on it, where a marker's read would be a `Fault`
        // (`EvalError::bridge_disposition`) — WI-456 keeps the sort half's named ties for
        // the bridge for the same reason, and before this ticket the bridge got the
        // default's WRONG dictionary here. A FORWARDED tie is a coherence verdict about
        // the chosen provider's own condition, and stays WI-855's.
        if let (ResolutionResult::Ambiguous { forwarded: false, .. }, Some((param, binder))) =
            (&result, type_carried)
        {
            if named_slot_ties != NamedSlotTies::Raise {
                trees.push((*name, param_slot_marker(goal.spec_sort, param, binder)));
                continue;
            }
        }
        match result {
            ResolutionResult::Resolved(tree) => trees.push((*name, BridgeSlot::Resolved(tree))),
            // WI-456 — EXCEPT, ON VALUE-DIRECTED DISPATCH, A TIE AT ONE OF THE SORT'S NAMED
            // SLOTS, which is not a coherence verdict at all: it is the NX4FD
            // under-determined slot above, one step later. A named slot is a type parameter
            // (058 §4.7) and a runtime value carries none — a `SortedSet` entity names its
            // sort and says nothing of its `O` — so the goal this resolves (`WeakOrd[T =
            // String]`) is not the question the slot asks ("which `O` did this value's
            // construction choose"), and a tie among its answers says only that the
            // arguments did not pin it. Recorded as that absence: nothing is built, so no
            // WRONG ordering can be, and a body that reads the slot is refused at the read
            // (WI-857).
            //
            // MEASURED as the shape that needs it: `FiniteCollection.size`'s default body
            // is `List.length(collect(c))`, and `collect` on a `SortedSet` arrives here by
            // value with two `WeakOrd[String]` in scope — `AmbiguousRequirement` for a
            // body (`toList(s)`) that never reads `O`. The typer-dispatched
            // `FiniteCollection.collect(s)` answered on the same program.
            //
            // NARROW THREE WAYS. (1) `named_slot_ties` — only value-directed dispatch enters
            // a frame to run a body that may never read the slot; the SLD bridge and the
            // host entry keep the tie, which the bridge turns into a delay rather than a
            // fault. (2) The slot at THIS chain index is a named one — by index, not by
            // spec, so an anonymous `requires WeakOrd[K]` beside `O` keeps WI-855's verdict.
            // (3) The tie is the slot's OWN, not `forwarded` from a condition of the
            // provider that answered it, which is a coherence verdict about that condition.
            // The SORT half only, where the layout keeps the slot: an op-scoped tie stays
            // WI-1091's loud verdict.
            //
            // WI-20260925-4ZZKZ — DECISION: KEPT, loud at the read. MEASURED (full
            // workspace, log-only probe): ONE slot left in the suite, R10KC's existential
            // return (`r10kc.exists.MySet.contains`), whose rigid skolem names no provider
            // anywhere — no route could have built a dictionary for it, the call site's
            // included. The value was CONSTRUCTED with one; moving the refusal to the entry
            // would refuse `toList(s)`-style bodies that never ask which.
            ResolutionResult::Ambiguous {
                forwarded: false, ..
            } if named_slot_ties == NamedSlotTies::RecordAbsent
                && !op_half
                && named_slot_at(kb, parent, i).is_some() =>
            {
                trees.push((
                    *name,
                    BridgeSlot::Absent {
                        spec_sort: goal.spec_sort,
                        why: UnavailableWhy::NamedSlotNotCarried,
                    },
                ));
            }
            // WI-855: a TIE is a coherence verdict, kept apart from the causes that
            // merely say "not pinnable at these types" — see `BridgeRequirements`.
            ResolutionResult::Ambiguous { goal_text, tie, .. } => {
                // WI-1091 — THE OP HALF RAISES THE TIE TOO, and the paragraph that used
                // to stand here is why it now must. WI-822 LEG 1 wrote: "the op half
                // skips this too … an op-scoped slot is not [a slot the callee's layout
                // demands], and a body that never reads it must keep running exactly as
                // it did before this chain was widened. A body that DOES read it raises
                // at the read; that message names the frame but not the tie, which is
                // the cost of not being able to regress a working call."
                //
                // THAT COST IS NOW PAID BY EVERY SUCH BODY, because WI-1091 widened the
                // placement: a body whose spec-op call is licensed by its own `requires`
                // now READS this slot rather than being served by value-direction. So
                // the skip stopped protecting a working call and started converting a
                // named coherence verdict — `AmbiguousRequirement`, which names the
                // requirement and both providers — into `Internal(DeferToRequirement:
                // __req_desc not bound)`, which names neither. MEASURED as five rows:
                // wi842 (both tie pins), wi843, wi855's value-directed tie, and WI-861's
                // own `a_witness_only_value_directed_tie_stays_loud` control.
                //
                // And WI-855's rule was never really about the layout — it is that a TIE
                // IS A COHERENCE VERDICT WITH NO EARLIER OWNER. 058 tier 3 lets nameable
                // providers coexist on purpose, so a tie reaching a route with no bracket
                // channel must go loud where it is found. That holds for an op-scoped
                // slot exactly as for a sort-level one; nothing about which half the slot
                // falls in changes who else could have reported it, which is NOBODY.
                //
                // The `Unresolvable` and no-provider arms are UNTOUCHED and still skip:
                // those say "not pinnable at these types", which is a different claim
                // with a different population — the 29 stdlib bodies WI-822 LEG 2
                // measured, which have a chain and never read it.
                return BridgeRequirements::Ambiguous {
                    requirement: goal_text,
                    candidates: tie
                        .candidates
                        .iter()
                        .map(|s| kb.qualified_name_of(*s).to_string())
                        .collect(),
                    slot: *name,
                };
            }
            // "no unique provider" was the umbrella wording BECAUSE it also covered
            // the tie; with that split off, what is left is a goal that resolves to
            // no provider at all or to a cycle.
            other => {
                if op_half {
                    continue;
                }
                return BridgeRequirements::Unresolvable {
                    detail: format!(
                        "`{}` could not be resolved: {}",
                        format_goal(kb, &goal),
                        describe_resolution_failure(kb, &other),
                    ),
                };
            }
        }
    }
    if trees.is_empty() && sort_len == 0 {
        // Every slot was an op-scoped one and none resolved: the answer this call had
        // BEFORE the chain was widened, down to not placing a `__req_self` the frame
        // never used to carry.
        //
        // SO `__req_self` RIDES WITH THE SLOTS, and one operation value-directed on two
        // argument sets can get two frame shapes — asked about by the WI-1092 review,
        // and kept. `frame_requirements_from_trees` leads every channel it builds with
        // the self slot because that is the WI-857 layout; a channel with no entries is
        // not a shorter channel, it is no channel, which is what `NoneNeeded` says. The
        // difference the two shapes make is only ever an ADDED `__req_self`, and with
        // `sort_len == 0` that stand-in is arity 0 — `Dictionary(impl: parent)`, the
        // frame's own sort, which is exactly what a self-slot read wants and strictly
        // better than the absent slot's raise-at-the-read. Making it uniform would mean
        // placing a self slot on a call that resolved nothing, which is the pre-widening
        // regression the branch above exists to avoid.
        return BridgeRequirements::NoneNeeded;
    }
    BridgeRequirements::Resolved(parent, trees)
}

/// The substitution that pins an operation's type parameters from GROUND argument
/// values — each argument's inferred type unified with its declared parameter type —
/// and, when `keep_arg_types`, each parameter's argument type keyed by parameter.
///
/// A parameter typed with the parent sort (`b: Box`) binds `Box`'s params from the
/// arg's type-args (`Box[T = Tag]` ⇒ `Box.T := Tag`); a parameter typed with a
/// sort-param directly (`x: T`) binds it from the arg's own type. One owner for the two
/// value-only readers, [`resolve_bridge_requirements`] and [`resolve_param_witnesses`], so
/// a witness is resolved at exactly the bindings the rest of the frame was.
fn pin_params_from_args(
    kb: &mut KnowledgeBase,
    params: &[(Symbol, Value)],
    args: &[Value],
    keep_arg_types: bool,
) -> (Substitution, HashMap<Symbol, Value>) {
    let mut subst = Substitution::new();
    let empty = Substitution::new();
    let mut param_arg_types: HashMap<Symbol, Value> = HashMap::new();
    for (i, (pname, ptype)) in params.iter().enumerate() {
        let Some(arg) = args.get(i) else { continue };
        let arg_ty = value_type_term(kb, &empty, arg);
        if keep_arg_types {
            param_arg_types.insert(*pname, arg_ty.clone());
        }
        unify_types(kb, &mut subst, &arg_ty, ptype);
    }
    (subst, param_arg_types)
}

/// `entry`'s spec at a call's arguments: δ BEFORE σ, then `Err` if a projection
/// survived. The one grounding for the two value-only readers,
/// [`resolve_bridge_requirements`] and [`resolve_param_witnesses`].
///
/// WI-20260909-S8CBV — δ BEFORE σ, the same order and the same fallback as
/// [`build_op_scoped_dicts`]: a projection names a member of the RECEIVER's type,
/// which a substitution over type VARIABLES cannot reach, so σ alone leaves the
/// dep un-pinned and the slot silently absent. On a failed elimination the
/// UN-eliminated spec rides on: an `ExprCarried` survivor is refused here, and anything
/// else reaches the caller's ordinary unpinnable path, so no dictionary is built from a
/// guess.
///
/// THE δ ERROR IS KEPT, not swallowed. An elimination that FAILS (a member the
/// receiver's sort does not declare) and one that leaves a NEUTRAL (an abstract
/// receiver) both arrive as "still a projection", and reporting them with one sentence
/// tells the author the arguments are at fault when the requirement itself may be.
/// `/code-review` drove it.
fn ground_entry_spec(
    kb: &mut KnowledgeBase,
    op: Symbol,
    entry: &RequiresEntry,
    param_arg_types: &HashMap<Symbol, Value>,
    subst: &Substitution,
) -> Result<Value, String> {
    let mut delta_error: Option<String> = None;
    let projected_spec =
        if param_arg_types.is_empty() || !value_contains_projection(kb, &entry.spec) {
            entry.spec.clone()
        } else {
            let ctx = TypeErrorContext::OperationReturn {
                op_name: op,
                surface: None,
            };
            match eliminate_type_projections(kb, &entry.spec, param_arg_types, None, &ctx, None) {
                Ok(v) => v,
                Err(e) => {
                    delta_error = Some(delta_failure_text(&e));
                    entry.spec.clone()
                }
            }
        };
    let concrete_spec = substitute_spec_via_subst(kb, &projected_spec, subst);
    if value_contains_expr_carried(kb, &concrete_spec) {
        return Err(format!(
            "`{}`'s `requires {}` names a projection these arguments do not ground{}",
            kb.qualified_name_of(op),
            render_requires_entry(kb, entry),
            match &delta_error {
                Some(d) => format!(" — projecting it failed: {d}"),
                None => "; forwarding a projection-carried dictionary from the \
                         caller's own requirement is not yet supported"
                    .to_owned(),
            },
        ));
    }
    Ok(concrete_spec)
}

/// WI-20260922-ATFGH — the recorded absence for a type-carried slot `param.binder`
/// ([`UnavailableWhy::ParamSlotNotCarried`]), at its own level. One spelling for its
/// producers.
///
/// WI-20260925-4ZZKZ — DECISION: KEPT, loud at the read. MEASURED (full workspace,
/// log-only probe): 4 slots, all HOST ENTRIES (the EE0EP rows), where the host holds a
/// repair the refusal names — `Interpreter::call_with_witnesses` — and a body that never
/// reads the slot answers. The route has argument values only; the witness is in the
/// argument's TYPE, which the typed call site reads and a value does not carry.
fn param_slot_marker(spec_sort: Symbol, param: Symbol, binder: Symbol) -> BridgeSlot {
    BridgeSlot::Absent {
        spec_sort,
        why: UnavailableWhy::ParamSlotNotCarried { param, binder },
    }
}

/// Every one of `goal`'s spec type-parameters bound to a fully GROUND type — the gate
/// before a σ-less resolution, which treats an abstract binding as a wildcard matching
/// ANY provider (see the SOUNDNESS note in [`resolve_bridge_requirements`]).
fn goal_is_fully_pinned(kb: &KnowledgeBase, goal: &SortGoal) -> bool {
    kb.type_params_of_sort(goal.spec_sort).iter().all(|tp| {
        goal.bindings
            .iter()
            .any(|(k, v)| kb.local_name_of(*k) == tp && type_value_is_ground(kb, *v))
    })
}

/// WI-20260922-ATFGH — the dictionaries for `op`'s type-carried slots
/// ([`SupplySource::witness_in_argument_type`]), built from the witnesses a HOST names.
/// `Ok` pairs each frame slot's name with its tree; `Err` is the sentence.
///
/// THE HOST SPELLING OF WHAT THE TYPED ROUTE READS. At a typed call the witness is read
/// out of the argument's TYPE ([`param_slot_witness`]) and pinned as a selection; a host
/// has no types to hand over, but it can NAME the provider, and that is the only thing
/// the type was being read for. So each witness becomes the same bare
/// [`InstanceSelection`] a typed call builds for a bare witness, and the ordinary
/// resolution does the rest — the witness's own conditions and named slots resolve as
/// its sub-goals, none of them chosen by the host. NOT BY PASSING TYPES: the dictionary is
/// what runtime needs, and the type is only where a typed call site reads the witness
/// from.
///
/// THE SAME BINDINGS AS THE REST OF THE FRAME: one σ for the call
/// ([`pin_params_from_args`]) and the bridge's own δ-then-σ grounding
/// ([`ground_entry_spec`]), so a witness is checked at exactly the goal the op-half
/// resolution asked.
///
/// LOUD ON EVERY MISMATCH, since a host that names a witness has said what it means: a
/// slot `op` does not have, a slot named twice, an unknown witness, a goal the arguments
/// do not pin — where the resolution's wildcard would accept any provider as the
/// witness, e.g. a generic `size[T](s: MySet[T = T])` whose set VALUE names no `T` — and
/// a witness that does not answer the goal are each refused here, at the entry.
pub(crate) fn resolve_param_witnesses(
    kb: &mut KnowledgeBase,
    op: Symbol,
    args: &[Value],
    witnesses: &[crate::eval::SlotWitness<'_>],
) -> Result<Vec<(Symbol, ResolvedRequiresNode)>, String> {
    let chain = op_dict_entries(kb, op);
    let names = chain.names(kb);
    let sort_len = chain.sort_len();
    // The slots a witness can name, as `(frame name, entry, param, binder)`.
    let carried: Vec<(Symbol, RequiresEntry, Symbol, Symbol)> = chain
        .iter()
        .zip(names.iter())
        .skip(sort_len)
        .filter_map(|(entry, name)| {
            let (p, b) = entry.supply.witness_in_argument_type()?;
            Some((*name, entry.clone(), p, b))
        })
        .collect();
    let op_qn = kb.qualified_name_of(op).to_string();
    // Every check that needs no resolution first, so a malformed request costs none.
    let mut matched: Vec<(Symbol, RequiresEntry, Symbol, String)> =
        Vec::with_capacity(witnesses.len());
    for w in witnesses {
        let spelled = format!("{}.{}", w.param, w.slot);
        let Some((name, entry, _, _)) = carried
            .iter()
            .find(|(_, _, p, b)| kb.local_name_of(*p) == w.param && kb.local_name_of(*b) == w.slot)
        else {
            let have: Vec<String> = carried
                .iter()
                .map(|(_, _, p, b)| format!("`{}.{}`", kb.local_name_of(*p), kb.local_name_of(*b)))
                .collect();
            return Err(format!(
                "`{op_qn}` has no slot `{spelled}` whose witness an argument type carries; {}",
                if have.is_empty() {
                    "it has none".to_string()
                } else {
                    format!("its slots of that kind are {}", have.join(", "))
                },
            ));
        };
        if matched.iter().any(|(.., sp)| *sp == spelled) {
            return Err(format!("`{spelled}` is named twice"));
        }
        let witness = kb
            .try_resolve_symbol(w.witness)
            .ok_or_else(|| format!("unknown witness `{}` for `{spelled}`", w.witness))?;
        matched.push((*name, entry.clone(), witness, spelled));
    }
    let Some(rec) = crate::kb::op_info::lookup_operation_info(kb, op) else {
        return Err(format!(
            "`{op_qn}` has no recorded signature, so its arguments cannot pin its slots"
        ));
    };
    let keep_arg_types = matched
        .iter()
        .any(|(_, e, ..)| value_contains_projection(kb, &e.spec));
    let (subst, param_arg_types) = pin_params_from_args(kb, &rec.params, args, keep_arg_types);
    let mut out = Vec::with_capacity(matched.len());
    for (name, entry, witness, spelled) in matched {
        let concrete = RequiresEntry {
            required_sort: entry.required_sort,
            spec: ground_entry_spec(kb, op, &entry, &param_arg_types, &subst)?,
            supply: entry.supply,
        };
        let Some(goal) = goal_from_requires_entry(kb, &concrete) else {
            return Err(format!(
                "`{op_qn}`'s slot `{spelled}` carries no readable spec bindings"
            ));
        };
        if !goal_is_fully_pinned(kb, &goal) {
            return Err(format!(
                "the arguments do not pin `{spelled}`'s goal `{}` — the values name no \
                 element type for it — so no witness can be checked against it",
                format_goal(kb, &goal),
            ));
        }
        let selected = [InstanceSelection {
            spec_sort: entry.required_sort,
            witness,
            slots: Vec::new(),
        }];
        let scope = ResolutionScope {
            available_requires: &[],
            sigma: None,
            selected: &selected,
            sub_goal_requires: &[],
        };
        // Unranked for the reason `resolve_bridge_requirements` gives. The rung decides
        // only the top goal, which the selection has already restricted to the witness.
        match resolve_with_rung(kb, &goal, &scope, DefaultRung::Unranked) {
            ResolutionResult::Resolved(tree) => out.push((name, tree)),
            other => {
                return Err(format!(
                    "the witness `{}` does not answer `{spelled}`'s goal `{}` at these \
                     arguments: {}",
                    kb.qualified_name_of(witness),
                    format_goal(kb, &goal),
                    describe_resolution_failure(kb, &other),
                ))
            }
        }
    }
    Ok(out)
}

/// WI-1091 — does the instance dictionary for `spec` at `provider` carry the requirement
/// slots the operation `target` will READ?
///
/// THE SAME QUESTION `Interpreter::expand_dispatching_dict` asks at the moment of the
/// frame push, where the answer `no` is a RAISE (WI-857's guard — "`resolve_op_target`
/// can land on a THIRD sort … a frame silently short of the slots its body reads"). Asked
/// here so that `requirements_for_value_directed_impl` does not re-key a channel onto a
/// redirected target the dictionary says nothing about, which would be that raise one
/// call early. Written as a function rather than inline because the two must not come to
/// disagree; the typer's defaulted arm asks a STRONGER question of its own (that
/// `resolve_op_target` lands on the spec op ITSELF, so the default body really is what
/// runs) and is deliberately not routed through this one.
///
/// THE SHAPE IT EXISTS FOR, measured on the stdlib: a dictionary for `FiniteCollection`
/// at `BoxColl`, whose `filter` the carrier INHERITS FROM `Iterable` — a third sort,
/// neither the spec the dictionary witnesses nor the provider it names. `Iterable`'s own
/// chain is not in that layout and never could be, so handing it over is not a supply at
/// all. Same shape one channel over: an `Iterable.isEmpty` channel redirected to
/// `Stream.isEmpty`.
///
/// TRUE for a target that reads NO slots (a namespace-level op, or an owner with an empty
/// chain), because there is then nothing to be short of — which is exactly the
/// `names.is_empty()` arm the eval guard already takes before raising.
pub(crate) fn dictionary_covers_target(
    kb: &mut KnowledgeBase,
    spec: Symbol,
    provider: Symbol,
    target: Symbol,
) -> bool {
    let Some(owner) = impl_parent_of_op(kb, target) else {
        return true;
    };
    // Proposal 066 §7: the target's OWN frame — its sort's chain under its provision.
    let names = op_owner_dict_entries(kb, target).names(kb);
    if names.is_empty() {
        return true;
    }
    // The LENGTH is checked as well as the presence, for the reason the eval guard checks
    // it: two interned copies of one sort would pass `same_sort_canonical` for identity
    // while their two chain reads disagreed, and a short slice is a frame missing slots.
    //
    // AT LEAST, not exactly (proposal 066 §7): a dispatch through a provision lays the
    // provider half out for THAT provision, and a target written outside every block
    // reads only the sort-level prefix of it — whose names every chain of the carrier
    // shares. A longer slice binds slots the target never reads; a shorter one is the
    // missing frame this guards.
    let self_provision = op_owner_provision(kb, target);
    dict_layout(kb, spec, provider, self_provision)
        .slots_for(kb, owner)
        .is_some_and(|slots| slots.len() >= names.len())
}

/// WI-1091 — the one GROUND completion of `goal`'s un-pinned elements, when the spec's
/// providers leave exactly one. `None` when they leave none or several.
///
/// WI-20260830-NX4FD — asked of BOTH halves of the chain now, not only the op half.
/// The two differ in what a `None` MEANS, and that difference stays with the caller:
/// an op-scoped slot is skipped (a body that never reads it must keep running), a
/// sort-level one keeps its slot as a recorded absence (the callee's layout is
/// measured against those slots). Nothing here changes with the half — a completion is
/// exact or it does not exist.
///
/// THE SHAPE THIS EXISTS FOR, measured: `operation twice[V, F](a: V) -> V requires
/// VectorSpace[V, F]` entered from the HOST. The argument pins `V := Vec3`; nothing
/// pins `F`, which appears in no parameter type, so [`resolve_bridge_requirements`]'
/// `all_pinned` gate skipped the slot — and under WI-1091's widened placement the body's
/// `VectorSpace.vec_add(a, a)` reads it and dies `__req_vectorspace not bound`. At a
/// written call site §5.2 makes the author pin it (`twice[F = Float](a)`); the host
/// boundary has no bracket to write, so the choice is to infer it or to refuse the entry.
///
/// WHY IT IS NOT A LOOSER MATCH. The obvious spelling — leave the element open in the
/// goal and let the matcher wildcard it — is CLOSED, and closed on purpose: a per-call
/// value that is a bare type-param does NOT match a concrete candidate ([`dispatch_
/// values_match`] owns that half of WI-824's rule emergently, and its doc says a
/// var-tolerant widening silently re-opens the mis-pin), while DROPPING the binding makes
/// the pairing loop in [`collect_provides_candidates`] reject the candidate outright (a
/// type param the goal omits is discriminating — else every concrete `Eq` impl would
/// match a bare `Eq` goal). Both refusals are right and neither is relaxed here.
///
/// So the completion is CONSTRUCTED and then re-decided by the ORDINARY resolution: one
/// candidate goal per provider, each fully pinned, each run through the very
/// [`resolve_with_rung`] the caller would have run. That is what keeps this from drifting
/// away from the matcher — nothing here decides whether a provider ANSWERS, only which
/// completions are worth asking about. Exactly one survivor is the answer; two are a tie
/// and none is no provider, and both leave the slot absent exactly as before.
pub(super) fn unique_provider_completion(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    scope: &ResolutionScope,
    rung: DefaultRung,
) -> Option<SortGoal> {
    // The elements the arguments did not pin, by the spec's own short names.
    let open: Vec<String> = kb
        .type_params_of_sort(goal.spec_sort)
        .into_iter()
        .filter(|tp| {
            !goal
                .bindings
                .iter()
                .any(|(k, v)| kb.local_name_of(*k) == tp && type_value_is_ground(kb, *v))
        })
        .collect();
    if open.is_empty() {
        return None;
    }
    // Each provider's own ground value for every open element, as one completion. A
    // provider that leaves any of them abstract (`fact VectorSpace[V, F]`, universally
    // quantified) offers no completion and is simply not proposed — it will still be
    // reached by whichever completion another provider proposes, since the resolution
    // below is the ordinary one.
    let spec_canon = kb.canonical_sort_sym(goal.spec_sort);
    let mut completions: Vec<SmallVec<[(Symbol, TermId); 2]>> = Vec::new();
    for rid in provides_rids_by_spec(kb, spec_canon) {
        if !kb.is_fact(rid) {
            continue;
        }
        let Some(head_named) = kb.fact_head_named_args(rid) else {
            continue;
        };
        let Some(spec_view_tid) = get_named_arg(kb, &head_named, "spec") else {
            continue;
        };
        let Some((view_base_sym, view_bindings)) = unwrap_spec_view(kb, spec_view_tid) else {
            continue;
        };
        if view_base_sym != goal.spec_sort {
            continue;
        }
        // A provider that DISAGREES on an element the arguments DID pin cannot answer
        // this goal at any completion, so it is not a rival. Conservative on purpose —
        // it excludes only a provably-ground mismatch — because the veto below rests on
        // whatever survives here.
        let mut could_answer = true;
        for (key, goal_value) in goal.bindings.clone() {
            if !type_value_is_ground(kb, goal_value) {
                continue;
            }
            let short = kb.local_name_of(key).to_string();
            let Some((_, cand)) = view_bindings
                .iter()
                .find(|(k, _)| kb.local_name_of(*k) == short.as_str())
                .copied()
            else {
                continue;
            };
            if type_value_is_ground(kb, cand) && !dispatch_values_match(kb, goal_value, cand) {
                could_answer = false;
                break;
            }
        }
        if !could_answer {
            continue;
        }
        let mut filled: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        for short in &open {
            let hit = view_bindings.iter().find(|(k, v)| {
                kb.local_name_of(*k) == short.as_str() && type_value_is_ground(kb, *v)
            });
            match hit {
                Some((k, v)) => filled.push((*k, *v)),
                None => {
                    filled.clear();
                    break;
                }
            }
        }
        if filled.len() != open.len() {
            // AN OPEN-ENDED RIVAL, and it is why this returns rather than skipping
            // (found by /code-review, and DRIVEN before the fix — measured `Ok(Int(1))`,
            // the ground provider's answer, where the parametric one would have given
            // 2). A provider that leaves an open element abstract answers the goal at
            // MORE THAN ONE completion, so it cannot propose one — and its silence used
            // to read as absence, which is what let a single ground `fact` look like the
            // only answer. It is not a rival to be counted, it is proof the arguments do
            // not decide: `fact Pair[E = A, F = A]` beside `fact Pair[E = Tag, F = Int64]`
            // makes both `F := Int64` and `F := Tag` answerable at `E = Tag`.
            return None;
        }
        // Two providers naming the same value for an element propose ONE completion —
        // they would resolve identically, and counting them twice would read as a tie.
        if !completions.iter().any(|prev| {
            prev.len() == filled.len()
                && prev
                    .iter()
                    .zip(filled.iter())
                    .all(|((_, a), (_, b))| values_structurally_equal(kb, *a, *b))
        }) {
            completions.push(filled);
        }
    }
    let mut answer: Option<SortGoal> = None;
    for filled in completions {
        let mut candidate_goal = goal.clone();
        for (key, value) in filled {
            match candidate_goal
                .bindings
                .iter_mut()
                .find(|(k, _)| kb.local_name_of(*k) == kb.local_name_of(key))
            {
                Some(slot) => slot.1 = value,
                None => candidate_goal.bindings.push((key, value)),
            }
        }
        if !matches!(
            resolve_with_rung(kb, &candidate_goal, scope, rung),
            ResolutionResult::Resolved(_)
        ) {
            continue;
        }
        if answer.is_some() {
            // Two completions both answer — the arguments genuinely do not decide, and
            // taking either would be the WRONG-dictionary case the `all_pinned` gate
            // exists to prevent.
            return None;
        }
        answer = Some(candidate_goal);
    }
    answer
}

/// Extract a `SortGoal` from a `RequiresEntry`'s SortView, keeping only
/// type-parameter bindings (op bindings don't constrain dispatch).
pub(super) fn goal_from_requires_entry(
    kb: &KnowledgeBase,
    entry: &RequiresEntry,
) -> Option<SortGoal> {
    let (_, raw_bindings) = unwrap_spec_view_value(kb, &entry.spec)?;
    let spec_qn = kb.qualified_name_of(entry.required_sort).to_string();
    let bindings: SmallVec<[(Symbol, TermId); 2]> = raw_bindings
        .into_iter()
        .filter(|(k, _)| is_type_param_binding(kb, *k, &spec_qn))
        .collect();
    Some(SortGoal {
        spec_sort: entry.required_sort,
        bindings,
        // A `requires` entry resolves by its declared bindings; carrier
        // discrimination is a call-site concern (WI-350).
        carrier: None,
    })
}

/// WI-222 Phase E (i) / WI-228: rewrite a Pin-now or Direct apply to
/// apply_within with a concrete fn (impl/op symbol) and a projected
/// requirements channel. Used when the callee's parent sort has non-
/// empty `requires_chain` so the callee body can read
/// `frame.requirements`. Returns true iff the rewrite was recorded.
///
/// When `resolved_tree` is `Some`, the requirements list is built from
/// the SLD-resolved sub_resolutions (WI-228 path) — conditional impls
/// produce nested `Dictionary` IR. When `None`, the call site's own
/// `dispatch_dict` is recorded where the typer built one, and only
/// otherwise does the per-dep search run against the callee's
/// `requires_chain` (Direct-call path; no SLD tree available).
///
/// WI-20260925-4ZZKZ — `dispatch_dict` FIRST, because it is the dictionary EVAL
/// threads (`CallClass::ConcreteApplyWithin::dispatch_dict`, built with the call's σ
/// and pin). The σ-less rebuild below re-derives it in the CALLEE's own parameter
/// space, where every element the call pinned is open again: a call pinning
/// `SortedSet[T = String, O = ByLength]` was recorded as a dictionary for
/// `SortedSet[T = El, O = OE]`, whose named slot the σ-less match could not read — a
/// spec half recorded absent in a record of a call that runs (MEASURED: the wn9p8 /
/// tx0g6 / wi456_no_scope rows).
#[allow(clippy::too_many_arguments)]
pub(crate) fn record_apply_within_concrete(
    kb: &mut KnowledgeBase,
    site: crate::kb::CallSite,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    fn_target_sym: Symbol,
    callee_spec_sort: Symbol,
    spec_op_sym: Symbol,
    caller_requires: &DictChain,
    resolved_tree: Option<&ResolvedRequiresNode>,
    dispatch_dict: Option<TermId>,
) -> bool {
    if kb.dispatch_rewrite_at(site).is_some() {
        return false;
    }
    let aw_sym = match kb.try_resolve_symbol("anthill.reflect.Expr.apply_within") {
        Some(s) => s,
        None => return false,
    };
    let syms = match ProjectionSyms::resolve(kb) {
        Some(s) => s,
        None => return false,
    };
    let orig_args_tid = match get_named_arg(kb, named_args, "args") {
        Some(t) => t,
        None => return false,
    };
    let dict_term = match (resolved_tree, dispatch_dict) {
        (Some(tree), _) => match emit_tree_as_projection(kb, caller_requires, tree, &syms) {
            Some(t) => t,
            None => return false,
        },
        (None, Some(built)) => built,
        (None, None) => match build_dispatching_dict_direct(
            kb,
            callee_spec_sort,
            op_owner_provision(kb, spec_op_sym),
            caller_requires,
            &syms,
        ) {
            Some(t) => t,
            None => return false,
        },
    };
    let requirements_list = wrap_dispatch_channel(kb, dict_term);

    mint_apply_within(
        kb,
        site,
        aw_sym,
        fn_target_sym,
        orig_args_tid,
        requirements_list,
        spec_op_sym,
    );
    true
}

/// Mint the `apply_within(fn = Ref(fn_sym), args, requirements)` a call site is rewritten
/// to, and record it — the ONE producer of that term, for the concrete rewrite
/// ([`record_apply_within_concrete`]) and the deferred one ([`record_apply_within_rewrite`])
/// alike. They were two copies until FDPJ8's canon (below) reached only the first; one
/// minter is what keeps the next change from doing the same.
///
/// WI-20260910-FDPJ8 — THE ENTITY'S OWN CANONICAL CONSTRUCTOR FORM, and both halves
/// of that are a change.
///
/// NO POSITIONAL CHANNEL. `anthill.reflect.Expr.apply_within` declares three named
/// fields and no positionals, so a positional channel described a shape the schema has
/// not got. It was also DEAD: `materialize_apply` (req_insertion.rs) is the only
/// producer of the `ClassifiedApply` both callers read, and it hardcodes
/// `pos_args: SmallVec::new()`. Dropping it removes a divergence between what this
/// writes and what `visit_fn`'s reader / the view head can see, at no cost to any
/// value ever produced — and the PARAMETER went with it from both callers, so a future
/// caller cannot hand them positionals to discard in silence.
///
/// AND THROUGH `canonicalize_record_named_args`, not a hand-ordered `from_slice`.
/// The key order here happened to match the declared field order, so this is not a
/// bug fix — it is what stops the next field (or a reordered declaration) from
/// silently minting a term the discrim tree keys differently from every other
/// `apply_within`. One canon, asked of the functor, exactly as every other record
/// producer asks it.
fn mint_apply_within(
    kb: &mut KnowledgeBase,
    site: crate::kb::CallSite,
    aw_sym: Symbol,
    fn_sym: Symbol,
    args: TermId,
    requirements: TermId,
    spec_op_sym: Symbol,
) {
    let fn_ref = kb.alloc(Term::Ref(fn_sym));
    let fn_field = kb.intern("fn");
    let args_field = kb.intern("args");
    let reqs_field = kb.intern("requirements");
    let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::from_slice(&[
        (fn_field, fn_ref),
        (args_field, args),
        (reqs_field, requirements),
    ]);
    kb.canonicalize_record_named_args(aw_sym, &mut named);
    let rewritten = kb.alloc(Term::Fn {
        functor: aw_sym,
        pos_args: SmallVec::new(),
        named_args: named,
    });
    kb.record_dispatch_rewrite(site, rewritten, spec_op_sym);
}

/// WI-222 Phase C+D / WI-237 (names model) / WI-239: defer-to-requirement
/// rewrite. Emits `apply_within(fn = Ref(spec_op_sym), args = <orig>,
/// requirements = [<dispatching dict>])`. Dispatch from spec-op to
/// impl-op happens at the apply_within reduction by reading the
/// dispatching dict's functor. `slot` is the DIRECT requirement's
/// position in `enclosing_sort`'s requires chain, mapped to the
/// synthesized `__req_*` param name via `req_name_for_chain_index`.
///
/// WI-239: `proj_path` descends into that direct requirement's bundled
/// value. Empty ⇒ the dispatching dict is the bare
/// `var_ref(name = __req_<slot>)` (the original WI-222 direct case);
/// non-empty ⇒ the spec is nested, so wrap the `var_ref` in one
/// `requirement_at_sort(chain, slot = k)` per `proj_path` index
/// (outermost last) — the same shape `build_dep_projection` Strategy 2
/// emits, here driven by the resolved tree path.
pub(crate) fn record_apply_within_rewrite(
    kb: &mut KnowledgeBase,
    site: crate::kb::CallSite,
    named_args: &SmallVec<[(Symbol, TermId); 2]>,
    spec_op_sym: Symbol,
    enclosing_sort: Option<Symbol>,
    // WI-822 LEG 1: the operation whose frame `slot` indexes — its sort's slots then
    // its own. Naming the slot from the SORT alone answers `None` for an op-scoped
    // one, and this function's `None` means "emit no rewrite at all", so the recorded
    // IR would silently lose exactly the calls this ticket makes work.
    enclosing_op: Option<Symbol>,
    slot: usize,
    proj_path: &[usize],
) -> bool {
    if kb.dispatch_rewrite_at(site).is_some() {
        return false;
    }
    let aw_sym = match kb.try_resolve_symbol("anthill.reflect.Expr.apply_within") {
        Some(s) => s,
        None => return false,
    };
    let syms = match ProjectionSyms::resolve(kb) {
        Some(s) => s,
        None => return false,
    };
    let orig_args_tid = match get_named_arg(kb, named_args, "args") {
        Some(t) => t,
        None => return false,
    };

    // WI-861 (found by review): the SORT is demanded only where the SORT's chain is what
    // is read. WI-822 LEG 1 gave this function a second chain owner and left the guard in
    // front of both, so an op-scoped classification on a NAMESPACE-level operation (no
    // enclosing sort) would emit NO REWRITE — silently, this function's `false` meaning
    // exactly that — for a call the typer had classified. Its eval twin
    // (`start_apply_deferred`) carried the identical guard, one arm apart, and raised
    // instead; both moved together. UNDRIVEN and stated as such at that twin, where the
    // probe that failed to reach either is recorded.
    let chain = match enclosing_op {
        Some(op) => op_dict_entries(kb, op),
        // No enclosing operation: the sort-level chain (proposal 066 §7).
        None => match enclosing_sort {
            Some(s) => provider_dict_entries(kb, s, None),
            None => return false,
        },
    };
    let name = match chain.name_at(kb, slot) {
        Some(n) => n,
        None => return false,
    };
    // var_ref(__req_<slot>), then one requirement_at_sort step per
    // projection index for the nested case (no-op when proj_path empty).
    let mut dict_expr = build_req_var_ref(kb, &syms, name);
    for &k in proj_path {
        dict_expr = build_req_at_sort(kb, &syms, dict_expr, k);
    }
    let requirements_list = wrap_dispatch_channel(kb, dict_expr);

    mint_apply_within(
        kb,
        site,
        aw_sym,
        spec_op_sym,
        orig_args_tid,
        requirements_list,
        spec_op_sym,
    );
    true
}

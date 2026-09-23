//! Validating call arguments against parameters: argument binding, arrow/callback
//! checks, arity and result-column errors, effect-row self-contradiction.

use super::*;

/// WI-408: outcome of validating one supplied argument / field value against
/// its declared type.
pub(super) enum ArgValidation {
    /// Conforms as-is, or unchecked (a non-ground / polymorphic position is
    /// left for spec-op dispatch / return conformance).
    Ok,
    /// Bare `T` supplied for a declared `Option[T]`: accepted by INSERTING a
    /// `some(...)` coercion around the argument occurrence (the WI-408
    /// some-insertion pass — first slice of the implicit-conversion
    /// framework). The payload is the resolved declared `Option` type, which
    /// the caller stamps onto the synthesized wrapper node.
    WrapSome { declared: Value },
    /// Concrete, ground, and non-conforming.
    Fail(TypeError),
}

/// WI-385: subtype-check one supplied value's type (`actual`) against a declared
/// parameter / field type (`declared`), GATED on groundness. Both sides are
/// first walked through the inference `subst` (so a param a prior argument
/// already pinned reads as its concrete type); the check fires ONLY when both
/// resolve to a fully-concrete type (`resolved_type_is_ground`) — a polymorphic
/// or still-free position is left for spec-op dispatch / return conformance.
/// `Fail` carries the RESOLVED forms (a clean "expected Int, got String",
/// never a raw `?_`) when the concrete actual does not conform. The shared
/// core of the operation-argument (`check_apply_iter`) and entity-field
/// (`check_constructor_iter`) validation.
///
/// Two boundary CONVERSIONS are accepted rather than flagged:
///  - **value→Term reflection** (`is_reflect_term_type`): total, both positions.
///  - **some-coercion** (WI-408, both positions): a bare `T` against a declared
///    `Option[T]` validates `actual` against the element `T` and, on success,
///    returns `WrapSome` — the caller wraps the argument occurrence in a
///    synthesized `some(...)`, so the value is PROPERLY Option-typed at
///    runtime (replaces WI-385's lenient-accept interim, under which the
///    value stayed bare in memory). A bare value that would need a NESTED
///    insertion (`Option[Option[T]]` supplied a bare `T`) is rejected loudly —
///    one wrap is inserted, never a silent double-wrap.
pub(super) fn validate_arg_against_param(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &Value,
    declared: &Value,
    span: Option<Span>,
    context: TypeErrorContext,
    // WI-20260824-Q0093: the occurrence `actual` is the type OF, when the caller has one
    // — read only on the failure path, by [`denoted_type_value`], so a rejected
    // proposal-055 type value can say what it denotes. `None` from a caller with no
    // expression in hand (a relational result column, a declared/actual signature pair).
    actual_node: Option<&Rc<NodeOccurrence>>,
) -> ArgValidation {
    let actual_g = walk_view(kb, subst, actual);
    let declared_g = walk_view(kb, subst, declared);
    // WI-836: [`walk_view`] resolves only the HEAD var / sort-alias chain — it stops at a
    // `Term::Fn`, so a type variable NESTED inside a sort application survives it. Feeding
    // that head-only resolution to `resolved_type_is_ground`, a WHOLE-STRUCTURE predicate,
    // read a param written `List[T = X]` (op type param) or `Box[T = T, O = O]` (the sort's
    // own params, written out) as NON-ground even once σ had fully bound it — so the gate
    // below SKIPPED the check and every generic multi-argument operation silently accepted
    // heterogeneous arguments. RETRY deeply on the non-ground verdict, which pairs the
    // predicate with a resolution of matching depth. (The narrative — why the three
    // neighbouring checks all fire, so the area looked covered — is in
    // `wi836_type_var_arg_agreement_test`'s module doc, beside the programs that pin it.)
    //
    // THIS is the site that must decide it, not the arg-unify loops whose `unify_types`
    // boolean is discarded: unify is EQUALITY, while this check is SUBTYPING plus the three
    // conversions below (reflect-`Term`, WI-408 some-coercion, provider-admissible
    // carrier→bare-spec). A unify-false would over-reject all three.
    //
    // Retried, not substituted for the shallow walk: for a shallow-ground value the deep
    // walk is an identity (groundness means no var and no sort-param ref anywhere left to
    // substitute), so this buys the newly-checkable case without putting an occurrence
    // rebuild on the hot path of every conforming argument. PURE σ (`walk_type_deep_value`,
    // not the grounding `resolve_type_deep_value`): a rigid projection stays an inert
    // neutral leaf and so stays non-ground and skipped, exactly as before — this widens
    // what σ RESOLVES, never what it δ-grounds.
    //
    // WITHHELD WHEN A CALLABLE APPEARS ANYWHERE ([`type_contains_callable`]). This gate does
    // not OWN arrow conformance: an arrow argument is routed to the component-wise
    // `validate_arrow_param_result` (WI-469) and `validate_callback_effect_row` (WI-440)
    // precisely BECAUSE its components must be judged one at a time with the effects row
    // left to dispatch. Deep-walking σ into a callback's row makes the arrow read as ground,
    // which hands it instead to the whole-type `types_compatible` — and that relation
    // REFUSES the pairing WI-775/WI-792 settled must be ACCEPTED: a `Function[A = (a: Int64,
    // b: Int64), B = Int64]` slot states NO arity, so the eta arrow of a 2-parameter
    // operation belongs in it. Measured, not predicted: without this,
    // `wi787_eta_spread_named_tuple_test` (3 cases), `wi784_closure_arity_test`'s rigid-`A`
    // case and `wi424`'s row-gated callback all flipped from load-clean to refused.
    //
    // WI-1085 — THE HOLE THIS LEFT IS CLOSED, and NOT by moving this carve-out. The gap
    // pinned here as `known_gap_two_callback_arguments_sharing_a_type_var_are_not_checked`
    // was read as a consequence of the withholding alone; it was equally a consequence of the
    // checker the callable is routed TO, which tested each component for groundness AS
    // WRITTEN and so skipped a variable σ had already pinned. Resolving the component first
    // (WI-1084 for the result, WI-1085 for the param) closes it with this withholding
    // untouched — the pin is now the positive `two_callback_arguments_sharing_a_type_var_-
    // must_agree`.
    //
    // STRUCTURAL, not a head test — the correction the first cut needed. `types_compatible`
    // DECOMPOSES a sort application down to `arrow_compatible_view`, so a callable NESTED in
    // one is judged by the same arrow relation as a top-level one: measured, a head-only
    // guard newly REFUSED `take[X](l: List[T = Function[A = X, B = Int64]], w: X)` applied
    // to a list of a 2-parameter operation's eta arrow, a program that loads clean before
    // WI-836. The withholding is decided on the DEEP-WALKED pair, which additionally covers
    // a callable σ INTRODUCES (`List[T = X]` with `X := (Int64) -> Bool`) — a shallow test
    // could not see that one at all. When it fires, the SHALLOW pair is kept and the gate
    // below skips exactly as it did before this ticket.
    // WI-1059: the DETERMINED reading — a `Var::Rigid` is not a hole, so a pair carrying one
    // is checkable here (see [`type_value_is_ground_g`] for why this is a different question
    // from the CONCRETE one WI-387 FIX 3 asks of the same walk). This is the gate whose skip
    // was WI-1059's second leak: a rigidified `E` made the pair non-ground and the function
    // returned `Ok` without checking anything.
    let mut both_ground =
        resolved_type_is_determined(kb, &actual_g) && resolved_type_is_determined(kb, &declared_g);
    // Groundness (cheap, and the verdict on a measured 69% of calls) is tested FIRST, so a
    // conforming concrete argument never pays for the walk or the callable scan.
    let (actual_g, declared_g) = if both_ground {
        (actual_g, declared_g)
    } else {
        let deep_a = walk_type_deep_value(kb, subst, &actual_g);
        let deep_d = walk_type_deep_value(kb, subst, &declared_g);
        if type_contains_callable(kb, &deep_a) || type_contains_callable(kb, &deep_d) {
            (actual_g, declared_g)
        } else {
            both_ground = resolved_type_is_determined(kb, &deep_a)
                && resolved_type_is_determined(kb, &deep_d);
            (deep_a, deep_d)
        }
    };
    if !both_ground {
        // WI-469: a denoted-bearing arrow callback param whose EFFECTS row is
        // non-ground (it carries the op's `EffP` type-param and a binder-relative
        // `-Modify[x]`) makes the WHOLE arrow non-ground, so the gate above would
        // skip it — silently accepting a callback whose CONCRETE param/result
        // element type is wrong (a `(String) -> Bool` where `(Int64) -> Bool` is
        // declared). When the arrow's param/result ARE concrete, validate them
        // here (contravariant param, covariant result); the effects-row alignment
        // stays deferred to dispatch / `validate_callback_effect_row`. A genuinely
        // polymorphic param/result (a free type-var) stays non-ground and is left
        // for dispatch — distinguishing polymorphic-non-ground from denoted-but-
        // concrete, the WI-385 groundness discipline.
        if let Some(err) =
            validate_arrow_param_result(kb, subst, &actual_g, &declared_g, span, &context)
        {
            return ArgValidation::Fail(err);
        }
        // WI-RKMD4: THE VARIABLE FREES ITS OWN SLOT, NOT THE HEAD ABOVE IT. Everything
        // above this line treats "not ground" as "not mine to decide", and for the
        // variable-occupied SLOTS that is right. It is not right for the constructor the
        // slots hang off: `Message[Trust = Untrusted]` against `Text[Trust = ?t]` is a
        // decided mismatch at `Message`/`Text` no matter what `?t` turns out to be, and
        // returning `Ok` here is what let it through. See [`nominal_head_mismatch`] for
        // why a silent pass is the WORST outcome available at this gate rather than a
        // neutral one.
        //
        // The pair here is the WI-836 retry's — DEEP-walked, or the shallow one it kept for
        // a callable. Either is admissible: a shallow read resolves strictly less, and
        // less-resolved can only make this check DECLINE (a var and a sort-param are both
        // "not a nominal head"), never claim a mismatch it would not claim deeply.
        if nominal_head_mismatch(kb, subst, &actual_g, &declared_g, HeadPosition::Argument) {
            return ArgValidation::Fail(conformance_error(
                kb,
                declared_g,
                actual_g,
                span,
                context,
                actual_node,
            ));
        }
        // THE CALLABLE-KIND VERDICT IS NOT ASKED AGAIN HERE, and it was until
        // `/code-review` read the call above. `nominal_head_mismatch`'s FIRST statement is
        // `callable_against_callable_free(actual, declared)` on these same two values, so a
        // second call on the line below could never be true — the comment defending it
        // ("the two reach different pairs: this one sees the whole argument, that one the
        // per-binding descent") described where the verdict was FIRST placed, not where it
        // ended up. MEASURED before removing it: neutralized, the anthill-core suite is
        // 5605/0, unchanged. The whole-argument pair is covered — by the call inside
        // `nominal_head_mismatch`, which the head test above reaches with it.
        return ArgValidation::Ok;
    }
    // value→Term reflection: total conversion, accept any actual vs declared Term.
    if is_reflect_term_type(kb, &declared_g) {
        return ArgValidation::Ok;
    }
    if types_compatible(kb, subst, &actual_g, &declared_g) {
        return ArgValidation::Ok;
    }
    // WI-408 some-coercion: a non-conforming value against `Option[T]`
    // re-checks against the element `T` (so `description: "…"` peels to a
    // Term and the reflection above accepts it) and reports the wrap. Runs
    // AFTER `types_compatible` so an already-conforming Option is never
    // re-wrapped; an `Option[T]` actual against `Option[Option[T]]` declared
    // is a valid PAYLOAD and takes the one outer wrap.
    if is_option_type(kb, &declared_g) {
        match extract_type_param(kb, &declared_g, "T") {
            Some(inner) => {
                return match validate_arg_against_param(
                    kb,
                    subst,
                    &actual_g,
                    &inner,
                    span,
                    context.clone(),
                    actual_node,
                ) {
                    ArgValidation::Ok => ArgValidation::WrapSome {
                        declared: declared_g,
                    },
                    // WrapSome: the value is bare at BOTH depths of a nested
                    // Option — a single wrap cannot repair it; demand the
                    // explicit inner `some(...)` rather than silently
                    // guessing the nesting depth. Fail: report the OUTER
                    // expected/actual pair (clearer than the peeled element
                    // mismatch).
                    ArgValidation::WrapSome { .. } | ArgValidation::Fail(_) => {
                        ArgValidation::Fail(TypeError::TypeMismatch {
                            site: TypeError::here(),
                            span,
                            context,
                            expected: declared_g,
                            denoted: denoted_type_value(kb, actual_node),
                            actual: actual_g,
                        })
                    }
                };
            }
            // A bare `Option` (unconstrained element) has no element to
            // re-check — any value is its `some` payload.
            None => {
                return ArgValidation::WrapSome {
                    declared: declared_g,
                }
            }
        }
    }
    // WI-385: a concrete carrier conforms to a BARE spec it PROVIDES — e.g.
    // `List[Int]` passed where `Stream` is declared (`List provides Stream`).
    // `types_compatible` confines provider-admissibility to its bare↔bare arm (so
    // it never drops a PARAMETERIZED spec's bindings), so a parameterized-carrier-
    // vs-bare-spec pairing reaches here unaccepted. The declared spec here is bare
    // (no bindings to drop), so an admissible provider is sound to accept —
    // restoring the pre-WI-385 behavior (no arg/field check rejected it) for the
    // concrete-provider→bare-spec case.
    if let (Some(actual_base), Some(declared_sort)) = (
        type_base_sort_view(kb, &actual_g),
        extract_sort_ref_sym(kb, &declared_g),
    ) {
        if sort_provides_admissibly(kb, actual_base, declared_sort) {
            return ArgValidation::Ok;
        }
    }
    ArgValidation::Fail(conformance_error(
        kb,
        declared_g,
        actual_g,
        span,
        context,
        actual_node,
    ))
}

/// WI-RKMD4: does `actual` disagree with `declared` at a NOMINAL HEAD CONSTRUCTOR —
/// the one verdict a pair the [`validate_arg_against_param`] groundness gate SKIPS can
/// still reach?
///
/// WHY THE SKIP WAS NOT A NEUTRAL OUTCOME. `both_ground` is the WI-385 discipline: a
/// position still carrying a variable is someone else's to settle, so leave it. That is
/// right about the variable's own SLOT and wrong about the constructor the slot hangs
/// off. `sum_flat(m: Text[Trust = ?t])` applied to a `Message[Trust = Untrusted]` is a
/// mismatch at `Message`/`Text` under EVERY instantiation of `?t`, and nobody downstream
/// re-asks it: the arg-unify loop's failure to bind `?t` is discarded, so `?t` stays free
/// and the RESULT type `Text[Trust = ?t]` reaches the next call still open. A free
/// variable is not a neutral leftover there — it is the MAXIMALLY PERMISSIVE value,
/// because the consumer instantiates it to whatever it wants. Measured on
/// `examples/guardians`, where `?t` is an information-flow label, the consumer was a
/// `sink(body: Text[Trust = Public])` and the accepted program was an exfiltration: the
/// silent pass LAUNDERED the label the signature exists to carry.
///
/// WHAT IT DECIDES, AND WHAT IT REFUSES TO DECIDE. Only the nominal spine — a bare sort
/// or a sort application, on BOTH sides, and not a `Function` spec. Every other form
/// answers "not mine": a variable (flex, rigid or a declared `type_var`), an arrow, a
/// named tuple, an effects row, a neutral projection, `nothing`. Those are the forms
/// whose conformance genuinely is deferred, and three of them (arrow, row, neutral) have
/// owners that this gate is deliberately positioned AFTER — `validate_arrow_param_result`,
/// `validate_callback_effect_row`, dispatch.
///
/// THE TWO CONVERSIONS ARE HEAD DISAGREEMENTS BY CONSTRUCTION, so neither may be read as
/// one: a declared reflect `Term` takes a value of any sort, and a declared `Option[T]`
/// takes a bare `T` through the WI-408 some-coercion. The ground path below the gate
/// accepts both INSTEAD of comparing, and this predicate must not contradict it. They are
/// withheld at DIFFERENT widths, which is the point of stating them separately: `Term`
/// takes any value at all, so nothing about the pair is decidable; the some-coercion
/// concerns only the OUTER head, so two `Option`s still descend and a wrong element sort
/// is refused under an `Option` exactly as under any other container.
///
/// `symmetric` is the DIRECTION question, and it is only false at the top. There the pair
/// is `actual <: declared` and the relation is the directed one. Below the top the
/// parameter's declared VARIANCE decides which side is the subtype, and this predicate
/// does not read variance — so it claims a mismatch only when NEITHER direction could
/// hold, the verdict covariant, contravariant, invariant and bivariant all agree on.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum HeadPosition {
    /// The outer ARGUMENT (or entity-field) position. Directed — the pair is `actual <:
    /// declared` — and the ONE place the two boundary conversions can apply.
    Argument,
    /// A nested binding, or a callback component. Neither boundary conversion reaches
    /// here.
    ///
    /// **THE PAIR IS STILL DIRECTED, and that is the correction /code-review found.** The
    /// sentence that stood here — "the parameter's declared VARIANCE is not read, so only
    /// a verdict both directions agree on may be claimed" — was true while every verdict
    /// under this position was symmetric, and stopped being true when WI-20260904-50B2K
    /// put [`callable_against_callable_free`], a ONE-DIRECTIONAL verdict, at
    /// [`nominal_head_mismatch`]'s top. It is claimed here, and soundly: every caller
    /// hands `(subtype-candidate, supertype-candidate)` in that order, and the
    /// CONTRAVARIANT caller reaches that convention by SWAPPING its operands rather than
    /// by asking a different question (see the arity-1 arrow-parameter arm). A directed
    /// verdict inside therefore reads one relation at both callers.
    ///
    /// **WHAT IS STILL NOT READ is the sort parameter's own VARIANCE at the per-binding
    /// descent**, which pairs `actual`'s binding with `declared`'s at the same label — a
    /// covariant reading. A verdict claimed there is wrong for a parameter declared
    /// contravariant.
    ///
    /// **BUILT, MEASURED AND NOT SHIPPED**, and the measurement is at the descent loop in
    /// [`nominal_head_mismatch`] rather than repeated here. The short of it: the gate is
    /// three lines ([`declared_variance`] has existed since WI-293), the INVARIANT default
    /// must ask the un-swapped direction or it refuses WI-836's program the moment its
    /// container is a user sort, and CONTRAVARIANT — the only arm that could then change
    /// an answer — reaches this descent zero times against ~196k reaches as the positive
    /// control. So the exposure is real and stated, and closing it waits for a program
    /// that reaches it. /code-review asked twice for an owner rather than prose; a ticket
    /// was written and deleted, because the description was longer than the fix and the
    /// fix turned out to be unmeasurable. WI-20260905-175SD owns what is actually missing:
    /// a PROGRAM that reaches this descent with a non-covariant parameter.
    Nested,
}

/// WI-20260904-50B2K — is `actual` a FUNCTION where `declared` can hold none? A decided
/// mismatch whatever the variables inside either side turn out to be, so it is claimable
/// on a NON-GROUND pair, which is the whole point: once an un-annotated lambda binder is
/// the engine's own variable, every type carrying one is non-ground and the groundness
/// gate withholds every verdict about it.
///
/// ONE DIRECTION, and the asymmetry is measured on both sides.
///   * ACTUAL callable, DECLARED callable-free: decided. There is no coercion from a
///     function to a type with no function anywhere in it.
///   * The REVERSE has two: an eta-lift and a zero-arg thunk. Claiming it broke
///     `wi_cbrsw_permission_effect_test::a_denial_of_a_sub_capability_does_not_forbid_the_
///     super_capability` with "expected () -> Unit, got Unit" on a program that must load.
///
/// `type_contains_callable` on the declared side, not a head test, is what keeps the
/// WI-408 some-coercion: a lambda handed to an `Option[T = Function[…]]` slot must be
/// WRAPPED, and that declared type contains a callable, so this declines.
fn callable_against_callable_free(kb: &KnowledgeBase, actual: &Value, declared: &Value) -> bool {
    // THE REFLECT-`Term` ESCAPE IS PART OF THE VERDICT, not of its callers. `value->Term`
    // is a TOTAL conversion — `validate_arg_against_param` states it as "accept any actual
    // vs declared Term" — so a function IS admissible in a `Term` slot and this claim must
    // decline. Found by `/code-review`, MEASURED: with the check left to the callers, this
    // verdict answered first at `nominal_head_mismatch`'s top and
    // `term_to_string(lambda x -> x)` flipped from LOADS CLEAN to "expected Term, got
    // ??param -> ??param" — while its ANNOTATED twin kept loading, because a ground pair
    // never reaches the non-ground branch at all. Asking it HERE is what makes one owner
    // cover both call sites; a caller-side guard is the shape that goes missing at the
    // second one.
    //
    // UNCONDITIONAL, where `nominal_head_mismatch`'s own reflect guard is
    // `HeadPosition::Argument`-gated: this verdict is an ADDITION, so declining more widely
    // than necessary can only withhold a refusal, never invent one.
    !is_reflect_term_type(kb, declared)
        && type_head_is_callable(kb, actual)
        && !type_contains_callable(kb, declared)
        && resolved_type_is_determined(kb, declared)
}

fn nominal_head_mismatch(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    actual: &Value,
    declared: &Value,
    position: HeadPosition,
) -> bool {
    // WITHHELD AT A CALLABLE HEAD — per NODE, which is as wide as WI-836's measurement
    // reaches and no wider. `types_compatible` decomposes a sort application down to
    // `arrow_compatible_view`, so comparing a `Function[A, B, E]` against anything here
    // would be a back door to the refusal WI-836 measured as WRONG: `take[X](l: List[T =
    // Function[A = X, B = Int64]], w: X)` applied to `cons(sub2, nil())` reaches this
    // descent as `Function[A = ?X, B = Int64]` against `Int64`, and that program loads and
    // evaluates (`wi836…::a_callback_slot_nested_in_a_sort_application_still_withholds`).
    //
    // NOT the whole-type [`type_contains_callable`], which is the withholding the WI-836
    // retry itself uses and which would be an exclusion wider than its justification here:
    // that ticket's evidence is about a callable being COMPARED, not about one being
    // present somewhere in the type. A callable nested in a binding this walk never
    // reaches — `Config[Fmt = Text[Trust = ?t], Hook = Function[…]]` — leaves the `Fmt`
    // disagreement perfectly decidable, and the coarse test would have dropped it. An
    // ARROW head needs no mention: it is not a nominal head, so it declines below anyway.
    // WI-20260904-50B2K — ABOVE the withholding below, because that withholding is
    // SYMMETRIC where its evidence is one-directional. WI-836's program descends to
    // actual `Int64` against declared `Function[A = ?X, B = Int64]` and must load; this
    // verdict is the OTHER pairing, actual callable against a callable-free declared, and
    // `takes_list([lambda x -> 7])` against `takes_list(l: List[T = Int64])` is decided at
    // the `T` binding no matter what the lambda's binder turns out to be.
    // THE ONE SITE, and it serves BOTH pairs — this function is called with the WHOLE
    // argument against the WHOLE declared type at `validate_arg_against_param`'s
    // non-ground branch (a lambda in an `Int64` field: `plain(lambda x -> x)` against
    // `entity plain(v: Int64)`) and again on each descent (a lambda inside a
    // `List[T = Int64]`). The gate used to ask the verdict a second time for the first of
    // those; measured dead and removed.
    if callable_against_callable_free(kb, actual, declared) {
        return true;
    }
    if type_head_is_callable(kb, actual) || type_head_is_callable(kb, declared) {
        return false;
    }
    if position == HeadPosition::Argument && is_reflect_term_type(kb, declared) {
        return false;
    }
    let (Some((a_base, a_bindings)), Some((d_base, d_bindings))) = (
        nominal_head_parts(kb, actual),
        nominal_head_parts(kb, declared),
    ) else {
        return false;
    };
    if !nominal_heads_compatible(kb, subst, a_base, d_base, position) {
        // The WI-408 some-coercion is a head disagreement BY CONSTRUCTION — a bare `T`
        // against a declared `Option[T]` — so at the ARGUMENT position this verdict is not
        // this predicate's to reach. It withholds the HEAD verdict only, not the whole
        // check: two `Option`s agree at their head and reach the descent below, where a
        // wrong element sort is refused exactly as it is under any other container. (The
        // ground path draws the same line — it re-checks against the ELEMENT, so
        // `Option[Message[…]]` against `Option[Text[Trust = ?t]]` fails there too.)
        //
        // AT THE ARGUMENT POSITION ONLY, and the guard is the whole point of
        // [`HeadPosition`] rather than a second bool. The coercion is inserted by
        // `check_apply_iter` around the ARGUMENT OCCURRENCE — there is no such rewrite for
        // a nested slot or a callback component — so honouring it deeper withholds a
        // verdict nobody else reaches. MEASURED (found by `/code-review`): with this
        // withheld at every depth, `take(xs: List[T = Option[T = Text[Trust = ?t]]])` given
        // a `List[T = Message[…]]` loaded CLEAN and laundered `?t` to `Public` at the sink,
        // while its ground twin was refused — the exact shape this ticket exists to close,
        // one level down.
        return position == HeadPosition::Nested || !is_option_type(kb, declared);
    }
    // DESCEND ONLY THROUGH ONE SORT'S OWN PARAMETERS. `nest3` is why there is a descent
    // at all: `List[T = Message[…]]` against `List[T = Text[Trust = ?t]]` agrees at
    // `List` and disagrees one level down, and a head-only test would have called that
    // program clean. It stops at a CROSS-SORT accept (provider admissibility, an alias
    // shape) because such an accept translates the parameter space, and this predicate
    // does not own that translation — [`parameterized_compatible_view`] does, and it gets
    // the pair once σ has determined it.
    if !same_sort_canonical(kb, a_base, d_base) {
        return false;
    }
    // `Label`, not [`BindingKeyMatch::for_bases`]: that predicate asks
    // `same_sort_canonical` and the guard above has already answered it, so calling it
    // here would read as if a cross-sort key spelling were handled and could only ever
    // return this same value.
    for (param, dv) in &d_bindings {
        let Some(av) = binding_for_param(kb, &a_bindings, *param, BindingKeyMatch::Label).cloned()
        else {
            continue;
        };
        // WI-20260904-50B2K — READING THE DECLARED VARIANCE HERE WAS BUILT, MEASURED AND
        // NOT SHIPPED, recorded so the next reader does not re-derive it. Pairing
        // `actual`'s binding with `declared`'s at the same label is a COVARIANT reading
        // and the only one this loop has; [`HeadPosition::Nested`]'s doc states the
        // exposure. [`declared_variance`] has existed since WI-293, so the gate is three
        // lines — and the three lines are the wrong trade:
        //
        //   COVARIANT     is what this loop already does.
        //   INVARIANT     is the DEFAULT (every sort with no variance fact), and asking
        //                 the swapped direction there DECIDES where the design says
        //                 withhold — the predicates under this descent are
        //                 one-directional by construction, this ticket's own fourth edit
        //                 having made them so. Driven: WI-836's program over a user sort
        //                 `Holder[T = Function[A = X, B = Int64]]` given `holder(v: 1)`
        //                 went from loading to "expected Holder[T = Function[A = ?X,
        //                 B = Int64]], got Holder[T = Int64]", while the identical program
        //                 over `List` (covariant) loads — WI-836's own row. So invariant
        //                 must ask the un-swapped direction, i.e. behave as covariant.
        //   CONTRAVARIANT is then the ONLY arm that could change an answer, and
        //                 `Contravariant(sort: Function, param: A)` is the only such fact
        //                 in the stdlib — so it needs a `Function` on BOTH sides, agreeing
        //                 at the head, reaching the non-ground branch. Probed over the
        //                 whole binary: ZERO reaches, against 145,858 Invariant and 50,480
        //                 Covariant as the positive control; two hand-built programs did
        //                 not reach it either.
        //   BIVARIANT     needs both facts on one parameter. Nothing asserts both.
        //
        // A four-arm match whose two live arms are the current behaviour and whose other
        // two cannot be driven READS as "variance is handled here" while nothing exercises
        // it — worse than this comment. Ship it when a program reaches it, which is
        // WI-20260905-175SD: find the witness first, and if none exists say so
        // structurally (the likely reason being that a `Function` pair is decided earlier,
        // by `arrow_compatible`'s hardcoded variance or by the head verdict, and never
        // reaches this NOMINAL descent).
        if nominal_head_mismatch(kb, subst, &av, dv, HeadPosition::Nested) {
            return true;
        }
    }
    false
}

/// The nominal spine of a type — `(head sort, its bindings)` for a bare sort `S` (no
/// bindings) or an application `S[…]`; `None` for every other form. The reading
/// [`nominal_head_mismatch`] is confined to, split out so the "which forms are nominal"
/// question is answered in ONE place rather than at each of its two uses.
///
/// A HEAD THAT IS ITSELF A PARAMETER IS NOT A HEAD, and it is spelled as a `Symbol` like
/// any other, which is what makes it worth stating. `sort Spec[F[T]]`'s marked carrier
/// `F` reaches here as `Parameterized { base: F }` — a higher-kinded slot the unifier
/// FILLS (`F[T = A] ≟ Option[T = X]` ⟹ `F := Option`, see [`parameterized_base_term`]),
/// so reading `F` as a constructor and comparing it to `Option` calls a fillable variable
/// a mismatch. MEASURED: without this, `wi453_hk_concrete_fill_test`'s two arg-carrier
/// rows are refused. `walk_view` does not close the gap — it resolves the head var /
/// alias chain and STOPS at a `Term::Fn`, so an application's FUNCTOR is never resolved
/// (which is exactly why a bare `T` reaches here already resolved to its var, and a
/// higher-kinded `F[…]` does not).
fn nominal_head_parts(kb: &KnowledgeBase, ty: &Value) -> Option<(Symbol, Vec<(Symbol, Value)>)> {
    let (base, bindings) = match extract_type(kb, ty) {
        TypeExtractor::SortRef(s) => (s, Vec::new()),
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return None,
    };
    if is_sort_param_symbol(kb, base)
        || matches!(
            resolve_sort_alias(kb, base).map(|t| kb.get_term(t)),
            Some(Term::Var(_))
        )
    {
        return None;
    }
    Some((base, bindings))
}

/// Are two nominal HEADS compatible — nominal identity, entity subtyping, `refines`,
/// provider admissibility, alias shape?
///
/// Asked by handing the two bare sort references to [`types_compatible`], which is the
/// same thing [`parameterized_compatible_view`] does with its two bases and for the same
/// reason: the head question already has an owner, and a second spelling of it here
/// would be a second opinion about when two sort identities are one — the drift WI-872
/// found five call sites of.
///
/// ON THE `Value` CARRIER, and it took a fix to make that available. `Value::SymbolRef(S)`
/// views as `ViewHead::Ref(S)` — exactly what [`type_head`] reads as a bare sort — but
/// [`types_compatible_view_structural`] had NO `sort_ref`↔`sort_ref` arm, so two of them
/// fell to its `_ => false` and reported every head as a mismatch, identical ones
/// included. WI-RKMD4 wired that arm (see [`bare_sort_compatible`]) rather than routing
/// around it through `kb.alloc(Term::Ref(…))`: interning a term to ask a question is the
/// wrong shape for a TRANSIENT query — hash-consing is for persistent, heavily-shared
/// structure — and routing around a silent wrong answer leaves it there for the next
/// producer. So this call is now that arm's DRIVER: every head comparison the corpus makes
/// goes through it.
///
/// Every probe substitution is DISCARDED, in both directions: this predicate is consulted
/// at a gate that otherwise returns `Ok` unchanged, so it must add refusals and nothing
/// else — no binding it makes may survive into the caller's σ.
pub(super) fn nominal_heads_compatible(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    actual: Symbol,
    declared: Symbol,
    position: HeadPosition,
) -> bool {
    if same_sort_canonical(kb, actual, declared) {
        return true;
    }
    let a_ref = Value::SymbolRef(actual);
    let d_ref = Value::SymbolRef(declared);
    let mut probe = subst.clone();
    if types_compatible(kb, &mut probe, &a_ref, &d_ref) {
        return true;
    }
    if position == HeadPosition::Nested {
        let mut probe = subst.clone();
        if types_compatible(kb, &mut probe, &d_ref, &a_ref) {
            return true;
        }
    }
    false
}

/// WI-469: validate a callback argument's CONCRETE arrow param/result element
/// types against the declared arrow param, for the case the
/// [`validate_arg_against_param`] groundness gate skips: a denoted-bearing arrow
/// whose EFFECTS row is non-ground (an `EffP` type-param + a binder-relative
/// `-Modify[x]`) but whose PARAM and RESULT types are concrete. Returns
/// `Some(error)` when a concrete component is decisively incompatible; `None`
/// when neither side is an arrow, or a relevant component is non-ground (left for
/// dispatch / unification — a genuinely polymorphic callback must NOT be rejected
/// here).
///
/// Variance follows function subtyping (the same relation [`arrow_compatible_view`]
/// uses, but component-wise so the non-ground effects row is left untouched):
///   * param is CONTRAVARIANT — the callback must accept the value the declared
///     arrow is called with (`declared.param <: actual.param`);
///   * result is COVARIANT — the callback's result must satisfy the declared
///     result (`actual.result <: declared.result`).
/// Each component check fires only when BOTH sides of it are ground, so a
/// polymorphic actual / declared component is conservatively skipped — groundness
/// asked of the component AFTER σ resolves it, so "polymorphic" means genuinely
/// un-pinned and not merely written with a variable (WI-1084/WI-1085; the one
/// exception, and why, is at the `Function` arm).
///
/// WI-1085 — WHICH RELATION the PARAM check uses is decided by the SPELLING OF
/// BOTH SIDES, not by the declared one alone. [`arrow_parts`] decomposes an `arrow`
/// and a `Function[A, B, E]` onto one `param`, but an arrow's is a parameter LIST
/// (applied positionally at arity ≠ 1) and a `Function`'s `A` is one argument's
/// DATA type — so one comparison served two questions and got the arrow one wrong.
/// The POSITIONAL relation needs a parameter list on each side, so it is reached
/// only by an `arrow`/`arrow` pair; the three MIXED pairings all take the by-name
/// one. Keying on the declared spelling alone was this ticket's first cut and gave
/// the positional relation to a `Function`-typed ARGUMENT at an arrow slot — the
/// same WI-775 bridge from the other side, pinned by
/// `wi1085…::a_function_typed_argument_at_an_arrow_slot_is_refused_whatever_the_labels`.
/// The arms at the site state each, along with which side σ resolves and why they
/// differ on that too.
pub(super) fn validate_arrow_param_result(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &Value,
    declared: &Value,
    span: Option<Span>,
    context: &TypeErrorContext,
) -> Option<TypeError> {
    let (Some((Some(d_param), d_result, _)), Some((Some(a_param), a_result, _))) =
        (arrow_parts(kb, declared), arrow_parts(kb, actual))
    else {
        // Not both arrows (or a param-less form) — nothing this helper can decide.
        return None;
    };
    // WI-1085: RENDERED AS σ RESOLVES IT — the type each side HAS at this call site, which is
    // what the reader needs and what the checks below mostly compare. The measured message
    // for two callback arguments sharing one variable was `expected ?X -> Int64, got String ->
    // Int64`: the reader was shown the variable and not the `Int64` the FIRST argument had
    // pinned it to, which is the whole content of the disagreement.
    //
    // UNIFORM, THOUGH ONE ARM COMPARES AS-WRITTEN. The `Function`-slot arm below deliberately
    // does not σ-resolve its operands, so on that path the rendering resolves more than the
    // comparison read. It resolves no LESS — that arm's gate already requires both operands
    // ground as written, so σ is an identity on them — and what it adds is the binding of a
    // component the comparison did not consult (a slot declared `-> R` prints its pinned `R`).
    // Extra context about the same two types, never a different verdict; a per-arm rendering
    // would buy nothing but a second way for the two to disagree.
    //
    // (`walk_type_deep_value` is pure σ, so this names a binding and never δ-grounds one into
    // existence.)
    let mismatch = |kb: &mut KnowledgeBase, subst: &mut Substitution| TypeError::TypeMismatch {
        site: TypeError::here(),
        span,
        context: context.clone(),
        expected: walk_type_deep_value(kb, subst, declared),
        // A CALLBACK's arrow component against the slot's: the pair is two arrow types,
        // and neither side is an expression this call has an occurrence for.
        denoted: None,
        actual: walk_type_deep_value(kb, subst, actual),
    };
    // WI-792: ARITY, and it runs FIRST because it is THE ONE COMPONENT THIS CHECK
    // CAN ALWAYS DECIDE. The groundness discipline below defers a component whose
    // type is still polymorphic; an arrow's arity is a ground `Const(Int)` sibling
    // however polymorphic its param and result are, so that justification simply
    // does not reach it. Without this, a callback argument to a TYPE-PARAMETERIZED
    // operation was never conformance-checked at all: `apply2[T](f: (x: T, y: T)
    // -> Int64, …)` given a ONE-tuple-parameter op loaded clean and trapped
    // `ArityMismatch` at eval, while the identical program written NON-generically
    // is refused at load by WI-791 — genericity was the whole difference.
    //
    // A `Function[A, B, E]` side yields `None` and the check skips, which is the
    // right answer rather than a gap: WI-775 settled that its `A` is the ONE
    // argument `apply(f, x: A)` passes, so it states no arity and cannot.
    //
    // DECIDED (WI-792, user): this also refuses the DUAL — a TWO-parameter op into
    // a generic `(x: T) -> R` slot — which loads and evaluates today, but only
    // because eval spreads a single POSITIONAL tuple argument; the name-keyed
    // spelling of the same program already traps. WI-791 took exactly this trade
    // at the conformance rung (`two_parameter_operation_is_refused_for_a_tuple_-
    // argument_arrow`) on the grounds that letting a type relation depend on how a
    // caller happens to build its tuple is incoherent. Since WI-784 the spread
    // convention is reachable through `Function[A, B]` for operations AND lambdas
    // in both application forms, so nothing is lost by refusing it here.
    let arity_key = kb.intern("arity");
    // WI-1085: both counts are kept — the equality below is one question, and WHICH
    // RELATION the param slots take is another that reads the same two numbers.
    let (d_arity, a_arity) = (
        arrow_arity(kb, declared, arity_key),
        arrow_arity(kb, actual, arity_key),
    );
    if let (Some(d), Some(a)) = (d_arity, a_arity) {
        if d != a {
            return Some(mismatch(kb, subst));
        }
    }
    // WI-801: and the `Function[A, B, E]` half of the same question, which the
    // paragraph above correctly declines to answer. That a `Function` states no
    // arity does NOT mean nothing about the callback's arity is decidable — its
    // `A` states a COMPONENT COUNT, and only two arities can be applied at the
    // slot. This is the NON-GROUND path's decider; the ground path's is
    // [`arrow_function_compatible`]. Reported through
    // [`function_slot_arity_error`] rather than `mismatch()`, which would render
    // the two sides identically — see that function's doc.
    //
    // WI-1087: σ-RESOLVED, for the same reason the components below are and with a sharper
    // consequence — this decider reads `A`'s COMPONENT COUNT, and an `A` written as a
    // variable states none, so a genuine arity disagreement reached the structural relation
    // instead and was rendered as a type mismatch. MEASURED on `apT[T](f: Function[A = T, B
    // = Int64], t: T)` given a 2-parameter operation and a 3-component tuple: `expected
    // Function[A = (a, b, c), …], got (_1, _2) -> Int64`, true and useless, where the
    // resolved read says `a callback of 1 parameter (taking the whole argument type) or 3
    // (its components spread), got a callback of 2 parameters`. Which is WI-795's rule —
    // report the pair that actually differs — and WI-801's, that this disagreement renders
    // as itself.
    let declared_r = walk_type_deep_value(kb, subst, declared);
    if let Some(err) = function_slot_arity_error(kb, &declared_r, actual, span, context) {
        return Some(err);
    }
    // Contravariant param: `declared.param <: actual.param`.
    //
    // WI-1085 — ONE COMPARISON WAS ANSWERING TWO DIFFERENT QUESTIONS. [`arrow_parts`] maps
    // both callable spellings onto one `param`, which erases the very distinction the answer
    // turns on, so the DECLARED spelling ([`type_dispatch_name_view`]) has to be consulted
    // separately. It selects the RELATION and, with it, the OPERAND that relation is applied
    // to — the two arms differ on both, and each says why.
    //
    // BOTH SPELLINGS ARE READ, not just the declared one. The positional relation belongs to
    // a pair of parameter LISTS, so it needs an `arrow` on EACH side — and the mismatched
    // pairing runs in both directions, a `Function[A = …]` ARGUMENT reaching an `arrow` slot
    // as readily as the reverse. Keying on the declared spelling alone would hand that one
    // the positional relation and bridge `A` to a parameter list from the other side, which
    // is the same WI-775 hole through the back door.
    let param_list_arity = match (
        type_dispatch_name_view(kb, declared),
        type_dispatch_name_view(kb, actual),
    ) {
        // Both counts are `Some` here BY CONSTRUCTION, so there is nothing to assert and no
        // count to invent: [`extract_type`]'s `Arrow` arm yields `Error` unless the `arity`
        // child reads as a `Const(Int)`, so a malformed arrow makes [`arrow_parts`] answer
        // `None` and this function returned at its head. (A first cut carried a
        // `debug_assert` here modelled on [`agreed_arrow_arity`]'s; that one guards a
        // relation reached WITHOUT an `arrow_parts` decode, and this one could not fire.)
        // The equality above has already refused a pair whose two counts disagree, so either
        // count names the same list length.
        (Some("arrow"), Some("arrow")) => d_arity,
        _ => None,
    };
    match param_list_arity {
        // A GENUINE ARROW PAIR — the arity above is one both sides state and agree on, and at
        // arity ≠ 1 the slot is a parameter LIST, applied POSITIONALLY (WI-782's `_1.._n`
        // convention, WI-442's synthetic escape). [`arrow_params_compatible`] is the relation
        // the GROUND path already uses for exactly this pair ([`arrow_compatible_view`]), and
        // it routes arity ONE back to the ordinary type relation itself (WI-791: a lone
        // parameter's slot is its TYPE, and a tuple there is DATA). Reading it BY NAME, as
        // this arm did, refuses what WI-782 REQUIRES: `foldLeft(f: (acc: Acc, x: Element) ->
        // Acc)` given an operation's eta arrow `(_1: Int64, _2: Int64) -> Int64` is `expected
        // (acc: ?Acc, x: Element), got (_1: Int64, _2: Int64)` — the 38 rows WI-1084 measured
        // and the reason it could σ-resolve only the RESULT. MEASURED AGAIN HERE, with only
        // this arm reverted: 35 rows over 17 tickets, the stdlib combinators among them.
        //
        // AND σ-RESOLVED, WI-1084's step for the result taken here at last: the groundness
        // gate is what defers a genuinely polymorphic component to dispatch, and it was
        // reading the component AS WRITTEN, so a variable the argument-unify loop had already
        // pinned still read as non-ground and the comparison was skipped. WI-836's correction
        // one level down — pair the predicate with a resolution of matching depth. It is what
        // makes this check reachable at all for an ordinary higher-order call, and what
        // closes the PARAM twin of the result hole WI-1084 closed (`wi836…::two_callback_-
        // arguments_sharing_a_type_var_must_agree`, the gap WI-836 pinned).
        Some(arity) => {
            let d_param_r = walk_type_deep_value(kb, subst, &d_param);
            let a_param_r = walk_type_deep_value(kb, subst, &a_param);
            if resolved_type_is_ground(kb, &d_param_r)
                && resolved_type_is_ground(kb, &a_param_r)
                && !arrow_params_compatible(kb, subst, &d_param_r, &a_param_r, arity)
            {
                return Some(mismatch(kb, subst));
            }
            // WI-RKMD4 — THE SAME HOLE, ONE COORDINATE OVER. The groundness gate above is
            // WI-385's, and it skips a callback parameter still carrying a variable for the
            // same reason [`validate_arg_against_param`]'s did — right about the variable's
            // SLOT, wrong about the constructor it hangs off. MEASURED, both directions:
            // `run(f: (m: Message[Trust = Untrusted]) -> Int64)` given a `cb(t: Text[Trust =
            // ?t])`, and the mirror with the variable on the DECLARED side, both loaded
            // clean while the all-ground pair beside them was refused.
            //
            // OPERANDS SWAPPED, because the parameter position is CONTRAVARIANT: the
            // obligation is `d_param <: a_param`, so `d_param` is the subtype-candidate
            // and goes in the `actual` slot. The swap is how this caller reaches the
            // convention every caller of [`nominal_head_mismatch`] uses, rather than a
            // second reading of the same predicate. At arity ≠ 1 the slot is a parameter
            // LIST (WI-782), which is a `named_tuple` and therefore not a nominal head on
            // either side, so this arm decides only the arity-1 pair — a lone parameter's
            // own type.
            //
            // THE SENTENCE THAT STOOD HERE IS VOID, and /code-review found it: "a callable
            // component needs no guard at this call: the predicate withholds at a callable
            // HEAD itself". WI-20260904-50B2K's fourth edit put
            // [`callable_against_callable_free`] ABOVE that withholding, so a callable
            // component now reaches a DIRECTED verdict here. It is asked in the sound
            // direction — the swap above means the question is "is a function admissible
            // where `a_param` is expected", which has no coercion when `a_param` carries
            // no callable — and the reverse pairing, the one with the eta-lift and the
            // zero-arg thunk (`wi_cbrsw_permission_effect_test::a_denial_of_a_sub_capability_
            // does_not_forbid_the_super_capability`), is excluded by that predicate's own
            // first conjunct. MEASURED: with the verdict computed beside this call and
            // reported, it fires ZERO times across the WHOLE `wi_tests` binary (4121 rows,
            // 0 failed) while the SAME probe at the per-binding descent fires ONCE — a
            // positive control, so the zero is a reach that is unwitnessed rather than a
            // probe that cannot fire. The probe APPENDS to a file rather than printing:
            // `O_APPEND` is atomic for a short write, so a marker cannot be torn by the
            // default test parallelism, which is what an `eprintln!` version would risk on
            // a control that fires exactly once. A lower bound, not a proof: the corpus is
            // not the population.
            if nominal_head_mismatch(kb, subst, &d_param_r, &a_param_r, HeadPosition::Nested) {
                return Some(mismatch(kb, subst));
            }
        }
        // EVERY MIXED PAIRING — all three of `Function`/`Function`, `Function` slot given an
        // arrow, and an ARROW SLOT GIVEN A `Function`. BY NAME, on the component AS WRITTEN,
        // and both halves are unchanged from WI-775/WI-1084 deliberately — except that
        // WI-1088 additionally requires the `Function`/`Function` pairing's two `A`s to agree
        // on ORDER, which by-name alone does not (see the arm's own comment below).
        //
        // So YES, an arrow slot's parameter LIST is compared by name here — that is not the
        // arm above leaking, it is the only relation available when the other side has no
        // list to zip against. A `Function[A = …]`'s `A` is the ARGUMENT's data type (what
        // flows to `apply(f, x: A)`); zipping a parameter list onto it is the WI-775 bridge
        // whichever side the list is on. The ground-path twin is
        // [`arrow_function_compatible`], which applies this same relation to this same pair
        // and carries the measurement. `wi1085…::a_function_typed_argument_at_an_arrow_slot_-
        // is_refused_whatever_the_labels` drives the arrow-slot direction.
        //
        // AND σ-RESOLVED SINCE WI-1087, which is the change that ticket's decision made SAFE
        // rather than merely consistent. WI-1085 left this operand AS WRITTEN and recorded
        // why: resolving it extended WI-775's by-name refusal to a pairing only a VARIABLE
        // `A` can present — `apT[T](f: Function[A = T, B = Int64], t: T)` given a
        // 2-parameter operation, where `T` is pinned by the SIBLING argument `t` — costing
        // SIX rows, every one a program that evaluates (all four of
        // `wi787_eta_spread_named_tuple_test`, `wi1085…::a_function_slot_still_spreads_an_-
        // operation_across_its_components`, and WI-1083's headline
        // `a_requires_carrying_member_runs_as_a_function_value`). Those six are exactly the
        // SPREAD reading, which the relation above now applies positionally instead of
        // refusing, so σ-resolution no longer costs them — it is what lets the σ-pinned `A`
        // reach the same verdict as the written-out one, which is what WI-1087 was filed
        // about. The two spellings now agree instead of one of them being invisible.
        None => {
            let d_param_r = walk_type_deep_value(kb, subst, &d_param);
            let a_param_r = walk_type_deep_value(kb, subst, &a_param);
            if resolved_type_is_ground(kb, &d_param_r) && resolved_type_is_ground(kb, &a_param_r) {
                // The SAME predicate the ground path consults, so the two cannot drift into
                // reading `A` differently — the drift WI-1087 exists to close.
                //
                // ONE DIRECTION ONLY: the `Function` is the DECLARED SLOT and the arrow is
                // the VALUE. The pairing is not symmetric, and giving the mirror this
                // relation is a soundness hole rather than a tidiness question. A
                // `Function[A]` SLOT admits arity 1 OR `|A|` (WI-801) and the arrow VALUE
                // states which of the two it is, so the slot's obligation is discharged. An
                // ARROW SLOT states a hard arity `n` and will apply its value with exactly
                // `n` arguments, while a `Function`-typed VALUE states no arity at all —
                // matching `n` against `|A|` proves nothing about the callable inside, which
                // may equally be the whole-`A` reading. MEASURED (review), loading clean and
                // trapping `ArityMismatch { expected: 1, got: 2 }` at eval when this arm was
                // symmetric: `pass(f: Function[A = (Int64, Int64), …]) = take(f, 1)` with
                // `take[Acc](g: (p: Acc, q: Int64) -> Int64, …)`, given a ONE-parameter
                // `whole(t: (Int64, Int64))`. That is the load-clean-then-trap class
                // WI-782/791/792/801 exist to remove.
                //
                // So the mirror keeps the by-name reading WI-1085 left it with.
                //
                // WI-1088 CORRECTED THE OTHER HALF OF THAT SENTENCE. `Function`/`Function`
                // used to be listed here as taking the by-name reading for the same reason —
                // "neither side states an arity, so both `A`s are read as the data types they
                // are". The premise is right and the conclusion did not follow: neither side
                // stating an arity means BOTH readings stay open, not that the data one wins,
                // and a value's spread mapping is pinned at its MINT. So that pairing owes the
                // INTERSECTION of the two readings, which on the order axis is
                // order-preserving — see [`function_pairing_permutes_a`], which the arm below
                // asks and which the ground route asks at
                // [`parameterized_compatible_view`].
                let list_arity = match (d_arity, a_arity) {
                    (None, Some(n)) => {
                        function_slot_reads_a_as_param_list(kb, &d_param_r, n).then_some(n)
                    }
                    _ => None,
                };
                let ok = match list_arity {
                    Some(n) => arrow_params_compatible(kb, subst, &d_param_r, &a_param_r, n),
                    // WI-1088: the `Function`/`Function` half of this arm, through the SAME
                    // predicate the ground path consults — the two must not come to hold
                    // different opinions about one pairing, which is the drift WI-1087 closed
                    // for the spread reading and this closes for the order axis.
                    // Asked FIRST, and it costs nothing when it does not apply: it returns on
                    // the two arities before reading either type. The operands are already
                    // σ-walked here; the predicate walks its own, which is an identity on
                    // these and is what lets the OTHER call site hand it raw bindings.
                    None => {
                        !function_pairing_permutes_a(
                            kb, subst, d_arity, a_arity, &d_param_r, &a_param_r,
                        ) && types_compatible(kb, subst, &d_param_r, &a_param_r)
                    }
                };
                if !ok {
                    return Some(mismatch(kb, subst));
                }
            }
        }
    }
    // WI-1084 — RESOLVE THE RESULT THROUGH σ BEFORE ASKING WHETHER IT IS GROUND, for the
    // reason the arrow arm above now shares: the gate was reading the component AS WRITTEN,
    // so a variable the argument-unify loop had already pinned still read as non-ground and
    // the comparison was skipped. The first of the two levels WI-1084 needed was that
    // unification had no arm to make the binding with at all (see
    // [`unify_arrow_function_view`]).
    //
    // WHAT THIS DOES NOT DO is re-open the WI-836 carve-out one frame up. That one withholds
    // the WHOLE-TYPE `types_compatible` for a callable, because it would refuse the WI-775
    // pairing (a `Function[A = (a, b)]` slot admitting a 2-parameter eta arrow). Here the
    // relation stays component-wise and only the operand of the groundness test moves. A
    // component that σ leaves non-ground is deferred exactly as before.
    let d_result_r = walk_type_deep_value(kb, subst, &d_result);
    let a_result_r = walk_type_deep_value(kb, subst, &a_result);
    // Covariant result: `actual.result <: declared.result`.
    if resolved_type_is_ground(kb, &d_result_r)
        && resolved_type_is_ground(kb, &a_result_r)
        && !types_compatible(kb, subst, &a_result_r, &d_result_r)
    {
        return Some(mismatch(kb, subst));
    }
    None
}

/// WI-408: the synthesized `some(value)` constructor occurrence around a
/// coerced argument / field node. `declared` (the resolved `Option[T]`) is
/// stamped as the wrapper's inferred type here — the `Stamp` frame only
/// stamps the enclosing node's own result, never an inserted child.
fn synthesize_some_wrap(
    kb: &mut KnowledgeBase,
    child: &Rc<NodeOccurrence>,
    declared: &Value,
) -> Rc<NodeOccurrence> {
    let some_sym = kb.resolve_symbol("anthill.prelude.Option.some");
    let value_sym = kb.intern("value");
    let pass = crate::kb::simp_rewrite::simp_pass(kb);
    // Named form `some(value: child)` — the canonical `some` shape (the
    // loader canonicalizes source-written positional `some(x)` to it too).
    let node = NodeOccurrence::synthesized_expr(
        Expr::Constructor {
            name: some_sym,
            pos_args: Vec::new(),
            named_args: vec![(value_sym, Rc::clone(child))],
            from_projection: false,
        },
        Rc::clone(child),
        pass,
        child.owner,
    );
    node.set_inferred_type(declared.clone());
    node
}

/// A synthesized named-tuple LITERAL occurrence, type already stamped.
///
/// ONE owner for a shape with a load-bearing and non-obvious representation: the
/// surface form of `(a: 1, b: 2)` is an `Expr::Constructor` over
/// `anthill.reflect.TupleLiteral` whose elements ALL ride in `named_args`
/// (parse/convert.rs relabels positional ones `_1`, `_2`, …). It is NOT
/// `Expr::TupleLit`, which is a non-surface IR shape eval refuses outright, and
/// NOT an `Expr::Apply`, which eval would dispatch as an operation call
/// (`UnknownOperation`). Eval routes the constructor through `start_constructor`
/// to a `Value::Tuple`, and `classify_ctor_arg` hoists an `_N`-at-index-N run
/// back into `Value::Tuple.pos` — so ONE construction serves both the positional
/// and the named spelling, provided the labels are the type's own.
///
/// Callers: WI-727's variadic capture record and WI-801's spread-call
/// normalization. Both previously restated the routing invariant above in their
/// own words, which is two owners for one fact about eval.
pub(super) fn synthesize_named_tuple_literal(
    kb: &mut KnowledgeBase,
    from: &Rc<NodeOccurrence>,
    named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
    ty: Value,
) -> Rc<NodeOccurrence> {
    let pass = crate::kb::simp_rewrite::simp_pass(kb);
    let functor = kb.resolve_symbol(dt::qualified(dt::TUPLE_LITERAL));
    let occ = NodeOccurrence::synthesized_expr(
        Expr::Constructor {
            name: functor,
            pos_args: Vec::new(),
            named_args,
            from_projection: false,
        },
        Rc::clone(from),
        pass,
        from.owner,
    );
    occ.set_inferred_type(ty);
    occ
}

/// WI-408: rebuild `occ` with `some(...)` wrappers around the flagged
/// children. `wraps` carries `(child-index, declared-Option-type)` pairs —
/// indices in reassembly order (positional args, then named args); every
/// other slot takes the child's TYPED result node (itself possibly
/// rewritten). The rebuilt node starts with fresh annotation cells, so the
/// caller must rebuild BEFORE writing `classification` /
/// the typer's stamps onto the apply/constructor occurrence.
pub(super) fn wrap_some_children(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    wraps: &[(usize, Value)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> Rc<NodeOccurrence> {
    let children = some_wrapped_children(kb, wraps, pos_results, named_results);
    crate::kb::simp_rewrite::reassemble(occ, &children)
}

/// The typed argument OCCURRENCES of one application, in reassembly order
/// (positional then named), with the WI-408 some-coercions materialized.
///
/// Shared by the two rewrites that need it — [`wrap_some_children`], which then
/// reassembles the call in place, and [`gather_spread_args_into_tuple`], which
/// folds them into one tuple. The `wraps` indices are into THIS order, so the
/// wrapping must happen here rather than at either caller: a coerced argument has
/// to become `some(v)` BEFORE it becomes a tuple component, or the wrapper lands
/// on the wrong node.
///
/// `check_apply_iter` bailed on any ill-typed child up front
/// (`collect_arg_errors`), which is what makes the `Ok`-child expectation hold.
fn some_wrapped_children(
    kb: &mut KnowledgeBase,
    wraps: &[(usize, Value)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> Vec<Rc<NodeOccurrence>> {
    let mut children: Vec<Rc<NodeOccurrence>> = pos_results
        .iter()
        .chain(named_results.iter())
        .map(|r| Rc::clone(&r.as_ref().expect("some_wrapped_children: Ok child").node))
        .collect();
    for (idx, declared) in wraps {
        children[*idx] = synthesize_some_wrap(kb, &children[*idx], declared);
    }
    children
}

/// WI-801: rewrite `f(v₁, …, vₙ)` at a `Function[A, B, E]` slot into `f((l₁: v₁,
/// …, lₙ: vₙ))`, where `l₁…lₙ` are `A`'s component labels — the ONE place the
/// spread-vs-whole decision is made, and the only place it CAN be made.
///
/// Eval pivots on the callee's own arity and the typer on `A`'s component count
/// (WI-801). Rather than teach eval the typer's quantity — it cannot be told: a
/// gather needs `A`'s LABELS and those are erased at runtime — this removes the
/// disagreement by handing eval a call whose shape is right for BOTH admitted
/// arities. A 1-parameter callee gets `A` itself; an `|A|`-parameter one meets
/// eval's long-standing spread adapters, which take a single tuple argument and
/// were already the tested path (`spread_eta_args` for an operation,
/// `match_tuple_pattern` for a lambda's binder list).
///
/// The labels come from `A` and are used AS-IS, which is what makes one
/// construction serve both tuple spellings: `extract_type` yields `_1`/`_2` for a
/// POSITIONAL `A` and the written labels for a NAMED one, and `classify_ctor_arg`
/// (eval/eval.rs) hoists exactly the `_N`-at-index-N run back into `Value::Tuple.
/// pos`. So the positional case rebuilds a positional tuple and the named case a
/// named one, without this site branching on which it has — the same
/// correspondence `convert.rs`' own `TupleLiteral` build relies on.
///
/// `named_args` is necessarily EMPTY here, not merely assumed: the `Function` arm
/// of [`positional_arg_expectations`] states no verdict unless every argument is
/// positional, so `gather` is `None` for any call carrying a label — which the
/// caller has already rejected, a `Function` having no binder names to bind one to.
///
/// `None` only for a non-`Apply` occurrence, which the caller reports loudly.
pub(super) fn gather_spread_args_into_tuple(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    a_type: Value,
    labels: &[Symbol],
    wraps: &[(usize, Value)],
    pos_results: &[Result<TypeResult, TypeError>],
) -> Option<Rc<NodeOccurrence>> {
    // WI-20260829-W6JH0: carried for the reason `reorder_named_args_in_apply` records.
    // This one runs AFTER the read, so it only corrupted the STORED node — still a
    // divergence between what was typed and what is kept.
    let Some(Expr::Apply {
        functor,
        type_args,
        recv_type,
        ..
    }) = occ.as_expr()
    else {
        return None;
    };
    let (functor, type_args) = (*functor, type_args.clone());
    let children = some_wrapped_children(kb, wraps, pos_results, &[]);
    // A HARD guard, not a `debug_assert`. The counts agree by construction — both
    // descend from the `positional` the `Function` arm of
    // [`positional_arg_expectations`] matched `A`'s component count against — so
    // this cannot fire today. But the pairing below is a `zip`, which TRUNCATES to
    // the shorter side: were the invariant ever broken, a debug-only assert
    // compiles out and the gather silently builds a tuple with components MISSING,
    // which is the "reads as handled when it isn't" failure the repo's
    // loud-error rule targets. The caller renders this `None` loudly.
    if children.len() != labels.len() {
        return None;
    }
    let tuple_node = synthesize_named_tuple_literal(
        kb,
        occ,
        labels.iter().copied().zip(children).collect(),
        a_type,
    );
    let pass = crate::kb::simp_rewrite::simp_pass(kb);
    Some(NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: recv_type.clone(),
            functor,
            pos_args: vec![tuple_node],
            named_args: Vec::new(),
            type_args,
        },
        Rc::clone(occ),
        pass,
        occ.owner,
    ))
}

/// WI-426 / WI-783 / WI-1100 — WHICH declared slot each argument of a call fills.
/// The one binder: a positional argument fills slot `i`, a label fills the slot it
/// names, and no slot may be filled twice. Everything a caller can ask about a call's
/// SHAPE is read off this — the label diagnostics (`label_errors`) and the arity ones
/// ([`call_arity_error`]) alike — so the two cannot answer from different pairings.
pub(super) struct ArgumentBinding {
    /// One [`TypeError`] per offending LABEL: one that names no parameter, and one that
    /// binds a parameter a positional argument (or an earlier label) already filled.
    /// Empty = every label resolved to a distinct free slot.
    pub(super) label_errors: Vec<TypeError>,
    /// The declared parameters this call filled with nothing, in declaration order.
    /// Carried as the NAMES rather than as a count: with labels in play a call can
    /// supply the right number of arguments and still leave a slot empty, and which
    /// one it is is the whole of what the author has to fix.
    unfilled: Vec<Symbol>,
    /// Positional arguments past the end of the declared list — each occupies no slot
    /// at all. Counted rather than flagged so the diagnostic can state the count given.
    surplus_positional: usize,
    /// Whether the call wrote ANY named argument. Read only by
    /// [`relational_result_column`], which §5.3 restricts to the all-positional
    /// spelling — see there.
    has_named_args: bool,
}

/// WI-20260827-1F0QP: the PARAMETER each POSITIONAL argument of a call binds — one
/// owner, read by every site that used to write `params.get(i)`.
///
/// Entry `i` is the parameter index positional argument `i` fills, or `None` when it
/// fills none (a surplus argument, including a relational goal's RESULT column). With
/// named arguments in play that is NOT `i`: they rank among the parameters the labels
/// have not already taken ([`KnowledgeBase::rank_positional_among_unnamed`]), the same
/// rule a constructor's arguments follow (kernel §6.3).
///
/// The no-labels case returns the identity, so every call written without a label — all
/// but a handful in the tree — takes exactly the mapping it always had, and this
/// function is the only place the two cases are told apart.
///
/// EVERY reader must use this, not just the one that binds. The type checker validates
/// argument `i` against parameter `i`, the inference loop unifies against parameter `i`,
/// and the function-value path indexes its slot list by `i`: with the rank rule live and
/// those three left alone, a mixed call would be CHECKED against one parameter and BOUND
/// to another — a silent wrong-type delivery, which is worse than the load error the
/// rank rule replaced. Review-found, after exactly that shipped in a first draft.
pub(super) fn positional_param_indices(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    pos_count: usize,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> SmallVec<[Option<usize>; 4]> {
    if named_args.is_empty() {
        return (0..pos_count)
            .map(|i| (i < params.len()).then_some(i))
            .collect();
    }
    let decl: SmallVec<[Symbol; 4]> = params.iter().map(|(s, _)| *s).collect();
    let assigned = match KnowledgeBase::rank_positional_among_unnamed(
        &decl,
        |p| named_args.iter().any(|(l, _)| same_label(kb, p, *l)),
        pos_count,
    ) {
        PositionalPlan::Assign(f) => f,
        // Over-applied: more positional arguments than parameters the labels left open.
        // Which of them is surplus is not a question with an answer, so NONE of them is
        // matched to a parameter and `call_arity_error` reports the count. The old
        // slot mapping matched the leading ones and reported the rest, which is how a
        // relational RESULT column used to be found — see [`relational_result_column`],
        // which now asks the question directly instead of inferring it from a surplus.
        PositionalPlan::OverArity { .. } => return (0..pos_count).map(|_| None).collect(),
        PositionalPlan::Skip => {
            unreachable!("rank_positional_among_unnamed returned Skip for a call's arguments")
        }
    };
    (0..pos_count)
        .map(|i| {
            assigned
                .get(i)
                .and_then(|f| params.iter().position(|(s, _)| *s == *f))
        })
        .collect()
}

/// WI-426 / WI-783: named-argument COVERAGE against a callee's parameter list —
/// every label must name a DISTINCT parameter that no positional argument has
/// already filled. Yields one [`TypeError`] per offending label; empty = clean.
///
/// This is a PRECONDITION of [`reorder_named_args_in_apply`], not a courtesy
/// check: that reorder sorts an UNMATCHED label last, and eval binds what it is
/// handed positionally (`start_apply` having discarded the labels), so a typo'd
/// or duplicated label would otherwise slide into whichever slot was left over
/// and bind a parameter the caller never named.
///
/// Shared by both callee kinds so their diagnostics cannot drift apart — a named
/// operation (`op.params`) and a function VALUE whose arrow type declares binder
/// names ([`arrow_declared_param_list`]) — with `subject` naming the kind in the
/// message. `#[track_caller]` so `site` still records the CALLING path rather than
/// this one shared body.
///
/// WI-1100: it also REPORTS THE COVERAGE it was already computing. Until then the
/// `covered` vector was built, read for the duplicate-label test, and dropped — and
/// the doc here said missing parameters are "deliberately NOT checked: partial
/// application is legal (WI-374)". That citation was to the wrong ticket and the wrong
/// language rule: WI-374 is the *type*-application expansion (a parametric sort left
/// partly unwritten), and the kernel spec has always said the opposite about VALUE
/// arguments — "the argument count must equal the declared arity"
/// (§"Applying a function value checks its arguments", stated of a named operation as
/// the thing an arrow application is checked *like*). No under-applied call produces a
/// function value anywhere in this language; it produced an `EvalError::ArityMismatch`
/// on whichever execution first reached it, which is the deferral WI-1100 removed.
#[track_caller]
pub(super) fn bind_call_arguments(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    pos_count: usize,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    callee: Symbol,
    subject: &str,
    span: Option<Span>,
) -> ArgumentBinding {
    let positional_filled = pos_count.min(params.len());
    // Most calls pass no labels at all; keep the common path allocation-free
    // (the pre-WI-783 inline version was guarded by the same emptiness test).
    // `unfilled` allocates only for a call that is already wrong.
    if named_args.is_empty() {
        return ArgumentBinding {
            label_errors: Vec::new(),
            unfilled: params[positional_filled..]
                .iter()
                .map(|(s, _)| *s)
                .collect(),
            surplus_positional: pos_count - positional_filled,
            has_named_args: false,
        };
    }
    let site = std::panic::Location::caller();
    // WI-20260827-1F0QP: a MIXED call ranks its positional arguments among the
    // parameters NOT already given by name — ONE rule with the constructor spelling
    // (§6.3), through the same owner. Marking the first `pos_count` parameters filled
    // and then reading the labels made `add2(2, a: 1)` a load error ("named argument
    // 'a' binds a parameter already given") while the constructor `two(2, a: 1)` was
    // legal, so an author had two models to learn for one shape.
    //
    // `same_label` is the comparator, not `Symbol` equality, which is why this calls
    // the list-taking [`KnowledgeBase::rank_positional_among_unnamed`] rather than
    // `positional_to_named_plan`: a call-site label and the declared parameter need
    // not be the same `Symbol` (`same_label` is the tree's existing rule here).
    // WI-20260827-1F0QP: through [`positional_param_indices`], the one owner — so which
    // parameter this check calls FILLED and which one the type checker validates against
    // and the runtime binds cannot disagree. Marking the first `pos_count` parameters
    // filled and then reading the labels made `add2(2, a: 1)` a load error ("named
    // argument 'a' binds a parameter already given") while the constructor `two(2, a: 1)`
    // was legal, so an author had two models to learn for one shape.
    let pos_params = positional_param_indices(kb, params, pos_count, named_args);
    let mut covered = vec![false; params.len()];
    // How many positional arguments actually LAND, once the named ones have taken their
    // parameters — the named-arg twin of `positional_filled` above, which counted against
    // the whole parameter list and so under-reported the surplus of a mixed over-applied
    // call (`add2(2, 3, a: 1)` has one surplus argument, not none).
    let positional_filled = pos_params.iter().filter(|p| p.is_some()).count();
    for idx in pos_params.iter().flatten() {
        covered[*idx] = true;
    }
    let mut label_errors = Vec::new();
    for (arg_name, _) in named_args.iter() {
        let reason = match params
            .iter()
            .position(|(s, _)| same_label(kb, *s, *arg_name))
        {
            None => Some(format!("names no parameter of {subject}")),
            Some(idx) if covered[idx] => Some("binds a parameter already given".to_string()),
            Some(idx) => {
                covered[idx] = true;
                None
            }
        };
        if let Some(reason) = reason {
            label_errors.push(TypeError::Other {
                site,
                span,
                context: TypeErrorContext::OperationArgument {
                    op_name: callee,
                    param: *arg_name,
                },
                expected: "a named argument matching a distinct unbound parameter".to_string(),
                actual: format!(
                    "named argument '{}' {}",
                    short_name_of(kb.local_name_of(*arg_name)),
                    reason
                ),
            });
        }
    }
    ArgumentBinding {
        unfilled: params
            .iter()
            .zip(&covered)
            .filter(|(_, filled)| !**filled)
            .map(|((s, _), _)| *s)
            .collect(),
        label_errors,
        surplus_positional: pos_count - positional_filled,
        has_named_args: true,
    }
}

/// WI-1104 — is this call the FUNCTIONAL-RELATION form, and if so WHICH positional
/// argument is its result column?
///
/// `Some(i)`: the call is a rule-body GOAL written at the operation's arity + 1
/// (kernel §5.3, WI-938) — `vec_add(a, b, ?c)` resolves as `unify(vec_add(a, b), ?c)` —
/// and `i` indexes the extra column, the one receiving the RESULT. `None`: an ordinary
/// call, whose every argument fills a declared slot.
///
/// ONE OWNER, TWO READERS, and that is the point of naming it. [`call_arity_error`] reads
/// it to ADMIT the extra column; [`check_apply_iter`] reads it to TYPE-CHECK that column
/// against the callee's declared return. Before WI-1104 only the first reading existed and
/// the column was never checked at all — the positional validation loop reads
/// `written_params.get(i)`, so an argument past the declared list was skipped, and nothing
/// downstream picked it up either: the goal's shape is decided at resolution
/// (`functional_relation_arity` / `dispatched_relation_arity`, kb/resolve.rs) where the
/// declared return is not consulted. `Desc.describe(leaf(), "not an int")` against
/// `-> Int64` loaded clean and answered nothing.
///
/// The three conditions, each load-bearing:
///   * [`NodePos::RuleBodyGoal`] — a VALUE-position call has no relational reading at all
///     (that was WI-1104's headline defect; see [`call_arity_error`]);
///   * `unfilled.is_empty()` — every declared slot is filled, so the surplus is genuinely
///     EXTRA rather than an argument that landed in the wrong place;
///   * `surplus_positional == 1` — EXACTLY one column over, so "in a rule body anything
///     goes" is not what was traded for the relational view. No label can be the surplus:
///     a label fills a slot, so a surplus is positional by construction, which is what
///     makes `params.len()` the column's index.
pub(super) fn relational_result_column(
    params: &[(Symbol, Value)],
    binding: &ArgumentBinding,
    pos: NodePos,
) -> Option<usize> {
    // WI-20260827-1F0QP added the `has_named_args` clause, and it is the SPEC's own
    // condition rather than a guard bolted on: §5.3 says of the functional-relation view
    // that "named arguments are not this shape: the result column is positional and
    // last". It was implied before only because a labelled call could not reach here —
    // a label over a positionally-filled parameter was a coverage error. With the rank
    // rule live it can: `Desc.describe(x: leaf(), ?r)` fills every parameter by name and
    // leaves one positional over, which is `unfilled` empty and `surplus_positional == 1`
    // exactly like the relational spelling. Without this clause that answered
    // `Some(params.len())` and the caller indexed `pos_results` out of bounds — a PANIC
    // on an ordinary load, review-found. Now it is the ordinary over-arity call it is,
    // and `call_arity_error` names the count.
    (pos == NodePos::RuleBodyGoal
        && !binding.has_named_args
        && binding.unfilled.is_empty()
        && binding.surplus_positional == 1)
        .then_some(params.len())
}

/// WI-1104 — the verdict on a relational goal's RESULT column
/// ([`relational_result_column`]): does the value written there fit what the operation
/// RETURNS?
///
/// Judged by the check an ARGUMENT gets ([`validate_arg_against_param`]) — the same
/// groundness gate (an unbound `?r`, the overwhelmingly common spelling, is non-ground
/// and left to resolution) and the same reflect-`Term` and provider-carrier tolerances —
/// but run in BOTH DIRECTIONS, which is where a column stops being an argument. The
/// context is [`TypeErrorContext::OperationReturn`], so the diagnostic reads `<op>.return`
/// rather than naming a parameter the column does not fill.
///
/// **WHY BOTH.** An argument flows IN, so `actual <: declared` is the whole question. A
/// result column is a UNIFICATION TARGET: the resolver binds the returned value into it
/// and coerces nothing, so the pair must be able to hold the same values, and subtyping
/// in EITHER direction alone admits a column that can never unify. Review-found, and the
/// two halves are exact mirrors — with a `-> (a: Int64, b: Int64)` return:
///
/// ```text
/// mk(v: 0).pair((a: 1, b: 2, c: 3))     -- column WIDER  than the return
/// mk(v: 0).triple((a: 1, b: 2))         -- column NARROWER (against `-> (a, b, c)`)
/// ```
///
/// Neither can ever unify. Under the argument direction alone the narrow one is refused
/// (a value with fewer fields does not fit a wider slot) and the wide one LOADS CLEAN,
/// because a named tuple with MORE fields is a subtype of one with fewer — the exact
/// "dead goal indistinguishable from one with no solutions" this check exists to remove,
/// admitted by the check itself. Requiring both directions refuses both, and leaves every
/// pair that could unify alone: for a scalar pair the two directions coincide, so the 78
/// decidable sites the suite drives are untouched (measured — one revert, one run).
///
/// The REVERSE direction runs on a CLONE of σ. `validate_arg_against_param` may bind
/// through `types_compatible`, and the reversed pair is asked as a QUESTION about this
/// call, not as part of its inference — the forward direction is the one whose bindings
/// this call is entitled to keep.
///
/// WHERE IT FIRES, MEASURED at this site rather than assumed. **Zero** times over an
/// `anthill load` of all thirteen `.anthill` projects in the repo — no shipped program
/// writes a relational goal on a callee this check can see, because the spelling needs a
/// callee with a SIGNATURE at the goal, which today means a spec op or a dot
/// ([`call_dispatch_shape`] rung 2); a plain operation named as a goal is a
/// `CallDispatch::Subgoal` and never reaches `check_apply_iter`. **93** times over the
/// `wi_tests` binary, **85 of them decidable** (both sides ground, so the check fires
/// rather than deferring), across 47 callees — the stdlib's own `Numeric.add` (22),
/// `Numeric.mul` and `PartialOrd.gt` among them. The corpus zero is not coverage
/// (WI-1034/WI-1063); the 85 are, and they are what a wrong check here would refuse.
///
/// **THE ONE PLACE IT DIVERGES from an argument: `WrapSome` is REFUSED, not applied.**
/// The WI-408 some-coercion repairs a bare `T` in an `Option[T]` slot by wrapping the
/// argument occurrence — a REWRITE. Here the goal is `unify(f(a…), col)` and the resolver
/// coerces nothing, so wrapping would change what the rule MEANS while making the load
/// look clean (WI-1058's third reason for not rewriting a rule body). Left un-wrapped and
/// un-reported it is a goal that can never unify, which is the defect this closes. So it
/// is reported, with the declared `Option[T]` as the expected type.
pub(super) fn result_column_error(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    column_type: &Value,
    declared_return: &Value,
    callee: Symbol,
    span: Option<Span>,
) -> Option<TypeError> {
    let context = TypeErrorContext::OperationReturn {
        op_name: callee,
        surface: None,
    };
    // The natural orientation first: its `Fail` already renders "expected <return>, got
    // <column>", which is what the author needs to read.
    match validate_arg_against_param(
        kb,
        subst,
        column_type,
        declared_return,
        span,
        context.clone(),
        // A RESULT COLUMN is a goal's argument place, not an expression: there is no
        // occurrence here whose denotation a message could name.
        None,
    ) {
        ArgValidation::Fail(err) => return Some(err),
        ArgValidation::WrapSome { declared } => {
            return Some(TypeError::TypeMismatch {
                site: TypeError::here(),
                span,
                context,
                expected: declared,
                denoted: None,
                actual: column_type.clone(),
            })
        }
        ArgValidation::Ok => {}
    }
    // …then the reverse (see this function's doc). Its own `Fail` message would read
    // backwards — "expected <column>, got <return>" — so only its VERDICT is taken and
    // the mismatch is stated in the reader's orientation.
    let mut probe = subst.clone();
    match validate_arg_against_param(
        kb,
        &mut probe,
        declared_return,
        column_type,
        span,
        context,
        None,
    ) {
        ArgValidation::Ok => None,
        ArgValidation::Fail(_) | ArgValidation::WrapSome { .. } => Some(TypeError::TypeMismatch {
            site: TypeError::here(),
            span,
            context: TypeErrorContext::OperationReturn {
                op_name: callee,
                surface: None,
            },
            expected: declared_return.clone(),
            denoted: None,
            actual: column_type.clone(),
        }),
    }
}

/// WI-1100 — the ARITY verdict on a call to a named operation: every declared slot is
/// filled exactly once, and no argument occupies a slot that does not exist. Read off
/// [`bind_call_arguments`]'s binding rather than re-derived, so "which slot does this
/// argument fill" is answered ONCE for a call. A bare count comparison would not do:
/// with labels in play a call can supply the right NUMBER of arguments and still leave a
/// slot empty (`pair(a: 1, bogus: 2)`), and only the binder knows which.
///
/// THE DEFECT IT CLOSES: nothing compared a call's argument count against the callee's
/// declaration. The positional loop reads `written_params.get(i)`, so a SURPLUS argument
/// simply matched no parameter and was skipped; a MISSING one left a parameter with
/// nothing to check against. Measured on the built CLI: `concat("a", "b", "c", "d")` on
/// the binary `String.concat` answered `loaded: 2602 facts, 176 rules` and `128 pass, 0
/// failed`, with the error deferred to `EvalError::ArityMismatch` on whichever execution
/// first reached the expression — and on the RESOLUTION path deferred to nothing at all,
/// the goal answering `no solutions` indistinguishably from one that legitimately has
/// none. What surfaced it: WI-1097's duplicate-id refusal built its message with a
/// four-argument `concat`, so the error path of an error-detection gate was itself broken
/// and the whole suite stayed green, because no test drove a store with a collision.
///
/// **BOTH NUMBERS ARE IN THE SOURCE'S CURRENCY** — what the author wrote, not what the
/// typer holds. `supplied` is counted at the call site BEFORE the WI-727 capture rewrite
/// appends its synthesized record (see the caller), and `capture_param` is subtracted
/// from the declared side and described instead: a `...args` slot is not an argument any
/// caller writes, so reporting it on either side states a count the source cannot have.
///
/// **THE RULE-BODY TOLERANCE, and why it is a reading rather than a hole.** A rule body's
/// goal may be written at the operation's arity + 1: that is the FUNCTIONAL-RELATION view
/// (kernel §5.3, WI-938) — `vec_add(a, b, ?c)` resolves as `unify(vec_add(a, b), ?c)`,
/// with the last column receiving the result — and it is the shape the WI-1043 rule-body
/// spec-op dispatch is written in (`rule answer(?r) :- Desc.describe(leaf(), ?r)`, where
/// `describe` takes one parameter). Those atoms reach this check through
/// [`dispatch_calls_in_occ`], so refusing arity + 1 there would refuse a delivered
/// language feature — 17 tests across five files, measured.
///
/// **WI-1104 SCOPED IT TO THE POSITION IT WAS ALWAYS ABOUT.** Until then the tolerance
/// was gated on `TypingEnv::rule_body_dispatch`, a PER-RULE flag, while GOAL-vs-VALUE is
/// [`BodyPos`] — so a VALUE-position rule-body call over-applied by exactly one was
/// admitted too, and MEASURED:
///
/// ```text
/// rule r(?y) :- leaf().describe(?d), ?y = concat("a", "b", "c")   -- loaded clean
/// ```
///
/// One program, two verdicts, decided by where it was written: an operation body carrying
/// the same expression was refused. The gate is now [`NodePos`], which rides the typer's
/// work-stack frame and so answers per NODE — see [`relational_result_column`], the one
/// owner of "is this the functional-relation form", read both here and by the RESULT-
/// COLUMN check the same tolerance now carries.
///
/// WHAT THE NARROWING COSTS, measured at this site over an `anthill load` of the repo's
/// thirteen projects: on stdlib + host bindings, 84 calls reach here from inside a rule
/// body — **44 at a goal, 40 at a value**, so the gate decides 40 sites differently and
/// is in no sense inert. Every project still loads clean, which says the second half:
/// nothing shipped was RELYING on the tolerance in a value position.
pub(super) fn call_arity_error(
    kb: &mut KnowledgeBase,
    params: &[(Symbol, Value)],
    binding: &ArgumentBinding,
    supplied: usize,
    capture_param: Option<Symbol>,
    callee: Symbol,
    pos: NodePos,
    span: Option<Span>,
) -> Option<TypeError> {
    if binding.surplus_positional == 0 && binding.unfilled.is_empty() {
        return None;
    }
    // The functional-relation view (see this function's doc). ADMITTED here and CHECKED
    // by the caller: the same predicate answers which column is the result.
    if relational_result_column(params, binding, pos).is_some() {
        return None;
    }
    let plural = |n: usize| if n == 1 { "" } else { "s" };
    let unfilled_tail = if binding.unfilled.is_empty() {
        String::new()
    } else {
        format!(
            "; no argument fills parameter{} {}",
            plural(binding.unfilled.len()),
            binding
                .unfilled
                .iter()
                .map(|s| format!("`{}`", short_name_of(kb.local_name_of(*s))))
                .collect::<Vec<_>>()
                .join(", "),
        )
    };
    // The DECLARED count in the same currency `supplied` is counted in: what a caller
    // writes. A variadic capture slot is not one of those — it is filled by the WI-727
    // rewrite, from named arguments the fixed list does not name — so it is subtracted
    // here and described instead.
    //
    // WI-1130 CORRECTED BOTH HALVES OF THE CAPTURE CASE. The tail read "plus any named
    // arguments the `...rest` capture collects", naming only ONE of the slot's two
    // channels — a POSITIONAL argument may fill it too (056 §5.4). And the COUNT still
    // said "expected 1 argument" for `cap[R](x: Int64, ...rest: R)`, which an author
    // reading it would take as forbidding the perfectly legal `cap(1, 2)`; the headline
    // and the tail contradicted each other. Both now admit the extra positional slot, and
    // state the EXCLUSIVITY — the rule `normalize_variadic_capture` refuses
    // `cap(1, 2, a: 3)` under. (The count half was found by a `/code-review` pass.)
    let declared = params.len() - usize::from(capture_param.is_some());
    let expected = match capture_param {
        // NO COUNT AT ALL for the capture case, and deliberately not the "N or N+1" a
        // review first proposed: that is false too. The named channel is UNBOUNDED —
        // `cap(1, a: 2, b: 3)` writes THREE arguments against one declared parameter and
        // is legal (`wi1100_call_arity_test::an_empty_variadic_capture_still_loads`) — so
        // no range describes what this callee admits. What is true is the SHAPE, so the
        // shape is what it states; the two counts the author can check against remain in
        // `actual` ("got N arguments") and in `unfilled_tail`.
        Some(c) => format!(
            "the parameter list `{}` filled — it declares {declared} parameter{}, and the \
             `...{}` capture takes EITHER one further positional argument OR any number of \
             named arguments the fixed list does not name, never both",
            kb.qualified_name_of(callee),
            plural(declared),
            short_name_of(kb.local_name_of(c)),
        ),
        None => format!(
            "{} argument{} — the parameter list `{}` declares",
            declared,
            plural(declared),
            kb.qualified_name_of(callee),
        ),
    };
    Some(TypeError::Other {
        site: TypeError::here(),
        span,
        // The subject is the call's SHAPE, not any one parameter — the same
        // `arity` pseudo-parameter the function-VALUE path's count mismatch
        // reports under, so the two render alike.
        context: TypeErrorContext::OperationArgument {
            op_name: callee,
            param: kb.intern("arity"),
        },
        expected,
        actual: format!("{supplied} argument{}{unfilled_tail}", plural(supplied)),
    })
}

/// WI-426: rebuild an operation-call `Apply` with its NAMED arguments reordered
/// into the callee's PARAMETER declaration order. Eval binds arguments
/// positionally — `start_apply` discards the labels and appends the named args
/// after the positional ones (eval.rs), delegating ordering to the typer — so
/// without this reorder a call written `two(b: …, a: …)` binds the value meant
/// for `b` to param `a` at runtime. The named labels match params by NAME
/// (see [`match_named_arg_param`]), not symbol identity. `some_wraps` (combined
/// pos+named indices in original order) are applied first so their indices stay
/// valid, then the named tail is sorted by each label's matched param index (an
/// unmatched label — a missing-param call, reported elsewhere — sorts last,
/// never silently rebinding). Returns `None` when `occ` is not a plain `Apply`.
pub(super) fn reorder_named_args_in_apply(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    params: &[(Symbol, Value)],
    pos_count: usize,
    some_wraps: &[(usize, Value)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> Option<Rc<NodeOccurrence>> {
    // WI-20260829-W6JH0: `recv_type` rides along with `type_args`. This rebuild runs
    // BEFORE the receiver type is read (it reorders a NAMED-argument call into positional
    // form and rebinds `occ`), so dropping it made a form-(3) bracket inert on any call
    // written with named arguments while working on the positional spelling of the same
    // call — one claim, two verdicts, decided by argument spelling. Found by /code-review.
    let (functor, labels, type_args, recv_type) = match occ.as_expr()? {
        Expr::Apply {
            functor,
            named_args,
            type_args,
            recv_type,
            ..
        } => (
            *functor,
            named_args.iter().map(|(s, _)| *s).collect::<Vec<Symbol>>(),
            type_args.clone(),
            recv_type.clone(),
        ),
        _ => return None,
    };
    let mut children = some_wrapped_children(kb, some_wraps, pos_results, named_results);
    let named_children = children.split_off(pos_count);
    let pos_children = children;
    // Precompute each label's matched param index (immutable kb borrow) before
    // sorting, so the sort key needs no kb access. Every label matches a distinct
    // param here — the caller's named-arg COVERAGE check already rejected unknown
    // / duplicate labels with a loud error — so `usize::MAX` is defensive only.
    let keys: Vec<usize> = labels
        .iter()
        .map(|&label| {
            params
                .iter()
                .position(|(s, _)| same_label(kb, *s, label))
                .unwrap_or(usize::MAX)
        })
        .collect();
    let mut triples: Vec<(usize, Symbol, Rc<NodeOccurrence>)> = keys
        .into_iter()
        .zip(labels)
        .zip(named_children)
        .map(|((k, l), c)| (k, l, c))
        .collect();
    triples.sort_by_key(|(k, _, _)| *k);
    // WI-20260827-1F0QP: a MIXED call is rewritten ALL-POSITIONAL, in PARAMETER ORDER.
    //
    // The runtime binds argument `i` to parameter `i` — `start_apply` streams
    // `pos_args ++ named_args` and `enter_operation` zips that against `params` — so
    // this rewrite is the ONLY thing that puts a call's arguments where its body reads
    // them. `pos ++ (named sorted by param)` lands correctly exactly when the
    // positional arguments occupy the LEADING parameters, which is the shape every
    // call had while a mixed one was refused at load. Now that `bind_call_arguments`
    // ranks them among the NOT-named, the positional arguments no longer do, and
    // emitting them first would hand parameter 0 an argument meant for parameter 1.
    //
    // Sorting ALL the arguments by parameter index and emitting them positionally is
    // the shape an all-positional call already has, so every downstream reader — the
    // SLD unfold's `anf_flatten`, `body_specialize`'s `reduce`, WI-938's
    // functional-relation view (which requires `named_arity: 0`) — sees a form it
    // already handles, rather than a novel all-named one. The labels are a SPELLING
    // that this pass has finished validating; nothing after it reads them.
    //
    // Untouched when the call is not mixed: an all-positional call has no labels to
    // rank against and an all-named one has no positional arguments to move, so both
    // keep the exact node they had.
    if !pos_children.is_empty() && !triples.is_empty() {
        // Through [`positional_param_indices`], the owner `bind_call_arguments` and the
        // two type-check loops read — so the parameter an argument is CHECKED against is
        // by construction the one it is BOUND to.
        let named_occs: Vec<(Symbol, Rc<NodeOccurrence>)> =
            triples.iter().map(|(_, l, c)| (*l, Rc::clone(c))).collect();
        let pos_params = positional_param_indices(kb, params, pos_children.len(), &named_occs);
        if pos_params.iter().all(|p| p.is_some()) {
            let mut ordered: Vec<(usize, Rc<NodeOccurrence>)> = pos_params
                .iter()
                .flatten()
                .copied()
                .zip(pos_children)
                .collect();
            ordered.extend(triples.into_iter().map(|(k, _, c)| (k, c)));
            ordered.sort_by_key(|(k, _)| *k);
            let pass = crate::kb::simp_rewrite::simp_pass(kb);
            return Some(NodeOccurrence::synthesized_expr(
                Expr::Apply {
                    recv_type,
                    functor,
                    pos_args: ordered.into_iter().map(|(_, c)| c).collect(),
                    named_args: Vec::new(),
                    type_args,
                },
                Rc::clone(occ),
                pass,
                occ.owner,
            ));
        }
    }
    let named_pairs: Vec<(Symbol, Rc<NodeOccurrence>)> =
        triples.into_iter().map(|(_, l, c)| (l, c)).collect();
    let pass = crate::kb::simp_rewrite::simp_pass(kb);
    Some(NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type,
            functor,
            pos_args: pos_children,
            named_args: named_pairs,
            type_args,
        },
        Rc::clone(occ),
        pass,
        occ.owner,
    ))
}

/// Wrap a BARE `EffectExpression` node (`merge(…)` / `present(…)` / `open(…)` /
/// `empty_row`, the shape a BOUND row-tail var walks to) into the canonical
/// `effects_rows(…)` wrapper the row machinery consumes. Carrier-preserving: a
/// ground expression stays ground, an occurrence stays an occurrence.
///
/// TOTAL, because A ROW HAS EXACTLY TWO CARRIERS — there is no third case to fall back
/// from. That is WI-20260820-CTD6D's verdict, which asked whether a `Value::Entity`-carried
/// row is REACHABLE (give the wrapper an `Entity` constructor and drive the flatten) or
/// UNREACHABLE BY CONSTRUCTION (say which producers can mint an effect-row `Value`, then
/// make the case loud). It is the second, and the reason is in the row IR itself rather
/// than in a reachability argument about who calls this:
///
///  * EVERY row-structural position in the occurrence IR is a
///    [`TypeChild`](crate::kb::node_occurrence::TypeChild) — `TypeNode::EffectsRows
///    { effects_expr }`, and `EffectExprNode`'s `Merge{left, right}` / `Present{label}` /
///    `Guarded{label}` / `Absent{label}` / `Open{tail}` — and `TypeChild` has two
///    variants, `Interned(TermId)` and `Node(Rc<NodeOccurrence>)`. The one non-`TypeChild`
///    child anywhere in the algebra is `Guarded.guard`, a `List[reflect.Term]`, which is
///    not a row. [`type_child_view_item`](crate::kb::term_view::type_child_view_item) maps
///    those two onto `ViewItem::Term` / `ViewItem::Node` and [`view_item_value`] onto
///    `Value::Term` / `Value::Node`, so READING a row's child never widens the carrier;
///  * the two constructor families agree. The term builders
///    (`make_effect_expression_{empty_row,present,guarded,absent,open,merge}`,
///    `make_effects_rows_type`) all return `TermId`; the occurrence builders
///    (`make_{merge,present,open,empty_row}_occ`, `make_effects_rows_occ`) all return
///    `Rc<NodeOccurrence>`. There is no third: a row is minted as a term or as an
///    occurrence;
///  * the LOADER is that same two-variant map. `type_expr_to_value` (kb/load.rs) is total
///    over `TypeChild`, and it builds BOTH an operation's declared `effect_values` and its
///    `params` — which is why the `OperationInfo` emission beside it already states this
///    invariant in the same breath, as `unreachable!("a param type is Term or Node")`. The
///    NARROWING direction says it too: [`value_to_type_child`], where a `Value` enters the
///    row IR, calls a scalar / `Var` / `Entity` in that slot "a typer bug";
///  * everything between those producers and here PRESERVES the carrier —
///    `walk_type_deep_value_g`, `substitute_ref_syms_value` and `rekey_resource_value` each
///    end `other => other.clone()`, and `merge_effects_into` only clones — and the σ surfacing
///    [`walk_value_to_resolved`] can only hand back what a bind put in: `bind_row_tail`
///    binds a `TermId`, the multi-tail absorb binds another row's own inner expression,
///    and WI-375's alias threading is gated on `matches!(value, Value::Node(_))`.
///
/// TWO CARRIERS ESCAPE THE IR ARGUMENT, and they need their own census — found by review of
/// this ticket, not by the four bullets above, which is why they are stated separately
/// rather than folded in. The classifier keys on `head(kb).functor_sym()`, and WI-436 makes
/// a 0-ARY row constructor read as a bare [`ViewHead::Ref`]: `empty_row` is one (it is by
/// volume the most common row shape reaching here — 27 621 of the 97 799 probed calls). A
/// `Value::SymbolRef(empty_row)` and a nullary `Value::Entity { functor: empty_row }` BOTH
/// answer `ViewHead::Ref(empty_row)` — `functor_view_head` canonicalizes the second — so
/// either would classify as a bare row WITHOUT ever passing through the row IR. Neither is
/// reachable, for a producer reason rather than a structural one:
///
///  * `Value::SymbolRef` has exactly FOUR producers. Three are at its evaluator minter
///    (`symbol_value`, eval/builtins.rs): `Dictionary.impl`, `OpRef.op`, `OpRef.named`.
///    The fourth is in the TYPER — [`nominal_heads_compatible`] (WI-RKMD4), which mints a
///    bare sort reference to ask the head question and discards it. Each hands back a sort
///    or operation symbol the KB already holds; none can be an `EffectExpression`
///    constructor. The count is stated rather than the reason alone because it is what
///    licenses the panic arm below, and a census outside the evaluator is exactly the kind
///    a later reader would not think to look for;
///  * a nullary `Value::Entity` over `empty_row` is what the EVALUATOR would mint for a
///    program writing `empty_row()`. That is a runtime value, and the typer's effect stream
///    is built by the loader and by the typer's own row extraction — never fed from the
///    evaluator.
///
/// `ctd6d_row_carrier_tests` drives the `SymbolRef` case directly, so this verdict is pinned
/// rather than only argued.
///
/// MEASURED as well as argued. A probe here and at both callers, over the whole workspace
/// suite (5353 tests over 35 binaries), logged 969 760 row-position values: every one was
/// `Value::Term` or `Value::Node` and the third arm never fired. A corpus run is only a
/// lower bound — which is why the verdict rests on the IR above and the run is only what
/// says nothing reachable contradicts it. The same run measured something the corpus DOES
/// leave uncovered: all 97 799 values that reached THIS function were `Value::Term`, so the
/// `Value::Node` arm is never taken by any program in the suite. `ctd6d_row_carrier_tests`
/// drives it directly for that reason.
///
/// The third arm is an OR-PATTERN over every remaining `Value` variant with NO `_`, so a new
/// carrier is a COMPILE ERROR here and its author has to decide, instead of inheriting a
/// silent fallback. It PANICS rather than taking [`value_to_type_child`]'s softer
/// `debug_assert!`-plus-fallback on the same invariant, and the difference is that that site
/// has a meaningful degradation to fall back ON (a fresh `?ungrounded` type var) whereas
/// this one does not: the only thing left to do with an unwrappable row is carry it whole,
/// which IS the defect. That is what the old `_ => None` cost: both callers read it as "not a
/// row" and carried the value whole — the pre-WI-441 leak. At an operation boundary that
/// surfaces as the malformed row atom `merge[left = present[…], …]` (WI-329's own back-out
/// measurement records the message verbatim; WI-493's combinator chain is the one that must
/// stay load-clean of it), and inside a lambda's arrow it becomes the malformed
/// `present(label = merge(…))` WI-329 fixed for the other carriers. The declassification was
/// silent BY CONSTRUCTION, because the classification is by FUNCTOR HEAD
/// ([`value_is_bare_row_expr`] reads `head(kb).functor_sym()`, which every carrier answers)
/// while only the carrier decided whether the wrap happened.
///
/// Shared by the two sites that must turn a walked row VALUE back into a row:
/// [`explode_incurred_effect_row`] (the op-boundary reader) and the call-site
/// effect-contribution loop (WI-329) — so the wrapping cannot drift between the
/// producer of a call's incurred effects and the reader that checks them.
pub(super) fn wrap_bare_effect_expr_as_row(kb: &mut KnowledgeBase, expr: &Value) -> Value {
    match expr {
        Value::Term { id: t, .. } => Value::term(kb.make_effects_rows_type(*t)),
        Value::Node(occ) => Value::Node(kb.make_effects_rows_occ(
            TypeChild::Node(Rc::clone(occ)),
            occ.span,
            occ.owner,
        )),
        // No `_`: see the doc above. A new `Value` variant lands here as a compile error.
        Value::Int(_)
        | Value::BigInt(_)
        | Value::Float(_)
        | Value::Bool(_)
        | Value::Str(_)
        | Value::Unit
        | Value::Tuple { .. }
        | Value::Entity { .. }
        | Value::Closure(_)
        | Value::OpRef { .. }
        | Value::Stream(_)
        | Value::Substitution(_)
        | Value::Map(_)
        | Value::Cell(_)
        | Value::Kb(_)
        | Value::FactRef(_)
        | Value::Var(_)
        | Value::SymbolRef(_)
        | Value::Relation { .. } => unreachable!(
            "effect row on a THIRD carrier: row-shaped by functor head, but neither \
             `Value::Term` nor `Value::Node` — and those are the only two the row IR \
             can mint, since every row-structural position is a `TypeChild` \
             (WI-20260820-CTD6D; this fn's doc carries the census): {expr:?}"
        ),
    }
}

/// WI-441: explode a ROW-shaped effect value into its component atoms —
/// the present labels plus the row-tail var (as a bare `Value::Term` Var
/// atom). Returns `None` when `effect` is not row-shaped (an ordinary
/// label like `Modify[c]` / `Error` / a bare row var — those compare
/// atom-to-atom as before). Row-shaped = the `effects_rows` wrapper OR a
/// bare `EffectExpression` node (`merge`/`present`/`absent`/`open`/
/// `empty_row`, matched by QUALIFIED functor so a user sort named `merge`
/// is not misclassified) — a bound row var walks to the bare form.
/// Absent atoms are DROPPED: they are constraints on the row, not effects
/// the body incurs.
pub(super) fn explode_incurred_effect_row(
    kb: &mut KnowledgeBase,
    effect: &Value,
) -> Option<Vec<Value>> {
    explode_declared_effect_row(kb, effect).map(|(atoms, _absent)| atoms)
}

/// IS THIS EFFECT VALUE A ROW, and if so what is it as a canonical `effects_rows(…)`?
/// `None` for an ordinary label (`Modify[c]`, `Error`, a bare row var), which its
/// callers compare atom-to-atom.
///
/// Split out of [`explode_incurred_effect_row`] by WI-20260830-APWM3 so the DECLARED
/// side ([`explode_declared_effect_row`]) classifies by exactly the same predicate the
/// INCURRED side does. The two are compared against each other, so a shape one calls a
/// row and the other calls a label is precisely the mismatch this pair exists to avoid
/// — the same argument [`wrap_bare_effect_expr_as_row`]'s doc makes for sharing the
/// WRAP between a call's effect producer and its reader.
///
/// Row-shaped = the `effects_rows` wrapper OR a bare `EffectExpression` node
/// (`merge`/`present`/`absent`/`open`/`empty_row`), matched by QUALIFIED functor so a
/// user sort that merely shares the short name `merge` is not misclassified. A bound
/// row var walks to the bare form.
pub(super) fn effect_value_as_row(kb: &mut KnowledgeBase, effect: &Value) -> Option<Value> {
    let is_rows_wrapper = matches!(type_dispatch_name_view(kb, effect), Some("effects_rows"));
    // WI-436: `empty_row` is a 0-ary constructor → bare `Ref` head; read the
    // functor symbol off either spelling so the empty row is still recognized
    // as row-shaped (not leaked as an undeclared `empty_row` effect label).
    let head_is_row_expr = effect.head(kb).functor_sym().is_some_and(|sym| {
        matches!(
            kb.qualified_name_of(sym)
                .strip_prefix("anthill.prelude.EffectExpression."),
            // WI-478: a bare `guarded(…)` atom is row-shaped (it explodes via
            // `decompose_effect_row`'s guarded arm → its label, conservatively
            // present) — without it, a guarded incurred effect surfaces whole.
            Some("merge" | "present" | "guarded" | "absent" | "open" | "empty_row")
        )
    });
    if !is_rows_wrapper && !head_is_row_expr {
        return None;
    }
    if is_rows_wrapper {
        return Some(effect.clone());
    }
    // Wrap the bare EffectExpression so `decompose_effect_row` sees the
    // canonical `effects_rows(…)` shape. Infallible: `head_is_row_expr` above
    // already says this IS a row, and a row has two carriers (WI-20260820-CTD6D
    // — [`wrap_bare_effect_expr_as_row`]'s doc carries the census). The `None`
    // this arm used to be able to produce was read by the caller as "not a row",
    // which is the pre-WI-441 leak.
    Some(wrap_bare_effect_expr_as_row(kb, effect))
}

/// WI-20260830-APWM3 — the DECLARED twin of [`explode_incurred_effect_row`]: flatten one
/// declared effect atom into `(atoms that ADMIT an incurred effect, ABSENT labels)`.
/// `None` when the atom is not row-shaped, and the caller then keeps it whole — exactly
/// as the incurred side does.
///
/// THE DEFECT IT CLOSES. A declared atom is a ROW whenever it was written as a
/// projection off a parameter (`effects {llm.E, Error}`) and the parameter's type is
/// CONCRETE: `llm: LiveLlm` with `LiveLlm provides Llm[E = {External}]` eliminates
/// `llm.E` to `merge[left = present[label = External], right = empty_row]`. The
/// coverage comparison then asked "is the incurred label `External` among the declared
/// members" of a list holding that merge as ONE OPAQUE MEMBER, and answered no —
/// `expected declared: [{merge[…]}, Error], got undeclared effect: External`. Only a
/// NON-EMPTY CONCRETE instantiation trips it: an abstract receiver leaves a row var
/// with nothing to flatten, and `E = {}` flattens to nothing. So the only row that
/// loaded at a concrete carrier was the OVER-declared literal one (`{External, Error}`),
/// which is the opposite of what row polymorphism is for.
///
/// THE MIRROR DIRECTION WAS ALREADY FIXED, which is why this is a gap and not a design
/// choice: WI-375 decomposes an `effects_rows(…)` wrapper on the BODY side precisely so
/// "the effect machinery sees flat labels, not the wrapper as one opaque effect". Same
/// reading, other side of the same comparison.
///
/// THE THREE BUCKETS, and why absences ride along rather than being dropped as they are
/// on the incurred side. An incurred `absent` is not an effect anything performs, so
/// [`explode_incurred_effect_row`] drops it; a DECLARED one is proposal 064's negative
/// claim (`-Permission[Model]`) and has its own reader — the denied-effect diagnostic.
/// Returning both buckets is what keeps a `-X` buried inside a projected row visible to
/// that reader; scanning the un-flattened list for a top-level `absent` functor (what
/// this replaced) could not see one.
///
/// A TAIL VAR IS AN ADMITTING ATOM, not a label: a declared row ending in an open tail
/// admits whatever binds there, and the incurred side explodes its own tails the same
/// way, so the two meet as equal vars.
pub(super) fn explode_declared_effect_row(
    kb: &mut KnowledgeBase,
    effect: &Value,
) -> Option<(Vec<Value>, Vec<Value>)> {
    let row = effect_value_as_row(kb, effect)?;
    let subst = Substitution::new();
    let (present, tails, absent) = decompose_effect_row(kb, &subst, &row)?;
    let mut atoms = present;
    for t in tails {
        atoms.push(Value::term(t));
    }
    Some((atoms, absent))
}

/// WI-440: two effect labels match modulo POSITIONAL binder alignment.
/// Direct structural equality first ([`resolved_labels_equal`]); otherwise an
/// applied-effect pair (`Modify[c]` vs `Modify[x]`) matches when the base
/// effect sorts are EQUAL and the resources are corresponding places under
/// `place_map` (actual-side place → declared-side place) — the positional
/// binder correspondence between an eta'd op's own params and the declared
/// callback's registered `CallbackParam` places.
fn labels_match_aligned(
    kb: &KnowledgeBase,
    subst: &Substitution,
    place_map: &HashMap<Symbol, Symbol>,
    a: &Value,
    e: &Value,
) -> bool {
    if resolved_labels_equal(kb, subst, a, e) {
        return true;
    }
    if labels_match_by_subsumption(kb, a, e) {
        return true;
    }
    let (
        TypeExtractor::Parameterized { base: a_base, .. },
        TypeExtractor::Parameterized { base: e_base, .. },
    ) = (extract_type(kb, a), extract_type(kb, e))
    else {
        return false;
    };
    if a_base != e_base {
        return false;
    }
    match (
        extract_effect_resource_sym(kb, a),
        extract_effect_resource_sym(kb, e),
    ) {
        (Some(ar), Some(er)) => ar == er || place_map.get(&ar) == Some(&er),
        _ => false,
    }
}

/// WI-705: reject a call whose SIGNATURE — the op's own effect row, or any of its
/// arrow / `Function`-typed param rows — an instantiation has made UNINHABITABLE:
/// present AND absent the same label (`{X, -X}`, the WI-328 piece-d
/// self-contradictory shape). Runs AFTER the argument-unification loops, so `subst`
/// carries the FULL instantiation — explicit `[E = {…}]` args AND argument/context
/// inference alike.
///
/// This is the SIGNATURE-altitude generalization of the WI-700 reject that lived
/// inside [`validate_callback_effect_row`]: that one fired only for an eta'd
/// OP-REF callback arg (a lambda arg, or a param with no arg at all, bailed at the
/// var-ref extraction) and only inspected the ONE callback param being validated.
/// Two shapes slipped through it: (a) the op's OWN row (`g[E]() effects {E, -X}`
/// called `g[E = {X}]()` — no callback param to inspect), and (b) a lambda callback
/// with a self-contradictory instantiated declared row. Being actual-agnostic and
/// covering the own-row plus every param row, this subsumes the WI-700 reject (now
/// removed) — including the case where inference (not an explicit `[…]`) binds the
/// offending row param, which the old per-arg check caught because it too ran after
/// unification. Placed before [`validate_callback_effect_row`] so that function may
/// assume an inhabitable declared row and own only actual-vs-declared conformance.
///
/// Gated on at least one op type param actually BOUND in `subst`: an uninstantiated
/// signature carries its rows as declared (a literal `{X, -X}` is a load-time
/// concern, not this call-site one), and only binding a row tail can newly make a
/// row uninhabitable. So the check is a no-op for a call that instantiates nothing.
///
/// KNOWN LIMITATION (not a WI-700 regression — the old check never saw these
/// either): a contradiction in a RETURN-position arrow row, or in the inner row of a
/// nested/curried arrow param, is not decomposed here; only the op's own row and the
/// OUTER row of each directly arrow-typed param are checked.
pub(super) fn check_signature_self_contradiction(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    op: &OperationInfoFull,
    fn_sym: Symbol,
    span: Option<Span>,
) -> Result<(), TypeError> {
    let any_param_bound = op.type_params.iter().any(|(_, v)| {
        let vt = type_param_var_term(kb, *v);
        resolved_var(kb, &walk_view(kb, subst, &TermIdView(vt))).is_none()
    });
    if !any_param_bound {
        return Ok(());
    }

    // (a) the op's OWN declared effect row. `op.effects` is a flat list of atoms /
    // written-row wrappers; decompose each RAW (resolving row params through
    // `subst`) and ACCUMULATE present/absent across the whole list — a clash may
    // span two elements (`[{E}, -X]`) as well as one wrapper (`{E, -X}`). A
    // non-decomposable element (malformed) contributes nothing and is reported by
    // its own diagnostic path; it must not mask or fabricate a clash here.
    let mut present: Vec<Value> = Vec::new();
    let mut absent: Vec<Value> = Vec::new();
    for e in &op.effects {
        if let Some((p, _tails, a)) = decompose_effect_row_raw(kb, subst, e) {
            present.extend(p);
            absent.extend(a);
        }
    }
    if let Some(err) = uninhabitable_row_error(
        kb,
        subst,
        &present,
        &absent,
        &op.effects,
        fn_sym,
        None,
        span,
    ) {
        return Err(err);
    }

    // (b) each arrow / `Function`-typed PARAM's declared effect row (after subst).
    // `arrow_parts` gates a non-callable param cheaply; a param row is a single
    // self-contained expression, so its clash is within the one decomposition.
    for (param_sym, param_type) in &op.params {
        let Some((_, _, Some(eff))) = arrow_parts(kb, param_type) else {
            continue;
        };
        let row = canonical_effects_row(kb, &eff);
        let Some((p, _tails, a)) = decompose_effect_row_raw(kb, subst, &row) else {
            continue;
        };
        if let Some(err) = uninhabitable_row_error(
            kb,
            subst,
            &p,
            &a,
            std::slice::from_ref(&row),
            fn_sym,
            Some(*param_sym),
            span,
        ) {
            return Err(err);
        }
    }
    Ok(())
}

/// The WI-705 uninhabitability test for one decomposed row (or the accumulated
/// present/absent of the op's own multi-element row). Returns the diagnostic iff
/// some label is present AND absent AND UNCONDITIONALLY present — a `guarded(X, g)`
/// atom decomposes to a conservative present `X` ([`decompose_effect_row_raw`],
/// WI-478), but it is only CONDITIONALLY present (WI-067 discharge may refute `g`
/// and drop it), so a guarded present that clashes with `-X` is NOT a hard
/// contradiction: defer to discharge rather than reject a row that may be
/// inhabitable. The guarded re-walk (`rows` are the source rows to re-scan) runs
/// only once a candidate clash exists — rare, since it needs an absent label — so
/// the common no-lacks path pays nothing beyond the cheap present/absent scan.
fn uninhabitable_row_error(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    present: &[Value],
    absent: &[Value],
    rows: &[Value],
    fn_sym: Symbol,
    param: Option<Symbol>,
    span: Option<Span>,
) -> Option<TypeError> {
    let clash = uninhabitable_row_clash(kb, subst, present, absent, rows)?;
    Some(signature_self_contradiction_error(
        kb, fn_sym, param, &clash, span,
    ))
}

/// WI-705's verdict WITHOUT its diagnostic — the ABSENT label a row unconditionally
/// contradicts, or `None`.
///
/// Split out by WI-20260825-CBRSW so the LOAD-time twin
/// ([`check_declared_row_contradiction`]) asks the same question the call-site check
/// asks, rather than re-deriving the guarded-deferral rule a second time. The two
/// RENDER differently — a load error names a declaration, a `TypeError` names a call —
/// but "is this row uninhabitable" is one decision and lives here.
pub(super) fn uninhabitable_row_clash(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    present: &[Value],
    absent: &[Value],
    rows: &[Value],
) -> Option<Value> {
    // Cheap pre-check: is any present label also absent at all? (Almost always no —
    // a row needs a `-X` lacks-constraint to clash.) Bail before the guarded walk.
    row_self_contradiction(kb, subst, present, absent)?;
    // A candidate clash exists. Gather the dischargeable (guarded) labels — each
    // cancels ONE present occurrence of that label (a `guarded(X,g)` atom decomposes
    // to a present `X`, WI-478). A label is a genuine contradiction only if it is
    // present AND absent AND has an UNCONDITIONAL occurrence, i.e. it appears in
    // `present` more times than in `guarded` (so a row carrying both `X :- g` and a
    // literal `X` alongside `-X` still rejects on the literal). Multiset-counted so a
    // label that is only ever guarded (`{X :- g, -X}`) defers to WI-067 discharge.
    let mut guarded: Vec<Value> = Vec::new();
    for r in rows {
        for (label, _guard) in collect_guarded_atoms(kb, subst, r) {
            guarded.push(label);
        }
    }
    // WI-20260825-CBRSW: counted with the same DIRECTIONAL verdict the pre-check used
    // ([`label_violates_absence`]), not with equality. Counting by equality here would
    // have made the pre-check's wider reading unreachable — a `Permission[GptModel]`
    // that violates `-Permission[Model]` is not EQUAL to it, so both counts came out 0
    // and `find` returned `None`, i.e. the pre-check found the clash and this line
    // dropped it. The guarded side is counted the same way, so a `Permission[GptModel]
    // :- g` still defers to WI-067 discharge exactly as a literal one does.
    fn count(kb: &mut KnowledgeBase, subst: &Substitution, hay: &[Value], needle: &Value) -> usize {
        hay.iter()
            .filter(|h| label_violates_absence(kb, subst, h, needle))
            .count()
    }
    let clash_idx = absent
        .iter()
        .position(|a| count(kb, subst, present, a) > count(kb, subst, &guarded, a))?;
    Some(absent[clash_idx].clone())
}

/// The WI-705 diagnostic: an instantiation (explicit `[E = {…}]` or inferred) made a
/// signature row admit AND lack `clash`. `param = Some(_)` names a callback PARAM row
/// (context `OperationArgument`, wording shared with the removed WI-700 reject so its
/// `shield`/`Outside`/`lack` assertions still hold); `param = None` names the op's OWN
/// effect row (context `OperationEffects`).
fn signature_self_contradiction_error(
    kb: &KnowledgeBase,
    fn_sym: Symbol,
    param: Option<Symbol>,
    clash: &Value,
    span: Option<Span>,
) -> TypeError {
    let label = type_display_name_value(kb, clash);
    let op_qn = kb.qualified_name_of(fn_sym);
    match param {
        Some(param_sym) => TypeError::Other {
            site: TypeError::here(),
            span,
            context: TypeErrorContext::OperationArgument {
                op_name: fn_sym,
                param: param_sym,
            },
            expected: format!(
                "callback parameter `{}` of `{}` to have a consistent effect row",
                kb.local_name_of(param_sym),
                op_qn,
            ),
            actual: format!(
                "its instantiation makes it both admit and lack `{label}` \
                 (violates its `-{label}` lacks-constraint)",
            ),
        },
        None => TypeError::Other {
            site: TypeError::here(),
            span,
            context: TypeErrorContext::OperationEffects { op_name: fn_sym },
            expected: format!("operation `{op_qn}` to have a consistent effect row"),
            actual: format!(
                "its instantiation makes its effect row both admit and lack `{label}` \
                 (violates its `-{label}` lacks-constraint)",
            ),
        },
    }
}

/// WI-440 — the `-Modify[binder]` CHECKING direction: validate a callback
/// argument's effect row against the declared callback parameter's row,
/// aligning the two binder spaces positionally. The declared row's labels
/// name the callback's registered `CallbackParam` places (`<op>.f.x`, the
/// WI-341 binder→place resolution); the ACTUAL argument's row names its own
/// places — for an eta'd operation, that op's OWN param places (`<pred>.c`);
/// for a LAMBDA, its top-level binder symbols (`lambda (c) -> …`, the WI-550
/// gensym'd identity its body effects reference) — param i of one corresponds
/// to param i of the other (`arg_places` order / binder order).
///
/// For each PRESENT label of the actual row:
///   * covered by a declared PRESENT label (mod alignment) → ok;
///   * matching a declared ABSENT label (mod alignment) → REJECT — the
///     lacks-constraint violation (`Modify[c]` against `-Modify[x]`);
///   * otherwise: declared row OPEN → absorbed; CLOSED → REJECT — an effect
///     the declared row does not admit, which would escape the WI-352/353
///     boundary propagation (that derives from the DECLARED callback row,
///     not from the argument actually passed).
///
/// Conservative skips (return `None`, no check): a non-arrow/`Function`
/// declared or actual type, a missing effects child, an actual row that is OPEN or
/// carries its own absents, or a row that fails to decompose. VALIDATION-only:
/// `subst` is read (label walking / bound row-tail resolution) and never extended —
/// inference stays with the `unify_types` pass that precedes this check.
///
/// WI-706 closed the LAMBDA gap: a non-eta argument no longer bails. The actual
/// callback source is now an eta'd op-ref OR an inline lambda ([`callback_actual_source`]);
/// a lambda's inferred row already rides its arrow type (`arrow_parts(actual)`, built
/// from the body's effects by the `LambdaBody` frame), and its top-level binder slots
/// align to the declared places exactly as an op's `arg_places` do. So
/// `shield[EffP = {}](lambda () -> poke())` — a lambda whose body incurs `{Outside}` —
/// is now REJECTED against the `-Outside` slot, agreeing with the eta twin `…(poke)`.
/// (The *self-contradiction* half — a lambda whose DECLARED param row is uninhabitable
/// after instantiation — is closed one altitude up by [`check_signature_self_contradiction`],
/// WI-705; this owns the actual-vs-declared conformance for the lambda BODY.)
///
/// An un-flattenable lambda parameter (a `_`, a `Cons(h, t)` destructure, or a nested
/// tuple) yields a `None` place slot: it stays position-aligned to the declared param
/// but contributes no place-map entry, so a PLACE-CARRYING actual label over it cannot
/// be matched to a declared PRESENT label by alignment. Such a label is then handled by
/// the same absent/closed checks as any other — absorbed by an open declared tail (a
/// row-polymorphic row) or rejected on a closed row (agreeing with the generic
/// arrow-subtype check that also runs, but with a label-naming diagnostic). A
/// PLACE-INDEPENDENT label (`Outside` / `External`, the WI-698 motivation) needs no
/// alignment and is always checked precisely, so a place-free escape through a
/// destructure lambda is caught — which the prior whole-lambda skip missed.
pub(super) fn validate_callback_effect_row(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    fn_sym: Symbol,
    param_sym: Symbol,
    declared: &Value,
    arg_occ: &Rc<NodeOccurrence>,
    actual: &Value,
    span: Option<Span>,
) -> Option<TypeError> {
    // WI-706: the actual callback source — an eta'd op-ref OR an inline lambda.
    // (Was `extract_var_ref_sym_node(arg_occ)?`, which bailed for a lambda,
    // leaving lambda callbacks unchecked against the declared lacks/closed row.)
    let actual_src = callback_actual_source(arg_occ)?;
    // Cheap head gate before `arrow_parts` (which interns its child keys on
    // every call): most var-ref args land in non-callable param slots.
    if !type_head_is_callable(kb, declared) {
        return None;
    }
    // WI-705 (was WI-700): the self-contradictory-instantiation reject moved OUT of
    // here to the SIGNATURE-altitude `check_signature_self_contradiction` (run after
    // the arg-unify loops, before this per-arg validation) — actual-agnostic,
    // covering every callback shape plus the op's OWN row, over the FULL instantiation
    // (explicit + inferred). So by the time control reaches here the declared row is
    // guaranteed inhabitable, and this function owns only actual-vs-declared
    // CONFORMANCE. Decompose the declared row via the FILTERING wrapper (restored from
    // WI-700's raw read): a self-contradictory row can no longer arrive, so the
    // filter's `None` now means only a genuinely malformed row — a conservative skip,
    // matching the other conformance skips below.
    let (_, _, decl_eff) = arrow_parts(kb, declared)?;
    let decl_eff = decl_eff?;
    let decl_row = canonical_effects_row(kb, &decl_eff);
    let (e_present, e_tails, e_absent) = decompose_effect_row(kb, subst, &decl_row)?;
    // The ACTUAL callback's row. WI-700 eta-lifts a nullary op ref so its declared
    // row is present here (an arrow) instead of collapsed to its return type.
    let (_, _, act_eff) = arrow_parts(kb, actual)?;
    let act_eff = act_eff?;
    let act_row = canonical_effects_row(kb, &act_eff);
    let (a_present, a_tails, a_absent) = decompose_effect_row(kb, subst, &act_row)?;
    if a_present.is_empty() || !a_tails.is_empty() || !a_absent.is_empty() {
        // A pure actual row conforms to any (consistent) declared row; an open /
        // absent-carrying actual is left to the unify path (v1).
        return None;
    }
    // WI-706: the actual callback's argument places, aligned to the declared
    // places positionally. An eta'd op contributes its `arg_places` (all real); a
    // lambda contributes its top-level binder slots (`None` for a `_`/literal
    // position, which occupies a slot so arity stays aligned but names nothing an
    // effect place could reference).
    let actual_places: Vec<Option<Symbol>> = match &actual_src {
        CallbackActual::Op(op_sym) => kb
            .symbols
            .arg_places(*op_sym)
            .iter()
            .map(|s| Some(*s))
            .collect(),
        CallbackActual::Lambda(slots) => slots.clone(),
    };
    let declared_places = kb.symbols.arg_places(param_sym);
    // Positional alignment is meaningful only for EQUAL arities — a mismatch
    // (which the generic arg validation rejects on the param type) must not
    // silently truncate the map and mis-align the surviving places.
    //
    // WI-1084 — EXCEPT WHEN THERE ARE NO DECLARED PLACES AND NOTHING NEEDS ONE, which is a
    // real population rather than a corner: a `Function[A, B, E]` parameter registers NO
    // argument places (it names no binders — its `A` is one argument's data type), so this
    // bail discarded the row check ENTIRELY for every `Function`-typed callback slot. That
    // is one of the two levels behind the measured leak `operation bang[A](x: A) -> A
    // effects {Error[T = String]}` reaching a slot declaring `E = {}` and RAISING at
    // runtime out of a `use_it() -> Int64` that declares no effects at all.
    //
    // THE MAP IS ONLY EVER CONSULTED FOR A BINDER-RELATIVE LABEL — `labels_match_aligned`
    // tries structural equality FIRST and reaches `place_map` only for an applied effect
    // whose resource is a place (`Modify[x]`). So when the actual's present labels are all
    // place-FREE there is nothing to align and the empty map costs nothing; `{Error}` versus
    // `{}` is decidable without knowing any correspondence. When the actual DOES name one of
    // its own places, the bail stands unchanged — a `Function` slot cannot express a
    // binder-relative effect, so there is no correspondence to establish and refusing on an
    // absent one would be inventing a verdict rather than reaching it.
    let aligned = actual_places.len() == declared_places.len();
    if !aligned {
        let names_own_place = actual_places.iter().flatten().any(|place| {
            a_present
                .iter()
                .any(|la| extract_effect_resource_sym(kb, la) == Some(*place))
        });
        if !declared_places.is_empty() || names_own_place {
            return None;
        }
    }
    let place_map: HashMap<Symbol, Symbol> = actual_places
        .iter()
        .zip(declared_places.iter().copied())
        .filter_map(|(a, e)| a.map(|a| (a, e)))
        .collect();
    // WI-20260908-9WVT7 — RESOLVE EACH LABEL THROUGH σ BEFORE COMPARING IT.
    // `labels_match_aligned` decides by structural equality after
    // `walk_value_to_resolved`, which chases a TOP-LEVEL variable chain and does NOT
    // descend into an `Fn`'s arguments. So a declared `Error[T = ?P]` was compared
    // UNRESOLVED against an actual `Error[T = Boom]` and reported as "a closed row …
    // does not admit" — even though argument unification had already bound
    // `?P := Boom` (measured by instrumenting the comparison: the label's `T` child
    // chased to the actual's `Boom` TermId while the label itself did not). Not
    // `Error`-specific: any parameterized label whose argument is a call-site-bound
    // type parameter was affected, and `Permission[C]` is the second witness.
    //
    // ALL THREE LISTS, and `e_absent` is not optional. It feeds the SAME comparator
    // below, so resolving only the present ones would leave the `-Label[Arg]`
    // lacks-constraint reject dead exactly when the denied label's argument resolves
    // through σ — including WI-CBRSW's `-Permission[X]`, whose whole purpose is to
    // deny privilege escalation. It also keeps the reject's message coherent: `viol`
    // and `la` are printed in one sentence and would otherwise be two spellings of
    // one σ.
    //
    // PLACED HERE, BELOW THE BAILS, NOT AT EACH `decompose_effect_row`. Three `?`
    // exits and the pure-actual early return sit above, and `walk_type_deep_value`
    // reaches `TermStore::alloc`, which increments a refcount on a hash-cons HIT that
    // nothing here releases. MEASURED over stdlib + three example corpora: of the
    // 31 / 19 / 80 / 19 invocations that reached the old (higher) site, ZERO reached
    // this loop — every one left at the pure-actual bail, so the walk was pure cost
    // and pure leak. `walk_type_deep_value` and not its grounding sibling
    // `resolve_type_deep_value`: this is a CHECK, so it propagates σ and must not
    // δ-ground a concrete-subject projection on the way.
    let e_present: Vec<Value> = e_present
        .iter()
        .map(|l| walk_type_deep_value(kb, subst, l))
        .collect();
    let e_absent: Vec<Value> = e_absent
        .iter()
        .map(|l| walk_type_deep_value(kb, subst, l))
        .collect();
    let a_present: Vec<Value> = a_present
        .iter()
        .map(|l| walk_type_deep_value(kb, subst, l))
        .collect();
    for la in &a_present {
        if e_present
            .iter()
            .any(|le| labels_match_aligned(kb, subst, &place_map, la, le))
        {
            continue;
        }
        if let Some(viol) = e_absent
            .iter()
            .find(|le| labels_match_aligned(kb, subst, &place_map, la, le))
        {
            return Some(TypeError::Other {
                site: TypeError::here(),
                span,
                context: TypeErrorContext::OperationArgument {
                    op_name: fn_sym,
                    param: param_sym,
                },
                expected: format!(
                    "callback for parameter `{}` of `{}` to lack `{}` (its `-…` lacks-constraint)",
                    kb.local_name_of(param_sym),
                    kb.qualified_name_of(fn_sym),
                    type_display_name_value(kb, viol),
                ),
                // WI-706: the diagnostic subject — the offending op by name, or "the
                // lambda argument". Built here (only on the reject path), so the clean
                // typing pass allocates nothing.
                actual: format!(
                    "{} declares `{}` on the corresponding parameter",
                    callback_actual_subject(kb, &actual_src),
                    type_display_name_value(kb, la),
                ),
            });
        }
        if e_tails.is_empty() {
            return Some(TypeError::Other {
                site: TypeError::here(),
                span,
                context: TypeErrorContext::OperationArgument {
                    op_name: fn_sym,
                    param: param_sym,
                },
                expected: format!(
                    "callback effects admitted by parameter `{}` of `{}` (a closed row)",
                    kb.local_name_of(param_sym),
                    kb.qualified_name_of(fn_sym),
                ),
                actual: format!(
                    "{} declares `{}`, which the closed row does not admit",
                    callback_actual_subject(kb, &actual_src),
                    type_display_name_value(kb, la),
                ),
            });
        }
    }
    None
}

/// WI-706: the ACTUAL source of a callback argument whose effect row
/// [`validate_callback_effect_row`] validates — either an eta'd operation reference
/// (its `arg_places` name the row's places) or an inline lambda (its top-level binder
/// slots do). Anything else (a value, a nested call) has no aligned places and never
/// reaches here as a callback.
enum CallbackActual {
    /// An eta'd `op` reference — `Op`'s `arg_places` are its row's places.
    Op(Symbol),
    /// An inline lambda — one slot per top-level parameter POSITION, in order:
    /// `Some(binder)` for a `Var` (the WI-550 gensym'd identity its body effects
    /// reference), `None` for a position that binds no single alignable name (a `_`,
    /// a literal, or a destructure). The `Vec` length is the lambda's arity, so it
    /// aligns to the declared `arg_places` length like an op's does.
    Lambda(Vec<Option<Symbol>>),
}

/// WI-706: classify a callback argument occurrence as an eta'd op-ref or an inline
/// lambda, returning `None` only for a shape that is neither (a value arg, a nested
/// call). A lambda always classifies as `Lambda` — even one whose parameter cannot be
/// fully flattened to positional binders (a constructor destructure / nested tuple);
/// its un-flattenable positions become `None` slots (position-aligned but unmappable)
/// rather than skipping the whole lambda.
fn callback_actual_source(occ: &Rc<NodeOccurrence>) -> Option<CallbackActual> {
    if let Some(op_sym) = extract_var_ref_sym_node(occ) {
        return Some(CallbackActual::Op(op_sym));
    }
    if let NodeKind::Expr {
        expr: Expr::Lambda { param, .. },
        ..
    } = &occ.kind
    {
        return lambda_binder_slots(param).map(CallbackActual::Lambda);
    }
    None
}

/// WI-706: the ordered top-level binder slots of a lambda parameter pattern (see
/// [`CallbackActual::Lambda`]). One slot per top-level parameter POSITION so the
/// `Vec` length is the lambda's arity (aligning to the declared `arg_places`): a
/// `Var` slot carries its binder symbol; every other shape — a `_`/literal (names
/// nothing) or a destructure (`Cons(h, t)` / a nested tuple, whose sub-binders have
/// no single positional identity) — is a `None` slot. A `None` slot stays
/// position-aligned but contributes no place-map entry (see
/// [`validate_callback_effect_row`] for how a label over it is then handled).
fn lambda_binder_slots(param: &Rc<NodeOccurrence>) -> Option<Vec<Option<Symbol>>> {
    /// One flat binder position: `Some(binder)` for a `Var`, `None` for any other
    /// shape (a `_`/literal, or a nested tuple/constructor with no single binder).
    fn slot(p: &Rc<NodeOccurrence>) -> Option<Symbol> {
        match p.as_pattern() {
            Some(Pattern::Var { name, .. }) => Some(*name),
            _ => None,
        }
    }
    match param.as_pattern()? {
        Pattern::Var { name, .. } => Some(vec![Some(*name)]),
        // A flat tuple (`lambda (a, b) -> …`, including the nullary `()`): one slot
        // per element (a non-`Var` element is a `None` slot — position-aligned but
        // unmappable).
        Pattern::Tuple { positional, .. } => Some(positional.iter().map(slot).collect()),
        // A single non-tuple parameter that binds no single alignable name — a `_`,
        // a literal, or a top-level `Cons(h, t)` destructure — is one `None` slot.
        Pattern::Wildcard | Pattern::Literal { .. } | Pattern::Constructor { .. } => {
            Some(vec![None])
        }
    }
}

/// WI-706: the diagnostic subject naming the offending callback argument — the
/// operation by qualified name (`operation `…poke3``) for an eta'd op-ref, or a
/// generic phrase for an inline lambda (a lambda has no name to cite).
fn callback_actual_subject(kb: &KnowledgeBase, actual_src: &CallbackActual) -> String {
    match actual_src {
        CallbackActual::Op(op_sym) => format!("operation `{}`", kb.qualified_name_of(*op_sym)),
        CallbackActual::Lambda(_) => "the lambda argument".to_string(),
    }
}

/// Extract the underlying sort symbol from a term in any of the
/// shapes a binding value may take: `sort_ref(name: Ref(X))`,
/// bare `Ref(X)` / `Ident(X)`, or a nullary `Fn { functor: X, … }`.
pub(super) fn sort_sym_of_term(kb: &KnowledgeBase, t: TermId) -> Option<Symbol> {
    if let Some(s) = extract_sort_ref_sym(kb, &TermIdView(t)) {
        return Some(s);
    }
    match kb.get_term(t) {
        // bare `Ref` handled above via `extract_sort_ref_sym` (WI-361); `Ident` here.
        Term::Ident(s) => Some(*s),
        Term::Fn { functor, .. } => Some(*functor),
        _ => None,
    }
}

/// True iff an `OperationInfo` exists for `op_sym` and it has no body.
/// (Operations declared without a body ⇒ specs / abstract decls.) WI-305: the
/// body is no longer a fact field; it lives in the `op_body_node` side-table,
/// so the body presence is read from there. The OperationInfo-existence gate is
/// preserved — a symbol with no `OperationInfo` (which the old field-walk would
/// report as "has body" via the loop falling through to `false`) must keep that
/// answer so non-operation symbols are not misclassified as body-less spec ops.
pub(super) fn operation_has_no_body(kb: &KnowledgeBase, op_sym: Symbol) -> bool {
    if crate::kb::op_info::lookup_operation_info(kb, op_sym).is_none() {
        return false; // no OperationInfo ⇒ not a body-less operation
    }
    kb.op_body_node(op_sym).is_none()
}

/// True iff `op_sym` resolves to an operation the runtime can actually
/// invoke by symbol: an `OperationInfo` exists for it AND its `body` is
/// `some(...)`. A symbol with no `OperationInfo` (e.g. the auto-bound
/// `anthill.prelude.String.eq` a `provides` block registers) or with
/// `body = none` (a spec-level declaration / derived op) is NOT a valid
/// static-dispatch rewrite target — the runtime resolves those via a
/// registered builtin or the spec's own derived rule. WI-237.
pub(crate) fn op_has_runnable_body(kb: &KnowledgeBase, op_sym: Symbol) -> bool {
    match crate::kb::op_info::lookup_operation_info(kb, op_sym) {
        Some(rec) => rec.body_node.is_some(),
        None => false,
    }
}

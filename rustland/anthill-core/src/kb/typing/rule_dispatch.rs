//! Dispatching calls inside rule bodies: body positions, data-slot hints, call-dispatch
//! shapes and their errors.

use super::*;

/// WI-282 / WI-1026 / WI-1043: recursively rewrite the calls a rule body's dispatch
/// DECIDES — an `Expr::DotApply`, and a DIRECT call on a spec op of either half — to
/// their dispatched form, preserving all non-call structure (`reassemble`'s ptr-eq
/// short-circuit keeps unchanged subtrees allocation-free). A dot or a DEFAULTED call is
/// dispatched as a unit via the typer's own walk (`type_check_node`), which recurses into
/// the receiver — so a nested `?x.a.b` chain dispatches outward-in through one call,
/// never double-visited here. A BODY-LESS call is walked into first and then decided (see
/// the acting arm). A pattern occurrence (`as_expr` = `None`) is left unchanged: a dot in
/// a pattern's type annotation is a TYPE projection, not a value dispatch.
///
/// WI-1026 added the second shape and with it the second REASON. A rule body naming
/// a defaulted spec op directly (`Desc.describe(leaf(), ?r)`) has no dot to trigger
/// the walk, so nothing typed it and nothing ran the WI-444 carrier-override
/// decision on it: the resolver folded `op_body_node(fn_sym)` — the SPEC'S DEFAULT —
/// and MEASURED, a carrier whose implementation arrives by a WI-431 instance fact
/// answered `1` where the same call in an operation body answered the supplied `7`,
/// and a two-supplier TIE answered `1` where the operation body is REFUSED AT LOAD.
/// Routing it through the same `check_apply_iter` keeps the pin and the refusal in
/// ONE owner rather than growing a rule-body copy (058 §3.1/§3.7: dispatch answers
/// by the value, and a read that SELECTS goes loud on the second candidate).
///
/// WI-1043 added the BODY-LESS half — the same rule one guard over
/// (`arbitrate_unarbitrated_supplier_tie` rather than `arbitrate_defaulted_supplier_tie`), and
/// the sentence that used to exclude it was wrong on its own terms: "it has no default to
/// shadow, so `reduce_op_value` leaves it un-ground and the goal residualizes rather than
/// answering wrongly" — residualizing IS the wrong answer. MEASURED, every supply shape
/// answered `[]` from a rule body where the same call in an operation body pins the
/// supplied implementation or is REFUSED at load. The gate is [`spec_op_call_parent`],
/// the union of the two halves, written once in [`defaulted_spec_op_parent`]'s
/// neighbourhood rather than as a fourth spelling (WI-1042).
///
/// WI-1056 took the ERROR POLICY: a body-less atom now reports every failure its
/// type-check finds, not only the two 058 ties of its own call. That is the FIRST rule-body
/// type check the language has ever run, so what it costs was decided site by site rather
/// than assumed — the corpus's 7 reports in 4 files split THREE ways, and only the last is
/// an exemption:
///
///   * **Two were typer gaps, fixed.** An entity CONSTRUCTOR applied in a rule body died as
///     `UnknownApplyFunctor` whenever it was eponymous or free-standing, because this
///     site's gate asked `is_constructor_symbol` where the question is
///     `is_entity_constructor` (`check_apply_iter`, WI-926/WI-1056). And a same-base
///     PARTIAL type application was refused against a fuller one — `Box[T = Int64]` against
///     `Box[T = Int64, U = Bool]` — although the BARE form `Box` was already accepted, both
///     halves of one spec sentence (kernel-language §"Expansion during unification")
///     decided opposite ways ([`parameterized_compatible_view`]).
///   * **One was a source error, fixed at its source.** `stdlib/anthill/prelude/bigint.anthill`'s
///     induction schema wrote bare `0` / `1` where `BigInt` is declared; a small literal is
///     an `Int64` and there is no implicit widening.
///   * **Seven reports at 4 sites were the standing WI-282 exemption**, and stay
///     unreported: an untyped rule-head variable as a dot receiver
///     ([`undecidable_by_this_typer`]).
///
/// WI-1058 WIDENED IT to every `Expr::Apply`, and what made that possible is not more
/// readings but ONE distinction: the walk now knows whether a node is a GOAL or DATA
/// ([`BodyPos`]), so a functor can answer differently in the two positions it is written
/// in. See [`call_dispatch_shape`] for the goal-position ladder,
/// [`data_functor_error`] for why a data slot is NOT type-checked (three measured
/// reasons — lost expectation, lost scope, and a rewrite that changes what the rule
/// means), and `wi1058_rule_body_position_test` for the corrected measurement: the
/// narrowing's own note predicted "two whole readings" split ~220/~150, and the retaken
/// count is 28 subgoals against 295 reports from ONE producer, the loader's synthesized
/// `<Sort>.induction`.
pub(super) fn dispatch_calls_in_occ(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    pos: BodyPos,
    // WI-1058 — the ENCLOSING rule's head functor, for the two checks that report about a
    // node rather than about a call: the message must name the rule whose TEXT the author
    // has to edit, not the callee it names (review-found — every other rule-body site in
    // the typer passes the enclosing symbol). `None` only if the head carries no functor.
    rule_sym: Option<Symbol>,
    // WI-20260904-50B2K part (b) — THE DECLARED TYPE OF THE SLOT THIS NODE WAS WRITTEN
    // IN, when the enclosing DATA term had one to give ([`data_slot_arg_hints`]). `None`
    // at the seed — a rule's top-level atom sits in no slot — and `None` for every child
    // whose parent declares nothing about it, which is what this walk handed every child
    // before this ticket.
    expected: Option<Value>,
    // WI-20260904-50B2K: the DECLARED type of this slot, read straight off the callee's
    // cached signature — the CHECK channel, beside `expected`'s HINT channel. Wider on
    // purpose: every slot with a declaration has one, where a hint is supplied only where
    // imposing a type top-down is correct.
    declared: Option<Value>,
    errors: &mut Vec<TypeError>,
) -> Rc<NodeOccurrence> {
    // ONE predicate for the shapes this walk decides, shared with the pre-scan
    // ([`occ_needs_call_dispatch`]) so a shape walked but not acted on, or acted on
    // but not walked, is impossible. It answers WHICH shape, because the error tail
    // below is not the same for all of them (WI-1043).
    //
    // WI-20260903-FC2X4 — that pairing is why `CallDispatch::BinderForm` was added THERE
    // rather than as an arm of the `match` below. A first cut short-circuited a binder
    // form in this function alone, which left the pre-scan answering `true` for a body
    // whose only dispatch-shaped node sits inside a lambda while this walk did nothing —
    // the "acted on but not walked" case the sentence above says cannot happen. Raised by
    // `/code-review`.
    let shape = occ.as_expr().and_then(|e| call_dispatch_shape(kb, e, pos));
    // WI-1043 — a BODY-LESS spec-op call is walked INTO as well as decided, so every
    // node beneath it keeps the decision and the error policy it had before this
    // ticket; the shape was admitted for a DISPATCH VERDICT, not to take the subtree
    // over. `type_check_node` types the whole atom, and this frame's tail reports only
    // TIES for that shape, so handing it the subtree SWALLOWED two delivered rule-body
    // diagnostics — `eq(?v, ?p.bogus)`'s member-not-found on a KNOWN receiver (WI-282)
    // and `eq(?r, ?b.guarded(0))`'s definite value-precondition violation (WI-602),
    // both raised INSIDE an `eq` atom, which loads as a call on the body-less
    // `PartialEq.eq`. MEASURED as two suite failures, not predicted. The two older
    // shapes do not recurse: `type_check_node` owns their subtree and reports all of it.
    // WI-1056 — where this atom's descendants START reporting. [`already_reported`] is
    // matched against the TAIL from here, never the whole accumulator: `errors` belongs to
    // `type_rule_bodies` and spans every atom of every rule in the batch, and the dedup key
    // is the rendered `(span, message)` — which `TypeError::span` answers `None` for on
    // some variants. Keyed against the whole vector, two genuinely distinct UNLOCATED
    // errors that render alike, in different rules, would collapse to one report and the
    // second would only appear on a later load. The question this guard asks is "did a
    // descendant of THIS node already say it", so the tail is exactly its domain.
    let mark = errors.len();
    let walked = match (shape, occ.as_expr()) {
        // WI-1058 — an UNTYPED position is left entirely alone, subtree included: a
        // discharge's binder tuple `tuple(?f₁, …, ?fₙ)`, and the interior of a type
        // written in a rule body. Neither is a value, so neither is walked — the wrapper
        // is never read as a call on a functor that names nothing, and a type's sort-name
        // leaves are never read as unresolved values.
        (_, _) if pos == BodyPos::Untyped => Rc::clone(occ),
        (Some(CallDispatch::Checked | CallDispatch::BinderForm), _) | (_, None) => Rc::clone(occ),
        (_, Some(expr)) => {
            // Collect child clones first so the immutable borrow on `occ` ends
            // before the mutable-`kb` recursion below.
            let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
            for_each_child(expr, |c| children.push(Rc::clone(c)));
            let child_pos = child_body_positions(kb, expr, pos, children.len());
            // WI-20260904-50B2K part (b) — and WHAT TYPE each slot declares, over the same
            // order and the same length.
            let (child_expected, child_declared) =
                data_slot_arg_hints(kb, shape, expr, children.len());
            // WI-20260904-50B2K — AND WHAT EACH SLOT DECLARES, which is a WIDER list than
            // the hints and answers a different question. A hint is only supplied where a
            // top-down type is CORRECT to impose (a lambda in a callable slot, a call in a
            // ground slot, …), and gating the CHECK on that left every other slot
            // unchecked: measured, `?r <=> addI([], 1)` LOADED in a rule body where its
            // operation-body twin was refused "expected Int64, got List[T = ??T]" — a
            // collection literal is not one of the shapes `apply_arg_hints` hints.
            let new_children: Vec<Rc<NodeOccurrence>> = children
                .iter()
                .zip(child_pos)
                .zip(child_expected)
                .zip(child_declared)
                .map(|(((c, p), e), d)| {
                    dispatch_calls_in_occ(kb, env, c, p, rule_sym, e, d, errors)
                })
                .collect();
            crate::kb::simp_rewrite::reassemble(occ, &new_children)
        }
    };
    let Some(shape) = shape else { return walked };
    // WI-1058 — a SUBGOAL is not a call and has no signature: it is an atom the
    // resolver proves against the clauses its functor heads. Nothing to dispatch, so
    // it never reaches `type_check_node`; what it gets is the check `check_apply_iter`
    // cannot make, which is whether any of those clauses could match it at all.
    let checked_not_typed = match shape {
        CallDispatch::Subgoal => Some(subgoal_shape_error(kb, &walked, rule_sym)),
        CallDispatch::DataTerm => Some(data_functor_error(kb, &walked, rule_sym)),
        _ => None,
    };
    // WI-20260904-50B2K part (b) — `expected` IS DROPPED HERE, and that is not a lost
    // channel: neither of these two shapes ever reaches `type_check_node`, so there is
    // nothing to hand it to. A `Subgoal` has no signature to check against and a
    // `DataTerm` is name-checked only, both for the reasons at their own doc sites.
    if let Some(found) = checked_not_typed {
        if let Some(e) = found {
            if !already_reported(kb, &errors[mark..], &e) {
                errors.push(e);
            }
        }
        return walked;
    }
    // Everything below reads `walked`, never the parameter: for the recursing shape the
    // children may have been rewritten, and both the type-check and the node this returns
    // must see that tree. It is the same `Rc` for the two non-recursing shapes.
    //
    // WI-1104 — and it hands the typer THE POSITION. This walk is the only thing in the
    // language that knows it: it owns goal descent ([`child_body_positions`]), so by the
    // time a node reaches `type_check_node` the answer exists nowhere else. Everything
    // BENEATH the handed-over node is data, which is why [`NodePos`] has two values where
    // [`BodyPos`] has four — the typer never descends into a goal.
    match type_check_node_at(kb, env, &walked, expected, node_pos_of(pos)) {
        // `result.node` is the dispatched tree (method `Apply` / reflect
        // `field_access` / a pinned spec-op `Apply`), re-typed and redex-free —
        // the same form an op body's call rewrites to.
        //
        // WI-1058 — …for the two DISPATCH shapes only. `Call` was admitted to CHECK a
        // fact pattern's fields, not to rewrite it, and `result.node` is redex-free: a
        // goal `V1(v: ite(true, 10, 20))` would be stored as `V1(v: 10)` AT LOAD, which
        // is reason 3 of the three at [`data_functor_error`] — a check that changes what
        // a rule MEANS is not a check. It still returns `walked`, so a dot its children
        // dispatched is kept. Review-found.
        Ok(result) => {
            // WI-20260904-50B2K — AND THE HINT IS NOW CHECKED, not only supplied.
            //
            // Part (b) carried a callee's declared slot type down as an EXPECTATION and
            // stopped there, which left the rule-body spelling accepting a child whose
            // WHOLE TYPE contradicts the slot — measured by `/code-review` as a WRONG
            // VALUE, not a missing refusal: `apply1(lambda x -> "no", 2)` loaded and
            // answered a `String` from a call declared `-> Int64`, while its
            // operation-body twin was refused. The binder half was already closed (the
            // hint types the binder, so the body's own calls are checked); this is the
            // whole-arrow half, which in an operation body is the argument POSITION and
            // which a rule-body data term has no site for (WI-1058).
            //
            // A FRESH σ, AND THAT IS NOT A FAIL-OPEN — the objection this fix was first
            // filed as a ticket for, then measured. `validate_arg_against_param` GATES on
            // groundness ("everything above this line treats 'not ground' as 'not mine to
            // decide'"), so a generic callee whose declared param type is its own type
            // parameter reaches that gate unresolved and is WITHHELD, which is exactly the
            // subset a fresh σ can answer. Driven both ways: the concrete slot is refused
            // with "expected Function[A = Int64, B = Int64], got Int64 -> String", while
            // `pick[X](f: Function[A = X, B = X], v: X)` still loads.
            //
            // IT IS THIS FUNCTION AND NOT A BARE `types_compatible`, so the three
            // conversions an operation body's argument gets ACCEPT the same values here:
            // the reflect-`Term` escape, WI-408's some-coercion and the provider-admissible
            // carrier. A narrower comparison would refuse programs the op-body spelling
            // accepts — inventing the asymmetry this ticket exists to remove, and
            // `control_a_non_callable_slot_hints_a_rule_body_lambda_with_nothing` is the
            // row that measures it (a lambda in a reflect `Term` slot, which a bare
            // `types_compatible` would refuse). ACCEPTANCE ONLY: see the `WrapSome` arm
            // below for the conversion whose REWRITE this site does not perform.
            //
            // ONLY WHERE THE CALLEE DECLARED SOMETHING — `declared`, NOT the hint, and
            // that is the wider of the two lists on purpose. Gating the check on the HINT
            // left every slot `apply_arg_hints` correctly says nothing about unchecked: a
            // lambda in an `Int64` slot loaded in a rule body and was refused in an
            // operation body (`a_lambda_in_a_non_callable_slot_is_refused_in_both_bodies`).
            // A slot with no DECLARATION still gets no check.
            //
            // THE THIRD CONJUNCT IS REPORT-ONCE. If anything beneath this node already
            // complained, that complaint IS this slot's error said at the place the author
            // must look, and adding a second one makes the rule-body spelling report TWO
            // where the operation body reports one — measured on the first cut of the
            // wider version, `wi1056::the_rule_body_and_the_operation_body_report_the_same_error`.
            // `already_reported` cannot do it: it matches on (span, text), and these two
            // differ in both.
            //
            // THE CONTEXT NAMES THE RULE, NOT THE SLOT (`value.body (rule)` where the
            // op-body twin says `apply1.f (op-arg)`), and that is a known shortfall rather
            // than a decision: pairing each hint with its PARAM symbol means threading
            // `apply_arg_hints`' internal positional-to-field ranking (WI-20260827-1F0QP's
            // rank-among-NOT-named rule) out through this channel. The error locates the
            // same span either way.
            if let (Some(exp), Some(rs), true) = (declared.as_ref(), rule_sym, errors.len() == mark)
            {
                let mut sigma = Substitution::new();
                match validate_arg_against_param(
                    kb,
                    &mut sigma,
                    &result.ty,
                    exp,
                    Some(walked.span.span),
                    TypeErrorContext::Rule {
                        name: rs,
                        field: RuleField::Body,
                    },
                    Some(&result.node),
                ) {
                    ArgValidation::Fail(e) => errors.push(e),
                    // ACCEPTED, AND THE ACCEPT IS ALL THIS SITE CLAIMS — spelled out
                    // rather than folded into the `Ok` arm, because /code-review read the
                    // comment above as promising the some-INSERTION too. It does not: the
                    // WI-408 rewrite wraps the ARGUMENT OCCURRENCE and belongs to
                    // `check_apply_iter`, which is the pass a rule-body data term does not
                    // get (WI-1058). So a rule body stores the bare value in an
                    // `Option[T = …]` slot where an operation body stores `some(…)` — a
                    // REWRITE asymmetry this check does not close and does not pretend to.
                    // Not silently dropped: `Ok` and `WrapSome` are the same verdict for
                    // the question asked here, which is only "does this conform".
                    ArgValidation::Ok | ArgValidation::WrapSome { .. } => {}
                }
            }
            if shape != CallDispatch::Call {
                result.node
            } else {
                walked
            }
        }
        // Every failure is a REAL error — surface it, never a silent skip
        // (project principle: loud over silent; the `Err(_) => Rc::clone(occ)`
        // catch-all this replaced masked genuine errors — a member-not-found on
        // a KNOWN receiver [`?p.bogus`], a WI-602 DEFINITE value-precondition
        // violation [`?b.guarded(0)`], any type / arity / effect mismatch inside
        // the dispatched form). A rule-body FLOAT is NOT one of these: the
        // WI-557/602 gate skips it, so `check_apply_iter` returns `Ok` and the
        // call dispatches clean (`rule_body_value_precondition_dot_dispatches`).
        // The node is left in place so downstream still sees an un-rewritten one.
        //
        // …except [`undecidable_by_this_typer`], and — for the RECURSING shape —
        // what a descendant has already reported ([`already_reported`]).
        Err(e) => {
            match shape {
                // Owns its whole subtree and does not recurse, so `mark` is its own
                // start and there is nothing beneath it to have reported already.
                // WI-20260903-FC2X4 — `BinderForm` shares this arm and shares its reason:
                // it does not recurse either, so `mark` is its own start and there is
                // nothing beneath it to have reported already.
                CallDispatch::Checked | CallDispatch::BinderForm => {
                    debug_assert_eq!(
                        mark,
                        errors.len(),
                        "a non-recursing shape reported nothing yet"
                    );
                    // LEAF BY LEAF, then RE-AGGREGATED — not `undecidable_by_this_typer`
                    // asked of the whole error.
                    //
                    // WI-880 — this arm used to ask it of `e` itself, which matches only a
                    // BARE exempt error. `collect_arg_errors` hands back one failing
                    // argument's error unwrapped and TWO as a `Multiple`, so the exemption
                    // held for one exempt argument and silently lapsed for two. That was
                    // latent while the arithmetic ops had no default body: `?dx =
                    // ?p1.position.x - ?p2.position.x` (`safety_common.anthill:277`, the
                    // very site `undecidable_by_this_typer`'s doc names) reached the
                    // BodyLessSpecOp arm, which flattens. Giving `Additive.sub` a default
                    // body moves `-` to THIS arm ([`call_dispatch_shape`] routes a
                    // defaulted spec op here), and the two unresolved receivers were
                    // refused — 15 tests, the corpus among them.
                    //
                    // RE-AGGREGATED with `aggregate_errors` rather than pushed as leaves,
                    // so this shape keeps pushing ONE report per call where it has one to
                    // make: a lone survivor stays unwrapped (which is the case that always
                    // worked) and several stay one `Multiple`, which is what
                    // `already_reported` flattens for.
                    let kept: Vec<TypeError> = e
                        .flatten()
                        .into_iter()
                        .filter(|leaf| !undecidable_by_this_typer(leaf))
                        .collect();
                    if !kept.is_empty() {
                        errors.push(aggregate_errors(kept));
                    }
                }
                // WI-1056 — the widening. WI-1043 admitted this shape for a dispatch
                // VERDICT and reported only the two 058 ties of its own call, because
                // reporting the rest refused the corpus; the corpus is now clean (see
                // this function's doc for what had to be fixed to make it so), so the
                // shape reports what type-checking actually found. LEAF BY LEAF rather
                // than as one `Multiple`: this frame types a WHOLE ATOM whose parts were
                // decided separately, so the aggregate is not one call's diagnostic.
                //
                // WI-1058 — `Call` shares this arm, and shares it because it shares the
                // reason: it too recurses first (so a descendant may already have
                // reported the same leaf) and it too types a whole node whose parts were
                // decided separately. One arm rather than two identical ones, so a change
                // to the policy cannot reach one shape and miss the other.
                CallDispatch::BodyLessSpecOp | CallDispatch::Call => {
                    for leaf in e.flatten() {
                        if undecidable_by_this_typer(&leaf)
                            || already_reported(kb, &errors[mark..], &leaf)
                        {
                            continue;
                        }
                        errors.push(leaf);
                    }
                }
                // Returned early above — neither reaches `type_check_node`.
                CallDispatch::Subgoal | CallDispatch::DataTerm => {
                    unreachable!("a checked-not-typed shape is decided before this match")
                }
            }
            walked
        }
    }
}

/// WI-1058 — WHERE in a rule body a node sits, which decides HOW it is read. The
/// distinction the typer lacked until this ticket, and the whole of what made the
/// general `Expr::Apply` unwidenable: **one name answers two questions depending on the
/// position it is written in**, and a walk that cannot tell the positions apart must
/// take one reading for both.
///
/// The live case is `anthill.reflect.Expr.ho_apply`. In a rule body it is the
/// higher-order-application BUILTIN (`BuiltinTag::HoApply`, variadic: a predicate and
/// the arguments to apply it to) — the form the loader's synthesized `<Sort>.induction`
/// is written in, and the form `SearchStream::lower_ho_apply` reads. As a VALUE it is
/// the reflect IR entity `ho_apply(predicate: Term, args: List[Term], type_args: …)`,
/// the node an operation body's `?P(a, b)` reflects to. Typing the goal against the
/// entity checks the applied argument against `List[T = Term]` and refuses it: 271 of
/// the 323 reports a position-blind widening produced, all from one producer.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum BodyPos {
    /// A goal the resolver proves or assumes — a rule's top-level body atom, and the
    /// `Proved` / `Assumed` slots of a connective beneath it. The [`GoalCommit`] says
    /// whether a DEAD goal here is a defect worth refusing.
    Goal(GoalCommit),
    /// A `tuple(…)` CONJUNCTION WRAPPER slot: the node here is the wrapper, and its
    /// positional children are the goals. A node in this position that is NOT a `tuple`
    /// is a single goal — the same defensive reading `KnowledgeBase::tuple_goal_children`
    /// takes, since the loader wraps every such body.
    ///
    /// A position rather than a name test at the node, and that is WI-1046's rule: a
    /// USER predicate locally named `tuple` is recognised as a wrapper only where the
    /// slot table put one, never by its spelling.
    GoalTuple(GoalCommit),
    /// Data — a goal's argument, and everything beneath it.
    Value,
    /// A term this typer does not type, and does not walk into. TWO producers, listed
    /// because the position is only as trustworthy as the list is complete:
    ///
    ///   * the variables a quantifier / discharge scopes ([`SlotReading::Binders`]) —
    ///     `forall_impl`'s `tuple(?f₁, …, ?fₙ)`;
    ///   * everything inside a TYPE written in a rule body
    ///     ([`rule_body_type_term`]) — `PartialEq[T = ?t]`, `List[T = ?x]`, `(?a ->
    ///     ?b)`. A type is a term (this repo's representation note), its leaves are
    ///     type names rather than values, and it is checked where it is BUILT
    ///     (`check_sort_type_args`, WI-710) rather than here.
    Untyped,
}

/// WI-1104 — the [`NodePos`] the typer is handed for a node this walk reaches at `pos`.
///
/// The projection is total and deliberately COARSE: the typer's only question is
/// "may this call be written at the operation's arity + 1", which is the FUNCTIONAL-
/// RELATION view (§5.3, WI-938) and belongs to a goal. [`GoalCommit`] does not enter it
/// — a *tolerated* dead goal is still a goal, and the relational spelling is legal in a
/// bare `or` branch exactly as it is at the top level. `Untyped` never reaches the
/// typer at all ([`dispatch_calls_in_occ`] returns before the type-check), so its row
/// here is unreachable-but-total rather than a reading.
fn node_pos_of(pos: BodyPos) -> NodePos {
    match pos {
        BodyPos::Goal(_) | BodyPos::GoalTuple(_) => NodePos::RuleBodyGoal,
        BodyPos::Value | BodyPos::Untyped => NodePos::Value,
    }
}

/// WI-1058 — is a DEAD goal at this position a defect this walk refuses, or one it leaves
/// to resolution?
///
/// The question is WI-863's and the answer is WI-1034's, re-asked here because the two
/// checks must not disagree about one position. `KnowledgeBase::undefined_rule_body_goals`
/// REFUSES a goal that names nothing at the body's top level and anywhere inside a `not`,
/// and TOLERATES one in a bare `or` / `push_choice` branch, in a bounded-quantifier body,
/// and anywhere inside a hereditary-Harrop discharge — each for a reason that transfers
/// verbatim to a goal that no clause can match by SHAPE:
///
///   * a bare disjunction branch or a quantifier body may never need to answer, so a dead
///     one costs nothing and refusing it rejects a valid program;
///   * a discharge's antecedents DECLARE the predicates its consequent proves, so a
///     hypothesis has no clause anywhere and its shape is whatever the discharge says.
///
/// MEASURED, both of them, in review: without this, `(forall(?p), prop(?p) -: prop(?p))`
/// beside a `fact prop(1, 2)` was refused TWICE — a program §5.3 legislates — and
/// `(q(?a) | q(?a, ?a))` was refused while `(q(?a) | absent(?a))` loaded, two dead
/// branches decided oppositely by two checks.
///
/// The walk still DESCENDS everywhere (a dot inside a tolerated branch must still
/// dispatch, and a data slot there must still be name-checked); what this gates is the
/// subgoal SHAPE check alone.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum GoalCommit {
    /// A rule's own top-level body atom. Checked — and its goal children are NOT, unless
    /// it is a `not` (WI-863's descent rule exactly).
    Top,
    /// Reached through a `not`, or through a connective already inside one. Checked, and
    /// so are its goal children.
    UnderNot,
    /// Reached through a bare `or` / `push_choice` / quantifier, or through a discharge.
    /// Walked, never shape-checked.
    Tolerated,
}

impl GoalCommit {
    /// Is a goal at this position one whose deadness this walk refuses?
    pub(super) fn checked(self) -> bool {
        matches!(self, GoalCommit::Top | GoalCommit::UnderNot)
    }

    /// The commitment a GOAL CHILD of a node at `self` inherits, given what that node is.
    /// WI-1034's `collect_undefined_body_goals` gate, verbatim: a `not` opens the scope,
    /// a discharge closes it, and a bare connective leaves its branches to resolution.
    ///
    /// A CONJUNCTION PASSES ITS COMMITMENT THROUGH UNCHANGED, and that is not a fourth
    /// rule but the same one: the reason a bare `or` branch is tolerated is that it may
    /// never need to answer, and a CONJUNCT always does — if it is dead the whole
    /// conjunction is. `a, b` and `a & b` must therefore be equally committed, and
    /// before `push_and` gave `and` a goal reading (WI-20260822-J38JE) they were not:
    /// MEASURED, `l(?x), absent(?x)` was refused and `l(?x) & absent(?x)` loaded clean.
    pub(super) fn child(self, is_not: bool, is_discharge: bool, is_conjunction: bool) -> Self {
        if is_discharge {
            return GoalCommit::Tolerated;
        }
        if is_conjunction {
            return self;
        }
        if self == GoalCommit::UnderNot || is_not {
            GoalCommit::UnderNot
        } else {
            GoalCommit::Tolerated
        }
    }
}

/// WI-1058 — the [`BodyPos`] of each child of `expr`, parallel to
/// [`for_each_child`]'s order, for a node itself reached at `pos`.
///
/// Everything is `Value` unless the node is a GOAL-position application that the ONE
/// slot table ([`KnowledgeBase::goal_slot_readings`]) answers for — which is what keeps
/// a data constructor's fields, and every argument of an ordinary subgoal, out of goal
/// position. Read from that table rather than written here, so the typer is not a fourth
/// hand-written copy of "which arguments are goals" (WI-1034/WI-1046).
pub(super) fn child_body_positions(
    kb: &KnowledgeBase,
    expr: &Expr,
    pos: BodyPos,
    n_children: usize,
) -> SmallVec<[BodyPos; 8]> {
    // A TYPE's interior is a type: its "arguments" are type arguments and its leaves are
    // sort names, neither of which has a value reading. Asked before the slot table so a
    // sort that happens to share a connective's short name cannot open a goal position
    // inside a type.
    if pos == BodyPos::Untyped || rule_body_type_term(kb, expr) {
        return smallvec::smallvec![BodyPos::Untyped; n_children];
    }
    let mut out: SmallVec<[BodyPos; 8]> = smallvec::smallvec![BodyPos::Value; n_children];
    // A BINDER'S PATTERN is not data. In an operation body these arrive as Pattern-kind
    // occurrences, which `as_expr` answers `None` for and the walk already skips; a RULE
    // body was materialized from a term, so the same pattern arrived as a structural
    // `Expr::Apply` on the parse-level meta-functor (`pattern_var`, `pattern_wildcard`,
    // …) — names the KB declares nothing under, by design. MEASURED on `rule all_pos(?xs)
    // :- all_match(?xs, lambda (x) -> is_pos(x))`, which reported `pattern_var` as an
    // unknown functor (`wi620_paren_lambda_param_test`).
    //
    // WI-20260903-FC2X4 — THE RULE-BODY HALF OF THAT IS HISTORY, and the marking is kept
    // for the reason it was written rather than for the shape it described. A rule's
    // compound expressions are now lowered by the walk that owns their layout, so a rule
    // body's binder pattern IS a `NodeKind::Pattern` and the `as_expr` skip above already
    // covers it. What still reaches here as an `Expr::Apply` on a marker functor is a
    // binder the delegation did not build — a reflect form the AUTHOR wrote, or a form
    // reached at a position the delegation declines — and for those the marking is the
    // only thing keeping a meta-functor out of the value walk.
    for i in pattern_child_indices(expr) {
        if let Some(p) = out.get_mut(i) {
            *p = BodyPos::Untyped;
        }
    }
    let (
        Expr::Apply {
            functor, pos_args, ..
        },
        BodyPos::Goal(commit) | BodyPos::GoalTuple(commit),
    ) = (expr, pos)
    else {
        return out;
    };
    // The wrapper: its positional children ARE the conjuncts, at the wrapper's own
    // commitment (a `tuple` is a punctuation node, not a connective that changes what a
    // dead goal costs). Asked only here, where the slot table said a wrapper belongs.
    if matches!(pos, BodyPos::GoalTuple(_)) && kb.local_name_of(*functor) == "tuple" {
        for p in out.iter_mut().take(pos_args.len()) {
            *p = BodyPos::Goal(commit);
        }
        return out;
    }
    // WI-1034's descent gate, re-asked per child (see [`GoalCommit::child`]).
    let child_commit = commit.child(
        kb.builtin_of(*functor) == Some(crate::kb::resolve::BuiltinTag::Not),
        kb.local_name_of(*functor) == "forall_impl",
        kb.is_goal_conjunction(*functor, pos_args.len()),
    );
    // `for_each_child` yields `pos_args` first, so a slot index is a child index.
    for slot in kb.goal_slot_readings(*functor, pos_args.len()) {
        let Some(p) = out.get_mut(slot.index) else {
            continue;
        };
        *p = match (slot.reading, slot.tuple_wrapped) {
            (crate::kb::SlotReading::Binders, _) => BodyPos::Untyped,
            (_, true) => BodyPos::GoalTuple(child_commit),
            (_, false) => BodyPos::Goal(child_commit),
        };
    }
    out
}

/// WI-20260904-50B2K part (b) — the top-down TYPE HINT for each child of a rule-body
/// DATA term, in [`for_each_child`] order and of the same length as
/// [`child_body_positions`].
///
/// THE `None` THIS CLOSES. WI-1058 does not type-check a `DataTerm` node
/// ([`data_functor_error`] states the three measured reasons), so a child it walks into
/// was typed with `expected: None` — and for a LAMBDA that is the difference between
/// having a binder type and not. `?r <=> apply1(lambda x -> x, 2)` gives the binder no
/// evidence of its own; only `apply1`'s declared `f: Function[A = Int64, B = Int64]` says
/// what `x` is, and until now nothing carried it one level down. The same `None` decided
/// the binder LABELS: [`bind_and_label_pattern`] takes a tuple pattern's labels from the
/// expected type (WI-803), so `apply2(lambda (a, b) -> a - b, (b: 2, a: 1))` had none and
/// zipped its binders to the LITERAL's source order — a WRONG VALUE, not an absent one,
/// which is what
/// `wi_50b2k_binder_inference_test::part_b_a_permuted_named_tuple_binds_a_rule_body_lambdas_binders_by_name`
/// measures (it stood as a `known_gap_` row in `wi_qqpq2_tuple_carrier_test` until this
/// change closed it).
///
/// **NOT A TYPE-CHECK OF THE PARENT, and the distinction is exactly WI-1058's three
/// reasons.** Those are about handing the DATA NODE to `check_apply_iter`: it would lose
/// the node's own expectation, be typed outside its binders' scope, and have its subtree
/// REWRITTEN redex-free into the stored rule. None of that happens here — the parent is
/// still only name-checked, its children are still walked by this walk under the scoping
/// it already had, and nothing is rewritten that was not rewritten before. What crosses
/// is one DECLARED TYPE per slot, read off the callee's signature.
///
/// **ONE OWNER FOR "WHAT DOES THIS SLOT HINT".** The hints come from
/// [`apply_arg_hints`], the same function an OPERATION body's call uses, so a rule-body
/// and an operation-body spelling of one call cannot come to hint differently — which is
/// the asymmetry this ticket exists to remove. That also inherits its narrowness for
/// free: only a lambda / bare reference in a callable slot ([`hof_arg_hint`]), a call in
/// a ground slot, a sort name in a `Type` slot, and a constructor application in a
/// variant slot get anything at all; every other child still gets `None`.
///
/// **IT ADDS NO REWRITING, and that is worth saying because WI-1058's third reason is a
/// rewrite.** A hint is consumed only by a child this walk hands to `type_check_node_at`
/// — a `Checked` dot, a `BodyLessSpecOp`/`Call` atom, a `BinderForm` — and three of those
/// four already STORE the re-typed node ([`dispatch_calls_in_occ`]'s `Ok(result) if shape
/// != CallDispatch::Call`), hint or no hint. A `DataTerm` and a `Subgoal` never reach the
/// typer at all, so the hint computed for them is dropped. What an expectation can change
/// is therefore WHICH rewrite an already-rewriting shape produces — a WI-408 some-coercion
/// where the slot is `Option[T = …]`, say — and it changes it toward the reading the same
/// call written in an operation body already gets. `holds(ite(true, 10, 20))` becoming
/// `holds(10)` is the hazard that reason names, and it is a `@[simp]` REDEX fold on a shape
/// this hint cannot reach.
///
/// `known` is EMPTY here, and that is not a stub: it is the map of sibling argument types
/// [`check_apply_iter`] fills from typed results, and this walk has typed no siblings.
/// Its two readers ([`hint_instantiation_subst`], [`bind_spec_params_for_hint`]) both
/// return nothing for an empty map, so a hint that would need a sibling's type is simply
/// not made — the declared type rides through as written.
/// WI-20260904-50B2K — TWO LISTS, ONE SIGNATURE READ, and they answer DIFFERENT
/// questions about the same slots:
///
///   * `.0` THE HINT — what to IMPOSE on this child before typing it. Narrow on purpose
///     (see the paragraphs above): a top-down type is only correct at a handful of shapes.
///   * `.1` THE DECLARATION — what the callee DECLARED here, which every slot with a
///     signature has. This is the CHECK channel, and it is deliberately wider: gating the
///     check on the hint left a collection literal in an `Int64` slot unchecked, so
///     `?r <=> addI([], 1)` loaded where its operation-body twin was refused.
///
/// RETURNED TOGETHER rather than from two functions, which is a cost decision AND a
/// correctness one — /code-review. The `op_record` map lookup and the `params.clone()` are
/// paid ONCE per data term instead of twice on the rule-body hot path, and the two lists
/// cannot come to read a different signature or a different slot mapping, since there is
/// only one of each.
fn data_slot_arg_hints(
    kb: &mut KnowledgeBase,
    shape: Option<CallDispatch>,
    expr: &Expr,
    n_children: usize,
) -> (SmallVec<[Option<Value>; 8]>, SmallVec<[Option<Value>; 8]>) {
    // Asked before anything is allocated: this runs at EVERY recursing node of every rule
    // body, and only a data term has a declaration to read.
    if shape != Some(CallDispatch::DataTerm) {
        return (
            smallvec::smallvec![None; n_children],
            smallvec::smallvec![None; n_children],
        );
    }
    let unhinted: SmallVec<[Option<Value>; 8]> = smallvec::smallvec![None; n_children];
    let nothing = || (unhinted.clone(), unhinted.clone());
    let Expr::Apply {
        functor,
        pos_args,
        named_args,
        ..
    } = expr
    else {
        return nothing();
    };
    // THE HINT READS AN OPERATION'S PARAMETERS AND DELIBERATELY NOT AN ENTITY'S FIELDS;
    // THE CHECK READS BOTH. Why the two lists part, and what measured it, is stated where
    // they actually part — at the `or_else` below.
    //
    // READ OFF THE CACHED SIGNATURE, NOT THROUGH [`lookup_operation_info_full`], and that
    // is a cost decision with teeth rather than a style one: that function's fast path is
    // the same `op_record` map read, but a symbol with NO record falls through to a
    // LINEAR SCAN of every `OperationInfo` fact — and "no record" is every data term
    // headed by an entity or a plain predicate, which is most of what a rule body is made
    // of. The map read is the gate `type_rule_bodies`' goal walk already calls "cheap map
    // lookup" at its own version of this question. Post-WI-1082 the cache is also the
    // AUTHORITY, not just the accelerator (`elaborate_self_ties` rewrites it), so reading
    // it is what keeps this hint agreeing with the call check.
    let op_params: Option<Vec<(Symbol, Value)>> = kb
        .op_record(*functor)
        .and_then(|r| r.signature.as_ref())
        .map(|sig| sig.params.clone());
    // THE CHECK READS AN ENTITY'S FIELDS TOO; THE HINT DOES NOT — and the two lists part
    // here rather than sharing one `params`, which is the whole reason they are computed
    // together. A HINT imposes a type before the child is typed, and the constructor chain
    // has no lambda arm (`arrow_slot_arg_hint` reads a bare operation NAME), so hinting an
    // entity field would make a build behave differently from its operation-body twin —
    // this ticket's own asymmetry pointing the other way. A CHECK imposes nothing: it
    // compares what the child turned out to be against what the field DECLARES, which is
    // exactly what the operation-body spelling of the same build already does.
    //
    // THE HINT CHAINS ARE NOT THE SAME ONE, which is why only the CHECK widens: a
    // constructor's fields hint through [`arrow_slot_arg_hint`] and the `*_from_ctor`
    // readings, which have no lambda arm at all — [`hof_arg_hint`] is the operation
    // chain's. Running an entity's fields through THAT chain would hint a rule-body
    // constructor's lambda field where the operation-body spelling hints nothing, which is
    // this ticket's own asymmetry pointing the other way.
    //
    // MEASURED, and the row that pinned the old SYMMETRIC gap is what caught it: once the
    // arrow began reflecting its body (part (c)'s first slice),
    // `runit(holder(f: lambda x -> takes_str(x)), 2)` was refused in an operation body and
    // still LOADED in a rule body — that row failing on its `entop` arm alone, which is
    // precisely the "if only one does, an asymmetry has been created" its own message
    // warned about. Now pinned by `wi_50b2k_binder_inference_test::
    // an_entity_field_lambda_is_refused_in_both_bodies_once_its_body_pins_the_binder`.
    //
    // `op_params` IS CLONED ONCE MORE HERE and that is the cheap half of the trade: the
    // alternative is reading the signature twice, which this function exists to avoid.
    let Some(params) = op_params
        .clone()
        .or_else(|| kb.entity_field_types(*functor).map(|f| f.to_vec()))
    else {
        return nothing();
    };
    let (pos_hints, named_hints) = apply_arg_hints(
        kb,
        *functor,
        op_params.as_ref(),
        &None,
        pos_args,
        named_args,
        &HashMap::new(),
    );
    let out: SmallVec<[Option<Value>; 8]> = pos_hints.into_iter().chain(named_hints).collect();
    // ASSERTED, NOT PADDED. `for_each_child` yields `pos_args` then `named_args` and
    // `apply_arg_hints` returns them in that order, so the two lists are aligned by
    // construction — and a `resize` here would keep them aligned by SLIDING, which is how
    // a hint silently lands on the wrong slot. If an `Expr::Apply` ever grows a child that
    // is not one of its arguments, this is where the walk must be told about it.
    // `assert_eq!`, NOT `debug_assert_eq!` — /code-review found the release hole. The
    // caller zips `children`, `child_pos` and this list, and a `zip` TRUNCATES to the
    // shortest: a short hint list would silently drop the tail children from the walk,
    // and a long one would reach `reassemble` and panic out of bounds inside
    // `ChildCursor::take` with nothing naming this site. Two `usize`s, once per data term.
    assert_eq!(
        out.len(),
        n_children,
        "WI-20260904-50B2K: a data term's hint list must be its child list, one per slot",
    );
    // AND THE DECLARATIONS, over the same `params` and through the CALL PATH'S OWN slot
    // owners — [`positional_param_indices`] (the rank-among-NOT-named rule,
    // WI-20260827-1F0QP) and [`match_named_arg_param`] (a written label against a
    // possibly-qualified parameter, by `same_label`). A raw index zip here was this
    // channel's first cut and was WRONG, driven: a named argument CONSUMES a parameter, so
    // in `f3(lambda x -> x, a: 1)` over `f3(a: Int64, b: Function[…])` the lambda is
    // parameter `b`, and reading `params[0]` compared it against `a: Int64` and REFUSED a
    // program its operation-body twin accepts — the exact asymmetry this ticket exists to
    // remove, created by the check meant to close one. `Symbol` equality for the named
    // lookup was the same defect quieter: it finds nothing and SKIPS the check.
    let slots = positional_param_indices(kb, &params, pos_args.len(), named_args);
    let declared: SmallVec<[Option<Value>; 8]> = slots
        .iter()
        .map(|slot| slot.and_then(|i| params.get(i)).map(|(_, t)| t.clone()))
        .chain(
            named_args
                .iter()
                .map(|(name, _)| match_named_arg_param(kb, &params, *name).map(|(_, t)| t.clone())),
        )
        .collect();
    assert_eq!(
        declared.len(),
        n_children,
        "WI-20260904-50B2K: a data term's declared-type list must be its child list, \
         one per slot"
    );
    (out, declared)
}

/// WI-1058 — the child indices of `expr` (in [`for_each_child`] order) that hold a
/// binding PATTERN rather than a value. Kept beside `for_each_child`'s arms in spirit:
/// every constructor that binds is listed, so a new binder form is a visible omission
/// here rather than a silent mis-typing of its pattern.
fn pattern_child_indices(expr: &Expr) -> SmallVec<[usize; 4]> {
    let mut out = SmallVec::new();
    match expr {
        // `f(pattern)` / `f(pattern, body)` — the pattern is child 0. `LambdaWithin` is
        // the requirement-carrying form of the same binder (WI-222/WI-237) and binds
        // identically; review-found, and the reason this list is written out rather than
        // derived is that a missing row is silent.
        Expr::Lambda { .. } | Expr::Let { .. } | Expr::LambdaWithin { .. } => out.push(0),
        // `scrutinee`, then per branch: pattern, body, and a guard when present.
        Expr::Match { branches, .. } => {
            let mut i = 1;
            for b in branches.iter() {
                out.push(i);
                i += 2 + usize::from(b.guard.is_some());
            }
        }
        _ => {}
    }
    out
}

/// WI-1058 — is this rule-body node an ARROW TYPE, whose interior is type-land?
///
/// A rule body's argument slots hold TERMS, and in this language a type IS a term with
/// logical variables in it — `?t <=> (?a -> ?b)`, `?t <=> (Int64 -> Int64 @ {})`. The
/// arrow family ([`crate::parse::pratt::is_arrow_functor`], the ONE owner of "which
/// spellings `->`/`@` mint") is minted by the pratt desugar and declared NOWHERE, so the
/// data-slot name check ([`data_functor_error`]) would report every arrow type as a name
/// that resolves to nothing. Its interior is types too — sort names, type variables,
/// effect rows — so the whole subtree is [`BodyPos::Untyped`].
///
/// **NARROW ON PURPOSE, and the first cut was not.** It also answered `true` for any
/// `has_kind(Sort)` functor, to keep a parameterized type application (`Holder[T =
/// Int64]`) out of the walk. That was a real requirement of an earlier design — one that
/// TYPE-CHECKED a data slot — and it survived into a design that does not, where it was
/// no longer paying for anything and was silently WIDE: an eponymous `sort E { entity
/// E(…) }` and a free-standing `entity E(…)` both carry `Sort` (WI-926), so every
/// constructor written in a data slot switched the walk off for its whole subtree.
/// MEASURED by driving the two spellings side by side: `here1(V1(v: bogusA(?x)))` was
/// refused and `here1(K1(v: bogusB(?x)))` — differing only in that `K1` is free-standing
/// — loaded clean, and a `?p.bogusmember()` dot inside one stopped being dispatched at
/// all. Found in review; the sort reading it was standing in for now lives where it
/// belongs, as a GOAL-position rung in [`call_dispatch_shape`] (an instance CLAIM is not
/// a subgoal), and a sort-headed term in a data slot is an ordinary
/// [`CallDispatch::DataTerm`] whose functor resolves.
fn rule_body_type_term(kb: &KnowledgeBase, expr: &Expr) -> bool {
    let Expr::Apply { functor, .. } = expr else {
        return false;
    };
    crate::parse::pratt::is_arrow_functor(kb.local_name_of(*functor))
}

/// WI-282 / WI-1056 — the deliberately-tolerated failures, asked at both places
/// [`dispatch_calls_in_occ`] can meet one: on a `Checked` shape's whole error, and on each
/// LEAF a recursing body-less atom's type-check produced. Two spellings of an exemption is
/// how an exemption silently stops applying — the leaf form is the one WI-1043's narrow
/// policy never had to ask, and it is exactly where the corpus lives.
///
/// Both are cases the typer CANNOT decide rather than cases it declines to report, and
/// both hold a status quo that predates the widening. There are two, and no more:
///
/// **An UNRESOLVED dot receiver** (`receiver_sort: None`, WI-282) is not a value dispatch
/// we can decide — either a polymorphic body var with no constraining goal (`rule f(?d,
/// ?p1, ?p2) :- ?dx = ?p1.position.x - …`: a rule head declares no types, so `?p1` HAS no
/// sort at load), or (load-bearing) the reflect `Expr.dot_apply` CONSTRUCTOR carried as
/// data in a rule body (an `Expr` induction principle / reflection rule), which
/// `materialize_from_handle` collapses to `Expr::DotApply` via the WI-425 isomorphism.
/// Erroring there would reject every program defining such a sort; leave it untouched (the
/// pre-WI-282 status quo — the dot flows to SLD structurally). This is the sole case where
/// a `DotApply` legitimately survives type-check. MEASURED as the whole of what WI-1056's
/// widening would otherwise have newly refused in the corpus once the three real defects
/// were fixed: 7 reports at 4 sites, all in
/// `examples/webots-modelling/lf1/safety_common.anthill` (`?p1.position`,
/// `?pose_prev.roll`), every one an untyped rule-head variable.
///
/// **An EQUATION-INTRODUCED functor applied in a rule body** (WI-898's question asked on
/// the rule-body side; see `check_apply_iter`'s arm for where it is raised and why it must
/// stay an `Err`). `ite` is the live case and it is not an accident of the stdlib:
/// `bool.anthill` argues that `ite` CANNOT be an operation, because an operation would
/// evaluate both branches. So there is no signature to check the call against, and its
/// `@[simp]` clauses give a type only per redex — the typer has no reading, and inventing
/// one is worse than having none (measured: a fresh type var unpinned the enclosing `=`
/// goal's carrier and refused the program for ambiguous dispatch instead). Reporting it
/// would refuse `rule clamp(?x, ?r) :- ?r = ite(gte(?x, 0), ?x, 0)`, a program smt-gen
/// lowers to `(ite …)` today, and whose twin in a rule HEAD this walk never even visits.
/// The exemption is on the RESOLVED functor: a bare `ite` with no `import
/// anthill.prelude.Bool.{ite}` interns bare, carries no kind, and is still refused —
/// correctly, since without the import it reaches none of the `@[simp]` rules either.
///
/// APPLIED TO BOTH SHAPES, and that was questioned in review as an unmeasured extension —
/// it is deliberate, and here is the case. `rule r(?v, ?c) :- ?v = Wv(n: 1).foo(ite(?c, 1,
/// 0))` puts the same untypeable functor in an argument of a DOT on a KNOWN receiver: that
/// dot is a `Checked` shape, `collect_arg_errors` hands back its one failing argument's
/// error unwrapped, and without the exemption on this side the program is refused for a
/// reason that is not about the dot. It is the same expression in the same position as the
/// body-less case, so one exemption covers it. What that costs is real and worth naming:
/// the enclosing call is then not checked or dispatched either, because its argument has
/// no type.
///
/// WHAT IT DOES NOT CHECK, stated rather than left to be discovered: nothing about the
/// call's TYPE survives. WI-1058 took the ARITY half, which this paragraph used to
/// concede as well ("`rule r(?x, ?r) :- ?r = ite(?x)` loads clean against a three-argument
/// functor") — a `@[simp]` rewrite fires by MATCHING a stored LHS, so a redex at an arity
/// no LHS has can never fire, and [`data_functor_error`] refuses it through the same
/// `unmatchable_shape_error` the subgoal check uses. What is still not derived is the
/// TYPE: the enclosing `=` goal's right-hand side stays unknown, which is why this
/// exemption stands and why the atom around it is still not decided. Deriving a type from
/// a functor's `@[simp]` clauses is what would retire it, and no ticket owns that yet.
fn undecidable_by_this_typer(e: &TypeError) -> bool {
    matches!(
        e,
        TypeError::DotDispatchNoMatch {
            receiver_sort: None,
            ..
        } | TypeError::UnreducedEquationFunctor { .. }
    )
}

/// WI-1056 — is `leaf` a report `errors` already carries?
///
/// **A REGRESSION GUARD, not tidiness**, and it is the clause that replaces WI-1043's
/// `own_call_tie`. [`dispatch_calls_in_occ`] both RECURSES into a body-less atom and then
/// type-checks the whole atom, so every failure inside one is derived once by the
/// descendant that owns it and again by each body-less ancestor. `=` goals load as
/// `PartialEq.eq` calls and arithmetic loads as `Numeric` calls, so the ancestors nest:
/// MEASURED on `safety_common.anthill:277` (`?dx = ?p1.position.x - ?p2.position.x`), one
/// dot reported TWICE — once from the enclosing `-` and once from the enclosing `=`. That
/// is the same defect WI-1043 found for a nested TIE and fixed with an (op, span) identity
/// on this node's own call; the widened policy cannot use that identity, because a failure
/// belonging to a descendant that is NOT itself a decided shape has no other reporter and
/// must survive.
///
/// KEYED ON WHAT THE USER SEES — `(span, format)`, the rendered report — because that is
/// exactly the claim being deduplicated: two errors that print identically at one source
/// location ARE one report, whatever internal shape produced them. `TypeError` has no
/// `PartialEq` (it carries `Value`s), and a coarser key (the variant + span) would collapse
/// two genuinely different findings at one span.
///
/// FLATTENS the already-pushed errors, because a `Checked` shape pushes its `Multiple`
/// intact while this shape pushes leaves: without it a leaf inside a dot's aggregate would
/// not be recognised and the duplicate would come back.
///
/// O(n²) over the reports of ONE rule body, on the failure path only — a load that reaches
/// it is already being refused.
fn already_reported(kb: &KnowledgeBase, reported_beneath: &[TypeError], leaf: &TypeError) -> bool {
    let key = (leaf.span(kb), leaf.format(kb));
    reported_beneath.iter().any(|e| {
        e.clone()
            .flatten()
            .iter()
            .any(|l| (l.span(kb), l.format(kb)) == key)
    })
}

/// WI-1043 — WHICH shape [`dispatch_calls_in_occ`] is deciding: it governs whether the
/// walk RECURSES into the node before deciding it, whether it is type-checked at all, and
/// how a failure is reported. Three surface shapes reach `type_check_node`; two of them
/// have been reaching it since WI-282 / WI-1026 and the third was admitted by WI-1043. The
/// two WI-1058 added do NOT reach it — they are CHECKED, not typed.
///
/// WI-1056 retired the third distinction this carried — `reports_every_failure`, WI-1043's
/// narrowing to the two 058 TIES of the deciding call. That clause was what let WI-1043
/// ship: an `=` goal loads as a call on the body-less `PartialEq.eq`, so this shape is
/// most of what a rule body is made of, and a rule body had never been type-checked
/// (`type_rule_bodies` decides dispatch; it does not check types). MEASURED PER LOAD at
/// the acting arm (2026-08-08): **133** newly decided body-less call sites on a
/// whole-corpus load — stdlib + host bindings + `examples/` + `anthill-todo` +
/// `anthill-testcases`, 28 of them on stdlib + bindings alone — whose failures were **19
/// leaf errors** (15 `DotDispatchNoMatch`, 2 `TypeMismatch`, 2 `UnknownApplyFunctor`,
/// **zero** dispatch verdicts), rendering as 7 load errors in 4 files, every one a program
/// that loaded and ran. WI-1056 decided all of them — see [`dispatch_calls_in_occ`]'s doc
/// for the three defects that had to be FIXED and the one exemption that stands — so the
/// narrowing has nothing left to withhold and the shape now reports what it finds.
///
/// WI-1058 added the last two, and with them the widening this enum's comment had been
/// promising since WI-1043: every `Expr::Apply` a rule body carries is now decided, as
/// a `Call` where it is DATA and as a `Subgoal` where it is a GOAL.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum CallDispatch {
    /// An `Expr::DotApply` (WI-282) or a direct call on a DEFAULTED spec op (WI-1026).
    /// Does NOT recurse: `type_check_node` owns its subtree and reports all of it.
    Checked,
    /// WI-1043 — a direct call on a BODY-LESS spec op. RECURSES first (see
    /// [`dispatch_calls_in_occ`]), then decides the whole atom.
    BodyLessSpecOp,
    /// WI-1058 — a FACT PATTERN at goal position: an entity-headed atom, whose shape is
    /// the entity's DECLARED field schema. Same policy as [`Self::BodyLessSpecOp`]:
    /// recurse, then type the node, reporting leaf by leaf.
    Call,
    /// WI-1058 — a GOAL whose functor heads clauses: an atom the resolver PROVES, not a
    /// call to type. Recurses into its arguments, then asks the one question a
    /// signature-directed check cannot: could any of those clauses match this atom at
    /// all ([`subgoal_shape_error`])? Never reaches `type_check_node` — a subgoal has no
    /// signature, and inventing one is what made every subgoal in the corpus die as
    /// `UnknownApplyFunctor`.
    Subgoal,
    /// WI-1058 — a compound term in a DATA slot. Checked for ONE thing, that its functor
    /// NAMES something ([`data_functor_error`]); never type-checked, for three measured
    /// reasons stated at [`call_dispatch_shape`].
    DataTerm,
    /// WI-20260903-FC2X4 — a BINDER FORM (`lambda` / `let` / `match`), whose children are
    /// not readable without it. Same policy as [`Self::Checked`]: does NOT recurse —
    /// `type_check_node`'s own `Expr::Lambda` / `Expr::Let` / `Expr::Match` arms bind the
    /// pattern into Γ (`bind_and_label_pattern`) and type the subtree under it, which is
    /// the one place in the typer that knows how — and reports leaf by leaf.
    BinderForm,
}

/// WI-282 / WI-1026 / WI-1043: is THIS node a call [`dispatch_calls_in_occ`] must decide
/// — an `Expr::DotApply`, or a direct call on a spec op (DEFAULTED, WI-1026; or
/// BODY-LESS, WI-1043)? Answers WHICH, since the error tail differs.
///
/// THE one predicate, asked by the walk's acting arm and by its pre-scan
/// ([`occ_needs_call_dispatch`]) alike. Two spellings of "which shapes we decide"
/// is the drift this ticket was created by: a shape walked but not acted on costs
/// a pass, a shape acted on but not walked is silent.
///
/// **WI-1043 — the spec-op arm is [`spec_op_call_parent`], BOTH halves.** WI-1026
/// admitted the defaulted half only, on the reasoning that a body-less op "has no default
/// to shadow, so `reduce_op_value` leaves it un-ground and the goal residualizes rather
/// than answering wrongly". Residualizing IS the wrong answer: MEASURED, `rule answer(?r)
/// :- Desc.describe(leaf(), ?r)` on a body-less `describe` loaded clean and answered `[]`
/// for EVERY supply shape — with one supplier, where the identical call in an operation
/// body answers the supplied value, and with two, where that call is REFUSED at load
/// (WI-1027). The half is admitted here so both reach `check_apply_iter`'s two blocks,
/// which is where the pin and the refusal already live.
///
/// **WI-1036 — the spec-op arm is [`defaulted_spec_op_parent`] AND NOTHING ELSE.** It was
/// that gate plus `!kb.is_builtin(f)`, excluding the `PartialOrd.{gt,gte,lt,lte}` family
/// (a defaulted spec op whose carrier implementations are host-mapped). WI-1026 gave that
/// exclusion two reasons and BOTH WERE FALSE, each refuted by driving
/// (`wi1036_builtin_defaulted_dispatch_test`):
///
///   1. "`reduce_op_value` returns early on a builtin before it reads a pin, so
///      classifying these sites changes nothing." It reads the pin FIRST — `op` comes
///      off `occ.apply_dispatch()` (WI-1037; `classified_apply_target().unwrap_or(functor)`
///      when this was measured) — and keys the builtin early-return on the PINNED
///      symbol. (2026-08-07 /code-review.)
///   2. "`req_insertion::run` emits a dispatch rewrite per classified occurrence, so
///      widening emits 60 new ones." It walks `kb.op_bodies_iter()`, and a RULE body is
///      not an operation body: the same classified call emits ONE rewrite from an
///      operation body and ZERO from a rule body. No rule-body classification has ever
///      produced a dispatch rewrite, builtin-mapped or not.
///
/// WHAT THE CLAUSE ACTUALLY WITHHELD — two things, both driven, neither about the pin:
///
///   * **The 058 §3.7 tie refusal.** A carrier supplying one of these ops TWICE (own
///     member + instance fact) was refused at load from an operation body and accepted
///     from a rule body — one program, two verdicts, decided by where the call is
///     written. Without the clause the rule body refuses at its own location, with the
///     same message.
///   * **§3.1 dispatch by value in OPERAND position.** A rule-body operand
///     `unify(?r, PartialOrd.gt(p, q))` on a carrier with a supplied override answered an
///     indefinite residual; classified, the pin names the override and
///     [`reduce_op_value`] folds it. The pin IS readable there — the carrier's own `gt`
///     is an ordinary bodied operation, not a builtin — so "both sides are builtin" was
///     only ever true of the STDLIB family, never of the population.
///
/// COST, measured at [`dispatch_calls_in_occ`]'s acting arm: FOUR newly decided sites on
/// a stdlib + host-bindings load (2 × `PartialOrd.gt`, 1 × `lt`, 1 × `gte`, all stdlib
/// rule bodies), five with `anthill-testcases`, none in `examples/github-todo` or
/// `anthill-todo`; the ticket's 60 does not reproduce. Those four are GOAL-position calls
/// whose pins name `Int64.gt` / `Float.gt`, both builtins, so `reduce_op_value` returns
/// early exactly as before — the corpus gets the refusal, not a dispatch change.
///
/// WHAT IS STILL BROKEN AND IS NOT THIS GATE'S: the same call in GOAL position on a
/// carrier with a supplied override still answers nothing. The goal takes
/// `BuiltinTag::Gt` off its SPELLED functor — no goal-position reader consults a pin —
/// and `builtin_cmp` fails silently on operands it cannot compare. Classifying it does
/// not help; **WI-879 owns it**, and its acceptance is exactly that such a comparison
/// "either answers correctly or raises, never silently fails".
///
/// # WI-1058 — the general `Expr::Apply`, and the POSITION that decides how to read it
///
/// The narrowing this function carried since WI-282 is gone, and what replaces it is
/// not "admit everything": it is that the walk now knows whether a node is a GOAL or
/// DATA ([`BodyPos`]), so one functor can answer differently in the two places it is
/// written. In a DATA position every application is a `Call` — that is the widening,
/// and it is what refuses a nested `p(bogus(?x))` whose functor names nothing (the
/// population WI-1034's goal walk does not reach, since it never descends into data).
/// In a GOAL position the ladder is four rungs, in this order and for these reasons:
///
///   1. **A CONNECTIVE is not a call.** `not` / `or` / `push_choice` / the scoping
///      markers, and the `tuple(…)` wrapper of a quantifier body — recognised by the
///      ONE slot table ([`KnowledgeBase::goal_slot_readings`]), never by spelling.
///      Their goal children are walked as goals; there is nothing at the node itself to
///      type.
///   2. **A SPEC OP keeps its two shapes**, unchanged — the `=` goal and the arithmetic
///      that most of a rule body is made of (WI-1026 / WI-1043 / WI-1056).
///   3. **A BUILTIN with no operation record is the BUILTIN**, whose arguments are goal
///      terms. One symbol is in this class and it is why the widening was blocked:
///      `anthill.reflect.Expr.ho_apply` is registered as `BuiltinTag::HoApply` *and*
///      declared as the reflect IR entity `ho_apply(predicate: Term, args: List[Term],
///      …)`. Read as the entity, `ho_apply(?P, Vec3(…))` checks a `Vec3` against
///      `List[T = Term]` and is refused. MEASURED (2026-08-09, stdlib + host bindings):
///      **271 of 323** reports a position-blind widening produced were this, every one
///      from ONE producer — the loader's synthesized `<Sort>.induction`
///      (`Loader::emit_induction_rule`), whose body is `ho_apply(?P, ctor(…))` by
///      construction. This clause is the exact twin of `check_apply_iter`'s WI-1056
///      rule-body arm, narrowed the same way and for the same reason: `SymbolKind` is a
///      SET, so an operation reading, if the symbol has one, WINS.
///   4. **Otherwise a `Subgoal`** — unless the functor carries a DECLARATION the typer
///      can check it against. An ENTITY-headed goal is a fact pattern whose shape comes
///      from the declared field schema (`check_constructor_iter`, which admits the
///      partial named-arg form the loader fresh-fills), and an OPERATION named as a goal
///      has a signature; both stay `Call`. Everything else is an atom the resolver
///      proves, checked against its own clauses ([`subgoal_shape_error`]).
///
/// **A GOAL IS NEVER REFUSED HERE FOR NAMING NOTHING**, and that is a division of
/// labour, not an omission. `subgoal_shape_error` says nothing when the functor heads no
/// clause, because absence in goal position is [`KnowledgeBase::undefined_rule_body_goals`]'s
/// (WI-1034) — and it is the only one of the two that holds the exemption a HYPOTHESIS
/// needs. A discharge's antecedent DECLARES its predicate (`(forall(?prev),
/// t4_property(?prev) -: t4_property(?prev))`), so `t4_property` heads no clause anywhere
/// and must not be refused; routing goal-position absence through `Call` refused exactly
/// that program. In DATA position there is no such tolerance and none is wanted — a
/// nested `p(bogus(?x))` is refused, which is the population WI-1034's walk never reaches.
pub(super) fn call_dispatch_shape(
    kb: &KnowledgeBase,
    expr: &Expr,
    pos: BodyPos,
) -> Option<CallDispatch> {
    if pos == BodyPos::Untyped || rule_body_type_term(kb, expr) {
        return None;
    }
    match expr {
        Expr::DotApply { .. } => Some(CallDispatch::Checked),
        // TWO gate calls, and the second is [`defaulted_spec_op_parent`] rather than the
        // bare body probe it conjoins, deliberately: naming the half by re-asking the
        // OWNER is what makes a clause added there reach this site too — the WI-1042
        // drift. MEASURED rather than assumed to be cheap, as reaches of
        // [`sort_is_parametric`] per stdlib + host-bindings load: 1004 before this
        // ticket, 1170 with the union admitting, **1178** with the owner re-asked. (Each
        // reach was 51 µs, O(|symbols|), when that was measured; WI-954 made the leg an
        // O(1) owner-scope read, so the counts stand and the price does not.) The second
        // call costs 8, because it runs its body probe BEFORE
        // the parametric leg — so it returns early for exactly the population this arm
        // added, and pays the leg twice only for the handful of DEFAULTED spec-op call
        // sites (WI-1036 counted 4–5 of those).
        // WI-20260903-FC2X4 — A BINDER FORM IS DECIDED AS A UNIT, because its children
        // name something only it introduces. `lambda x -> x + 1`'s body names `x`, and
        // only the LAMBDA puts `x` in Γ; this walk has no Γ to extend, so descending
        // typed `plus(x, 1)` in an empty environment and reported the binder as an
        // unresolved NAME. Handing the whole node to `type_check_node` instead reuses the
        // binder scoping that already exists there.
        //
        // NOT REACHABLE BEFORE THIS TICKET, which is why the arm is new rather than
        // long-missing: a rule body's lambda was materialized from a POSITIONAL marker
        // term whose named keys `visit_fn` could not find, so its body was `⊥` and there
        // was no `x` to resolve. [`child_body_positions`]'s note about a binder's PATTERN
        // child records the same shape from the other side.
        //
        // Derived from [`pattern_child_indices`] rather than re-listing the forms: that
        // function is the one place every binding constructor is enumerated, and its own
        // doc says a missing row there is silent.
        _ if !pattern_child_indices(expr).is_empty() => Some(CallDispatch::BinderForm),
        Expr::Apply {
            functor, pos_args, ..
        } => {
            let spec_op = || {
                spec_op_call_parent(kb, *functor).map(|_| {
                    if defaulted_spec_op_parent(kb, *functor).is_some() {
                        CallDispatch::Checked
                    } else {
                        CallDispatch::BodyLessSpecOp
                    }
                })
            };
            match pos {
                // Returned above, with the type-term test it shares a reason with.
                BodyPos::Untyped => None,
                BodyPos::Value => spec_op().or(Some(CallDispatch::DataTerm)),
                BodyPos::Goal(commit) | BodyPos::GoalTuple(commit) => {
                    // 1 — a connective (rung 1). The `tuple` wrapper is recognised only
                    // in the slot the table put one in, never by its name alone.
                    let wrapper = matches!(pos, BodyPos::GoalTuple(_))
                        && kb.local_name_of(*functor) == "tuple";
                    if wrapper || !kb.goal_slot_readings(*functor, pos_args.len()).is_empty() {
                        return None;
                    }
                    // 2 — the two spec-op shapes, unchanged.
                    if let Some(s) = spec_op() {
                        return Some(s);
                    }
                    // 3 — a resolver BUILTIN, which is read by the builtin.
                    if kb.builtin_of(*functor).is_some() {
                        return None;
                    }
                    // 4 — a FACT PATTERN, whose shape is the entity's declared field
                    // schema. The one goal-position shape with a declaration to check
                    // against. ASKED BEFORE the sort rung below, because an eponymous
                    // `sort E { entity E(…) }` is ONE symbol carrying both kinds and
                    // WI-1056 settled that a rule-body `E(a: 1)` is a CONSTRUCTION.
                    if kb.is_entity_constructor(*functor) {
                        return Some(CallDispatch::Call);
                    }
                    // 5 — a SORT-headed atom is a TYPE or an INSTANCE CLAIM (`rule r(?t)
                    // :- Modifiable[T = ?t]`, `fact Modifiable[T = Cell]`), never a
                    // subgoal. Its argument grammar is not a predicate's: WI-407 carrier
                    // slots and WI-431 op-bearing bindings both live here, so measuring it
                    // against the shapes of the facts asserted under it refuses the
                    // stdlib's own reflect rules (`Modifiable[?t]` against `Modifiable[T =
                    // Cell]`). Checked where it is BUILT, by `check_sort_type_args`
                    // (WI-710/WI-927).
                    if kb.has_kind(*functor, crate::intern::SymbolKind::Sort) {
                        return None;
                    }
                    // 6 — a SUBGOAL, shape-checked only where a dead one is a defect
                    // ([`GoalCommit`]). A tolerated position still WALKS — its dots
                    // dispatch and its data slots are name-checked — it just does not
                    // report the shape.
                    commit.checked().then_some(CallDispatch::Subgoal)
                }
            }
        }
        _ => None,
    }
}

/// WI-1058 — the SUBGOAL check: could ANY clause of this atom's functor match it?
///
/// A rule subgoal has no signature, so the question a call-site check asks ("do these
/// arguments fit the declared parameters") has no answer here. The question that DOES
/// have one is the resolver's own: a goal matches a clause by unifying with its head,
/// and a head of a different SHAPE — a different positional arity, or a different set of
/// named-argument labels — can never unify with it. A subgoal no clause can match is a
/// dead conjunct: the rule it sits in silently answers nothing, which reads exactly like
/// "no such fact". This is WI-1034's defect one step further in — that walk refuses a
/// goal whose functor names NOTHING; this one refuses a goal whose functor names
/// something that cannot be it.
///
/// **A PROOF OF IMPOSSIBILITY, not a shape preference**, and that is what decides the
/// two ways it declines to fire:
///
///   * A clause whose head is not a hash-consed `Term::Fn` (a `Value::Node` / entity
///     value fact — WI-348/WI-366) has no readable label set here, so no such proof
///     exists and nothing is reported. Stated rather than left to be found: this is a
///     limit on what can be PROVED, so widening it means reading those heads, not
///     loosening this.
///   * A functor with no indexed clause at all is not this check's — WI-1034's goal walk
///     owns absence, with the hypothesis exemption and the discrimination-tree backstop
///     an arity-0 proposition needs. Reporting it here too would say the same thing
///     twice about one defect.
///
/// ENTITY-headed goals never arrive: [`call_dispatch_shape`] routes them to the
/// constructor reading, whose shape comes from the DECLARED field schema (and admits
/// the partial named-arg form the loader fresh-fills), not from the facts asserted under
/// it.
fn subgoal_shape_error(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    rule_sym: Option<Symbol>,
) -> Option<TypeError> {
    let Some(Expr::Apply { functor, .. }) = occ.as_expr() else {
        return None;
    };
    let mut shapes: Vec<(usize, Vec<Symbol>)> = Vec::new();
    for rid in kb.rules_by_functor_iter(*functor) {
        // No readable shape ⇒ no proof; say nothing at all.
        let head = kb.fact_head_term(rid)?;
        let shape = match kb.get_term(head) {
            Term::Fn {
                pos_args,
                named_args,
                ..
            } => (pos_args.len(), named_args.iter().map(|(k, _)| *k).collect()),
            // `Ref(c) ≡ Fn{c}` at arity 0 (WI-436) — the canonical spelling of a
            // 0-ary application, and how a bare proposition is stored.
            Term::Ref(_) | Term::Ident(_) => (0, Vec::new()),
            _ => return None,
        };
        shapes.push(shape);
    }
    unmatchable_shape_error(kb, occ, &shapes, "a clause", rule_sym)
}

/// WI-1058 — the shared half of the two "could this ever match" checks
/// ([`subgoal_shape_error`], and the `@[simp]` REDEX arm of [`data_functor_error`]):
/// given every shape the name's clauses present, is this term's shape none of them?
///
/// ONE function because it is one question asked of two clause SOURCES — a predicate's
/// heads and an equation's LHSs — and the rendering, the label canonicalisation and the
/// "no clauses ⇒ no proof" rule must not differ between them. `subject` names the source
/// in the message ("a clause" / "a `@[simp]` equation"), which is the only difference.
fn unmatchable_shape_error(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    shapes: &[(usize, Vec<Symbol>)],
    subject: &str,
    rule_sym: Option<Symbol>,
) -> Option<TypeError> {
    let Some(Expr::Apply {
        functor,
        pos_args,
        named_args,
        ..
    }) = occ.as_expr()
    else {
        return None;
    };
    if shapes.is_empty() {
        return None;
    }
    let canon = |n: usize, labels: &[Symbol]| (n, sorted_labels(labels.iter().copied()));
    let here = canon(
        pos_args.len(),
        &named_args.iter().map(|(k, _)| *k).collect::<Vec<_>>(),
    );
    let mut distinct: Vec<(usize, Vec<Symbol>)> = Vec::new();
    for (n, labels) in shapes {
        let s = canon(*n, labels);
        if s == here {
            return None;
        }
        if !distinct.contains(&s) {
            distinct.push(s);
        }
    }
    let render = |(n, labels): &(usize, Vec<Symbol>)| {
        let mut s = format!("{n} positional");
        for l in labels {
            s.push_str(&format!(" + `{}`", kb.local_name_of(*l)));
        }
        s
    };
    let alternatives: Vec<String> = distinct.iter().map(render).collect();
    Some(TypeError::Other {
        site: TypeError::here(),
        span: Some(occ.span.span),
        // The ENCLOSING rule, not the callee: the callee is already named in the message
        // body, and this field renders as "the rule this error is in" — which is the text
        // the author must edit.
        context: TypeErrorContext::Rule {
            name: rule_sym.unwrap_or(*functor),
            field: RuleField::Whole,
        },
        expected: format!(
            "a term {subject} of `{}` can match ({})",
            kb.qualified_name_of(*functor),
            alternatives.join(" or "),
        ),
        actual: render(&here),
    })
}

/// WI-1058 — the DATA-slot check: does this compound term's functor NAME anything?
///
/// The one question a rule body's data slot can be asked without an expectation and
/// without a scope, and it is the question WI-895 filed: an un-imported functor interns
/// bare, so `holds894(ite(true, 10, 20))` loads clean, never fires as a `@[simp]` redex,
/// and says nothing. WI-1034 closed the GOAL-position half of that; this is the other
/// half, asked with the SAME head test ([`KnowledgeBase::undefined_functor`]) so the two
/// positions cannot disagree about which names exist. That head test carries a
/// scoping-marker exemption; whether a data slot ever REACHES it is not claimed here (a
/// marker is a goal connective, so [`call_dispatch_shape`] answers for it first) — the
/// point of sharing is that the two positions ask one authority, not that both use every
/// clause of it.
///
/// **NOT a type-check, and that is measured rather than chosen for caution.** Handing a
/// data slot to `check_apply_iter` — the obvious reading of "widen the walk to every
/// `Expr::Apply`" — is wrong three separate ways, each found by driving the suite:
///
///   1. **It loses the EXPECTATION.** `check_apply_iter`'s readings are
///      expectation-directed: a sort name denotes a `Type` VALUE only in a slot that
///      expects one (`check_bare_ref`'s WI-206 arm). Typed standalone with `expected:
///      None`, `takes_type(Holder[T = Int64])`'s argument reported `unresolved name:
///      Int64` about a name that resolves — `wi927_bracket_surface_test`,
///      `wi710_rule_body_type_arg_test`, `wi839_call_bracket_channel_test`, and 24 more.
///   2. **It loses the SCOPE.** A node under a `lambda` / `let` is typed outside its
///      binder, so `all_match(?xs, lambda (x) -> is_pos(x))` reported `x` unresolved
///      twice (`wi620_paren_lambda_param_test`).
///   3. **It REWRITES the body.** `dispatch_calls_in_occ` stores `type_check_node`'s
///      result node, which is redex-free — so `holds(ite(true, 10, 20))` became
///      `holds(10)` AT LOAD and the rule answered under `ResolveConfig { simplify:
///      false }`, where its whole point is to answer nothing
///      (`wi884_sibling_backing_test`). A check that changes what a rule MEANS is not a
///      check.
///
/// Each is structural, not a missing case: a rule body's data slot holds a TERM, and the
/// typer's call ladder is about VALUES in a typed context. That is why WI-895 said this
/// half "needs its own predicate, not a wider walk", and this is that predicate.
fn data_functor_error(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    rule_sym: Option<Symbol>,
) -> Option<TypeError> {
    // Only a COMPOUND term: a bare name in a data slot is a nullary constructor or a
    // logic constant, and refusing those is a different, wider claim than this one
    // (WI-1034's goal walk makes it at goal position, with the discrimination-tree
    // backstop an arity-0 proposition needs).
    let Some(Expr::Apply { functor, .. }) = occ.as_expr() else {
        return None;
    };
    // WI-1058 — the ONE thing that IS checkable about an EQUATION-introduced functor's
    // redex, and the hole `undecidable_by_this_typer` handed here by name: a `@[simp]`
    // rewrite fires by MATCHING a stored LHS, so a call at an arity no LHS has can never
    // fire, whatever the tag says. That exemption's doc states the gap exactly — "nothing
    // about the call itself survives, ARITY INCLUDED — `rule r(?x, ?r) :- ?r = ite(?x)`
    // loads clean against a three-argument functor". It no longer does. The exemption
    // itself STANDS: deriving a redex's TYPE from its clauses is a different and much
    // larger reading, and this ticket did not deliver it.
    if kb.has_kind(*functor, crate::intern::SymbolKind::EquationFunctor) {
        if let Some(shapes) = crate::kb::simp_rewrite::equation_lhs_shapes(kb, *functor) {
            if let Some(e) =
                unmatchable_shape_error(kb, occ, &shapes, "a `@[simp]` equation", rule_sym)
            {
                return Some(e);
            }
        }
    }
    let sym = kb.undefined_functor(&Value::Node(Rc::clone(occ)))?;
    // NOT `UnknownApplyFunctor`, whose sentence is "expected a known operation or
    // arrow-typed variable" — advice about a CALL SITE, which a data slot is not. The
    // consequence here is that nothing can unify with the term and no `@[simp]` rule can
    // rewrite it; `UndefinedDataFunctor` says that, in the goal twin's voice.
    Some(TypeError::UndefinedDataFunctor {
        span: Some(occ.span.span),
        name: sym,
    })
}

/// The argument labels of a call / head, deduplicated and ordered, so two spellings of
/// one shape compare equal. Named arguments are canonicalized at load by DECLARED field
/// order where a schema exists and by interning order otherwise, so their stored order
/// is not a stable comparison key.
fn sorted_labels(labels: impl Iterator<Item = Symbol>) -> Vec<Symbol> {
    let mut v: Vec<Symbol> = labels.collect();
    v.sort_by_key(|s| s.index());
    v.dedup();
    v
}

/// WI-282 / WI-1026: does `occ` CARRY, anywhere in its subtree, a node
/// [`call_dispatch_shape`] answers for? A cheap pre-scan so the dispatch walk
/// skips rule bodies with none. Explicit-stack walk (matching its sibling
/// [`occurrence_contains_functor`]) so a deeply-nested body can't overflow the host
/// stack.
///
/// The conditions share ONE pre-scan because they share one walk: a body with only
/// a spec-op call still needs the var-type env installed, which is what
/// `type_rule_bodies` builds around this gate. Still cheap after WI-1026 widened it
/// — see [`call_dispatch_shape`] for the measurement that says so.
///
/// WI-1058: the stack carries each node's [`BodyPos`], derived by the SAME
/// [`child_body_positions`] the acting walk uses. Without it the two walks would ask
/// [`call_dispatch_shape`] different questions about the same node — the exact drift
/// this shared predicate exists to prevent, one argument further along.
pub(super) fn occ_needs_call_dispatch(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> bool {
    let mut stack: Vec<(Rc<NodeOccurrence>, BodyPos)> =
        vec![(Rc::clone(occ), BodyPos::Goal(GoalCommit::Top))];
    while let Some((o, pos)) = stack.pop() {
        if let Some(expr) = o.as_expr() {
            if call_dispatch_shape(kb, expr, pos).is_some() {
                return true;
            }
            let mut children: SmallVec<[Rc<NodeOccurrence>; 8]> = SmallVec::new();
            for_each_child(expr, |c| children.push(Rc::clone(c)));
            let child_pos = child_body_positions(kb, expr, pos, children.len());
            stack.extend(children.into_iter().zip(child_pos));
        }
    }
    false
}

/// WI-282 / WI-307: collect a rule's De Bruijn variable types from its head term
/// and body occurrences (op-argument / entity-field positions), returning the
/// `var id → type` map plus whether the constraints are contradictory. Head and
/// body are closed against the same De Bruijn vars, so their idx keys align.
///
/// The single collection per rule for [`type_rule_bodies`], which reports the
/// contradiction (sort-scoped), skips a contradictory rule's dispatch (the
/// receiver sort would be unreliable), and stamps the map onto the body's `Var`
/// leaves (WI-603). `var_types` is carried
/// carrier-agnostically as `Value` (WI-342 P3): today every entry is a
/// `Value::Term` from `OperationInfo` / entity-field metadata; it holds a
/// `Value::Node` type unchanged once those producers migrate in P4. WI-307: the
/// body-node slice is taken by reference (the caller clones it out first) so the
/// immutable borrow does not conflict with the inner `&mut kb` constraint pass.
pub(super) fn collect_rule_var_types(
    kb: &mut KnowledgeBase,
    head: TermId,
    body_nodes: &[Rc<NodeOccurrence>],
) -> (HashMap<u32, Value>, bool) {
    let mut subst = Substitution::new();
    let mut var_types: HashMap<u32, Value> = HashMap::new();
    // WI-9C2PZ — which entries are a CALL's placeholder rather than a statement about the
    // variable. Lives for the collection and is dropped with it; see [`constrain_vid`].
    let mut param_backed: ParamBackedVars = HashSet::new();
    collect_term_type_constraints(kb, head, &mut var_types, &mut param_backed, &mut subst);
    for node in body_nodes {
        collect_occurrence_type_constraints(
            kb,
            node,
            &mut var_types,
            &mut param_backed,
            &mut subst,
        );
    }
    // WI-9C2PZ — RESOLVE THE MAP THROUGH THE SUBSTITUTION IT BUILT, which until now was
    // collected and dropped. `rule r(?x, ?y) :- eq(?x, ?y), parent(of: ?x, is: ?)`
    // records both variables at this call's instantiation of `PartialEq.T` and then
    // binds that variable to `String` from `parent.of` — so the answer for `?y` is in
    // the substitution and nowhere else, and without this step `?y` stays an unknown
    // though `eq` forces it equal to a `String`.
    //
    // WI-741 CALLED THIS EXACT STEP UNSOUND AND WAS RIGHT AT THE TIME: with the
    // parameter uninstantiated, the variable it bound was the ONE alias every `eq` in
    // the rule shared, so resolving through it typed an `Int64` variable `String`
    // (measured, in the `mix` shape of
    // `wi741_two_spec_calls_at_different_carriers_do_not_contradict`). Per-application
    // instantiation is what makes the binding local to the call that made it, and
    // therefore what makes this sound. The two halves ship together for that reason.
    //
    // UNCONDITIONAL, including for a contradictory rule. Skipping it there was the first
    // cut and /code-review caught the asymmetry it created: [`relation_clause_columns`]
    // publishes a clause's columns whether or not the rule is contradictory, so one clause
    // of a relation would publish RAW column types while its siblings published resolved
    // ones — the inheritance silently not applying to that clause alone. There is nothing
    // to protect against either: a failed unification records no binding, so what σ holds
    // is exactly the agreements that were reached.
    if std::env::var("NO_RESOLVE_9C2PZ").is_err() {
        for ty in var_types.values_mut() {
            let (resolved, _) = crate::kb::node_occurrence::subst_value_type(kb, ty, &subst);
            *ty = resolved;
        }
    }
    (var_types, subst.is_contradiction())
}

/// Collect type constraints from a term: for each variable in an operation/entity
/// argument position, record the expected type.
pub(super) fn collect_term_type_constraints(
    kb: &mut KnowledgeBase,
    term: TermId,
    var_types: &mut HashMap<u32, Value>,
    param_backed: &mut ParamBackedVars,
    subst: &mut Substitution,
) {
    match kb.get_term(term) {
        Term::Fn {
            functor,
            pos_args,
            named_args,
            ..
        } => {
            let functor = *functor;
            let pos_args = pos_args.clone();
            let named_args = named_args.clone();

            // Expected types from operation params or entity fields — the dispatch the
            // body walker applies to an occurrence, on the head's `TermId` arguments.
            constrain_application(
                kb,
                functor,
                &pos_args,
                &named_args,
                var_types,
                param_backed,
                subst,
            );

            // Recurse into subterms
            for &arg in pos_args.iter() {
                collect_term_type_constraints(kb, arg, var_types, param_backed, subst);
            }
            for &(_, arg) in named_args.iter() {
                collect_term_type_constraints(kb, arg, var_types, param_backed, subst);
            }
        }
        _ => {}
    }
}

//! Proposal 050 (WI-537): the resolver bridge that proves goals from Γ, and match-arm
//! Γ narrowing.

use super::*;

// ── Proposal 050 (WI-537): the resolver bridge ─────────────────
//
// Discharge a goal against the local logical storage Γ on the *existing* SLD
// resolver — `goal` is resolved over **KB ∪ Γ** in one search, Γ riding the
// resolver's `ResolveConfig::gamma` overlay (consulted at the candidate step
// exactly like a frame's `assumed_facts`). There is no separate Γ-membership
// matcher: a Γ fact and a KB-rule derivation that *uses* a Γ fact are both
// found by the same SLD machinery, so none of it is duplicated. This is the
// load-bearing new mechanism the proposal calls out — the typer does not
// otherwise call `kb.resolve` during body checking.

/// Try to **prove** `goal` from Γ (`flow`) ∪ KB via one SLD search.
///
/// `definite_only` (WI-519) is the floundering guard: a non-ground `not(P)`
/// residualizes and is *skipped*, so a goal ranging over an unknown runtime
/// parameter stays UNPROVEN (the open-world reading), never a
/// negation-as-failure "drop" (048 §"Discharge is constructive refutation, not
/// NAF"). Returns `true` only on a *definite* (residual-free) solution — the
/// soundness contract every consumer (WI-067 discharge, WI-539
/// `requires`-check) relies on. A Γ fact `neq(b, 0)` over a rigid parameter `b`
/// proves the query `neq(b, 0)` over the same `b` (the overlay keys it
/// `RigidVar(b)`); a *symbolic* `neq(b, 0)` with empty Γ flounders → unproven.
pub fn prove_from_gamma(kb: &mut KnowledgeBase, flow: &FlowEnv, goal: &Value) -> bool {
    let config = crate::kb::resolve::ResolveConfig {
        definite_only: true,
        max_solutions: 1,
        gamma: Some(flow.index()),
        opaque_skolems: Some(flow.skolems()),
        ..crate::kb::resolve::ResolveConfig::default()
    };
    kb.resolve(std::slice::from_ref(goal), &config)
        .iter()
        .any(|s| s.residual.is_empty())
}

/// WHAT Γ SAYS ABOUT A GOAL — three answers, because a proof bridge has three.
///
/// [`prove_from_gamma`] returns a bool and therefore folds two of them together: a goal
/// Γ REFUTES and a goal Γ cannot DECIDE both come back `false`. That fold is safe (an
/// undecided guard does not fire, which is the conservative direction) but it is not
/// honest to the author — the two need opposite repairs, and only one of them is a
/// repair at all. See [`GammaVerdict`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GammaVerdict {
    /// A DEFINITE (residual-free) solution exists — Γ derives the goal.
    Proved,
    /// A COMPLETE search found NO answer at all — not one solution, definite or
    /// residual, and nothing was cut short. Only here does closed-world reasoning
    /// license "the goal does not follow".
    ///
    /// STRICT, and the strictness is the point. The first draft returned this whenever
    /// no answer carried an undecided goal, which swept in ordinary FLOUNDERED
    /// residuals (an unbound `?` in the conjunct) and DEPTH-TRUNCATED searches — both
    /// of them non-answers, both then reported to the author as "your body is wrong".
    /// That is the very flounder/refutation conflation this type exists to end,
    /// relocated one level up.
    Refuted,
    /// No proof, and no refutation either — the search did not decide it.
    ///
    /// `universal` says WHICH non-answer, because only one of them has a specific
    /// repair. `true`: some goal ranged over a UNIVERSAL — a `var_ref` binder reference
    /// or a contract σ's eigenvariable — where closed-world absence is not negation, so
    /// no further resolution decides it. `false`: an ordinary flounder or a
    /// depth-truncated search, undischarged rather than undecidable, and possibly
    /// decidable with more budget or more bindings.
    ///
    /// NAMED FOR THE QUESTION, NOT FOR ONE ANSWER. It was `open_world`, after the first
    /// [`crate::kb::resolve::UnknownCause`]; the second (`OpaqueSkolem`) is a different
    /// carrier of the same thing, and a field named after one cause invites its reader
    /// to test for that cause rather than for the property. The property is what the
    /// message depends on, and [`crate::kb::resolve::UnknownCause::is_universal`] owns
    /// it in an exhaustive match.
    Undecided { universal: bool },
    /// The search could not EVALUATE part of the goal — it reported a fault
    /// ([`crate::kb::resolve::ResolveError`]), so there is no reading of the result to
    /// trust. `message` is the fault, already phrased for the author.
    ///
    /// ITS OWN VARIANT because it is a different thing from all three others and,
    /// before it existed, wore the wrong one. An ORDERING over a contract parameter —
    /// `ensures gt(x, 0)`, whose σ makes `gt(c, 0)` for an eigenvariable `c` — reaches
    /// `builtin_cmp`'s no-order arm, since `c` is a `Term::Ref` and not an ordered
    /// literal. That arm now reports a fault and residualizes; this reader dropped the
    /// fault (it drained with `resolve_goals_with_truncation`, which returns no errors)
    /// and the residual then read as an ordinary flounder. MEASURED: the author was told
    /// the conjunct was "left UNDISCHARGED … having delayed on a variable nothing bound
    /// or stopped at the depth limit", when nothing had delayed and nothing had been cut
    /// short — and "bind what it waits on" is advice no binding can satisfy.
    Faulted { message: String },
}

/// [`prove_from_gamma`]'s answer, un-folded — for the callers that must tell a REFUTED
/// goal from an UNDECIDED one.
///
/// TWO RESOLVES, AND ONLY ON THE COLD PATH. The first is byte-identical to
/// [`prove_from_gamma`]'s — same config, same reader — so a goal that PROVES costs
/// exactly what it costs today and this function adds nothing to the hot path. The
/// second runs only where the first found no proof, which is where the distinction is
/// wanted and where a diagnostic is about to be written anyway.
///
/// WHY THE SECOND RESOLVE IS NEEDED AT ALL, rather than reading the first's solutions:
/// the first sets `definite_only`, which SKIPS every non-definite branch outright
/// (`step_init`'s residual gate) — an undecided answer is discarded before it can be
/// yielded, so `prove_from_gamma` genuinely cannot see one. MEASURED before this
/// function existed: an open-world goal fired `BuiltinResult::Unknown` and the same
/// call returned `0 solutions, 0 carrying undecided`.
///
/// UNBOUNDED `max_solutions` on the second, deliberately: the question is "does ANY
/// answer carry an undecided goal", and a bound of 1 would answer it from whichever
/// residual came out first — reporting the wrong verdict for a goal that is undecided
/// further down the stream. The fast path has already established there is no proof to
/// find, so this walks a search that yields only residuals — and a search that ends
/// having found nothing does the same work either way, since proving a result EMPTY is
/// what makes [`GammaVerdict::Refuted`] sayable at all.
///
/// TRUNCATION IS READ, NOT ASSUMED AWAY. `resolve_goals_with_truncation` rather than
/// `resolve`, because a search cut off at `max_depth` found no answer for a reason that
/// has nothing to do with the goal — and `resolve` alone cannot tell that from a
/// complete empty search, which is exactly the distinction `Refuted` rests on.
pub fn prove_from_gamma_verdict(
    kb: &mut KnowledgeBase,
    flow: &FlowEnv,
    goal: &Value,
) -> GammaVerdict {
    if prove_from_gamma(kb, flow, goal) {
        return GammaVerdict::Proved;
    }
    let config = crate::kb::resolve::ResolveConfig {
        definite_only: false,
        max_solutions: 0,
        gamma: Some(flow.index()),
        opaque_skolems: Some(flow.skolems()),
        ..crate::kb::resolve::ResolveConfig::default()
    };
    // `resolve_with_stats`, NOT `resolve_goals_with_truncation`: the latter answers
    // `(solutions, truncated)` and DROPS `ResolveStats::errors`, so a goal the resolver
    // could not evaluate came back indistinguishable from one that merely floundered.
    let (sols, stats) = kb.resolve_with_stats(std::slice::from_ref(goal), &config);
    let truncated = stats.truncated;

    // READ THE CAUSE, do not infer it from the list being non-empty. Both causes today
    // answer `is_universal` the same way, so this changes no row — it is here so that a
    // third cause has to decide rather than inherit the universal wording by default.
    if let Some(cause) = sols
        .iter()
        .flat_map(|s| s.undecided.iter())
        .map(|(_, cause)| *cause)
        .next()
    {
        return GammaVerdict::Undecided {
            universal: cause.is_universal(),
        };
    }
    // THE FAULT IS ASKED AFTER, and the order is the point. `stats.errors` is
    // per-STREAM: a fault raised on ANY branch — a different candidate rule, an
    // unrelated conjunct — lands in it. `Solution::undecided` is per-ANSWER, so a cause
    // there is about a goal in THIS residual. Asking the fault first let an unrelated
    // no-order arm elsewhere in the search rewrite an eigenvariable conjunct's message
    // into "`gt` has no order for this operand pair", pointing the author at operands
    // their conjunct does not mention.
    //
    // Reached, not dead: an `Error` deliberately contributes NO `undecided` entry (a
    // fault is not a statement about a universal), so a goal whose only problem is a
    // fault has nothing above to match and falls here.
    if let Some(err) = stats.errors.first() {
        return GammaVerdict::Faulted {
            message: err.message.clone(),
        };
    }
    // ANY residual answer, or a cut-short search, is a NON-ANSWER — not a refutation.
    // Only an empty, complete search licenses the closed-world reading.
    if truncated || sols.iter().any(|s| !s.is_definite()) {
        return GammaVerdict::Undecided { universal: false };
    }
    GammaVerdict::Refuted
}

/// WI-756 — THE Γ VOCABULARY: the one form every Γ fact and every Γ goal is in.
///
/// A `Value::Node` occurrence crosses the GOAL-LOWERING BOUNDARY
/// (`try_occurrence_to_term` → `term_body_to_nodes`) so a nullary CONSTRUCTOR
/// reads as the closed datum `Ref` (WI-592) instead of the `var_ref` op-body
/// lowering wraps EVERY bare identifier in; a genuine binder stays `var_ref` and
/// still flounders (the sound open-world default). Compound carriers recurse —
/// a fact like `eq(var_ref(x), <value>)` (`binding_gamma_fact`,
/// `match_arm_gamma_facts`, a negated `if` condition) carries its operands as
/// children, and it is the OPERANDS that need the boundary. Every other carrier
/// is already in this form: a σ-substituted `requires`/`ensures` clause is a
/// term (WI-539/WI-558), and a scalar is itself. Re-materializing as an
/// occurrence rather than stopping at the `TermId` keeps op-calls foldable
/// (`reduce_op_value`), as `proof_verify::discharge_contract_proof` does.
///
/// PRODUCERS AND CONSUMERS MUST SHARE IT, which is why this is applied at
/// [`FlowEnv::assume`] (every fact's door) and at [`in_body_proof_goal`] (the
/// one goal built from source rather than from a clause). The Γ overlay is
/// consulted STRUCTURALLY, ahead of the builtin and its open-world delay
/// (`resolve.rs`'s `gamma_candidates_for`), so a fact spelling `Red` as
/// `var_ref` cannot discharge a goal spelling it `Ref`: before WI-756
/// `if eq(c, Red) then needy(c)` did not satisfy `needy`'s `requires eq(c, Red)`
/// though the identical program over an `Int64` literal did.
///
/// `try_`, NOT the asserting `occurrence_to_term`: a `conclude`/condition takes
/// a full `_term`, which admits shapes that are deliberately NOT goals — the
/// args-bearing `DotApply` above all — whose `None` is back-pressure the
/// reifier's own doc says not to "finish". Such a value rides on unlowered: it
/// can neither prove nor match a goal, so it is inert either way, where
/// asserting would turn legal (if unprovable) source into a debug panic. `⊥` is
/// treated the same — an elaborated-away conclusion is not a goal, and lowering
/// it would put a `⊥` term where a proposition belongs.
///
/// TWO HALVES, in order. [`goal_form_carrier`] settles how the fact is CARRIED
/// (everything above); [`goal_form_proposition`] then settles how its connectives
/// are SPELLED, because a fact arriving from a VALUE position spells `not` as the
/// dispatched `Bool.not` where every goal spells it `anthill.kernel.not`
/// (WI-567). Both are needed and neither subsumes the other: WI-756's `Red` case
/// is a carrier mismatch inside a correctly-spelled goal, WI-567's is the reverse.
pub(crate) fn goal_form(kb: &mut KnowledgeBase, v: Value) -> Value {
    let v = goal_form_carrier(kb, v);
    goal_form_proposition(kb, v)
}

/// WI-567 — the PROPOSITION half of the Γ vocabulary, applied at the two doors
/// [`goal_form`] serves and nowhere else.
///
/// [`goal_form_carrier`] settles how a fact is CARRIED; this settles how its
/// connectives are SPELLED. An `if` condition is VALUE position — it is an
/// operation-body expression and must evaluate at run time — so `if not(P)` loads
/// as the dispatched `Bool.not` (WI-529). The consumer that later reads it as a
/// PROPOSITION builds goal vocabulary (`negate_goal` mints `anthill.kernel.not`,
/// the NAF primitive). Γ is matched STRUCTURALLY, so before WI-567 an
/// `if not(isEmpty(xs))` fork deposited a fact that was structurally unequal to the
/// very goal it was about, and `head(xs)` in the then-branch kept its
/// `Error[EmptyStream]` — WI-567's one remaining acceptance clause. The routing
/// table is [`KnowledgeBase::goal_position_boolean`], shared with the loader's two
/// directions rather than re-spelled here.
///
/// REACH: the head, and then only through a NEGATION's operand. That bound is the
/// point, not thrift — `not`'s argument is the one operand position guaranteed to be
/// a proposition. Routing an ARBITRARY operand would be a category error: the `b` in
/// a fact `eq(x, not(b))` is a boolean VALUE, and rewriting it to the NAF primitive
/// would change what the fact says. `and` / `or` conditions are therefore left in
/// their value spelling and simply discharge nothing (conservative — the guard stays
/// present).
///
/// THAT BOUND IS NOT ABOUT `and` LACKING A GOAL READING, and this doc used to end by
/// saying it was ("`and` has no goal reading at all"). It has had one since
/// WI-20260822-J38JE (`kernel.and` over `push_and`, and §6.6 now calls the three
/// symmetric). The reason to leave an arbitrary operand alone is the category error
/// stated above and nothing else — which makes the bound STRONGER, since it no longer
/// rests on a property of one connective that has since changed. WI-20260825-P9Y67
/// re-measured this the expensive way: a loader change that redirected every rule-body
/// data slot made `rule r() :- holds(not(true))` stop matching `fact holds(not(true))`,
/// exit 0 and no diagnostic — this paragraph's own argument, one pass over. Corrected
/// via `/code-review`.
fn goal_form_proposition(kb: &mut KnowledgeBase, v: Value) -> Value {
    let ViewHead::Functor {
        functor: Some(f),
        pos_arity,
        named_arity,
    } = v.head(kb)
    else {
        return v;
    };
    // SHAPE FIRST, NAMES SECOND: a negation is unary and positional, so this test
    // rejects the common Γ fact (`eq(a, b)`, a match pattern, a `requires` clause)
    // before any symbol lookup — and this runs once per fact entering Γ, i.e. per
    // `if` / `match` arm / `let` in every operation body the typer walks.
    // `named_arity == 0` is not just thrift: the swap rebuilds POSITIONALLY,
    // exactly as `negate_goal`'s functor swap does, so a named-form
    // `not(query: ..)` must keep its value spelling rather than lose the named
    // channel into a wrong-arity goal.
    if pos_arity != 1 || named_arity != 0 {
        return v;
    }
    // No `kernel.not` (a prelude-less KB) ⇒ no goal vocabulary to route INTO, so
    // the fact rides in its value spelling rather than be dropped.
    let Some(not_sym) = kb.try_resolve_symbol("anthill.kernel.not") else {
        return v;
    };
    // A NEGATION is the goal primitive itself (a `negate_goal` wrapper, already in
    // goal vocabulary) or the value op that routes to it (a source `if not(..)`).
    // `pos_arity`, not a literal `1`: the gate above already established it, and the
    // routing table carries its own arity column, so a second hand-spelled `1` here
    // would be a third copy of "`not` is unary" — the shape this table exists to have
    // ONE of. Behaviour-identical today (the gate makes it exactly 1); it stops being
    // so the moment either the table or the gate moves, which is the point.
    if f != not_sym && kb.goal_position_boolean(f, pos_arity) != Some(not_sym) {
        return v;
    }
    // Within the declared arity, so a `None` is a malformed goal rather than a case
    // to skip — the same stance `negate_goal` takes one function below.
    let inner = v
        .pos_arg(kb, 0)
        .expect("pos_arg in range during goal_form_proposition")
        .to_value();
    // Recurse on the operand only (`goal_form_proposition`, not `goal_form`): the
    // carrier pass already ran over the whole fact, and re-running it would re-lower
    // an already-lowered child.
    let inner = goal_form_proposition(kb, inner);
    kb.make_goal_value(not_sym, vec![inner])
}

/// The CARRIER half of [`goal_form`] — see its doc for the whole contract.
fn goal_form_carrier(kb: &mut KnowledgeBase, v: Value) -> Value {
    match v {
        Value::Node(occ) => {
            let lowered = crate::kb::node_occurrence::try_occurrence_to_term(kb, &occ)
                .filter(|t| !matches!(kb.get_term(*t), Term::Bottom))
                .and_then(|t| kb.term_body_to_nodes(&[t]).into_iter().next());
            match lowered {
                Some(n) => Value::Node(n),
                None => Value::Node(occ),
            }
        }
        Value::Entity {
            functor,
            pos,
            named,
        } => Value::Entity {
            functor,
            pos: pos
                .iter()
                .map(|c| goal_form_carrier(kb, c.clone()))
                .collect(),
            named: named
                .iter()
                .map(|(k, c)| (*k, goal_form_carrier(kb, c.clone())))
                .collect(),
        },
        Value::Tuple { pos, named } => Value::Tuple {
            pos: pos
                .iter()
                .map(|c| goal_form_carrier(kb, c.clone()))
                .collect(),
            named: named
                .iter()
                .map(|(k, c)| (*k, goal_form_carrier(kb, c.clone())))
                .collect(),
        },
        other => other,
    }
}

/// WI-538 — the goal an in-body `proof <target> by <strategy> [conclude P]`
/// discharges (typer, `Expr::Proof`). Named and `pub` so a test can DRIVE the
/// site's own construction instead of re-spelling it: the Γ the site proves
/// under is transient (`Env::flow`, never stored), and a discharged conclusion
/// is only `assume`d into that Γ — where it is re-derivable from KB ∪ Γ by
/// construction — so the discharge VERDICT has no end-to-end observable, and
/// this pairing with [`prove_from_gamma`] is the closest a test can get.
///
/// The `conclude` proposition is put in the Γ vocabulary ([`goal_form`]) — the
/// same form the other two `prove_from_gamma` obligation sites get for free by
/// building their goal from a clause term (WI-539's σ-substituted `requires`,
/// WI-558's contract `ensures`). WI-756: handing the RAW `conclude` occurrence
/// to the resolver instead made its open-world gate (`resolve.rs`'s
/// `force_delay` → [`KnowledgeBase::value_has_open_world_ref`] →
/// `occurrence_has_var_ref`) read `Red` as a runtime binder, so the goal
/// force-delayed and NO in-body proof over a bare constructor could discharge —
/// not even the reflexive `conclude eq(Red, Red)`, and `conclude eq(Green, Red)`
/// over a carrier whose own `eq` holds stayed unproved.
pub fn in_body_proof_goal(
    kb: &mut KnowledgeBase,
    target: Symbol,
    conclude: Option<&Rc<NodeOccurrence>>,
) -> Value {
    match conclude {
        Some(c) => goal_form(kb, Value::Node(Rc::clone(c))),
        // Short form: the goal is the `target` rule as a 0-ary atom.
        // Incompleteness (sound, not unsound): an N-ary rule head is not
        // reconstructed with fresh vars, so the arity mismatch fails the
        // unifier — short-form discharge currently fires only for genuinely
        // 0-ary rules. Reconstructing N-ary heads is a follow-on.
        None => kb.make_goal_value(target, Vec::new()),
    }
}

/// Constructively **refute** a guard: prove its negation from Γ (proposal
/// 050 / 048). A guarded effect is dropped only on a positive proof of
/// `¬guard`; an unrefutable guard (a symbolic parameter) stays present —
/// the conservative default.
pub fn refute_guard(kb: &mut KnowledgeBase, flow: &FlowEnv, guard: &Value) -> bool {
    match negate_goal(kb, guard) {
        Some(neg) => prove_from_gamma(kb, flow, &neg),
        // Cannot form the negation ⇒ cannot refute ⇒ keep the effect (sound).
        None => false,
    }
}

/// Negate a guard for refutation (proposal 050 open question C). `eq ⇄ neq`
/// by **functor swap**, so a branch's positive `neq(b, 0)` fact discharges an
/// `eq(b, 0)` guard by resolving the `neq(b, 0)` fact straight out of the Γ
/// overlay — a `not(eq(..))` wrapper would not match the `neq` fact and could
/// only ever flounder. Any other predicate
/// negates by the reflect `not(..)` wrapper (resolved open-world by NAF +
/// floundering). `None` when the kernel's `not` is unavailable (a prelude-less
/// KB) — the caller then keeps the effect rather than guess.
pub(super) fn negate_goal(kb: &mut KnowledgeBase, goal: &Value) -> Option<Value> {
    let (eq_sym, neq_sym) = eq_neq_functors(kb);
    if let ViewHead::Functor {
        functor: Some(f),
        pos_arity,
        named_arity,
    } = goal.head(kb)
    {
        let swapped = if f == eq_sym {
            neq_sym
        } else if Some(f) == neq_sym {
            Some(eq_sym)
        } else {
            None
        };
        // The functor swap rebuilds the goal positionally (`make_goal_value` is
        // positional-only), so it is only faithful when the goal carries no named
        // args. A named-form `eq(a: .., b: ..)` (legal — the op declares named
        // params) falls through to the `not(..)` wrapper below, which preserves
        // the whole goal (it flounders → effect conservatively kept) rather than
        // silently dropping the named channel into a wrong-arity goal.
        if let (Some(target), 0) = (swapped, named_arity) {
            let mut args = Vec::with_capacity(pos_arity);
            for i in 0..pos_arity {
                // A positional slot inside the declared arity must be present;
                // a None here is a malformed goal, not a case to skip silently.
                let item = goal
                    .pos_arg(kb, i)
                    .expect("pos_arg in range during negate_goal");
                args.push(item.to_value());
            }
            return Some(kb.make_goal_value(target, args));
        }
    }
    kb.try_resolve_symbol("anthill.kernel.not")
        .map(|not_sym| kb.make_goal_value(not_sym, vec![goal.clone()]))
}

// ── Proposal 050 (WI-537): match-arm Γ narrowing ───────────────
//
// The producer side of the proposal-050 `match` modification rule: an arm
// narrows Γ with its pattern fact and the negations of earlier arms, just as
// the `if`-fork (above) narrows with the branch condition / its negation.
// `prove_from_gamma` is the consumer side. Like the `if`-fork these facts are
// additive — read by WI-067 discharge / WI-538 proofs — so they change no
// types or effects.

/// Resolve a pattern's constructor NAME to the scrutinee's constructor it names.
/// Constructor patterns are written by SHORT NAME (`case Red`, `case some(x)`); the
/// scrutinee's type picks which sort's constructor, so this is the pattern equivalent of
/// name resolution (`resolve_in_scope`), scoped to the scrutinee's OWN constructors.
/// Returns the resolved scrutinee constructor, or `None` if the name names none of them.
///
/// WI-672: this is a short-name LOOKUP (resolving a written name to a symbol), NOT an
/// identity comparison. The loaded pattern name is a fresh binder symbol
/// (`load_pattern_var`'s `binder_sym`) carrying only a display name, so matching it to a
/// constructor can only be by name — the pattern equivalent of resolving any written
/// identifier. Callers then hold the RESOLVED constructor and compare it canonically
/// downstream, so `same_symbol`'s last-segment bridge no longer rides pattern coverage.
pub(super) fn resolve_pattern_ctor(
    kb: &KnowledgeBase,
    name: Symbol,
    scrutinee_ctors: &[Symbol],
) -> Option<Symbol> {
    let want = short_name_of(kb.qualified_name_of(name));
    scrutinee_ctors
        .iter()
        .copied()
        .find(|&c| short_name_of(kb.qualified_name_of(c)) == want)
}

/// A `Var`-pattern name resolved to the NULLARY constructor it names, or `None` if it is
/// a plain binding (`case x`). Resolves against the scrutinee's constructor set by short
/// name ([`resolve_pattern_ctor`]); failing that, a globally-known constructor symbol is
/// taken as-is; either way the arity gate below has the last word.
///
/// NOT called directly by the readers — they go through [`var_pattern_ctor`], which adds
/// the `: T` gate. Three of them share it: [`collect_covered_entities`] (coverage),
/// [`pattern_match_value`] (the Γ pattern fact) and [`match_arm_nullary_ctor`] (the
/// WI-20260827-EJ5F5 rewrite that makes the arm actually MATCH the constructor), so none
/// can drift on what counts as one.
///
/// WI-946 examined the fallback below and left it: `name` is `load_pattern_var`'s
/// FRESH BINDER SYMBOL (see [`resolve_pattern_ctor`]), never the entity's own, so
/// neither disjunct can fire and swapping the strict view for the total one is
/// unobservable. Measured, not reasoned: `case Blue` over a `Colour` scrutinee,
/// where `Blue` is a nullary constructor of ANOTHER enum and therefore genuinely
/// `is_constructor_symbol`, is treated as a catch-all BINDER — the exhaustiveness
/// check reports no missing `Green`, exactly as for a free-standing `entity Bare`.
/// That the two agree is what shows the fallback is dead rather than strict-biased.
pub(super) fn pattern_var_ctor_sym(
    kb: &KnowledgeBase,
    name: Symbol,
    scrutinee_ctors: &[Symbol],
) -> Option<Symbol> {
    let candidate = resolve_pattern_ctor(kb, name, scrutinee_ctors).or_else(|| {
        (kb.is_constructor_symbol(name) || kb.strict_parent_sort(name).is_some()).then_some(name)
    })?;
    // WI-20260827-EJ5F5: NULLARY only. A bare name is a constructor pattern exactly
    // when the constructor it names needs no arguments to BE a value; `case cons` over
    // a `List` names a constructor that takes two fields, so the written text is not a
    // value and cannot be one arm of a case split. Before this gate all three readers
    // took it for a covering pattern: exhaustiveness recorded `cons` as covered (while
    // the arm in fact behaves as a catch-all binder, so every later arm was dead), and
    // `pattern_match_value` put `eq(scrutinee, Ref(cons))` into the arm's Γ and
    // `neq(scrutinee, Ref(cons))` into every later one — a ground claim about a symbol
    // that denotes no value. Gated HERE rather than at each reader so the coverage,
    // Γ and rewrite readers cannot drift on what a bare name means. The rewrite asks one
    // question MORE ([`declares_a_nullary_entity`]) — see there for why that is a second
    // question and not a second answer to this one.
    takes_no_fields(kb, candidate).then_some(candidate)
}

/// A name that does not take arguments — the only kind a BARE name in a pattern can
/// denote (see [`pattern_var_ctor_sym`]). PERMISSIVE by design: it asks only that the
/// symbol is not KNOWN to take fields, so a symbol the KB declares nothing for answers
/// TRUE. `register_declared_field_types` runs for EVERY entity (kb/load.rs, WI-936), so a
/// declared nullary constructor is an EMPTY row and a fielded one can never read as
/// nullary by being absent from the registry — the permissiveness reaches only names no
/// declaration covers.
///
/// That is the right answer for the two readers that only NAME a constructor — coverage
/// and the Γ pattern fact — and both are meaningful over a hand-built KB whose symbols
/// were interned rather than declared. MEASURED: spelling this strictly fails
/// `wi537_local_interpretation_test::match_nullary_ctor_arms_accumulate_negations`, whose
/// `case red` stops carrying `eq(s, red)` so the later arms lose their negations. It is
/// NOT the right answer for the rewrite, which is why the next predicate exists.
fn takes_no_fields(kb: &KnowledgeBase, ctor: Symbol) -> bool {
    kb.entity_field_types(ctor).is_none_or(|f| f.is_empty())
}

/// A DECLARED entity that takes no fields — [`takes_no_fields`] AND the declaration.
///
/// The extra condition the REWRITE needs, for a reason the other two readers have not
/// got: it turns its answer into a `Pattern::Constructor` the matcher then tests
/// STRUCTURALLY, and a name the KB declares no entity for has no structure to match, so
/// the arm would never fire — silently. Naming a constructor and being able to MATCH one
/// are two questions; only this one is about matching, which is why it is a second
/// predicate rather than a stricter spelling of the first.
///
/// NO LOADED PROGRAM SEPARATES THE TWO, and it is said here rather than left to be
/// rediscovered. The symbols that differ come from `pattern_var_ctor_sym`'s near-dead
/// `strict_parent_sort` disjunct (a SORT name) and from a hand-built KB; WI-946 measured
/// that disjunct unreachable from source — `name` is `load_pattern_var`'s FRESH BINDER
/// SYMBOL, neither a constructor nor a sort. Written the strict way because this ticket
/// changed the consequence of a wrong `true`, not because a row demands it.
pub(super) fn declares_a_nullary_entity(kb: &KnowledgeBase, ctor: Symbol) -> bool {
    matches!(kb.entity_field_types(ctor), Some(f) if f.is_empty())
}

/// A local binder reference as a Γ `Value` — its WI-537 `var_ref(x)` term twin
/// (head `Functor{var_ref}`, one `name` child), the indexable form every body
/// reference to the binder also reads as. The single place this shape is built,
/// shared by the `let x ≡ e` fact ([`binding_gamma_fact`]) and the match arm
/// destructure fact ([`pattern_match_value`]); if the canonical binder-reference
/// form ever moves again (it migrated Ident→Opaque→var_ref across WI-537), both
/// producers move with it.
fn binder_ref_value(name: Symbol, span: crate::span::SourceSpan, owner: Option<Symbol>) -> Value {
    Value::Node(NodeOccurrence::new_expr(Expr::VarRef { name }, span, owner))
}

/// The value a `match` pattern matches, as a Γ-fact RHS. Two callers, one shape:
///   - `admit_binders = false` → the GROUND value, the RHS of a LATER arm's
///     negation `neq(scrutinee, value(p))`. `None` for a binder / binder-bearing
///     constructor — a whole family no single value can soundly negate (only the
///     existential `¬∃v. s = some(v)` would; 050 open Q C, deferred).
///   - `admit_binders = true` → the arm's OWN positive `eq(scrutinee, value(p))`,
///     which additionally reads a binder as its `var_ref(x)` twin (WI-550): a
///     bare `case x` → the alias `x ≡ s`; `case some(x)` → `some(var_ref(x))`,
///     the destructure fact relating the binder to the scrutinee.
/// For a fully-ground pattern the two modes coincide, so a ground arm's `eq` and
/// its later-arm `neq` speak the same value. In BOTH modes a `Wildcard` (and a
/// constructor with a wildcard hole, `some(_)`) yields `None` — no referenceable
/// value. Mappings: literal `0` → `Const(0)`; nullary ctor `none`/`red` →
/// `Ref(ctor)` (the CANONICAL symbol via [`pattern_var_ctor_sym`], so the fact
/// `Ref`-matches a resolved reference elsewhere); `some(none)` → `some(none)`.
/// Tuple patterns are deferred (`None`).
fn pattern_match_value(
    kb: &mut KnowledgeBase,
    pattern: &Rc<NodeOccurrence>,
    scrutinee_ctors: &[Symbol],
    admit_binders: bool,
) -> Option<Value> {
    match pattern.as_pattern()? {
        Pattern::Wildcard => None,
        Pattern::Literal { value } => Some(Value::term(kb.alloc(Term::Const(value.clone())))),
        Pattern::Var { name, .. } => {
            // `case red` (nullary ctor) → its CANONICAL `Ref` (the scrutinee-set
            // symbol, not the bare loaded `*name`, so it `Ref`-matches a resolved
            // reference). A binding `case x` → the binder's `var_ref(x)` twin, but
            // ONLY in `admit_binders` mode; for a negation it has no ground value.
            match var_pattern_ctor(kb, pattern, *name, scrutinee_ctors) {
                Some(ctor) => Some(Value::term(kb.alloc(Term::Ref(ctor)))),
                None => admit_binders.then(|| binder_ref_value(*name, pattern.span, pattern.owner)),
            }
        }
        Pattern::Constructor {
            name,
            pos_args,
            named_args,
        } => {
            let name = *name;
            // Every sub-pattern must yield a value (`?` short-circuits to `None`
            // on the first one that doesn't — a wildcard hole in either mode, or a
            // binder hole when `!admit_binders`). Sub-patterns resolve against no
            // outer ctor set — a bare name in argument position is a binding unless
            // it is itself a known constructor (`some(none)`).
            let mut pos: Vec<Value> = Vec::with_capacity(pos_args.len());
            for sub in pos_args {
                pos.push(pattern_match_value(kb, sub, &[], admit_binders)?);
            }
            let mut named: Vec<(Symbol, Value)> = Vec::with_capacity(named_args.len());
            for (field, sub) in named_args {
                named.push((*field, pattern_match_value(kb, sub, &[], admit_binders)?));
            }
            // A 0-ary `Constructor` (rare — nullary ctors parse as Var-patterns)
            // normalizes to the canonical `Ref` form (WI-436: Ref(c) ≡ nullary
            // Fn{c}) so it matches a nullary ctor written elsewhere.
            Some(if pos.is_empty() && named.is_empty() {
                Value::term(kb.alloc(Term::Ref(name)))
            } else {
                Value::Entity {
                    functor: name,
                    pos: Rc::from(pos),
                    named: Rc::from(named),
                }
            })
        }
        Pattern::Tuple { .. } => None,
    }
}

/// The proposal-050 binding fact `x ≡ value` for `let x = value` (WI-550): the
/// binder's `var_ref(x)` reference twin (the indexable form WI-537 gave a
/// binder, now per-site unique) equated to the bound `value`. The caller gates
/// on a PURE value (`x` denotes the value of an effect-free `e`) and `assume`s
/// the result into the body's Γ, where it later lets a consumer (WI-067
/// discharge) relate `x` to its value. `assume` keeps any indexable `value` (a
/// literal, binder, constructor, or pure call) and drops only a genuinely
/// `Opaque`-headed one (a lambda / collection literal / control-flow form)
/// losslessly.
pub fn binding_gamma_fact(
    kb: &mut KnowledgeBase,
    binder: Symbol,
    value: Value,
    span: crate::span::SourceSpan,
    owner: Option<Symbol>,
) -> Value {
    let eq_sym = kb.eq_functor();
    let binder_ref = binder_ref_value(binder, span, owner);
    kb.make_goal_value(eq_sym, vec![binder_ref, value])
}

/// Per-arm Γ facts for a `match` — the producer side of the proposal-050
/// `match` modification rule (WI-537). For arm `i` (`arms[i]`) the returned
/// facts narrow that arm's Γ:
///
///   - `eq(scrutinee, value(pᵢ))` — the pattern fact: in arm `i` the scrutinee
///     has `pᵢ`'s shape. The value includes binders as their `var_ref` twin
///     (`case some(x)` ⟹ `eq(s, some(var_ref(x)))`, WI-550) — see
///     [`pattern_match_value`] (`admit_binders = true`). Absent when `pᵢ` denotes
///     no referenceable value (a wildcard, or a constructor with a wildcard hole).
///   - `neq(scrutinee, value(pⱼ))` for each earlier arm `j < i` whose pattern is
///     GROUND and UNGUARDED — the scrutinee is known to differ from `pⱼ`'s
///     value. `case 0 → … ; case _ → div(a, s)` thus carries `neq(s, 0)` into
///     the wildcard arm (the canonical WI-067 discharge: a guard `eq(s, 0)` is
///     refuted from Γ). A guarded earlier arm matches only conditionally, a
///     non-ground one only partially — neither excludes its value from later
///     arms, so neither contributes a negation. (The "not-any" negation of a
///     binder pattern, `¬∃x. s = some(x)`, needs a reified form — 050 open Q C —
///     and is deferred.)
///
/// `arms` is `(pattern, has_guard)` in source order. Facts are built with the
/// same carrier (`make_goal_value` / `eq` / `neq`) the bridge and the `if`-fork
/// use, so they index and match identically; `assume` later drops any whose
/// scrutinee or value heads `Opaque` (a control-flow / lambda scrutinee, say —
/// a plain call or constructor scrutinee indexes fine) — losslessly, since such
/// a fact could never match a goal-shaped query.
pub fn match_arm_gamma_facts(
    kb: &mut KnowledgeBase,
    scrutinee: &Value,
    arms: &[(Rc<NodeOccurrence>, bool)],
    scrutinee_ctors: &[Symbol],
) -> Vec<Vec<Value>> {
    let eq_sym = kb.eq_functor();
    let neq_sym = kb.try_resolve_symbol("anthill.prelude.PartialEq.neq");
    let mut out: Vec<Vec<Value>> = Vec::with_capacity(arms.len());
    // Negations accumulated from earlier ground, unguarded arms.
    let mut earlier_neqs: Vec<Value> = Vec::new();
    for (pattern, has_guard) in arms {
        // POSITIVE fact value: what this arm matches, binders included as their
        // `var_ref` twin (`case some(x)` ⟹ `some(var_ref(x))`) — WI-550.
        let positive = pattern_match_value(kb, pattern, scrutinee_ctors, true);
        // NEGATION value: the GROUND value a LATER arm can soundly exclude (a
        // binder / non-ground pattern is `None`).
        let ground = pattern_match_value(kb, pattern, scrutinee_ctors, false);
        let mut facts: Vec<Value> = earlier_neqs.clone();
        if let Some(pv) = &positive {
            facts.push(kb.make_goal_value(eq_sym, vec![scrutinee.clone(), pv.clone()]));
        }
        out.push(facts);
        // A ground, unguarded arm excludes its value from every LATER arm: it
        // matches exactly that value (ground), unconditionally (unguarded). A
        // binder arm (`case some(x)`) would exclude later arms only via the
        // existential "not-any" negation `¬∃v. s = some(v)` (050 open Q C reified
        // form, deferred — co-designed with the WI-067 consumer), so it adds none.
        if !has_guard {
            if let (Some(pv), Some(neq)) = (ground, neq_sym) {
                earlier_neqs.push(kb.make_goal_value(neq, vec![scrutinee.clone(), pv]));
            }
        }
    }
    out
}

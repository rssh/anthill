//! Type compatibility (subtyping): `types_compatible`, variance, join/meet, branch
//! joins, and witness-provides admissibility.

use super::*;

// ── Type compatibility (subtyping) ─────────────────────────────

/// Check if `actual` type is compatible with (subtype of) `expected` type.
/// Works on Type entity terms: sort_ref, parameterized, arrow, named_tuple, type_var, nothing.
/// Lattice `≤` on type terms — `actual <: expected` with reflexivity.
/// Alias for [`types_compatible`]; prefer this name when the directional
/// nature of the relation matters (subtype check, effect-element
/// compatibility, etc.). The strict (irreflexive) version is
/// [`is_subtype`].
///
/// WI-326: takes `&mut KnowledgeBase` because [`arrow_compatible_view`] now
/// invokes row subtyping, which allocates fresh row-tail vars in the
/// both-open case.
///
/// WI-335: takes `&mut Substitution` so nested arrow checks (e.g.
/// `arrow_compatible`'s param + result + effects sub-checks, plus any
/// recursive descent through [`parameterized_compatible_view`] /
/// [`named_tuple_compatible`] / [`arrow_function_compatible`]) thread
/// **one** substitution through the whole sub-tree. This makes row-var
/// bindings from one sub-position visible to sibling positions —
/// fixing the soundness gap where nested arrows sharing a row var
/// across positions got inconsistent bindings under independent local
/// substitutions.
///
/// **Caller contract**: most call sites want each check independent of
/// any other check; they allocate `Substitution::new()` per call. Call
/// sites in a row-aware chain (e.g. inside another `types_compatible`
/// frame) thread the same subst through.
///
/// **Failure semantics**: when this function returns `false`, the
/// substitution may carry partial bindings from sub-checks that
/// succeeded before a sibling failed (and may even be marked
/// `is_contradiction()`). Callers that intend to make a subsequent
/// independent decision after a `false` result MUST discard the
/// substitution (or snapshot before the call). Threading-through
/// callers in this module rely on the early-return-on-false discipline
/// and never re-use a failed subst.
pub fn types_lesseq(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: TermId,
    expected: TermId,
) -> bool {
    types_compatible(kb, subst, &TermIdView(actual), &TermIdView(expected))
}

/// WI-342 P4-B2: subtype/compatibility, carrier-agnostically. Mirrors
/// [`unify_types`]'s split — the hot `(TermId, TermId)` path stays byte-identical
/// in [`types_compatible_term_dispatch`]; a `Value`-carrier side routes to
/// [`types_compatible_view_structural`] (the unify/subtype lockstep, so a
/// denoted-bearing type compares consistently in both directions). Note the
/// term dispatch does NOT walk its inputs through `subst` at the top (unlike
/// `unify_types`) — callers pass already-resolved types — so the entry only
/// dispatches on the carrier, preserving that contract.
pub fn types_compatible<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &B,
) -> bool {
    match (actual.as_bind_value(), expected.as_bind_value()) {
        (BindValue::Term(a), BindValue::Term(e)) => types_compatible_term_dispatch(kb, subst, a, e),
        _ => types_compatible_view_structural(kb, subst, actual, expected),
    }
}

/// The `TermId`-only subtype dispatch — byte-identical to the pre-P4-B2
/// `types_compatible` body. Reached when both sides are hash-consed carriers.
fn types_compatible_term_dispatch(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: TermId,
    expected: TermId,
) -> bool {
    if actual == expected {
        return true;
    }

    // WI-361: dispatch on the canonical form tag (see `type_dispatch_name`) so a
    // term-backed `Ref(S)` / `Fn{S,named}` routes through the same arms as the
    // deep `sort_ref` / `parameterized`.
    let actual_functor = type_dispatch_name(kb, actual);
    let expected_functor = type_dispatch_name(kb, expected);

    // type_var is compatible with anything (wildcard for inference)
    if actual_functor == Some("type_var") || expected_functor == Some("type_var") {
        return true;
    }

    // nothing is bottom — compatible with any type
    if actual_functor == Some("nothing") {
        return true;
    }

    // WI-400 (ζ): a neutral projection is its own rigid type — equal only to an identical
    // neutral, never to a concrete type. Placed AFTER the type_var / nothing wildcards so
    // a neutral still flows into an unconstrained var for inference.
    if let Some(verdict) = expr_carried_zeta(kb, &TermIdView(actual), &TermIdView(expected)) {
        return verdict;
    }

    match (actual_functor, expected_functor) {
        (Some("sort_ref"), Some("sort_ref")) => {
            bare_sort_compatible(kb, subst, &TermIdView(actual), &TermIdView(expected))
        }
        (Some("parameterized"), Some("parameterized")) => {
            // WI-342 dispatch consolidation: route through the carrier-agnostic
            // subtype relation (TermId wrapped in TermIdView) — one impl, no
            // term-specific twin to drift from.
            parameterized_compatible_view(kb, subst, &TermIdView(actual), &TermIdView(expected))
        }
        // Name-binding normalization: a bare sort name `S` is `S` with
        // its type params unconstrained — it is compatible with any
        // instantiation `S[bindings]` and vice versa. The typer infers
        // a bare type for nullary constructors (`nil()` → `List`,
        // `none()` → `Option`), so a body whose branches mix `List` and
        // `List[T = Row]` must still satisfy a `List[T = Row]` return
        // annotation. Only the base sort identity is checked here; the
        // bindings on the parameterized side stand unconstrained
        // against the bare side.
        (Some("sort_ref"), Some("parameterized")) => {
            // WI-381: a structured (ground) defined-type / alias on the bare side
            // resolves to its underlying shape and re-dispatches as parameterized — so
            // `IntList` vs `List[T = Int]` CHECKS the bindings (`T = Int` kept) and an
            // `IntList` value conforms to its own definition. Without this, the
            // bare↔param arm below checks base-sort nominal compat ONLY, dropping the
            // alias's fixed bindings.
            if let Some(shape) = extract_sort_ref_sym(kb, &TermIdView(actual))
                .and_then(|s| resolve_alias_shape(kb, s))
            {
                return types_compatible(kb, subst, &TermIdView(shape), &TermIdView(expected));
            }
            // bare `S` vs `B[…]`: nominal base-sort compatibility, then (WI-402)
            // BINDING-PRECISE provider admissibility — a concrete carrier vs a
            // parameterized spec it provides checks every expected binding against
            // the provider fact's value, so the bindings are never dropped (the
            // hazard that confines the bare-spec accept to the bare↔bare arm
            // above). WI-361: `parameterized_base_sym` reads the base sort
            // form-agnostically (deep `base` field or the term-backed functor).
            match (
                extract_sort_ref_sym(kb, &TermIdView(actual)),
                parameterized_base_sym(kb, expected),
            ) {
                (Some(a), Some(eb)) => {
                    sort_sym_compatible(kb, a, eb)
                        || bare_provider_binding_precise(kb, subst, a, &TermIdView(expected))
                }
                _ => false,
            }
        }
        (Some("parameterized"), Some("sort_ref")) => {
            // WI-381: mirror — resolve a structured alias on the bare (expected) side.
            if let Some(shape) = extract_sort_ref_sym(kb, &TermIdView(expected))
                .and_then(|s| resolve_alias_shape(kb, s))
            {
                return types_compatible(kb, subst, &TermIdView(actual), &TermIdView(shape));
            }
            match (
                extract_sort_ref_sym(kb, &TermIdView(expected)),
                parameterized_base_sym(kb, actual),
            ) {
                // WI-405 FACET A: a parameterized carrier `S[bindings]` — including a
                // PARTIAL form such as a constructor result `S[A = ?_]` — conforms to a
                // BARE provider spec it provides. `sort_provides_admissibly` is base-only,
                // which is sound here precisely because the expected spec is bare (it
                // carries no bindings to drop) — the same reasoning that confines the
                // WI-344 accept to the bare↔bare arm. Applying it here too makes provider
                // admissibility UNIFORM across the dispatch arms (the WI-405 root cause).
                //
                // WI-466: the parameterized side is the ACTUAL, the sort_ref side the
                // EXPECTED, so the nominal check is `sort_sym_compatible(actual=ab,
                // expected=e)` — matching the `(sort_ref, parameterized)` sibling arm and
                // the `sort_provides_admissibly(ab, e)` beside it. The pre-WI-466 call
                // passed `(e, ab)` (swapped): it (1) false-REJECTED a parameterized actual
                // whose base refines/is-entity-of the bare expected (`Refined[T=Int64]` vs
                // `Base` where `Refined requires Base`), and (2) false-ACCEPTED the reverse
                // (a `Base[..]` where an expected spec that refines `Base` was demanded) —
                // a soundness hole.
                (Some(e), Some(ab)) => {
                    // WI-20260829-N01PY: the witness leg LAST — see
                    // [`witness_provides_admissibly`] for why the carrier-keyed
                    // `sort_provides_admissibly` cannot answer for a witness-provided
                    // carrier, and why this one costs a bucket read on the common path.
                    //
                    // NO entity→parent hop, and unlike the bare arm's this is MEASURED at
                    // this site: /code-review read `ab = parameterized_base_sym(actual)`
                    // as possibly a CONSTRUCTOR symbol, so a witness keyed on the parent
                    // sort would be missed. Probed with an entity-parameterized actual
                    // (`boxed(v: 1)` against `provides Cap[C = Box[T = T]]`), the actual
                    // arrives as the PARENT `Box[T = Int64]` and the row loads — so there
                    // is nothing for a hop to reach here either.
                    sort_sym_compatible(kb, ab, e)
                        || sort_provides_admissibly(kb, ab, e)
                        || witness_provides_admissibly(kb, WitnessActual::Term(actual), ab, e)
                }
                _ => false,
            }
        }
        (Some("arrow"), Some("arrow")) => {
            arrow_compatible_view(kb, subst, &TermIdView(actual), &TermIdView(expected))
        }
        // `arrow` is the typer's shorthand for the stdlib `Function[A, B, E]`
        // (see `arrow_parts`), so a lambda's `arrow(Int, Int)` body satisfies
        // a declared `Function[Int, Int]` return and vice versa. (WI-289)
        (Some("arrow"), Some("parameterized")) | (Some("parameterized"), Some("arrow")) => {
            arrow_function_compatible(kb, subst, &TermIdView(actual), &TermIdView(expected))
        }
        (Some("named_tuple"), Some("named_tuple")) => {
            named_tuple_compatible(kb, subst, &TermIdView(actual), &TermIdView(expected))
        }
        (Some("effects_rows"), Some("effects_rows")) => {
            // WI-333: row subsumption via [`subtype_effect_rows`]. The
            // identical-TermId case is already short-circuited by
            // [`KnowledgeBase`]'s hash-consing at the top of
            // [`types_compatible`]; this arm reaches when both sides are
            // effects_rows wrappers with structurally-distinct payloads.
            //
            // WI-335: uses the threaded subst so row-var bindings from
            // sibling positions are visible. This affects multiple
            // entry paths into this arm:
            //   - direct (effects_rows, effects_rows) comparison;
            //   - parameterized_compatible recursing on Function[E]
            //     bindings (the WI-333 path);
            //   - any nested types_compatible inside an arrow's param /
            //     result / effects sub-check.
            // Pre-WI-335 a local scratch subst meant each invocation
            // reasoned in isolation, accepting nested arrows /
            // parameterized bindings whose shared row var had no
            // consistent global binding across sibling positions.
            subtype_effect_rows(kb, subst, &TermIdView(actual), &TermIdView(expected))
        }
        _ => {
            // WI-441: a pair with one ROW-shaped side (a bare `open(?ρ)` row
            // binding vs a rigid row var, a wrapper vs a bare expression) is
            // a row comparison — see the unify-dispatch twin.
            if value_is_row_shaped(kb, &TermIdView(actual))
                || value_is_row_shaped(kb, &TermIdView(expected))
            {
                subtype_effect_rows(kb, subst, &TermIdView(actual), &TermIdView(expected))
            } else {
                false
            }
        }
    }
}

/// WI-342 P4-B2: carrier-agnostic subtype dispatch — the [`TermView`] analog of
/// [`types_compatible_term_dispatch`], reached when at least one side is a
/// `Value` carrier (a `Value::Node`). Resolves both through `subst`; if both
/// land on a hash-consed `Term`, hands back to the term dispatch. Otherwise
/// dispatches the forms `unify_types` already handles cross-carrier, keeping the
/// two relations in lockstep: `denoted` (value-in-type subtyping IS equality →
/// the same Ref-compare unify uses), `arrow` (contravariant param / covariant
/// result / covariant effects), `effects_rows`, `parameterized`.
///
/// EVERY non-`false` arm of the term dispatch now has a peer here — `named_tuple` and
/// both `sort_ref`↔`parameterized` directions were wired after that sentence was
/// written, and `sort_ref`↔`sort_ref` by WI-RKMD4, which was the last one missing and the
/// only one whose absence was a WRONG answer rather than a conservative one (two
/// identical bare sorts read as a mismatch). What reaches `_ => false` below is a FORM
/// MISMATCH or a variable, for both of which `false` is the verdict rather than a
/// deferral.
pub(super) fn types_compatible_view_structural<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &B,
) -> bool {
    let a = walk_view(kb, subst, actual);
    let e = walk_view(kb, subst, expected);
    if let (Value::Term { id: x, .. }, Value::Term { id: y, .. }) = (&a, &e) {
        return types_compatible_term_dispatch(kb, subst, *x, *y);
    }

    // WI-361: canonical type tag, not raw functor (see `unify_view_structural`) —
    // a flipped parameterized / term-backed `Fn{S, named}` routes to the
    // `parameterized` arms instead of falling through to the re-grounding bridge.
    let af = type_dispatch_name_view(kb, &a);
    let ef = type_dispatch_name_view(kb, &e);
    // type_var is the inference wildcard; nothing is bottom (subtype of all).
    if af == Some("type_var") || ef == Some("type_var") {
        return true;
    }
    if af == Some("nothing") {
        return true;
    }

    // WI-400 (ζ): neutral projection — same decision as the term dispatch, carrier-
    // agnostic (a compound `a.b.T` rides a `Value::Node` ExprCarried, so it reaches here).
    if let Some(verdict) = expr_carried_zeta(kb, &a, &e) {
        return verdict;
    }

    match (af, ef) {
        // value-in-type: `denoted(c) <: denoted(d)` iff `c == d` (no proper
        // subtyping between distinct carried values) — the same relation unify
        // computes, so the two directions agree.
        (Some("denoted"), Some("denoted")) => unify_denoted_view(kb, &a, &e),
        (Some("arrow"), Some("arrow")) => arrow_compatible_view(kb, subst, &a, &e),
        (Some("effects_rows"), Some("effects_rows")) => subtype_effect_rows(kb, subst, &a, &e),
        (Some("parameterized"), Some("parameterized")) => {
            parameterized_compatible_view(kb, subst, &a, &e)
        }
        // WI-361/WI-342: `arrow` and `Function[A,B,E]` denote the same callable
        // type. Read the parts carrier-agnostically (no re-ground) so a
        // `Value::Node` arrow checks against a `Function` without a lossy bridge.
        // Dispatch is now canonical (`type_head`), so a term-backed `Fn{Function,
        // named}` reports `parameterized` and hits this arm directly too.
        (Some("arrow"), Some("parameterized")) | (Some("parameterized"), Some("arrow")) => {
            arrow_function_compatible(kb, subst, &a, &e)
        }
        (Some("named_tuple"), Some("named_tuple")) => named_tuple_compatible(kb, subst, &a, &e),
        // Bare `S` vs `B[…]`: nominal base-sort compatibility, then WI-402
        // binding-precise provider admissibility (mirrors
        // `types_compatible_term_dispatch`). `sort_sym_compatible` takes
        // (sort_ref-side sym, parameterized-side base); `sort_functor_of_view`
        // surfaces the head sym for a `sort_ref` and the base for a `parameterized`.
        // WI-RKMD4: the arm this dispatch was MISSING. Every other non-`false` arm of the
        // term dispatch has a peer here; this one did not, so two bare refs on a `Value`
        // carrier fell to the `_ => false` below and were reported as a mismatch even when
        // they were the SAME sort. Unreachable only by accident of production — a bare ref
        // is normally hash-consed, so the both-`Term` early return took it first — and a
        // silent wrong answer as soon as a non-`Term` producer existed, which is what
        // [`nominal_heads_compatible`] is. Through the SAME body the term arm runs, not a
        // second spelling of it.
        (Some("sort_ref"), Some("sort_ref")) => bare_sort_compatible(kb, subst, &a, &e),
        (Some("sort_ref"), Some("parameterized")) => {
            // WI-381: resolve a structured (ground) alias on the bare side and
            // re-dispatch — mirrors `types_compatible_term_dispatch` so the subtype
            // relation stays carrier-symmetric (the Node-carrier path must resolve
            // aliases just as the term path does, or an alias compared against a
            // denoted-bearing parameterized type would drop its fixed bindings).
            if let Some(shape) =
                sort_functor_of_view(kb, &a).and_then(|s| resolve_alias_shape(kb, s))
            {
                return types_compatible(kb, subst, &TermIdView(shape), &e);
            }
            match (sort_functor_of_view(kb, &a), sort_functor_of_view(kb, &e)) {
                // Nominal base, then (WI-402) binding-precise provider admissibility —
                // mirrors the term dispatch so the relation stays carrier-symmetric.
                (Some(av), Some(eb)) => {
                    sort_sym_compatible(kb, av, eb)
                        || bare_provider_binding_precise(kb, subst, av, &e)
                }
                _ => false,
            }
        }
        (Some("parameterized"), Some("sort_ref")) => {
            // WI-381: mirror — resolve a structured alias on the bare (expected) side.
            if let Some(shape) =
                sort_functor_of_view(kb, &e).and_then(|s| resolve_alias_shape(kb, s))
            {
                return types_compatible(kb, subst, &a, &TermIdView(shape));
            }
            match (sort_functor_of_view(kb, &e), sort_functor_of_view(kb, &a)) {
                // WI-405 FACET A: parameterized carrier vs bare provider spec — mirror the
                // term dispatch so provider admissibility stays carrier-symmetric.
                // WI-466: nominal check is `(actual=ab, expected=ev)` — the parameterized
                // side is the ACTUAL, the sort_ref the EXPECTED (the pre-WI-466 `(ev, ab)`
                // was swapped; see the term-dispatch twin for the two latent defects).
                // WI-20260829-N01PY — THE WITNESS LEG IS NOT ON THIS ARM, and that is a
                // KNOWN GAP rather than an oversight, so it is written down at the site
                // whose contract it breaks (one line up: "so provider admissibility stays
                // carrier-symmetric").
                //
                // ON THIS ARM, NOT IN THIS FUNCTION — the distinction matters because
                // WI-20260829-2NMXA is scoped from this comment. The `(sort_ref, sort_ref)`
                // arm above DOES reach the leg, through the `bare_sort_compatible` it
                // shares with the term dispatch, so a bare witnessed carrier on a `Value`
                // carrier is ACCEPTED here today. Whoever closes 2NMXA must add the leg to
                // this arm only; adding it to the function would double it (found by
                // /code-review, which read the earlier "NOT HERE" as the wider claim).
                //
                // MEASURED, a drivable pair: a DENOTED effect row on the actual
                // (`MappedStream[…, EF = {Modify[k]}]`) routes here instead of to the term
                // dispatch, and is REFUSED at `total(c: FiniteCollection)` while the
                // byte-identical ground-row twin is accepted. The pair is
                // `n01py_witness_provision_subtype_test::a_denoted_effect_row_is_a_known_gap`.
                //
                // WHY IT CANNOT SIMPLY BE ADDED: `witness_provides_admissibly` asks its
                // question by building a `SortGoal`, whose `bindings` are `TermId`s — and
                // a denoted binding is exactly the thing that HAS no `TermId`
                // (`unwrap_spec_view_value` says so at its own doc, and drops such
                // bindings). Wiring the leg in and reading `walk_view`'s result was tried:
                // the actual comes back a `Value::Node`, the branch never fires, and the
                // verdict does not move. Substituting a bare `Ref(ab)` instead would ask
                // about a DIFFERENT type — the carrier with its arguments dropped — and
                // could answer for a witness the value does not match. Closing it means
                // giving `SortGoal` a carrier-agnostic binding, which is its own increment
                // (WI-20260829-2NMXA). Found by /code-review.
                (Some(ev), Some(ab)) => {
                    sort_sym_compatible(kb, ab, ev) || sort_provides_admissibly(kb, ab, ev)
                }
                _ => false,
            }
        }
        // WI-342: every non-false arm of `types_compatible_term_dispatch` now has a
        // carrier-agnostic peer above; any other pair is a form mismatch, which the
        // term dispatch also rejects (`_ => false`). No re-ground bridge.
        // WI-441 exception: one ROW-shaped side ⇒ a row comparison (see the
        // term-dispatch twin).
        _ => {
            if value_is_row_shaped(kb, &a) || value_is_row_shaped(kb, &e) {
                subtype_effect_rows(kb, subst, &a, &e)
            } else {
                // WI-20260904-50B2K — A SAME-FORM PAIR HERE IS AN UNWIRED ARM, NOT A
                // MISMATCH, and the two must not look alike. The doc above claims "every
                // non-`false` arm of the term dispatch now has a peer here"; that is TRUE
                // TODAY (measured: this table is the term table plus `denoted`) and is
                // enforced by NOTHING. Add an arm to one dispatch and forget the other and
                // a real relation silently becomes `false`, wearing the same clothes as a
                // legitimate form mismatch — the two-lists-one-rule failure the typer has
                // been bitten by before.
                //
                // The predicate separates them exactly: DIFFERENT form names is the
                // mismatch this arm exists to answer, while the SAME form name on both
                // sides means this dispatch has no arm for a form both sides share, which
                // can only be an omission. A variable side reports `None` and is not a
                // form, so it stays `false` as before.
                //
                // NOT DRIVEN BY THE CORPUS, stated so it does not read as covered. It was
                // attempted: removing the `named_tuple` arm from THIS table alone (the
                // term table keeping its own) did not make the assert fire, so no pair of
                // named tuples reaches this dispatch through the `Value` carrier in the
                // suite. That is a trap for a FUTURE omission, not a tested path — and it
                // is a second finding in its own right: the arms of this table that the
                // corpus never exercises are unknown, and a census of which of them a
                // program can actually reach has not been done.
                // `poly_type` IS THE ONE SAME-FORM PAIR THAT IS NOT AN OMISSION, and the
                // first cut of this assert did not except it — `/code-review` found it.
                // [`type_dispatch_name_view`] NAMES `PolyType` precisely so that a ∀
                // reaching the structural arms is a MISMATCH no arm accepts ("what it must
                // never do if it somehow does is MATCH `arrow`"), so `false` here is the
                // decision, not a missing wire. Without the exception a debug build would
                // ABORT on the pair its own design says to refuse.
                //
                // NOT DRIVEN EITHER WAY, and that is the honest state: `check_bare_ref`
                // instantiates a ∀ at the reference — the one mint's one consumer — so no
                // program in the corpus reaches this dispatch with two of them. The
                // exception is written from the design decision 5000 lines away rather
                // than from a red row.
                // Everything stays INSIDE the macro so release builds evaluate none of
                // it — a `let` above the assert would have paid for two
                // `type_dispatch_name_view` calls on every fall-through.
                //
                // KEPT AS A `debug_assert` RATHER THAN A DIAGNOSTIC, asked again by
                // /code-review ("a user program hitting an unwired pair crashes a debug
                // build") and declined: the condition is not one a PROGRAM can create.
                // Both tables are compiled in, so they can only disagree because someone
                // edited one and not the other — the reader this fires for is the
                // DEVELOPER who did, which is what a `debug_assert` is for. A user on a
                // release build gets `false`, the safe refusal, either way. What WOULD
                // change the answer is the census this comment already says is undone: if
                // some arm turns out to be reachable only through a form pair the corpus
                // never produces, the pair stops being a developer error.
                debug_assert!(
                    !matches!(
                        (type_dispatch_name_view(kb, &a), type_dispatch_name_view(kb, &e)),
                        (Some(x), Some(y)) if x == y && x != "poly_type"
                    ),
                    "types_compatible_view_structural: no arm for the shared form {:?} \
                     — the term dispatch has a peer this one is missing; wire it rather \
                     than letting it read as a form mismatch",
                    type_dispatch_name_view(kb, &a),
                );
                false
            }
        }
    }
}

/// WI-342: the sole arrow subtyping, carrier-agnostic over [`TermView`] (both
/// the `TermId` dispatch via [`TermIdView`] and the `Value` carrier route here).
/// Contravariant param (`expected.param <: actual.param`), covariant result,
/// covariant effects via the carrier-agnostic [`subtype_effect_rows`]. A missing
/// effects field is the empty (pure) row.
pub(super) fn arrow_compatible_view<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &B,
) -> bool {
    let param_sym = kb.intern("param");
    let result_sym = kb.intern("result");
    let effects_sym = kb.intern("effects");

    // WI-791: parameter COUNT is invariant — a function of a different arity is
    // neither a subtype nor a supertype, it is uncallable in the other's place.
    // (Width subtyping over a parameter list was already refused by WI-782; this
    // is the same statement made where the count is actually recorded.)
    let Some(arity) = agreed_arrow_arity(kb, actual, expected) else {
        return false;
    };

    // Contravariant param: expected.param <: actual.param.
    match (
        named_child_value(kb, actual, param_sym),
        named_child_value(kb, expected, param_sym),
    ) {
        (Some(ap), Some(ep)) => {
            // WI-775: a PARAMETER LIST, not a data tuple — see `unify_arrow_params`.
            if !arrow_params_compatible(kb, subst, &ep, &ap, arity) {
                return false;
            }
        }
        _ => return false,
    }
    // Covariant result: actual.result <: expected.result.
    match (
        named_child_value(kb, actual, result_sym),
        named_child_value(kb, expected, result_sym),
    ) {
        (Some(ar), Some(er)) => {
            if !types_compatible(kb, subst, &ar, &er) {
                return false;
            }
        }
        _ => return false,
    }
    // Covariant effects: actual ⊆ expected (open-tail subsumption). A missing
    // side is the empty row (mirrors `arrow_compatible`).
    match (
        named_child_value(kb, actual, effects_sym),
        named_child_value(kb, expected, effects_sym),
    ) {
        (Some(ae), Some(ee)) => subtype_effect_rows(kb, subst, &ae, &ee),
        (None, None) => true,
        (Some(ae), None) => match kb.try_make_empty_effects_rows() {
            Some(er) => subtype_effect_rows(kb, subst, &ae, &TermIdView(er)),
            None => false,
        },
        (None, Some(ee)) => match kb.try_make_empty_effects_rows() {
            Some(er) => subtype_effect_rows(kb, subst, &TermIdView(er), &ee),
            None => false,
        },
    }
}

/// Per-(sort, parameter) variance, read from the declared `Covariant` /
/// `Contravariant` facts (proposal 035; `stdlib/anthill/reflect/typing.anthill`).
/// No fact ⇒ invariant (the safe default); both ⇒ bivariant. WI-293.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum Variance {
    Covariant,
    Contravariant,
    Invariant,
    Bivariant,
}

/// Look up the declared variance of `sort`'s parameter `param` from the KB
/// variance facts. Reads the facts directly via the per-functor rule index — the
/// idiom every other typer fact reader uses (`sort_provides` / `requires`), NOT
/// SLD: the `effective_*` / `check_variance` rules in the stdlib are retained-but-
/// unconsumed scaffolding for the future inference layer (WI-184), so matching the
/// fact index directly is the consistent choice. The `sort` is a registered sort so
/// it matches by canonical identity ([`same_sort_canonical`]); the `param` is written
/// bare in the fact (`param: T`) and resolved against the sort's param by short name
/// ([`same_label`]), a scoped label lookup within the already-sort-matched fact.
pub(super) fn declared_variance(kb: &KnowledgeBase, sort: Symbol, param: Symbol) -> Variance {
    let cov = matches_variance_fact(kb, "anthill.reflect.typing.Covariant", sort, param);
    let con = matches_variance_fact(kb, "anthill.reflect.typing.Contravariant", sort, param);
    match (cov, con) {
        (true, true) => Variance::Bivariant,
        (true, false) => Variance::Covariant,
        (false, true) => Variance::Contravariant,
        (false, false) => Variance::Invariant,
    }
}

/// Whether a `Covariant`/`Contravariant` fact (named by `fact_qn`) is asserted for
/// `(sort, param)`. Walks `rules_by_functor` and matches the `sort` by canonical
/// identity and the `param` by short-name label. The `entity Covariant(sort: Symbol, param: Symbol)`
/// declaration also shows up under this functor, but its arg values are the field
/// metadata type (`Symbol`), so it never matches a real `(sort, param)` lookup.
fn matches_variance_fact(kb: &KnowledgeBase, fact_qn: &str, sort: Symbol, param: Symbol) -> bool {
    let Some(functor) = kb.try_resolve_symbol(fact_qn) else {
        return false;
    };
    kb.rules_by_functor_iter(functor).any(|rid| {
        let Some(named) = kb.fact_head_named_args(rid) else {
            return false;
        };
        let sort_ok = get_named_arg(kb, &named, "sort")
            .and_then(|t| crate::kb::load::sort_ref_functor(kb, t))
            .is_some_and(|s| same_sort_canonical(kb, s, sort));
        // WI-764: the param label is compared ONLY for a fact whose sort already matched.
        // `same_label` is a within-one-sort matcher — comparing this fact's param against
        // an unrelated sort's is exactly the cross-sort misuse its `debug_assert` exists to
        // catch. Previously both sides were computed eagerly and `&&`-ed, so every variance
        // fact's param was label-compared regardless of sort; harmless while every stdlib
        // variance fact keys its param BARE, but WI-764 newly routes QUALIFIED param
        // symbols in here (a canonical `Relation.T` now reaches `declared_variance`), so
        // the short-circuit stops being cosmetic.
        sort_ok
            && get_named_arg(kb, &named, "param")
                .and_then(|t| crate::kb::load::sort_ref_functor(kb, t))
                .is_some_and(|p| same_label(kb, p, param))
    })
}

/// Check one parameterized binding by the parameter's DECLARED variance
/// (WI-293), keyed on the supertype's variance contract (`expected_base`):
/// covariant → actual <: expected (the prior unconditional check);
/// contravariant → expected <: actual (flipped); invariant (default) → both
/// directions (equal); bivariant → either. The two-direction arms run on a
/// CLONED subst and commit only on success, so a failed direction can't leave
/// partial row/var bindings in the threaded `subst` (the per-direction hygiene
/// `join_types` uses; matters for the `||` bivariant arm, where direction-2 must
/// see a clean subst). Shared by [`parameterized_compatible_view`]'s same-base
/// arm (the actual carries the param) and its cross-sort provider arm (WI-387
/// FIX 2: the actual-side value comes from the actual's provider fact).
fn check_binding_by_variance<A: TermView, E: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    expected_base: Symbol,
    param: Symbol,
    av: &A,
    ev: &E,
) -> bool {
    match declared_variance(kb, expected_base, param) {
        Variance::Covariant => types_compatible(kb, subst, av, ev),
        Variance::Contravariant => types_compatible(kb, subst, ev, av),
        Variance::Invariant => {
            let mut probe = subst.clone();
            if types_compatible(kb, &mut probe, av, ev) && types_compatible(kb, &mut probe, ev, av)
            {
                *subst = probe;
                true
            } else {
                false
            }
        }
        Variance::Bivariant => {
            let mut probe = subst.clone();
            if types_compatible(kb, &mut probe, av, ev) {
                *subst = probe;
                true
            } else {
                types_compatible(kb, subst, ev, av)
            }
        }
    }
}

/// WI-342: the sole `parameterized` subtyping, carrier-agnostic over [`TermView`]
/// (both the `TermId` dispatch via [`TermIdView`] and the `Value` carrier route
/// here). Base compatible, then every EXPECTED binding must have a matching (by
/// param name) actual binding whose value is compatible — by the parameter's
/// DECLARED variance (WI-293), not unconditionally covariantly.
///
/// Bindings are read via [`extract_type`], which skips a *malformed* binding (one
/// whose value is missing). The deleted `TermId`-specific `parameterized_compatible`
/// instead `return false`d on such a binding — so this consolidation is marginally
/// more permissive on a corrupt EXPECTED type. Unreachable in practice
/// (`make_parameterized_type` always builds complete bindings), and it brings the
/// subtype direction into line with unify, which has always *skipped* malformed
/// bindings — removing a prior asymmetry rather than introducing one.
pub(super) fn parameterized_compatible_view<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &B,
) -> bool {
    // WI-361: base + bindings form-agnostic via `extract_type` (see
    // `unify_parameterized_view`); the base subtype check recurses the full
    // `types_compatible` on `Ref(S)` (preserving provider admissibility), not a
    // sort-symbol shortcut.
    let (actual_base, actual_bindings) = match extract_type(kb, actual) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return false,
    };
    let (expected_base, expected_bindings) = match extract_type(kb, expected) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return false,
    };
    let actual_base_ty = kb.alloc(Term::Ref(actual_base));
    let expected_base_ty = kb.alloc(Term::Ref(expected_base));
    if !types_compatible(
        kb,
        subst,
        &TermIdView(actual_base_ty),
        &TermIdView(expected_base_ty),
    ) {
        return false;
    }

    // WI-1088: `Function`/`Function`, where BOTH readings of `A` are still open and the
    // relation owed is their INTERSECTION — order-preserving. The per-binding loop below
    // relates the two `A`s with the ordinary `types_compatible`, which is the whole-`A`
    // (data) reading and order-free since WI-803; the spread reading also has an opinion
    // and it is the one a value's already-pinned mapping obeys. See
    // [`function_pairing_permutes_a`] for the two programs that measured it.
    //
    // HERE, and not at [`arrow_function_compatible`]: that function is reached only from
    // the `(arrow, parameterized)` dispatch arms, so it never sees two `Function`s. This
    // is the ONE site both carrier routes decompose a `Function`-vs-`Function` pairing at
    // (`types_compatible_term_dispatch` and `types_compatible_view_structural` both land
    // here), so the guard is stated once.
    //
    // Through [`function_spec_parts`], the WI-802 owner, on the base + bindings already in
    // hand — so a `Function` is recognized the one way the rest of the file recognizes it
    // and no binding is re-extracted. The EXPECTED side is asked first: it is one
    // `qualified_name_of` compare, and a non-`Function` slot (every other parameterized
    // comparison in the corpus) stops there.
    // The two `A`s are CLONED out of the borrows before the call: `function_spec_parts`
    // borrows `bindings`, the predicate needs `&mut kb` to σ-resolve them, and a binding is
    // an `Rc`-carried `Value`, so the clone is a refcount bump rather than a deep copy.
    let permuting_as = function_spec_parts(kb, expected_base, &expected_bindings)
        .and_then(|(d_a, _, _)| Some(d_a?.clone()))
        .zip(
            function_spec_parts(kb, actual_base, &actual_bindings)
                .and_then(|(a_a, _, _)| Some(a_a?.clone())),
        );
    if let Some((d_a, a_a)) = permuting_as {
        // Neither side is an `arrow` — both are parameterized types this arm decoded —
        // so the arities the predicate gates on are `None` by construction.
        if function_pairing_permutes_a(kb, subst, None, None, &d_a, &a_a) {
            return false;
        }
    }

    // WI-764: how to compare the two sides' binding KEYS — see [`binding_for_param`].
    let key_match = BindingKeyMatch::for_bases(kb, actual_base, expected_base);
    // WI-387 FIX 2: the actual's cross-sort provider view (`List` provides
    // `Stream`) — loop-invariant (`actual_base`/`expected_base` are fixed for the
    // whole check), so resolve it ONCE rather than per missing expected param
    // (mirrors FIX 3's hoist of `provider_bindings`; `provider_spec_view_bindings`
    // is a full scan of every `SortProvidesInfo` fact). `None` for a same-base
    // check (no cross-sort translation) or a non-provider actual. Deliberately still
    // keyed on RAW base inequality, not on `key_match`: the two ask different questions
    // (is a cross-SORT translation needed, vs how to spell one sort's param keys), and
    // widening this one to `same_sort_canonical` would be an untestable behavior change
    // — it could only ever differ for two interned copies of ONE sort, where the key
    // match below already resolves the bindings directly.
    //
    // WI-20260829-GNPG7 — TRANSITIVE, because the one-hop reader made this relation
    // disagree with `sort_provides` about the same question. `sort_provides` (which the
    // BARE-spec arms reach through `sort_provides_admissibly`) walks the whole provision
    // chain; `provider_spec_view_bindings` reads a single DIRECT `SortProvidesInfo` fact.
    // So `ti(c: Iterable)` accepted a `List[T = Row]` and `ti(c: Iterable[Element = Row])`
    // refused the same argument — not because the parameter carried bindings, which is
    // what the ticket read off its own table, but because `List` reaches `Iterable` in TWO
    // hops (`List provides Stream`, `Stream provides Iterable`) and never declares it
    // directly. MEASURED with the spec held fixed and only the hop count varied:
    // `MutableStack`, which declares `provides Iterable[C = MutableStack[T], …]` ITSELF,
    // was accepted at `Iterable[C = MutableStack[T = Row], Element = Row, E = {}]` — the
    // fully-bound spec view naming its own carrier — while `List` was refused at the same
    // shape. A bindings-carrying spec view is therefore not a distinct "view" the language
    // refuses; it is admitted whenever the provision is direct.
    let cross_sort_provider = if actual_base != expected_base {
        subtype_provider_view(kb, actual_base, expected_base)
    } else {
        None
    };
    // WI-20260829-XZMGC — THE SPEC'S CARRIER PARAMETER, when the view above was COMPOSED
    // through a provision chain and therefore does not carry one. `C` is the value
    // `Iterable.iterator(c: C)` receives, and on a `List` that is THE LIST — so it is
    // checked against `actual` itself, which is the strongest reading available here and
    // the one the DIRECT case already gets (a direct `provides Iterable[C = MutableStack[T],
    // …]` names its own carrier, and the WI-441 instantiation below grounds its `T` off
    // this instance). MEASURED, and it is why the carrier param is not simply given the
    // bare `Ref(actual_base)` inside `subtype_provider_view`: `MutableStack[T = Row]` is
    // REFUSED at `Iterable[C = MutableStack[T = Bool]]`, and the bare form would have
    // ACCEPTED the two-hop twin `Iterable[C = List[T = Bool]]` for a `List[T = Row]`.
    //
    // `None` for a direct view, for a same-base check, and for a spec with no identifiable
    // carrier parameter — in each of those the view's own binding stands.
    let carrier_param_is_ours = match &cross_sort_provider {
        Some((_, true)) => spec_carrier_param(kb, expected_base)
            .and_then(|p| type_param_vid_in_sort(kb, expected_base, p)),
        _ => None,
    };
    let cross_sort_provider = cross_sort_provider.map(|(view, _)| view);
    // WI-441: the provider view's binding values carry the CARRIER's canonical
    // param vars (`provides Stream[T = T, E = {ES, EF}]` holds MappedStream's
    // own ES/EF alias vars). Instantiate them through THIS actual instance's
    // bindings (ES := the instance's ES value, …), so the per-param comparison
    // below sees the instance's row, not the canon vars (a two-row provision
    // `{ES, EF}` cannot pair against the expected row's tails without it —
    // two-tail-to-two-tail pairing is ambiguous).
    //
    // WI-20260829-9NJTX — THE INSTANTIATION IS A REWRITE OF THE VIEW, NOT A FACT ABOUT THE
    // CALLER'S WORLD, and it is applied here rather than published into `subst`. It used
    // to `subst.bind_value` each canon var and let the comparison below resolve through
    // it. Those binds outlive the comparison, and the var they name is the SORT's — one
    // `List.T` shared by every `List` instance and every comparison in that substitution —
    // so the FIRST instance compared won for all the rest. DRIVEN, both directions, by
    // [`wi_9njtx_provider_instantiation_rollback_test`]:
    //
    //   * after a FAILED comparison (`List[T = Row]` at `Iterable[Element = Bool]`) the
    //     binding stayed and the NEXT argument, `List[T = Int64]` at
    //     `Iterable[Element = Int64]`, was refused against `Row` — a spurious second error
    //     on a program with one mistake in it.
    //   * after a SUCCEEDING one (`List[T = Row]` at `Iterable[Element = Row]`) it stayed
    //     just the same, and refused the same well-typed second argument — a correct
    //     program rejected. This is why the rollback-on-failure the ticket asked for is
    //     NOT the repair: it leaves this row wrong. Measured — see the test's header.
    //
    // A scratch child of `subst` carries the binds instead. `with_parent` is what makes it
    // a REWRITE: `bind_value` consults only the child's own map, so this instance's value
    // SHADOWS anything the parent chain already says about the canon var, where the old
    // `resolve_as_value(..).is_none()` guard deferred to it. The values are walked through
    // that child once, up front, and the loop below compares the walked values on the
    // caller's own `subst`, which the instantiation never touches.
    //
    // THE SHADOWING IS NOT A CORNER CASE and is worth the number: over `wi_tests` the canon
    // var is ALREADY bound in the caller's chain on 46,107 of these iterations, and on
    // 40,984 of those the inherited value DIFFERS from this instance's — chiefly
    // `MappedStream` / `FilteredStream`, whose params other typer paths ground. Every one
    // is a comparison that used to be decided against a foreign instance's value. The
    // corpus is green either way, so the suite is not what justifies the direction; the
    // instance being compared owning the meaning of its own parameter is.
    //
    // WHAT THE SHADOWING DOES NOT COVER: the three `continue`s below. A param whose
    // qualified name does not resolve, whose alias is not a `SortAlias`, or whose alias
    // target is not a `Var::Global` (a slot pinned concrete at declaration —
    // [`sort_type_params_as_pairs`] filters for exactly the ones that are vars) binds
    // nothing here, so it still resolves through the parent chain, which is the
    // pre-WI-9NJTX reading for that param. They were inert while this loop only wrote into
    // `subst`; they are load-bearing now. MEASURED across the whole workspace: ZERO
    // firings, so nothing the corpus reaches falls through them — which is also why there
    // is no `debug_assert` here. An assertion nothing can drive is not a guard, and the
    // honest form of "unmeasured" is this sentence. Found by /code-review.
    let cross_sort_provider = match cross_sort_provider {
        None => None,
        Some(view) => {
            let mut instance = Substitution::with_parent(subst.clone());
            for (ap, av) in &actual_bindings {
                let q = format!(
                    "{}.{}",
                    kb.qualified_name_of(actual_base),
                    kb.local_name_of(*ap)
                );
                let Some(qsym) = kb.try_resolve_symbol(&q) else {
                    continue;
                };
                let Some(target) = resolve_sort_alias(kb, qsym) else {
                    continue;
                };
                let Term::Var(Var::Global(vid)) = kb.get_term(target) else {
                    continue;
                };
                let vid = *vid;
                instance.bind_value(kb, vid, av.clone());
            }
            let mut instantiated: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
            for (p, v) in view {
                // Deep, and then surfaced, for the reason WI-394 records at the arm that
                // used to do this walk lazily: a `Value::Node` binding resolves to a bare
                // var under `walk_type_deep` alone.
                let walked = walk_type_deep(kb, &instance, v);
                instantiated.push((p, surface_node_binding_to_term(kb, &instance, walked)));
            }
            Some(instantiated)
        }
    };
    for (param, ev) in &expected_bindings {
        // The actual-side value to check against the expected binding `ev`:
        // normally the actual's OWN binding for `param`. WI-387 FIX 2: when the
        // actual lacks it AND the actual is a CROSS-SORT provider of the expected
        // (`List` lacks `Stream.E` but provides `Stream`), fall back to the value
        // the actual's provider fact supplies for that param (matched by short
        // name) — so `List[Elem]` conforms to `Stream[T = Elem, E = {}]` via
        // `provides Stream[E = {}]`. The actual was never translated through its
        // provider into the expected sort's param space before, so the missing
        // expected param rejected unconditionally. A param absent on BOTH sides,
        // or a SAME-base actual genuinely missing the param (`cross_sort_provider`
        // is `None`), still rejects: this LOOSENS the cross-sort case only and
        // cannot newly-reject existing code.
        //
        // WI-1056 — THE SAME-BASE MISSING PARAM is taken by the arm below, and the case
        // for it is not the spec sentence but a MEASUREMENT of the language as it stands.
        // ONE type, FOUR spellings, and only the partial one was refused:
        //
        //     operation feed[U](b: Box[T = Int64, U = U]) -> …   LOADS
        //     operation feed(b: Box)                     -> …   LOADS
        //     operation feed(b: Box[T = Int64, U = ?])   -> …   LOADS
        //     operation feed(b: Box[T = Int64])          -> …   REFUSED   ← the outlier
        //
        // against `takes_full(b: Box[T = Int64, U = Bool])`, and identically for an
        // EFFECT ROW (`Stream[T = Int64]` vs `Stream[T = Int64, E = {}]`). Writing the
        // wildcard out — `U = ?` — is the same type as omitting it, and it already
        // conformed; so did the bare form and the explicit operation type parameter. The
        // arm below makes the fourth spelling agree with the other three.
        //
        // A FIRST CUT REVERTED THIS ON A FALSE CONTROL, and the mistake is worth keeping
        // because it is easy to repeat: the effect-row program above was observed to flip
        // from REFUSED to accepted when the arm landed, and read as a regression it
        // introduced. It is not — the identical acceptance is reachable on main by writing
        // `E = ?` or the bare `Stream`. The control measured "did this arm change THIS
        // program's verdict" and never asked "was that verdict already obtainable by
        // spelling the same type differently".
        //
        // WHETHER THE PERMISSIVE READING IS RIGHT AT ALL is a real and separate question —
        // an unwritten row means "unknown effects", which arguably must not satisfy "no
        // effects" — but it is pre-existing and belongs to all four spellings, not to this
        // one. **WI-1059** owns it, and the cost of the restrictive answer is measured
        // there (33 stdlib load errors, and only after patching BOTH carrier arms —
        // WI-1016).
        // WI-20260829-XZMGC — the composed view's missing carrier param, checked against
        // the ACTUAL itself. Placed ABOVE the `binding_for_param` lookup and not inside the
        // `None` arm: the actual is a foreign sort here (this is the cross-sort branch), and
        // a parameter of its own that happens to share the spec carrier's SHORT NAME would
        // otherwise answer for it — the key match is by short name across two sorts, so that
        // collision is a spelling coincidence, not a binding.
        if let Some(cvid) = carrier_param_is_ours {
            if type_param_vid_in_sort(kb, expected_base, *param) == Some(cvid) {
                if !check_binding_by_variance(kb, subst, expected_base, *param, actual, ev) {
                    return false;
                }
                continue;
            }
        }
        // WI-764: keyed via [`binding_for_param`] — raw identity here rejected a WRITTEN
        // `Relation[T = .., E = ..]` annotation against the very relation it describes.
        let ok = match binding_for_param(kb, &actual_bindings, *param, key_match) {
            Some(av) => check_binding_by_variance(kb, subst, expected_base, *param, av, ev),
            None => {
                let short = short_name_of(kb.local_name_of(*param));
                let pv = cross_sort_provider.as_ref().and_then(|view| {
                    view.iter()
                        .find(|(p, _)| short_name_of(kb.local_name_of(*p)) == short)
                        .map(|(_, v)| *v)
                });
                match pv {
                    // WI-1056 — the SAME-BASE partial application (see the note above the
                    // loop for the four-spelling measurement that decides it).
                    //
                    // GATED ON THE ACTUAL'S OWN DECLARED PARAMETERS, so this admits a
                    // partial application and NOT a type missing something its base never
                    // had: a `param` the actual's base does not declare is a malformed
                    // expected type (or a cross-sort key the arm below owns), and it still
                    // rejects. `sort_type_params_as_pairs` is exactly "the parameters an
                    // unwritten slot would expand to a fresh var for" — it already filters
                    // to the slots whose alias target is a `Var`, i.e. the ones with
                    // nothing else to fill them.
                    _ if actual_base == expected_base
                        && binding_for_param(
                            kb,
                            &sort_type_params_as_pairs(kb, actual_base),
                            *param,
                            key_match,
                        )
                        .is_some() =>
                    {
                        true
                    }
                    Some(pv) => {
                        // WI-461: the provider value carries the carrier's canonical param
                        // refs (`provides Stream[T, {}]` holds List's `T`), so a concrete /
                        // NEUTRAL expected (`l.T`) must compare against the instance's
                        // value and not the raw canon ref. That resolution is no longer
                        // done here: WI-20260829-9NJTX moved it to the view itself, so `pv`
                        // ARRIVES instantiated and deep-walked and this leg is the precise
                        // one it already was in effect — the walk used to happen implicitly
                        // through the canon binds the instantiation left in `subst`.
                        //
                        // THE SECOND LEG NOW FIRES ZERO TIMES, and that is the change
                        // working rather than a branch to delete. MEASURED, both trees,
                        // by logging `pvr != pv` at this site: before, it was reached
                        // 10,313 times over `wi_tests` and resolved further on 59 of them,
                        // ACCEPTING 39 bindings the first leg had rejected — because the
                        // first leg was handed the raw canon ref and only ever walked it
                        // shallowly. After, 13,149 reaches and `pvr != pv` is false on
                        // every one: those 39 are now decided by the first leg, off the
                        // value the view arrives already carrying.
                        //
                        // It is kept because the case it covers is not empty, only
                        // unreached: the view is walked against a snapshot of `subst` taken
                        // before this loop, and `subst` gains bindings DURING it (an
                        // earlier param's comparison binds a var a later `pv` mentions).
                        // Gated on `pvr != pv`, so it can only ever ACCEPT what the first
                        // leg did not — never reject.
                        let mut probe = subst.clone();
                        if check_binding_by_variance(
                            kb,
                            &mut probe,
                            expected_base,
                            *param,
                            &TermIdView(pv),
                            ev,
                        ) {
                            *subst = probe;
                            true
                        } else {
                            let pvr = walk_type_deep(kb, subst, pv);
                            // WI-394: surface a non-`Term` (`Value::Node`)
                            // binding so the "did it resolve further?" probe
                            // (`pvr != pv`) sees the resolved carrier instead
                            // of the bare var (which equals `pv` and would
                            // spuriously fail the binding).
                            let pvr = surface_node_binding_to_term(kb, subst, pvr);
                            // PROBE-AND-COMMIT, like the leg above and for the reason this
                            // whole ticket is about: `check_binding_by_variance`'s
                            // Covariant / Contravariant arms hand `subst` straight to
                            // `types_compatible`, so a leg that binds a row tail and THEN
                            // returns false used to leave that binding behind — the one
                            // write on this arm still able to do so, in the function whose
                            // contract is now that a failed comparison leaves nothing.
                            // Latent, not observed: this leg is measured firing zero times
                            // (see above), so the clone is on a path the corpus never
                            // takes and no test moves either way. It is here so the arm's
                            // two legs answer the same way, rather than because anything
                            // failed without it. Found by /code-review.
                            if pvr != pv {
                                let mut probe = subst.clone();
                                if check_binding_by_variance(
                                    kb,
                                    &mut probe,
                                    expected_base,
                                    *param,
                                    &TermIdView(pvr),
                                    ev,
                                ) {
                                    *subst = probe;
                                    true
                                } else {
                                    false
                                }
                            } else {
                                false
                            }
                        }
                    }
                    None => false,
                }
            }
        };
        if !ok {
            return false;
        }
    }
    true
}

/// Compatibility between the typer's `arrow(param, result, effects)` and the
/// stdlib `Function[A, B, E]` (in either order) — they denote the same callable
/// type. Carrier-agnostic over [`TermView`] (WI-361/WI-342): routed here from
/// BOTH the `TermId` dispatch ([`types_compatible_term_dispatch`], via
/// [`TermIdView`]) AND the `Value`-carrier dispatch
/// ([`types_compatible_view_structural`]), so a `Value::Node` callback arrow
/// checks against a `Function[A, B, E]` directly — natively, with no re-grounding
/// bridge. Decomposes both via [`arrow_parts`] (which yields
/// `None` for a non-`Function` parameterized type, so `arrow` vs `List[T]` stays
/// incompatible), checks contravariant param + covariant result, and (WI-332)
/// covariant effects via the carrier-agnostic [`subtype_effect_rows`]. WI-289.
pub(super) fn arrow_function_compatible<A: TermView, E: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &E,
) -> bool {
    let (a_param, a_result, a_eff) = match arrow_parts(kb, actual) {
        Some(parts) => parts,
        None => return false,
    };
    let (b_param, b_result, b_eff) = match arrow_parts(kb, expected) {
        Some(parts) => parts,
        None => return false,
    };

    // WI-791: no arity EQUALITY check on this arm, and that is a decision rather
    // than an omission. A `Function[A, B, E]` states no arity and cannot: its `A`
    // is the ONE argument `apply(f, x: A)` passes, so `Function[(T, T), Bool]` has
    // denoted both the single-tuple-argument reading and the eta arrow of a
    // 2-parameter op since WI-775. Demanding arity 1 of the arrow side would break
    // the latter; demanding a match would need a count `Function` does not have.
    // What DOES hold here is the by-name param comparison below, which is what
    // WI-775 installed to keep `(acc, x)` from bridging to `(_1, _2)`.
    //
    // WI-801: what ALSO holds is that the two readings above are the ONLY two.
    // Stating no arity bounds the check to a SET rather than an equality; it does
    // not remove it. The param comparison below cannot stand in for that, because
    // an unannotated lambda adopts `A` as its param type and so passes it
    // regardless of how many binders it wrote.
    //
    // This is the GROUND path's decider (the non-ground path's is
    // `validate_arrow_param_result`). It only decides — being inside
    // `types_compatible`, it returns `bool` and the two types are not in scope
    // where a message would be built; [`conformance_error`] renders the verdict
    // at the sites that do have them. `b_param` IS the `A` the check needs, so it
    // is handed over rather than re-extracted: this runs per comparison,
    // including every one that succeeds.
    let arity_key = kb.intern("arity");
    if let (Some(a_arity), Some(bp)) = (arrow_arity(kb, actual, arity_key), b_param.clone()) {
        if arrow_arity(kb, expected, arity_key).is_none()
            && function_slot_arity_counts_for(kb, &bp, a_arity).is_some()
        {
            return false;
        }
    }
    // Param is contravariant (expected param <: actual param), result
    // covariant — matching `arrow_compatible`. A missing param on either side
    // (a bare `Function` without an `A` binding, polymorphic) is unconstrained.
    let params_ok = match (&a_param, &b_param) {
        // WI-775: BY NAME at the WHOLE-`A` reading — a `Function[A = …]`'s `A` is the
        // argument's DATA type (it is what flows to `apply(f, x: A)`), so bridging
        // `(acc, x)` to `(_1, _2)` THERE is the unsoundness that ticket closed:
        // measured on the pre-WI-775 tree, `apply2(add2)` with `f: Function[A = (acc:
        // Int64, x: Int64), B = Int64]` loaded clean and trapped at eval with
        // `ArityMismatch { expected: 2, got: 1 }`.
        //
        // WI-1087: AND POSITIONALLY AT THE SPREAD READING, which is the OTHER of the two
        // call counts WI-801 admits at this slot and which the by-name rule was silently
        // refusing outright — see [`function_slot_reads_a_as_param_list`] for the
        // conflict and its measurement. The WI-775 trap above is not reachable through
        // this arm: it was an `ArityMismatch` at eval, and WI-784/WI-787 have since
        // taught the runtime to spread a tuple — name-keyed included — across a
        // multi-parameter operation. The arity SET is still enforced, one block up.
        //
        // ONE DIRECTION ONLY — the `Function` must be the EXPECTED slot and the arrow the
        // ACTUAL value. This function is routed here from both dispatch orders, so the
        // mirror (a `Function`-typed ARGUMENT at an `arrow` slot) reaches it too, and it must
        // NOT take this relation: an arrow slot states a hard arity and applies its value
        // with exactly that many arguments, while a `Function`-typed value states no arity
        // and may be either reading, so matching the slot's `n` against `|A|` proves nothing
        // about the callable inside. See `validate_arrow_param_result`'s `None` arm for the
        // program that measured it — load-clean, `ArityMismatch` at eval.
        (Some(ap), Some(bp)) => match (
            arrow_arity(kb, actual, arity_key),
            arrow_arity(kb, expected, arity_key),
        ) {
            (Some(n), None) if function_slot_reads_a_as_param_list(kb, bp, n) => {
                arrow_params_compatible(kb, subst, bp, ap, n)
            }
            // NO `Function`/`Function` ARM HERE, and WI-1088 measured why rather than
            // leaving it to be re-derived: this function is reached only from the
            // `(arrow, parameterized)` dispatch arms, so one side is always an `arrow`
            // and an arrow always carries an `arity` child. The pairing WI-1088 refuses
            // decomposes through [`parameterized_compatible_view`] instead, which is
            // where its guard lives.
            _ => types_compatible(kb, subst, bp, ap),
        },
        _ => true,
    };
    if !params_ok {
        return false;
    }
    if !types_compatible(kb, subst, &a_result, &b_result) {
        return false;
    }

    // WI-332: covariant effects via [`subtype_effect_rows`], consistent with
    // `arrow_compatible`. **Missing E** is treated symmetrically with missing A:
    // omitting the binding means *polymorphic* (accept any), NOT *empty* — so
    // `Function[A, B]` (no E) accepts an effectful actual, while the explicit
    // `Function[A=…, B=…, E={}]` form keeps the closed-empty semantic and rejects
    // effectful actuals (regression-tested). The arrow side always synthesizes an
    // `effects` field, so its `None` arm is defensive only.
    //
    // WI-335: the threaded subst is shared across the param/result/effects
    // sub-checks so a row var bound in one position is visible in the others.
    match (a_eff, b_eff) {
        // Either side polymorphic in E → accept.
        (None, _) | (_, None) => true,
        (Some(ae), Some(ee)) => {
            // Normalize a legacy `List[Type]` E binding to a canonical row; an
            // already-canonical row (or a `Value::Node` row) passes through.
            let ae = canonical_effects_row(kb, &ae);
            let ee = canonical_effects_row(kb, &ee);
            subtype_effect_rows(kb, subst, &ae, &ee)
        }
    }
}

/// The `base` sort_ref of a `parameterized(base, bindings)` type term.
/// The base sort symbol of a parameterized type, form-agnostic (WI-361): the
/// deep `parameterized(base: sort_ref(S), …)` base field or the term-backed
/// `Fn{S, …}` functor, via [`type_head`]. `None` if not a parameterized type.
fn parameterized_base_sym(kb: &KnowledgeBase, ty: TermId) -> Option<Symbol> {
    match type_head(kb, &TermIdView(ty)) {
        TypeHead::Parameterized { base, .. } => Some(base),
        _ => None,
    }
}

/// Strict subtype check: actual is a proper subtype of expected.
/// `is_subtype(A, A)` is false. `is_subtype(red, Color)` is true.
///
/// WI-326: takes `&mut KnowledgeBase` (transitively, via
/// [`types_compatible`] → [`arrow_compatible_view`] → row subtyping).
///
/// WI-335: does NOT take a `&mut Substitution` argument. Unlike
/// [`types_compatible`], `is_subtype` is a context-free lattice
/// question — "is sub strictly less than sup?" — that should not depend
/// on any caller's bindings. We allocate a fresh substitution internally
/// so the answer is purely a function of `(kb, sub, sup)`. Callers that
/// want row-binding propagation should use [`types_compatible`] directly.
pub fn is_subtype(kb: &mut KnowledgeBase, sub: TermId, sup: TermId) -> bool {
    if sub == sup {
        return false;
    }
    let mut subst = Substitution::new();
    types_compatible(kb, &mut subst, &TermIdView(sub), &TermIdView(sup))
}

/// WI-287: one step up the entity→enclosing-sort chain. `Some(parent
/// sort as a type)` when `t` is a `sort_ref` to an entity nested in a
/// sort; `None` for a top-level sort (no enclosing parent) or a
/// non-`sort_ref` type. Lets [`join_types`] find a common supertype of
/// two distinct entity-typed branches even when leaves weren't already
/// widened to their sort.
fn widen_to_parent_sort(kb: &mut KnowledgeBase, t: TermId) -> Option<TermId> {
    let sym = extract_sort_ref_sym(kb, &TermIdView(t))?;
    let parent = kb.strict_parent_sort(sym)?;
    Some(kb.make_sort_ref(parent))
}

/// WI-342: carrier-agnostic widen for [`join_types`]. Only a nominal sort widens
/// up the entity→sort lattice; a `Value::Node` (an arrow / denoted-bearing type)
/// has no parent sort, so two incomparable Node arrows correctly fail to join.
fn widen_value(kb: &mut KnowledgeBase, v: &Value) -> Option<Value> {
    match v {
        Value::Term { id: t, .. } => widen_to_parent_sort(kb, *t).map(Value::term),
        _ => None,
    }
}

/// WI-287: a common supertype (an upper bound) of two branch types in the
/// (top-less) Type lattice, or `None` when they have none. NOT necessarily
/// the strict least upper bound: a polymorphic `none()`/`nil()` typed bare
/// `Option`/`List` could in principle specialize to the sibling branch's
/// `Option[T=Int]` (making the strict lub `Option[T=Int]`), but the typer
/// neither tracks that a bare type is the polymorphic kind nor unifies it
/// here, so for the bare-vs-parameterized case this returns the more-
/// general type instead (see [`more_general_type`]) — a sound upper bound,
/// not the lub. Commutative: `join_types(a, b) == join_types(b, a)`, so
/// folding branches is order-independent. A wildcard (`type_var`) branch
/// imposes no constraint, so the other branch's type is the result. When
/// exactly one type conforms to the other (`types_compatible`, covering
/// entity→sort and `requires`-refine) the supertype wins; when both
/// directions hold (identical, or bare-vs-parameterized) [`more_general_type`]
/// decides; failing both, two SAME-BASE parameterized types get a real
/// parameterized LUB built per-binding by declared variance (WI-464,
/// [`join_parameterized_same_base`]), and otherwise the nominal sides are widened
/// one level up the entity→enclosing-sort chain and retried. The climb is bounded
/// — each step strictly ascends or a side stops widening — so it terminates.
pub(super) fn join_types(kb: &mut KnowledgeBase, a: Value, b: Value) -> Option<Value> {
    // WI-342: carrier-agnostic — `a`/`b` are `Value`s (a branch may be a
    // `Value::Node` lambda arrow). WI-464: the join RETURNS one of its inputs, or
    // (for two same-base parameterized types) CONSTRUCTS the parameterized LUB
    // recursively, or widens a nominal side up the lattice. `types_compatible` is
    // already carrier-agnostic; we pass the `Value`s directly rather than re-grounding.
    // WI-361: dispatch on the CANONICAL type tag (`type_dispatch_name_view`), not
    // the raw functor — a term-backed type_var is `Fn{TypeExtractor.TypeVar, …}`
    // whose raw functor name is "TypeVar", so a raw `== "type_var"` check would
    // miss the inference wildcard and force the full lattice climb (spurious clash).
    // WI-20260829-WBXGX — AN APPLICATION OF HASH-CONSING, and the cheapest arm here.
    // `join(a, a) = a`, which the loop below reaches only after `types_compatible` in BOTH
    // directions (two `Substitution` allocations and a lattice walk) and then
    // `more_general_type`. `TermId` equality answers it in ONE comparison, and is sound
    // precisely because the store is hash-consed by structure — CLAUDE.md's representation
    // note names O(1) structural equality as exactly what that buys.
    //
    // IT IS HERE RATHER THAN AT A CALL SITE so every caller gets it: the branch join over
    // `if`/`match` arms asks this of homogeneous arms as often as a collection literal asks
    // it of homogeneous elements.
    //
    // MEASURED over the whole `wi_tests` corpus — 449,660 calls, bucketed by carrier:
    //
    //     both interned, EQUAL      397,064   88.3%   this arm, one integer compare
    //     both interned, different   52,596   11.7%   the walk below
    //     either not interned             0    0.0%
    //
    // So the fast path is the DOMINANT one, and the last row answers a question that was
    // asked and is worth recording as settled: a computed hash on `Value` would generalize
    // this arm past the interned carrier, and there is nothing here for it to serve — a
    // `Value::Node` (an arrow, a denoted type — deliberately not interned) never reaches
    // `join_types` at all. If a producer ever routes one here, this comment is the place
    // that says the fast path silently stops covering it.
    //
    // IT HAS NO TEST ROW AND SHOULD NOT: backing it out fails NOTHING (lib 600/0, `wi_tests`
    // 4253/0), which is the correct outcome for a performance change and is itself the
    // correctness evidence — the one-integer answer is the answer the walk below gives, so a
    // red row would mean it had changed behaviour.
    if let (Value::Term { id: x }, Value::Term { id: y }) = (&a, &b) {
        if x == y {
            return Some(a);
        }
    }
    if type_dispatch_name_view(kb, &a) == Some("type_var") {
        return Some(b);
    }
    if type_dispatch_name_view(kb, &b) == Some("type_var") {
        return Some(a);
    }
    let (mut a, mut b) = (a, b);
    // Bound defensively against any pathological parent cycle; real
    // entity→sort chains are a single level.
    for _ in 0..64 {
        // WI-335: each direction of the lattice check is an independent
        // question — allocate per-direction substs so a binding made
        // checking `a <: b` doesn't influence the `b <: a` check.
        let mut subst_ab = Substitution::new();
        let mut subst_ba = Substitution::new();
        match (
            types_compatible(kb, &mut subst_ab, &a, &b),
            types_compatible(kb, &mut subst_ba, &b, &a),
        ) {
            // `a <: b` only: `b` is the supertype.
            (true, false) => return Some(b),
            // `b <: a` only: `a` is the supertype.
            (false, true) => return Some(a),
            // Mutually compatible: identical types, or the bare-vs-
            // parameterized normalization where both directions hold
            // (`Option` vs `Option[T=Int]`). We return the less-
            // constrained side — a sound upper bound, deliberately more
            // general than the strict lub (which would keep the bindings)
            // — picked deterministically so the result is order-
            // independent. (Different parameterizations like
            // `List[Int]`/`List[String]` are NOT mutually compatible — the
            // parameterized arm checks bindings — so they fall through to
            // the widen step.)
            (true, true) => return Some(more_general_type(kb, &a, &b)),
            // Incomparable. WI-464: two same-base parameterized types
            // (`Option[T=Cat]` / `Option[T=Dog]`) get a real parameterized LUB —
            // recurse per binding by the parameter's DECLARED variance (covariant
            // `join(av,bv)`, contravariant `meet(av,bv)`, invariant `av≡bv`),
            // yielding `Option[T=Animal]`. When a binding can't be combined (no
            // common supertype, or unequal invariant bindings) the helper falls
            // back to the bare base sort — still a sound common supertype. (The
            // earlier WI-382 deferral was wrong: `meet_types` is just `join_types`'s
            // dual over the same lattice, built directly in Rust like the WI-293
            // subtyping half — no per-sort-algorithm framework needed.)
            (false, false) => {
                match join_parameterized_same_base(kb, &a, &b) {
                    SameBaseCombine::Combined(lub) => return Some(lub),
                    // WI-20260829-WBXGX: same base, and a binding has no combination —
                    // `Option[T = Int64]` vs `Option[T = String]` on an invariant `T`. The
                    // search is OVER: there is no upper bound of the two that is not also
                    // BELOW both of them (see [`SameBaseCombine::NoCombination`]), and
                    // widening cannot help — `widen_value` climbs a bare `sort_ref` and
                    // these are applications. Returning the bare base here is what let a
                    // `String` reach an `Int64` slot.
                    SameBaseCombine::NoCombination => return None,
                    SameBaseCombine::NotApplicable => {}
                }
                // Not same-base parameterized: widen the entity side(s) one level
                // (entity → enclosing sort) up the nominal lattice and retry.
                let wa = widen_value(kb, &a);
                let wb = widen_value(kb, &b);
                if wa.is_none() && wb.is_none() {
                    return None;
                }
                if let Some(x) = wa {
                    a = x;
                }
                if let Some(y) = wb {
                    b = y;
                }
            }
        }
    }
    None
}

/// WI-287: between two *mutually*-`types_compatible` types, the upper
/// bound to keep. This arm is reached only when `types_compatible` holds
/// in BOTH directions, which (apart from identical types) means the
/// bare-vs-parameterized normalization: `Option` and `Option[T=Int]` each
/// conform to the other (a bare sort is "compatible with any instantiation
/// and vice versa"). The *strict* lub here is the parameterized side
/// (`Option[T=Int]`): a polymorphic `none()` specializes to it. But the
/// typer can't tell a polymorphic bare (`none()`/`nil()`, safe to
/// specialize) from a declared `-> Option` carrying some other unknown `T`
/// (where claiming `Int` would be wrong), so we deliberately return the
/// bare (more-general) side — a sound upper bound that never over-claims a
/// binding, at the cost of dropping the strict lub's precision. A
/// return/annotation pins the bindings via checked mode regardless; this
/// only affects annotation-free synthesis. Returns `a` when neither side
/// is parameterized (identical types). Keeps [`join_types`] commutative.
pub(super) fn more_general_type(kb: &KnowledgeBase, a: &Value, b: &Value) -> Value {
    match (more_general_form(kb, a), more_general_form(kb, b)) {
        (Some("sort_ref"), Some("parameterized")) => a.clone(),
        (Some("parameterized"), Some("sort_ref")) => b.clone(),
        _ => a.clone(),
    }
}

/// The form tag of a branch type for [`more_general_type`]'s bare-vs-
/// parameterized normalization, via the canonical classifier ([`type_head`]) so
/// it is carrier-agnostic. WI-361: a `Value::Node` parameterized reports
/// `parameterized` even though its raw functor is now the base sort (the carrier
/// mirrors the term backing `Fn{S,named}`), exactly like a term-backed
/// `Fn{S,named}` / `Ref(S)` on the `TermId` side — a raw-functor read would miss
/// it and mis-normalize the join to the over-specific side.
fn more_general_form(kb: &KnowledgeBase, v: &Value) -> Option<&'static str> {
    type_dispatch_name_view(kb, v)
}

/// WI-464: which lattice bound a per-binding combine computes — the least upper
/// bound (`Lub`, used by [`join_types`]) or the greatest lower bound (`Glb`, used
/// by [`meet_types`]). Threaded through [`combine_parameterized_same_base`] so the
/// shared per-binding-by-variance skeleton serves both; a CONTRAVARIANT parameter
/// flips it (the dual bound).
#[derive(Clone, Copy)]
enum LatticeDir {
    Lub,
    Glb,
}

impl LatticeDir {
    /// The dual direction — a contravariant parameter computes the opposite bound
    /// of its enclosing type (the LUB of `Fn[A=…]` meets the two `A`s).
    fn flip(self) -> Self {
        match self {
            LatticeDir::Lub => LatticeDir::Glb,
            LatticeDir::Glb => LatticeDir::Lub,
        }
    }
}

/// WI-464: the GREATEST LOWER BOUND of two branch types — the lattice DUAL of
/// [`join_types`]. The Type lattice has a bottom (`nothing`), so the meet is
/// TOTAL: two types always have a GLB (at worst `nothing`), unlike the top-less
/// join (which returns `None` for incomparable nominal types). Used for the
/// CONTRAVARIANT-parameter arm of the parameterized LUB (a contravariant param's
/// join is the meet of its two binding values) and, dually, for the covariant arm
/// of the parameterized GLB.
///
/// Mirrors [`join_types`] arm-for-arm with the order reversed: a `type_var`
/// wildcard meets to the other side; when one type conforms to the other the
/// SUBtype wins (vs the supertype for join); mutually-compatible types meet to the
/// MORE-SPECIFIC side ([`more_specific_type`], dual of [`more_general_type`]); two
/// same-base parameterized types recurse per declared variance; incomparable types
/// meet to `nothing`. Commutative, like [`join_types`].
pub(super) fn meet_types(kb: &mut KnowledgeBase, a: Value, b: Value) -> Value {
    if type_dispatch_name_view(kb, &a) == Some("type_var") {
        return b;
    }
    if type_dispatch_name_view(kb, &b) == Some("type_var") {
        return a;
    }
    // WI-335: each direction of the lattice check is independent — per-direction
    // substs, exactly as [`join_types`].
    let mut subst_ab = Substitution::new();
    let mut subst_ba = Substitution::new();
    match (
        types_compatible(kb, &mut subst_ab, &a, &b),
        types_compatible(kb, &mut subst_ba, &b, &a),
    ) {
        // `a <: b`: `a` is the SUBtype, hence the lower bound (dual of join).
        (true, false) => a,
        // `b <: a`: `b` is the lower bound.
        (false, true) => b,
        // Mutually compatible (identical, or bare-vs-parameterized): the
        // more-SPECIFIC side is the GLB (dual of join's more-general choice).
        (true, true) => more_specific_type(kb, &a, &b),
        // Incomparable: a same-base parameterized GLB if both qualify, else the
        // bottom type — two incomparable nominal types share no lower bound but
        // `nothing`.
        (false, false) => meet_parameterized_same_base(kb, &a, &b)
            .unwrap_or_else(|| Value::term(kb.make_nothing_type())),
    }
}

/// WI-464: dual of [`more_general_type`] — between two MUTUALLY-compatible types
/// (identical, or the bare-vs-parameterized normalization where each conforms to
/// the other) the GLB keeps the MORE-SPECIFIC side: `Option` meet `Option[T = Int]`
/// is `Option[T = Int]`. Returns `a` when neither side is parameterized (identical
/// types). Keeps [`meet_types`] commutative.
fn more_specific_type(kb: &KnowledgeBase, a: &Value, b: &Value) -> Value {
    match (more_general_form(kb, a), more_general_form(kb, b)) {
        (Some("sort_ref"), Some("parameterized")) => b.clone(),
        (Some("parameterized"), Some("sort_ref")) => a.clone(),
        _ => a.clone(),
    }
}

/// WI-464: two types are EQUIVALENT when each is a subtype of the other — the
/// equality an INVARIANT parameter demands of its two binding values for the
/// parameterized LUB/GLB to keep that binding (else the whole type falls back to
/// its conservative bound). Context-free, like [`is_subtype`]: a fresh subst per
/// direction.
fn types_equivalent(kb: &mut KnowledgeBase, a: &Value, b: &Value) -> bool {
    let mut s1 = Substitution::new();
    if !types_compatible(kb, &mut s1, a, b) {
        return false;
    }
    let mut s2 = Substitution::new();
    types_compatible(kb, &mut s2, b, a)
}

/// WI-464: combine two SAME-BASE parameterized types into their LUB (`Lub`) or GLB
/// (`Glb`), recursing per binding by the parameter's DECLARED variance ([`declared_variance`]).
/// The shared skeleton behind [`join_parameterized_same_base`] /
/// [`meet_parameterized_same_base`]: a COVARIANT parameter combines in the
/// enclosing `dir`, a CONTRAVARIANT one in the dual ([`LatticeDir::flip`]), an
/// INVARIANT one requires its two values be [`types_equivalent`], and a BIVARIANT
/// one (variance both ways ⇒ irrelevant to subtyping) takes `dir` for a sound,
/// commutative representative.
///
/// Returns `None` when the two are NOT same-base parameterized (the caller then
/// widens for a join, or bottoms-out for a meet). WI-769: "same base" is CANONICAL
/// sort identity; each binding's key is looked up by the one shared binding-key
/// rule ([`binding_for_param`] — a citation keys `T` canonically, a written
/// signature bare; raw identity missed the pair and silently dropped the whole
/// schema); and the result is CONSTRUCTED on the sort's canonical base and param
/// symbols, keeping the callers' documented commutativity STRUCTURAL for declared
/// plain params (an undeclared/foreign-spelled key and an invariant binding's kept
/// value still follow the a-side). When a binding
/// cannot be combined — a covariant/contravariant sub-combine has no result, an
/// invariant param's values differ, the two sides bind different param subsets, or
/// a duplicate-keyed side double-consumes one slot — it answers
/// [`SameBaseCombine::NoCombination`], which the LUB reads as NO JOIN (WI-20260829-WBXGX
/// retired the bare-base fallback: `S` is an upper bound that is also a lower bound) and
/// the GLB as the bottom type.
/// Construction stays on the hash-consed term path (the
/// nominal, heavily-shared structure that should remain a `TermId`); a `Value::Node`
/// combined binding (an arrow / denoted type — exotic for a branch join) falls back
/// to the conservative bound rather than minting a Node-carried type.
/// WI-20260829-WBXGX — what [`combine_parameterized_same_base`] found, as three answers
/// rather than two.
///
/// `Option<Value>` conflated the two failures, and they call for opposite things: "these
/// are not two same-base parameterized types" means the caller should WIDEN and retry,
/// while "same base, and a binding has no combination" means the search is OVER. For the
/// GLB the conflation was harmless (both end at the bottom type); for the LUB it was the
/// bug — see [`SameBaseCombine::NoCombination`].
pub(super) enum SameBaseCombine {
    /// Not two same-base parameterized types. The caller widens (LUB) or bottoms out (GLB).
    NotApplicable,
    /// Combined per binding, by each parameter's declared variance.
    Combined(Value),
    /// Same base, and some binding has NO combination in this direction — a covariant
    /// sub-combine with no result, an invariant param whose values differ, different param
    /// subsets, a duplicate key.
    ///
    /// **FOR THE LUB THIS IS "NO JOIN", NOT "THE BARE BASE".** It used to return `S`, on the
    /// reasoning that every `S[..] <: S` so the bare sort is a sound upper bound. It IS an
    /// upper bound; it is not a usable one, because `types_compatible` treats bare-vs-
    /// parameterized as compatible in BOTH directions — so `S` is also below every
    /// instantiation, and handing it back as a join launders the bindings. MEASURED
    /// (`/code-review`): `takeOpts([some(1), some("x")])` against `List[T = Option[T =
    /// Int64]]` loaded, putting a `String` in an `Int64` slot, and so did the same shape
    /// through an `if`. A lattice whose "least upper bound" is also a lower bound has no
    /// join there, and saying so is the honest answer.
    ///
    /// FOR THE GLB the bottom type stays: `nothing` is below everything and is not
    /// compatible upward, so it carries none of this.
    NoCombination,
}

fn combine_parameterized_same_base(
    kb: &mut KnowledgeBase,
    dir: LatticeDir,
    a: &Value,
    b: &Value,
) -> SameBaseCombine {
    let (a_base, a_binds) = match extract_type(kb, a) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return SameBaseCombine::NotApplicable,
    };
    let (b_base, b_binds) = match extract_type(kb, b) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return SameBaseCombine::NotApplicable,
    };
    // WI-769: ONE canonical comparison derives both the same-base gate and the
    // per-binding key-match mode (the dispatch arm-(2) idiom, `match_candidate_
    // against_goal`) — canonical sort identity, not raw symbol identity: a sort
    // interns under multiple Symbol copies (WI-617), and a raw `!=` read a twin
    // pair as different sorts, turning a same-sort combine into a spurious
    // no-join. A different SORT is not a same-base combine — the caller widens
    // (LUB) or bottoms out (GLB).
    let key_match = BindingKeyMatch::for_bases(kb, a_base, b_base);
    if key_match != BindingKeyMatch::Label {
        return SameBaseCombine::NotApplicable;
    }
    // The combine CONSTRUCTS a type — build base AND binding keys on the sort's
    // canonical symbols (canonicalize at the producer, WI-581), whichever
    // copies/spellings the inputs carried: a-side key spellings would make the
    // result depend on argument order, against the callers' documented
    // commutativity (`join_types(a, b) == join_types(b, a)`). The commutativity
    // is structural for DECLARED plain params; a constrained param (filtered
    // from `sort_type_params_as_pairs`), a foreign-spelled key, and an
    // invariant binding's kept value still follow the a-side.
    let base = kb.canonical_sort_sym(a_base);
    let declared = sort_type_params_as_pairs(kb, base);
    // Same base sort ⇒ same params; guard a malformed/partial binding set.
    if a_binds.len() != b_binds.len() {
        return SameBaseCombine::NoCombination;
    }
    let mut used = vec![false; b_binds.len()];
    let mut result: Vec<(Symbol, TermId)> = Vec::with_capacity(a_binds.len());
    for (param, av) in &a_binds {
        // WI-769: key lookup by the one shared rule ([`binding_for_param`]) —
        // the sides may spell one slot canonically vs bare (the WI-726/764/768
        // producer split), which raw `q == param` missed, silently dropping the
        // whole schema. A residual miss means the sides bind DIFFERENT param
        // subsets (partial instantiations): no per-param combine exists, so the
        // conservative bound, as for an uncombinable binding below. A DOUBLE-
        // consumed b slot (a duplicate-keyed a side — the recorded WI-764
        // producer defect) also bows out conservatively: label-bridging is not
        // injective, and constructing from it would mint a duplicate-keyed type
        // that silently drops one of b's bindings.
        let Some(bi) = binding_index_for_param(kb, &b_binds, *param, key_match) else {
            return SameBaseCombine::NoCombination;
        };
        if std::mem::replace(&mut used[bi], true) {
            return SameBaseCombine::NoCombination;
        }
        let bv = &b_binds[bi].1;
        let combined: Value = match declared_variance(kb, base, *param) {
            Variance::Covariant | Variance::Bivariant => {
                match combine_binding(kb, dir, av.clone(), bv.clone()) {
                    Some(v) => v,
                    None => return SameBaseCombine::NoCombination,
                }
            }
            Variance::Contravariant => {
                match combine_binding(kb, dir.flip(), av.clone(), bv.clone()) {
                    Some(v) => v,
                    None => return SameBaseCombine::NoCombination,
                }
            }
            Variance::Invariant => {
                if types_equivalent(kb, av, bv) {
                    av.clone()
                } else {
                    return SameBaseCombine::NoCombination;
                }
            }
        };
        // Result key: the sort's DECLARED canonical param symbol. Only an
        // UNDOTTED (bare-written) key re-keys by label — a dotted key either IS
        // a declared param (identity) or is FOREIGN (another sort's / an
        // op-scoped `T`, WI-708) and keeps its spelling: re-keying it by short
        // name would be a guess, and `same_label`'s both-dotted debug_assert
        // polices exactly that comparison. A re-key COLLISION (both sides
        // symmetrically duplicate-keyed, invisible to the used-guard above)
        // bows out conservatively too — the result never carries duplicate keys.
        let canon_key = if let Some(i) =
            binding_index_for_param(kb, declared.as_slice(), *param, BindingKeyMatch::Identity)
        {
            declared[i].0
        } else if !kb.qualified_name_of(*param).contains('.') {
            binding_index_for_param(kb, declared.as_slice(), *param, BindingKeyMatch::Label)
                .map(|i| declared[i].0)
                .unwrap_or(*param)
        } else {
            *param
        };
        if result.iter().any(|(k, _)| *k == canon_key) {
            return SameBaseCombine::NoCombination;
        }
        match combined {
            Value::Term { id: t, .. } => result.push((canon_key, t)),
            // A Node-carried combined binding: stay off the Node path; bail.
            _ => return SameBaseCombine::NoCombination,
        }
    }
    let base_ref = kb.make_sort_ref(base);
    SameBaseCombine::Combined(Value::term(kb.make_parameterized_type(base_ref, &result)))
}

/// WI-464: combine one binding's two values per the lattice `dir`. `Lub` is the
/// partial [`join_types`] (the Type lattice is top-less, so `None` propagates);
/// `Glb` is the total [`meet_types`] (a bottom exists, so always `Some`). WI-20260829-WBXGX
/// made the `Lub` genuinely partial at the same-base arm too — see
/// [`SameBaseCombine::NoCombination`] — so a `None` here now propagates from one more place.
fn combine_binding(kb: &mut KnowledgeBase, dir: LatticeDir, a: Value, b: Value) -> Option<Value> {
    match dir {
        LatticeDir::Lub => join_types(kb, a, b),
        LatticeDir::Glb => Some(meet_types(kb, a, b)),
    }
}

/// WI-464: the parameterized LUB of two same-base parameterized types — the
/// `Lub` instance of [`combine_parameterized_same_base`]. `join(Option[T = Cat],
/// Option[T = Dog]) = Option[T = Animal]`.
pub(super) fn join_parameterized_same_base(
    kb: &mut KnowledgeBase,
    a: &Value,
    b: &Value,
) -> SameBaseCombine {
    combine_parameterized_same_base(kb, LatticeDir::Lub, a, b)
}

/// WI-464: the parameterized GLB of two same-base parameterized types — the `Glb`
/// instance of [`combine_parameterized_same_base`].
fn meet_parameterized_same_base(kb: &mut KnowledgeBase, a: &Value, b: &Value) -> Option<Value> {
    match combine_parameterized_same_base(kb, LatticeDir::Glb, a, b) {
        SameBaseCombine::Combined(v) => Some(v),
        // The GLB is TOTAL: a bottom exists, and `nothing` is a sound lower bound of any
        // pair. Unlike the LUB's bare base it is not compatible upward, so it launders
        // nothing — see [`SameBaseCombine::NoCombination`].
        SameBaseCombine::NoCombination => Some(Value::term(kb.make_nothing_type())),
        SameBaseCombine::NotApplicable => None,
    }
}

/// WI-20260829-9TGP7: is this expected type NO REAL BOUND on a branching expression's
/// branches — a wildcard every type conforms to, rather than a constraint?
///
/// TWO FORMS, and before this predicate only the first was recognized. `type_var` is the
/// declared wildcard the typer already treated as "compatible with anything"
/// ([`types_compatible`]'s first arm). `FlexVar` is the ENGINE's own unbound logical
/// variable — `map`'s `Dst` at a call site that has not yet been told what the callback
/// returns — and it is exactly as unconstraining, but [`types_compatible`] has no arm for
/// it at all: `type_dispatch_name_view` answers `None` for a variable head (deliberately,
/// WI-1079 — the structural arms are not where a variable is decided), so the subtype
/// relation fell to its `_ => false` and read an UNCONSTRAINED expectation as a MISMATCH.
///
/// `Skolem` is NOT here and that is the point of naming the two separately: an opened
/// existential / a rigidified parameter unifies with nothing but itself, so it IS a real
/// bound and a branch that does not match it must still be refused. MEASURED, not assumed
/// — an operation's declared `[T]` arrives here as a `Skolem` (`rigidify_op_type_params`,
/// WI-392, rigidifies it for the body check), so `if b then x else 1` at `-> T` still
/// refuses the `Int64` branch while `if b then x else y` still loads. Both rows are
/// `wi_9tgp7_branch_expected_flex_var_test::a_rigid_expectation_still_refuses`.
///
/// NOT [`is_type_variable`] (in `type_preds.rs`, not nearby — the first
/// version of this note said "one screen up" and was wrong), the three-way test that answers a
/// DIFFERENT question — "is this position generic at all", for the list-literal lowering,
/// where a skolem and a flex var carry the same (absent) information. Here they do not: a
/// skolem BOUNDS its branches and a flex var does not, so the two predicates must disagree
/// on `Skolem` and a future reader merging them would silently delete the refusal above.
fn expected_is_unconstraining(kb: &KnowledgeBase, exp: &Value) -> bool {
    matches!(
        type_head(kb, exp),
        TypeHead::TypeVar(_) | TypeHead::FlexVar(_)
    )
}

/// WI-287: the result type of a branching expression (`match` / `if`),
/// computed from *every* branch body instead of taking branch 0 (the old
/// soundness gap). `construct` names the form for diagnostics ("match",
/// "if"); `branch_tys` are the branch-body types in source order.
///
/// When an expected type is present every branch must conform to it
/// (`types_compatible`, covering entity→sort and `requires`-refine) —
/// the enforcement the old code skipped, since it only type-checked the
/// synthesized type, which was branch 0. The result is the join of the
/// branch types ([`join_types`] — a sound common supertype, not strictly
/// the lub), preferred for precision but never widened past the expected
/// type and never collapsed to a `type_var` hint (which would lose the
/// concrete branch type when the expression is passed as a generic
/// argument). The Type lattice is top-less: branches with no common
/// supertype and no expected type to bound them (e.g. `Int` vs
/// `String`) are a type error, reported against the branch that breaks
/// the join.
///
/// WI-20260829-9TGP7: AN EXPECTED TYPE THAT IS A BARE VARIABLE IS NOT A BOUND, and this
/// is one of the few expression forms that ENFORCES its top-down hint rather than ignoring
/// it — so it is the one that had to learn the difference. See
/// [`expected_is_unconstraining`]; the three arms it guards are marked below.
pub(super) fn compute_branch_join_type(
    kb: &mut KnowledgeBase,
    // WI-20260824-Q0093: per branch — its type, its span, and the OCCURRENCE that type
    // came from. The third is read only on the failure path ([`denoted_type_value`]), so a
    // branch rejected for denoting a type says which one; the branch families' negative
    // destination is this check, so without it `if c then "a" else Cell` could only say
    // `got Type`.
    branch_tys: &[(Value, Option<Span>, Option<Rc<NodeOccurrence>>)],
    expected: Option<Value>,
    construct: &str,
) -> Result<Value, TypeError> {
    // Intern once up front so the type-lattice borrows below can take
    // `kb` immutably without colliding with a deferred `kb.intern`.
    let branch_ctx = TypeErrorContext::Rule {
        name: kb.intern(construct),
        field: RuleField::Whole,
    };
    // WI-342: branch types are carrier-agnostic `Value`s (a branch may be a
    // `Value::Node` lambda arrow). The join returns one of them — no
    // re-grounding. `TypeError` fields are `Value` (S2), so the branch carrier
    // flows straight into any diagnostic below.
    let first_ty: Value = match branch_tys.first() {
        Some((b, _, _)) => b.clone(),
        None => {
            return Err(TypeError::Other {
                site: TypeError::here(),
                span: None,
                context: branch_ctx,
                expected: format!("non-empty {construct} expression"),
                actual: format!("{construct} with no branches"),
            })
        }
    };

    // Checked mode: every branch must conform to the expected type
    // (`types_compatible` covers entity→sort and `requires`-refine).
    // This is the enforcement the old code skipped — it only ever
    // type-checked the synthesized type, which was branch 0.
    // WI-20260829-9TGP7: ...unless the expectation is no bound at all. An unbound
    // inference variable (`map`'s `Dst`, before the callback has told the call site what
    // it returns) constrains nothing — it is a HINT flowing top-down, and the binding that
    // makes it concrete happens ABOVE, when the lambda's arrow unifies with the declared
    // `(x: Element) -> Dst`. Running the subtype relation against it here refused every
    // branch, because `types_compatible` has no variable arm (see
    // [`expected_is_unconstraining`]). The `Substitution` below is fresh and discarded, so
    // there was never a binding to be had here either way.
    let checked = expected
        .as_ref()
        .filter(|e| !expected_is_unconstraining(kb, e));
    if let Some(exp) = checked {
        for (bt, span, node) in branch_tys {
            // WI-335: each branch's conformance check is independent.
            let mut subst = Substitution::new();
            if !types_compatible(kb, &mut subst, bt, exp) {
                return Err(TypeError::TypeMismatch {
                    site: TypeError::here(),
                    span: *span,
                    context: branch_ctx,
                    expected: exp.clone(),
                    denoted: denoted_type_value(kb, node.as_ref()),
                    actual: bt.clone(),
                });
            }
        }
    }

    // Synthesized type: the join (common supertype) of the branch types. Track the
    // branch that breaks the join (no common supertype) for diagnostics.
    let mut acc = first_ty;
    let mut clash: Option<(Value, Option<Span>, Option<Rc<NodeOccurrence>>)> = None;
    for (bt, span, node) in &branch_tys[1..] {
        match join_types(kb, acc.clone(), bt.clone()) {
            Some(j) => acc = j,
            None => {
                clash = Some((bt.clone(), *span, node.clone()));
                break;
            }
        }
    }

    match (clash, expected) {
        // The join exists: prefer this precise synthesized type, but
        // never widen past an expected type the branches already satisfy
        // (and never collapse a precise join to a `type_var` hint).
        (None, None) => Ok(acc),
        (None, Some(exp)) => {
            // WI-20260829-9TGP7: an unconstraining expectation loses to the join
            // outright. `types_compatible(acc, ?Dst)` is false (no variable arm), so
            // without this the precise `Int64` would be discarded for the bare `?Dst` —
            // the very collapse the comment above forbids, one form over.
            if expected_is_unconstraining(kb, &exp) {
                return Ok(acc);
            }
            let mut subst = Substitution::new();
            if types_compatible(kb, &mut subst, &acc, &exp) {
                Ok(acc)
            } else {
                Ok(exp)
            }
        }
        // No climb-computed join, but every branch conforms to `expected`
        // (checked above) — `expected` is their common upper bound. This
        // is the `requires`-refine case the entity-parent climb can't see.
        // A `type_var` `exp`, though, is no real bound (it's compatible
        // with anything), so accepting it would collapse a genuine clash
        // to a wildcard — report the clash instead, mirroring the
        // type_var guard in the `(None, Some)` arm above.
        (Some((bt, span, node)), Some(exp)) => {
            // WI-20260829-9TGP7: `FlexVar` joins `type_var` here for the same reason the
            // comment above gives — an unbound inference variable is no upper bound, so
            // accepting it would collapse a genuine branch clash to a wildcard.
            if expected_is_unconstraining(kb, &exp) {
                Err(TypeError::TypeMismatch {
                    site: TypeError::here(),
                    span,
                    context: branch_ctx,
                    expected: acc.clone(),
                    denoted: denoted_type_value(kb, node.as_ref()),
                    actual: bt.clone(),
                })
            } else {
                Ok(exp)
            }
        }
        // No expected type and no common supertype — the top-less lattice
        // has no join, so the branch types genuinely clash.
        (Some((bt, span, node)), None) => Err(TypeError::TypeMismatch {
            site: TypeError::here(),
            span,
            context: branch_ctx,
            expected: acc.clone(),
            denoted: denoted_type_value(kb, node.as_ref()),
            actual: bt.clone(),
        }),
    }
}

/// WI-RKMD4: the bare↔bare subtype relation, carrier-agnostically — nominal identity /
/// entity subtyping / `refines`, then WI-344 provider admissibility, then WI-405 FACET B's
/// alias re-dispatch.
///
/// LIFTED OUT OF [`types_compatible_term_dispatch`] BECAUSE THE OTHER DISPATCH HAD NO ARM
/// AT ALL. [`types_compatible_view_structural`] carries a peer for every other non-`false`
/// arm — `sort_ref`↔`parameterized` in both directions included — and had none for
/// `sort_ref`↔`sort_ref`, so a pair of bare refs on a `Value` carrier fell to its `_ =>
/// false` and read as a MISMATCH, identical sorts included. It was unreachable only by
/// accident of production (a bare ref is normally hash-consed, so the both-`Term` early
/// return caught it first) — a silent wrong answer waiting for the first non-`Term`
/// producer, which is what [`nominal_heads_compatible`] became. One shared body rather
/// than a second spelling: the WI-342 discipline the parameterized arm already follows,
/// and the only way the two carriers cannot drift on when two sort identities are one.
///
/// `None` from either side (not a bare sort) is `false`, as the deleted `sort_ref_-
/// compatible` answered — the arm is reached only when both dispatch as `sort_ref`, so
/// that case is unreachable rather than lenient.
///
/// The alias re-dispatch is reached only after the nominal and provider checks fail (a
/// pure loosening), and each branch runs on a PROBE clone committed only on success, so a
/// failed branch can never leak partial bindings into the next branch or the caller
/// (mirrors [`bare_provider_binding_precise`]); the bare↔bare comparison is
/// ground-vs-ground, so a success commits no new bindings anyway. Termination:
/// [`resolve_alias_shape`] is `None` for a non-alias AND (WI-405) for a non-well-founded
/// recursive alias, so the recursion bottoms out.
pub(super) fn bare_sort_compatible<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual: &A,
    expected: &B,
) -> bool {
    let (Some(a), Some(e)) = (
        extract_sort_ref_sym(kb, actual),
        extract_sort_ref_sym(kb, expected),
    ) else {
        return false;
    };
    // Provider admissibility is CONFINED to this arm so it never rides the `sort_ref ↔
    // parameterized` base check and drops a parameterized spec's bindings — see
    // [`sort_provides_admissibly`].
    if sort_sym_compatible(kb, a, e) || sort_provides_admissibly(kb, a, e) {
        return true;
    }
    // WI-20260829-N01PY — the WITNESS leg, and it belongs at BOTH bare-expected arms.
    // The first cut wired it only into `(parameterized, sort_ref)`, where the stdlib's
    // `MappedStream[…]` lives; a witnessed carrier with NO type parameters (`sort
    // PlainWitness provides Cap[C = Plain]`) compares here instead and stayed refused —
    // one arm fixed, its sibling left, which is the shape WI-405 FACET A was filed for
    // one relation over. `a_bare_witnessed_carrier_is_admissible_too` is that row.
    //
    // The actual is BARE, so its type term IS `Ref(a)` — no bindings to carry. No
    // entity→parent hop is added here: `sort_provides_admissibly` above makes that hop on
    // the SYMBOL, and a witness goal needs the carrier's TYPE, which the parent's symbol
    // is not; measured, an entity-typed value already arrives at this arm as its parent
    // sort, so the hop has nothing to reach and is left unwritten rather than shipped
    // untested.
    if witness_provides_admissibly(kb, WitnessActual::Bare(a), a, e) {
        return true;
    }
    // WI-405 FACET B: resolve a structured (ground) alias on EITHER side and re-dispatch,
    // so two aliases of the same shape (`sort IntList = List[T = Int64]; sort IntList2 =
    // List[T = Int64]`) compare by their underlying shapes and not by nominal NAME only.
    // WI-381 wired alias resolution into the bare↔parameterized arms but NOT here.
    for (shape_sym, shape_is_actual) in [(a, true), (e, false)] {
        let Some(shape) = resolve_alias_shape(kb, shape_sym) else {
            continue;
        };
        let mut probe = subst.clone();
        let ok = if shape_is_actual {
            types_compatible(kb, &mut probe, &TermIdView(shape), expected)
        } else {
            types_compatible(kb, &mut probe, actual, &TermIdView(shape))
        };
        if ok {
            *subst = probe;
            return true;
        }
    }
    false
}

/// Check if sort symbol A is compatible with sort symbol B:
/// same symbol, entity_of, or refines via requires chain.
///
/// WI-872 — THE IDENTITY LEG IS [`same_sort_canonical`], NEVER THE LAST SEGMENT. This
/// read `local_name_of(a) == local_name_of(b)` under the comment "handles qualified vs
/// short name", which is the unsound short-name comparison of two SORT identities that
/// WI-672 deleted `same_symbol` for (spec §8.6: identity is by resolved symbol, never by
/// last segment). It is not on some peripheral path: this IS the nominal leg of
/// [`types_compatible`], so every position that asks "is this type that type" asked it by
/// short name — five call sites, all in that one relation.
///
/// TWO OPPOSITE SYMPTOMS FROM ONE BRANCH, which is why the ticket's account was half of
/// it. At an ARGUMENT position it ACCEPTED — `operation takeA(f: a.Foo)` swallowed a
/// `b.Foo` from another namespace, a silent wrong value. At a DISPATCH it REFUSED: a
/// local `sort Pair`/`Set`/`Map` was offered the PRELUDE sort's provision, whose condition
/// then resolved at the prelude sort's own parameter and failed — `no impl matches …
/// PartialEq[T = anthill.prelude.Pair.A]` — so those short names were effectively
/// RESERVED against a user sort. WI-872 was filed for the second and named only it.
///
/// MEASURED, both directions, with the branch stashed and rebuilt for the control:
/// a two-namespace `Foo` pair LOADED CLEAN before and is refused after; local
/// `Set`/`Map`/`Pair` (the WI-1098-underivable `(a: Float, b: Int64)` shape) were refused
/// before and load after. `List`/`Option`/`Stream`/`Duple` load EITHER WAY and are
/// therefore not evidence — see `wi872_short_name_sort_identity_test`, which says so at
/// each row.
///
/// WHAT THE DELETED BRIDGE WAS HOLDING UP: nothing. Instrumented to fire only on the
/// bridging case (symbols differ, short names agree), it logged ZERO firings across
/// `stdlib/`, `examples/github-todo/` and `anthill-todo/`, and the full workspace stayed
/// green but for the recorded-defect arm that panics BECAUSE the defect is fixed. A
/// genuinely bare-interned copy would have to be fixed at its PRODUCER anyway — the rule
/// [`KnowledgeBase::canonical_sym`] states for itself, "never papered over by a
/// `canonical_sym` call at the consumer".
pub(crate) fn sort_sym_compatible(
    kb: &KnowledgeBase,
    actual_sym: Symbol,
    expected_sym: Symbol,
) -> bool {
    if same_sort_canonical(kb, actual_sym, expected_sym) {
        return true;
    }

    // Entity subtyping: actual is entity of parent sort.
    // Check both direct match and transitive (parent's requires chain).
    if let Some(parent_sym) = kb.strict_parent_sort(actual_sym) {
        if sort_sym_compatible(kb, parent_sym, expected_sym) {
            return true;
        }
    }

    // Requires/refines: A refines B if A requires B (directly or transitively)
    if sort_refines(kb, actual_sym, expected_sym) {
        return true;
    }

    false
}

/// WI-344: provider admissibility — `actual_sym` (or, if it is an entity,
/// its parent sort) declares `fact expected_sym[carrier = …]`, so a value
/// of `actual_sym` is usable where the spec `expected_sym` is required.
/// The value-position twin of `requires`: `requires X` and `fact X[Y]` are
/// the demand and supply ends of one relation, so a position demanding the
/// spec is discharged by the supplying fact (the same `SortProvidesInfo`
/// that `requires`-resolution and field-membership checks consult — see
/// `check_value_sort_membership`).
///
/// Deliberately base-only, and called only from arms of [`types_compatible`]
/// where the EXPECTED side is a BARE spec (carries no bindings to drop) — NOT
/// from `sort_sym_compatible`, because that is also reached from the
/// `sort_ref ↔ parameterized` arms' base check, where a base-only accept would
/// admit a binding mismatch (a `Widget` providing `Comparable[T = Widget]`
/// accepted where `Comparable[T = Gadget]` is expected). Two such bare-expected
/// call sites: the original `(sort_ref, sort_ref)` arm (WI-344), and — uniformly
/// since WI-405 FACET A — the `(parameterized, sort_ref)` arm (a parameterized
/// carrier `S[bindings]` vs a bare spec it provides) and its carrier-agnostic
/// peer in [`types_compatible_view_structural`]. The accept stays sound at every
/// site for the same reason: the spec is bare. The same-parameter parameterized
/// case (`List[T]` vs `Stream[T]`) reaches subtyping only through
/// `parameterized_compatible`'s base check — where its per-binding loop validates
/// the bindings separately. The bare-value-vs-PARAMETERIZED-spec case (`Widget`
/// vs `Comparable[T = Widget]`) is handled by the binding-PRECISE
/// [`bare_provider_binding_precise`] (WI-402), which checks every expected binding
/// against the provider fact instead of dropping them. The fact is trusted to
/// mean `actual` implements `expected` (WI-343 validates that separately).
pub(super) fn sort_provides_admissibly(
    kb: &KnowledgeBase,
    actual_sym: Symbol,
    expected_sym: Symbol,
) -> bool {
    if sort_provides(kb, actual_sym, expected_sym) {
        return true;
    }
    // An entity value's provision comes from its parent sort.
    if let Some(parent_sym) = kb.strict_parent_sort(actual_sym) {
        return sort_provides_admissibly(kb, parent_sym, expected_sym);
    }
    false
}

/// WI-20260829-K0E8T — the ACTUAL side of a witness question, as its asker holds it.
///
/// Two variants because the arms that ask hold different things and the gate refuses
/// nearly always. [`types_compatible_term_dispatch`]'s `(parameterized, sort_ref)` arm
/// already HAS the actual's type term; [`bare_sort_compatible`] has only a sort SYMBOL
/// and used to mint `Ref(a)` for it BEFORE the gate — 1214 times per stdlib load, every
/// one for a question answered `false` a few lines later.
///
/// THE MINT IS CHEAP BUT UNBALANCED, which is the half that is not about speed.
/// `make_sort_ref` is `TermStore::alloc(Term::Ref(a))`, and on a hash-cons HIT `alloc`
/// still bumps a refcount that nothing on this path ever decrements — so a REFUSED
/// compare left the actual sort's term one reference heavier than it found it, forever.
/// The refcount is also the only observable: `Ref(Int64)` is long since interned, so the
/// eager mint added no SLOT and `TermStore::len` could not see it. That is what
/// `k0e8t_witness_gate_test` asserts, and what makes the defect invisible without it.
///
/// THE CARRIER IS A NUDGE, NOT A PROOF — the tests are the guard. There is no `TermId`
/// to pass until [`Self::term`] is called, and it is called past the gate, so the eager
/// mint is no longer the thing a caller reaches for. It is still WRITABLE:
/// `WitnessActual::Term(kb.make_sort_ref(a))` at the bare arm compiles and reinstates the
/// defect exactly (found by /code-review, which wrote it and ran it — an earlier version
/// of this paragraph claimed "UNSPELLABLE", which is false). What actually catches that
/// is `k0e8t_witness_gate_test`, and its module note says which rows move.
pub(super) enum WitnessActual {
    /// The caller already holds the actual's type term.
    Term(TermId),
    /// A BARE actual, whose type term is `Ref(sym)` — minted only past the gate.
    Bare(Symbol),
}

impl WitnessActual {
    /// FIND BEFORE ALLOC, and that is what ends the unbounded growth rather than merely
    /// narrowing its population. Hoisting the mint past the gate leaves the REFUSED
    /// compares (all but 32 of 30,726,442 across the `anthill-core` suite) allocating
    /// nothing at all — but an ACCEPTED one still ran `alloc`, which increfs on a
    /// hash-cons HIT, and nothing on this path ever decrements. A program type-checking
    /// the same witnessed pair repeatedly would add one reference per compare, without
    /// bound, and pin that slot forever (found by /code-review; the first cut shipped the
    /// hoist alone and left this).
    ///
    /// [`KnowledgeBase::find_sort_ref`] is WI-849's read-only half and answers `Some` for
    /// every sort whose `Ref` is already interned — which, after the first compare of a
    /// given carrier, is all of them. The `alloc` fallback is therefore bounded by the
    /// number of DISTINCT carriers, once each, not by the number of compares.
    ///
    /// NOT INCREFFING IS SOUND HERE because the id does not outlive the call: it is the
    /// re-entrancy key (removed on every exit) and one `goal_bindings` value handed to
    /// `spec_resolves_at_bindings`, which answers a `bool` and retains nothing. Nor can
    /// the slot be freed underneath it — type-checking retracts nothing, and the only
    /// route to a free is `decref`, which is reached from retraction alone.
    pub(super) fn term(self, kb: &mut KnowledgeBase) -> TermId {
        match self {
            Self::Term(t) => t,
            Self::Bare(s) => kb.find_sort_ref(s).unwrap_or_else(|| kb.make_sort_ref(s)),
        }
    }
}

/// WI-20260829-N01PY — provider admissibility THROUGH A WITNESS: the leg
/// [`sort_provides_admissibly`] structurally cannot have.
///
/// THE TWO READERS. A `provides` clause files `SortProvidesInfo(sort_ref = <the
/// ENCLOSING sort>, …)` — `load_provides_clause` writes `domain` there — so a WITNESS,
/// whose carrier appears only in the spec's carrier BINDING (`sort MappedStreamFinite
/// provides FiniteCollection[C = MappedStream[…]]`), files under the WITNESS. The
/// carrier-keyed walk [`sort_provides`] therefore answers FALSE for a carrier that is
/// fully spoken for, which [`provision_carriers_of_spec`]'s doc already states for the
/// eq-derive reader. DISPATCH does not ask that question — it reads the spec-base bucket
/// and matches each provision's carrier binding — so the two readers of one relation
/// disagreed, and this is the leg that ends the disagreement at the subtype side.
///
/// ONE ARM IS DELIBERATELY WITHOUT IT — `types_compatible_view_structural`'s
/// `(parameterized, sort_ref)`, which a DENOTED actual routes to. That is a stated known
/// gap with a drivable fixture and a ticket (WI-20260829-2NMXA); the reason it is not a
/// one-line addition is written at that arm. IT IS THAT ARM AND NOT THAT FUNCTION —
/// `types_compatible_view_structural`'s OTHER bare-expected arm does reach this leg, and
/// the inventory below says how.
///
/// THREE ARMS REACH IT, ACROSS BOTH DISPATCHERS, and only ONE of them is a textual call:
///   * [`types_compatible_term_dispatch`] `(parameterized, sort_ref)` — calls it directly.
///   * [`types_compatible_term_dispatch`] `(sort_ref, sort_ref)` — through
///     [`bare_sort_compatible`].
///   * [`types_compatible_view_structural`] `(sort_ref, sort_ref)` — through the SAME
///     [`bare_sort_compatible`], which is shared by both dispatchers. This one is why the
///     count is three and not two, and grepping this function's name finds only two of
///     the three (found by /code-review; the first version of this doc read "TWO CALL
///     SITES, BOTH BARE-EXPECTED ARMS of `types_compatible_term_dispatch`", which
///     under-counted the population a later census would trust).
///
/// Which arm a carrier lands at is decided by whether it has TYPE PARAMETERS, which has
/// nothing to do with how its provision is filed — the first cut wired only the
/// parameterized arm (where the stdlib's `MappedStream[…]` lives) and left a bare
/// witnessed carrier refused, which `a_bare_witnessed_carrier_is_admissible_too` is the
/// row for. Every arm above is BARE on the expected side, which is what makes the accept
/// sound for the reason [`sort_provides_admissibly`]'s doc gives: a bare spec carries no
/// bindings to drop.
///
/// MEASURED, four rows over one minimal fixture (`n01py_witness_provision_subtype_test`),
/// one axis varied — how the provision is FILED — and the DIRECT rows are the control
/// that passes either way:
///
///   | reader                  | DIRECT provision | WITNESS provision |
///   | dot dispatch `Cap.get(x)` | LOADS          | LOADS             |
///   | spec-typed ARG `sink(x)`  | LOADS          | REFUSED ← the gap |
///
/// In the stdlib that row IS the ticket: `MappedStreamFinite` is what makes
/// `xs.map(f)` finite, so `xs.map(f).size()` dispatches — while an operation the AUTHOR
/// declares over the same spec (`operation summarize(c: FiniteCollection)`) refused the
/// very same value. Option (a) of the ticket's three ("an eager consumer accepting any
/// `FiniteCollection` rather than a concrete `List`") was not a design road not taken; it
/// was unwritable.
///
/// THE CONDITION IS NOT WAIVED, and that is why this defers to [`resolve`] rather than
/// asking a structural question of its own. A witness is a CONDITIONAL instance —
/// `MappedStreamFinite requires FiniteCollection[C = S]`, i.e. "a mapped stream is finite
/// WHEN ITS SOURCE IS" — so accepting on the head alone would make a `MappedStream` over
/// an infinite generator an eagerly-consumable collection, which is precisely the
/// unsoundness `FiniteCollection` exists to prevent. `resolve` is the ONE owner of "does
/// this carrier satisfy this spec at these bindings" (it is what dispatch asks, and what
/// reports `no impl provides …` for an unmet condition), so asking it here cannot drift
/// from what dispatch decides. `an_unmet_witness_condition_is_still_refused` and
/// `an_infinite_source_is_still_refused` are that control, in the minimal fixture and in
/// the stdlib.
///
/// SCOPE `requires` ARE NOT VISIBLE HERE, deliberately and conservatively. The subtype
/// relation has no call site and no enclosing operation, so `available_requires` is
/// empty: a witness whose condition is met only by the CALLER's own `requires
/// FiniteCollection[C = S]` is still refused. That is strictly narrower than dispatch and
/// strictly wider than before this leg existed. It is STATED and not pinned by a cell, on
/// purpose: such a cell would be red for a reason nobody could separate from the arms
/// until the scope is actually threaded here — see the test file's module note, which
/// says so at the list of what the back-out moves.
///
/// THE GATE COMES BEFORE ANY RESOLUTION, and the whole function is reached only AFTER
/// `sort_sym_compatible` and [`sort_provides_admissibly`] have both refused — so it is
/// purely a loosening: no accept that stood before changes, which is what the
/// workspace-wide back-out says (6085 passed, 8 failed, all eight in
/// `n01py_witness_provision_subtype_test` and one capability-matrix table).
///
/// AND THE GATE IS CHEAP AT THE MEASURED POPULATION — WHICH IS A FACT ABOUT `stdlib/`,
/// NOT ABOUT THIS CODE. The first version of this paragraph asserted neither half from a
/// number: it read "`types_compatible` is hot" and priced the gate at "a memoized
/// [`spec_carrier_param`] read plus one `by_spec_base` bucket scan" — wrong twice over,
/// because `spec_carrier_param` runs AFTER the gate (the paragraph below says why it
/// MUST), and nothing had been counted. WI-20260829-K0E8T counted it, over a full
/// `stdlib/` load (`load_stdlib`, release; every row deterministic):
///
///   | `types_compatible` calls                          | 2799 |
///   | ... reaching [`bare_sort_compatible`]             | 1238 |
///   | ... falling through to this leg                   | 1214 |
///   | THIS FUNCTION's entries, all three arms           | 1267 |
///   | provision rids the gate looked at, TOTAL          |    4 |
///   | provisions whose witness carrier MATCHED          |    0 |
///   | entries with `provides_index` absent              |    0 |
///
/// `types_compatible` is therefore not hot in the sense the word carries — 2799 calls is
/// ~17 per millisecond of a 168 ms load — and the `by_spec_base` bucket is EMPTY at 1263
/// of the 1267 entries. BEFORE the split below, this leg was 87% of every
/// [`provisions_of_spec`] call in the load (1267 of 1457) while accounting for 0.2% of
/// the rids they decode (4 of 1924); after it, the load makes 194 such calls in all and
/// the leg is TWO of them.
///
/// PRICED per compare (200k in-process iterations, min-of-9, release), the gate against
/// the whole bare↔bare compare it rides on, BEFORE this ticket's repair:
///
///   | expected side is …                     | leg on | backed out | the gate |
///   | a sort nothing provides (1263 of 1267) |  566ns |      400ns |    166ns |
///   | `Stream` (6 provisions)                | 1593ns |      406ns |   1186ns |
///   | `FiniteCollection` (6 provisions)      | 3186ns |      396ns |   2790ns |
///
/// BOTH READINGS ARE THE ANSWER, and the ticket asked for both. Times the population the
/// leg is ~0.21 ms of a 168 ms load — 0.13%, which a paired in-process min-of-11
/// whole-load A/B cannot resolve (168.5 / 166.9 / 169.0 ms for shipped / eager-mint /
/// backed-out: three distributions that overlap completely, and the CONTROL has the
/// slowest minimum of the three). PER ENTRY it was 42% of the entire failed compare, and
/// 3–7× it once the expected spec HAS provisions — so a program whose failed compares
/// name `PartialEq` (22 provisions in `stdlib/`) rather than a plain sort pays a bill
/// `stdlib/` does not.
///
/// WHAT K0E8T CHANGED, both behaviour-preserving, and neither justified by the load:
///   * the bare arm no longer MINTS before the gate ([`WitnessActual`], which says what
///     the mint costs and why the refcount is the observable);
///   * `spec_canon` is threaded into [`provisions_from_rids`] and `actual_canon` is
///     deferred past the emptiness check, so the common path does ONE
///     `canonical_sort_sym` (an FQN string hash) where it did three, and never enters the
///     decoder at all.
///
///   RE-MEASURED, all five arms PAIRED IN ONE PROCESS on the same common-shape pair.
///   Per arm: the MINIMUM over five runs of a min-of-9 over 200k iterations — minimum,
///   because contention only ADDS, and ONE run could not separate the arms (D's gate
///   ranged 29–79 ns across three of them). The gate column is that arm minus E:
///
///   | A  old gate, eager mint (what HEAD did) |  566.0 ns | 166.4 ns |
///   | B  old gate, lazy mint                  |  525.1 ns | 125.5 ns |
///   | C  new gate, eager mint                 |  492.9 ns |  93.3 ns |
///   | D  new gate, lazy mint (SHIPPED)        |  451.4 ns |  51.8 ns |
///   | E  leg backed out (control)             |  399.6 ns |    n/a   |
///
///   166 ns → 52 ns, and 42% of the failed compare → 13% of it. AND WHERE IT BUYS
///   NOTHING, which is half the result: against `FiniteCollection` (6 provisions) the
///   gate moves 2790 → 2649 ns, 5%, because the per-fact DECODE dominates and neither
///   change touches it; and with `provides_index` absent all four arms sit at ~18.1 µs,
///   because the scan returns all 96 facts so the emptiness check cannot fire. Both are
///   by construction: what was removed is the EMPTY-bucket path's overhead, and that is
///   the only population either repair was aimed at.
///
/// WHAT IT DID NOT DO: memoize the witness carriers per spec, which would collapse the
/// gate to one `HashMap` lookup. At 0.15% of a load that buys nothing measurable and
/// costs a new index with its own invalidation surface — the WI-954 failure mode, a stale
/// index answering EMPTY. Revisit only against a program whose measured population is not
/// `stdlib/`'s; the counts above are what to re-take first.
///
/// THE `build_provides_index`-ABSENT CASE IS PATHOLOGICAL AND ALL BUT UNREACHABLE — not
/// unreachable, which is the correction a census bought. Before the index exists [`SymbolKeyedFactIndex::rids_or_scan`] returns EVERY
/// `SortProvidesInfo` fact (96 in `stdlib/`) and the per-fact re-filter throws them all
/// away: the same common-case compare costs 18058 ns with the leg against 8024 ns
/// without — the gate alone 10035 ns, 193× the 52 ns it costs indexed. Note the BASELINE
/// moves too, 400 → 8024 ns, because [`sort_provides_admissibly`] reads the same index: a
/// missing index is expensive for the whole relation, not for this leg.
///
/// `provides_index` is `None` only between a load phase's start and
/// `build_provides_index`, so the window is narrow: not one of the 1267 stdlib-load
/// entries lands in it, and across the whole `anthill-core` suite it is hit TWICE in
/// 30,726,442 entries — 6.5e-8, but not the zero a smaller sample would have reported.
/// That suite figure is ANCHORED TO THE COMMIT IT WAS TAKEN AT, `fd2af338` (13 binaries,
/// 5303 tests, 4381 threads); every other number here is re-taken on the base this change
/// actually ships against. That rebase moved the LOAD (~143 → ~168 ms) and moved no
/// census row and no per-compare column — the CONTROL arm moved with it, so it is the
/// four typer commits underneath and not this change. NEITHER REPAIR ABOVE HELPS THERE, by
/// construction: the scan returns all 96 facts, so the emptiness check cannot fire and
/// the mint is noise against 10 µs. The price is recorded so a future pass that moves a
/// `types_compatible` caller ahead of the index build knows what it would be paying.
pub(super) fn witness_provides_admissibly(
    kb: &mut KnowledgeBase,
    actual: WitnessActual,
    actual_base: Symbol,
    expected_spec: Symbol,
) -> bool {
    let spec_canon = kb.canonical_sort_sym(expected_spec);
    // THE GATE. Two steps, and the SPLIT is WI-20260829-K0E8T's: the WI-660
    // `by_spec_base` bucket first, and only if it is non-empty the decode +
    // `witness_dispatch_carrier` walk — that function being the ONE owner of the witness
    // criterion (its `None` means the provision's carrier IS its provider — a
    // self-provision or an instance fact, both of which `sort_provides_admissibly` has
    // already answered for). Reading the rids HERE rather than through
    // [`provisions_of_spec`] is what lets `actual_canon` wait: at 1263 of 1267
    // stdlib-load entries the bucket is empty, and canonicalizing the actual for a bucket
    // with nothing in it is an FQN string hash spent on a decided question. The empty
    // answer is now one `canonical_sort_sym` and one `HashMap` lookup, with no `Vec`
    // allocated and the decoder never entered.
    //
    // AND IT MUST COME BEFORE [`spec_carrier_param`], which is not merely an ordering
    // preference — it is what keeps this leg from ENLARGING that function's POPULATION.
    // `spec_carrier_param` walks `sort_type_params_as_pairs`, whose `published_param_var`
    // carries the WI-954 tripwire: a sort declaring a DOTTED type parameter (`sort a.b.T =
    // ?`) publishes no canonical variable for it, and the assert says so rather than
    // silently dropping the parameter. That assert's own doc records it as "LATENT, NOT
    // LIVE ... measured, 29 binaries, 4441 tests" — true only because the function was
    // asked about sorts NAMED IN PROVISIONS. Asked first, this leg would ask it about
    // EVERY bare expected sort in a failed compatibility check, and
    // `wi1000_secondary_entry_content_test::a_dotted_declaration_name_is_not_the_entrys_content`
    // aborts the load (MEASURED; and in a RELEASE build the `debug_assert` vanishes and the
    // parameter is silently dropped instead, which is the WI-384/WI-954 defect itself).
    // Behind the gate the population is exactly what it was: a spec with a provision whose
    // view is a `SortView`, which `witness_dispatch_carrier` already asks about.
    // Found by /code-review.
    let rids = provides_rids_by_spec(kb, spec_canon);
    if rids.is_empty() {
        return false;
    }
    let actual_canon = kb.canonical_sort_sym(actual_base);
    let rows: Vec<SmallVec<[(Symbol, TermId); 2]>> = provisions_from_rids(kb, spec_canon, rids)
        .filter_map(|(provider, spec_t, bindings)| {
            witness_dispatch_carrier(kb, expected_spec, provider, spec_t)
                .filter(|c| *c == actual_canon)
                .map(|_| bindings)
        })
        .collect();
    if rows.is_empty() {
        return false;
    }
    // The carrier PARAMETER is the slot the actual type goes in. A spec with none is not
    // one a witness can be keyed on — `witness_dispatch_carrier` reads the SAME param to
    // decide what a witness is, so a non-empty `rows` means this answers `Some` — and
    // `None` refuses, it does not pass.
    let Some(carrier_param) = spec_carrier_param(kb, spec_canon) else {
        return false;
    };
    let carrier_short = short_name_of(kb.local_name_of(carrier_param)).to_string();
    // EACH WITNESS ASKS ITS OWN GOAL. The carrier slot takes the ACTUAL type; every other
    // slot takes the value THAT PROVISION'S HEAD WRITES, verbatim.
    //
    // TAKING THEM FROM THE HEAD IS THE WHOLE TRICK, and two simpler spellings were
    // MEASURED WRONG before it — each passing one arm of the test file while failing the
    // other, which is what a control is for:
    //
    //   * OMITTING the siblings — `collect_provides_candidates` REJECTS a candidate whose
    //     head binds a type param the goal leaves out ("else every concrete `Eq` impl
    //     would match a bare `Eq` goal"), so every candidate is dropped and the goal
    //     reports `no impl provides`. Both arms fail.
    //   * A WILDCARD in the sibling slot — no spelling works for both candidate shapes,
    //     and that is a RULE rather than an accident. Against an impl-param head binding
    //     (`Element = T`, the stdlib witnesses) a wildcard is accepted un-constrained by
    //     `match_impl_param`'s WI-507 arm; against a CONCRETE one (`Element = Int64`, the
    //     minimal fixture) it must NOT be, because WI-824's rule is that an abstract
    //     per-call value does not match a concrete candidate — accepting would PIN a call
    //     to an impl the caller never chose. A minted `?_` passed the minimal fixture and
    //     failed the stdlib one; a fresh logic var did the reverse.
    //
    // The head's own value is neither: at an impl-param head it IS that param (accepted,
    // un-constraining, by the same WI-507 arm), and at a concrete head it is that
    // concrete (matched exactly). No value is invented, so nothing is claimed that the
    // provision did not already write.
    //
    // AND THE HEAD'S KEYS ARE TAKEN VERBATIM, which /code-review read as this being the
    // one `SortGoal` producer that skips `is_type_param_binding`. MEASURED, with that
    // filter added and instrumented: it drops ZERO bindings across the typer's rows and
    // the whole capability matrix, and changes no verdict — because `unwrap_spec_view`
    // has already dropped every non-`TermId` binding, and an `effects E = ?` param IS a
    // sort (WI-320), so the filter answers `true` for the very binding it was expected to
    // remove. A guard that refuses nothing is not shipped; the population it would guard
    // is stated here instead.
    // RE-ENTRANCY, and it is a correctness guard: `resolve` calls back into the subtype
    // relation to match a candidate head, so a provision whose carrier binding is the SPEC
    // ITSELF makes this question its own sub-question. See
    // `KnowledgeBase::witness_admissibility_in_flight` for the measured shape — the
    // borrow is dropped before `resolve` runs, and released on every exit below.
    let actual = actual.term(kb);
    let key = (actual, spec_canon);
    if !kb.witness_admissibility_in_flight.borrow_mut().insert(key) {
        return false;
    }
    for bindings in rows {
        let mut goal_bindings: SmallVec<[(Symbol, TermId); 2]> =
            smallvec::smallvec![(carrier_param, actual)];
        for (param, value) in bindings {
            if short_name_of(kb.local_name_of(param)) == carrier_short {
                continue;
            }
            goal_bindings.push((param, value));
        }
        // ONE OWNER for "does this carrier satisfy this spec at these bindings", shared
        // with declared-field validation — and it is the resolver DISPATCH uses, which is
        // what keeps this leg from becoming a second opinion. It is also what enforces
        // the witness's CONDITION: a witness is a conditional instance
        // (`MappedStreamFinite requires FiniteCollection[C = S]` — "a mapped stream is
        // finite WHEN ITS SOURCE IS"), so accepting on the head alone would make a mapped
        // stream over an infinite generator an eagerly-consumable collection, which is
        // the exact unsoundness `FiniteCollection` exists to prevent.
        if spec_resolves_at_bindings(kb, spec_canon, goal_bindings) {
            kb.witness_admissibility_in_flight.borrow_mut().remove(&key);
            return true;
        }
    }
    kb.witness_admissibility_in_flight.borrow_mut().remove(&key);
    false
}

/// WI-402 (bound/manifest half): BINDING-PRECISE provider admissibility — a value of a
/// bare concrete carrier sort conforms to a PARAMETERIZED spec type when the carrier
/// (or, for an entity, its parent sort — `sort_provides_admissibly`'s hop) PROVIDES the
/// spec and every binding the expected type carries checks against the value the
/// provider fact supplies for that param (matched by short name, the provider-view
/// convention). This is the bare↔parameterized counterpart of
/// [`parameterized_compatible_view`]'s WI-387 FIX 2 cross-sort arm: a bare carrier has
/// no bindings of its own, so EVERY expected binding resolves through the provider
/// view. The case `sort_provides_admissibly`'s doc deferred ("admitting it needs
/// binding-precise resolution") — `SubscriberStore provides DataProvider[K = String]`
/// now conforms to `DataProvider[K = String]`, while `DataProvider[K = Int64]` (binding
/// contradicted) and a non-provider stay mismatches.
///
/// A param the provider leaves unbound REJECTS — never silently passes (the expected
/// binding is a demand; an unverifiable supply must not discharge it). Purely a
/// LOOSENING of the `(sort_ref, parameterized)` arms: reached only after
/// `sort_sym_compatible` refused, so no existing accept changes. The WI-401
/// abstracting-return gate is unaffected — it runs AFTER conformance and still rejects
/// a PARTIAL manifest (an expected type that omits some spec member entirely).
///
/// The binding loop runs on a PROBE substitution, committed only on success — the arm
/// was substitution-pure before WI-402, and a failed multi-binding check must not leak
/// the prefix's bindings (e.g. a row-tail var bound by an effects binding) into the
/// caller's threaded subst (the per-direction hygiene `check_binding_by_variance`'s own
/// Invariant arm uses, one level up).
pub(super) fn bare_provider_binding_precise<E: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual_sym: Symbol,
    expected: &E,
) -> bool {
    let TypeExtractor::Parameterized {
        base: expected_base,
        bindings: expected_bindings,
    } = extract_type(kb, expected)
    else {
        return false;
    };
    let mut carrier = actual_sym;
    let (provider_view, carrier_param_is_ours) = loop {
        // WI-20260829-GNPG7 — TRANSITIVE here for the same reason as
        // `parameterized_compatible_view`'s `cross_sort_provider`, and this is the SECOND
        // site of the one gap, not a separate one: both are the subtype relation asking
        // "what does this carrier bind the spec's params to", and both asked it one hop
        // deep while `sort_provides` answered the neighbouring "does it provide it at all"
        // over the whole chain. MEASURED on the bare-actual side with the information
        // held constant — `nil()` (bare `List`) conformed to `Stream[E = {}]`, one hop,
        // and was refused at `Iterable[E = {}]`, two hops, for the same `E = {}` the same
        // provision determines.
        //
        // NOT the same walk as the `strict_parent_sort` loop around it: that one climbs
        // ENTITY→parent to find a carrier, this one composes provisions once a carrier is
        // fixed. Nesting them is what makes an entity of a 2-hop provider work.
        if let Some(found) = subtype_provider_view(kb, carrier, expected_base) {
            break found;
        }
        // Entity → parent sort. The chain is acyclic: `strict_parent_sort` is
        // the STRICT parent, so §6.3's eponymous self-edge never appears here.
        let Some(parent_sym) = kb.strict_parent_sort(carrier) else {
            return false;
        };
        carrier = parent_sym;
    };
    // WI-20260829-XZMGC — the same rule as [`parameterized_compatible_view`]'s, spelled
    // with the actual this site HAS: a composed view carries no carrier param, and here the
    // actual is a BARE sort, so its own type is a bare sort ref. Allocated inside the
    // composed branch only: this function is on the per-comparison subtype path and the
    // direct branch must stay allocation-free.
    //
    // `carrier`, NOT `actual_sym`, AND THE DIFFERENCE IS OBSERVABLE — they part company
    // when the entity→parent loop above climbed, i.e. the actual is an ENTITY of a
    // providing sort. `Iterable.C` declares no variance so the check is INVARIANT, and no
    // one value satisfies both spellings: MEASURED with a `boxed` argument, `Ref(carrier)`
    // accepts `Iterable[C = Box]` and refuses `Iterable[C = boxed]`, `Ref(actual_sym)` does
    // exactly the reverse. What decides is the DIRECT provision, which is the same question
    // with no composition in it: a carrier providing `Iterable` ITSELF binds `C` to that
    // carrier, so a `boxed` argument is accepted at `Iterable[C = DBox]` and refused at
    // `Iterable[C = DBox.boxed]`. `carrier` agrees with that; `actual_sym` would contradict
    // it. So the rule is the receiver's own type AS THE PROVISION SEES IT, and for an
    // entity that is the sort the provision is filed at.
    //
    // NOT A CLAIM ABOUT THE OTHER SITE. [`parameterized_compatible_view`] has no
    // entity→parent climb, so for an entity actual it finds no provider view at all and
    // refuses every carrier spelling — MEASURED, `boxed[T = Int64]` at `Iterable[C = Box]`,
    // `[C = Box[T = Int64]]`, `[C = boxed]` and `[C = boxed[T = Int64]]` are all refused,
    // with this change and with it backed out. That asymmetry is the missing climb and is
    // PRE-EXISTING; this ticket neither creates nor closes it. An earlier draft of this
    // comment claimed the two sites agree here — they do not, and only the bare one has an
    // answer to agree with. Found by /code-review.
    let composed_carrier: Option<(VarId, TermId)> = if carrier_param_is_ours {
        spec_carrier_param(kb, expected_base)
            .and_then(|p| type_param_vid_in_sort(kb, expected_base, p))
            .map(|vid| (vid, kb.alloc(Term::Ref(carrier))))
    } else {
        None
    };
    let mut probe = subst.clone();
    for (param, ev) in &expected_bindings {
        if let Some((cvid, self_ty)) = composed_carrier {
            if type_param_vid_in_sort(kb, expected_base, *param) == Some(cvid) {
                if !check_binding_by_variance(
                    kb,
                    &mut probe,
                    expected_base,
                    *param,
                    &TermIdView(self_ty),
                    ev,
                ) {
                    return false;
                }
                continue;
            }
        }
        let short = short_name_of(kb.local_name_of(*param));
        let Some(pv) = provider_view
            .iter()
            .find(|(p, _)| short_name_of(kb.local_name_of(*p)) == short)
            .map(|(_, v)| *v)
        else {
            return false;
        };
        // WI-391: a plain-sort-name leaf binding is now the canonical `Ref(S)` (normalized
        // at the producer, `sort_binding_to_value`), so `normalize_spec_binding_type` is a
        // no-op for it; retained as a defensive leaf-normalizer for any non-`Ref` shape. A
        // STRUCTURED binding value (`K = List[T = Int64]`) still rides raw and today REJECTS
        // — the deep/positional canonicalization (and the §5.3 extractability of structured
        // shapes) is the deferred fact-path / structured-binding work. Conservative: a false
        // REJECT only, never a false accept — anchored by the `#[ignore]`d wi402
        // structured-accept test.
        let pv = normalize_spec_binding_type(kb, pv).unwrap_or(pv);
        if !check_binding_by_variance(kb, &mut probe, expected_base, *param, &TermIdView(pv), ev) {
            return false;
        }
    }
    *subst = probe;
    true
}

/// WI-401 — detect an ABSTRACTING (sealing) return so the base model stays escape-free
/// (docs/design/path-dependent-types.md §5). A return is interface-expressible — and so
/// admitted — when it is concrete, or rooted at the operation's own inputs (a param's
/// type, the op's type-params), or (the deferred WI-402 admit-form) made manifest by an
/// `ensures`. The ONE thing that escapes is a return whose abstract member is minted
/// *inside* the body: a concrete carrier UPCAST to the **bare abstract spec it provides**
/// (`seal(s: SubscriberStore) -> DataProvider = s` — the `K = String` is erased, so the
/// resulting `DataProvider.K` roots at nothing in scope, the ML avoidance problem). This
/// returns `Some(error)` for exactly that pattern. Called only after the body conforms to
/// the return type, so it never fires for a plain mismatch.
///
/// NOT flagged (each carries no NEW hidden-local abstraction):
///   - same base sort (`f(p: DataProvider) -> DataProvider = p`) — the return's
///     abstractness, if any, is the input `p`'s, interface-rooted;
///   - a return that is NOT a provider upcast (a concrete nominal/entity supertype, or a
///     type-variable return rooted at an op type-param — `sort_functor_of_view` is `None`);
///   - a MANIFEST spec return that binds every member (`-> DataProvider[K = String]`, or
///     `-> Stream[Elem, {}]` whose members root at the op's own type-params) — the members
///     are carried, nothing abstract escapes.
pub(super) fn abstracting_return_error(
    kb: &KnowledgeBase,
    body_ty: &Value,
    ret_ty: &Value,
    op_sym: Symbol,
) -> Option<TypeError> {
    // WI-488: a TUPLE / named_tuple return carries no sort functor, so the
    // sort-based gate below (which bails on `sort_functor_of_view == None`)
    // never inspects it — `mkBare(m: MemStore) -> (KVStore, Bool) = (m, true)`
    // used to load clean. Recurse into the components, re-applying the SAME
    // bare-vs-manifest-vs-ensures gate per component: an abstracting tuple
    // element is the §5 escape exactly as a bare top-level return is. Components
    // are aligned the SAME way conformance aligned them
    // ([`align_named_tuple_slots`] in `DATA` mode, since a return type is a
    // data tuple, not a parameter list — WI-775; passing
    // body as `actual` so each pair is `(body_component, ret_component)`).
    // WI-788: that alignment is now slot-by-slot with the names required to
    // agree, so the mispairing this comment used to warn about — a NAMED tuple
    // whose body/return field orders DIFFER (`(a: m, b: true)` vs
    // `-> (b: Bool, a: KVStore)`) letting the escape slip past a raw positional
    // zip — cannot arise: differing orders are different types and conformance
    // rejects them before this gate runs. Sharing the alignment still matters
    // for the `None` arm below.
    // The gate's own `same_sort_canonical` short-circuit spares an input-rooted /
    // equal component, and its `unbound` check spares a manifest one — so the
    // per-component reuse honours the "must NOT reject" cases without restating
    // them. Tuple components are the only gap here: a NOMINAL parameterized return
    // abstracting a type-arg (`-> Box[T = KVStore]` from a body `Box[T = MemStore]`)
    // is rejected even earlier, as an invariant-param TYPE MISMATCH.
    //
    // WI-775, on the `None` arm below: `align_named_tuple_slots` returning `None`
    // (shapes don't align) collapses through `.and_then` into `None`, which this
    // function's contract reads as "no escape found" — a fail-open. It cannot fire,
    // and the reason is worth stating because it is NOT local: return CONFORMANCE
    // runs first and is `named_tuple_compatible(actual = body, expected = ret)` —
    // the SAME alignment, SAME `DATA` mode, SAME argument order — so any pair
    // this gate could not align was already rejected. The `DATA` narrowing makes
    // the arm strictly more reachable than before, so if conformance ever widens
    // (or stops sharing this alignment), the `None` arm must be split into
    // "aligned, no escape" vs "could not align" rather than left silent.
    if named_tuple_field_types(kb, body_ty).is_some()
        && named_tuple_field_types(kb, ret_ty).is_some()
    {
        let body_fields = named_tuple_fields(kb, body_ty);
        let ret_fields = named_tuple_fields(kb, ret_ty);
        // WI-775: a RETURN type is a data tuple — align by NAME.
        return align_named_tuple_slots(kb, &body_fields, &ret_fields, TupleAlign::DATA).and_then(
            |slots| {
                aligned_pairs(&slots, &body_fields, &ret_fields)
                    .find_map(|(bc, rc)| abstracting_return_error(kb, bc, rc, op_sym))
            },
        );
    }

    let body_sort = sort_functor_of_view(kb, body_ty)?;
    let ret_sort = sort_functor_of_view(kb, ret_ty)?;
    if same_sort_canonical(kb, body_sort, ret_sort) {
        return None;
    }
    if !sort_provides_admissibly(kb, body_sort, ret_sort) {
        return None;
    }
    // WI-402 (existential half): admit this abstract `Spec` return iff the loader
    // existential-REWROTE it (`-> C ensures Spec[C, …]`) — the output dual of `requires`.
    // The operation then guarantees the result provides `Spec`, so the abstract members
    // are interface-rooted (not a hidden local) and the existential is escape-free. A bare
    // `-> Spec` return that merely carries an `ensures` was NOT rewritten (its written type
    // is a real sort, members unbound) — it stays the strict escape and is rejected below.
    if kb.existential_return_ops.contains(&op_sym) {
        return None;
    }
    // Manifest iff every one of the spec's members has a binding in the return type. A
    // binding to a concrete type OR to the op's own type-parameter (`Stream[Elem, {}]`,
    // `Elem` input-rooted) is interface-expressible; a member left wholly UNBOUND escapes
    // (a bare spec leaves them all unbound; a PARTIAL manifest leaves some unbound — §5: a
    // partial manifest still escapes).
    let unbound: Vec<String> = kb
        .type_params_of_sort(ret_sort)
        .into_iter()
        .filter(|p| extract_type_param(kb, ret_ty, p).is_none())
        .collect();
    if unbound.is_empty() {
        return None;
    }
    let ret_name = kb.qualified_name_of(ret_sort).to_owned();
    let members = unbound
        .iter()
        .map(|m| format!("'{m}'"))
        .collect::<Vec<_>>()
        .join(", ");
    Some(TypeError::Other {
        site: TypeError::here(),
        span: None,
        context: TypeErrorContext::OperationReturn {
            op_name: op_sym,
            surface: None,
        },
        expected: "an interface-expressible return (concrete, input-rooted, or an `ensures` \
                   manifest)"
            .to_owned(),
        actual: format!(
            "an abstracting return: the body provides '{ret_name}' only by an upcast that leaves \
             its member(s) {members} unbound, so the abstract member would escape its scope \
             (the avoidance problem) — bind the member(s) (`{ret_name}[…]`), return a concrete \
             type, or root them at the operation's inputs",
        ),
    })
}

/// WI-457: the WI-401 escape gate applied to the LEAVES of a branching body.
///
/// A join body (`-> KVStore = if persistent then diskStore else memStore`) widens
/// divergent concrete providers up to the bare/partial spec, so the joined
/// `body_ty` equals the declared return sort. The DIRECT [`abstracting_return_error`]
/// short-circuits on `same_sort_canonical(body_sort, ret_sort)` and so MISSES it — the
/// abstract member (`KVStore.K`) would escape via the join without an `ensures`
/// vouching for it, the gap WI-401 left for join bodies. We re-apply the gate to
/// each branch LEAF's own (typer-stamped) inferred type: a leaf that is itself a
/// provider-upcast to the bare spec is the escape, exactly as the direct
/// `-> KVStore = memStore` form is rejected.
///
/// This naturally honours WI-457's "must NOT reject" constraints, because every
/// leaf goes through the UNCHANGED [`abstracting_return_error`]: a same-sort leaf
/// (an input-rooted `KVStore` value) short-circuits on `same_sort_canonical`; a leaf under
/// a fully-manifest return has no unbound member; an `ensures`-vouched op is in
/// `existential_return_ops`. It walks the TAIL positions of the body — both arms of
/// each `if`, every `match` arm body, and a `let` BODY — so a join nested or wrapped
/// by a `let` in tail position is reached. Runs only AFTER the direct gate passes;
/// a non-branching body's sole leaf is the body itself (already judged there).
///
/// WI-468 (let-value laundering, sibling vector): a join — or even a plain
/// concrete provider — bound to a `let` VALUE and returned through the variable
/// (`let s : Spec = if … ; s`, or `let s : Spec = concreteProvider ; s`) launders
/// its abstract type via the binding's ANNOTATION. The body env binds `s` to the
/// bare-spec annotation (`check_bare_ref` reads `env.lookup_var`), so the returned
/// tail leaf `s` is genuinely typed `Spec == ret_sort` and the per-leaf gate
/// short-circuits on `same_sort_canonical` — yet the abstract member still escapes. The
/// fix is DATAFLOW: see through a returned let-bound variable to the binding's
/// VALUE node, which the typer stamped with its OWN synthesized type (`MemStore`,
/// the concrete provider), not the laundering annotation. Re-processing the value
/// node re-applies the UNCHANGED [`abstracting_return_error`] to that synthesized
/// type, so the launder is caught exactly as the direct `-> Spec = concreteProvider`
/// form is — and the value may itself be a join (`let s = if … ; s`), reached
/// because the value node is pushed back onto the walk.
///
/// This only flags a variable in TAIL (return) position — the walk reaches a
/// let-bound var only through the body's tail leaves, never through a value used
/// internally (`let s = m ; someOp(s)`, where the tail leaf is the `someOp(...)`
/// apply, not `s`). The see-through resolves each value in the scope in force
/// WHERE it was bound (an `Rc`-shared cons list), so a shadowing rebind
/// (`let x = m ; let s = x ; let x = other ; s`) resolves `s`'s `x` to `m`, not
/// `other`. The walk is ITERATIVE (an explicit stack) — op bodies nest `else if`
/// arbitrarily deep (cf. wi285_unrec), so host recursion here would risk the very
/// stack overflow the iterative typer avoids.
///
/// WI-480 (DESTRUCTURING-pattern laundering, sibling of WI-468): a destructuring
/// `let` binder (`let (s, _): (Spec, …) = (concreteProvider, …) ; s`,
/// `let boxed(s): Box = boxed(concreteProvider) ; s`) launders the same way — the
/// component var `s` is bound to its laundered annotation-component type and slips
/// `same_sort_canonical`. WI-468's `let_bound_var_name` only saw a single `Pattern::Var`, so
/// these were never tracked. The see-through is generalised to a SELECTOR PATH: a
/// destructuring binder records each destructured name → `(binding value node,
/// path)`, where the path is the tuple-position / constructor-field selectors from
/// the value down to that name. The walk threads the path — a literal tuple /
/// constructor is projected STRUCTURALLY to the concrete element node (chased on as
/// WI-468), and an opaque value (a call result) or an input parameter is projected
/// at the TYPE level (the value's own component type). In every case the UNCHANGED
/// [`abstracting_return_error`] is re-applied to the seen-through component type, so
/// its `same_sort_canonical` short-circuit remains the line between a laundered concrete
/// upcast (flagged: the value's component is a concrete provider widened at the let,
/// exactly like `-> Spec = concreteProvider`) and an interface-rooted abstract
/// (spared: an input-rooted component, or one a producer's signature already exposes
/// as the bare spec — `let (s,_) = mkBare(m)` with `mkBare -> (Spec, …)`, which is
/// consistent with the unflagged producer; tuple-component escapes at the producer
/// are a separate, producer-side concern).
pub(super) fn branch_leaf_abstracting_return_error(
    kb: &KnowledgeBase,
    body: &Rc<NodeOccurrence>,
    ret_ty: &Value,
    op_sym: Symbol,
) -> Option<TypeError> {
    // Only a branching / let body can hide a widened-provider join behind a
    // `body_ty == ret_sort` the direct gate skips; a plain body is fully judged there.
    if !matches!(
        body.as_expr(),
        Some(Expr::If { .. } | Expr::Match { .. } | Expr::Let { .. })
    ) {
        return None;
    }
    // Each entry pairs a tail node with the let-scope in force and the still-to-apply
    // SELECTOR PATH (empty for a whole value; non-empty for a destructured component).
    let mut stack: Vec<(Rc<NodeOccurrence>, Rc<LeafScope>, Vec<LeafSelector>)> =
        vec![(Rc::clone(body), Rc::new(LeafScope::Empty), Vec::new())];
    // Backstop: a malformed binding cycle (not reachable in well-typed scope, but
    // the leaf see-through follows value nodes) must terminate rather than spin.
    let mut hops = 0usize;
    const MAX_LEAF_HOPS: usize = 100_000;
    while let Some((node, scope, path)) = stack.pop() {
        match node.as_expr() {
            Some(Expr::If {
                then_branch,
                else_branch,
                ..
            }) => {
                stack.push((Rc::clone(then_branch), Rc::clone(&scope), path.clone()));
                stack.push((Rc::clone(else_branch), Rc::clone(&scope), path));
            }
            Some(Expr::Match { branches, .. }) => {
                for b in branches {
                    stack.push((Rc::clone(&b.body), Rc::clone(&scope), path.clone()));
                }
            }
            Some(Expr::Let {
                pattern,
                value,
                body,
                ..
            }) => {
                // Record each binding the pattern introduces (the value resolves in
                // the scope BEFORE this let), then descend into the BODY only — a let
                // value is not itself a tail position; it escapes solely via a
                // returned reference. A destructuring pattern yields one binding per
                // destructured name, each with its selector path into `value`.
                let mut bindings = Vec::new();
                destructure_bindings(pattern, &[], &mut bindings);
                let mut body_scope = Rc::clone(&scope);
                for (name, bpath) in bindings {
                    body_scope = Rc::new(LeafScope::Bind {
                        name,
                        base: Rc::clone(value),
                        path: bpath,
                        parent: body_scope,
                    });
                }
                stack.push((Rc::clone(body), body_scope, path));
            }
            // A literal aggregate WITH a remaining selector path: project the
            // component node STRUCTURALLY and chase it (so `(concreteProvider, …)`
            // sees the element's own stamped type, and an input-rooted element
            // `(param, …)` short-circuits on `same_sort_canonical`).
            Some(
                Expr::TupleLit { .. } | Expr::Constructor { .. } | Expr::ConstructorWithin { .. },
            ) if !path.is_empty() => {
                if let Some(child) = project_node_component(kb, &node, &path[0]) {
                    stack.push((child, scope, path[1..].to_vec()));
                } else if let Some(e) = gate_component_type(kb, &node, &path, ret_ty, op_sym) {
                    // A structural mismatch (pattern/value arity or named/positional
                    // form differs) — fall back to projecting the component TYPE.
                    return Some(e);
                }
            }
            // A tail leaf (a bare value reference, an opaque call, a literal value).
            _ => {
                // WI-468/480: see through a returned let-bound variable to its
                // binding (value node + path), resolving in the scope where it was
                // bound. A free var (param / outer binder) is not in scope here →
                // fall through to its own stamped type (path empty) or a TYPE
                // projection of it (path non-empty, an input-rooted component).
                if let Some(name) = leaf_var_ref(&node) {
                    if let Some((base, base_path, base_scope)) = scope.resolve(kb, name) {
                        hops += 1;
                        if hops <= MAX_LEAF_HOPS {
                            // The variable denotes `base` projected by `base_path`;
                            // any outer projection applies on top of that.
                            let mut combined = base_path;
                            combined.extend(path);
                            stack.push((base, base_scope, combined));
                            continue;
                        }
                    }
                }
                if path.is_empty() {
                    // The whole value is returned: re-apply the gate to its own type.
                    if let Some(leaf_ty) = node.inferred_type() {
                        if let Some(e) = abstracting_return_error(kb, &leaf_ty, ret_ty, op_sym) {
                            return Some(e);
                        }
                    }
                } else if let Some(e) = gate_component_type(kb, &node, &path, ret_ty, op_sym) {
                    // An opaque value (a call) or an input parameter with a remaining
                    // projection — no element node to see through, so gate the
                    // component TYPE (the value's own, NOT the laundering annotation).
                    return Some(e);
                }
            }
        }
    }
    None
}

/// WI-480: re-apply [`abstracting_return_error`] to a node's component TYPE — its
/// stamped `inferred_type` projected along `path` (tuple positions / constructor
/// fields). Used where no structural element node exists to see through: an opaque
/// call result, or an input parameter. Yields `None` when the type can't be
/// projected (a non-tuple/entity carrier) — conservatively unflagged.
fn gate_component_type(
    kb: &KnowledgeBase,
    node: &Rc<NodeOccurrence>,
    path: &[LeafSelector],
    ret_ty: &Value,
    op_sym: Symbol,
) -> Option<TypeError> {
    let mut ty = node.inferred_type()?;
    for sel in path {
        ty = project_type_component(kb, &ty, sel)?;
    }
    abstracting_return_error(kb, &ty, ret_ty, op_sym)
}

/// WI-468/480: the let-binding scope threaded through
/// [`branch_leaf_abstracting_return_error`]'s leaf walk — an `Rc`-shared cons list
/// mapping a let-bound variable to its binding's VALUE node plus the SELECTOR PATH
/// from that value down to the variable (empty for a single `Pattern::Var`,
/// non-empty for a destructured component — WI-480). Immutable so each branch push
/// is O(1). A binding's `parent` is the scope in force BEFORE that `let`, which is
/// also the scope its value resolves in — so a reference to a rebound name sees the
/// value it was actually bound to, not a later shadow.
pub(super) enum LeafScope {
    Empty,
    Bind {
        name: Symbol,
        base: Rc<NodeOccurrence>,
        path: Vec<LeafSelector>,
        parent: Rc<LeafScope>,
    },
}

impl LeafScope {
    /// Resolve a tail-position variable to `(base value node, selector path, the
    /// scope that base resolves in)`. `None` for a free variable (a parameter or
    /// outer binder), whose own stamped type is then read directly.
    pub(super) fn resolve(
        self: &Rc<Self>,
        kb: &KnowledgeBase,
        name: Symbol,
    ) -> Option<(Rc<NodeOccurrence>, Vec<LeafSelector>, Rc<LeafScope>)> {
        let mut cur = self;
        loop {
            match cur.as_ref() {
                LeafScope::Empty => return None,
                LeafScope::Bind {
                    name: n,
                    base,
                    path,
                    parent,
                } => {
                    if same_label(kb, *n, name) {
                        return Some((Rc::clone(base), path.clone(), Rc::clone(parent)));
                    }
                    cur = parent;
                }
            }
        }
    }
}

/// WI-480: a selector into a destructured value — a tuple position / constructor
/// positional field (`Pos`) or a named tuple element / constructor field (`Named`).
#[derive(Clone)]
pub(super) enum LeafSelector {
    Pos(usize),
    Named(Symbol),
}

/// WI-480: decompose a `let` pattern into the (name, selector-path) bindings it
/// introduces, recursively. A `Pattern::Var` is a single binding at the current
/// path; a tuple / constructor pattern recurses into each sub-pattern with the
/// position / field selector appended. Wildcard / literal patterns bind nothing.
fn destructure_bindings(
    pattern: &Rc<NodeOccurrence>,
    prefix: &[LeafSelector],
    out: &mut Vec<(Symbol, Vec<LeafSelector>)>,
) {
    match pattern.as_pattern() {
        Some(Pattern::Var { name, .. }) => out.push((*name, prefix.to_vec())),
        // WI-803: `Pos(i)` stays correct even for a LABELLED binder list. The
        // selector is resolved against the pattern's expected TYPE
        // (`project_type_component`), and in that type component `i` IS
        // `labels[i]` — the labels were read off it in declaration order. `Pos(i)`
        // and `Named(labels[i])` therefore name the same component here; only the
        // RUNTIME value can be permuted, and this walk never looks at one.
        Some(Pattern::Tuple { positional, .. }) => {
            for (i, sub) in positional.iter().enumerate() {
                let mut p = prefix.to_vec();
                p.push(LeafSelector::Pos(i));
                destructure_bindings(sub, &p, out);
            }
        }
        Some(Pattern::Constructor {
            pos_args,
            named_args,
            ..
        }) => {
            for (i, sub) in pos_args.iter().enumerate() {
                let mut p = prefix.to_vec();
                p.push(LeafSelector::Pos(i));
                destructure_bindings(sub, &p, out);
            }
            for (sym, sub) in named_args {
                let mut p = prefix.to_vec();
                p.push(LeafSelector::Named(*sym));
                destructure_bindings(sub, &p, out);
            }
        }
        _ => {} // Wildcard, Literal — bind nothing
    }
}

/// WI-480: structurally project one selector from a LITERAL aggregate value node
/// (tuple / constructor). A constructor maps `Pos`↔`Named` through the entity's
/// declared field order, so a positional pattern over a named value (or vice versa)
/// still sees through. `None` when the selector doesn't resolve (caller falls back
/// to a TYPE projection).
fn project_node_component(
    kb: &KnowledgeBase,
    node: &Rc<NodeOccurrence>,
    sel: &LeafSelector,
) -> Option<Rc<NodeOccurrence>> {
    match node.as_expr()? {
        Expr::TupleLit { positional, named } => match sel {
            LeafSelector::Pos(i) => positional.get(*i).map(Rc::clone),
            LeafSelector::Named(s) => named
                .iter()
                .find(|(k, _)| same_label(kb, *k, *s))
                .map(|(_, v)| Rc::clone(v)),
        },
        Expr::Constructor {
            name,
            pos_args,
            named_args,
            ..
        }
        | Expr::ConstructorWithin {
            name,
            pos_args,
            named_args,
            ..
        } => project_constructor_arg(kb, *name, pos_args, named_args, sel),
        _ => None,
    }
}

/// One constructor argument by selector, bridging positional↔named via the entity's
/// declared field order. A surface tuple literal `(a, b)` is a `TupleLiteral`
/// pseudo-constructor with NO registered field types and `_1`/`_2`-keyed named args
/// (see `convert.rs` `push_tuple_literal`), so a `Pos(i)` selector over it maps to
/// the synthesized `_{i+1}` field name — letting a tuple element that is itself a
/// laundered let-var (`let x: Spec = m ; let (s,_) = (x, …) ; s`) be chased
/// structurally to its value, which a TYPE projection (reading `x`'s laundered
/// stamped type) would miss.
fn project_constructor_arg(
    kb: &KnowledgeBase,
    ctor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    sel: &LeafSelector,
) -> Option<Rc<NodeOccurrence>> {
    match sel {
        LeafSelector::Pos(i) => {
            if let Some(a) = pos_args.get(*i) {
                return Some(Rc::clone(a));
            }
            // No positional arg at `i`: map index → field name and look up the named
            // arg. A real entity uses its declared field order; a tuple-literal
            // pseudo-constructor (no registered fields) uses the `_{i+1}` tuple key.
            match kb.entity_field_types(ctor).and_then(|f| f.get(*i)) {
                Some((fname, _)) => named_args
                    .iter()
                    .find(|(k, _)| same_label(kb, *k, *fname))
                    .map(|(_, v)| Rc::clone(v)),
                None => named_args
                    .iter()
                    .find(|(k, _)| is_positional_label_at(kb.local_name_of(*k), *i))
                    .map(|(_, v)| Rc::clone(v)),
            }
        }
        LeafSelector::Named(s) => {
            if let Some((_, a)) = named_args.iter().find(|(k, _)| same_label(kb, *k, *s)) {
                return Some(Rc::clone(a));
            }
            let idx = kb
                .entity_field_types(ctor)?
                .iter()
                .position(|(k, _)| same_label(kb, *k, *s))?;
            pos_args.get(idx).map(Rc::clone)
        }
    }
}

/// WI-480: project one selector from a tuple / entity TYPE (carrier-agnostic). Used
/// when no structural value node exists (an opaque call result, an input param). A
/// tuple type indexes its named-tuple components in field order (matching how
/// [`bind_and_label_pattern`] binds the destructured var's type); a `Named`
/// selector matches by field name. `None` for a non-tuple carrier.
fn project_type_component(kb: &KnowledgeBase, ty: &Value, sel: &LeafSelector) -> Option<Value> {
    match sel {
        LeafSelector::Pos(i) => named_tuple_field_types(kb, ty)?.get(*i).cloned(),
        LeafSelector::Named(s) => match extract_type(kb, ty) {
            TypeExtractor::NamedTuple(fields) => fields
                .into_iter()
                .find(|(k, _)| same_label(kb, *k, *s))
                .map(|(_, v)| v),
            _ => None,
        },
    }
}

/// The variable a tail leaf references, if it is a bare value reference (the forms
/// `value_references` enumerates: `Ident` / `Ref` / `VarRef`).
fn leaf_var_ref(node: &Rc<NodeOccurrence>) -> Option<Symbol> {
    match node.as_expr() {
        Some(Expr::Ident(s)) | Some(Expr::Ref(s)) => Some(*s),
        Some(Expr::VarRef { name }) => Some(*name),
        _ => None,
    }
}

//! Type unification (`unify_types`) over views, terms and values, and deep walks of
//! resolved types.

use super::*;

/// Unify two types **carrier-agnostically** (WI-342 P3): each side is any
/// [`TermView`] — a `TermId` (wrap in [`TermIdView`]) or a `Value`-carried type
/// (a `Value::Node` occurrence from `make_*_occ`, a `Value::Var`, …). This is
/// the migrated entry point — there is no `TermId`-only facade; callers holding
/// a `TermId` pass `&TermIdView(t)`.
///
/// Each side is resolved through the substitution to a `Value` — the same
/// carrier-agnostic representation [`Substitution`] already stores bindings in
/// (`Value::Term` is the hash-consed carrier; `Value::Node` an occurrence type;
/// `Value::Var` a logic var). This slice (P3) carries the var-bind + `denoted`
/// paths; the structural arms (`unify_parameterized`/`unify_arrow`/rows) are
/// still `TermId`-only and are reached only when BOTH sides resolve to
/// `Value::Term` — full structural unification of `Value`-carried
/// arrows/parameterized/rows is P4 (slice b).
///
/// WI-307 v1a: `kb` is `&mut` for fresh tail-variable allocation in the row
/// arms; all type-checker call sites already hold `&mut KnowledgeBase`.
/// WI-400 — the ζ (receiver σ-equality) decision for an expression-carried projection
/// at the type-relation boundary, shared by `unify_types` and the `types_compatible`
/// (subtype) dispatchers so the two relations treat a neutral identically (the design's
/// "refuse a bare projection symmetrically").
///
/// A projection that reaches a type relation is a NEUTRAL: δ-grounding already ran at the
/// env-bearing site (operation call / `let` / operation body-binding) and could not make
/// the member manifest (an abstract receiver), so the rigid `ExprCarried` survived. Returns
/// `Some(verdict)` when at least one side is an `ExprCarried` head, `None` when neither is
/// (the caller continues its ordinary structural dispatch). The verdict:
///
///   - **both neutral** — equal iff they project the SAME member off σ-EQUAL receivers: a
///     structural CHECK, never a binding. `ExprCarried` is a NON-INJECTIVE head
///     (`peek(a).T` and `peek(b).T` may both be `Int64` without `a = b`), so the relation
///     must NOT decompose `p.M =?= q.M` into `p =?= q`. The base scope compares receivers
///     structurally (eager let-alias canonicalization at the formation site is the deferred
///     increment that makes `let y = z ⟹ y.M ≡ z.M`; the union-find-over-σ generality is
///     the deferred flexible / rule-body case);
///   - **one neutral, one concrete** — a rigid abstract type is neither sub- nor
///     super-type of a concrete type, so refused (`expected String, got s.cell.T`). The
///     inference wildcards (`type_var` / `nothing`) are handled by the callers BEFORE this,
///     so a neutral still flows into an unconstrained var for inference.
///
/// Design: path-dependent-types.md §4 (ζ/δ/η), §4.1.
pub(super) fn expr_carried_zeta<A: TermView, B: TermView>(
    kb: &KnowledgeBase,
    a: &A,
    b: &B,
) -> Option<bool> {
    // WI-428: a `RigidTypeProjection` (`P.Key`, the type-keyed neutral) is the second
    // neutral kind, treated exactly like `ExprCarried` at the relation boundary: two
    // rigid projections are equal iff same member off the same subject under the same
    // declaring sort (a structural CHECK — non-injective, never decomposed into a
    // subject unification); a neutral never equals a concrete type; the two neutral
    // KINDS never equal each other (an expression-keyed and a type-keyed neutral have
    // no conversion in the base scope — δ-normalization across kinds is the recorded
    // §5.3 convergence).
    let a_neutral = matches!(
        type_head(kb, a),
        TypeHead::ExprCarried | TypeHead::RigidProjection
    );
    let b_neutral = matches!(
        type_head(kb, b),
        TypeHead::ExprCarried | TypeHead::RigidProjection
    );
    if !a_neutral && !b_neutral {
        return None;
    }
    if a_neutral && b_neutral {
        match (extract_type(kb, a), extract_type(kb, b)) {
            (
                TypeExtractor::ExprCarried {
                    value: va,
                    member: ma,
                },
                TypeExtractor::ExprCarried {
                    value: vb,
                    member: mb,
                },
            ) => {
                return Some(same_qname(kb, ma, mb) && views_structurally_equal(kb, &va, &vb));
            }
            (
                TypeExtractor::RigidTypeProjection {
                    sort: sa,
                    subject: va,
                    member: ma,
                },
                TypeExtractor::RigidTypeProjection {
                    sort: sb,
                    subject: vb,
                    member: mb,
                },
            ) => {
                // Subject identity via [`SubjectKey`] (the param's alias-var id), NOT
                // raw term identity: two occurrences of one projection may carry Refs
                // to DIFFERENT symbol registrations of the same param (the inner
                // self-named `ns.W.P.P` vs the outer `ns.W.P`).
                let subjects_eq = match (&va, &vb) {
                    (Value::Term { id: ta, .. }, Value::Term { id: tb, .. }) => {
                        match (subject_key_of_term(kb, *ta), subject_key_of_term(kb, *tb)) {
                            (Some(ka), Some(kb2)) => subject_keys_equal(kb, ka, kb2),
                            _ => views_structurally_equal(kb, &va, &vb),
                        }
                    }
                    _ => views_structurally_equal(kb, &va, &vb),
                };
                return Some(
                    same_qname(kb, ma, mb) && same_sort_canonical(kb, sa, sb) && subjects_eq,
                );
            }
            _ => return Some(false),
        }
    }
    Some(false)
}

/// **WHAT SURVIVES A `false` — the rule ~16 discarding callers depend on** (WI-20260904-60143).
///
/// This relation does NOT roll back. Everything it bound on the way down stays in `subst`
/// whatever it answers, and that is DELIBERATE: the argument-unification sites discard the
/// boolean by design (unify is EQUALITY, argument passing is SUBTYPING plus conversions, so a
/// unify-`false` must not by itself reject), and what they take from the call is the
/// SUBSTITUTION. [`unify_arrow_function_view`]'s doc states it for its own arm — "its job is
/// to BIND" — and it is the whole relation's contract. A rollback was BUILT AND MEASURED on
/// this tree and costs four rows, each a groundness-gated refusal reached *by* the partial
/// binding: `wi1084_arrow_function_unify_tests::the_two_spellings_of_one_slot_answer_alike`,
/// `wi1078_unbound_return_var_test::the_tie_survives_the_opening`,
/// `wi1082_self_return_tie_test::a_bodyless_member_cannot_launder_either`, and
/// `wi1083_polytype_test::a_result_type_disagreement_is_refused`. The variable pinned by an
/// AGREEING component is what makes the disagreeing one read ground and therefore comparable.
///
/// **SO NO AUTHORIAL ORDER MAY DECIDE WHICH OF THEM SURVIVE.** That is the whole of the fix,
/// and it is narrower than "descend totally". A list whose slot order is the AUTHOR'S — a
/// parameterized type's bindings (`Pair[A = …, B = …]` or `Pair[B = …, A = …]`), a tuple's
/// fields, an arrow's parameter LIST (in the `arrow` spelling; the `Function[A, B, E]` one
/// does not unify a multi-parameter list at all — see [`unify_arrow_function_view`]) —
/// unifies EVERY slot and returns their CONJUNCTION, so
/// what a `false` leaves behind is "every slot that agreed" and not "the slots written before
/// the one that did not" ([`unify_parameterized_view`], [`unify_named_tuple_as`];
/// `wi_60143_total_unify_descent_test` drives one back-out per loop). A later slot cannot
/// un-say an earlier one's disagreement, so the early exit only ever decided which half of σ
/// a discarding caller got to read.
///
/// An arrow's `param` / `result` / `effects` are NOT such a list — their order is fixed by the
/// FORM, so stopping at the first disagreeing part is already a function of the two types
/// alone. Those keep the short-circuit, and [`unify_arrow_view`] carries the measurement that
/// says they must: continuing past a disagreeing `param` fills unwritten carrier params from
/// a unify that failed, and turns a refusal into a clean load. A HEAD mismatch — differing
/// functors, differing arity, a missing component — exits hard for the same reason: those are
/// unrelatable shapes, not disagreeing slots.
///
/// **WHAT A CALLER MAY THEREFORE ASSUME — AND THE BINDINGS ARE NOT ALL OF IT.** On `false`,
/// σ holds what agreed: evidence about the argument, not an instantiation of the call, and now
/// the same evidence however the disagreeing type was spelled. On `true`, σ is a unifier
/// EXCEPT through [`unify_parameterized_with_sort_ref`], which binds the sort's canonical
/// param vars with an UNWALKED `Substitution::bind` and then answers `true` unconditionally —
/// so a conflicting re-bind there leaves `true` beside a recorded conflict.
///
/// That is the second channel this relation writes and neither verdict resets: the sticky
/// `contradiction` flag and `contradiction_details`, set by `Substitution::bind` /
/// `bind_value` on a conflicting re-bind. It is NOT inert — [`enforce_member_tie`] reads
/// `contradiction_details` and renders an `OperationTypeParams` refusal from it. Unifying
/// every slot of an author-ordered list (above) strictly widens the set of slots that can
/// reach that arm, since slots after the first disagreeing one now descend. NOT DRIVEN:
/// /code-review built two programs for it (a `Box[T]` member given a `Pair[A, B]`, with a
/// plain disagreement and with a `provides`-based subtype in slot A) and the per-argument
/// conformance check refused first in both, so [`enforce_member_tie`] was never reached and
/// no row of `wi_60143_total_unify_descent_test` covers this channel. Recorded as an
/// unmeasured widening rather than a proven one — but a caller reasoning from the paragraph
/// above must know σ carries more than bindings.
///
/// A caller that reads σ as an ANSWER
/// and must not absorb a failed unify's evidence takes the probe-commit instead: `let mut
/// probe = subst.clone(); if unify_types(kb, &mut probe, ..) { *subst = probe; }`
/// (`Substitution::clone` is O(1) — `imbl`, WI-569). SIX sites do exactly that today and say
/// why at each: [`hint_instantiation_subst`], the `lacks`-conflict probe, the
/// contradiction-replay scratch, the operation-return check, and the two row-matching loops
/// (`pair_present_labels` / `cover_present_labels`), whose restore is a BACKTRACK between
/// candidate labels rather than a rollback of the verdict.
pub fn unify_types<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
) -> bool {
    let a = walk_view(kb, subst, a);
    let b = walk_view(kb, subst, b);

    // Identity fast-path. A hash-consed `TermId` carrier has O(1) structural eq
    // (shared id ⇒ equal). WI-470: an occurrence-carried type (now the primary
    // arrow/row form) recovers a cheap fast-path via `Rc::ptr_eq` — two slots
    // holding the SAME occurrence are trivially unifiable. This catches shared
    // spines (the common case: one inferred type threaded to two sites) without
    // materializing; structurally-distinct-but-equal Node arrows fall through to
    // the carrier-agnostic structural arms below (correct, just not O(1)).
    match (&a, &b) {
        (Value::Term { id: x, .. }, Value::Term { id: y, .. }) if x == y => return true,
        (Value::Node(x), Value::Node(y)) if Rc::ptr_eq(x, y) => return true,
        _ => {}
    }

    // Var arms — a logic var may be a hash-consed `Term::Var(Global)` or a
    // `Value::Var(Global)`; bind the other side by its carrier.
    if let Some(vid) = resolved_var(kb, &a) {
        return bind_resolved(kb, subst, vid, b);
    }
    if let Some(vid) = resolved_var(kb, &b) {
        return bind_resolved(kb, subst, vid, a);
    }

    // WI-399: an un-eliminated expression-carried projection (`s.T` / `s.cell.T`)
    // must NEVER reach unification. Every projection is discharged at its typing
    // SITE — where the env resolves the receiver's type: an operation call
    // (`check_apply_iter`, via `param_to_arg_type`) or a `let` annotation
    // (`visit_type`, via the env's `var_bindings`). A projection head that survives
    // to here was reached from a site that does NOT yet eliminate (a rule body, a
    // higher-order apply) — so the receiver's type is not known at unification. Refuse
    // EXPLICITLY here rather than rely on the structural fallback below, which would
    // reach `types_compatible`'s `_ => false` only after treating the opaque
    // `ExprCarried` head as a plain term — making the "no un-eliminated projection
    // passes a type relation" invariant legible at the unify boundary the WI-399
    // design names. Placed AFTER the var arms so a var still binds (mirroring how the
    // subtype sibling `types_compatible` lets `type_var`/`nothing` win first): the two
    // relations refuse a bare projection symmetrically — there it is `_ => false` by
    // construction, here it is this guard.
    // WI-400 (ζ — the σ-equality arm, replacing the WI-399 safety-net guard).
    if let Some(verdict) = expr_carried_zeta(kb, &a, &b) {
        return verdict;
    }

    match (&a, &b) {
        // Both hash-consed → today's `TermId` structural dispatch. This is the
        // hot path (no producer mints `Value`-carried types yet) and stays free
        // of the carrier-agnostic `denoted` check: two `TermId` `denoted`s with
        // distinct refs have distinct TermIds (→ `false` via the dispatch) and
        // equal ones share a TermId (→ the identity fast-path above), so the
        // `denoted` Ref-compare is only needed when hash-cons identity is lost
        // (a `Value` carrier on at least one side).
        (Value::Term { id: x, .. }, Value::Term { id: y, .. }) => {
            unify_term_dispatch(kb, subst, *x, *y)
        }
        // At least one `Value` carrier (hash-cons identity is lost). Dispatch
        // structurally through the carrier-agnostic [`TermView`] arms (WI-342
        // P4): a `Value`-carried `denoted` / `parameterized` unifies against its
        // ground twin (cross-carrier) or another `Value` carrier.
        //
        // "Forms not yet wired return `false` (sound: refuses rather than
        // mis-unifies)" is what this said, and it is STALE and teaches the wrong
        // reading. An unwired form is a SILENT SKIP, not a sound refusal — it is
        // indistinguishable from a genuine mismatch at every reader. The arms are
        // now measured to be in step with the term dispatch, and the `_` arm of
        // `types_compatible_view_structural` asserts loudly when a SAME-FORM pair
        // reaches it, which is the only shape an omission can take.
        _ => unify_view_structural(kb, subst, &a, &b),
    }
}

/// WI-342 P4: carrier-agnostic structural dispatch — the [`TermView`] analog of
/// [`unify_term_dispatch`], reached from [`unify_types`] when at least one side
/// is a non-hash-consed carrier (a `Value::Node`). Reads each side's functor
/// name and immediate children through [`TermView`] and recurses via the generic
/// [`unify_types`], so a child of any carrier unifies uniformly.
///
/// This is deliberately a *separate* dispatch from [`unify_term_dispatch`]
/// rather than a single generic one folded over both arms: the `(Term, Term)`
/// path is the hot, heavily row-tested path (WI-307/328) and stays byte-
/// identical. Consolidating the two dispatches once the row machinery is fully
/// carrier-agnostic (P4-B) is a follow-up.
fn unify_view_structural<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
) -> bool {
    // WI-361: dispatch on the CANONICAL type tag (`type_head`), not the raw
    // functor — a flipped parameterized carrier / term-backed `Fn{S, named}`
    // reports its base sort as the raw functor, so raw-functor dispatch would miss
    // the `parameterized` arm (and the `denoted` alpha-equivalence path beneath it).
    // WI-342: every arm of `unify_term_dispatch` has a carrier-agnostic peer here,
    // so the dispatch is wired natively for both carriers with no re-ground bridge.
    // The arms below mirror `unify_term_dispatch`'s exactly (same functor pairs,
    // same helpers); the final `_` mirrors its `_ => types_compatible` fallback.
    match (
        type_dispatch_name_view(kb, a),
        type_dispatch_name_view(kb, b),
    ) {
        (Some("denoted"), Some("denoted")) => unify_denoted_view(kb, a, b),
        (Some("parameterized"), Some("parameterized")) => unify_parameterized_view(kb, subst, a, b),
        (Some("parameterized"), Some("sort_ref")) => {
            unify_parameterized_with_sort_ref(kb, subst, a, b)
        }
        (Some("sort_ref"), Some("parameterized")) => {
            unify_parameterized_with_sort_ref(kb, subst, b, a)
        }
        (Some("arrow"), Some("arrow")) => unify_arrow_view(kb, subst, a, b),
        // WI-1084: the two spellings of ONE type — see [`unify_arrow_function_view`]. Without
        // these two arms the pair fell to the `_ =>` subtype fallback below, which decomposes
        // but cannot BIND, so unification through a `Function[…]`-typed slot learned nothing.
        (Some("arrow"), Some("parameterized")) => unify_arrow_function_view(kb, subst, a, b),
        (Some("parameterized"), Some("arrow")) => unify_arrow_function_view(kb, subst, b, a),
        (Some("named_tuple"), Some("named_tuple")) => unify_named_tuple(kb, subst, a, b),
        // WI-441 (was the weaker WI-320 structural unify): a top-level row
        // pair takes the FULL row algorithm — the structural inner-unify was
        // order-sensitive over `merge`, rejecting equal rows written in
        // different binding orders (the two-row carriers' `{ES, EF}`).
        (Some("effects_rows"), Some("effects_rows")) => unify_effect_rows(kb, subst, a, b),
        // Mirrors `unify_term_dispatch`'s `_ => types_compatible(...)` — a unify of
        // any other (form-mismatched) pair falls back to the subtype check, which is
        // itself carrier-agnostic (no re-ground). WI-441: a pair with ONE
        // row-shaped side (a bare `open(?ρ)` row-var binding vs a rigid row
        // var; an `effects_rows` vs a bare expression) is a ROW comparison —
        // the generic fallback cannot equate `?ρ` with `open(?ρ)`.
        _ => {
            if value_is_row_shaped(kb, a) || value_is_row_shaped(kb, b) {
                unify_effect_rows(kb, subst, a, b)
            } else {
                types_compatible(kb, subst, a, b)
            }
        }
    }
}

/// WI-342: the sole `parameterized` unification, carrier-agnostic over
/// [`TermView`] — both the `TermId` dispatch (via [`TermIdView`]) and the
/// `Value` carrier route here. Bases unify via the generic [`unify_types`];
/// bindings are matched by param name (a-side bindings present on the b-side
/// must unify; b-only bindings are width-ignored).
/// The base of a parameterized type as a unifiable term (WI-453). A type-param base
/// — the marked carrier `F` of a `sort Spec[F[T]]`, var-backed by WI-452's
/// `SortAlias` — resolves to its backing `Var` so the parameterized unify can FILL
/// it (`F[T=A] ≟ Option[T=X]` ⟹ `F := Option` at a use-site; `F → skolem` at a
/// def-site, so `F[T=A] ≟ F[T=B]` stays a rigid decomposition). A concrete base
/// (`Option`, `List`) has no var-target SortAlias and stays `Ref(base)`. Only
/// reached when the two bases DIFFER (same-functor unify never needs the alias scan).
pub(super) fn parameterized_base_term(kb: &mut KnowledgeBase, base: Symbol) -> TermId {
    let var = resolve_sort_alias(kb, base)
        .filter(|t| matches!(kb.get_term(*t), Term::Var(Var::Global(_))));
    var.unwrap_or_else(|| kb.alloc(Term::Ref(base)))
}

/// How [`binding_for_param`] compares two parameterized types' binding KEYS — chosen from
/// the two bases via [`BindingKeyMatch::for_bases`] rather than passed as a bare flag,
/// because the two modes have opposite failure modes and nothing else distinguishes them.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum BindingKeyMatch {
    /// Both types are instances of ONE sort: match by LABEL. Within a single sort, short
    /// name IS the canonical param identity (a sort's params have distinct labels), so
    /// [`same_label`] is exact — and it is required, because the two producers key the same
    /// slot differently (see [`binding_for_param`]).
    Label,
    /// The bases are DIFFERENT sorts: do not add a label match. Both callers' base checks
    /// deliberately accept different bases related by provider admissibility (`List provides
    /// Stream`, WI-344), and pairing a bare `T` with a foreign sort's QUALIFIED `Stream.T`
    /// would be a guess; cross-sort callers translate through an explicitly aligned provider
    /// view instead.
    ///
    /// This mode is NOT a barrier between two sorts' slots, and must not be read as one.
    /// Identity is tried first regardless of mode, and a WRITTEN key is `reintern(p.last())`
    /// — the bare symbol `T`, ONE globally-interned symbol shared by every sort. So two
    /// different sorts' bare-written `T` slots already pair by raw identity, exactly as they
    /// did before WI-764. Measured over the `wi_tests` corpus: of 47,432 calls, 19,463 have
    /// different-sort bases and 16,681 of those share an exact key symbol — chiefly
    /// `MappedStream`/`Stream` and `List`/`Stream` on `T`. That pairing is CORRECT there
    /// only by convention: `stdlib/anthill/prelude/combinators.anthill` deliberately names
    /// each carrier's params to match `Stream`'s. What this mode withholds is the
    /// *additional* bare↔foreign-qualified match, nothing more.
    ///
    /// And nothing catches a misuse at runtime: [`same_label`]'s `debug_assert` fires only
    /// when BOTH names are dotted, while the characteristic input here is a bare key whose
    /// qualified name is just `"T"`. Do not weaken this gate expecting CI to notice.
    Identity,
}

impl BindingKeyMatch {
    pub(super) fn for_bases(kb: &KnowledgeBase, a_base: Symbol, b_base: Symbol) -> Self {
        if same_sort_canonical(kb, a_base, b_base) {
            BindingKeyMatch::Label
        } else {
            BindingKeyMatch::Identity
        }
    }
}

/// WI-726 / WI-764 — look a parameterized type's binding up by its PARAM KEY.
///
/// The two producers key the SAME slot with DIFFERENT symbols: a `Relation[T = (name,
/// age)]` VALUE (built via [`assemble_relation_type`] → [`sort_type_params_as_pairs`]) keys
/// `T` with the sort's CANONICAL param symbol `anthill.prelude.Relation.T`, while a WRITTEN
/// signature type `Relation[T = L]` keys it with a BARE last-segment `T` (the loader lowers
/// via `reintern(p.last())`). Raw `p == param` misses that pair, so the slot does not match
/// and the two sides disagree about a type they both describe.
///
/// IDENTITY IS TRIED FIRST across the whole slice, and a label match only on miss. That
/// keeps the common case at one integer compare per binding (identity is what nearly every
/// call resolves on), keeps [`same_label`] — and its `debug_assert` — off the typer's hot
/// conformance path, and makes an exact key win over a merely same-labelled one should a
/// bindings list ever carry both spellings of one slot.
///
/// Shared by the UNIFY ([`unify_parameterized_view`]) and SUBTYPE
/// ([`parameterized_compatible_view`]) directions: WI-726 fixed this in unify only, and the
/// subtype twin kept raw identity — which is exactly the WI-764 bug (a written `Relation[T
/// = .., E = ..]` op-return annotation did not conform against the same relation cited from
/// a rule). Those two now share one rule.
///
/// WI-768 enrolled DISPATCH into this same rule — `match_candidate_against_goal`'s arm-(2)
/// binding lookup and `values_structurally_equal`'s nested one. Before that, dispatch and
/// the typer DISAGREED about the canonical-vs-bare pair: a spec-op call on a rule citation
/// type-checked (WI-764 taught conformance to accept it) and then silently failed to
/// dispatch — the provider was dropped, so the call was never pinned to it.
///
/// The `specificity` bump beside that lookup meant enrolling could move overload ORDERING
/// as well as acceptance, so WI-764 deferred it. MEASURED rather than assumed: over the
/// `wi_tests` corpus all 116 arm-(2) binding lookups already resolved on RAW identity
/// (`raw=true label=true`, every one), so no candidate changes from dropped to kept and
/// every candidate's specificity score is unchanged. The ordering effect is nil for
/// existing code; it appears only for the newly-accepted pair, where the alternative was
/// no candidate at all.
///
/// WI-843 RETIRED THE SECOND HALF OF THAT ARGUMENT. It used to read "two providers of
/// one spec for one carrier — the shape where a changed score could flip a winner — is
/// separately refused as an ambiguous witness". That refusal is gone: 058 tier 3 lets
/// two NAMEABLE providers coexist, so such a pair now reaches `pick_most_specific` and
/// the score DOES decide it (measured under WI-843: a ground `Monoid[T = List[T =
/// Int64]]` beside a parametric `Monoid[T = List[T = E]]` loads and answers the ground
/// one). The MEASUREMENT above still stands on its own — every existing arm-(2) lookup
/// resolved on raw identity, so no existing candidate's score moved — but the appeal to
/// a load-time backstop no longer does.
///
/// WI-769 enrolled the LUB/GLB lattice (`combine_parameterized_same_base`): its raw-identity
/// key miss silently dropped the WHOLE schema (bare base sort for the LUB, `nothing` for the
/// GLB), which a downstream check then accepted against any parameterization (a bare `S`
/// conforms to `S[anything]`). Its base guard is canonical for the same reason. NOTE the
/// ticket's "binding matcher executed by ZERO tests" measurement was an artifact of scoping
/// to the `wi_tests` binary: at workspace scope the WI-464 lattice unit tests drive the
/// matcher directly (4 hits, all bare/bare keys — which is why the miss stayed invisible).
///
/// WI-825 enrolled the σ-cover verdict (`sigma_pair_precise`'s both-compound arm): the
/// recursive per-argument named-binding lookup routes through this rule, its `key_match`
/// derived once from `for_bases` (which is `Label` under the same-base gate the arm already
/// applies), so the σ-structural compound comparison cannot drift from the unify/subtype ones.
///
/// WI-826 enrolled the requirement-cover KEY ITERATION — `supply_covers_demanded_keys`
/// (both cover walks: `entries_cover` and `requires_entry_covers_goal`, the latter's
/// second leg too). It had been a hand-rolled `find(same_label)` inside `entries_cover`,
/// i.e. label-ONLY, and consolidating the two walks was about to give that spelling a
/// second reader. `Label` is `for_bases`' verdict under the same-spec gate every caller
/// applies, so enrolling only ADDS the identity-first pass.
///
/// STILL NOT enrolled — one site. Enumerated deliberately: WI-726 and WI-764
/// diverged precisely because `0f31beb2` had consolidated that pair *to keep them in
/// lockstep* and the doc then claimed a lockstep that no longer held. Keep this list
/// honest, or the rule drifts again.
///
/// * `goals_equal` — cycle detection over two `SortGoal`s. This one does NOT carry the
///   WI-768 bug (it already matches by `same_label`, so it bridges the bare-vs-canonical
///   pair), but it is a fourth hand-rolled spelling of this rule and DIFFERS from it: it is
///   label-ONLY, so it lacks the identity-first pass that makes an exact key beat a merely
///   same-labelled one, and it puts `same_label`'s `debug_assert` on the path
///   unconditionally instead of only after an identity miss. Its `spec_sort` guard already
///   establishes `Label`, so enrolling it is `binding_for_param(kb, &b.bindings, *k,
///   BindingKeyMatch::Label)` — left alone here only because changing its tie-breaking is a
///   behavior change outside WI-768's demonstrated defect.
///
/// WI-860 enrolled the DEFAULT-ROW carrier overlap ([`carrier_views_overlap`], 058
/// §3.6's `one_default`): a same-family per-parameter walk of exactly the
/// `sigma_pair_precise` shape, so `Label` is again `for_bases`' verdict under the base
/// gate it already applies and enrolling only adds the identity-first pass. It lives in
/// this module rather than in `kb::defaults` so it could.
///
/// Related, kept in situ: `matches_variance_fact` bridges a variance fact's bare-written
/// `param` against either key spelling via sort-gated [`same_label`] (WI-764-annotated).
/// It is a fact-arg matcher, not a bindings-list lookup, so it does not enroll — but a
/// change to the key rule must visit it too, or variance lookup diverges from binding
/// lookup and a covariant param silently reads as invariant.
pub(super) fn binding_for_param<'a, T>(
    kb: &KnowledgeBase,
    bindings: &'a [(Symbol, T)],
    param: Symbol,
    mode: BindingKeyMatch,
) -> Option<&'a T> {
    binding_index_for_param(kb, bindings, param, mode).map(|i| &bindings[i].1)
}

/// [`binding_for_param`] by INDEX — the actual rule. Separate so a caller needing MUTABLE
/// access to the slot (`unroll_annotation_with_inferred`, which merges an annotation's
/// bindings with the value's) shares this one definition instead of hand-rolling a third
/// spelling of it; a `&mut` borrow cannot be handed back through the by-reference form.
pub(super) fn binding_index_for_param<T>(
    kb: &KnowledgeBase,
    bindings: &[(Symbol, T)],
    param: Symbol,
    mode: BindingKeyMatch,
) -> Option<usize> {
    if let Some(i) = bindings.iter().position(|(p, _)| *p == param) {
        return Some(i);
    }
    match mode {
        BindingKeyMatch::Identity => None,
        BindingKeyMatch::Label => bindings.iter().position(|(p, _)| same_label(kb, *p, param)),
    }
}

pub(super) fn unify_parameterized_view<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
) -> bool {
    // WI-361: read base + bindings via `extract_type` — both carriers present the
    // term backing `Fn{S, named}` (base = functor, bindings = named args). Each
    // base is a sort; present it as a bare `Ref(S)` and recurse `unify_types`,
    // preserving the full base relation (incl. WI-344 provider admissibility),
    // not a sort-symbol shortcut.
    let (a_base, a_bindings) = match extract_type(kb, a) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return false,
    };
    let (b_base, b_bindings) = match extract_type(kb, b) {
        TypeExtractor::Parameterized { base, bindings } => (base, bindings),
        _ => return false,
    };
    // WI-453 (§5.4): when the two bases DIFFER, a type-param base (the marked
    // carrier `F`) resolves to its backing Var so `F[T=A] ≟ Option[T=X]` FILLS
    // `F := Option` (use-site) / skolem-compares (def-site). Same-functor unify
    // (`List ≟ List`, `F ≟ F`) takes the trivial Ref path — no alias scan.
    let (a_base_ty, b_base_ty) = if a_base == b_base {
        (kb.alloc(Term::Ref(a_base)), kb.alloc(Term::Ref(b_base)))
    } else {
        (
            parameterized_base_term(kb, a_base),
            parameterized_base_term(kb, b_base),
        )
    };
    if !unify_types(kb, subst, &TermIdView(a_base_ty), &TermIdView(b_base_ty)) {
        return false;
    }
    // WI-726: key comparison via [`binding_for_param`] — the two producers spell one slot's
    // key either canonically or bare. An a-side param the b-side does not bind is WIDTH-
    // ignored (unify is width-tolerant here by design; the subtype twin is the direction
    // that rejects) — which is exactly why the key match must be right: before WI-726 a
    // key MISS was indistinguishable from a genuinely absent binding, so the slot was
    // skipped, `unify_types` returned true without binding it, and the op type param
    // surfaced later as `UnconstrainedTypeParam` far from the cause.
    let key_match = BindingKeyMatch::for_bases(kb, a_base, b_base);
    // WI-20260904-60143 — EVERY SLOT, THEN THE VERDICT (`&=`, not `return false`). See
    // [`unify_types`]' "what survives a `false`" note: the discarding callers read this σ,
    // and THIS LIST'S ORDER IS THE AUTHOR'S, so stopping at the first disagreeing slot made
    // WHICH bindings they read a function of how the slots were spelled. Measured,
    // `take[X](p: Pair[A = Int64, B = X])` given `Pair[A = String, B = Int64]` refused with
    // `expected Pair[A = Int64, B = ?X]` — a raw inference variable in a user-facing message
    // — while the same disagreement written `Pair[A = X, B = Int64]` refused with the pinned
    // `Pair[A = Int64, B = Int64]`. One program, two slot orders, two messages. A LATER slot
    // cannot un-say an earlier one's disagreement (the verdict is a conjunction either way),
    // so the only thing the early exit bought was the arbitrariness.
    let mut ok = true;
    for (param, av) in &a_bindings {
        if let Some(bv) = binding_for_param(kb, &b_bindings, *param, key_match) {
            ok &= unify_types(kb, subst, av, bv);
        }
    }
    ok
}

/// WI-342: the sole `arrow` unification, carrier-agnostic over [`TermView`]
/// (both the `TermId` dispatch via [`TermIdView`] and the `Value` carrier route
/// here). `param`/`result` unify via the generic [`unify_types`]; `effects` via
/// the carrier-agnostic [`unify_effect_rows`]. A missing effects field is
/// treated as the empty row.
/// WI-1084 — UNIFY across the TWO SPELLINGS OF ONE TYPE: an `arrow` against a
/// `Function[A, B, E]`. `docs/kernel-language.md` §4.4 says outright that these are the
/// same type (`A` = param, `B` = result, `E` = effects); SUBTYPING has honoured that since
/// WI-289 via [`arrow_function_compatible`], and unification did not.
///
/// WHAT WENT WRONG WITHOUT IT, and it is not that the pair was refused — it is that it was
/// never DECOMPOSED. `unify_types`' dispatch had only `(arrow, arrow)`, so the pair took the
/// `_ =>` fallback to [`types_compatible`], which decomposes correctly but CANNOT BIND: it is
/// a subtype check, and a component pair like `Int64` vs a flexible `?A1` has no arm there
/// (WI-1079 deliberately gives a variable no dispatch tag, on the grounds that "unification
/// binds or refuses it first" — which is exactly what did not happen here). So the whole-type
/// unify answered `false` with ZERO bindings, for a correct pair as readily as a wrong one,
/// and every caller inferring through a `Function[…]`-typed slot learned nothing.
///
/// MEASURED, `idp[A](x: A) -> A` instantiated to `(x: ?A1) -> ?A1` against four slots — the
/// arrow spellings are the control, and they were always right:
///
/// | slot | before | after |
/// |---|---|---|
/// | `(v: Int64) -> Int64` | true, binds `?A1 := Int64` | unchanged |
/// | `(v: Int64) -> String` | false, binds `?A1 := Int64` | unchanged |
/// | `Function[A = Int64, B = Int64, E = {}]` | **false, 0 bindings** | true, binds `?A1` |
/// | `Function[A = Int64, B = String, E = {}]` | false, **0 bindings** | false, binds `?A1` |
///
/// BY WHOLE `A`, NOT POSITIONALLY, which is the one rule this must not get wrong: WI-775
/// settled that a `Function[A = …]`'s `A` is the ARGUMENT's data type — what flows to
/// `apply(f, x: A)` — so a named-tuple `A` is ONE tuple-typed argument, not a parameter list.
/// Routing this through [`unify_arrow_view`] would apply `unify_arrow_params`' positional
/// alignment and bridge `(acc, x)` to `(_1, _2)`, re-opening precisely the unsoundness WI-775
/// closed. Each component is unified WHOLE.
///
/// ARITY IS READ, BUT NO ARITY VERDICT IS RETURNED — the distinction matters. This function
/// consults the arrow's arity only to decide whether its `param` and the `Function`'s `A` are
/// the same KIND of thing (see the comment at the param component); it never refuses a pair
/// FOR its arity, because a `Function` states none and cannot ([`arrow_function_compatible`]'s
/// reason). Deciding arity stays with the checkers — [`arrow_function_compatible`] on the
/// ground path, [`validate_arrow_param_result`] / [`function_slot_arity_error`] on the
/// non-ground one.
///
/// ITS JOB IS TO BIND. The arg-unify loop discards this boolean by design (unify is equality,
/// argument passing is subtyping, and a unify-false would over-reject the legitimate
/// conversions), so what this contributes is the SUBSTITUTION the deciders then read — which
/// is why "answered false having bound nothing" was a defect and "answers false having bound
/// `?A1`" is the fix.
fn unify_arrow_function_view<AR: TermView, FN: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    arrow: &AR,
    function: &FN,
) -> bool {
    let (Some(a_parts), Some(f_parts)) = (arrow_parts(kb, arrow), arrow_parts(kb, function)) else {
        return false;
    };
    let (a_param, a_result, a_eff) = a_parts;
    let (f_param, f_result, f_eff) = f_parts;
    // A missing param is POLYMORPHIC, not empty — a bare `Function` without an `A` binding
    // constrains nothing, exactly as it constrains nothing in the subtype twin.
    //
    // AND THE PARAM COMPONENT IS UNIFIED ONLY AT ARROW ARITY 1, which is where the two sides
    // are the SAME KIND OF THING. WI-791: an arrow's `param` is the sole parameter's TYPE at
    // arity 1 and the parameter LIST at any other arity, while a `Function`'s `A` is always
    // ONE argument's data type. At arity 1 those are one category and unify outright — that
    // is the case this arm exists for, `Function[A = Int64, …]` pinning an instantiated
    // `∀A. A -> A`'s `?A1`, and it binds var-to-var as readily as var-to-concrete.
    //
    // At any other arity they are related by the WI-775/WI-787 SPREAD convention — a
    // named-tuple `A` admits a 2-parameter operation's eta arrow, because `f(3, 10)` and
    // `f((3, 10))` are both legal at that slot — and a convention about how a CALL is
    // written is not a type identity. Unifying anyway BINDS `A` to the positional `(_1: …,
    // _2: …)` spelling, and that binding is then read by the callee's OTHER parameters,
    // where a data tuple is name-keyed (WI-788/WI-803) and `(x: Int64, acc: Int64)` no
    // longer matches. MEASURED: `wi787_eta_spread_named_tuple_test`, 4 rows, failing at a
    // SIBLING argument with `expected (_1: Int64, _2: Int64), got (x: Int64, acc: Int64)`.
    //
    // NOT a groundness gate, which was the first cut and was wrong for the reason it is
    // worth recording: it also refused `A ~ ?X`, a var-to-var unification the substitution
    // handles natively (`bind_compressed`'s path compression IS the equality class), and so
    // threw away legitimate inference to dodge a problem that is not about variables at all.
    let a_arity = kb.intern("arity");
    let spread_shaped = arrow_arity(kb, arrow, a_arity) != Some(1);
    // WI-20260904-60143 — THE SHORT-CIRCUIT STAYS, in step with [`unify_arrow_view`]'s (see
    // its note for the measured reason): both arms stop at the first disagreeing PART, so
    // neither spelling of one type answers differently about what a failed unify leaves
    // behind — the parity WI-1084 closed here.
    //
    // THAT PARITY IS ABOUT THE SHORT-CIRCUIT AND NOTHING ELSE, and the `spread_shaped` guard
    // below is where the two spellings genuinely diverge: at any arity but 1 this arm does
    // not unify the param AT ALL (WI-787 — a `Function`'s `A` is one argument's data type,
    // an arrow's `param` at that arity is a parameter LIST, and the two are related by a
    // calling convention rather than an identity), while [`unify_arrow_view`] sends its
    // parameter list through [`unify_named_tuple_as`] and therefore through this ticket's
    // every-slot loop. So a multi-parameter arrow's parameter list is author-ordered and
    // total in the arrow spelling and SKIPPED WHOLESALE in this one. Pre-existing and
    // deliberate; named here because the paragraph above would otherwise read as claiming a
    // parity on that axis too. Found by `/code-review`.
    if let (Some(x), Some(y)) = (&a_param, &f_param) {
        if !spread_shaped && !unify_types(kb, subst, x, y) {
            return false;
        }
    }
    if !unify_types(kb, subst, &a_result, &f_result) {
        return false;
    }
    // Same reading of a missing `E`: polymorphic. The arrow side always synthesizes an
    // `effects` child, so only the `Function` side can be `None` in practice.
    match (a_eff, f_eff) {
        (None, _) | (_, None) => true,
        (Some(ae), Some(ee)) => {
            let ae = canonical_effects_row(kb, &ae);
            let ee = canonical_effects_row(kb, &ee);
            unify_effect_rows(kb, subst, &ae, &ee)
        }
    }
}

fn unify_arrow_view<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a: &A,
    b: &B,
) -> bool {
    let param_sym = kb.intern("param");
    let result_sym = kb.intern("result");
    let effects_sym = kb.intern("effects");

    // WI-791: two arrows relate only if they take the SAME NUMBER of parameters,
    // and the count also says how to read the param slot below.
    let Some(arity) = agreed_arrow_arity(kb, a, b) else {
        return false;
    };

    // WI-20260904-60143 — AN ARROW'S PARTS KEEP THE SHORT-CIRCUIT, and that is the line the
    // ticket drew rather than an omission. What had to become total is a list whose order is
    // AUTHORIAL — a parameterized type's bindings, a tuple's fields, and this arrow's own
    // parameter LIST, which reaches [`unify_named_tuple_as`] through [`unify_arrow_params`]
    // — because there "which bindings survive a `false`" was a function of how the author
    // happened to write the slots. (The `Function[A, B, E]` spelling does NOT reach it for a
    // multi-parameter list; [`unify_arrow_function_view`]'s `spread_shaped` guard says why.) `param` / `result` / `effects`
    // are fixed by the FORM, so stopping at the first disagreeing part is already determined
    // by the two types and not by anyone's spelling.
    //
    // AND CONTINUING HERE IS UNSOUND, MEASURED. A disagreeing `param` means the two arrows
    // are not the same function, so a `result` binding taken across it is drawn from two
    // unrelated types. Made total, it FILLS UNWRITTEN CARRIER PARAMS from a unify that
    // failed and `wi_mdwew_bare_spec_arg_provision_test::ambient_requires_compound_clause_-
    // value_is_not_bound_verbatim` goes from REFUSED to a clean load — "grant a licence and
    // bind a wrong rigid together", which is the exact shape that test exists to forbid.
    // (Three more rows moved with it: that file's `foreign_provision_binding_is_refused_-
    // like_its_concrete_twin` and two in `wi599_carrier_arg_provision_test`.)
    match (
        named_child_value(kb, a, param_sym),
        named_child_value(kb, b, param_sym),
    ) {
        (Some(x), Some(y)) => {
            // WI-775: a PARAMETER LIST, not a data tuple — positional alignment
            // is admissible here (and only here).
            if !unify_arrow_params(kb, subst, &x, &y, arity) {
                return false;
            }
        }
        _ => return false,
    }
    match (
        named_child_value(kb, a, result_sym),
        named_child_value(kb, b, result_sym),
    ) {
        (Some(x), Some(y)) => {
            if !unify_types(kb, subst, &x, &y) {
                return false;
            }
        }
        _ => return false,
    }

    match (
        named_child_value(kb, a, effects_sym),
        named_child_value(kb, b, effects_sym),
    ) {
        (Some(x), Some(y)) => unify_effect_rows(kb, subst, &x, &y),
        (None, None) => true,
        (Some(x), None) => match kb.try_make_empty_effects_rows() {
            Some(er) => unify_effect_rows(kb, subst, &x, &TermIdView(er)),
            None => false,
        },
        (None, Some(y)) => match kb.try_make_empty_effects_rows() {
            Some(er) => unify_effect_rows(kb, subst, &TermIdView(er), &y),
            None => false,
        },
    }
}

/// Decode a `List[record]` of two-field records into `(symbol-field, value-field)`
/// pairs, carrier-agnostic over [`TermView`] — a hash-consed `Term` cons-list OR a
/// `Value::Entity` cons-list (the WI-361 poisoned `named_tuple` `fields` carrier).
/// Shared by a `parameterized`'s `bindings` (`TypeBinding{param, value}`) and a
/// `named_tuple`'s `fields` (`TypeField{name, type}`). `sym_key` names the
/// `Ref`-valued field (read as a `Symbol`), `val_key` the type-valued field (read
/// as a `Value`); a cell that is not a `cons` record or is missing either field is
/// skipped.
pub(crate) fn list_records_to_pairs<V: TermView>(
    kb: &KnowledgeBase,
    list: &V,
    sym_key: &str,
    val_key: &str,
) -> Vec<(Symbol, Value)> {
    let (Some(head_key), Some(tail_key)) = (kb.lookup_symbol("head"), kb.lookup_symbol("tail"))
    else {
        return Vec::new();
    };
    let mut out = Vec::new();
    let mut next = decode_cons_cell(kb, list, head_key, tail_key, sym_key, val_key, &mut out);
    while let Some(cell) = next {
        next = decode_cons_cell(kb, &cell, head_key, tail_key, sym_key, val_key, &mut out);
    }
    out
}

/// WI-1083 — decode a `List[T]` of BARE elements, carrier-agnostic over [`TermView`]:
/// the element sibling of [`list_records_to_pairs`], which decodes a list whose cells
/// hold two-field RECORDS. A `PolyType`'s `binders` is a `List[Term]` of variables —
/// there is no record to unpack, so reusing the pair decoder would have meant giving
/// each binder a wrapper record it does not have.
///
/// Same cons/nil spine and the same tolerance: a non-`cons` cell simply ends the walk,
/// so a `nil` (or a malformed list) reads as the empty list rather than an error. The
/// one producer is [`crate::kb::load::build_value_list`], whose output this reverses.
pub(crate) fn value_list_elements<V: TermView>(kb: &KnowledgeBase, list: &V) -> Vec<Value> {
    let (Some(head_key), Some(tail_key)) = (kb.lookup_symbol("head"), kb.lookup_symbol("tail"))
    else {
        return Vec::new();
    };
    let mut out = Vec::new();
    if !is_list_cons_cell(kb, list) {
        return out;
    }
    let Some(first) = named_child_value(kb, list, head_key) else {
        return out;
    };
    out.push(first);
    let mut cell = named_child_value(kb, list, tail_key);
    while let Some(c) = cell {
        if !is_list_cons_cell(kb, &c) {
            break;
        }
        match named_child_value(kb, &c, head_key) {
            Some(h) => out.push(h),
            None => break,
        }
        cell = named_child_value(kb, &c, tail_key);
    }
    out
}

/// WI-20260904-50B2K part (c) — is this view the EMPTY list, as opposed to something
/// [`value_list_elements`] merely failed to decode?
///
/// That decoder is deliberately tolerant — "a `nil` (or a malformed list) reads as the empty
/// list rather than an error" — which is exactly the ambiguity the `binders` arm of
/// [`extract_type`] refuses to live with. `binders` can afford to reject an empty answer
/// outright, because a ∀ with no binders is malformed anyway. A CONTEXT may legitimately be
/// empty, so it needs the distinction drawn rather than assumed: `nil` is the head
/// [`crate::kb::load::build_value_list`] writes for an empty list, and anything else that
/// decoded to nothing did not decode.
pub(super) fn value_is_nil_list<V: TermView>(kb: &KnowledgeBase, v: &V) -> bool {
    let Some(nil) = kb.try_resolve_symbol("anthill.prelude.List.nil") else {
        return false;
    };
    matches!(
        v.head(kb),
        ViewHead::Functor { functor: Some(f), .. } if kb.canonical_sym(f) == kb.canonical_sym(nil)
    )
}

/// Is this view a `List.cons` cell? The spine test [`value_list_elements`] and
/// [`decode_cons_cell`] both walk on — ONE owner, so the two decoders cannot come to
/// disagree about what a list cell is.
pub(super) fn is_list_cons_cell<V: TermView>(kb: &KnowledgeBase, v: &V) -> bool {
    match v.head(kb) {
        ViewHead::Functor {
            functor: Some(f), ..
        } => kb.qualified_name_of(f) == "anthill.prelude.List.cons",
        _ => false,
    }
}

/// One step of [`list_records_to_pairs`]: if `cell` is a `cons` record, push its
/// `head` record's `(sym_key, val_key)` pair into `out` and return its `tail` as a
/// [`Value`]; otherwise (nil / non-cons) `None`.
fn decode_cons_cell<V: TermView>(
    kb: &KnowledgeBase,
    cell: &V,
    head_key: Symbol,
    tail_key: Symbol,
    sym_key: &str,
    val_key: &str,
    out: &mut Vec<(Symbol, Value)>,
) -> Option<Value> {
    if !is_list_cons_cell(kb, cell) {
        return None;
    }
    if let Some(rec) = named_child_value(kb, cell, head_key) {
        if let (Some(s), Some(v)) = (
            view_child_sym(kb, &rec, sym_key),
            view_child_value(kb, &rec, val_key),
        ) {
            out.push((s, v));
        }
    }
    named_child_value(kb, cell, tail_key)
}

/// A [`ViewItem`] (which may borrow `kb`) as an owned [`Value`], freeing the
/// caller's `kb` borrow before a `&mut kb` recursion.
pub(super) fn view_item_value(item: &ViewItem) -> Value {
    match item {
        ViewItem::Term(t) => Value::term(*t),
        ViewItem::Value(v) => (*v).clone(),
        ViewItem::Owned(v) => v.clone(),
        // WI-20260904-02ERR: through the choke point, so an arrow param that IS a type
        // variable reads back as `Value::Var` and the σ walks resolve it. Leaving it a
        // `Value::Node` made `resolved_type_is_ground` answer false and skipped
        // `arrow_params_compatible` entirely — a wrong accept (`/code-review`).
        ViewItem::Node(rc) => crate::kb::node_occurrence::occurrence_as_type_value(rc),
    }
}

/// WI-342 P3: resolve a view through the substitution to a `Value` (the
/// carrier-agnostic resolved type). The concrete carrier is recovered via
/// [`TermView::as_bind_value`] — a `TermId` carrier runs the existing
/// `walk_type` (var + sort-alias resolution); a `Value` carrier walks
/// `Value::Term`/`Value::Var` and surfaces the rest (`Value::Node`, entities).
pub(super) fn walk_view(kb: &KnowledgeBase, subst: &Substitution, v: &impl TermView) -> Value {
    match v.as_bind_value() {
        BindValue::Term(t) => walk_term_to_resolved(kb, subst, t),
        BindValue::Value(val) => walk_value_to_resolved(kb, subst, val),
        BindValue::Path(_) => {
            // A discrim-tree var-path is not a type carrier — refuse rather than
            // fabricate one (`Unit` unifies with nothing meaningful here).
            debug_assert!(false, "unify_types: Path carrier in a type position");
            Value::Unit
        }
    }
}

/// Walk a `TermId`-carried type, then surface a non-`Term` `Value` binding the
/// `TermId` walk can't see (`walk_type` narrows to `Value::Term`, skipping
/// non-`Term` bindings).
pub(super) fn walk_term_to_resolved(kb: &KnowledgeBase, subst: &Substitution, t: TermId) -> Value {
    let t2 = walk_type(kb, subst, t);
    if let Term::Var(Var::Global(vid)) = kb.get_term(t2) {
        if let Some(v) = subst.resolve_as_value(*vid) {
            if !matches!(v, Value::Term { .. }) {
                return walk_value_to_resolved(kb, subst, v.clone());
            }
        }
    }
    Value::term(t2)
}

/// Walk a `Value`-carried type through the substitution. `Value::Term` defers to
/// the `TermId` walk; an unbound `Value::Var` resolves through `subst`; every
/// other form (`Value::Node`, entities) is already resolved.
pub(super) fn walk_value_to_resolved(
    kb: &KnowledgeBase,
    subst: &Substitution,
    val: Value,
) -> Value {
    // Iterative + cycle-guarded (WI-417): follow a `Value::Var` binding chain via
    // `resolve_as_value`. A `Value::Term` defers to the (guarded) `walk_type`
    // path; an unbound var / non-var carrier ends the chain. A cyclic `Value::Var`
    // substitution returns a representative instead of recursing forever.
    let mut cur = val;
    let mut visited: SmallVec<[VarId; 4]> = SmallVec::new();
    loop {
        match cur {
            Value::Term { id: t, .. } => return walk_term_to_resolved(kb, subst, t),
            Value::Var(Var::Global(vid)) => {
                if visited.contains(&vid) {
                    return Value::Var(Var::Global(vid));
                }
                match subst.resolve_as_value(vid) {
                    Some(bound) => {
                        visited.push(vid);
                        cur = bound.clone();
                    }
                    None => return Value::Var(Var::Global(vid)),
                }
            }
            // WI-20260904-02ERR: THE THIRD SPELLING OF A TYPE VARIABLE, chased exactly like
            // the two above. The doc's "every other form is already resolved" stopped being
            // true when a variable gained the occurrence carrier: a `TypeNode::Var` returned
            // as-is is an UNWALKED var, so a BOUND one would be compared structurally
            // against its own binding and mismatch.
            Value::Node(ref occ) if occ_type_var_global(occ).is_some() => {
                let vid = occ_type_var_global(occ).expect("guarded by the arm");
                if visited.contains(&vid) {
                    return cur;
                }
                match subst.resolve_as_value(vid) {
                    Some(bound) => {
                        visited.push(vid);
                        cur = bound.clone();
                    }
                    None => return cur,
                }
            }
            other => return other,
        }
    }
}

/// WI-394: a `TermId`-consuming caller that walked a var which actually
/// resolved to a non-`Term` carrier (a `Value::Node` denoted / written
/// effect-row binding) would misread the bare var as unresolved — both
/// `walk_type` and `walk_type_deep` deliberately STOP at a non-`Term`
/// binding, returning the var unchanged. Surface such a binding by lowering
/// it faithfully to a `TermId` (`value_to_term`, lossless for a `Node` via
/// WI-390 `occurrence_to_term`). A `Term` binding, an unbound var, or an
/// un-lowerable carrier returns `walked` unchanged (the pre-WI-394 behavior).
/// Callers that can consume a `Value` directly should instead walk via
/// `walk_term_to_resolved` / `walk_value_to_resolved`; this is the bridge for
/// the sites that genuinely need a `TermId` (storage / structural compare).
pub(super) fn surface_node_binding_to_term(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    walked: TermId,
) -> TermId {
    let vid = match kb.get_term(walked) {
        Term::Var(Var::Global(vid)) => *vid,
        _ => return walked,
    };
    let bound = match subst.resolve_as_value(vid) {
        Some(v) if !matches!(v, Value::Term { .. }) => v.clone(),
        _ => return walked,
    };
    match value_to_term(kb, &bound) {
        Ok(t) => t,
        Err(e) => {
            // A var bound to a non-`Term`, non-lowerable carrier (opaque / Unit
            // / Tuple / a runtime-only `Value`) standing in a TYPE slot is a
            // malformation, not a benign miss — surface it loudly (mirrors the
            // `walk_view` Path-carrier guard). Release stays strictly no-worse
            // than the pre-WI-394 walk: keep the bare var.
            debug_assert!(
                false,
                "surface_node_binding_to_term: type var {vid:?} bound to an \
                 un-lowerable carrier {bound:?}: {e:?}"
            );
            walked
        }
    }
}

/// The logic-var id a resolved type *is*, if any — a hash-consed
/// `Term::Var(Global)` or a `Value::Var(Global)`.
pub(super) fn resolved_var(kb: &KnowledgeBase, r: &Value) -> Option<VarId> {
    match r {
        Value::Term { id: t, .. } => match kb.get_term(*t) {
            Term::Var(Var::Global(vid)) => Some(*vid),
            _ => None,
        },
        Value::Var(Var::Global(vid)) => Some(*vid),
        // WI-20260904-02ERR: the occurrence-carried spelling. Its absence here was the
        // single most consequential `_ =>` in the census: `unify_types` asks this before
        // its structural arms, so a `TypeNode::Var` read as "not a variable" fell through
        // to a STRUCTURAL comparison and an identity lambda's `?param` stopped unifying
        // with `Int64` — MEASURED as "type mismatch in main.return (op-return): expected
        // Int64, got ??param" on `let f = lambda x -> x  f(7)`.
        Value::Node(occ) => occ_type_var_global(occ),
        _ => None,
    }
}

/// WI-20260904-02ERR: the `VarId` of an occurrence that IS a flex type variable, else
/// `None`. One reader for the shape, so the σ walk and the unifier cannot disagree about
/// what counts as a variable.
fn occ_type_var_global(occ: &Rc<NodeOccurrence>) -> Option<VarId> {
    match occ.as_type() {
        Some(TypeNode::Var(Var::Global(vid))) => Some(*vid),
        _ => None,
    }
}

/// Bind `vid` to a resolved type by its carrier (WI-342 P3): `bind_term` for a
/// hash-consed `TermId`, `bind_value` for any other `Value` carrier.
pub(super) fn bind_resolved(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    vid: VarId,
    other: Value,
) -> bool {
    match other {
        Value::Term { id: t, .. } => {
            if occurs_in(kb, vid, t) {
                return false;
            }
            subst.bind_term(kb, vid, t);
        }
        other => {
            if occurs_in_view(kb, vid, &other) {
                return false;
            }
            subst.bind_value(kb, vid, other);
        }
    }
    !subst.is_contradiction()
}

/// Short functor name of a resolved type, carrier-agnostically (via [`TermView`]).
pub(super) fn resolved_functor_name<'a>(
    kb: &'a KnowledgeBase,
    r: &impl TermView,
) -> Option<&'a str> {
    // WI-436: a bare `Ref(c)` is the 0-ary application of `c` — read its functor
    // symbol off either spelling (`functor_sym` accepts both `Functor` and
    // `Ref`), so a 0-ary EffectExpression / reflect constructor canonicalized to
    // the bare `Ref` (`empty_row`, `wildcard`, …) is still recognized by name.
    r.head(kb).functor_sym().map(|sym| kb.local_name_of(sym))
}

/// WI-342 P3: unify two `denoted` types by their carried value. For the value
/// forms produced today the carried value is an `Expr::Ref(sym)` / `Term::Ref`
/// occurrence — both expose `ViewHead::Ref` — so two `denoted` unify iff their
/// value refers to the same symbol. Works cross-carrier (a ground
/// `denoted(Ref(c))` unifies with a `Value`-carried `denoted(Node(Ref(c)))`),
/// which is what lets P3 run while loaders stay on the legacy path.
pub(super) fn unify_denoted_view<A: TermView, B: TermView>(
    kb: &mut KnowledgeBase,
    a: &A,
    b: &B,
) -> bool {
    // Sequential (not a single tuple) so each `&mut kb` borrow is released
    // before the next — `denoted_ref_sym` interns the `value` field symbol.
    let sa = denoted_ref_sym(kb, a);
    let sb = denoted_ref_sym(kb, b);
    match (sa, sb) {
        (Some(sa), Some(sb)) => {
            if sa == sb {
                return true;
            }
            // ALPHA-EQUIVALENCE of a binder-naming effect target — §5.5. The
            // binder is a `CallbackParam` place (`f.a`) and its alpha-canonical
            // identity is its POSITION among the callback's params, which is the
            // spec's rule expressed as this function's De Bruijn view of the place.
            //
            // SOUNDNESS INVARIANT (position-only comparison), which is local to
            // this site and NOT in the spec: a raw `Modify[CallbackParam]`
            // label exists ONLY inside its own callback arrow's `effects` child —
            // the binder is meaningless outside its arrow's scope, and
            // `region::op_boundary_effects` re-keys any callback Modify to a
            // concrete op place (input / result), or drops it, before it reaches
            // a top-level op effect row. So two `CallbackParam` denoteds only
            // ever meet here through `arrow_compatible_view`, which has ALREADY
            // aligned the two arrows (param children unified first) — i.e. they
            // are corresponding binders, so equal position ⇒ same binder. A
            // future caller comparing two binders NOT through aligned-arrow
            // unify would break this — keep callback-Modify labels arrow-local.
            match (
                callback_binder_position(kb, sa),
                callback_binder_position(kb, sb),
            ) {
                (Some(pa), Some(pb)) => pa == pb,
                _ => false,
            }
        }
        // WI-302: a non-`Ref` carried value — a COMPOUND value FIELD-PATH
        // (`c.contents` / `result.a`, a `DotApply` chain) — compares by STRUCTURAL
        // equality of the two carried value occurrences. The value is opaque (it
        // INDEXES the type; there is no binding to unify, exactly as the `sa == sb`
        // Ref arm is plain identity), so two such denoteds are the same type iff their
        // value paths are structurally identical — `Modify[c.contents]` unifies with
        // `Modify[c.contents]` but not `Modify[d.contents]`. (A literal carried value
        // compares structurally too; a bound-name nested apply still needs alpha-aware
        // comparison — deferred, and `views_structurally_equal` conservatively refuses
        // it, never a wrong accept.)
        _ => {
            let value_key = kb.intern("value");
            match (a.named_arg(kb, value_key), b.named_arg(kb, value_key)) {
                (Some(va), Some(vb)) => views_structurally_equal(kb, &va, &vb),
                _ => false,
            }
        }
    }
}

/// WI-341 alpha-equivalence: the 0-based position of a `CallbackParam` binder
/// among its callback's parameters — its alpha-canonical identity. `None` for a
/// non-binder symbol (an op param / result / sort), which is compared by
/// identity instead. The parent callable is the place's qualified name minus its
/// last segment (`<op>.f.a` → `<op>.f`), and its ordered params are on its symbol
/// (`SymbolTable::arg_places`).
fn callback_binder_position(kb: &KnowledgeBase, sym: Symbol) -> Option<usize> {
    if kb.kind_of(sym) != Some(crate::intern::SymbolKind::CallbackParam) {
        return None;
    }
    let qn = kb.qualified_name_of(sym);
    let parent_qn = qn.rsplit_once('.').map(|(p, _)| p)?;
    let callback = kb.try_resolve_symbol(parent_qn)?;
    kb.symbols
        .arg_places(callback)
        .iter()
        .position(|&p| p == sym)
}

/// The symbol a `denoted`'s `value` child refers to, if it is a NAME-shaped
/// occurrence — read carrier-agnostically through [`TermView`]. `intern` (not
/// `lookup_symbol`) so the read is robust in a KB that hasn't interned the
/// well-known `value` field symbol (a production KB always has via stdlib load).
///
/// WI-20260902-CZJ2N: the arity pin is the retired `ViewHead::Ref` variant. Two
/// `denoted` types unify iff their value refers to the SAME SYMBOL, so an APPLIED
/// value (`some(?x)`) must keep answering `None` here and fall to the structural
/// comparison, not report `some`.
fn denoted_ref_sym(kb: &mut KnowledgeBase, r: &impl TermView) -> Option<Symbol> {
    let value_key = kb.intern("value");
    let child = r.named_arg(kb, value_key)?;
    match child.head(kb) {
        ViewHead::Functor {
            functor: Some(s),
            pos_arity: 0,
            named_arity: 0,
        } => Some(s),
        _ => None,
    }
}

/// Occurs check over a [`TermView`] (the `Value`-carried analog of
/// [`occurs_in`]): does `vid` appear anywhere inside `v`?
///
/// A `Value::Node` type is walked completely via [`occ_contains_var`] (which reads
/// the occurrence storage directly), not through the view alone — belt-and-braces
/// so a var nested in a parameterized binding / named-tuple field can't be missed,
/// which would let `bind_resolved` create a cyclic binding. So a `Value::Node` is
/// walked completely via [`occ_contains_var`]
/// over the occurrence spine; every other carrier (a `TermId`, which exposes all
/// children) uses the view walk.
pub(super) fn occurs_in_view(kb: &KnowledgeBase, vid: VarId, v: &impl TermView) -> bool {
    if let BindValue::Value(Value::Node(occ)) = v.as_bind_value() {
        return occ_contains_var(kb, vid, &occ);
    }
    match v.head(kb) {
        // Only a flex `Global` can be the var being bound; a `Rigid` / `DeBruijn`
        // head is a distinct constant/binder and never occurs as `vid` (it would
        // formerly have read as `Opaque` and fallen through to `false`).
        ViewHead::Var(x) => x.as_global() == Some(vid),
        ViewHead::Functor {
            functor,
            pos_arity,
            named_arity,
        } => {
            // WI-20260911-7TN1Q: the exact twin of [`occurs_in`]'s `Term::Ref` leaf — a
            // BARE (nullary) head naming a sort-level type parameter IS an occurrence of
            // that parameter's variable. Nullary because that is what a `Term::Ref`
            // reads as through the view, and because the deep spelling of a
            // param-HEADED application (`F[X = Int64]`) carries its `F` as a child
            // `sort_ref`, which this walk reaches on its own.
            if let (Some(s), 0, 0) = (functor, pos_arity, named_arity) {
                if sort_param_ref_is_var(kb, s, vid) {
                    return true;
                }
            }
            for i in 0..pos_arity {
                if let Some(c) = v.pos_arg(kb, i) {
                    if occurs_in_view(kb, vid, &c) {
                        return true;
                    }
                }
            }
            for k in v.named_keys(kb) {
                if let Some(c) = v.named_arg(kb, k) {
                    if occurs_in_view(kb, vid, &c) {
                        return true;
                    }
                }
            }
            false
        }
        _ => false,
    }
}

/// Complete occurs-check over a `Value::Node` occurrence spine — walks ALL
/// children (including the bindings/fields the [`TermView`] doesn't expose for
/// Rep-A `parameterized`/`named_tuple`). A ground `TypeChild` defers to the
/// hash-consed [`occurs_in`]; a poisoned child recurses.
fn occ_contains_var(kb: &KnowledgeBase, vid: VarId, occ: &Rc<NodeOccurrence>) -> bool {
    let child = |kb: &KnowledgeBase, c: &TypeChild| match c {
        TypeChild::Interned(t) => occurs_in(kb, vid, *t),
        TypeChild::Node(n) => occ_contains_var(kb, vid, n),
    };
    if let Some(tn) = occ.as_type() {
        return match tn {
            // WI-20260904-02ERR: THE OCCURS CHECK'S WHOLE SUBJECT. Its interned twin is
            // caught by `occurs_in` through the `Interned` arm; missing it here would let
            // `?T := List[?T]` through and build an infinite type.
            TypeNode::Var(Var::Global(w)) => *w == vid,
            TypeNode::Var(_) => false,
            // A `denoted`'s carried value is a VALUE reference — an `Expr::Ref` or a
            // WI-302 field-access path (`c.contents`, a `DotApply` chain over value
            // Refs + field names) — never a type var, so it cannot capture `vid`.
            TypeNode::Denoted { .. } => false,
            TypeNode::Parameterized { base, bindings } => {
                child(kb, base) || bindings.iter().any(|(_, c)| child(kb, c))
            }
            TypeNode::EffectsRows { effects_expr } => child(kb, effects_expr),
            // WI-791: a ground `Const(Int)` `arity` can hold no var; walked for
            // totality over the node's children.
            TypeNode::Arrow {
                param,
                result,
                effects,
                arity,
            } => child(kb, param) || child(kb, result) || child(kb, effects) || child(kb, arity),
            // WI-361: `fields` is the `Value`-carried `List[TypeField]`; the
            // view-walking `occurs_in_view` descends its cons cells + records and
            // into any poisoned (`Value::Node`) field type via `occ_contains_var`.
            TypeNode::NamedTuple { fields } => occurs_in_view(kb, vid, fields),
            // WI-397: the receiver occurrence + the ground `member` ref.
            TypeNode::ExprCarried { value, member } => child(kb, value) || child(kb, member),
            // WI-1083: an occurs-check asks whether binding `vid` here would build a
            // cycle, so BOTH lists are searched — a bound occurrence is still an
            // occurrence, and reporting it is the conservative direction (a missed
            // occurrence is an infinite type, a spurious one only refuses a binding).
            TypeNode::PolyType {
                binders,
                context,
                body,
            } => {
                occurs_in_view(kb, vid, binders)
                    || occurs_in_view(kb, vid, context)
                    || child(kb, body)
            }
        };
    }
    if let Some(en) = occ.as_effect_expr() {
        return match en {
            EffectExprNode::Present { label } | EffectExprNode::Absent { label } => {
                child(kb, label)
            }
            // WI-478: the var may occur in the label (a `TypeChild`) or inside the
            // guard's `Value`-carried goal list (`occurs_in_view`, as NamedTuple).
            EffectExprNode::Guarded { label, guard } => {
                child(kb, label) || occurs_in_view(kb, vid, guard)
            }
            EffectExprNode::Merge { left, right } => child(kb, left) || child(kb, right),
            EffectExprNode::Open { tail } => child(kb, tail),
            EffectExprNode::EmptyRow => false,
        };
    }
    false
}

/// The `TermId`-only structural dispatch (functor-pair match) — reached from
/// [`unify_types`] only when both sides resolve to a hash-consed `Term`.
///
/// WI-342 dispatch consolidation: the `parameterized` and `arrow` arms now route
/// through the carrier-agnostic [`unify_parameterized_view`] / [`unify_arrow_view`]
/// (wrapping each ground `TermId` in [`TermIdView`]) — one implementation per
/// relation, shared with the `Value`-carrier path in [`unify_view_structural`].
/// The remaining arms stay `TermId`-specific because they have no `Value`-carried
/// counterpart yet (`unify_parameterized_with_sort_ref`, `unify_named_tuple`) or
/// are deliberately weaker here than the row algorithm
/// (`effects_rows`-vs-`effects_rows`, see [`unify_view_structural`]).
fn unify_term_dispatch(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_resolved: TermId,
    b_resolved: TermId,
) -> bool {
    // WI-361: dispatch on the canonical form tag so a term-backed `Ref(S)` /
    // `Fn{S,named}` routes through the same arms as the deep `sort_ref` /
    // `parameterized` (identical to the raw functor name on the deep form).
    let a_functor = type_dispatch_name(kb, a_resolved);
    let b_functor = type_dispatch_name(kb, b_resolved);

    match (a_functor, b_functor) {
        // WI-342 dispatch consolidation: the `parameterized` / `arrow` arms route
        // through the carrier-agnostic `*_view` relations (wrapping each ground
        // `TermId` in `TermIdView`) — one implementation per relation, no
        // term-specific twin to drift from. The `*_view` fns are byte-equivalent
        // to the deleted `unify_parameterized` / `unify_arrow` for the TermId
        // carrier (same base/param/result/binding logic + empty-row synthesis).
        (Some("parameterized"), Some("parameterized")) => {
            unify_parameterized_view(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
        }
        (Some("parameterized"), Some("sort_ref")) => unify_parameterized_with_sort_ref(
            kb,
            subst,
            &TermIdView(a_resolved),
            &TermIdView(b_resolved),
        ),
        (Some("sort_ref"), Some("parameterized")) => unify_parameterized_with_sort_ref(
            kb,
            subst,
            &TermIdView(b_resolved),
            &TermIdView(a_resolved),
        ),
        (Some("arrow"), Some("arrow")) => {
            unify_arrow_view(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
        }
        // WI-1084: the term-dispatch twin of the view arms — one type, two spellings.
        (Some("arrow"), Some("parameterized")) => {
            unify_arrow_function_view(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
        }
        (Some("parameterized"), Some("arrow")) => {
            unify_arrow_function_view(kb, subst, &TermIdView(b_resolved), &TermIdView(a_resolved))
        }
        (Some("named_tuple"), Some("named_tuple")) => {
            unify_named_tuple(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
        }
        (Some("effects_rows"), Some("effects_rows")) => {
            // WI-441 (was the WI-320 structural inner-unify): the FULL row
            // algorithm — the structural form was order-sensitive over
            // `merge`, rejecting equal rows written in different orders.
            unify_effect_rows(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
        }
        _ => {
            // WI-441: a pair with one ROW-shaped side (a bare `open(?ρ)`
            // binding vs a rigid row var, etc.) is a row comparison — see
            // the view-dispatch twin.
            if value_is_row_shaped(kb, &TermIdView(a_resolved))
                || value_is_row_shaped(kb, &TermIdView(b_resolved))
            {
                unify_effect_rows(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
            } else {
                types_compatible(kb, subst, &TermIdView(a_resolved), &TermIdView(b_resolved))
            }
        }
    }
}

/// Unify `parameterized(B, [P = V, …])` with `sort_ref(B)`.
///
/// `sort_ref(B)` doesn't pin B's sort-level type parameters — they're
/// the loader-cached unification Vars shared across B's signature
/// (per `sort T = ?` registration in `load.rs`). Binding each P's
/// canonical Var to V in the substitution propagates the parameterized
/// side's bindings into B's return-type and effect positions.
///
/// Bases must match. Type params not bound on the parameterized side
/// stay unbound (caller didn't constrain them — width subtyping).
pub(super) fn unify_parameterized_with_sort_ref<P: TermView, S: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    parameterized: &P,
    sort_ref: &S,
) -> bool {
    // WI-361: read base + bindings form-agnostically — deep `parameterized(base,
    // bindings)` OR term-backed `Fn{S, named}`. A non-parameterized side, a base
    // mismatch, or a non-`sort_ref` falls back to the plain compat relation.
    // WI-342: carrier-agnostic over [`TermView`] (both sides may be a `Value::Node`).
    let TypeExtractor::Parameterized {
        base: pbase_sym,
        bindings,
    } = extract_type(kb, parameterized)
    else {
        return types_compatible(kb, subst, parameterized, sort_ref);
    };
    let Some(sref_sym) = extract_sort_ref_sym(kb, sort_ref) else {
        return types_compatible(kb, subst, parameterized, sort_ref);
    };
    // WI-381: a sort_ref to a structured (ground) defined-type / alias resolves to its
    // underlying shape first — `IntStream` ⟹ `Stream[T = Int]` — so the alias's fixed
    // bindings are ENFORCED against the parameterized side instead of the bare ref
    // going all-fresh and silently dropping them. Re-dispatch through `unify_types`.
    if let Some(shape) = resolve_alias_shape(kb, sref_sym) {
        return unify_types(kb, subst, parameterized, &TermIdView(shape));
    }
    if pbase_sym != sref_sym {
        return types_compatible(kb, subst, parameterized, sort_ref);
    }

    for (psym, value) in &bindings {
        // Classify the binding value up front so the `format!` + symbol-resolve
        // below runs ONLY for a value that actually binds the alias Var. Two bind:
        //  - a ground (`Value::Term`) value;
        //  - WI-375: a Node-carried EFFECT-ROW — a WRITTEN row `E = {Modify[c]}`
        //    whose `effects_rows(…)` carries the `c` occurrence (the whole binding
        //    is a `Value::Node`). Bound via `bind_value` so the row threads into a
        //    bare-`Stream` consumer param instead of being dropped, which left `E`
        //    an unresolved `?_` that leaked as a spurious `undeclared effect`.
        // Every other carrier (a non-effect-row value-in-type `Value::Node` — a
        // denoted `Vector[Int, 3]` size — a `Var`, a scalar) binds nothing here:
        // skip it without the symbol work (the pre-WI-375 leading-`continue`
        // early-out). Out of WI-375 scope, those ride on their own SortRequiresInfo
        // / SortAlias value fact (WI-366); binding them here would perturb it.
        let is_effect_row_node = matches!(value, Value::Node(_))
            && matches!(type_head(kb, value), TypeHead::EffectsRows);
        if !matches!(value, Value::Term { .. }) && !is_effect_row_node {
            continue;
        }
        let qualified = format!(
            "{}.{}",
            kb.qualified_name_of(pbase_sym),
            kb.local_name_of(*psym),
        );
        let Some(qualified_sym) = kb.try_resolve_symbol(&qualified) else {
            continue;
        };
        let Some(alias_target) = resolve_sort_alias(kb, qualified_sym) else {
            continue;
        };
        let Term::Var(Var::Global(vid)) = kb.get_term(alias_target) else {
            continue;
        };
        let vid = *vid;
        match value {
            // Ground (term-carried): bind after the occurs-check guards a cycle.
            // WI-20260911-RS2G4: through [`bind_or_refine_member_param`], because this
            // var may already carry a WRITTEN bracket's claim about the same parameter.
            Value::Term { id: t, .. } => {
                if !occurs_in(kb, vid, *t) {
                    bind_or_refine_member_param(kb, subst, vid, *t);
                }
            }
            // Guaranteed an effect-row Node by `is_effect_row_node` above. (The
            // occurs-check is term-only; a freshly-opened alias Var never occurs
            // inside a user-written row, so no cycle arises here.)
            _ => {
                subst.bind_value(kb, vid, value.clone());
            }
        }
    }
    true
}

/// WI-20260911-RS2G4 — TWO CLAIMS ABOUT ONE CANONICAL SORT PARAMETER MUST BE UNIFIED,
/// not first-wins.
///
/// [`Substitution::bind_term`] keeps the FIRST binding and records anything else as a
/// conflict; [`enforce_member_tie`] then EXEMPTS a pair that re-unifies — in a `scratch`
/// substitution, so the refinement it just proved is thrown away. That was invisible
/// while argument unification was the only writer of these vars per call. It is not any
/// more: a form-(3) receiver bracket ([`seed_receiver_type_args`]) and a callee bracket
/// both bind this var BEFORE any argument reaches it, and a bracket value with an
/// unwritten slot (`[T = List]`, expanded to `List[T = ?f]`) is strictly MORE GENERAL
/// than what the argument carries. First-wins therefore let a TRUE partial claim delete
/// what the argument determined — WI-20260829-W6JH0's finding 2 one level in.
///
/// MEASURED, on `mine(b: Box) -> Option[T = T]` inside `sort Box[T]` with the declared
/// return `Option[T = List[T = String]]` and the argument `box(v: [1])`:
///
/// | call | before | after |
/// |---|---|---|
/// | `Box.mine(box(v: [1]))` | refused, `got Option[T = List[T = Int64]]` | unchanged — the control |
/// | `Box.mine[T = List](box(v: [1]))` | **loads clean** | refused, same message |
/// | `Box[T = List].mine(box(v: [1]))` | **loads clean** | refused, same message |
///
/// UNIFY, THEN FALL BACK TO THE RAW BIND, and the fallback is not defensive. It is what
/// keeps every existing conflict diagnostic byte-identical: an irreconcilable pair
/// (`Int64` vs `Letter`) must still land in `contradiction_details`, which is the only
/// channel [`enforce_member_tie`] reads and the only thing that makes the §3 tie loud. So
/// a refinable pair absorbs its refinement here, and an irreconcilable one is recorded
/// exactly as before.
pub(super) fn bind_or_refine_member_param(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    vid: VarId,
    t: TermId,
) {
    // The two fast paths are today's [`Substitution::bind_term`] verbatim, and they are
    // what keeps the trial below off the hot path: an UNBOUND var (the overwhelmingly
    // common case) and a re-bind to the identical hash-consed term never clone anything.
    match subst.resolve_as_value(vid) {
        None => {
            subst.bind(kb, vid, t);
            return;
        }
        Some(Value::Term { id, .. }) if *id == t => return,
        _ => {}
    }
    // ON A TRIAL COPY, because a failed `unify_types` leaves bindings behind and — the
    // shape that forced this — a BARE reference to a parametric sort rides that sort's
    // CANONICAL variables, so refining through one can re-enter this very var.
    // MEASURED, `wi374_expansion_test::member_tie_refinement_accepted`:
    // `append(cons(head: nil, …), cons(head: cons(head: 1, …), …))` binds `List.T` to a
    // bare `List` and then to `List[T = Int64]`; unifying those re-dispatches through
    // [`unify_parameterized_with_sort_ref`], which resolves `List.T` to the SAME var and
    // tries to bind it to `Int64`. The refinement is not a refinement at all, and
    // committing the partial σ turned an accepted program into
    // `first bound to List, got Int64`.
    //
    // A contradiction the trial RECORDED counts as failure even though the unify
    // answered `true`: [`unify_parameterized_with_sort_ref`] returns `true`
    // unconditionally, so its boolean does not see a nested bind conflict.
    //
    // A **NEW** DETAIL, not the absolute `is_contradiction()` flag, because the flag is not
    // a statement about THIS bind. `enforce_member_tie` ACCEPTS a contradictory σ whenever
    // every recorded detail is exempt — a WI-424 body rigid as the prior, or a pair that
    // re-unifies — and those calls load. Reading the flag would therefore make every LATER
    // refinement in such a call fall back to the raw bind, i.e. make one program's verdict
    // depend on argument ORDER. The census says the shape is live: a green `wi_tests` run
    // records 12 505 conflicts against 93 429 refinements, so σ carries the flag on calls
    // that pass.
    //
    // The detail COUNT is the whole discriminator because a conflict `subst` already
    // records pushes no second copy (`bind_term` dedups per `(var, attempted)`), so an
    // exact repeat inside the trial is not news — σ already carries it and
    // `enforce_member_tie` already judges it.
    //
    // WI-20260911-7TN1Q — AND A THIRD CONJUNCT `(prior_flag || !trial.is_contradiction())`
    // USED TO STAND HERE, claiming to catch "a trial that turned the flag on where `subst`
    // had it off". It could not: every writer reachable inside the trial is a
    // `Substitution::bind*`, and each PUSHES a detail before setting the flag. So a trial
    // that raises the flag anew has grown the count and the conjunct above rejects it
    // first; a dedup hit instead means the entry — and therefore the flag — was ALREADY in
    // σ, so `trial.is_contradiction() == prior_flag` and the disjunction is a tautology.
    // The `contradiction_details` field doc does warn that DIRECT `contradiction = true`
    // writers record nothing, which is the state the conjunct was written for; the two in
    // the typer are `FIRST_CUT_9C2PZ`-gated and neither is on `unify_types`' callee side,
    // and MEASURED with a temporary probe at this site the state never arises at all —
    // `flag set, no detail` fired 0 times across `anthill-core`'s 6046 tests. Removed
    // rather than re-documented, because a guard that cannot fire reads as protection.
    // `/code-review` raised the conjunct as a LOST-DETAIL defect; the count conjunct is
    // why it never was one.
    let prior_details = subst.contradiction_details.len();
    let mut trial = subst.clone();
    let var_t = kb.alloc_or_find_var_term(Var::Global(vid));
    if unify_types(kb, &mut trial, &TermIdView(var_t), &TermIdView(t))
        && trial.contradiction_details.len() == prior_details
    {
        *subst = trial;
        return;
    }
    subst.bind(kb, vid, t);
}

/// Occurs check: does `vid` appear anywhere inside `term`?
///
/// WI-20260911-7TN1Q: "appear" includes a `Term::Ref` NAMING the variable's parameter —
/// the spelling a written `T` inside `sort Box[T]` actually lowers to. See
/// [`sort_param_ref_is_var`] for why that is the walk's own rule and not a widening.
pub(super) fn occurs_in(kb: &KnowledgeBase, vid: VarId, term: TermId) -> bool {
    match kb.get_term(term) {
        Term::Var(Var::Global(v)) => *v == vid,
        // WI-20260911-7TN1Q: a `Ref` to a sort-level type parameter is an occurrence of
        // that parameter's variable — see [`sort_param_ref_is_var`].
        Term::Ref(s) => sort_param_ref_is_var(kb, *s, vid),
        Term::Fn {
            pos_args,
            named_args,
            ..
        } => {
            pos_args.iter().any(|t| occurs_in(kb, vid, *t))
                || named_args.iter().any(|(_, t)| occurs_in(kb, vid, *t))
        }
        _ => false,
    }
}

/// WI-20260911-7TN1Q — is `sym` a sort-level type PARAMETER whose `SortAlias` target is
/// `Var::Global(vid)`? The alias-aware half of the occurs check, asked by [`occurs_in`]'s
/// `Term::Ref` arm and by [`occurs_in_view`]'s bare-head one.
///
/// MIRRORS [`walk_type`]'S ALIAS HOP EXACTLY — the same `is_sort_param_symbol` gate and
/// the same `resolve_sort_alias` read — and that correspondence is the whole
/// justification: the occurs check must refuse precisely the bindings the σ walk can
/// chase, no more. A written `T` inside `sort Box[T]` lowers to `Term::Ref(Box.T)`, the
/// parameter's SYMBOL, not to its variable; `walk_type` resolves that `Ref` back to
/// `?T_Box`, so `?T_Box := Option[T = Ref(Box.T)]` is cyclic THROUGH THE ALIAS and
/// `walk_type_deep_g` chased it until the stack ended (WI-20260911-7TN1Q, reachable from
/// WI-841 on; `wi_7tn1q_occurs_check_sort_alias_test` carries the six programs).
///
/// THE `is_sort_param_symbol` GATE IS NOT LOAD-BEARING, and saying so is the honest half:
/// a top-level `sort Term = ?` in `anthill.reflect` also has a `SortAlias`-to-`Var` entry,
/// and MEASURED with the gate forced open (`if false && !is_sort_param_symbol`) the three
/// corpora load with identical fact/rule counts and `anthill-core`'s 6045 tests pass. It
/// stays because the CORRESPONDENCE with `walk_type` is the entire argument for this arm's
/// scope — an occurs check that refused more than the walk can chase would be refusing
/// bindings for no reason — not because a row needs it. `walk_type` states the same gate's
/// purpose at its own site.
///
/// WHAT THE VID COMPARISON IS FOR, by contrast, is measured: answering "is `sym` ANY sort
/// parameter" instead of "is it THIS one" refuses `Duo.pairOf[A = Box[T = T]]()` written
/// inside `sort Box[T]`, a legitimate program — back-out (E) of the test file, 1 red.
///
/// THE CENSUS, with a temporary probe on every firing: the arm fires NOWHERE in `stdlib/`,
/// `examples/github-todo`, `rustland/anthill-todo/anthill`, or the workspace suite —
/// only on the programs the test file names.
fn sort_param_ref_is_var(kb: &KnowledgeBase, sym: Symbol, vid: VarId) -> bool {
    if !is_sort_param_symbol(kb, sym) {
        return false;
    }
    match resolve_sort_alias(kb, sym) {
        Some(t) => matches!(kb.get_term(t), Term::Var(Var::Global(v)) if *v == vid),
        None => false,
    }
}

/// Like [`walk_type`] but recurses into `Term::Fn` children so Var bindings propagate
/// into nested positions like `Option[T = Var(vid)]`. PURE σ-propagation: a NEUTRAL head
/// (`RigidProjection` / `ExprCarried`) is an inert leaf — the walk never σ-substitutes or
/// δ-grounds it (see [`walk_type_deep_g`]). The call-site result-resolve points use the
/// grounding sibling [`resolve_type_deep_value`]; internal unification keeps using the shallow
/// `walk_type` since the per-functor `unify_parameterized` / `unify_arrow` arms already
/// recurse structurally.
pub(super) fn walk_type_deep(kb: &mut KnowledgeBase, subst: &Substitution, ty: TermId) -> TermId {
    walk_type_deep_g(kb, subst, ty, false)
}

/// WI-453 (§5.4 concrete fill): if `functor` is a marked carrier (a type-param with a
/// `SortAlias → Var`, WI-452) that has FILLED to a CONCRETE sort through `subst`
/// (`F := Option`), return that sort. An unfilled / abstract / skolemized carrier — the
/// var resolves to itself, a rigid skolem, or another sort-param — yields `None`, so the
/// application keeps its symbol functor (def-site decomposition unaffected; the
/// undischarged fill surfaces as a loud no-instance error at dispatch, not here).
fn filled_carrier_sort(
    kb: &KnowledgeBase,
    subst: &Substitution,
    functor: Symbol,
) -> Option<Symbol> {
    let var_t = resolve_sort_alias(kb, functor)
        .filter(|t| matches!(kb.get_term(*t), Term::Var(Var::Global(_))))?;
    // WI-394: walk to a `Value` so a non-`Term` (`Value::Node`) fill is seen
    // through the view; a `Node` that is not a concrete `sort_ref` yields
    // `None` ("not filled to a concrete sort"), the same as a bare var.
    let walked = walk_term_to_resolved(kb, subst, var_t);
    genuine_concrete_sort(kb, extract_sort_ref_sym(kb, &walked)?)
}

/// WI-956 — "`s` is a GENUINE CONCRETE sort": not a sort-type-param (an abstract
/// carrier, which must stay abstract and forward), and a name that really plays the
/// sort role. Two readers ask it in the same two lines — [`filled_carrier_sort`] on a
/// marked carrier's fill and [`ground_rigid_projection_if_concrete`] on an op
/// type-param's fill — and both mean it as "may I treat this as a carrier now".
///
/// `has_kind`, not the `kind_of` both used to spell — and say the strength of that
/// honestly, because it is NOT the driven half of WI-956. MEASURED over stdlib +
/// anthill-stl: 64 of 2598 symbols are sorts whose ENTITY role registered first (the
/// top-level `entity X(…)` sugar of §6.3 — `reflect.SortInfo`, `prelude.TypeBinding`,
/// …), and `kind_of` answers "not a sort" for every one, which here reads as "the fill
/// is not concrete". A HARDENING, not a fix: no program could be built to observe it,
/// because a kind-hidden sort cannot currently carry the `provides` or the member this
/// grounding reads. The only two ways to make one are that sugar, whose desugared body
/// is exactly one entity, and re-declaring the name with a body — and the re-declared
/// body does not resolve names from its namespace (MEASURED: `provides Resource[…]`
/// inside one reports *unresolved name 'Resource'*), which is its own defect and not
/// this one. Kept anyway: `kind_of` is documented for DISPLAY, and a membership gate
/// that happens to be unreachable is still asking the wrong question. The same misread
/// on the PARENT side is reachable and driven — see [`impl_parent_sort_of_op`].
pub(crate) fn genuine_concrete_sort(kb: &KnowledgeBase, s: Symbol) -> Option<Symbol> {
    if is_sort_param_symbol(kb, s) || !kb.has_kind(s, crate::intern::SymbolKind::Sort) {
        return None;
    }
    Some(s)
}

/// Shared body of [`walk_type_deep`] (`ground = false`, pure σ) and the grounding entry
/// [`resolve_type_deep_value`] (`ground = true`). When `ground` is set, the call-time
/// concrete-fill (δ-reduction) applies: a `RigidProjection` whose subject has resolved
/// (through `subst`) to a CONCRETE sort grounds via [`ground_rigid_projection_if_concrete`]
/// (the §5.4 concrete fill ⟹ CHECK); an abstract-subject projection stays the rigid
/// neutral. Keeping that grounding OUT of the `ground = false` walk is what lets the
/// ordinary σ-walk (rigidify, effect resolution, goal canonicalization) never accidentally
/// ground — or σ-substitute through — a projection's identity slot.
pub(super) fn walk_type_deep_g(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    ty: TermId,
    ground: bool,
) -> TermId {
    let resolved = walk_type(kb, subst, ty);
    match kb.get_term(resolved) {
        Term::Fn { .. } => {
            // PURE σ STOPS AT A NEUTRAL HEAD. A `RigidProjection`'s `subject` and an
            // `ExprCarried`'s receiver are IDENTITY slots — `expr_carried_zeta` compares
            // two neutrals by them STRUCTURALLY, never a unification position — and the
            // WI-392/424 rigidify pass must not rewrite them either (that would erase the
            // identity and the WI-400 non-injectivity `P.K ≢ Q.K`). So the deep walk
            // treats both as inert leaves. δ-grounding a CONCRETE-subject `RigidProjection`
            // (`P.V` with `P := CounterState` ⟹ `CounterState.V`, the §5.4 concrete fill ⟹
            // CHECK) happens ONLY when `ground` is set — i.e. through [`resolve_type_deep_value`]
            // at the call-site result-resolve points — never as a side effect of an
            // ordinary σ-walk.
            let head = type_head(kb, &TermIdView(resolved));
            if matches!(head, TypeHead::RigidProjection) {
                return if ground {
                    ground_rigid_projection_if_concrete(kb, subst, resolved).unwrap_or(resolved)
                } else {
                    resolved
                };
            }
            if matches!(head, TypeHead::ExprCarried) {
                return resolved;
            }
            // WI-453 (§5.4 concrete fill, INJECTIVE application): when grounding, a
            // parameterized type whose FUNCTOR is a marked carrier `F` filled to a
            // concrete sort `C` grounds its base — `F[T=A]` with `F := Option` ⟹
            // `Option[T=A]` (the table's `F := List` decomposition). Gated on `ground`
            // (the call-site result-resolve points), like the RigidProjection fill: a
            // pure σ walk leaves the symbol functor alone, so the def-site
            // `F[T=A] ≟ F[T=B]` decomposition (base-symbol equality) is untouched. Sound
            // because the application is injective — there is no non-injective neutral
            // identity to protect (that is the §5.3 projection, handled above).
            if ground {
                let functor = match kb.get_term(resolved) {
                    Term::Fn { functor, .. } => Some(*functor),
                    _ => None,
                };
                if let Some(c) = functor.and_then(|f| filled_carrier_sort(kb, subst, f)) {
                    let named: Vec<(Symbol, TermId)> = match kb.get_term(resolved) {
                        Term::Fn { named_args, .. } => {
                            named_args.iter().map(|(s, t)| (*s, *t)).collect()
                        }
                        _ => Vec::new(),
                    };
                    let walked: Vec<(Symbol, TermId)> = named
                        .into_iter()
                        .map(|(s, t)| (s, walk_type_deep_g(kb, subst, t, ground)))
                        .collect();
                    let base = kb.alloc(Term::Ref(c));
                    return kb.make_parameterized_type(base, &walked);
                }
            }
            kb.map_fn_children(resolved, |kb, child| {
                walk_type_deep_g(kb, subst, child, ground)
            })
        }
        _ => resolved,
    }
}

/// WI-383: δ-ground a `RigidProjection` when its subject has resolved (through `subst`) to
/// a CONCRETE sort — the call-time concrete-fill CHECK. The member resolves off the
/// carrier via [`project_type_member`] (including through the carrier's `provides` facts,
/// the WI-376 path). Returns `None` — leaving the projection the opaque rigid neutral —
/// when the subject is still abstract (a var / rigidify-pass rigid var / an enclosing
/// sort-param carrier, i.e. the §5.4 abstract fill ⟹ ADD/forward case) or when the member
/// does not ground off the carrier (the un-discharged requirement surfaces at the call's
/// own `requires` check, not here). Soundness: WI-400's rule forbids BINDING vars to force
/// `P.K ≡ Q.K`; reading a member off an ALREADY-concrete subject binds nothing.
fn ground_rigid_projection_if_concrete(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    proj: TermId,
) -> Option<TermId> {
    let TypeExtractor::RigidTypeProjection {
        sort,
        subject,
        member,
    } = extract_type(kb, &TermIdView(proj))
    else {
        return None;
    };
    // WI-383: only an OPERATION-type-param projection grounds here (decl_sort = the op). A
    // SORT-type-param projection (decl_sort = a sort) keeps the WI-428 opacity untouched —
    // its grounding rides the existing eliminator path.
    //
    // WI-956 answered this ticket's question — is the gate doing MORE than "the owner is
    // an operation"? It was doing LESS. `kind_of` asks which keyword came FIRST, and an
    // `entity foo(…)` + `operation foo(…)` pair really does register
    // `[Entity, Sort, Operation]` (MEASURED), which `kind_of` reports as `Entity`.
    //
    // A HARDENING, not a fix, and no test claims otherwise: that collision is not a
    // usable program. MEASURED on the fixture — with `entity getV(k: Int64)` beside
    // `operation getV[T](target: T) -> T.V`, the ENTITY wins the call site and the load
    // fails in the entity's own field check (*type mismatch in getV.k (entity-field)*)
    // long before any projection grounds. So the divergence cannot be observed here
    // today; `has_kind` is used because a membership gate should ask the membership
    // question, not because a program noticed. (`kind_of`'s doc: for DISPLAY only.)
    //
    // Switching does not blur the WI-383 split. The op-record lookup two lines down is
    // what decides: a name playing both roles reaches `declared_type_param_var`, which
    // answers `None` unless the OPERATION's BRACKET declares this param — so the split
    // still turns on where the param was declared, never on a registration order.
    if !kb.has_kind(sort, crate::intern::SymbolKind::Operation) {
        return None;
    }
    // The subject `Ref` is a DISTINCT registration of the op type-param from the canonical
    // inference var the call binds (an op type-param has no `SortAlias`, so
    // `walk_type(subject)` lands on an unbound sibling var). Go to the op's own
    // `OperationInfo.type_params`, whose var IS the one arg-inference binds — the same
    // authority [`type_param_global_var`] consults for a written occurrence (WI-943).
    //
    // WI-954 PUBLISHED THAT VARIABLE AND THIS SITE STILL DOES NOT READ THE MAP, because
    // the question here is not "what does this parameter denote" but "is it the
    // OPERATION'S BRACKET that declared it" — the WI-383 split. The map is keyed by the
    // parameter's symbol, and a symbol playing both the `Sort` and `Operation` roles
    // owns one scope, so a scope-keyed read cannot separate the sort body's
    // `sort T = ?` from the operation's `[T]`; nor would it answer `None` for WI-402's
    // existential carrier, which is op-scoped but is not a bracket parameter. See
    // [`op_info::declared_type_param_var`](crate::kb::op_info::declared_type_param_var).
    let Value::Term { id: subj_t, .. } = subject else {
        return None;
    };
    let subj_sym = extract_sort_ref_sym(kb, &TermIdView(subj_t))?;
    let subj_name = kb.local_name_of(subj_sym).to_owned();
    let tp_var = crate::kb::op_info::declared_type_param_var(kb, sort, &subj_name)?;
    let tp_var = type_param_var_term(kb, tp_var);
    // WI-394: walk to a `Value` so a non-`Term` (`Value::Node`) subject fill is
    // seen through the view; a `Node` that is not a concrete `sort_ref` yields
    // `None`, keeping the projection the abstract neutral (as a bare var did).
    let walked = walk_term_to_resolved(kb, subst, tp_var);
    // A genuine concrete sort only: never a sort-type-param (abstract carrier → forward),
    // and not an operation / other kind. WI-956 gave that test its one owner, shared with
    // `filled_carrier_sort` which asked it in the same two lines.
    let s = genuine_concrete_sort(kb, extract_sort_ref_sym(kb, &walked)?)?;
    // SOUND grounding (WI-383 /code-review): read `member` ONLY through a spec that
    // LICENSES this projection — an op `requires Spec[C = subject]` clause that declares
    // `member` and mentions the subject — AND that the carrier `s` actually PROVIDES; then
    // read `member`'s binding from THAT provision. NOT the spec-agnostic
    // `project_type_member` first-match over the carrier's provides: that read the member
    // off an arbitrary (possibly UNLICENSED) provided spec and made the result depend on
    // `provides` declaration order (two soundness holes). A carrier that does not provide
    // the licensing spec leaves the projection the opaque neutral — the requirement is
    // unmet and the call is rejected downstream, never silently ground to a wrong member.
    let member_str = kb.local_name_of(member).to_owned();
    let key = subject_key_of_term(kb, subj_t)?;
    let mut mentions_subject = false;
    for e in op_requires_entries(kb, sort) {
        if !spec_mentions_key(kb, &e.spec, key) {
            continue;
        }
        mentions_subject = true;
        if !kb
            .type_params_of_sort(e.required_sort)
            .iter()
            .any(|d| d.as_str() == member_str)
        {
            continue;
        }
        let Some(bindings) = provider_spec_view_bindings(kb, s, e.required_sort) else {
            continue;
        };
        let Some(bound) = bindings
            .iter()
            .find(|(n, _)| kb.local_name_of(*n) == member_str)
            .map(|(_, b)| *b)
        else {
            continue;
        };
        // WI-391: the provider binding is the canonical `Ref(S)` shape, so the grounded
        // member walks directly (the late nullary-`Fn` normalization is retired).
        return Some(walk_type_deep(kb, subst, bound));
    }
    // WI-383 SELF-CARRIER (implicit licensing): no `requires` bound mentions the subject,
    // so the projection is self-licensed — `T.member` reads the carrier's OWN declared
    // `sort <member>` (the resource-declares-its-value-type tie). Ground only a MANIFEST
    // member (`sort V = Int64`, whose SortAlias target is a concrete sort); an abstract
    // `sort V = ?` (target a Var) or a carrier lacking the member stays the neutral
    // (rejected downstream). Gated on `!mentions_subject` so an EXTERNAL licensing bound
    // the carrier failed to provide is NEVER bypassed by reading the carrier's own member
    // (the Q3 soundness rule).
    if !mentions_subject {
        let member_qn = format!("{}.{}", kb.qualified_name_of(s).to_owned(), member_str);
        if let Some(member_sym) = kb.symbols.by_qualified_name.get(&member_qn).copied() {
            // Must be the carrier's OWN declared abstract-sort member (`sort <member> = …`):
            // a Sort symbol with an EXACT `SortAlias`. A name-directed pass is deliberately
            // NOT consulted here — it would return an UNRELATED sort's same-named member when
            // this child is an entity/operation/body-sort that merely shares the name (a
            // soundness hole); WI-956 deleted the one that existed, so [`resolve_sort_alias`]
            // now matches only this symbol for every caller.
            if kb.kind_of(member_sym) == Some(crate::intern::SymbolKind::Sort) {
                if let Some(target) = resolve_sort_alias(kb, member_sym) {
                    let g = walk_type_deep(kb, subst, target);
                    // Ground ONLY a manifest member (`sort V = Int64`). An abstract
                    // `sort V = ?` (resolves to a Var) or a sibling-param alias
                    // (`sort V = W`, resolves to a sort-param ref) is NOT ground and stays
                    // the neutral (rejected downstream).
                    if type_value_is_ground(kb, g) {
                        // WI-391: the SortAlias target is the canonical `Ref(S)` shape
                        // (`type_expr_to_value`), so the manifest member grounds directly.
                        return Some(g);
                    }
                }
            }
        }
    }
    None
}

/// Walk a type term through the substitution, resolving Vars and type params.
///
/// Iterative (not recursive) so a CYCLIC substitution cannot overflow the host
/// stack. A cycle arises (WI-416) when two distinct `Var` instances of the
/// SAME sort-parameter cross-bind — e.g. typing `member(x, items)` from inside
/// a sort whose element unifies with `List.T` can leave `subst[a] = Var(b)`,
/// `subst[b] = Ref(Coll.T)`, and `SortAlias(Coll.T) = Var(a)`, so the chain
/// `a -> Ref -> a` never terminates. Every var in such a cycle is unified to
/// the same (here abstract) type, so on revisiting a var we stop and return the
/// current term — a sound representative of the equivalence class. The
/// `visited` set is a stack-local `SmallVec`; the overwhelmingly common chain
/// is 0–2 hops, so it never allocates and the linear `contains` is trivial.
pub(super) fn walk_type(kb: &KnowledgeBase, subst: &Substitution, ty: TermId) -> TermId {
    let mut ty = ty;
    // 0–2 hops in practice; inline-4 never spills for any realistic alias chain.
    let mut visited: SmallVec<[VarId; 4]> = SmallVec::new();
    loop {
        if let Term::Var(Var::Global(vid)) = kb.get_term(ty) {
            let vid = *vid;
            if visited.contains(&vid) {
                return ty; // WI-416: cycle — `ty` is a representative.
            }
            match subst.resolve_as_value(vid) {
                Some(Value::Term { id: bound, .. }) => {
                    visited.push(vid);
                    ty = *bound;
                    continue;
                }
                // Non-`Term` (a denoted `Value::Node`) or unbound: keep the var.
                // This term-only walker deliberately stops here; its carrier-aware
                // caller `walk_term_to_resolved` surfaces a `Value::Node` binding
                // afterward via `resolve_as_value`.
                _ => return ty,
            }
        }
        // WI-361: a bare sort is `Ref(S)` (term backing) or `sort_ref(name: Ref(S))`
        // (deep); `extract_sort_ref_sym` recognizes both. Any other shape (a
        // parameterized / arrow / non-type term) is left unchanged.
        let sym = match extract_sort_ref_sym(kb, &TermIdView(ty)) {
            Some(s) => s,
            None => return ty,
        };
        // Only resolve the sort ref through its SortAlias-to-Var if the symbol is
        // a *sort-level type parameter* (registered via `sort T = ?` inside a sort
        // body). Top-level abstract sorts like `sort Term = ?` in anthill.reflect
        // also have a SortAlias-to-Var entry, but they're concrete-but-opaque types
        // from a typer perspective — collapsing every `sort_ref(Term)` into Term's
        // alias Var would lose the sort-ref form and surface as `TermId(N)` in
        // diagnostics.
        if !is_sort_param_symbol(kb, sym) {
            return ty;
        }
        let alias_target = match resolve_sort_alias(kb, sym) {
            Some(t) => t,
            None => return ty,
        };
        let Term::Var(Var::Global(vid)) = kb.get_term(alias_target) else {
            return alias_target;
        };
        let vid = *vid;
        if visited.contains(&vid) {
            return alias_target; // WI-416: cycle — the alias var represents it.
        }
        match subst.resolve_as_value(vid) {
            // Term-narrow (term-world alias chase): only a `Value::Term` binding
            // is a `TermId` this loop can chase; a non-`Term` carrier (a `Value::Node`
            // effect-row/occurrence binding) is not representable here, so the alias
            // var represents it — as before.
            Some(Value::Term { id: bound, .. }) => {
                let bound = *bound;
                visited.push(vid);
                ty = bound;
                continue;
            }
            _ => return alias_target,
        }
    }
}

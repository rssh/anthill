//! Spec member and override signature checks: member signatures, override refinement,
//! modify targets, effect registration and written row bindings.

use super::*;

/// WI-20260822-1MAGR — DOES THE CARRIER'S OWN MEMBER FIT THE SPEC OPERATION IT
/// CLAIMS TO IMPLEMENT? Arity, parameter types (and so their ORDER), and the
/// return type, with the provision's σ applied to the spec's declaration.
///
/// Until this check, a provision certified that a member of that NAME exists and
/// nothing more (kernel-language.md §8.7, WI-935, measured): `fact
/// VectorSpace[Vec3, Float]` loaded clean with `vec_add` at one argument, with
/// `vec_sub` returning `Float`, or with `vec_scale`'s two parameters swapped, and
/// each then mis-dispatched or died at the call. WI-20260822-59CDQ compared the
/// return type in ONE place — where a contract clause's `result` binder is what
/// discharges it — and deliberately stopped there; this is the general question it
/// handed on.
///
/// # The gate: the member must be the SOLE BACKING
///
/// The comparison runs only where the spec operation has no implementation of its own
/// that would back this carrier — a default body or a resolver builtin, which is
/// [`op_backed`]'s own spec-op predicate and NOT the wider [`op_is_executable`] (see
/// the gate's comment for why the host-mapping leg is excluded). That is not a cost
/// dodge — it is the line between two different programs, and the whole corpus
/// separates on it:
///
///   * The spec supplies NOTHING. The member is the only thing that can back the
///     operation; there is no other implementation for it to be distinct FROM, and
///     if it does not fit, the provision's claim is simply false. Nothing else in
///     the loader would ever say so.
///   * The spec supplies its own implementation. A same-named member of a
///     different signature is then a DISTINCT operation, and the default is what
///     backs the provision — the reading §8.7 already gives the `requires`
///     direction (WI-1048: "different arity, a different parameter type, a
///     different return type ⇒ distinct operations by construction"), and a call
///     that expected the spec's shape is already a loud type error naming both
///     types. Refusing here would instead overturn two decided rules: WI-1125's
///     `operation neq() -> Bool` beside `provides PartialEq[T = Color]` ("a 0-ary
///     member is not `PartialEq.neq` under any reading, so it supplies nothing and
///     the program is fine") and its witness twin `neq(a: Int64, b: Int64)`, both
///     of which sit beside the `PartialEq.neq` BUILTIN.
///
/// MEASURED, report-only over the whole corpus + fixture suite — 1152 distinct
/// (carrier, spec, op) pairs across 999 carriers. The comparison flagged 67 of them
/// and every one was a legitimate program; the two decidability gates below account
/// for 56 (42 self-receiver parameters, 14 projection-carrying return types), leaving
/// 11. The SOLE-BACKING gate splits those 11 exactly, with no crossings:
///   * the 3 beside an executable spec operation are precisely the programs the
///     language had already decided must load — `wi1125.nullary`,
///     `wi1125.witnessunrelated`, `wi1042.nonparametric`;
///   * the 8 beside a body-less one are all deliberate mismatch fixtures: six in
///     `wi347_override_refinement_test`, and `p3_spec_wrong_sig.anthill` /
///     `p7_sig_and_row.anthill` in `docs/measurements/guardians/`, the two probes
///     that RECORDED this gap as C1 of that example's `measured.md`.
///
/// # What is not compared, and why each is undecidable rather than excused
///
///   * THE SELF-RECEIVER PARAMETER. A spec that types a parameter as ITSELF
///     (`splitFirst(s: Stream)`) is naming the dispatch receiver, and an override
///     narrows it to the carrier (`splitFirst(xs: List)`). Contravariance would
///     refuse every one of them; dispatch is what makes the narrowing sound, since
///     the receiver is the carrier by construction. Recognised structurally — the
///     spec side's sort functor IS the spec, the member side's IS the carrier —
///     never by position: `test.wi596.Bag.holds(x: T, b: Bag)` puts it second.
///   * A TYPE CARRYING AN EXPRESSION PROJECTION (`s.T`, WI-376). σ binds the
///     spec's TYPE PARAMETERS; it cannot ground a projection off the operation's
///     own parameter, and the two operations' receivers are different parameters,
///     so `Stream.splitFirst`'s `s.T` and `List.splitFirst`'s `xs.T` are two
///     distinct neutrals that [`types_compatible`] refuses (`expr_carried_zeta`:
///     "a neutral projection is equal only to an identical neutral"). Deciding
///     these needs the receiver-relative alignment WI-461/WI-474 do at a CALL, not
///     a σ over type parameters.
///   * A NON-GROUND PAIR — the fail-open [`instance_binding_type_ok`] already
///     applies, so a higher-kinded or unbound parameter is not judged. GROUND IS A
///     PROPERTY OF THE TYPE, NOT OF ITS CARRIER: a type carrying a literal argument
///     (`Foo[T = Int64, N = 3]`) rides the occurrence carrier and IS judged, with σ
///     applied beneath it (WI-20260923-Z1Q8B — until then every such pair failed open).
///
/// PARAMETER ORDER IS A PARTIAL CHECK AND SAYS SO. It is decidable only where the
/// types differ: `f(a: Int64, b: Int64)` written in either order is the same
/// signature, so a swap there is invisible and no message claims otherwise. Where
/// the types do differ, a permutation that WOULD fit is reported as an order
/// mistake rather than as N unrelated parameter mismatches, because that is the
/// repair.
///
/// THE POPULATION is [`check_override_refinement`]'s own: the provision's declaring
/// sort's OWN declared member of the spec operation's short name. That includes a
/// WITNESS sort's members (the declaring sort is the witness, and σ still binds the
/// spec's parameter to the carrier the provision names), and it excludes two things
/// that have their own owners — an instance fact's op-valued BINDING, which
/// [`check_instance_fact_op_signatures`] compares, and a member [`op_backed`] reaches
/// only by qualified name rather than through the sort's own-op list.
///
/// ONE REFUSAL PER MEMBER, and the legs are checked in shape order — arity, then
/// parameters, then the return. Arity short-circuits because a per-position
/// comparison across two different arities pairs unrelated parameters and reports
/// noise; the parameter leg short-circuits the return because every message here
/// prints BOTH signatures in full, so a second refusal would repeat what the first
/// already showed. (That is the opposite trade from the contract legs beside it,
/// whose messages name a CLAUSE each and so are worth reporting together — see
/// WI-20260822-59CDQ's `a_return_type_refusal_does_not_hide_an_independent_contract_
/// defect`. The contract legs still run and still report, so a member that both
/// mis-fits and weakens a postcondition says both.)
#[allow(clippy::too_many_arguments)]
pub(super) fn check_member_signature(
    kb: &mut KnowledgeBase,
    carrier: Symbol,
    spec: Symbol,
    spec_op: Symbol,
    op_short: &str,
    spec_info: &crate::kb::op_info::OpInfoRecord,
    impl_info: &crate::kb::op_info::OpInfoRecord,
    sigma: &[(Symbol, TermId)],
    errors: &mut Vec<crate::kb::load::LoadError>,
) -> MemberSignature {
    use crate::kb::load::LoadError;
    // THE GATE (see the doc above), asked with [`op_backed`]'s OWN spec-op predicate
    // and not with the general [`op_is_executable`].
    //
    // THE DIFFERENCE IS THE HOST-MAPPING LEG, and it is load-bearing rather than
    // incidental. `op_is_executable` counts an `operation_map` entry, and
    // [`KnowledgeBase::is_host_mapped_op`] is a FLAT SET with no carrier dimension — so
    // a host mapping naming the SPEC's own member says an implementation exists
    // somewhere, never that THIS carrier is realized. That is WI-876's defect A, which
    // is exactly why `op_backed` drops the leg for its spec-op candidate. Asking the
    // wider predicate here would gate the comparison off in the one case where the
    // member really is the only backing: `op_backed` would refuse to count the host
    // mapping for the carrier, and this pass would have skipped the member on the
    // strength of it.
    if kb.is_builtin(spec_op) || op_has_runnable_body(kb, spec_op) {
        return MemberSignature::Alignable;
    }
    // The carrier / spec names are read ONLY on a refusal. This function runs for every
    // (spec op, member) pair of every provision on every load — the stdlib alone carries
    // ~146 provisions — and the overwhelmingly common outcome is that the signatures fit,
    // so nothing above the failure branches allocates.
    let refuse = |kb: &KnowledgeBase, errors: &mut Vec<LoadError>, reason: String| {
        errors.push(LoadError::IncompatibleMemberSignature {
            carrier: kb.qualified_name_of(carrier).to_string(),
            spec: kb.qualified_name_of(spec).to_string(),
            op: op_short.to_string(),
            reason,
        });
    };

    // ── arity ───────────────────────────────────────────────────────────────
    if spec_info.params.len() != impl_info.params.len() {
        let spec_sig = render_op_signature(kb, op_short, spec_info, sigma);
        let impl_sig = render_op_signature(kb, op_short, impl_info, &[]);
        let spec_qn = kb.qualified_name_of(spec).to_string();
        let reason = format!(
            "the spec declares `{spec_sig}` ({} parameter(s)) and the member is `{impl_sig}` ({}), \
             and `{spec_qn}.{op_short}` has no default body and no builtin, so this member \
             is the only thing that could back it for this carrier (a host `operation_map` \
             on the spec's own member does not: it names no carrier)",
            spec_info.params.len(),
            impl_info.params.len()
        );
        refuse(kb, errors, reason);
        return MemberSignature::ArityDiffers;
    }

    // ── parameter types (contravariant: σ(spec) <: member) ──────────────────
    let n = spec_info.params.len();
    let mut bad: Vec<usize> = Vec::new();
    for i in 0..n {
        let (_, spec_pty) = &spec_info.params[i];
        let (_, impl_pty) = &impl_info.params[i];
        if instance_binding_type_ok(kb, spec_pty, impl_pty, sigma, false) != Some(false) {
            continue;
        }
        // THE SELF-RECEIVER, and the projection gate — see the doc above. Both are
        // reached only by a position that has ALREADY compared as incompatible, which
        // is why the canonicalizations sit here rather than above the loop.
        let is_receiver = sort_functor_of_view(kb, spec_pty)
            .is_some_and(|b| kb.canonical_sort_sym(b) == kb.canonical_sort_sym(spec))
            && sort_functor_of_view(kb, impl_pty)
                .is_some_and(|b| kb.canonical_sort_sym(b) == kb.canonical_sort_sym(carrier));
        let carries_projection =
            value_contains_projection(kb, spec_pty) || value_contains_projection(kb, impl_pty);
        if !is_receiver && !carries_projection {
            bad.push(i);
        }
    }
    if !bad.is_empty() {
        // ORDER vs TYPE. A permutation of the member's parameters that WOULD fit
        // says the author wrote them in the wrong order, which is a different
        // repair from "this parameter has the wrong type". Bounded because the
        // search is factorial and a signature past this width is not a swap.
        let permuted = bad.len() >= 2
            && bad.len() <= MEMBER_SIGNATURE_PERMUTATION_LIMIT
            && member_params_are_a_permutation(kb, spec_info, impl_info, sigma, &bad);
        let spec_sig = render_op_signature(kb, op_short, spec_info, sigma);
        let impl_sig = render_op_signature(kb, op_short, impl_info, &[]);
        let reason = if permuted {
            format!(
                "the member's parameters are the spec's in a different ORDER — the spec \
                 declares `{spec_sig}` (at this provision's bindings) and the member is \
                 `{impl_sig}`. (Only decidable where the types differ: two parameters of \
                 the same type in either order are the same signature and are not \
                 reported.)"
            )
        } else {
            let mut ps: Vec<String> = Vec::new();
            for &i in &bad {
                let sub = sigma_subst_type(kb, &spec_info.params[i].1, sigma);
                let want = type_display_name_value(kb, &sub);
                let got = type_display_name_value(kb, &impl_info.params[i].1);
                ps.push(format!(
                    "parameter {} is `{got}` where the spec's is `{want}`",
                    i + 1
                ));
            }
            format!(
                "{} — the spec declares `{spec_sig}` (at this provision's bindings) and the \
                 member is `{impl_sig}`",
                ps.join("; ")
            )
        };
        refuse(kb, errors, reason);
        return MemberSignature::Alignable;
    }

    // ── return type (covariant: member <: σ(spec)) ──────────────────────────
    if instance_binding_type_ok(
        kb,
        &spec_info.return_type,
        &impl_info.return_type,
        sigma,
        true,
    ) == Some(false)
        && !value_contains_projection(kb, &spec_info.return_type)
        && !value_contains_projection(kb, &impl_info.return_type)
    {
        let sub = sigma_subst_type(kb, &spec_info.return_type, sigma);
        let want = type_display_name_value(kb, &sub);
        let got = type_display_name_value(kb, &impl_info.return_type);
        let spec_sig = render_op_signature(kb, op_short, spec_info, sigma);
        let impl_sig = render_op_signature(kb, op_short, impl_info, &[]);
        let reason = format!(
            "the member returns `{got}`, which is not a subtype of the spec's `{want}` — the \
             spec declares `{spec_sig}` (at this provision's bindings) and the member is \
             `{impl_sig}`"
        );
        refuse(kb, errors, reason);
    }
    MemberSignature::Alignable
}

/// WI-20260822-1MAGR — can the legs AFTER [`check_member_signature`] still align the
/// member's parameters to the spec's? They all compare in the spec's vocabulary
/// through a positional `zip`, so the answer is "yes iff the arities agree" — a
/// judgement about the ALIGNMENT and not about whether the signature was refused.
/// `Alignable` is therefore also what a gated-off pair and a same-arity refusal both
/// return.
#[derive(PartialEq, Eq)]
pub(super) enum MemberSignature {
    Alignable,
    ArityDiffers,
}

/// WI-20260822-1MAGR — the widest signature the order leg searches. The search is
/// factorial in the parameter count, and a swap is a two- or three-parameter
/// mistake; past this the message falls back to naming the mismatched positions,
/// which is still the repair.
const MEMBER_SIGNATURE_PERMUTATION_LIMIT: usize = 6;

/// WI-20260822-1MAGR — are the member's MISMATCHED parameters the spec's, REORDERED?
/// True when some non-identity permutation of `bad` makes every one of those
/// positions fit. Used only to choose the diagnostic; the refusal itself is already
/// decided by the positional pass.
///
/// OVER `bad`, NOT OVER ALL n. The positions the positional pass EXEMPTED — the
/// self-receiver, a projection-carrying type — never fit positionally, so a search
/// over the whole list would answer `false` for any signature that has one and report
/// a genuine swap of two later parameters as two unrelated type mismatches. Searching
/// the mismatched positions alone asks the question the message wants: are these the
/// same types, in the wrong places?
fn member_params_are_a_permutation(
    kb: &mut KnowledgeBase,
    spec_info: &crate::kb::op_info::OpInfoRecord,
    impl_info: &crate::kb::op_info::OpInfoRecord,
    sigma: &[(Symbol, TermId)],
    bad: &[usize],
) -> bool {
    let mut idx: Vec<usize> = (0..bad.len()).collect();
    permutations_any(&mut idx, 0, &mut |perm: &[usize]| {
        if perm.iter().enumerate().all(|(i, &j)| i == j) {
            return false;
        }
        (0..bad.len()).all(|i| {
            instance_binding_type_ok(
                kb,
                &spec_info.params[bad[i]].1,
                &impl_info.params[bad[perm[i]]].1,
                sigma,
                false,
            ) != Some(false)
        })
    })
}

/// Depth-first permutation search: calls `f` on each permutation of `idx` and stops
/// at the first `true`. Sole consumer [`member_params_are_a_permutation`].
fn permutations_any(idx: &mut Vec<usize>, k: usize, f: &mut dyn FnMut(&[usize]) -> bool) -> bool {
    if k == idx.len() {
        return f(idx);
    }
    for i in k..idx.len() {
        idx.swap(k, i);
        if permutations_any(idx, k + 1, f) {
            idx.swap(k, i);
            return true;
        }
        idx.swap(k, i);
    }
    false
}

/// WI-20260822-1MAGR — render one operation's declared signature for a diagnostic:
/// `vec_scale(c: Float, v: Vec3) -> Vec3`. `sigma` is the provision's type-parameter
/// binding, so the SPEC side is printed as the author of the provision would have to
/// write it (`-> Vec3`, not `-> V`); pass an empty σ for the member's own side.
fn render_op_signature(
    kb: &mut KnowledgeBase,
    short: &str,
    info: &crate::kb::op_info::OpInfoRecord,
    sigma: &[(Symbol, TermId)],
) -> String {
    let mut parts: Vec<String> = Vec::with_capacity(info.params.len());
    for (name, ty) in &info.params {
        let sub = sigma_subst_type(kb, ty, sigma);
        let n = kb.local_name_of(*name).to_string();
        parts.push(format!("{n}: {}", type_display_name_value(kb, &sub)));
    }
    let ret = sigma_subst_type(kb, &info.return_type, sigma);
    format!(
        "{short}({}) -> {}",
        parts.join(", "),
        type_display_name_value(kb, &ret)
    )
}

/// WI-347 — operation-override refinement check. A carrier's own operation
/// that implements/overrides a spec operation (own-op-beats-inherited, §8.7)
/// must REFINE the spec op: effects no wider, precondition no stronger,
/// postcondition no weaker. The soundness twin of the provider/call-site
/// checks — a caller programs against the SPEC's contract, so an override that
/// raises an effect the spec doesn't cover (or strengthens a precondition /
/// weakens a postcondition) would surprise it.
///
/// EFFECTS: `∀ ie ∈ impl_effects. ∃ se ∈ spec_effects[σ]. ie <: se`
/// (`types_compatible`, the relation `spec-instance-dispatch.md §"Effect
/// compatibility"` specifies). Decided PER ATOM, wherever the atom is decidable —
/// it mentions no type parameter, on either carrier (WI-20260822-1TKN0: a denoted
/// `Modify[c]` names a place and is compared). A parametric atom (`effects E`)
/// fails open alone, which keeps the stdlib's polymorphic-effect providers from
/// false-positiving while still catching a ground effect-widening (the doc's
/// `Network`-vs-`Error` case). σ grounds the spec row first, on either carrier
/// ([`sigma_subst_type`], WI-20260923-Z1Q8B). The contract (`requires`/`ensures`)
/// legs and the member-signature check ([`check_member_signature`]) run on this
/// same pass.
pub fn check_override_refinement(kb: &mut KnowledgeBase) -> Vec<crate::kb::load::LoadError> {
    use crate::kb::load::LoadError;
    // WI-20260822-1TKN0 — the frame-condition marker, resolved once for the whole
    // walk rather than per effect label (see [`effect_is_modify`]).
    let modify_sym = kb.try_resolve_symbol("anthill.prelude.Modify");
    // Own declared ops per sort — owned snapshot, no `kb` borrow held in the loop.
    let own: std::collections::HashMap<Symbol, Vec<Symbol>> =
        crate::kb::load::sorts_and_own_ops(kb).into_iter().collect();
    let short = |kb: &KnowledgeBase, s: Symbol| -> String {
        kb.qualified_name_of(s)
            .rsplit('.')
            .next()
            .unwrap_or("")
            .to_string()
    };

    // Snapshot provisions before the (mutating) refinement walk:
    // (carrier, spec base, σ = spec type-param symbol → provision binding value).
    struct Prov {
        carrier: Symbol,
        spec: Symbol,
        sigma: Vec<(Symbol, TermId)>,
    }
    let provs: Vec<Prov> = provides_rows(kb)
        .map(|row| {
            // The view's RAW named arguments, not `row.bindings` — see [`spec_param_sigma`].
            let named: &[(Symbol, TermId)] = match kb.get_term(row.spec_view) {
                Term::Fn { named_args, .. } => named_args,
                _ => &[],
            };
            Prov {
                carrier: row.provider,
                spec: row.spec_base,
                sigma: spec_param_sigma(kb, row.spec_base, named),
            }
        })
        .collect();

    let mut errors = Vec::new();
    for p in &provs {
        let (Some(spec_ops), Some(carrier_ops)) = (own.get(&p.spec), own.get(&p.carrier)) else {
            continue;
        };
        for &spec_op in spec_ops {
            let sn = short(kb, spec_op);
            // The carrier's own op of the same short name is its override/impl.
            let Some(&impl_op) = carrier_ops.iter().find(|&&o| short(kb, o) == sn) else {
                continue;
            };
            let Some(spec_info) = crate::kb::op_info::lookup_operation_info(kb, spec_op) else {
                continue;
            };
            let Some(impl_info) = crate::kb::op_info::lookup_operation_info(kb, impl_op) else {
                continue;
            };

            // WI-20260822-1MAGR — THE MEMBER'S SIGNATURE, before the legs below.
            //
            // AND AN ARITY MISMATCH ENDS THE PAIR, which is not tidiness. Every leg
            // below compares in the SPEC'S PARAM VOCABULARY via `param_align`, and that
            // alignment is a positional `zip` of the two parameter lists — across two
            // different arities it pairs unrelated parameters and leaves the impl's
            // surplus ones unaligned, so a clause the override restates VERBATIM stops
            // matching. MEASURED (/code-review): spec `describe(a: T, b: Int64) requires
            // posi(b)` against member `describe(b: Int64) requires posi(b)` reported the
            // signature AND "it strengthens the precondition — the override `requires` a
            // condition the spec operation does not", which is false; the override
            // strengthens nothing. At EQUAL arity the alignment is sound whatever the
            // types are, so a parameter-type or return-type refusal does NOT end the
            // pair — the contract legs still run and still report beside it, which is
            // WI-20260822-59CDQ's "report beside, not instead".
            if check_member_signature(
                kb,
                p.carrier,
                p.spec,
                spec_op,
                &sn,
                &spec_info,
                &impl_info,
                &p.sigma,
                &mut errors,
            ) == MemberSignature::ArityDiffers
            {
                continue;
            }

            // ── the result binder, and the return type it commits to ───────
            //
            // The RESULT BINDER needs the same alignment as a parameter, and for
            // the same reason. `result` is defined per operation as `<op>.result`
            // (proposal 041), so the spec's and the override's are DIFFERENT
            // symbols. Without this the contract legs below compare
            // `Spec.op.result` against `Impl.op.result`, they never match, and
            // **a spec operation carrying `ensures` has no possible provider** —
            // an override restating the spec's postcondition VERBATIM was refused.
            // Measured on `examples/guardians`, whose task spec wants
            // `ensures mentions_all(result)`.
            //
            // GATED ON A CLAUSE EXISTING. Two qualified-name lookups per
            // (spec-op, impl-op) pair on every load is not free — the stdlib alone
            // carries ~146 provisions — and an op pair with no contract clauses can
            // never read this entry. The disjuncts are the two legs' own driving
            // lists: the postcondition leg iterates the SPEC's `ensures`, the
            // precondition leg the IMPL's USER `requires`, so an impl `ensures`
            // beside a spec that declares none is compared against nothing and does
            // not put this gate up.
            //
            // `user_precondition_clauses`, NOT the raw list — the loader injects an
            // `EffectsRuntime[Effects = E]` clause into `requires` for every free
            // effect-row variable (`infer_effects_row_requires`), so the raw list is
            // non-empty for every effect-polymorphic override whether or not its
            // author wrote a contract. Reading it raw opened this gate on most of the
            // stdlib and made the cost sentence above false. Asked with `any` rather
            // than by building the filtered Vec, since only emptiness is wanted here.
            //
            // WI-20260822-1TKN0 — THE EFFECTS LEG IS A THIRD READER, and the
            // sentence above ("an op pair with no contract clauses can never read
            // this entry") was false the moment that leg started aligning a denoted
            // label: `Modify[result]` NAMES the binder. `MutableStack.new` over
            // `MutableCollection.new` is exactly that pair — two `Modify[result]`
            // rows, not one contract clause between them — and it was refused for
            // restating the spec's own effect verbatim.
            //
            // Its OWN driving condition, not a restatement of the contract legs':
            // does the row this leg rewrites carry a target that is a PLACE? Only
            // the IMPL row is ever aligned, so only it is asked. Structural, and it
            // touches no symbol table, so the cost sentence above still holds.
            let wants_result_alignment = !spec_info.ensures.is_empty()
                || impl_info
                    .requires
                    .iter()
                    .any(|c| !is_effects_runtime_clause(kb, c))
                || impl_info.effects.iter().any(|e| view_bears_denoted(kb, e));
            // WI-20260822-1TKN0 — the spec-side SYMBOL rides beside its `Ref` term
            // because the effects leg now aligns a `Value::Node` label too, and the
            // occurrence rewrite is keyed `Symbol → Symbol` (it rebuilds
            // `Expr::Ref` leaves, which hold a symbol, not a `TermId`). Read off
            // the SAME `resolve_op_result_sym` pair that builds the term entry, so
            // the two spellings of one alignment cannot drift apart.
            let mut result_binders: Option<(Symbol, TermId)> = None;
            let mut result_binder_syms: Option<(Symbol, Symbol)> = None;
            if wants_result_alignment {
                match (
                    crate::kb::region::resolve_op_result_sym(kb, spec_op),
                    crate::kb::region::resolve_op_result_sym(kb, impl_op),
                ) {
                    (Some(sr), Some(ir)) if ir != sr => {
                        // `find_term`, not `alloc`: this only NAMES a term the
                        // symbol table already holds alive, and the entry rides in
                        // a local dropped each iteration with no decref, so `alloc`
                        // would leak a refcount per pair.
                        let sr_ref = if let Some(t) = kb.find_term(&Term::Ref(sr)) {
                            t
                        } else {
                            kb.alloc(Term::Ref(sr))
                        };
                        result_binders = Some((ir, sr_ref));
                        result_binder_syms = Some((ir, sr));
                    }
                    (Some(_), Some(_)) => {}
                    // NOT a silent skip. Every operation gets a `result` binder at
                    // scan time, so a miss here means the symbol was minted under a
                    // different prefix than the op's qualified name, or lost its
                    // `OpResult` kind. The consequence is the pre-fix bug verbatim —
                    // every provider of an `ensures`-carrying spec op refused — with
                    // nothing naming the cause, so say it.
                    (s_r, i_r) => debug_assert!(
                        false,
                        "override refinement: no OpResult binder for {} (spec: {:?}, impl: {:?}); \
                         contract clauses over `result` cannot be compared and every \
                         provider of this spec op will be refused",
                        kb.qualified_name_of(spec_op),
                        s_r.is_some(),
                        i_r.is_some(),
                    ),
                }
            }

            // Impl-param → spec-param alignment, shared by the effects leg and
            // the contract legs below. A GUARDED effect atom's guard is a
            // predicate over the op's own params (`Error[EmptyStream] :-
            // isEmpty(xs)`), so without the alignment an override restating the
            // spec's own guarded row verbatim — modulo its param name — read as
            // a widening and was refused (WI-818: `List.head` vs `Stream.head`,
            // the first carrier override to carry one).
            //
            // WI-20260822-1TKN0: built in TWO spellings from ONE walk — the
            // `TermId`-valued map the hash-consed rewrite takes, and the
            // `Symbol → Symbol` map the occurrence rewrite takes. Same pairs, same
            // loop, so a param that aligns on one carrier aligns on the other.
            let mut param_align_syms: HashMap<Symbol, Symbol> = HashMap::new();
            let param_align: Vec<(Symbol, TermId)> = {
                let mut a = Vec::new();
                for ((ip, _), (sp, _)) in impl_info.params.iter().zip(spec_info.params.iter()) {
                    if ip != sp {
                        let sp_ref = kb.alloc(Term::Ref(*sp));
                        a.push((*ip, sp_ref));
                        param_align_syms.insert(*ip, *sp);
                    }
                }
                a
            };
            // WI-20260919-N31XX (proposal 065 §3) — AND THE TWO OPERATIONS' TYPE
            // PARAMETERS ALIGN TOO, for exactly the reason their VALUE parameters do.
            //
            // The legs below compare clauses by carrier-agnostic STRUCTURAL equality, and
            // an operation's type parameter is its own logical variable (`load.rs`: "an op
            // type-param is its own logical variable, distinct from any same-named outer
            // sort parameter"). So `Desc.f.B` and `Leaf.f.B` are two different symbols, and
            // without this an override RESTATING the spec's clause verbatim —
            // `requires Eq[T = B]` on both sides — read as an ADDITION and was refused as
            // "it strengthens the precondition". MEASURED by WI-20260919-BQHGD's probe,
            // which pinned that over-refusal as today's behaviour; a GROUND restatement
            // (`Eq[T = Int64]`) always loaded, because hash-consing gives both sides one
            // `TermId`, which is what made the gap look like an absence rather than a bug.
            //
            // IT IS 065 §3 THAT MAKES THIS LOAD-BEARING rather than a nicety. An
            // implementation must be able to restate `requires TypeValue[T = B]` to read
            // `B` at all — that is the whole of "a spec that wants its implementations to
            // inspect `B` must say so in the spec". Without the alignment no implementation
            // could ever restate it, so the subset rule would admit nothing and the
            // parametricity rule would have no legal spelling.
            //
            // KEYED ON THE OP-SCOPED SYMBOL, not on `OpInfoRecord::type_params`' own
            // `Symbol`. That field holds the BARE interned name (`B`), while a clause
            // reference resolves to the op-scoped `<ns>.<op>.B` — the symbol
            // `substitute_impl_params_alloc` will be matching against. Keying on the bare
            // name would make every substitution a silent no-op, the same failure σ's own
            // comment records above.
            //
            // ONE CLAUSE SPELLING IS ALIGNED, AND IT IS THE ONLY ONE THAT OCCURS.
            // `substitute_impl_params_alloc` rewrites `Ref` / `Ident` / nullary `Fn` and
            // leaves `Term::Var` alone, while `clause_named_type_param` documents a SECOND
            // spelling — a bare `Var::Global`, which is how a row TAIL arrives. MEASURED
            // rather than assumed: a `debug_assert` refusing any impl precondition clause
            // containing a bare `Var` was run over the full workspace and never fired
            // across 7211 tests, so no clause in the corpus uses it. A future one would
            // fail OPEN — the alignment would miss it and the restatement would be refused
            // as an addition, which is a FALSE REFUSAL the author can see and not a silent
            // wrong answer. That is why this ships keyed on the symbol spelling rather than
            // growing a `Var`-aware rewrite for a shape nothing produces.
            //
            // AN ARITY MISMATCH ALIGNS NOTHING, for the reason the VALUE-parameter guard
            // above gives at length: a positional `zip` across two different arities pairs
            // unrelated parameters. There is no `continue` here to match the value side's,
            // because differing TYPE arity is not itself a signature refusal today; the
            // conservative answer is to align nothing and let the clause comparison fall
            // where it falls.
            //
            // ONE WALK, TWO SPELLINGS, like `param_align` above — the `TermId`-valued map
            // the hash-consed clause rewrite takes and the `Symbol → Symbol` map the
            // occurrence rewrite takes, built from the same pairs so they cannot disagree.
            let type_param_pairs: Vec<(Symbol, Symbol)> = {
                let mut pairs = Vec::new();
                if impl_info.type_params.len() == spec_info.type_params.len() {
                    let impl_scope = kb.symbols.scope_id(impl_op);
                    let spec_scope = kb.symbols.scope_id(spec_op);
                    for ((ip, _), (sp, _)) in impl_info
                        .type_params
                        .iter()
                        .zip(spec_info.type_params.iter())
                    {
                        // `None` is not a skipped case worth reporting: `type_param_sym`
                        // reads the set `add_type_param` filled, so a parameter it does not
                        // know is one no clause reference could have resolved to either.
                        if let (Some(i), Some(s)) = (
                            kb.symbols.type_param_sym(impl_scope, kb.local_name_of(*ip)),
                            kb.symbols.type_param_sym(spec_scope, kb.local_name_of(*sp)),
                        ) {
                            if i != s {
                                pairs.push((i, s));
                            }
                        }
                    }
                }
                pairs
            };
            let type_param_align: Vec<(Symbol, TermId)> = type_param_pairs
                .iter()
                .map(|(i, s)| {
                    let t = kb.alloc(Term::Ref(*s));
                    (*i, t)
                })
                .collect();

            let full_align: Vec<(Symbol, TermId)> = {
                let mut a = param_align.clone();
                a.extend(type_param_align.iter().copied());
                if let Some(entry) = result_binders {
                    a.push(entry);
                }
                a
            };
            let full_align_syms: HashMap<Symbol, Symbol> = {
                let mut m = param_align_syms.clone();
                // BOTH SPELLINGS OR NEITHER — the invariant `param_align`'s own comment
                // states ("a param that aligns on one carrier aligns on the other"). The
                // effects leg reads this `Symbol → Symbol` map, and a guarded effect row
                // over a type parameter is the same restatement problem as a clause.
                //
                // NO TEST EXERCISES THIS HALF, and that is recorded rather than left to be
                // assumed from its presence: MEASURED, with this one line removed the full
                // workspace runs 7211 tests and 0 failures, exactly as with it. No fixture
                // has a guarded effect row over an operation's own type parameter. It is
                // here because the two maps are one alignment and letting them disagree is
                // how the next such row gets refused for a reason nobody can see — not
                // because anything today needs it. The contract half IS driven, by
                // `restating_the_specs_type_param_clause_loads`.
                m.extend(type_param_pairs.iter().copied());
                if let Some((ir, sr)) = result_binder_syms {
                    m.insert(ir, sr);
                }
                m
            };

            // WI-20260822-59CDQ — THE RETURN TYPES MUST AGREE WHEREVER THE RESULT
            // BINDER IS WHAT DISCHARGES A CLAUSE. Aligning the two binders makes
            // `ensures P(result)` on the spec and `ensures P(result)` on the
            // override compare EQUAL; that is a claim that the two `result`s denote
            // values of the same type, and nothing else on this pass compares return
            // types (kernel-language.md §8.7 — a provision certifies that a member of
            // that NAME exists, not that it fits; enforcing conformance generally is
            // WI-20260822-1MAGR). Without this an op promising `mentions_all(result)`
            // of a `Report` was discharged by one returning `Int64`.
            //
            // THE CONDITION IS THE DISCHARGE ITSELF, not "a clause mentions
            // `result`" — the exact question, asked by running the comparison the
            // legs below run, twice: is there a clause pair that matches WITH the
            // binder aligned and does NOT match without it? Three cases separate
            // only under that reading, and each wants a different message:
            //
            //   * spec `P(result)` / impl `P(result)` — discharged by the alignment
            //     alone, so the return types decide and are what the refusal names.
            //   * spec `P(x)` / impl `P(x)` — matches with or without, so the binder
            //     decides nothing and a differing return type is the general
            //     signature question this pass does not ask (§8.7 / WI-935).
            //   * spec `P(x)` / impl `P(result)` — matches under neither, so the
            //     override genuinely weakens the postcondition; naming the return
            //     types there would send the author to fix the wrong line, since
            //     fixing it would not make the program load.
            //
            // COVARIANT, NOT EQUAL: an override may return a SUBTYPE of the spec's
            // return, and a predicate about a value of the subtype is the same
            // proposition — so the test is `impl_ret <: spec_ret`, the same
            // `types_compatible` direction the effects leg uses.
            //
            // DECIDABLE ONLY, FAIL-OPEN OTHERWISE — the same predicate the effects
            // leg below uses, and for the same reason. (It used to be only the same
            // SHAPE: this gate still read the CARRIER — `Value::Term` plus
            // `!contains_type_param` — after WI-20260822-1TKN0 retired exactly that test
            // from the effects leg, so a return type riding `Value::Node` because it
            // carries a denoted, `Foo[T = Int64, N = 3]`, was skipped as undecidable
            // and a mismatch over it loaded clean. Pinned by
            // `a_denoted_return_type_mismatch_is_compared`.) Refusing needs the
            // two types to be KNOWN incompatible, and treating "cannot decide" as
            // "differs" would re-refuse providers the pass cannot judge. σ is what
            // makes the ordinary parametric case decidable: a spec returning its
            // own parameter (`op(x: T) -> T`) grounds to the provision's binding
            // (`-> Carrier`) before the comparison — on either carrier since
            // WI-20260923-Z1Q8B, so `-> Foo[T = T, N = 3]` grounds to
            // `Foo[T = Carrier, N = 3]` (`a_sigma_bound_denoted_return_type_mismatch_
            // is_compared`); before it σ handed the occurrence carrier back untouched
            // and that return type failed open here. What still fails open is a
            // return type σ does not ground — a parameter the provision binds
            // nothing to, or a higher-kinded one.
            let mut ret_mismatch: Option<(String, String)> = None;
            if result_binders.is_some() {
                let impl_pre = user_precondition_clauses(kb, &impl_info.requires);
                let spec_pre = user_precondition_clauses(kb, &spec_info.requires);
                let discharges = result_binder_discharges(
                    kb,
                    &impl_info.ensures,
                    &spec_info.ensures,
                    &full_align,
                    &param_align,
                ) || result_binder_discharges(
                    kb,
                    &impl_pre,
                    &spec_pre,
                    &full_align,
                    &param_align,
                );
                if discharges {
                    let spec_ret = sigma_subst_type(kb, &spec_info.return_type, &p.sigma);
                    let decidable =
                        |kb: &KnowledgeBase, v: &Value| !view_contains_type_param(kb, v);
                    if decidable(kb, &spec_ret) && decidable(kb, &impl_info.return_type) {
                        let mut subst = Substitution::new();
                        if !types_compatible(kb, &mut subst, &impl_info.return_type, &spec_ret) {
                            ret_mismatch = Some((
                                type_display_name_value(kb, &spec_ret),
                                type_display_name_value(kb, &impl_info.return_type),
                            ));
                        }
                    }
                }
            }

            let align = full_align;
            let align_syms = full_align_syms;

            // ── effects-⊆ (per-atom; fail-open on what cannot be compared) ──
            let spec_effs: Vec<Value> = spec_info
                .effects
                .iter()
                .map(|se| sigma_subst_type(kb, se, &p.sigma))
                .collect();

            // WI-20260822-1TKN0 — DECIDABLE, WHICH IS NOT "HASH-CONSED".
            //
            // This gate used to read `matches!(e, Value::Term { .. })` plus
            // `!contains_type_param(..)` — a CARRIER test where an ABSTRACTNESS test
            // was meant. A denoted effect label (`Modify[c]`) rides a `Value::Node`
            // because it carries an occurrence, not because it is parametric, and
            // reading the carrier conflated the two (the Representation note in
            // CLAUDE.md: a non-hash-consed carrier matches identically). The two
            // questions are now asked apart:
            //
            //   * PARAMETRIC — a row variable / sort parameter can still
            //     instantiate to anything, so nothing about the atom is decided.
            //   * DENOTED — a target that is a PLACE, not a type. `types_compatible`
            //     relates two denoteds by EQUALITY (`unify_denoted_view`), which is
            //     the exact relation for place-vs-place and the WRONG one for
            //     place-vs-resource-TYPE: `Modify[c]` with `c: Cell` refines
            //     `Modify[T = Cell]` (`Cell.set` over `ModifyRuntime.set`, in the
            //     stdlib), and nothing on this pass relates a place to a type.
            //
            // WI-20260823-39AD2 REMOVED THE SECOND ARM OF THIS GATE, and the removal
            // is not "the relation was built" — the relation was found to be
            // UNNECESSARY. A `Modify` over a place facing a `Modify` over a TYPE was
            // undecidable here, and `Cell.set` over `ModifyRuntime.set` was the one
            // shape in the tree that reached it. A `Modify` target is now a PLACE on
            // BOTH sides ([`check_modify_targets`] refuses a type target at its
            // declaration), so the two labels are place-vs-place — which
            // `unify_denoted_view` already relates EXACTLY, after `align_effect_label`
            // rewrites the override's own param name into the spec's vocabulary.
            // MEASURED: `Cell.set` is now accepted BY COMPARISON, and spelling its
            // effect `Modify[value]` (the wrong parameter, same arity, same carrier) is
            // REFUSED — which under the old fail-open loaded clean.
            //
            // THE DELETION IS NOT SEPARATELY PINNABLE BY A FIXTURE, and saying so is the
            // point rather than crediting a neighbour row: the gate needed a spec
            // `Modify` over a TYPE to fire, and that shape no longer loads, so the arm is
            // dead BY CONSTRUCTION. Measured both ways — restoring the two closures
            // beside the refusal leaves `wi347_override_refinement_test` at 37/37 and the
            // stdlib clean, unchanged. What IS pinned is the capability the arm was
            // suppressing: `a_place_target_naming_the_wrong_parameter_is_refused`.
            let decidable = |kb: &KnowledgeBase, e: &Value| !view_contains_type_param(kb, e);

            // A MALFORMED `Modify` BELONGS TO ITS DECLARATION, NOT TO THIS LEG. A target
            // that is not a place is refused by [`check_modify_targets`] where it is
            // written; judging COVERAGE for it here would report a second error whose
            // repair is not the line it names — a spec `Modify[T]` makes the override's
            // honest `Modify[c]` read as a widening, so the author is sent to fix the
            // override that is correct. MEASURED before this skip: the type-target
            // fixture emitted the coverage refusal FIRST and the real error second.
            //
            // Skips the ATOM, not the row — an `Eff2` beside a malformed `Modify` is
            // still judged, the same per-atom scoping WI-20260822-1TKN0 bought.
            let target_keys = ModifyTargetKeys::new(kb);
            let malformed_modify = |kb: &KnowledgeBase, e: &Value| {
                matches!(
                    classify_modify_target(kb, e, modify_sym, &target_keys),
                    Some((_, ModifyTarget::Type)) | Some((_, ModifyTarget::Missing))
                )
            };

            // THE PREMISE FOR REFUSING ANYTHING is that the SPEC row is fully known.
            // A spec effect still carrying a parameter could σ-instantiate to cover
            // an impl effect, so a refusal read off a partly-unknown spec row would
            // refuse a provider this pass cannot judge. A spec atom that is DENOTED
            // is known — it just names a place — so it does not put this gate up.
            //
            // WHAT CHANGED (WI-20260822-1TKN0): the IMPL row is no longer part of
            // that premise. It used to be — the old `confident` demanded EVERY impl
            // effect be ground too — which made one undecidable atom fail-open the
            // WHOLE ROW: an `Eff2` this leg refuses on its own went unreported the
            // moment a `Modify[c]` sat beside it. The fail-open now scopes to the
            // ATOM that earns it, which is what it was always described as doing.
            let spec_row_is_well_formed = !spec_effs.iter().any(|e| malformed_modify(kb, e));
            if spec_row_is_well_formed && spec_effs.iter().all(|e| !view_contains_type_param(kb, e))
            {
                // WI-20260823-39AD2 DELETED A SECOND REFUSAL ARM FROM THIS LOOP, and
                // for the reason its sibling deletion gives: it became unreachable, not
                // satisfied. The arm carried a nicer message for a `Modify` this leg
                // could not COMPARE against a spec row granting none — "the spec
                // operation declares no `Modify` at all". Reaching it required an impl
                // `Modify` that is not `decidable`, i.e. one whose target CONTAINS a type
                // param — which is precisely a non-place target, refused now at its
                // declaration by [`check_modify_targets`]. A lawful `Modify[place]` the
                // spec never granted is `decidable`, so it was always refused by the
                // generic arm below, and still is: `a_modify_target_the_spec_never_
                // granted_is_refused` and `a_modify_on_a_resource_the_spec_did_not_name_
                // is_refused` are that capability, unchanged.
                for ie in &impl_info.effects {
                    if malformed_modify(kb, ie) {
                        continue;
                    }
                    if decidable(kb, ie) {
                        // Compare ALIGNED (spec param vocabulary); DIAGNOSE with the
                        // author's own spelling — the message must quote a guard the
                        // override actually wrote, not one rewritten to the spec's
                        // param names (WI-818 review).
                        let ie_aligned = align_effect_label(kb, ie, &align, &align_syms);
                        let covered = spec_effs.iter().any(|se| {
                            let mut subst = Substitution::new();
                            types_compatible(kb, &mut subst, &ie_aligned, se)
                        });
                        if !covered {
                            errors.push(LoadError::IncompatibleOverride {
                                carrier: kb.qualified_name_of(p.carrier).to_string(),
                                spec: kb.qualified_name_of(p.spec).to_string(),
                                op: sn.clone(),
                                reason: format!(
                                    "the override declares effect `{}`, which is not covered by \
                                     any effect the spec operation declares (effects must not widen)",
                                    type_display_name_value(kb, ie)
                                ),
                            });
                        }
                    }
                    // Otherwise FAIL OPEN, and after WI-20260823-39AD2 exactly ONE
                    // shape is left undecided: an atom still PARAMETRIC — which is now
                    // necessarily a NON-`Modify` label, since a parametric `Modify`
                    // target is refused at its declaration. Driven by
                    // `a_parametric_non_modify_atom_still_fails_open_beside_a_judged_
                    // neighbour`, which had to be written with an `Eff1[T = R]` for
                    // exactly that reason: the parametric `Modify[R]` this arm used to be
                    // reached with no longer loads, so a fixture using one would measure
                    // the declaration refusal and leave this unpinned.
                    //
                    // The place-vs-resource-TYPE arm that used to sit here is GONE,
                    // and not because the missing relation was built: the language
                    // question the two docs disagreed on was settled the other way.
                    // A `Modify` target is a PLACE (kernel-language.md §5.6 — `Env`
                    // maps resource NAMES), `ModifyRuntime.set`'s `effects Modify[T]`
                    // was a stdlib defect rather than a lawful shape this pass could
                    // not judge, and place-vs-place needs no relation beyond the
                    // equality `unify_denoted_view` already gives. See
                    // [`check_modify_targets`].
                    //
                    // STILL OPEN, and NOT this leg's question: nothing at any site
                    // checks `Modifiable[typeof(target)]`, so `Modify[pattern]` on a
                    // `pattern: String` parameter loads clean — the other half of
                    // WI-20260823-39AD2.
                }
            }

            // WI-20260822-59CDQ. The two `result`s denote values of different types,
            // so no clause over `result` may be discharged across them — and
            // reporting that as a weakened postcondition would name the clause the
            // author wrote correctly rather than the signature that makes it
            // undischargeable.
            //
            // REPORTED BESIDE THE CONTRACT LEGS, NOT INSTEAD OF THEM. The legs still
            // run, and still run with the binder ALIGNED — which is what keeps the
            // `result` clause from also reporting as a weakening, the double-report
            // this error exists to replace. What that buys is the independent half:
            // an override that mismatches its return type AND strengthens a
            // precondition, or drops some unrelated spec `ensures`, now says both at
            // once instead of revealing the second only after the first is fixed and
            // the file reloaded.
            if let Some((spec_ret, impl_ret)) = ret_mismatch {
                errors.push(LoadError::IncompatibleOverride {
                    carrier: kb.qualified_name_of(p.carrier).to_string(),
                    spec: kb.qualified_name_of(p.spec).to_string(),
                    op: sn.clone(),
                    reason: format!(
                        "the contract clause it restates from the spec is one over `result`, \
                         and it returns `{impl_ret}` where the spec operation returns \
                         `{spec_ret}` — a condition promised about `{spec_ret}` is not \
                         discharged by one about `{impl_ret}`"
                    ),
                });
            }

            // ── contract refinement (requires/ensures, structural subset) ───
            // Compare in the spec op's param vocabulary via the shared `align`
            // (contracts are predicates over op params, not the spec
            // type-param, so σ is not applied). The loader's auto-
            // `EffectsRuntime` requires are filtered out — those are the
            // effects check's concern. Conservative: clauses match by
            // carrier-agnostic structural equality (`views_structurally_equal`;
            // for the ground clauses here == hash-consed `TermId` equality); a
            // logically-equivalent but syntactically-different refinement is not
            // yet recognized (a future SMT-backed entailment check would subsume
            // this).
            // precondition no-stronger: every impl precondition must be one the
            // spec also requires (the override demands no more than the spec).
            let spec_pre = user_precondition_clauses(kb, &spec_info.requires);
            for ic in user_precondition_clauses(kb, &impl_info.requires) {
                let ic = substitute_clause(kb, &ic, &align);
                if !spec_pre
                    .iter()
                    .any(|sp| views_structurally_equal(kb, sp, &ic))
                {
                    errors.push(LoadError::IncompatibleOverride {
                        carrier: kb.qualified_name_of(p.carrier).to_string(),
                        spec: kb.qualified_name_of(p.spec).to_string(),
                        op: sn.clone(),
                        reason: "it strengthens the precondition — the override `requires` a \
                                 condition the spec operation does not"
                            .to_string(),
                    });
                }
            }
            // postcondition no-weaker: every spec postcondition must be one the
            // impl also ensures (the override promises no less than the spec).
            let impl_post: Vec<Value> = impl_info
                .ensures
                .iter()
                .map(|c| substitute_clause(kb, c, &align))
                .collect();
            for sc in &spec_info.ensures {
                if !impl_post
                    .iter()
                    .any(|ip| views_structurally_equal(kb, ip, sc))
                {
                    errors.push(LoadError::IncompatibleOverride {
                        carrier: kb.qualified_name_of(p.carrier).to_string(),
                        spec: kb.qualified_name_of(p.spec).to_string(),
                        op: sn.clone(),
                        reason: "it weakens the postcondition — the override does not `ensure` a \
                                 condition the spec operation promises"
                            .to_string(),
                    });
                }
            }
        }
    }
    errors
}

/// WI-20260823-39AD2 — unwrap an effect-row element down to its LABEL.
///
/// An element of an operation's effect list is the bare label in the common case, but
/// the row algebra also admits wrappers that carry their own functor: `guarded(label,
/// guard)` for `{E :- g}` (WI-478 / proposal 048) and `absent(label)` for `-E` (WI-327).
/// A predicate asked directly on the element therefore answers about the WRAPPER. Peels
/// repeatedly, since nothing forbids nesting, and returns the element unchanged when it
/// is already a label.
pub(super) fn peel_effect_atom(kb: &KnowledgeBase, e: &Value, label_key: Symbol) -> Value {
    let mut cur = e.clone();
    // Bounded by the row's own depth; the loop terminates because each step descends
    // into a strictly smaller child.
    loop {
        let is_wrapper = matches!(
            resolved_functor_name(kb, &cur),
            Some("guarded") | Some("absent") | Some("present")
        );
        if !is_wrapper {
            return cur;
        }
        match named_child_value(kb, &cur, label_key) {
            Some(inner) => cur = inner,
            // A wrapper with no `label` child is malformed; return it so the caller
            // judges what it can see rather than silently dropping the atom.
            None => return cur,
        }
    }
}

/// WI-20260823-39AD2 — A `Modify` TARGET IS A PLACE, NEVER A TYPE.
///
/// kernel-language.md §5.6 settles what `Modify[X]` denotes: `Env` is a partial map
/// from resource NAMES to terms, and `Modify[X]` says the operation may inspect and
/// update `Env(X)`. So `X` names a RESOURCE — a parameter, `result`, a field path off
/// one — and a TYPE in that slot names no slot at all. `prelude/effects.anthill` used
/// to read it the other way ("keyed by the resource-identity TYPE T") and wrote the only
/// `Modify` over a type IN THE STDLIB, `ModifyRuntime.set`'s `effects Modify[T]`; that
/// line was the defect, and this pass is what keeps it from coming back.
///
/// NOT the only one in the TREE — the test fixtures were part of the population too, and
/// saying otherwise is the trap this project has recorded before. `wi329_handler_
/// discharge_test` (`Modify[Res]`), `wi698_row_param_refinement_test` (`Modify[Reg]`) and
/// three `eval_test` m5 rows all wrote one, and were repaired with the stdlib. One
/// SURVIVES on purpose, in the position below this pass does not reach:
/// `anthill-cpp-gen/tests/higher_kinded_arrow_test.rs` writes `@ {Modify[Calc]}` inside a
/// parameter's arrow type.
///
/// WHY A REFUSAL AND NOT A COMPARISON. `Modify[<type>]` is unsatisfiable BY
/// CONSTRUCTION, so there is nothing for a later pass to relate it to: σ binds a type
/// parameter to a TYPE (`provides ModifyRuntime[T = Cell]` binds `T` to the sort),
/// never to a place, so no instantiation of `Modify[T]` ever becomes a resource name.
/// Left admissible it does not merely go unchecked — it DISABLES checking, in two
/// different directions depending on whether the provision grounds it:
///
///   * σ-BOUND — `Modify[T]` grounds to `Modify[T = Cell]`, a ground TYPE target, and
///     the override's honest `Modify[c]` is then compared against a type. That pairing
///     was the `place_vs_resource_type` fail-open this ticket deletes from
///     [`check_override_refinement`]; deleting it without this refusal does not fix the
///     program, it refuses the CORRECT one with a message about coverage.
///   * NOT σ-BOUND — `Modify[T]` stays a type-param var, and the effects-⊆ premise gate
///     ("the SPEC row is fully known") fails open the WHOLE row, taking unrelated atoms
///     with it.
///
/// So the fail-open does not disappear when the relation is dropped — it MOVES. This
/// pass stops it at the declaration, where the author can read the message.
///
/// WHAT COUNTS AS A PLACE is [`TypeHead::Denoted`], which the LOADER decides — a
/// parameter, `result`, a field path off one, a value-producing zero-arg operation
/// (WI-313), and a NULLARY CONSTRUCTOR naming an ambient resource
/// (WI-20260823-4GBQV, `load::type_expr_to_child_modify_target`). This pass does not
/// re-derive that list; adding a spelling there admits it here, which is the point of
/// keeping the classification in one place.
///
/// SCOPE, and both limits have a witness rather than a caution.
///
///   * THE TARGET SLOT ONLY, not what its type admits. A `Modify` over a place whose
///     type is not `Modifiable` (`Modify[pattern]` on a `pattern: String`) is admitted
///     here — the other half of WI-20260823-39AD2, not yet written.
///   * AN OPERATION'S OWN ROW ONLY, not an effect row nested in a PARAMETER's arrow
///     type (`handle(body: () -> Int64 @ {Modify[X], Sig})`). That position scopes
///     differently — its lawful target is the arrow's OWN binder, the `CallbackParam`
///     shape `unify_denoted_view` compares by position and `prelude/iterable.anthill`
///     writes as `-Modify[x]` — so the same predicate cannot simply be pointed at it,
///     and the absent (`-E`) atoms living there are not `Modify`-headed at all. The
///     asymmetry is REAL and MEASURED, not assumed: the exact spelling refused on an
///     operation's own row loads clean one level in, which
///     `a_type_target_inside_a_parameters_arrow_row_is_not_checked` pins, and
///     `anthill-cpp-gen/tests/higher_kinded_arrow_test.rs`'s `@ {Modify[Calc]}` is a live
///     witness in the tree. Deciding the arrow position needs the callback-binder
///     population measured first; WI-20260823-39AD2 records it.
///
/// Runs over every `OperationInfo` FACT's declared row — one per fact, so a spec op and
/// its impl are each judged (WI-701) — after all operations load, like its neighbours
/// `check_const_purity` / `check_macro_purity`. Reported once per (operation, label):
/// `load_all` into a live KB banks a second fact for a type-parameter-bearing operation
/// (WI-1049), and one declaration must not read as two errors.
pub fn check_modify_targets(kb: &mut KnowledgeBase) -> Vec<crate::kb::load::LoadError> {
    let Some(modify_sym) = kb.try_resolve_symbol("anthill.prelude.Modify") else {
        // No prelude `Modify` — nothing in this KB can name the effect at all.
        return Vec::new();
    };
    let keys = ModifyTargetKeys::new(kb);
    let modify = Some(modify_sym);
    let mut errors = Vec::new();
    let mut reported: HashSet<(Symbol, String)> = HashSet::new();
    for (op_sym, effects) in crate::kb::op_info::all_operation_effects(kb) {
        // WI-20260831-RSRP5: through [`effect_element_labels`], for the reason its doc
        // gives — a bound alias (`effects E = Modify[Thing]`) and a row behind one were
        // both invisible here while the sibling registration gate followed the alias.
        // Same fact, same route, two answers.
        //
        // THE WRITTEN ELEMENT IS KEPT BESIDE THE LABEL IT RESOLVES TO, because the
        // refusal has to be findable in the source. Following the alias means the label
        // is `Modify[Thing]` while the author wrote `effects {E}` — a message naming only
        // the resolved form points at a string that appears nowhere in their file. The
        // sibling registration gate prints both halves ("declares effect `E`, but `Beep`
        // is not a REGISTERED effect kind"), which is what makes it actionable, and this
        // now does the same. (/code-review)
        let elements: Vec<(Value, Value)> = effects
            .iter()
            .flat_map(|e| {
                effect_element_labels(kb, e, keys.label)
                    .into_iter()
                    .map(|l| (e.clone(), l))
                    .collect::<Vec<_>>()
            })
            .collect();
        for (written, e) in &elements {
            let (label_value, kind) = match classify_modify_target(kb, e, modify, &keys) {
                Some(pair) => pair,
                None => continue,
            };
            let detail = match kind {
                ModifyTarget::Place => continue,
                ModifyTarget::Type => "whose target is a TYPE",
                // Distinguished because the repair differs: a bare `Modify` is not a
                // mis-named place, it names nothing at all, so "name the parameter"
                // reads as advice about a target the author never wrote.
                ModifyTarget::Missing => "which names no target at all",
            };
            let label = type_display_name_value(kb, &label_value);
            if !reported.insert((op_sym, label.clone())) {
                continue;
            }
            // WI-20260831-RSRP5 (/code-review): "`E`, which names `Modify[Thing]`," when
            // the two differ, so the message names the token the author can find in their
            // file as well as the label it resolves to. Identical forms print once.
            let written = type_display_name_value(kb, written);
            let named_as = if written == label {
                format!("`{label}`")
            } else {
                format!("`{written}`, which names `{label}`,")
            };
            errors.push(crate::kb::load::LoadError::Other {
                message: format!(
                    "operation `{}` declares effect {} {} — a `Modify` target is a \
                     PLACE: anything that DENOTES a value, i.e. a parameter, `result`, a \
                     field path off one, a value-producing zero-arg operation, or a \
                     NULLARY CONSTRUCTOR naming an ambient resource \
                     (kernel-language.md §5.6 — `Env` maps resource NAMES). A type there \
                     names no resource, and no instantiation can make it one: a provision \
                     binds a type parameter to a TYPE, never to a place. Name the place \
                     that is mutated (e.g. `Modify[target]`).",
                    kb.qualified_name_of(op_sym),
                    named_as,
                    detail,
                ),
            });
        }
    }
    errors
}

/// WI-20260825-CBRSW — an operation's OWN declared effect row may not both ADMIT and
/// LACK a label. Load-blocking.
///
/// THE SITE THE CODE ALREADY NAMED. [`check_signature_self_contradiction`] is WI-705's
/// call-site check and is gated on at least one op type parameter being BOUND, because —
/// in its own words — "an uninstantiated signature carries its rows as declared (a
/// literal `{X, -X}` is a load-time concern, not this call-site one)". No load-time site
/// asked, so the literal was admitted: MEASURED, an operation declaring
/// `effects {Permission[Model], -Permission[Model]}` whose body actually mints the
/// capability loaded completely clean, with BOTH legs silent — the body leg because the
/// label IS among the declared atoms, and WI-705 because nothing was instantiated. That
/// is the cheapest possible evasion of a denial, and proposal 064's whole value is in the
/// denial being trustworthy.
///
/// The verdict is [`uninhabitable_row_clash`], shared with the call-site check, so the
/// guarded deferral is the same one rule: a `X :- g` atom is only CONDITIONALLY present
/// (WI-067 discharge may refute `g`), so `{X :- g, -X}` is left to discharge while a row
/// carrying a literal `X` beside it still rejects. Only the RENDERING differs — this one
/// names a declaration, WI-705's names a call.
///
/// SCOPE — AN OPERATION'S OWN ROW ONLY, the same limit as its two neighbours
/// [`check_modify_targets`] and [`check_effect_registration`] and for the same measured
/// reason: `all_operation_effects` does not reach a row nested in a PARAMETER's arrow
/// type. A contradiction THERE is the shape WI-705 does catch, at the call that
/// instantiates it.
///
/// Reported once per operation — `load_all` into a live KB banks a second `OperationInfo` fact
/// for a type-parameter-bearing operation (WI-1049), and one declaration must not read as
/// two errors.
pub fn check_declared_row_contradiction(kb: &mut KnowledgeBase) -> Vec<crate::kb::load::LoadError> {
    // An EMPTY substitution: this reads the row AS DECLARED. Anything an instantiation
    // makes contradictory is WI-705's, at the call.
    let subst = Substitution::new();
    let mut errors = Vec::new();
    let mut reported: HashSet<Symbol> = HashSet::new();
    for (op_sym, params, effects) in crate::kb::op_info::all_operation_params_and_effects(kb) {
        // WI-20260830-APWM3 — PROJECTIONS DISCHARGED FIRST, and this is a correction that
        // ticket owed rather than a widening it chose. A clash SPANNING a projection —
        // `effects {llm.E, -External}` where `llm: LiveLlm` and `LiveLlm provides
        // Llm[E = {External}]` — used to be caught downstream by accident: the op-effects
        // coverage check could not match the incurred `External` against the un-flattened
        // merge term, fell through to the denial arm, and reported it as a violated `-X`.
        // APWM3 taught that check to flatten, so the match succeeded and the program
        // LOADED — a body performing `External` under a row that denies it. MEASURED
        // both ways; `a_denial_is_not_evaded_by_projecting_the_label_it_denies` is that
        // program, and the literal `{External, -External}` this pass already refused is
        // its control.
        //
        // The elimination does NOT breach the "AS DECLARED" stance above. That stance is
        // about a TYPE-PARAMETER INSTANTIATION, which arrives at a CALL and is WI-705's;
        // a receiver projection reads the type a parameter is DECLARED with, written in
        // the same signature. `{llm.E, -External}` is uninhabitable as written, at every
        // call, with nothing instantiated.
        let effects = eliminate_declared_row_projections(kb, op_sym, &params, &effects);
        // Accumulate ACROSS the atom list, not per atom: a clash may span two elements
        // (`effects {E}, -X`) as well as sit inside one written row. A non-decomposable
        // element contributes nothing — it has its own diagnostic path and must neither
        // mask nor fabricate a clash here.
        let mut present: Vec<Value> = Vec::new();
        let mut absent: Vec<Value> = Vec::new();
        for e in &effects {
            // CLASSIFY BY SHAPE, and do not lean on `decompose_effect_row_raw` to tell a
            // bare label from a row. It returns an EMPTY decomposition — `Some((⌀,⌀,⌀))`,
            // not `None` — for anything that is not an `EffectExpression`, so an element
            // written as just `Boom` decomposes to nothing at all and silently
            // contributes no present label. MEASURED: the first cut of this pass read
            // `effects {Boom, -Boom}` as (present = [], absent = [Boom]) and therefore
            // refused nothing, in the corpus or in its own fixture.
            //
            // The row functors are the ones that walk's own match names; everything else
            // that heads as a TYPE is an ordinary bare label, i.e. a PRESENT atom (the
            // default spelling, §5.5). Anything else — a malformed element — contributes
            // nothing: it has its own diagnostic path and must neither mask nor fabricate
            // a clash here.
            //
            // WI-20260830-APWM3 — CLASSIFIED BY THE SHARED PREDICATE, which keeps the
            // rule above and fixes the one spelling that was wrong. This list was
            // hand-written and read the LOCAL name, where the `effects_rows` WRAPPER's
            // local name is `EffectsRows` — so a wrapped row matched no arm, was not a
            // TYPE head either, and contributed NOTHING, in silence. Latent while every
            // element was written bare; live the moment the elimination above began
            // producing wrapped rows, and MEASURED as such — the first cut of that fix
            // still let `{llm.E, -External}` load. [`effect_value_is_row_shaped`] reads
            // the QUALIFIED functor, so it also stops a user sort named `merge` from
            // being taken for the kernel algebra, and it is the same predicate the
            // op-effects reader uses — the two cannot drift into disagreeing about what
            // a row is.
            let row_shaped = effect_value_is_row_shaped(kb, e);
            if row_shaped {
                if let Some((p, _tails, a)) = decompose_effect_row_raw(kb, &subst, e) {
                    present.extend(p);
                    absent.extend(a);
                }
            } else if matches!(
                type_head(kb, e),
                TypeHead::SortRef(_) | TypeHead::Parameterized { .. }
            ) {
                present.push(e.clone());
            }
        }
        // The overwhelmingly common row carries no `-X` at all; bail before the walk.
        if absent.is_empty() {
            continue;
        }
        let Some(clash) = uninhabitable_row_clash(kb, &subst, &present, &absent, &effects) else {
            continue;
        };
        if !reported.insert(op_sym) {
            continue;
        }
        let label = type_display_name_value(kb, &clash);
        errors.push(crate::kb::load::LoadError::Other {
            message: format!(
                "operation `{}` declares an effect row that both ADMITS and LACKS `{label}`, \
                 so no call of it can be well-typed: `-{label}` says the operation never \
                 performs that effect, and the same row says it may. Drop whichever half is \
                 wrong — the denial, if the operation really does perform it; the presence, \
                 if the claim is that it does not. (A GUARDED occurrence `{label} :- g` is \
                 not a contradiction: it defers to guard discharge, and only an \
                 unconditional one is reported here.)",
                kb.qualified_name_of(op_sym),
            ),
        });
    }
    errors
}

/// WI-20260823-VM3YB — AN EFFECT LABEL MUST NAME A REGISTERED EFFECT KIND.
///
/// `stdlib/anthill/prelude/effects.anthill` has stated the registration since it was
/// written — "Effect kinds are registered via `fact Effect[T = Kind[?]]`", the spelling
/// WI-20260917-S8JYF retired for `provides Effect[T = Kind]` — and
/// proposal 013 §"Effect checking is KB querying" says what it is FOR: "Unknown effect
/// kind = missing fact". Nothing asked. An effect row could name any sort at all, so a
/// MISSPELLED label was a silent NEW effect rather than an error, and the declaration
/// that was supposed to admit it was inert everywhere it was written.
///
/// Labels stay OPEN (§5.5) — any sort may become an effect kind, the kernel fixes no
/// list. What this pass adds is that becoming one is an ACT: the sort is registered,
/// once, beside its declaration. Open-and-registered, not open-and-unchecked.
///
/// IT READS THE PROVISION RELATION, WHICH IS NOW THE ONLY CHANNEL. A registration is a
/// `provides Effect[T = K]` — in `K`'s own body, or in a `namespace K` secondary entry
/// — and lands as an `anthill.reflect.SortProvidesInfo` provision of `Effect`
/// (`load_provides_clause`), so [`all_provisions`] sees every one of them.
///
/// THE ALTERNATIVE WAS MEASURED AND IS WRONG, and it is worth keeping the measurement
/// because it is what a reader reaches for first. An `Effect`-headed CLAUSE walk
/// (`rules_by_functor(Effect)`) was total for neither spelling even while both existed:
/// it found the five bare registrations — `Suspension`, `Branch`, `External`, and
/// guardians' `Model` / `Filesystem` — and missed `Modify` and `Error`, whose
/// registrations were written `fact Effect[T = Modify[?]]`, because a raw fact head
/// carries that binding POSITIONALLY (`Fn{Modify, pos:[?]}`), which [`type_head`] reads
/// as `Error` rather than `Parameterized`. Since WI-20260917-S8JYF there is no fact leg
/// to consider: a `fact` asserts an ordinary predicate and registers nothing.
///
/// WHAT IS JUDGED is a label that NAMES a kind — [`TypeHead::SortRef`] or
/// [`TypeHead::Parameterized`], following any `sort X = Y` alias to what it names.
/// Everything else is skipped because it names no kind to look up:
///
///   * EXEMPT while it is a HOLE: a sort's declared effect ROW PARAMETER. `effects
///     Effect = ?` (WI-320) lowers to a type parameter, so `effects Effect` inside
///     `PersistentCollection` heads as a `SortRef` to `PersistentCollection.Effect`.
///     Seven are live in the prelude (`Function.E`, `Iterable.E`, `MappedStream.EF`/`ES`,
///     …), all of them holes. A hole is a slot for a row, not a label — but a BOUND one
///     (`effects E = Kind`, `sort X = Kind`) is a NAME for what it is bound to and IS
///     judged; [`effect_label_kind`] carries that distinction and the two programs that
///     forced it.
///   * SKIPPED, having no name at all: the engine's own variables
///     ([`TypeHead::FlexVar`] / [`TypeHead::Skolem`] — 21 in the prelude, the opened
///     row params), and a receiver projection `s.E` ([`TypeHead::ExprCarried`] /
///     [`TypeHead::RigidProjection`] — 11 in the prelude, `Stream.head` and its
///     neighbours). Both are rows-in-waiting; whatever they ground to was judged where
///     it was WRITTEN.
///
/// The atom wrappers peel first ([`peel_effect_atom`]), so a guarded (`Error[E] :- g`),
/// an explicit-presence (`+K`) and a LACKS atom (`-Modify[x]`) are each judged on their
/// label. A lacks constraint is included deliberately: a misspelled `-Cloak` constrains
/// nothing and reads as though it did.
///
/// SCOPE — AN OPERATION'S OWN ROW ONLY, the same limit as its neighbour
/// [`check_modify_targets`] and for the same measured reason: an effect row nested in a
/// PARAMETER's arrow type (`handle(body: () -> Int64 @ {K, Rho})`) scopes differently and
/// `all_operation_effects` does not reach it. `a_label_inside_a_parameters_arrow_row_is_
/// not_checked` pins that, beside the Modify pass's own witness.
///
/// THE CORPUS WAS ALREADY CLEAN, which is why this could be switched on rather than
/// staged. The ticket predicted the opposite — that `Clock`, `ConsoleOutput` and
/// `ConsoleError` were unregistered and that turning the check on would refuse working
/// programs — because it counted `fact Effect[…]` only, and those three were already
/// registered with `provides`. Census over every `.anthill` tree that loads (stdlib, both
/// `examples/`, `anthill-testcases/`, `lf1`, `anthill-cpp-gen`, `anthill-stl`,
/// `anthill-todo`): 437 declared row elements at the widest, ZERO unregistered.
///
/// A SECOND WALK OF EVERY `OperationInfo` FACT, beside [`check_modify_targets`]' — and
/// affordable, measured rather than assumed, because `load_phase_inner` is on the
/// load-time path WI-653 tuned. Debug CLI, stdlib + an empty namespace,
/// `ANTHILL_LOAD_TIMING=1`, three runs: this mark is 0.98 / 1.11 / 1.17 ms against a
/// `type_check_sorts` mark of 806 ms / 1.77 s / 1.01 s in the same loads — ~0.1%, and the
/// same order as the neighbour it duplicates (0.67–0.81 ms). Sharing one walk would tie
/// two passes that answer DIFFERENT questions of one row (is this target a place / is this
/// label a kind) and report at different sites, which is the coupling `check_modify_targets`
/// was deliberately not folded into `check_override_refinement` to avoid.
///
/// Load-blocking, on this ticket's own evidence: an unregistered label produces no
/// runtime failure — it propagates, composes and discharges exactly like a registered
/// one — so there is no later site to be loud at. Reported once per (operation, kind) for
/// the same reason [`check_modify_targets`] is: `load_all` into a live KB banks a second
/// `OperationInfo` fact for a type-parameter-bearing operation (WI-1049), and one
/// declaration must not read as two errors.
///
/// NOT THE OTHER HALF THIS TICKET FOUND. A `fact` whose functor RESOLVES TO NOTHING is
/// still admitted silently — `fact Effect[T = K]` with `Effect` un-imported mints a bare
/// global predicate and registers nothing, which is how the WI-698 fixture shipped a
/// review cycle claiming a registration it never made. That is not an effects defect: it
/// is `remap_name_str`'s bare-`intern` fallback being FINAL at a fact head, whose own
/// comment already names `load_fact` as one of the two sites owing a refusal, and it is
/// WI-20260821-RDGQC's first measured bullet. Left there. What this pass does supply is
/// that the effects consequence is no longer invisible: the un-imported spelling now
/// fails at the LABEL, loudly.
pub fn check_effect_registration(kb: &mut KnowledgeBase) -> Vec<crate::kb::load::LoadError> {
    let Some(effect_sym) = kb.try_resolve_symbol("anthill.prelude.Effect") else {
        // No prelude `Effect` — nothing in this KB can register a kind, so nothing can
        // be measured against a registration either.
        return Vec::new();
    };
    // `Effect`'s sole declared type parameter, read from the DECLARATION rather than
    // spelled `"T"` here, so renaming it in effects.anthill moves both ends together.
    //
    // LOUD, unlike the guard above, and the two are not the same case. `Effect` is NOT
    // pre-registered by `register_stdlib_scopes`, so an unresolvable name means a KB that
    // never loaded the prelude — nothing there can name an effect either. Reaching HERE
    // means `Effect` is declared and carries no type parameter, which no registration
    // could bind: every `provides Effect[T = K]` in the tree would be malformed too. Returning
    // empty would make this pass inert exactly the way the declaration it enforces used to
    // be — the failure this ticket exists to end, re-created in the checker.
    let Some(param) = kb
        .type_params_of_sort(effect_sym)
        .first()
        .map(|n| kb.intern(n))
    else {
        return vec![crate::kb::load::LoadError::Other {
            message: format!(
                "`{}` declares no type parameter, so no `provides Effect[T = Kind]` can \
                 bind one and no effect kind can be registered — the \
                 effect-registration check cannot run. The prelude declares \
                 `sort Effect {{ sort T = ? }}` \
                 (`stdlib/anthill/prelude/effects.anthill`); this KB's `Effect` is \
                 not that sort.",
                kb.qualified_name_of(effect_sym),
            ),
        }];
    };
    let label_key = kb.intern("label");
    let registered = registered_effect_kinds(kb, effect_sym, param);
    let mut errors = Vec::new();
    let mut reported: HashSet<(Symbol, Symbol)> = HashSet::new();
    for (op_sym, effects) in crate::kb::op_info::all_operation_effects(kb) {
        // WI-20260831-RSRP5 — STILL PEEL-ONLY HERE, and that is a measurement, not an
        // omission. Routing this gate through [`effect_element_labels`] like its two
        // siblings was built and BACKED OUT: the alias half is already inside
        // [`effect_label_kind`], which has followed `sort X = Y` since
        // WI-20260823-VM3YB, and the ROW half targets a shape the grammar cannot
        // express — see the residue paragraph on `effect_label_kind`. The wiring
        // survived its own back-out with every test green, which is the definition of a
        // branch that fires nowhere.
        for e in &effects {
            let label = peel_effect_atom(kb, e, label_key);
            let Some(kind) = effect_label_kind(kb, &label) else {
                continue;
            };
            if registered.contains(&kb.canonical_sort_sym(kind)) {
                continue;
            }
            if !reported.insert((op_sym, kind)) {
                continue;
            }
            // The repair names the kind by its SHORT name and says WHERE that spelling
            // resolves — beside the declaration. Naming it short without the "where" sent
            // the author of a sort-NESTED kind to a namespace-level line that does not
            // load (`unresolved name 'Beep'`, plus a carrier-less provision error) and
            // left the original refusal standing; naming it qualified would be advice
            // about a spelling the binding slot does not take.
            //
            // NOT `fact Effect[…]`: WI-20260917-S8JYF retired it, so the line this used to
            // advise re-raised this refusal (MEASURED, and pinned from the other side by
            // `wi_s8jyf…::an_effect_kind_registers_through_provides_only`).
            //
            // THREE PLACES, each MEASURED to load: the kind's OWN body (the only one a
            // namespace-level kind has — it is declared by no sort, and it is the spelling
            // effects.anthill documents first), the sort that declares a NESTED kind, and a
            // secondary entry. The secondary entry's address is printed QUALIFIED and is
            // absolute only at the FILE'S TOP LEVEL: nested in another namespace the same
            // name is read relative to it — `namespace a.Host.Beep` inside `namespace a`
            // opens `a.a.Host.Beep`, the clause is refused as carrier-less, and this
            // refusal stands. (A RELATIVE name nested beside the declaration — `namespace
            // Beep` — loads too, and `a_namespace_block_provides_registers_the_kind`
            // drives it; the message prints the one spelling that needs no "where".)
            let op = kb.qualified_name_of(op_sym);
            let label = type_display_name_value(kb, &label);
            let kind_qn = kb.qualified_name_of(kind);
            let short = kb.local_name_of(kind);
            errors.push(crate::kb::load::LoadError::Other {
                message: format!(
                    "operation `{op}` declares effect `{label}`, but `{kind_qn}` is not a \
                     REGISTERED effect kind — nothing in the knowledge base says that sort \
                     is an effect, so this row element names a label the kernel never \
                     admitted and a misspelling of it would read as a new effect rather \
                     than as an error. Effect labels are OPEN (kernel-language.md §5.5) — \
                     any sort may be one — but becoming one is a declaration, `provides \
                     Effect[T = {short}]`, written where `{short}` is in scope: in \
                     `{short}`'s own body, or inside the sort that declares it. If it is \
                     declared elsewhere, write the clause in a `namespace {kind_qn}` block \
                     at the file's TOP LEVEL — that is the sort's own ADDRESS, and nested \
                     in another namespace the same name is read relative to it and opens \
                     a different one (proposal 013; \
                     `stdlib/anthill/prelude/effects.anthill`). If the label is a typo, \
                     fix the spelling.",
                ),
            });
        }
    }
    errors
}

/// WI-20260823-VM3YB — the SORT an effect-row label names, or `None` when the label
/// names no kind to look up. See [`check_effect_registration`] for what each `None`
/// covers and why.
///
/// AN ALIAS IS FOLLOWED, NOT EXEMPTED, and the difference is two programs. A declared
/// `sort X = Y` is a NAME for `Y`, so the question "is this a registered kind" is asked of
/// `Y`; only a chain bottoming out in a HOLE (`sort E = ?` — the row parameter WI-320's
/// `effects E = ?` lowers to) names no kind, and it falls out at the `type_head` match
/// because a variable is not a `SortRef`. The first cut instead exempted every
/// `resolve_sort_alias` hit, which is wider than "row parameter" by exactly the bound
/// cases, and MEASURED both of them loading clean with an unregistered `Boom` one
/// indirection away: `sort Nope = Boom … effects Nope`, and `effects E = Boom … effects E`
/// (a documented spelling — `effects-runtime.anthill:6`) whose bound was judged NOWHERE,
/// since the declaration site is not walked either. Found by review, not by the corpus:
/// the prelude's row parameters are all holes, so nothing in the tree exercised the
/// distinction.
///
/// THE RESIDUE THIS ONCE RECORDED IS CLOSED BY MEASUREMENT, not by code
/// (WI-20260831-RSRP5). It read: "a binding whose target is an effect ROW rather than a
/// single label (`sort E = {A, B}`) heads as [`TypeHead::EffectsRows`] and its ELEMENTS
/// go unjudged. No such declaration exists in the tree" — and the reason none exists is
/// that the shape IS NOT WRITABLE. `effects_sort_item`'s grammar is `effects <name> =
/// <_type>` (`tree-sitter-anthill/grammar.js`), and a row is not a `_type`: both
/// `sort E = {Zip, Error}` and `effects E = merge(Zap, Error)` are PARSE ERRORS. So there
/// are no elements to reach, and the row-explosion this note asked for would be a walk
/// over a case no program can present. Exploding a row that arrives some OTHER way is
/// still needed and still happens — a `provides Spec[E = {…}]` binding is one, and
/// [`check_written_row_bindings`] explodes it — but not here.
fn effect_label_kind(kb: &KnowledgeBase, label: &Value) -> Option<Symbol> {
    match type_head(kb, &resolve_effect_label_alias(kb, label)?) {
        TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => Some(s),
        _ => None,
    }
}

/// WI-20260901-47VWX — WHAT A RUN OF [`check_written_row_bindings`] IS FOR.
///
/// The check does two things in one walk, and only one of them is a verdict: it RECORDS
/// which clause facts it has seen (`KnowledgeBase::claim_row_binding_clause`, because two
/// of its three sources walk the whole KB with no batch boundary) and it JUDGES the ones
/// it has not. A load that runs no checks still needs the first half — otherwise the
/// clause facts IT created stay unclaimed and the next batch judges them, failing over a
/// file it was never handed.
///
/// SO THE CHECK-LESS LOAD RUNS THIS WALK, NOT A COPY OF IT. Every earlier attempt at this
/// keyed on a PRODUCER — restore the claims the load dropped (WI-20260901-EA6KS), then
/// also claim what its declaration walk PRESENTED — and each was a census of writers that
/// the next writer escaped: `derive_forwarded_provisions` asserts a `SortProvidesInfo` row
/// through `assert_fact_carrier`, above the stop and through no presentation, and MEASURED
/// leaked a refusal about `test.v47vwx.fwd` into a later batch of one clean unrelated sort
/// with the presentation-keyed repair in place. Borrowing the READER's population instead
/// is what makes that unreachable: a producer this check cannot see is one it cannot
/// judge either. A SECOND ENUMERATOR WOULD BE THE SAME MISTAKE — hence one walk with a
/// mode rather than a claim-only copy of the two source loops, which is a census of the
/// check's own sources and drifts the first time a fourth is added.
pub(crate) enum RowBindingRun {
    /// Judge every clause not yet seen — and claim it, as before.
    Judge,
    /// Claim every clause not yet seen and judge NOTHING: the settlement a
    /// `LoadOptions { run_typer: false }` load owes at its return.
    ///
    /// IT DOES DROP A REFUSAL, and saying otherwise would be the comfortable version of
    /// this note. Before it, a clause written by a check-less load WAS eventually
    /// reported — by whichever later batch first ran the check, blamed on a file that
    /// batch was never given. That refusal is not relocated; nothing judges it. The
    /// trade is the SITE half's, made twice for one reason
    /// ([`crate::kb::LoadCheckMarks`]): the alternative is that a `load_all` of a clean
    /// unrelated file FAILS, which makes the entry point unusable in the incremental
    /// workflow it exists to serve.
    ///
    /// RE-PRESENTATION RECOVERS THE WRITTEN CLAUSES AND NOT THE DERIVED ROWS — the
    /// qualification this note used to leave out, stated here because it is the guarantee
    /// a reader takes away from the decision site (/code-review). A later batch that
    /// RE-PRESENTS the file drops each WRITTEN clause's claim through
    /// `KnowledgeBase::note_metadata_fact_presented` and is refused normally, which is
    /// what `a_check_less_load_claims_the_clauses_it_wrote`'s fourth batch pins. A row
    /// `derive_forwarded_provisions` MATERIALIZED is never re-presented at all:
    /// `forwarded_rows_to_derive` returns only rows NOT ALREADY PRESENT, so the second
    /// load filters it out before `assert_forwarded_provides` and there is no assertion to
    /// hang a presentation on. Such a row is judged by no batch, ever — including a full
    /// re-load of the identical file, and including the case where the partial load
    /// ERRORED, since the claim sits above both the `Ok` and the `Err` arm of
    /// `load_phase_inner`'s early return. `…_claims_a_row_it_derived_too`'s fourth batch
    /// pins exactly that, and says why recovering it would have to happen at the deriver's
    /// filter rather than at an entry point. The author still meets a refusal at the
    /// clause they actually WROTE, which is the one they can fix, and that is why this is
    /// a stated cost rather than a hole.
    ///
    /// IT IS NOT A LANGUAGE-LEVEL NARROWING, so `docs/kernel-language.md` §5.5's "every
    /// position that writes a row is checked" stands unamended: §5.5 states what the
    /// CHECK decides, and this run does not weaken the check — it declines to charge one
    /// batch's clauses to another. A caller that loads a file through the ordinary
    /// pipeline meets every refusal §5.5 promises; `run_typer: false` is a library option
    /// that runs no check at all, and a language spec that had to enumerate it would be
    /// describing the loader instead of the language.
    ClaimOnly,
}

/// WI-20260901-47VWX — claim every row-binding clause in the KB without judging one, for
/// a load that will run no check. See [`RowBindingRun::ClaimOnly`].
///
/// IT IS A WHOLE-KB WALK, and that is affordable rather than assumed so: MEASURED at
/// 390 µs on a stdlib-sized KB in a debug build, against a load of the same KB in the
/// hundreds of milliseconds. It runs only on the `run_typer: false` path.
pub(crate) fn claim_written_row_bindings(kb: &mut KnowledgeBase) {
    let errs = check_written_row_bindings(kb, &[], RowBindingRun::ClaimOnly);
    debug_assert!(
        errs.is_empty(),
        "a ClaimOnly run judges nothing, so it can produce no diagnostic"
    );
}

/// WI-20260831-RSRP5 / WI-20260831-V25N3 — AN EFFECT LABEL IS JUDGED WHERE THE ROW IS
/// WRITTEN, at every position a row can be written in.
///
/// THE ROUTE THE PER-LABEL GATES COULD NOT SEE, and the reason it is closed HERE rather
/// than by widening them. A carrier binds a spec's row parameter — `LiveLlm provides
/// Llm[E = {External}]` — and every operation that projects `llm.E` then carries those
/// labels. MEASURED: `provides Spec[E = {Modify[Thing]}]` (a TYPE-targeted `Modify`) and
/// `provides Spec[E = {Beep}]` (an unregistered kind) BOTH LOADED CLEAN, judged by
/// nothing, while the identical labels written in an operation row were refused.
///
/// WHY THE BINDING AND NOT THE PROJECTION. RSRP5 was filed to teach the per-label gates
/// to read a projection through, the way WI-20260830-APWM3 taught the op-effects
/// coverage check and 054's exclusion. Measuring the population changed the answer: a
/// label can only reach a projected row by being WRITTEN somewhere. Judging it there
/// therefore covers the projection route ENTIRELY, and does it better — one site instead
/// of every caller, a diagnostic that points at the line the author wrote, and a verdict
/// for a carrier no caller has projected yet.
///
/// IT ALSO LEAVES `docs/kernel-language.md` §5.5 TRUE AS WRITTEN. That section exempts
/// "a receiver projection (`s.E`)" from the registration rule, on the ground that it
/// names no kind. Read as "the projection names no kind OF ITS OWN — the kind is named
/// at the binding, and judged there", the exemption is exactly right, and the widening
/// RSRP5 first proposed would have contradicted it.
///
/// ## The two SOURCES, and why the boundary between them is where it is (V25N3)
///
/// RSRP5 shipped this over `provides` clauses alone, and §5.5's "judged once, at its
/// origin" was then FALSE for the third origin: a row written as a TYPE ARGUMENT in a
/// signature (`operation ask(s: Spec[E = {Beep}], …)`). Both offending spellings loaded
/// clean, on a minimal fixture and on guardians' `Llm` alike. Closing it is a CENSUS of
/// the positions a row can be written in, not a new rule — the judging half below is
/// unchanged.
///
/// The census is measured, not enumerated from a ticket's examples
/// (WI-20260830-APXSS), by walking every live fact head, the const-type table and every
/// op/const body of a corpus that writes a row at each candidate position and asking
/// where the binding LANDED. It bottoms out in exactly two sources:
///
/// 1. **[`crate::kb::ParameterizedSite`]** — WI-835's registry of every written
///    parameterized type, recorded AT THE TYPE LOWERINGS so a new type position cannot
///    escape by being added elsewhere. It reaches an operation's parameter and return
///    types, an entity FIELD's type, a `sort S = …` alias, a `const`'s type, a body
///    `let` annotation and a typed lambda binder — and any of those NESTED inside a
///    tuple, an arrow parameter, or another instantiation. It does NOT reach an
///    operation's own `requires` / `ensures`; that is source 3, and the distinction is
///    load-bearing — see it.
///
/// 2. **The three SPEC-CLAUSE facts** — `SortProvidesInfo`, `SortRequiresInfo`,
///    `ProvidesConditionInfo`. `sort_inst_to_value` is the one `TypeExpr::Parameterized`
///    lowering that records NO site: it assembles a `reflect.SortView` instead, and its
///    outputs are exactly those three facts. So the boundary is not a judgement call —
///    source 2 is precisely `sort_inst_to_value`'s output, and source 1 is everything
///    else. (Its nested bindings still record, via `sort_binding_to_value`, which is why
///    a row nested INSIDE a provision — `provides Box[T = Spec[E = {Beep}]]`, measured
///    unjudged before this — arrives through source 1.)
///
/// ONLY ROW PARAMETERS ARE JUDGED, and the filter is the DECLARATION rather than the
/// binding's shape. `effects E = ?` lowers to `sort E = ?` plus `requires
/// EffectsRuntime[Effects = E]` (`prelude/effects-runtime.anthill`), so a row parameter
/// is identified by that anchor and nothing else — see [`effect_row_params_of_spec`].
/// Filtering on the VALUE looking row-shaped was the obvious alternative and is wrong in
/// BOTH directions: it MISSES the brace-less `provides Spec[E = Beep]`, which loads and
/// binds a row just as much (measured), and it would judge whatever a TYPE parameter
/// happened to be bound to — `Spec[C = Int64]` refused for `Int64` not being a
/// registered effect kind.
///
/// Reported once per (origin, spec, param, label), so one clause reaching the walk down
/// two routes does not read as two errors while the SAME slot written twice in one
/// signature still reports twice.
///
/// COST OF THE TWO ADDED SOURCES, measured rather than argued (release, guardians,
/// min of 3, `ANTHILL_LOAD_TIMING=1`): 0.13 ms with the spec-clause source alone — the
/// shape RSRP5 shipped — and 0.42 ms with all three. For scale, its sibling gates
/// (`check_modify_targets`, `check_effect_registration`) cost 0.15 ms each and
/// `scan_definitions` alone costs 4.5 ms on the same load.
pub(crate) fn check_written_row_bindings(
    kb: &mut KnowledgeBase,
    sites: &[crate::kb::ParameterizedSite],
    run: RowBindingRun,
) -> Vec<crate::kb::load::LoadError> {
    let judging = matches!(run, RowBindingRun::Judge);
    let effect_sym = kb.try_resolve_symbol("anthill.prelude.Effect");
    let modify = kb.try_resolve_symbol("anthill.prelude.Modify");
    if judging && effect_sym.is_none() && modify.is_none() {
        // Neither rule can be stated in this KB — no prelude `Effect`, no prelude
        // `Modify`. Mirrors each sibling gate's own bail.
        //
        // A `ClaimOnly` RUN DOES NOT TAKE IT, and the asymmetry is the point: a judging
        // run that bails has judged nothing, so a later batch judging those clauses is
        // the FIRST judgement and belongs to it. A check-less load will never judge
        // them, in this batch or any other, so its claim stands whether or not the two
        // rules can be stated here — otherwise a partial load into a prelude-less KB
        // hands its clauses to whichever later batch first has a prelude.
        return Vec::new();
    }
    let keys = ModifyTargetKeys::new(kb);
    let registered = effect_sym.filter(|_| judging).and_then(|es| {
        // `Effect`'s sole declared type parameter, read from the DECLARATION — the same
        // sourcing [`check_effect_registration`] uses, so renaming it in effects.anthill
        // moves both ends together. `None` (no parameter) makes this half inert here
        // rather than duplicating that gate's loud bootstrap refusal.
        let param = kb.type_params_of_sort(es).first().map(|n| kb.intern(n))?;
        Some(registered_effect_kinds(kb, es, param))
    });

    // Snapshot first: the judging walk below mutates `kb` (interning, row explosion).
    struct RowBinding {
        /// The phrase that completes "… binds `Spec`'s row parameter `E`", naming
        /// WHERE the author wrote it. A spec clause names the clause and its keyword; a
        /// written type argument says only that much and leans on its span.
        ///
        /// IT IS ALSO THE DEDUP IDENTITY, and that is the /code-review finding: keyed on
        /// the owner SYMBOL instead, a sort writing the same bad label in `provides
        /// Spec[E = {Beep}]` AND `requires Spec[E = {Beep}]` reported ONCE, naming only
        /// the `provides` — MEASURED — and the author fixed that, reloaded, and met the
        /// other. Keying on the rendered origin makes the key exactly as fine as the
        /// message, which is the only key that cannot collapse two things a reader has
        /// to fix separately.
        origin: String,
        spec: Symbol,
        /// WI-20260831-RSRP5 (/code-review) — WHICH row parameter this binds. A spec may
        /// declare more than one (`effects E = ?` beside `effects F = ?`), and without it
        /// two bad bindings of the SAME label deduped to ONE message that named neither
        /// slot — measured on `provides TwoRows[E = {Beep}, F = {Beep}]`, which reported
        /// once. It is in the dedup key AND in the message, because a reader who cannot
        /// see which half is wrong cannot fix the right one.
        param: Symbol,
        value: Value,
        span: Option<crate::span::SourceSpan>,
    }
    let mut bindings: Vec<RowBinding> = Vec::new();
    // Shared by all three sources — see [`row_params_of`] for why it is memoized.
    let mut row_params_by_spec: HashMap<Symbol, Vec<Symbol>> = HashMap::new();

    // ── Source 2: the three spec-clause facts ────────────────────────────────
    for clause in all_spec_clause_views(kb) {
        // ONCE PER KB, not once per load (/code-review). This walk has no batch
        // boundary of its own — unlike source 1, whose registry is drained per load — so
        // a `load_all` into a live KB of a CLEAN file into a KB already holding an offending
        // clause re-reported it: MEASURED, a second batch of one unrelated sort failed
        // with an error naming a file it was never given. The claim is DROPPED again
        // when the loader re-presents the fact, which is the other direction and needs
        // its own mechanism: `KnowledgeBase::note_metadata_fact_presented`.
        if !kb.claim_row_binding_clause(clause.rid) {
            continue;
        }
        if !judging {
            continue;
        }
        let Some((spec_base, named)) = unwrap_spec_view(kb, clause.spec_view) else {
            continue;
        };
        let row_params = row_params_of(kb, spec_base, &mut row_params_by_spec);
        if row_params.is_empty() {
            continue;
        }
        let spec_qn = kb.qualified_name_of(spec_base).to_string();
        let owner_qn = kb.qualified_name_of(clause.owner).to_string();
        // NO SPAN, and the two candidates were BUILT AND MEASURED ANSWERING `None`
        // rather than argued away (/code-review raised the gap and proposed the first).
        // `functor_span` is keyed off a converted `Term::Fn` FUNCTOR — it holds spans for
        // names that appear APPLIED in a body, not for a sort or operation DECLARATION —
        // and `rule_head_span` is empty for a loader-EMITTED metadata fact, which is what
        // a `SortProvidesInfo` is. `term_span` on the `SortView` is not a third option:
        // the term is hash-consed and aliases across sites, so it would point at some
        // OTHER file's identical clause. So a fact-sourced refusal names its owner and
        // its clause keyword and no line; a SITE-sourced one carries `path:line:col`.
        for (k, v) in &named {
            let Some(param) = type_param_sym_of_binding(kb, *k, &spec_qn) else {
                continue;
            };
            if !row_params.iter().any(|p| *p == param) {
                continue;
            }
            bindings.push(RowBinding {
                origin: format!("`{owner_qn} {} {spec_qn}`", clause.kind.keyword()),
                spec: spec_base,
                param,
                value: Value::term(*v),
                span: None,
            });
        }
    }

    // ── Source 1: every written parameterized type ───────────────────────────
    // NOT WALKED BY A `ClaimOnly` RUN, and that is not an optimization: a site carries no
    // per-KB claim to leave behind (its registry is drained per load, and a check-less
    // load's sites are truncated away by `restore_load_check_marks`), so there is nothing
    // here for a later batch to inherit. The caller passes `&[]` anyway; this says why
    // that is the right argument rather than an empty-looking accident.
    for site in sites.iter().filter(|_| judging) {
        let row_params = row_params_of(kb, site.base, &mut row_params_by_spec);
        if row_params.is_empty() {
            continue;
        }
        let spec_qn = kb.qualified_name_of(site.base).to_string();
        for (key, bound) in &site.bindings {
            // THROUGH THE SAME LADDER AS A `SortView` KEY, not a raw `Symbol` compare.
            // A site's binding key is minted in the WRITING scope (`kb.intern("E")` for a
            // positional, `reintern(p.last())` for a named one) while
            // `effect_row_params_of_spec` returns the spec's OWN parameter symbol
            // (`test.Spec.E`) — the WI-422 class of silent miss, and MEASURED as one
            // here: keyed on `Symbol` equality this arm matched NOTHING and every
            // written type argument stayed unjudged, with the spec-clause arm beside it
            // passing.
            let Some(param) = type_param_sym_of_binding(kb, *key, &spec_qn) else {
                continue;
            };
            if !row_params.iter().any(|p| *p == param) {
                continue;
            }
            bindings.push(RowBinding {
                origin: "a written type argument".to_string(),
                spec: site.base,
                param,
                value: bound.clone(),
                span: Some(site.span),
            });
        }
    }

    // ── Source 3: an operation's own `requires` / `ensures` clauses ──────────
    // NOT a type lowering at all: an op-scoped clause list is OVERLOADED (it carries
    // both spec requirements and VALUE preconditions, `requires plus: Monoid[T],
    // neq(b, 0)`), so the loader converts each item with `convert_term` — the GOAL
    // converter — and no `TypeExpr` lowering runs. MEASURED: with sources 1 and 2 alone
    // `operation go(…) requires Spec[E = {Beep}]` and its named-binder twin were the
    // only two positions of the census still loading clean.
    for (rid, op_sym, clauses) in crate::kb::op_info::all_operation_contract_clauses(kb) {
        // Once per KB, for the spec-clause loop's reason, and claimed per FACT rather
        // than per clause because one `OperationInfo` fact carries both lists. The batch
        // that RE-PRESENTS the file still reports it, and only a batch that does not
        // present it at all skips it — but the claim does not deliver that on its own
        // (the assert dedups onto the claimed id), so see
        // `KnowledgeBase::note_metadata_fact_presented`, which is what drops it.
        if !kb.claim_row_binding_clause(rid) {
            continue;
        }
        if !judging {
            continue;
        }
        let mut found: Vec<(&'static str, Symbol, Symbol, Value)> = Vec::new();
        for (keyword, clause) in clauses {
            let mut in_clause: Vec<(Symbol, Symbol, Value)> = Vec::new();
            collect_row_bindings_in_goal(kb, &clause, &mut row_params_by_spec, &mut in_clause, 0);
            found.extend(in_clause.into_iter().map(|(s, p, v)| (keyword, s, p, v)));
        }
        if found.is_empty() {
            continue;
        }
        let op_qn = kb.qualified_name_of(op_sym).to_string();
        // No span — see the spec-clause loop above, where the same two lookups were
        // measured answering `None`.
        let span = None;
        for (keyword, spec, param, value) in found {
            bindings.push(RowBinding {
                origin: format!("`{op_qn}`'s `{keyword}` clause"),
                spec,
                param,
                value,
                span,
            });
        }
    }

    let mut errors = Vec::new();
    // THE ORIGIN, NOT THE OWNER SYMBOL (/code-review). The key has to be exactly as fine
    // as the message: `provides` and `requires` on ONE sort render differently and are
    // two things to fix, but share an owner — measured collapsing to a single
    // `provides`-only diagnostic when the owner keyed it. The SPAN is in the key beside
    // it because two written type arguments in one signature share the constant site
    // origin and are separated by nothing else.
    let mut reported: HashSet<(
        String,
        Option<crate::span::SourceSpan>,
        Symbol,
        Symbol,
        String,
    )> = HashSet::new();
    for b in &bindings {
        for label in effect_element_labels(kb, &b.value, keys.label) {
            let display = type_display_name_value(kb, &label);
            if !reported.insert((b.origin.clone(), b.span, b.spec, b.param, display.clone())) {
                continue;
            }
            let spec_qn = kb.qualified_name_of(b.spec).to_string();
            let slot = kb.local_name_of(b.param).to_string();
            let span = b.span.map(|s| s.span);
            let source = b.span.map(|s| s.source);
            let mut push = |detail: String| {
                let err = crate::kb::load::LoadError::WrittenEffectRowLabel {
                    spec: spec_qn.clone(),
                    param: slot.clone(),
                    label: display.clone(),
                    origin: b.origin.clone(),
                    detail,
                    span,
                };
                errors.push((err, source));
            };
            if let Some((_, kind)) = classify_modify_target(kb, &label, modify, &keys) {
                let which = match kind {
                    ModifyTarget::Place => None,
                    ModifyTarget::Type => Some("whose target is a TYPE"),
                    ModifyTarget::Missing => Some("which names no target at all"),
                };
                if let Some(which) = which {
                    push(format!(
                        "{which} — a `Modify` target is a PLACE, not a type \
                         (kernel-language.md §5.6). A row TYPE-ARGUMENT is not a \
                         signature, so the places a SIGNATURE offers are not available \
                         here: there is no parameter to name, and no `result`. What IS \
                         available is an ambient resource — a NULLARY CONSTRUCTOR that \
                         denotes one (`Modify[clock]` over an `entity clock`), which is \
                         the §5.6 form written for exactly this position."
                    ));
                    continue;
                }
            }
            let Some(registered) = registered.as_ref() else {
                continue;
            };
            let Some(kind) = effect_label_kind(kb, &label) else {
                continue;
            };
            // A TYPE PARAMETER NAMES NO KIND — §5.5's own exemption for "a row variable
            // the checker has opened", asked of the label rather than of its carrier.
            //
            // WHY IT IS ASKED AT ALL, since the type lowerings already answer it: a SORT
            // parameter carries a `SortAlias(P, Var)` fact, so `effect_label_kind`
            // follows it to a variable and returns `None` above. An OPERATION's bracket
            // parameter carries no such fact — its variable lives in the op's own record
            // — so it arrives here as an ordinary `SortRef`. That is invisible through
            // sources 1 and 2, where a type param in scope lowers to a `Term::Var`
            // outright, and LIVE through source 3, whose clauses are converted by the
            // GOAL converter: MEASURED, the prelude's `map[…, EffS, …] requires
            // Iterable[C = Sc, Element = S, E = EffS]` (and `filter`'s twin) were
            // refused for `EffS` not being a registered effect kind, on every program
            // that merely loads the prelude.
            if is_sort_param_symbol(kb, kind) {
                continue;
            }
            if registered.contains(&kb.canonical_sort_sym(kind)) {
                continue;
            }
            let short = kb.local_name_of(kind).to_string();
            let kind_qn = kb.qualified_name_of(kind).to_string();
            push(format!(
                "but `{kind_qn}` is not a REGISTERED effect kind — nothing in the \
                 knowledge base says that sort is an effect, so this names a label the \
                 kernel never admitted and a misspelling of it would read as a new effect \
                 rather than as an error. Effect labels are OPEN (kernel-language.md \
                 §5.5) — any sort may be one — but becoming one is a declaration: \
                 `provides Effect[T = {short}]`, written inside `{short}`'s own \
                 `sort`/`enum` body, or in a `namespace {short}` block at its address \
                 when it has no body to write it in. If the label is a typo, fix the \
                 spelling."
            ));
        }
    }
    // WI-745: attribute a site-sourced refusal to the file its span indexes into, so it
    // renders `path:line:col`. A spec-clause refusal has no span and stays bare.
    errors
        .into_iter()
        .map(|(err, source)| match source {
            Some(src) => err.located_in_kb_source(kb, src),
            None => err,
        })
        .collect()
}

/// WI-20260831-V25N3 — every `Spec[rowParam = …]` reachable inside one GOAL term, as
/// `(spec, row parameter, bound row)`.
///
/// A STRUCTURAL DESCENT, because a clause is not one application: a multi-goal clause is
/// a `conjunction(g1, …)`, and a spec application can be an ARGUMENT of another
/// (`requires Iterable[C = Box[T = Spec[E = {…}]]]`). Sources 1 and 2 need no such walk —
/// a `ParameterizedSite` is already one application, and a `SortView`'s nested bindings
/// record their own sites — so this is the goal-list reader's own machinery, not a
/// general one.
///
/// DEPTH-BOUNDED for the same reason [`effect_element_labels`] is: the bound guards a
/// malformed (cyclic) structure this walk owns no verdict for, and on overflow it returns
/// what it found rather than nothing.
fn collect_row_bindings_in_goal(
    kb: &mut KnowledgeBase,
    v: &Value,
    row_params_by_spec: &mut HashMap<Symbol, Vec<Symbol>>,
    out: &mut Vec<(Symbol, Symbol, Value)>,
    depth: u32,
) {
    if depth > EFFECT_ELEMENT_DEPTH_LIMIT {
        return;
    }
    let ViewHead::Functor {
        functor: Some(base),
        ..
    } = v.head(kb)
    else {
        return;
    };
    let keys = v.named_keys(kb);
    let row_params = row_params_of(kb, base, row_params_by_spec);
    if !row_params.is_empty() {
        let spec_qn = kb.qualified_name_of(base).to_string();
        for k in &keys {
            let Some(param) = type_param_sym_of_binding(kb, *k, &spec_qn) else {
                continue;
            };
            if !row_params.iter().any(|p| *p == param) {
                continue;
            }
            if let Some(bound) = v.named_arg(kb, *k).map(|b| b.to_value()) {
                out.push((base, param, bound));
            }
        }
    }
    let mut kids: Vec<Value> = Vec::new();
    let mut i = 0;
    while let Some(a) = v.pos_arg(kb, i) {
        kids.push(a.to_value());
        i += 1;
    }
    for k in &keys {
        if let Some(a) = v.named_arg(kb, *k) {
            kids.push(a.to_value());
        }
    }
    for k in kids {
        collect_row_bindings_in_goal(kb, &k, row_params_by_spec, out, depth + 1);
    }
}

/// WI-20260831-RSRP5 (/code-review) / WI-20260831-V25N3 — `spec`'s effect-row
/// parameters, MEMOIZED PER SPEC.
///
/// [`effect_row_params_of_spec`] walks the spec's whole `requires` chain and scans each
/// entry's keys, and the readers ask it once per CLAUSE, once per SITE and once per node
/// of a contract-clause descent — so a spec with N providers walked the identical chain N
/// times on a pass that already visits every provision in the KB. Keyed on the spec base,
/// which is what the answer depends on. An EMPTY vec is a cached ANSWER, not a miss: it
/// means "this sort declares no row", the overwhelmingly common case, and every caller
/// short-circuits on it.
fn row_params_of(
    kb: &mut KnowledgeBase,
    spec: Symbol,
    cache: &mut HashMap<Symbol, Vec<Symbol>>,
) -> Vec<Symbol> {
    if let Some(cached) = cache.get(&spec) {
        return cached.clone();
    }
    let computed = effect_row_params_of_spec(kb, spec);
    cache.insert(spec, computed.clone());
    computed
}

/// WI-20260831-V25N3 — WHICH SPEC CLAUSE a row binding was written in. Only the keyword
/// differs in the diagnostic, but the three are three FACTS, so the walk that gathers
/// them has to name them.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum SpecClauseKind {
    Provides,
    Requires,
    ProvidesCondition,
}

impl SpecClauseKind {
    /// The keyword the author wrote, for the diagnostic. A provision CONDITION is a
    /// `provides X :- Y` tail, so its keyword names the tail rather than the clause —
    /// otherwise the message points at the provided spec, which is not the one at fault.
    fn keyword(self) -> &'static str {
        match self {
            SpecClauseKind::Provides => "provides",
            SpecClauseKind::Requires => "requires",
            SpecClauseKind::ProvidesCondition => "provides … :-",
        }
    }
}

/// WI-20260831-V25N3 — one written SPEC CLAUSE: its owning sort and the `SortView` it
/// names. The three facts `sort_inst_to_value` emits, in one walk.
struct SpecClauseView {
    pub(super) kind: SpecClauseKind,
    /// The sort the clause is written on.
    pub(super) owner: Symbol,
    pub(super) spec_view: TermId,
    /// The fact this clause IS, so the caller can claim it once per KB — see
    /// [`KnowledgeBase::claim_row_binding_clause`].
    pub(super) rid: RuleId,
}

/// Every `provides` / `requires` / `provides … :-` clause in the KB, as
/// [`SpecClauseView`]s.
///
/// NOT [`all_provisions`] widened: that decoder resolves the PROVIDER relation (it
/// unwraps views, follows conditional provisions), which is a different question from
/// "what did the author write in this clause". This one reads the three facts' raw
/// `spec` / `condition` slots, because the row binding under judgement is a written
/// token, not a derived one.
fn all_spec_clause_views(kb: &KnowledgeBase) -> Vec<SpecClauseView> {
    let mut out = Vec::new();
    for (qn, kind, spec_field) in [
        (
            "anthill.reflect.SortProvidesInfo",
            SpecClauseKind::Provides,
            "spec",
        ),
        (
            "anthill.reflect.SortRequiresInfo",
            SpecClauseKind::Requires,
            "spec",
        ),
        (
            "anthill.reflect.ProvidesConditionInfo",
            SpecClauseKind::ProvidesCondition,
            "condition",
        ),
    ] {
        let Some(sym) = kb.try_resolve_symbol(qn) else {
            continue;
        };
        // TERM-ONLY for all three, the condition relation included: a value-headed
        // condition fact is invisible here, where [`decoded_condition_row`] reads it.
        for rid in kb.rules_by_functor(sym) {
            let Some((owner, _, spec_view)) = sort_clause_fields(kb, rid, spec_field) else {
                continue;
            };
            out.push(SpecClauseView {
                kind,
                owner,
                spec_view,
                rid,
            });
        }
    }
    out
}

/// WI-20260831-RSRP5 — WHICH OF `spec`'S TYPE PARAMETERS ARE EFFECT-ROW PARAMETERS.
///
/// `effects E = ?` is sugar: it lowers to `sort E = ?` PLUS `requires
/// EffectsRuntime[Effects = E]` (`stdlib/anthill/prelude/effects-runtime.anthill`, which
/// states the equivalence in those words). The sort parameter it mints is
/// indistinguishable from an ordinary `sort C = ?` — same `SortAlias(_, Var)` shape, same
/// entry in `type_params_of_sort` — so the ANCHOR is the only thing that says which
/// parameter carries a row, and reading it is what keeps
/// [`check_written_row_bindings`] off a type parameter's binding.
fn effect_row_params_of_spec(kb: &mut KnowledgeBase, spec: Symbol) -> Vec<Symbol> {
    let Some(anchor) = effects_runtime_sym(kb) else {
        return Vec::new();
    };
    // BY LOCAL NAME, not an interned `Symbol`: the anchor's `Effects` key was resolved
    // in the requires clause's own scope, and `kb.intern("Effects")` mints/finds a
    // symbol that need not be that one — the WI-422 class of silent miss, and MEASURED
    // as one here (the chain held `SortView[Effects = E]` and the symbol lookup found
    // nothing in it).
    direct_requires_chain(kb, spec)
        .iter()
        .filter(|entry| same_sort_canonical(kb, entry.required_sort, anchor))
        .filter_map(|entry| {
            let key = *entry
                .spec
                .named_keys(kb)
                .iter()
                .find(|k| kb.local_name_of(**k) == "Effects")?;
            let bound = named_child_value(kb, &entry.spec, key)?;
            match type_head(kb, &bound) {
                TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => Some(s),
                _ => None,
            }
        })
        .collect()
}

/// WI-20260831-RSRP5 — THE LABELS AN EFFECT-ROW ELEMENT ULTIMATELY NAMES: presence
/// wrappers peeled, `sort X = Y` aliases followed, and any ROW it bottoms out in
/// exploded into its members (each of which is put through the same walk).
///
/// THE ONE PLACE THE ELEMENT/LABEL GAP IS CLOSED. Every per-label gate over an effect
/// row asks a question about a LABEL — "is this `Modify`'s target a place?", "is this a
/// registered kind?" — of a list that holds ELEMENTS, and the two are the same thing
/// only in the simplest spelling. Three ways they come apart, all measured:
///
///   * a PRESENCE WRAPPER — `present(label: L)` / `-L` / `L :- g`, handled by
///     [`peel_effect_atom`] since WI-20260823-VM3YB;
///   * an ALIAS — `effects E = Modify[Thing]` names the label `E`, and a gate asking
///     `effect_is_modify` of `E` answers no. [`check_effect_registration`] followed the
///     chain, [`check_modify_targets`] did not, so the same sort was refused for an
///     unregistered label and admitted for a type-targeted `Modify`;
///   * a ROW — `sort E = {A, B}`, whose members went unjudged by BOTH. That was recorded
///     as residue on [`effect_label_kind`] ("reaching them means exploding a row here …
///     a widening this ticket has no population to measure"); the walk it wanted is
///     [`explode_declared_effect_row`], which WI-20260830-APWM3 built for the op-effects
///     reader. This is that residue closed, not a new ambition.
///
/// ABSENCES COME BACK TOO, as their bare labels. A gate asking "is this a REGISTERED
/// kind" or "is this `Modify` target a PLACE" wants the same answer for `-X` as for `X`:
/// a denial naming an unregistered label is as much a misspelling as a presence naming
/// one, and `peel_effect_atom` has always peeled a top-level `absent` for exactly that
/// reason. A gate that must tell presence from absence — the uninhabitable-row check —
/// does its own decomposition and does not come through here.
///
/// DEPTH-BOUNDED, because a row reached through an alias may name another alias. The
/// bound is a backstop against a cyclic declaration, which is malformed and which this
/// walk owns no verdict for; on overflow it returns what it has, so a gate judges the
/// labels it could reach rather than silently judging none.
pub(crate) fn effect_element_labels(
    kb: &mut KnowledgeBase,
    e: &Value,
    label_key: Symbol,
) -> Vec<Value> {
    let mut out: Vec<Value> = Vec::new();
    let mut stack: Vec<(Value, u32)> = vec![(e.clone(), 0)];
    while let Some((cur, depth)) = stack.pop() {
        if depth > EFFECT_ELEMENT_DEPTH_LIMIT {
            out.push(cur);
            continue;
        }
        let peeled = peel_effect_atom(kb, &cur, label_key);
        let Some(resolved) = resolve_effect_label_alias(kb, &peeled) else {
            // Cyclic alias chain: judge the label as written rather than dropping it.
            out.push(peeled);
            continue;
        };
        match explode_declared_effect_row(kb, &resolved) {
            Some((present, absent)) => {
                for l in present.into_iter().chain(absent) {
                    stack.push((l, depth + 1));
                }
            }
            None => out.push(resolved),
        }
    }
    out
}

/// How deep [`effect_element_labels`] follows alias-then-row nesting. Generous: the
/// deepest shape in the tree is one row behind one alias.
const EFFECT_ELEMENT_DEPTH_LIMIT: u32 = 8;

/// WI-20260831-RSRP5 — FOLLOW A LABEL'S `sort X = Y` ALIAS CHAIN to the value it names.
/// The walk [`effect_label_kind`] has always done, split out because a second gate needs
/// the resolved VALUE and not just its base symbol.
///
/// A BOUND ROW ALIAS IS A LABEL WEARING A NAME. `sort S ... effects E = Modify[Thing]`
/// declares `E` as a name for that label (`docs/kernel-language.md` §5.5: "A **bound**
/// alias is followed rather than exempted — `effects E = Kind`, like `sort X = Kind`, is
/// a name for `Kind` and is judged as one"), and an operation of `S` then writes
/// `effects {E}`. Every per-label gate therefore has to walk the chain before asking its
/// question, or it judges the NAME instead of the label.
///
/// [`check_effect_registration`] always did; [`check_modify_targets`] did not, and that
/// asymmetry was the measured gap — `effects E = Modify[Thing]` on a sort put a
/// TYPE-targeted `Modify` into every one of its operations' rows and the "a `Modify`
/// target is a PLACE" refusal never fired, while the same sort with an UNREGISTERED
/// label was refused. Same route, same fact, two answers.
///
/// `None` on chain overflow only — a non-sort head (a row var, an arrow) is returned
/// AS IS, since it is a label this walk has nothing to do to, not a failure. That split
/// is why the return is `Option<Value>` and not `Value`: the overflow case is a
/// malformed (cyclic) declaration this walk owns no verdict for, and withholding is the
/// conservative answer there rather than a silent skip of something judgeable.
fn resolve_effect_label_alias(kb: &KnowledgeBase, label: &Value) -> Option<Value> {
    let mut cur = label.clone();
    // An alias chain is finite by construction; the bound is a backstop against a cyclic
    // one — see the doc above.
    for _ in 0..ALIAS_CHAIN_LIMIT {
        let base = match type_head(kb, &cur) {
            TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => s,
            _ => return Some(cur),
        };
        match resolve_sort_alias(kb, base) {
            None => return Some(cur),
            Some(target) => cur = Value::term(target),
        }
    }
    None
}

/// How many `sort X = Y` links [`effect_label_kind`] follows before giving up. Generous:
/// the longest chain in the tree is one.
const ALIAS_CHAIN_LIMIT: usize = 16;

/// WI-20260823-VM3YB — every REGISTERED effect kind, as canonical sort symbols.
///
/// `param` is `Effect`'s declared type parameter. The lookup runs in
/// [`BindingKeyMatch::Label`] rather than by identity: a registration written inside the
/// KIND's own body (`sort Modify { provides Effect[T = Modify[?]] }`) keys the slot with
/// the name as WRITTEN, which resolves against the enclosing sort's own `T`, while one
/// written elsewhere keys it with the resolved `Effect.T`. Both name the same parameter
/// of the ONE sort `Effect`, and the label is what says so.
fn registered_effect_kinds(
    kb: &KnowledgeBase,
    effect_sym: Symbol,
    param: Symbol,
) -> HashSet<Symbol> {
    let mut out: HashSet<Symbol> = HashSet::new();
    for row in all_provisions(kb) {
        if kb.canonical_sort_sym(row.spec) != kb.canonical_sort_sym(effect_sym) {
            continue;
        }
        let Some((_, bindings)) = unwrap_spec_view(kb, row.spec_view) else {
            continue;
        };
        let Some(binding) = binding_for_param(kb, &bindings, param, BindingKeyMatch::Label) else {
            continue;
        };
        // The registration binds a KIND: `Modify[?]` registers `Modify`, `Branch`
        // registers `Branch`. Read through the same classifier the labels are read
        // through, so a shape that is a label on one side is a registration on the other.
        if let Some(k) = match type_head(kb, &Value::term(*binding)) {
            TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => Some(s),
            _ => None,
        } {
            out.insert(kb.canonical_sort_sym(k));
        }
    }
    out
}

/// What stands in a `Modify`'s target slot. See [`classify_modify_target`].
#[derive(Clone, Copy, PartialEq, Eq)]
enum ModifyTarget {
    /// A DENOTED place occurrence — the lawful shape.
    Place,
    /// A sort ref, a type-param var, an `ExprCarried` type projection (`s.T`) — anything
    /// that names a TYPE rather than a slot in `Env`.
    Type,
    /// No target binding at all — a bare `Modify`.
    Missing,
}

/// The two interned keys [`classify_modify_target`] needs, hoisted so a caller in a loop
/// interns once rather than per label (interning takes `&mut kb`, which the classifier
/// deliberately does not).
struct ModifyTargetKeys {
    pub(super) t: Symbol,
    pub(super) label: Symbol,
}

impl ModifyTargetKeys {
    pub(super) fn new(kb: &mut KnowledgeBase) -> Self {
        Self {
            t: kb.intern("T"),
            label: kb.intern("label"),
        }
    }
}

/// WI-20260823-39AD2 — is this effect-row element a `Modify`, and if so what stands in
/// its target slot? Returns the PEELED label beside the verdict; `None` when the element
/// is not a `Modify` at all.
///
/// TWO CALLERS, ONE CLASSIFICATION, and they are two different questions asked of one
/// fact — which is exactly why they must not each write their own predicate:
///   * [`check_modify_targets`] REPORTS a non-place target, at the declaration.
///   * [`check_override_refinement`]'s effects leg SKIPS an atom with one, on either
///     side, because the refusal belongs to that declaration and reporting a coverage
///     consequence here would send the author to a line whose repair would not load.
///
/// The atom wrappers are peeled first ([`peel_effect_atom`]): a row element is not always
/// the bare label, and asking the question of the wrapper answers about the wrapper.
fn classify_modify_target(
    kb: &KnowledgeBase,
    e: &Value,
    modify: Option<Symbol>,
    keys: &ModifyTargetKeys,
) -> Option<(Value, ModifyTarget)> {
    // WI-20260831-RSRP5 — NO ALIAS WALK HERE, deliberately, and it was measured before it
    // was removed. A bound row alias (`effects E = Modify[Thing]`) does have to be
    // followed before this predicate can answer, but every caller now arrives through
    // [`effect_element_labels`], which follows it (and explodes a row behind it) as one
    // walk. Adding a second resolution inside this function made the route-B fixture pass
    // and then survived its own back-out — the sign of a branch that fires nowhere. The
    // one call site that still passes a RAW element ([`check_override_refinement`]'s
    // `malformed_modify`) is dead by construction for the reason recorded at it: the
    // shape it screens for no longer loads, because [`check_modify_targets`] — through
    // that same walk — refuses it first.
    let label = peel_effect_atom(kb, e, keys.label);
    if !effect_is_modify(kb, &label, modify) {
        return None;
    }
    // The target rides the `T` binding — `Modify[c]` lowers positionally onto `Modify`'s
    // declared `sort T = ?`. The positional slot is read too, so a shape that never
    // reached the named form is JUDGED rather than skipped.
    let target = label.named_arg(kb, keys.t).or_else(|| label.pos_arg(kb, 0));
    let kind = match target {
        None => ModifyTarget::Missing,
        Some(t) if matches!(type_head(kb, &t), TypeHead::Denoted) => ModifyTarget::Place,
        Some(_) => ModifyTarget::Type,
    };
    Some((label, kind))
}

/// WI-431 (B) — INSTANCE-FACT op-binding SIGNATURE validation. An instance fact
/// `fact Spec[<carrier param> = C, op = boundOp, …]` makes `boundOp` back the
/// spec op `Spec.op` for carrier `C` (rule 1 coverage + increments 2/4 dispatch).
/// Nothing else checks `boundOp`'s SIGNATURE against `Spec.op`'s, so a mis-bound
/// op (`combine = unrelatedOp`) would load and then dispatch to a wrongly-typed
/// impl. This pass checks, with σ (the spec's type parameter → its provision
/// binding) applied to the spec op's types: same param ARITY; each PARAM type
/// contravariantly compatible (the bound op accepts the spec's arg type); the
/// RETURN type covariantly compatible. Type comparisons are GROUND-GATED — only
/// when neither the σ-substituted spec type nor the bound type mentions a type
/// parameter, on either carrier — so a higher-kinded binding whose param stays
/// parametric (`pure : F[T = A]`) fails open, deferred to WI-383. (Until
/// WI-20260923-Z1Q8B the gate demanded two `Value::Term`s, which skipped every type
/// carrying a denoted — see [`instance_binding_type_ok`].) Arity is always checked.
/// A dedicated pass (not folded into [`check_override_refinement`]) because the two
/// compare DIFFERENT things: this one an op-valued BINDING (`combine = wrongOp`),
/// which names a free operation the author wrote out, and the other a carrier's own
/// MEMBER. WI-20260822-1MAGR gave the member half its own comparison
/// ([`check_member_signature`]) after measuring what the carrier-own population
/// needs and this one does not — the SELF-RECEIVER exemption, the expression-
/// projection gate, and the sole-backing gate, none of which a bound free operation
/// can want. (When this pass was written the reason given here was instead that
/// instance facts had no stdlib presence, so it could be strict without measuring;
/// that was true and is no longer the distinction.)
pub fn check_instance_fact_op_signatures(
    kb: &mut KnowledgeBase,
) -> Vec<crate::kb::load::LoadError> {
    use crate::kb::load::LoadError;
    // Spec's own declared ops, to resolve a binding key's short name → the spec op.
    let own: HashMap<Symbol, Vec<Symbol>> =
        crate::kb::load::sorts_and_own_ops(kb).into_iter().collect();

    // Snapshot the INSTANCE-FACT provisions before the (mutating) type checks:
    // carrier, spec base, σ (type-param bindings), and the op-valued bindings
    // (binding-key short name → bound operation). A provision with no op binding
    // is a plain type-only provision and is skipped.
    struct Prov {
        carrier: Symbol,
        spec: Symbol,
        sigma: Vec<(Symbol, TermId)>,
        ops: Vec<(String, Symbol)>,
    }
    let provs: Vec<Prov> = provides_rows(kb)
        .filter_map(|row| {
            let spec_qn = kb.qualified_name_of(row.spec_base);
            // The op-valued bindings: every binding [`spec_param_sigma`] does not take.
            let ops: Vec<(String, Symbol)> = row
                .bindings
                .iter()
                .filter(|(k, _)| !is_type_param_binding(kb, *k, spec_qn))
                .filter_map(|(k, v)| {
                    let bound_op = binding_op_symbol(kb, *v)?;
                    Some((
                        short_name_of(kb.qualified_name_of(*k)).to_string(),
                        bound_op,
                    ))
                })
                .collect();
            if ops.is_empty() {
                return None;
            }
            Some(Prov {
                carrier: row.provider,
                spec: row.spec_base,
                sigma: spec_param_sigma(kb, row.spec_base, &row.bindings),
                ops,
            })
        })
        .collect();

    let mut errors = Vec::new();
    for p in &provs {
        let Some(spec_ops) = own.get(&p.spec) else {
            continue;
        };
        // Per-provision invariants — hoisted out of the per-binding loop.
        let carrier_qn = kb.qualified_name_of(p.carrier).to_string();
        let spec_qn = kb.qualified_name_of(p.spec).to_string();
        for (op_short, bound_op) in &p.ops {
            // The spec op the binding key names. A key naming no spec op is the
            // coverage check's concern, not this one.
            let Some(&spec_op) = spec_ops
                .iter()
                .find(|&&o| short_name_of(kb.qualified_name_of(o)) == *op_short)
            else {
                continue;
            };
            let Some(spec_info) = crate::kb::op_info::lookup_operation_info(kb, spec_op) else {
                continue;
            };
            let Some(bound_info) = crate::kb::op_info::lookup_operation_info(kb, *bound_op) else {
                continue;
            };
            let bound_qn = kb.qualified_name_of(*bound_op).to_string();

            // ── arity (always checkable) ────────────────────────────────────
            if spec_info.params.len() != bound_info.params.len() {
                errors.push(LoadError::IncompatibleInstanceBinding {
                    carrier: carrier_qn.clone(),
                    spec: spec_qn.clone(),
                    op: op_short.clone(),
                    reason: format!(
                        "the spec operation takes {} parameter(s) but the bound operation '{}' takes {}",
                        spec_info.params.len(), bound_qn, bound_info.params.len()),
                });
                continue;
            }

            // ── per-param type (contravariant: σ(spec_param) <: bound_param) ─
            for (i, ((_, spec_pty), (_, bound_pty))) in spec_info
                .params
                .iter()
                .zip(bound_info.params.iter())
                .enumerate()
            {
                if instance_binding_type_ok(kb, spec_pty, bound_pty, &p.sigma, false) == Some(false)
                {
                    let bound_disp = type_display_name_value(kb, bound_pty);
                    let spec_sub = sigma_subst_type(kb, spec_pty, &p.sigma);
                    let spec_disp = type_display_name_value(kb, &spec_sub);
                    errors.push(LoadError::IncompatibleInstanceBinding {
                        carrier: carrier_qn.clone(),
                        spec: spec_qn.clone(),
                        op: op_short.clone(),
                        reason: format!(
                            "parameter {} of the bound operation has type `{}`, incompatible with the spec parameter type `{}`",
                            i + 1, bound_disp, spec_disp),
                    });
                }
            }

            // ── return type (covariant: bound_ret <: σ(spec_ret)) ───────────
            if instance_binding_type_ok(
                kb,
                &spec_info.return_type,
                &bound_info.return_type,
                &p.sigma,
                true,
            ) == Some(false)
            {
                let bound_disp = type_display_name_value(kb, &bound_info.return_type);
                // At THIS provision's bindings, as the verdict compared it (and as the
                // member-signature messages print it): `Foo[T = Tag, N = 3]`, not the
                // declared `Foo[T = T, N = 3]` that `T = Int64` would seem to satisfy.
                let spec_sub = sigma_subst_type(kb, &spec_info.return_type, &p.sigma);
                let spec_disp = type_display_name_value(kb, &spec_sub);
                errors.push(LoadError::IncompatibleInstanceBinding {
                    carrier: carrier_qn.clone(),
                    spec: spec_qn.clone(),
                    op: op_short.clone(),
                    reason: format!(
                        "the bound operation returns `{}`, incompatible with the spec return type `{}`",
                        bound_disp, spec_disp),
                });
            }
        }
    }
    errors
}

/// WI-431 (B): compare one bound-op type against the σ-substituted spec-op type.
/// `Some(true)` confidently compatible, `Some(false)` a confident mismatch (→ a loud
/// error), `None` not confident — a type σ leaves PARAMETRIC, which fails open (the
/// higher-kinded case, deferred to WI-383).
/// `bound_is_subtype`: the return is covariant (`bound <: σ(spec)`), a param is
/// contravariant (`σ(spec) <: bound` — the bound op must accept the spec's arg).
///
/// WI-20260923-Z1Q8B — DECIDABLE IS NOT "HASH-CONSED", the correction
/// WI-20260822-1TKN0 made to the effects leg and 87246ea2 to the return leg of
/// [`check_override_refinement`]. This answered `None` for ANY `Value::Node`, calling
/// it "a non-ground / `Value::Node` parametric type" — the CARRIER read where
/// ABSTRACTNESS was meant. A type rides the occurrence carrier because it carries a
/// denoted, the literal `3` in `Foo[T = Int64, N = 3]`, not because it is parametric,
/// so every caller — the WI-1MAGR member signature, its order search, and
/// [`check_instance_fact_op_signatures`] — loaded a mismatch over one clean.
/// MEASURED: a member returning `Foo[T = String, N = 3]` for a body-less spec op
/// returning `Foo[T = Int64, N = 3]` loaded with zero errors, while the same program
/// over `Int64` / `Bool` was refused.
///
/// Both halves now read the type as a `Value`: σ through [`sigma_subst_type`], the one
/// Value-level σ (this function used to run its own `TermId`-only σ, so a spec parameter
/// beneath a denoted — `Foo[T = T, N = 3]` — could not have grounded behind any gate),
/// and the gate through [`view_contains_type_param`], which on the term carrier decides
/// arm for arm what `contains_type_param` did. Two hash-consed types still meet in
/// `types_compatible`'s term dispatch, so the verdict on that carrier cannot move.
fn instance_binding_type_ok(
    kb: &mut KnowledgeBase,
    spec_ty: &Value,
    bound_ty: &Value,
    sigma: &[(Symbol, TermId)],
    bound_is_subtype: bool,
) -> Option<bool> {
    let spec_sub = sigma_subst_type(kb, spec_ty, sigma);
    // Confident only when neither side mentions a type parameter.
    if view_contains_type_param(kb, &spec_sub) || view_contains_type_param(kb, bound_ty) {
        return None;
    }
    let mut subst = Substitution::new();
    Some(if bound_is_subtype {
        types_compatible(kb, &mut subst, bound_ty, &spec_sub)
    } else {
        types_compatible(kb, &mut subst, &spec_sub, bound_ty)
    })
}

/// WI-1048 — can a call site CONFUSE a requires-shadow with the operation it
/// shadows? This is the gate on WI-346's lint (`load::check_requires_shadows`),
/// which until now compared SHORT NAMES ONLY and so could not tell a deliberate
/// REFINEMENT from an accidental collision.
///
/// The lint exists for the author who believed `requires` overrides. That belief
/// only costs anything when the two operations are INTERCHANGEABLE at a call
/// site: `xs.op(…)` picks one, the author expected the other, and nothing
/// complains. When the two are distinguishable — different arity, a different
/// parameter type, a different return type — they are distinct operations by
/// construction, dispatch picks the more specific one deterministically, and a
/// mismatched expectation is already a LOUD type error naming both types
/// (measured on `FiniteCollection.map` vs `Iterable.map`, WI-1048).
///
/// So: **warn unless the two are confidently distinguishable.** Every leg that
/// cannot be decided falls open to "confusable" — i.e. to warning, WI-346's
/// pre-existing behaviour. The lint can therefore only get QUIETER where a
/// difference is proven, never silently retire itself on a comparison this
/// function failed to make.
///
/// Legs, in order:
///  * ARITY — always decidable.
///  * PARAM types, pairwise — decided only when both sides are `Value::Term`.
///    A callback parameter carrying a `denoted` effect (`-Modify[x]`) is a
///    `Value::Node` with no `TermId`, so σ cannot rewrite it and it is not
///    compared. Both `map`/`filter` pairs have exactly such a parameter, which
///    is why the param leg is NOT what silences them.
///  * RETURN type — same `Value::Term` gate. This is the leg that decides the
///    stdlib pair (`Stream[…]` vs `FiniteCollection[…]`, different functors).
///
/// EFFECTS are deliberately NOT a leg. An effect row does not distinguish two
/// operations at a call site — the call is spelled identically either way — and
/// an author who restated the spec's signature with a narrower row is exactly
/// the author who believed `requires` overrides. Adding effects would silence
/// that. (Effect refinement IS checked, on the `provides` direction, by
/// [`check_override_refinement`].)
///
/// Params are paired POSITIONALLY, as in [`check_override_refinement`] and
/// [`check_instance_fact_op_signatures`] — an override aligns with the spec by
/// position, not by parameter name.
///
/// A type leg is decided by [`types_definitely_differ`], for which a type
/// PARAMETER is a wildcard: `requires Pingable` binding nothing leaves the spec
/// op's `x: Pingable.T` un-σ-substituted, and an unbound parameter is not a
/// different type from the shadow's `x: Int64` — it is an UNKNOWN one, which
/// `Int64` instantiates. That case must keep warning, and does.
///
/// `spec_view` is the `requires Spec[…]` clause, whose type-param bindings are
/// σ: the spec's parameters are rewritten into the shadowing sort's vocabulary
/// before comparison (`Sp.T ↦ Carrier`), exactly as
/// [`check_instance_fact_op_signatures`] does for a provision. Its OP bindings
/// are not σ and are skipped by [`type_param_sym_of_binding`]. σ is what lets a
/// leg be decided at all where the spec states its type abstractly.
pub(crate) fn requires_shadow_is_confusable(
    kb: &mut KnowledgeBase,
    spec: Symbol,
    spec_op: Symbol,
    local_op: Symbol,
    spec_view: &Value,
) -> bool {
    // No `OperationInfo` for one of them ⇒ nothing to compare ⇒ warn.
    let (Some(spec_info), Some(local_info)) = (
        crate::kb::op_info::lookup_operation_info(kb, spec_op),
        crate::kb::op_info::lookup_operation_info(kb, local_op),
    ) else {
        return true;
    };
    if spec_info.params.len() != local_info.params.len() {
        return false; // different arity — a call site cannot confuse them
    }
    let sigma: Vec<(Symbol, TermId)> = unwrap_spec_view_value(kb, spec_view)
        .map(|(_, bindings)| spec_param_sigma(kb, spec, &bindings))
        .unwrap_or_default();

    // Params then return, cloned out of the two records so the `&mut kb`
    // substitution below is not fighting the borrow they are read through.
    let pairs: Vec<(Value, Value)> = spec_info
        .params
        .iter()
        .map(|(_, t)| t)
        .chain(std::iter::once(&spec_info.return_type))
        .zip(
            local_info
                .params
                .iter()
                .map(|(_, t)| t)
                .chain(std::iter::once(&local_info.return_type)),
        )
        .map(|(s, l)| (s.clone(), l.clone()))
        .collect();
    for (spec_ty, local_ty) in pairs {
        let (Value::Term { id: spec_t, .. }, Value::Term { id: local_t, .. }) =
            (&spec_ty, &local_ty)
        else {
            continue; // a denoted carrier — undecidable, falls open to "confusable"
        };
        let spec_sub = if sigma.is_empty() {
            *spec_t
        } else {
            substitute_impl_params_alloc(kb, *spec_t, &sigma)
        };
        if types_definitely_differ(kb, spec_sub, *local_t) {
            return false; // a confidently different type — distinct operations
        }
    }
    true
}

/// WI-1048 — can these two type terms NEVER denote the same type? The
/// one-directional half of a comparison: `true` is a proof of difference,
/// `false` means "same, or not provably different". Never the other way round,
/// because [`requires_shadow_is_confusable`] warns on everything it cannot
/// prove distinct.
///
/// A TYPE PARAMETER on either side is a WILDCARD — that is the whole subtlety
/// here, and two independent cases need it:
///  * an UNBOUND spec parameter. `requires Pingable` (no bindings) leaves the
///    spec op's `x: Pingable.T` with nothing for σ to substitute; against the
///    shadow's `x: Int64` that is not a difference, it is an unknown that
///    `Int64` instantiates. Calling it "different" would silence exactly the
///    accidental collision WI-346 exists for.
///  * each operation's OWN variable for its own type parameter.
///    `Iterable.map[Dst]` and `FiniteCollection.map[Dst]` both spell `Dst`, but
///    the loader mints a distinct `VarId` per operation (`VarId` compares by id,
///    not name), so hash-cons identity reads two identical signatures as
///    different — retiring the lint for precisely the generic operations it most
///    needs to cover.
/// Both are wildcards, so neither can carry a proof of difference. What DOES
/// carry one is a disagreement at a position where neither side is a parameter:
/// `Stream[…]` vs `FiniteCollection[…]` differ in their head functor, which no
/// instantiation can reconcile — the stdlib pair, decided.
///
/// ELISION IS NOT DIFFERENCE, and it is the second thing that has to fall open.
/// `Stream[T = Int64]` and `Stream[T = Int64, E = {}]` name the same constructor;
/// the first simply leaves `E` unstated, and an unstated argument instantiates to
/// whatever stands opposite it. So is a bare `List` against `List[T = Int64]` —
/// a name reference IS the nullary spelling of its own constructor, which is what
/// [`type_ctor_view`] reads both sides through. Hence only positions BOTH sides
/// state are compared, and a differing argument COUNT proves nothing: what proves
/// a difference is the head constructor disagreeing, or a stated argument the two
/// give incompatible values for.
///
/// Anything that is not constructor-headed on both sides is UNDECIDED, not
/// different — the fail-open direction the contract above requires. Hash-cons
/// identity would be exact for two ground literals but wrong for every mixed
/// pair, and this predicate is not the place to enumerate which is which.
fn types_definitely_differ(kb: &KnowledgeBase, a: TermId, b: TermId) -> bool {
    if a == b {
        return false;
    }
    // `is_type_param_value` tests the HEAD, which is what a wildcard needs: a
    // parameter NESTED inside a concrete constructor (`List[T = C]`) leaves the
    // constructor itself decidable, and the nested position is reached by the
    // recursion below and wildcarded there.
    if is_type_param_value(kb, a) || is_type_param_value(kb, b) {
        return false;
    }
    let (Some((fa, pa, na)), Some((fb, pb, nb))) = (type_ctor_view(kb, a), type_ctor_view(kb, b))
    else {
        return false; // not constructor-headed on both sides — undecided
    };
    if fa != fb {
        return true; // a different constructor, which no instantiation reconciles
    }
    // Shared positions only. A position one side elides is unstated, not other.
    if pa
        .iter()
        .zip(pb.iter())
        .any(|(x, y)| types_definitely_differ(kb, *x, *y))
    {
        return true;
    }
    na.iter().any(|(k, x)| {
        nb.iter()
            .find(|(k2, _)| k2 == k)
            .is_some_and(|(_, y)| types_definitely_differ(kb, *x, *y))
    })
}

/// A type term read as `(constructor, positional args, named args)`. A bare name
/// reference is its own constructor applied to nothing — `Ref(List)` and
/// `Fn{List, [], [T = Int64]}` are the same constructor, one stating an argument
/// the other elides. `None` for a term that names no constructor at all (a
/// literal, a tuple), which [`types_definitely_differ`] treats as undecided.
/// WI-1048.
///
/// The `Ref`/`Ident`/nullary-`Fn` collapse is load-bearing beyond the elision
/// case: it is the same equivalence [`substitute_impl_params_alloc`] rewrites
/// between (see [`view_ref_symbol`], its owner on the `requires`-binding
/// side), so a σ-substituted spec type compares equal to the identical type the
/// loader built directly. Without it the two `*_is_silent` tests in
/// `wi1048_requires_shadow_refinement_test` go undecided — measured, they are
/// what fails.
///
/// WI-1052 — A SORT ALIAS IS EXPANDED FIRST, for the same reason. `sort IntList =
/// List[T = Int64]` names one type twice, so reading `IntList` as its own
/// constructor made it "definitely different" from `List[T = Int64]` — a FALSE
/// proof, and one that fails CLOSED: [`types_definitely_differ`] is consulted to
/// decide whether a shadow is confusable, so a bogus difference SILENCES the
/// warning. Measured, with a control: the fixture in
/// `wi1052_alias_spelled_return_type_still_warns` loaded silent while the same
/// file with the alias written out warned — a verdict turning on how the author
/// spelled a type, which is exactly what WI-1048 exists to stop.
///
/// Only the BARE-NAME spelling is followed (`Ref`/`Ident`/argument-less `Fn`).
/// An alias head carrying arguments would lose them if the expansion simply
/// replaced the term, and UNDECIDED is the safe answer there — as it is when the
/// chain exceeds [`ALIAS_EXPANSION_LIMIT`], which is a bound on user input rather
/// than a claim that no alias chain is longer.
pub(super) fn type_ctor_view(
    kb: &KnowledgeBase,
    t: TermId,
) -> Option<(
    Symbol,
    SmallVec<[TermId; 4]>,
    SmallVec<[(Symbol, TermId); 2]>,
)> {
    let mut t = t;
    for _ in 0..ALIAS_EXPANSION_LIMIT {
        let (sym, view) = match kb.get_term(t) {
            Term::Fn {
                functor,
                pos_args,
                named_args,
            } => (*functor, (*functor, pos_args.clone(), named_args.clone())),
            Term::Ref(s) | Term::Ident(s) => (*s, (*s, SmallVec::new(), SmallVec::new())),
            _ => return None, // not constructor-headed — undecided
        };
        // Bare name only: an application states arguments the expansion does not.
        if view.1.is_empty() && view.2.is_empty() {
            if let Some(expanded) = resolve_sort_alias(kb, sym) {
                // `!=` catches a one-step self-alias; the loop bound catches longer
                // cycles, so neither can spin here.
                if expanded != t {
                    t = expanded;
                    continue;
                }
            }
        }
        return Some(view);
    }
    None
}

/// WI-1052 — how many `SortAlias` hops [`type_ctor_view`] follows before giving up
/// and answering UNDECIDED. Chains in the corpus are one hop; the bound exists so a
/// cyclic or pathological set of aliases cannot spin, not because a longer chain is
/// known to be illegal.
const ALIAS_EXPANSION_LIMIT: usize = 16;

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
///     never by position: `test.wi596.Bag.holds(x: T, b: Bag)` puts it second. This
///     comparison passes every such parameter; only the RECEIVER is sound by dispatch,
///     and [`member_narrower_than_spec`] refuses a member narrowing a SECOND one to the
///     carrier (`combine(a: Widget, b: Widget)`, `b` admitting any provider).
///   * A TYPE CARRYING AN EXPRESSION PROJECTION (`s.T`, WI-376). σ binds the
///     spec's TYPE PARAMETERS; it cannot ground a projection off the operation's
///     own parameter, and the two operations' receivers are different parameters,
///     so `Stream.splitFirst`'s `s.T` and `List.splitFirst`'s `xs.T` are two
///     distinct neutrals that [`types_compatible`] refuses (`expr_carried_zeta`:
///     "a neutral projection is equal only to an identical neutral").
///     [`member_narrower_than_spec`] relates them — the parameters and the return —
///     reading each projection as the call reads it, off the argument it projects.
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
    provision: &ProvisionMembers,
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
    // so nothing above the failure branches allocates — but the member rule below, which
    // builds the spec's arguments on the success path too: only for a GATED pair, and its
    // per-provision half once per provision ([`ProvisionMembers`]).
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
    // The member's parameters by the spec's names, positionally: a type naming one by value
    // (a callback's `Modify[p]`) names the spec's `p` in the spec and the member's in the
    // member, two symbols, so a verbatim member compared unequal (WI-20260929-0RP29, MEASURED).
    let impl_to_spec: HashMap<Symbol, Symbol> = impl_info
        .params
        .iter()
        .zip(&spec_info.params)
        .filter(|((m, _), (s, _))| m != s)
        .map(|((m, _), (s, _))| (*m, *s))
        .collect();
    let mut bad: Vec<usize> = Vec::new();
    for i in 0..n {
        let (_, spec_pty) = &spec_info.params[i];
        let (_, impl_pty) = &impl_info.params[i];
        let impl_pty = if impl_to_spec.is_empty() {
            impl_pty.clone()
        } else {
            substitute_ref_syms_value(kb, impl_pty, &impl_to_spec)
        };
        if instance_binding_type_ok(kb, spec_pty, &impl_pty, sigma, false) != Some(false) {
            continue;
        }
        // THE SELF-RECEIVER, and the projection gate — see the doc above. Both are
        // reached only by a position that has ALREADY compared as incompatible, which
        // is why the canonicalizations sit here rather than above the loop.
        let is_receiver = sort_functor_of_view(kb, spec_pty)
            .is_some_and(|b| kb.canonical_sort_sym(b) == kb.canonical_sort_sym(spec))
            && sort_functor_of_view(kb, &impl_pty)
                .is_some_and(|b| kb.canonical_sort_sym(b) == kb.canonical_sort_sym(carrier));
        let carries_projection =
            value_contains_projection(kb, spec_pty) || value_contains_projection(kb, &impl_pty);
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

    // ── the member takes every argument list the spec takes, and returns what it promises ──
    let fit = member_narrower_than_spec(
        kb,
        carrier,
        spec,
        spec_op,
        spec_info,
        impl_info,
        sigma,
        provision,
        &impl_to_spec,
    );
    if let MemberFit::Narrower(n) = fit {
        let spec_sig = render_op_signature(kb, op_short, spec_info, sigma);
        let impl_sig = render_op_signature(kb, op_short, impl_info, &[]);
        let sigs = format!(
            "The spec declares `{spec_sig}` (at this provision's bindings) and the member is \
             `{impl_sig}`"
        );
        // The two types as compared where the rule read them otherwise than the declarations
        // print (a projection read, a receiver typed by the spec, a return), else as declared.
        let (decl_spec, decl_member) = match n.at {
            Some(i) => (&spec_info.params[i].1, &impl_info.params[i].1),
            None => (&spec_info.return_type, &impl_info.return_type),
        };
        let got_decl = member_type_display(kb, decl_member);
        let (want, got) = match &n.compared {
            Some((w, g)) => (member_type_display(kb, w), member_type_display(kb, g)),
            None => {
                let sub = sigma_subst_type(kb, decl_spec, sigma);
                (member_type_display(kb, &sub), got_decl.clone())
            }
        };
        // Two sides that PRINT ALIKE differ where this rendering does not look: only a top-level
        // arrow prints its row ([`member_type_display`]), and a rigid and a flexible variable
        // share one name. Said, where the refusal would otherwise read as a tautology (`Box[T =
        // Int64 -> Int64]` "admits arguments" `Box[T = Int64 -> Int64]` "does not").
        let sigs = if want == got {
            format!(
                "{sigs}. The two types compared print alike: they differ in a part this \
                 rendering leaves out — the effect row of a function type inside them, or two \
                 variables of one name"
            )
        } else {
            sigs
        };
        let carrier_short = kb.local_name_of(carrier).to_string();
        let spec_short = kb.local_name_of(spec).to_string();
        let reason = match (n.at, n.why) {
            (None, Narrower::Return { unwritten }) => format!(
                "the member returns `{got}`, which is not a subtype of the spec's `{want}`, each \
                 read as a call reads it at the spec's arguments — {sigs}{}",
                if unwritten {
                    ". The member's return leaves a slot unwritten, which is a type the member \
                     picks and no caller knows: write it, or name it by a type parameter of the \
                     member's that one of its parameters fixes"
                } else {
                    ""
                }
            ),
            (None, Narrower::Unreadable { spec, why }) => format!(
                "the {} return type does not read at the spec's arguments — {why}. {sigs}",
                if spec { "spec's" } else { "member's" }
            ),
            (Some(i), why) => {
                let name = kb.local_name_of(impl_info.params[i].0).to_string();
                let at = format!("parameter {} (`{name}: {got_decl}`)", i + 1);
                let narrower = |why: String| {
                    format!(
                        "{at} takes less than the spec's, so a call written against the spec \
                         can pass it an argument its own signature refuses — {why}. {sigs}"
                    )
                };
                match why {
                    Narrower::Receiver { by_spec: true, .. } => narrower(format!(
                        "`{name}` is the receiver, and the spec receives every provider of \
                         `{spec_short}` this provision covers, as `{want}`, where the member's \
                         `{got}` does not take them all; type `{name}` as the spec writes it at \
                         this provision, or write the restriction into the spec's receiver"
                    )),
                    Narrower::Receiver {
                        written: false,
                        sort,
                        ..
                    } => {
                        let recv_short = kb.local_name_of(sort).to_string();
                        narrower(format!(
                            "`{name}` is the receiver, and the spec receives every \
                             `{recv_short}` this provision covers, where the member's `{got}` \
                             fixes what the spec leaves open; type `{name}` as `{recv_short}` at \
                             its own parameters, or write the restriction into the spec's receiver"
                        ))
                    }
                    Narrower::Receiver { sort, .. } => {
                        let recv_short = kb.local_name_of(sort).to_string();
                        narrower(format!(
                            "`{name}` is the receiver, and the spec receives every \
                             `{recv_short}` its receiver's type admits at this provision's \
                             bindings (`{want}`), where the member's `{got}` does not take them \
                             all; type `{name}` as the spec writes it"
                        ))
                    }
                    Narrower::AnyProvider => narrower(format!(
                        "the spec's `{want}` admits any provider of `{spec_short}`, and the \
                         member's `{got}` only a `{carrier_short}`; type `{name}` by the spec, or \
                         make the spec parameter the receiver's type"
                    )),
                    Narrower::Tied { with: None } => narrower(format!(
                        "inside `{carrier_short}` a bare `{carrier_short}`, or one written with \
                         `{carrier_short}`'s own parameters, is THIS instance (the parametricity \
                         tie), so the member's `{got}` ties `{name}` to the receiver, where the \
                         spec's `{want}` need not be the receiver's instance; give `{name}`'s \
                         `{carrier_short}` type arguments of its own, or tie the two in the spec"
                    )),
                    // No receiver: the instance is whichever the first parameter naming it took.
                    Narrower::Tied { with: Some(j) } => {
                        let first = kb.local_name_of(impl_info.params[j].0).to_string();
                        narrower(format!(
                            "inside `{carrier_short}` a bare `{carrier_short}`, or one written \
                             with `{carrier_short}`'s own parameters, is THIS instance (the \
                             parametricity tie), so the member's `{got}` ties `{name}` to \
                             `{first}`, where the spec's `{want}` is an instance of its own; give \
                             `{name}`'s `{carrier_short}` type arguments of its own, or tie the \
                             two in the spec"
                        ))
                    }
                    Narrower::Other => narrower(format!(
                        "the spec's `{want}` admits arguments the member's `{got}` does not; \
                         widen the member's parameter to the spec's type"
                    )),
                    Narrower::Circular { binding, sort } => {
                        let recv_short = kb.local_name_of(sort).to_string();
                        let b = type_display_name_value(kb, &Value::term(binding));
                        format!(
                            "{at} is the receiver, and the provision binds its type to `{b}`, \
                             which writes one of `{recv_short}`'s own parameters inside its own \
                             slot — no `{recv_short}` is that type, so no call written against \
                             the spec reaches this member; write that slot as `?` (any type), \
                             leave it unwritten, or bind a parameter of the spec's to what it was \
                             meant to name. {sigs}"
                        )
                    }
                    Narrower::Unreadable { spec: true, why } => format!(
                        "{at}: the spec's `{want}` does not read at this provision — {why}. {sigs}"
                    ),
                    Narrower::Unreadable { spec: false, why } => {
                        format!("{at} does not read at the spec's arguments — {why}. {sigs}")
                    }
                    Narrower::Return { .. } => {
                        panic!("member_narrower_than_spec: a return refusal names a parameter")
                    }
                }
            }
            (None, why) => panic!(
                "member_narrower_than_spec: a parameter's refusal kind without a parameter ({})",
                match why {
                    Narrower::Receiver { .. } => "Receiver",
                    Narrower::AnyProvider => "AnyProvider",
                    Narrower::Tied { .. } => "Tied",
                    Narrower::Other => "Other",
                    Narrower::Circular { .. } => "Circular",
                    Narrower::Unreadable { .. } | Narrower::Return { .. } => "unreachable",
                }
            ),
        };
        refuse(kb, errors, reason);
        return MemberSignature::Alignable;
    }

    // ── return type (covariant: member <: σ(spec)) ──────────────────────────
    // Where the rule above compared it, it is judged: as a call reads it, which this raw-σ
    // comparison is not (a bare carrier binding is any instance here, and a return naming a
    // type parameter is undecided — MEASURED: `-> Car[V = Int64]` behind `-> T` at `T = Car`
    // loaded and a spec call read a `String` off it). It stays for the member no call written
    // against the spec reaches, which the rule compares nothing of — by the spec's names, as the
    // parameters above are (a verbatim `-> Buf[T = Int64, N = n]` named two `n`s and was
    // refused printing one type twice, MEASURED).
    if !matches!(fit, MemberFit::Unreached) {
        return MemberSignature::Alignable;
    }
    let impl_return = if impl_to_spec.is_empty() {
        impl_info.return_type.clone()
    } else {
        substitute_ref_syms_value(kb, &impl_info.return_type, &impl_to_spec)
    };
    if instance_binding_type_ok(kb, &spec_info.return_type, &impl_return, sigma, true)
        == Some(false)
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

/// WI-20260929-0RP29 — what [`member_narrower_than_spec`] reads of a PROVISION, built on the
/// first gated member that asks and shared by the rest of its operations: a provision whose
/// spec backs every operation with a body pays nothing.
pub(super) struct ProvisionMembers<'a> {
    spec: Symbol,
    /// The declaring sort, whose members are compared and whose own parameters a member's
    /// self references denote.
    carrier: Symbol,
    /// The provision's bindings AS THE `provides` FACT STORES THEM — spec parameter ↦ the type
    /// the clause wrote (`provides Sp[T = List[T = V]]` ⟹ `T ↦ List[T = V]`), read off the
    /// fact's spec-view term ([`spec_param_sigma`]). STORED DATA, not the result of a
    /// substitution, which is why it is `TermId`s: a fact's arguments are hash-consed. It is
    /// called σ for its USE — the spec's signature with each parameter reference replaced by
    /// its binding ([`sigma_subst_type`]). Everything DERIVED from it is a `Value`
    /// ([`ProvisionShared::template`]).
    sigma: &'a [(Symbol, TermId)],
    /// The sort the spec's carrier parameter is bound to where it is not the declaring sort
    /// (a WITNESS's carrier: `BoxHolder provides Holder[C = Box]` receives a `Box`).
    witness: Option<Symbol>,
    shared: std::cell::OnceCell<ProvisionShared>,
}

/// The per-provision half of [`member_narrower_than_spec`]'s arguments ([`ProvisionMembers`]).
struct ProvisionShared {
    /// The witness's carrier, canonical ([`ProvisionMembers::witness`]).
    witness: Option<Symbol>,
    /// The declaring sort at its own parameters: a member's bare self reference, and the
    /// instance a self-receiver receives.
    own_decl: TermId,
    /// σ as a call reads it, ONCE per spec parameter. The provision is written inside the
    /// declaring sort, so a reference to that sort in a binding reads as it does in the sort's
    /// own operations (§3's tie): bare, or with a slot unwritten, it is THIS instance — at any
    /// depth, whichever parameter it binds and whether an operation receives on it. A FOREIGN
    /// sort's unwritten slot (a witness's carrier among them) is a variable every reader of the
    /// parameter shares (`c: C, d: C` at `C = Box` are one `Box`, as the call ties them).
    /// INTERIM (user, 2026-10-01): WI-20261001-80ZV8 makes a bare sort fresh `?` slots in both
    /// places and writes this instance as `Self`.
    ///
    /// On whatever carrier each binding's expansion rides — a rebuilt arrow is an occurrence, a
    /// row around an expanded label a value — and substituted as that
    /// ([`sigma_subst_type_values`]).
    template: Vec<(Symbol, Value)>,
    /// The spec's own parameters: one the provision leaves unbound stays a WILDCARD, as in the
    /// rest of this check (a provision naming no carrier is refused on its own, WI-KXNEX).
    spec_own: SmallVec<[VarId; 4]>,
}

impl<'a> ProvisionMembers<'a> {
    pub(super) fn new(
        spec: Symbol,
        carrier: Symbol,
        sigma: &'a [(Symbol, TermId)],
        witness: Option<Symbol>,
    ) -> Self {
        ProvisionMembers {
            spec,
            carrier,
            sigma,
            witness,
            shared: std::cell::OnceCell::new(),
        }
    }

    fn shared(&self, kb: &mut KnowledgeBase) -> &ProvisionShared {
        self.shared.get_or_init(|| {
            let decl = kb.canonical_sort_sym(self.carrier);
            let witness = self.witness.map(|w| kb.canonical_sort_sym(w));
            let spec_canon = kb.canonical_sort_sym(self.spec);
            let own_decl = own_application(kb, decl);
            let spec_own = own_params_of(kb, spec_canon)
                .iter()
                .map(|&(_, v)| v)
                .collect();
            let template = self
                .sigma
                .iter()
                .map(|&(p, b)| {
                    let b = self_references_at_own_parameters(kb, b, decl);
                    let b = row_parameter_binding_as_row(kb, spec_canon, p, b);
                    let b =
                        expand_foreign_sorts_and_row_labels(kb, &b, Some(decl), SlotVar::Flexible);
                    (p, b)
                })
                .collect();
            ProvisionShared {
                witness,
                own_decl,
                template,
                spec_own,
            }
        })
    }
}

/// The binding of a spec's EFFECT-ROW parameter as the row it denotes ([`row_holding_label`]):
/// `E = Error[Foo]` is the row holding that label, as `E = {Error[Foo]}` writes it. A row
/// parameter's variable stands where a row does — a callback row's tail, `f: … @ {E}` — and
/// bound to the bare label it made `open(tail: Error[T = Foo])`, which no row reader decomposes:
/// the spec's callback row read as nothing and every member was refused (MEASURED: the member
/// restating `@ {Error[Foo]}` behind `provides Sp[E = Error[Foo]]`).
fn row_parameter_binding_as_row(
    kb: &mut KnowledgeBase,
    spec: Symbol,
    p: Symbol,
    b: Value,
) -> Value {
    let short = short_name_of(kb.local_name_of(p)).to_owned();
    if !sort_param_is_effect_row(kb, spec, &short) {
        return b;
    }
    row_holding_label(kb, &b).unwrap_or(b)
}

/// `sort` at its own parameters (bare when it declares none).
fn own_application(kb: &mut KnowledgeBase, sort: Symbol) -> TermId {
    let pairs = sort_type_params_as_pairs(kb, sort);
    let base = kb.make_sort_ref(sort);
    if pairs.is_empty() {
        base
    } else {
        kb.make_parameterized_type(base, &pairs)
    }
}

/// The CARRIER-PARAM RECEIVER of an operation with no self-receiver (WI-424): its first
/// parameter typed by a spec parameter the provision binds to one of `sorts` — with that spec
/// parameter, the binding (σ can bind one key twice, `C = Int64, C = Car`), and the sort it
/// names.
fn carrier_param_receiver_of(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    sigma: &[(Symbol, TermId)],
    sorts: &[Symbol],
) -> Option<(usize, Symbol, TermId, Symbol)> {
    params.iter().enumerate().find_map(|(i, (_, pty))| {
        let v = declared_type_param_vid(kb, pty)?;
        sigma.iter().find_map(|&(p, b)| {
            if type_param_global_var(kb, p) != Some(v) {
                return None;
            }
            sorts
                .iter()
                .copied()
                .find(|&s| composed_self_reference(kb, s, b))
                .map(|s| (i, p, b, s))
        })
    })
}

/// WI-20260929-0RP29 (user decision, 2026-09-30) — WHY a member takes less than its spec,
/// for the refusal to name the repair that fits.
#[derive(Clone, PartialEq, Eq)]
enum Narrower {
    /// The operation's RECEIVER takes fewer carriers than the spec sends it — `written` when
    /// the spec's receiver writes the restriction it is held to (a carrier parameter bound to
    /// `Box[B = Int64]`, a self-receiver `s: Sp[T = Int64]`), so the member's differs from what
    /// the spec writes rather than fixing what it leaves open; `by_spec` when the member types
    /// it by the spec itself, compared as the spec's type at this provision.
    Receiver {
        written: bool,
        by_spec: bool,
        sort: Symbol,
    },
    /// A parameter the spec types by the SPEC ITSELF, other than the receiver: it admits any
    /// provider of the spec, and the member's takes only the carrier.
    AnyProvider,
    /// The member's parameter is THIS instance (§3's parametricity tie) where the spec's need
    /// not be — at any depth. `with` is the parameter that fixed the member's instance first,
    /// where the operation has no receiver to fix it.
    Tied { with: Option<usize> },
    /// Anything else.
    Other,
    /// The provision binds the receiver's parameter to a type writing one of the carrier's own
    /// parameters inside its own slot (`C = Box[B = List[T = B]]`): no instance is that type,
    /// so no call through the spec reaches the member.
    Circular { binding: TermId, sort: Symbol },
    /// A projection does not read here — on the spec's side, the spec's own (`spec: true`).
    Unreadable { spec: bool, why: String },
    /// The member's return type is not a subtype of the spec's. `unwritten`: it leaves a slot
    /// unwritten — a type the member picks, which no caller knows.
    Return { unwritten: bool },
}

/// Where [`member_narrower_than_spec`] found the member narrower, and why.
struct Narrowing {
    /// The parameter, or `None` for the return type.
    at: Option<usize>,
    why: Narrower,
    /// The two types as compared, where they differ from the declarations at this provision's
    /// bindings — a projection read, a receiver typed by the spec, a return — for the refusal
    /// to print what was compared.
    compared: Option<(Value, Value)>,
}

impl Narrowing {
    fn at(i: usize, why: Narrower) -> Self {
        Narrowing {
            at: Some(i),
            why,
            compared: None,
        }
    }
}

/// What [`member_narrower_than_spec`] found.
enum MemberFit {
    /// Every position and the return compared: the member takes what the spec takes and
    /// returns what it promises.
    Fits,
    /// No call written against the spec reaches the member — the spec's receiver, as written,
    /// admits no provider at this provision's bindings, and the call CHECKS its receiver against
    /// that type ([`receiver_type_is_closed`]) — so nothing was compared.
    Unreached,
    /// The first parameter, or the return, where the member is narrower.
    Narrower(Narrowing),
}

impl From<Narrowing> for MemberFit {
    fn from(n: Narrowing) -> Self {
        MemberFit::Narrower(n)
    }
}

/// WI-20260929-0RP29 (user decisions, 2026-09-30 and 2026-10-01) — DOES THE MEMBER TAKE EVERY
/// ARGUMENT LIST THE SPEC OPERATION TAKES, AND RETURN WHAT IT PROMISES? [`MemberFit::Narrower`]
/// names the first parameter (or the return) where it does not.
///
/// A call written against the spec reaches the member at run time, so a member that refuses
/// an argument list the spec admits receives arguments its own signature forbids. The
/// per-position comparison above cannot see the commonest way to be narrower, because it
/// is not in any one parameter: `Car.pick(x: Car, s: Car)` beside `Sp.pick(x: T, s: Sp)`
/// at `Car provides Sp[T = Car]` compares `Car` with `Car` at both positions, yet inside
/// `sort Car` every bare `Car` is THIS instance (§3's parametricity tie), so the member
/// demands `x.V = s.V` where the spec lets them differ.
///
/// THE SPEC'S ARGUMENTS, as a call writes them against it, in a substitution of their own:
///   * THE RECEIVER, per operation and as dispatch reads it — the parameter typed by the spec
///     itself ([`self_receiver_param_index`]), else the first typed by a spec parameter the
///     provision binds to the carrier (the WI-424 carrier-param receiver; a witness's carrier
///     for a witness). An operation with NEITHER is compared all the same: a spec call reaches
///     its member wherever the call fixes the spec's parameters — by its arguments, a call-site
///     bracket (`Mon2.total[U = Int64](xs)`), or an operation-level `requires` dictionary — so
///     it has no instance to receive, and the member's own parameters are bound by the first
///     position that names them.
///   * THE INSTANCE is the carrier at its own parameters, which the provision's references to
///     them denote — the receiver's slots, as the call grounds them (WI-593): `C = Car[V =
///     Int64, W = V]` receives a `Car` whose `W` is its `V`. The carrier-param receiver's binding
///     is MET with it, a foreign sort's unwritten slot in it any type; one that writes a
///     parameter inside its own data slot (`B = List[T = B]`, or around another) admits no
///     instance and is refused, where a row slot's (`EC = {EC, Error[Foo]}`) is a row that
///     holds the label. A self-receiver written with arguments (`s: Sp[T = U]`) meets each —
///     its foreign sorts fresh per occurrence — with the provision's binding of that parameter,
///     the operation's own type parameters bound by it as the call binds them, along the
///     parameter's declared variance where the two are not equal — EQUAL being each a subtype
///     of the other, which unification alone does not say. A binding that does not relate to it
///     so, or only through a type holding itself, is never reached through the spec WHERE THE
///     CALL CHECKS ITS RECEIVER AGAINST THAT TYPE — where it is closed as written, every spec
///     parameter bound and none through a variable ([`receiver_type_is_closed`];
///     [`MemberFit::Unreached`]: nothing of the member is compared). Elsewhere the call admits
///     the receiver and the member is reached: the argument then holds it to nothing, and the
///     comparison goes on. Everything left open is ANY type (a rigid of its own).
///   * THIS INSTANCE — the receiver's — is also every reference to the DECLARING sort a binding
///     leaves bare or part-written, at any depth and whichever parameter it binds (`T = Car`,
///     `T = Car[V = V]`, `T = List[T = Car]`): the provision is written inside the sort, where
///     the name reads as it does in the sort's own operations (§3's tie). One written at other
///     arguments (`C = Car[V = Int64]`) is that type, and an INDEPENDENT instance is written
///     (`T = Car[V = ?]`). INTERIM (user, 2026-10-01): WI-20261001-80ZV8 makes a bare sort
///     fresh `?` slots in a provision as in an operation, and writes this instance `Self`.
///   * A FOREIGN sort's unwritten slot in a binding — a witness's carrier among them — is one
///     variable per spec parameter, read alike wherever the parameter is.
///   * A parameter typed by the spec itself, other than the receiver, is ANY provider of the
///     spec — so a member taking only the carrier there is narrower.
///   * A type parameter the spec operation declares (unless the receiver binds it), an
///     unwritten slot the spec's own text leaves (fresh per occurrence, WI-374), and a written
///     `?` are each ANY type.
///   * A PROJECTION reads as the call reads it, off the type of the argument it projects — as
///     the positions compared so far have bound it ([`resolve_recorded`]): the
///     receiver's `Sort` is that type, a parameter of the carrier's own its slot, and any other
///     member the binding of the provision that LENDS it, at that argument's parameters — over
///     this instance, an independent instance, or any provider (`o: Sp` makes `o.T` any type),
///     on both sides. WHICH provision lends it is the receiver's DECLARATION's to say, as at the
///     call: this one for a receiver the spec types (`s: Sp`, a parameter of the spec's — a
///     witness's binding read through its carrier view at the receiver projected), the sort's
///     own provisions by agreement for one declared at the carrier (`c: Car`), and the call's
///     reading for one another spec declares. One the lender leaves unbound is a wildcard, and
///     one that reduces nowhere (off a field path) the same projection on both sides
///     ([`ProjectionReader`]).
///
/// THE MEMBER'S PARAMETERS keep their own variables, its own parameters among them — bound as a
/// call binds them, by unifying with the spec's arguments, the receiver first — and an
/// unwritten slot of a foreign sort is a fresh variable per occurrence at any depth (WI-374,
/// the call's own expansion); its parameters' names are the spec's (`Modify[p]`).
///
/// THE VERDICT is subtyping: each spec argument must be a subtype of the member's parameter
/// ([`types_compatible`] — a wider member, by width, contravariance or row, fits), and the
/// member's return type a subtype of the spec's — every return, read as the call reads it (the
/// per-position comparison is left the member no call through the spec reaches,
/// [`MemberFit::Unreached`]). One substitution threads the member's variables
/// across the positions, by unification, and a variable it binds two ways is the tie
/// ([`genuine_contradiction_since`]); where unification stops short of a wider member, its
/// variables are bound along the relation's own decomposition ([`bind_member_vars_along`]).
/// UNIFICATION ONLY BINDS; THE RELATION JUDGES. It runs on a probe, a unifier that binds a
/// variable inside itself is dropped before anything walks it ([`binds_a_cycle`]), and its
/// `true` is no verdict — it equates two types across an invariant slot, a reversed arrow or
/// an alias that the relation does not relate — so the relation is asked of what it bound, at
/// every position and at the return. The provision's own open variables (a written `?`, a
/// foreign sort's unwritten slot in a binding) are the same any-type on both sides, since the
/// relation reads a provider's view off the provision.
///
/// AN UNWRITTEN SLOT IN A RETURN belongs to whoever picks it. The member produces the value: its
/// own unwritten slot is a type it chose and the caller does not know, the spec text's the
/// member's to pick; under a returned arrow's PARAMETER the two turn over. A
/// member variable a position compared EARLIER — the receiver, then the positions holding no
/// projection, then each projection position once what it reads is bound — binds to a subtype
/// of a later one's argument is read as the conflict, where a call would join them
/// (WI-20260930-JPSDH records the join the fallback lacks); the other order is admitted, since
/// the later subtype fits.
#[allow(clippy::too_many_arguments)]
fn member_narrower_than_spec(
    kb: &mut KnowledgeBase,
    carrier: Symbol,
    spec: Symbol,
    spec_op: Symbol,
    spec_info: &crate::kb::op_info::OpInfoRecord,
    impl_info: &crate::kb::op_info::OpInfoRecord,
    sigma: &[(Symbol, TermId)],
    provision: &ProvisionMembers,
    impl_to_spec: &HashMap<Symbol, Symbol>,
) -> MemberFit {
    let decl = kb.canonical_sort_sym(carrier);
    let spec_canon = kb.canonical_sort_sym(spec);
    let shared = provision.shared(kb);
    let (witness, own_decl) = (shared.witness, shared.own_decl);
    let mut template = shared.template.clone();
    let spec_own = shared.spec_own.clone();
    // THE RECEIVER: the self-receiver, receiving the declaring sort, else the carrier-param
    // receiver, receiving the sort its binding names — the declaring sort, or a witness's
    // carrier — with that binding, since σ can bind one key twice (`C = Int64, C = Car`).
    let self_recv = self_receiver_param_index(kb, &spec_info.params, spec);
    let carrier_recv = match self_recv {
        Some(_) => None,
        None => {
            let sorts: SmallVec<[Symbol; 2]> = std::iter::once(decl).chain(witness).collect();
            carrier_param_receiver_of(kb, &spec_info.params, sigma, &sorts)
        }
    };
    let recv = self_recv.or(carrier_recv.map(|(i, ..)| i));
    let recv_sort = carrier_recv.map_or(decl, |(.., s)| s);
    let own = if recv_sort == decl {
        own_decl
    } else {
        own_application(kb, recv_sort)
    };
    // THE INSTANCE, in the spec side's own substitution.
    let mut prep = Substitution::new();
    let mut receiver_written = false;
    if let Some((i, p, b, _)) = carrier_recv {
        for (q, v) in template.iter_mut() {
            if *q == p {
                *v = Value::term(own);
            }
        }
        if !is_this_instance(kb, &Value::term(b), recv_sort) {
            receiver_written = true;
            let read = self_references_at_own_parameters(kb, b, decl);
            if !meet_receiver_binding(kb, &mut prep, own, &read, recv_sort) {
                let why = Narrower::Circular {
                    binding: b,
                    sort: recv_sort,
                };
                return Narrowing::at(i, why).into();
            }
        }
    }
    if let Some(i) = self_recv {
        let written = sort_application_parts(kb, &spec_info.params[i].1)
            .map(|(_, w)| w)
            .unwrap_or_default();
        receiver_written = !written.is_empty();
        let spec_params = sort_type_params_as_pairs(kb, spec_canon);
        // A written argument the provision's binding does not meet excludes the provider ONLY
        // WHERE THE CALL CHECKS THE RECEIVER AGAINST THE TYPE, which it does where the type is
        // closed as the spec writes it ([`receiver_type_is_closed`]). Elsewhere the call admits
        // the receiver and the member is reached: the argument then holds it to nothing, and the
        // member is compared against the carrier at any parameters.
        let closed = receiver_type_is_closed(kb, &spec_params, &written);
        for (k, t) in written {
            let Some(q) = spec_params
                .iter()
                .map(|(q, _)| *q)
                .find(|q| same_label(kb, *q, k))
            else {
                continue;
            };
            // A parameter the provision leaves unbound is a wildcard: nothing to meet.
            let Some((_, b)) = template.iter().find(|(p, _)| *p == q) else {
                continue;
            };
            let b = b.clone();
            // The spec's own text: a foreign sort's unwritten slot is fresh PER OCCURRENCE
            // (WI-374), so `s: Sp[K = List, W = List]` writes two lists. Met unexpanded, both
            // bound `List`'s one canonical `T`; a binding of each at another element type then
            // read as a contradiction, the provision as unreachable, and the operation went
            // uncompared (MEASURED: a narrower member loaded and crashed).
            let t = sigma_subst_type_values(kb, &t, &template);
            let t =
                expand_foreign_sorts_and_row_labels(kb, &t, Some(spec_canon), SlotVar::Flexible);
            let mut probe = prep.clone();
            let before = probe.contradiction_details.len();
            // EQUAL, which unification alone does not say: between two types holding no
            // variable it falls back to the subtype relation, so `T = cat` "unified" with a
            // written `Sp[T = Animal]` whatever `T`'s variance — and an INVARIANT parameter's
            // provision was read as reached, its member refused for a receiver no call
            // admits (`Sp.total(c, 1)` is "expected Sp[T = Animal], got Car" — MEASURED). The
            // two are equal where each is a subtype of the other.
            let unified = unify_types(kb, &mut probe, &b, &t)
                && !genuine_contradiction_since(kb, &probe, before);
            // A meet that binds a variable to a type holding itself (`s: Sp[T = List[T = U], W =
            // U]` at `T = V, W = List[T = V]`) admits no receiver — and is not to be resolved
            // through: a deep resolve of such a substitution does not return.
            if unified && binds_a_cycle(kb, &probe) {
                if closed {
                    return MemberFit::Unreached;
                }
                continue;
            }
            let mut reached = unified && {
                let bb = resolve_type_deep_value(kb, &probe, &b);
                let tb = resolve_type_deep_value(kb, &probe, &t);
                views_structurally_equal(kb, &bb, &tb)
                    || types_compatible(kb, &mut probe.clone(), &tb, &bb)
            };
            if !reached {
                // Not equal: reached by the parameter's declared variance, the operation's own
                // variables bound along that relation first as a call binds them (`s: Sp[T =
                // (a: U)]` at `T = (a: Int64, b: Int64)` is `U = Int64`) — the relation binds
                // nothing, and left `U` unbound it read every such provision as unreachable.
                probe = prep.clone();
                let variance = declared_variance(kb, spec_canon, q);
                if matches!(variance, Variance::Covariant | Variance::Contravariant) {
                    bind_member_vars_along(
                        kb,
                        &mut probe,
                        &b,
                        &t,
                        variance == Variance::Contravariant,
                    );
                }
                if binds_a_cycle(kb, &probe) {
                    if closed {
                        return MemberFit::Unreached;
                    }
                    continue;
                }
                let t = resolve_type_deep_value(kb, &probe, &t);
                reached = match variance {
                    Variance::Covariant => types_compatible(kb, &mut probe, &b, &t),
                    Variance::Contravariant => types_compatible(kb, &mut probe, &t, &b),
                    Variance::Bivariant => true,
                    Variance::Invariant => false,
                };
            }
            if !reached {
                if closed {
                    return MemberFit::Unreached;
                }
                continue;
            }
            prep = probe;
        }
    }
    // A spec parameter the provision BINDS is that binding wherever its VARIABLE is read, not
    // only where the spec's text names it: a binding naming another (`T = List[T = Sp.U]` at `U
    // = Int64`) and a callback row's tail (`f: … @ {E}`) reach the parameter as its canonical
    // variable, which σ — a substitution of references — never sees. Left unbound it stayed a
    // WILDCARD, as a parameter the provision leaves unbound does, and a member narrower than
    // the binding was admitted (MEASURED: `put(c: Car, k: List[T = String])` behind `k: s.T`
    // loaded and ran `String.length` on an `Int64`). A key σ binds twice, and a binding holding
    // its own parameter (`T = List[T = Sp.T]`, no finite type), stay as they were.
    for (ps, v) in own_params_of(kb, spec_canon) {
        let mut bound = template.iter().filter(|(q, _)| *q == ps);
        let (Some((_, tb)), None) = (bound.next(), bound.next()) else {
            continue;
        };
        if prep.resolve_as_value(v).is_some() {
            continue;
        }
        let mut probe = prep.clone();
        probe.bind_value(kb, v, tb.clone());
        if !binds_a_cycle(kb, &probe) {
            prep = probe;
        }
    }
    // Every variable left open is ANY type: the instance's slots first, named after its
    // parameters, then the template's and the operation's own type parameters.
    for (ps, v) in own_params_of(kb, recv_sort) {
        if prep.resolve_as_value(v).is_none() {
            let rho = fresh_rigid_named(kb, ps);
            prep.bind_term(kb, v, rho);
        }
    }
    // The bindings' own open variables — a written `?`, a foreign sort's unwritten slot — are
    // read by the MEMBER's side too: the subtype relation reads a provider's view off the
    // provision, the same bindings and the same variables. Left open there, `Car <: Sp[T = s.T]`
    // compared the provision's `Car[V = ?]` with the any-type the rule had made of that very
    // `?`, and a member returning its own carrier behind `-> Sp[T = s.T, E = s.E]` was no
    // subtype of it. (The carrier's own parameters are not among them: the member binds those.)
    //
    // ANY TYPE WHERE A PARAMETER READS IT — the caller passes it, and the call ties every
    // parameter typed by one spec parameter, and the return, to it. A variable NO parameter
    // reads stands in the RETURN only, where nothing the caller passes fixes it: it is left
    // open here, and the return leg below holds the member to leaving it as open
    // ([`leaves_open`]). Made any type there too, `fresh(n: Int64) -> Buf[T = Int64]` behind
    // `-> State` at `State = Buf[T = Int64]` — `N` unwritten in both — compared two unknowns
    // of one name and was refused (MEASURED, once a member's own unwritten return slot stopped
    // unifying with whatever stood across it).
    let param_read: Vec<VarId> = {
        let by_spec_recv = recv.filter(|&i| {
            sort_functor_of_view(kb, &impl_info.params[i].1)
                .is_some_and(|b| kb.canonical_sort_sym(b) == spec_canon)
        });
        // As `prep` reads each: the receiver's meeting may have bound a parameter's variable
        // to the binding's own (`C = Car[V = ?]` met with the instance), and the receiver
        // reads the instance whatever its declared type says.
        let mut read = Vec::new();
        for (i, (_, pty)) in spec_info.params.iter().enumerate() {
            let at = if by_spec_recv == Some(i) {
                spec_at_provision(kb, pty, &template)
            } else if recv == Some(i) {
                Value::term(own)
            } else {
                sigma_subst_type_values(kb, pty, &template)
            };
            let at = resolve_type_deep_value(kb, &prep, &at);
            read.extend(kb.collect_vars(&at));
        }
        read
    };
    // The bindings' OWN open variables only. The declaring sort's parameters are not among
    // them: a provision that binds them receives them, and a WITNESS's — which no receiver
    // fixes (`Car provides Sp[T = Int64, J = V]` receives an `Int64`) — are any type whoever
    // reads them. Left open with the rest, such a `V` was free where the member's own types
    // name it, and `x: Car[V = List[T = V]]` bound it inside itself (MEASURED: the loader's
    // stack overflowed on a member that fits).
    let declaring_own = own_params_of(kb, decl);
    let mut return_only: SmallVec<[VarId; 4]> = SmallVec::new();
    for (_, b) in &template {
        let open = resolve_type_deep_value(kb, &prep, b);
        for v in kb.collect_vars(&open) {
            if !param_read.contains(&v)
                && !spec_own.contains(&v)
                && !declaring_own.iter().any(|&(_, own)| own == v)
                && !return_only.contains(&v)
            {
                return_only.push(v);
            }
        }
    }
    let kept: SmallVec<[VarId; 8]> = spec_own.iter().chain(&return_only).copied().collect();
    let mut provision_any: Vec<(VarId, TermId)> = Vec::new();
    for (_, b) in &template {
        provision_any.extend(rigidify_open(kb, &mut prep, b, &kept));
    }
    let op_vars: SmallVec<[VarId; 2]> = spec_info
        .type_params
        .iter()
        .filter_map(|(_, v)| match v {
            Var::Global(v) => Some(*v),
            _ => None,
        })
        .collect();
    // Whether the receiver bound each, read before the rest are made any type.
    let op_vars_bound: SmallVec<[VarId; 2]> = op_vars
        .iter()
        .copied()
        .filter(|v| prep.resolve_as_value(*v).is_some())
        .collect();
    for (ps, v) in &spec_info.type_params {
        if let Var::Global(v) = v {
            if prep.resolve_as_value(*v).is_none() {
                let rho = fresh_rigid_named(kb, *ps);
                prep.bind_term(kb, *v, rho);
            }
        }
    }
    let instance = resolve_type_deep_value(kb, &prep, &Value::term(own));
    // A spec type as the call reads it: σ once per parameter, the spec text's own unwritten
    // slots fresh per occurrence (WI-374), whatever stays open any type.
    let spec_side = |kb: &mut KnowledgeBase,
                     prep: &mut Substitution,
                     ty: &Value,
                     template: &[(Symbol, Value)]| {
        let s = sigma_subst_type_values(kb, ty, template);
        let s = expand_foreign_sorts_and_row_labels(kb, &s, None, SlotVar::Rigid);
        let _ = rigidify_open(kb, prep, &s, &spec_own);
        resolve_type_deep_value(kb, prep, &s)
    };
    let decl_own: SmallVec<[VarId; 4]> = own_params_of(kb, decl).iter().map(|&(_, v)| v).collect();
    let witness_view = carrier_recv.and_then(|(_, _, b, s)| (s != decl).then_some(b));
    let reader = ProjectionReader::new(kb, recv_sort, spec_canon, sigma, witness_view);
    // The receiver first — a call binds the member's own parameters from it — then the other
    // positions, then a projection position once those it reads are.
    let n = spec_info.params.len();
    let projecting: Vec<bool> = (0..n)
        .map(|i| {
            value_contains_projection(kb, &spec_info.params[i].1)
                || value_contains_projection(kb, &impl_info.params[i].1)
        })
        .collect();
    let mut order: Vec<usize> = recv.filter(|&r| !projecting[r]).into_iter().collect();
    order.extend((0..n).filter(|&i| Some(i) != recv && !projecting[i]));
    order.extend(projection_order(kb, spec_info, impl_info, &projecting));
    let mut spec_args: HashMap<Symbol, Value> = HashMap::new();
    let mut member_args: HashMap<Symbol, Value> = HashMap::new();
    let mut subst = Substitution::new();
    for &(v, rho) in &provision_any {
        subst.bind_term(kb, v, rho);
    }
    let ctx = TypeErrorContext::OperationReturn {
        op_name: spec_op,
        surface: None,
    };
    let any_projection = projecting.iter().any(|&p| p);
    let return_projecting = value_contains_projection(kb, &spec_info.return_type)
        || value_contains_projection(kb, &impl_info.return_type);
    for (k, &i) in order.iter().enumerate() {
        let (spec_p, spec_pty) = &spec_info.params[i];
        let (impl_p, impl_pty) = &impl_info.params[i];
        // One plain type on both sides relates to itself and binds nothing another position
        // reads; deep-expanding it minted a variable per unwritten slot for nothing (MEASURED:
        // 4.4x the check on `Pair[A = List, B = Option]` positions).
        if !any_projection
            && !return_projecting
            && Some(i) != recv
            && views_structurally_equal(kb, spec_pty, impl_pty)
            && plain_type(kb, spec_pty, &[decl, recv_sort])
        {
            continue;
        }
        // A member receiver typed by the SPEC ITSELF takes any provider, never fewer than the
        // spec's receiver — so it is compared as the spec's type at this provision, not as the
        // carrier (the relation does not see a WITNESS's carrier as the spec's provider).
        let by_spec = Some(i) == recv
            && sort_functor_of_view(kb, impl_pty)
                .is_some_and(|b| kb.canonical_sort_sym(b) == spec_canon);
        // WHAT A PROJECTION READS IS EACH ARGUMENT AS BOUND SO FAR. An argument is recorded when
        // its position is compared, and a position compared after it may bind a variable it
        // holds (`x: Car[V = W]`, then `z: W` behind `z: String`). Read as recorded, `y: x.J`
        // projected off an open `W` and stayed the neutral projection — and a member fitting
        // its spec was refused (MEASURED: `op[W](x: Car[V = W], y: x.J, z: W)` behind `y:
        // String, z: String` at `J = V`).
        if projecting[i] {
            resolve_recorded(kb, &subst, &mut spec_args);
            resolve_recorded(kb, &subst, &mut member_args);
        }
        let arg = if projecting[i] {
            let prep_now = prep.clone();
            match reader.eliminate(kb, spec_pty, &spec_args, None, &prep_now, &ctx) {
                Ok(s) => spec_side(kb, &mut prep, &s, &template),
                Err(why) => {
                    return Narrowing::at(i, Narrower::Unreadable { spec: true, why }).into()
                }
            }
        } else if Some(i) == recv && !by_spec {
            instance.clone()
        } else if by_spec {
            let at = spec_at_provision(kb, spec_pty, &template);
            spec_side(kb, &mut prep, &at, &template)
        } else {
            spec_side(kb, &mut prep, spec_pty, &template)
        };
        let member = {
            let prep_now = prep.clone();
            match reader.member_type(
                kb,
                impl_pty,
                &member_args,
                impl_to_spec,
                &prep_now,
                &ctx,
                decl,
                false,
            ) {
                Ok(m) => m,
                Err(why) => {
                    return Narrowing::at(i, Narrower::Unreadable { spec: false, why }).into()
                }
            }
        };
        // UNIFICATION BINDS — the member's variables, a wildcard, a slot left to the other side —
        // and the RELATION judges. On a probe: a unifier binding a variable inside itself solves
        // nothing (its occurs check reads a binding as written: `K ↦ W`, then `W ↦ List[T = K]`),
        // and is dropped before anything walks it — a deep resolve through it does not return
        // (MEASURED: the loader's stack overflowed on such a member instead of refusing it).
        let before = subst.contradiction_details.len();
        let mut probe = subst.clone();
        let unified = unify_types(kb, &mut probe, &arg, &member);
        let mut cyclic = binds_a_cycle(kb, &probe);
        if !cyclic && !unified && !genuine_contradiction_since(kb, &probe, before) {
            bind_member_vars_along(kb, &mut probe, &arg, &member, false);
            cyclic = binds_a_cycle(kb, &probe);
        }
        if !cyclic {
            subst = probe;
        }
        let contradiction = first_genuine_contradiction_since(kb, &subst, before);
        // Resolved first: the relation walks the top of a type, not the variables inside it —
        // BOTH sides, the spec's a wildcard an earlier position bound (left unresolved it read as
        // unrelated, and a member wider by width beside it was refused).
        let member = resolve_type_deep_value(kb, &subst, &member);
        let arg = resolve_type_deep_value(kb, &subst, &arg);
        // A unifier's `true` is no verdict: between two types holding no variable it falls back
        // to the subtype relation in ARGUMENT order at every depth, whatever the position's
        // variance (`Cell[V = cat]` "unifies" with `Cell[V = Animal]`), and across two sorts it
        // compares no binding. So where it unified, the two are EQUAL or the relation holds.
        let fits = !cyclic
            && contradiction.is_none()
            && if unified {
                views_structurally_equal(kb, &arg, &member)
                    || types_compatible(kb, &mut subst.clone(), &arg, &member)
            } else {
                // The relation binds as it decomposes, and what it binds is kept for the
                // positions after this one — unless it bound a variable inside itself, which is
                // no verdict and nothing a later resolve may walk.
                let mut related = subst.clone();
                let holds = types_compatible(kb, &mut related, &arg, &member)
                    && !binds_a_cycle(kb, &related);
                if holds {
                    subst = related;
                }
                holds
            };
        if !fits {
            let why = if Some(i) == recv {
                Narrower::Receiver {
                    written: receiver_written,
                    by_spec,
                    sort: recv_sort,
                }
            } else if sort_functor_of_view(kb, spec_pty)
                .is_some_and(|b| kb.canonical_sort_sym(b) == spec_canon)
            {
                Narrower::AnyProvider
            } else if contradiction.is_some_and(|(v, _, _)| decl_own.contains(&v))
                || (holds_this_instance(kb, impl_pty, decl, &decl_own)
                    && holds_carrier(kb, &arg, decl))
            {
                // What it is tied TO: the receiver, which fixes the member's instance first —
                // or, with no receiver, the first parameter that named it.
                let first = order[..k]
                    .iter()
                    .copied()
                    .find(|&j| holds_this_instance(kb, &impl_info.params[j].1, decl, &decl_own));
                match (recv, first) {
                    (Some(_), _) => Narrower::Tied { with: None },
                    (None, Some(j)) => Narrower::Tied { with: Some(j) },
                    (None, None) => Narrower::Other,
                }
            } else {
                Narrower::Other
            };
            // The declaration at this provision prints the types where nothing the rule read
            // changed them; a projection read, a receiver typed by the spec, and an operation
            // type parameter the receiver bound (`x: U` at `U = String`) print as compared.
            let op_param_bound = kb
                .collect_vars(spec_pty)
                .iter()
                .any(|v| op_vars_bound.contains(v));
            return MemberFit::Narrower(Narrowing {
                at: Some(i),
                why,
                compared: (projecting[i] || by_spec || op_param_bound).then(|| (arg, member)),
            });
        }
        // What a projection over this position reads — recorded only where one does: the
        // member's parameter as THIS instance where its type is (the receiver, a bare
        // carrier), else as it resolved.
        if any_projection || return_projecting {
            let member_arg = if is_this_instance(kb, impl_pty, decl) {
                resolve_type_deep_value(kb, &subst, &Value::term(own_decl))
            } else {
                member
            };
            spec_args.insert(*spec_p, arg);
            member_args.insert(*impl_p, member_arg);
        }
    }
    // THE RETURN: the member's must be a subtype of the spec's, each read as the call reads it at
    // these arguments — the spec's unwritten slots the caller's to fill. EVERY return, not only
    // one holding a projection: the per-position comparison reads the provision's bindings as
    // written, where a bare carrier is any instance and a return naming a type parameter is
    // undecided, so `-> Pair[A = Car[V = Int64], …]` behind `-> Pair[A = T, …]` at `T = Car`, `->
    // Option[T = V]` behind `-> Option[T = T]` at `T = List[T = Int64]` and `-> Option[T = Int64]`
    // behind `get[W](…) -> Option[T = W]` each loaded, and a spec call read the wrong type off
    // the result (MEASURED) — while the same types spelled with a projection were refused. One
    // plain type on both sides is itself.
    let plain_return = !return_projecting
        && views_structurally_equal(kb, &spec_info.return_type, &impl_info.return_type)
        && plain_type(kb, &spec_info.return_type, &[decl, recv_sort]);
    if !plain_return {
        let unreadable = |spec: bool, why: String| Narrowing {
            at: None,
            why: Narrower::Unreadable { spec, why },
            compared: None,
        };
        let prep_now = prep.clone();
        resolve_recorded(kb, &subst, &mut spec_args);
        resolve_recorded(kb, &subst, &mut member_args);
        // WHO PICKS AN UNWRITTEN SLOT. A returned type is produced by the member: its own
        // unwritten slot is a type the member chose and the caller does not know (a rigid), and
        // the spec text's is the member's to pick — a fresh variable to unify with (`want`), and
        // left unwritten for the relation (`want_open`), which binds nothing: a member returning
        // a PROVIDER of a bare `Base` is a subtype of it, where `Carrier <: Base[B = ?B]` is no
        // question the relation answers. Under a returned arrow's PARAMETER the two turn over:
        // the returned function takes every instantiation of what its parameter leaves unwritten,
        // so there the spec's slot is any type and the member's its to instantiate. Read alike on
        // both sides, a member's bare `-> List` behind `-> List[T = T]`, and a `-> (xs: List[T =
        // Int64]) -> Int64` behind `-> (xs: List) -> Int64`, each loaded (MEASURED: a spec call
        // read the wrong element type off the result, at run time).
        let (want, want_open) = match reader.eliminate(
            kb,
            &spec_info.return_type,
            &spec_args,
            None,
            &prep_now,
            &ctx,
        ) {
            Ok(s) => {
                let s = sigma_subst_type_values(kb, &s, &template);
                let open = expand_foreign_sorts_under_params(kb, &s, None, SlotVar::Rigid);
                let s = expand_foreign_sorts_by_polarity(
                    kb,
                    &s,
                    None,
                    SlotVar::Flexible,
                    SlotVar::Rigid,
                );
                (
                    resolve_type_deep_value(kb, &prep, &s),
                    resolve_type_deep_value(kb, &prep, &open),
                )
            }
            Err(why) => return unreadable(true, why).into(),
        };
        // The variables minted between the two marks are the member return's own unwritten
        // slots: the types the member picked and the caller does not know.
        let mark = kb.intern("?mark");
        let slots_from = kb.fresh_var(mark).raw();
        let got = match reader.member_type(
            kb,
            &impl_info.return_type,
            &member_args,
            impl_to_spec,
            &prep_now,
            &ctx,
            decl,
            true,
        ) {
            Ok(m) => resolve_type_deep_value(kb, &subst, &m),
            Err(why) => return unreadable(false, why).into(),
        };
        let slots_to = kb.fresh_var(mark).raw();
        let own_slot = |v: VarId| (slots_from..slots_to).contains(&v.raw());
        // As a parameter is judged: unification BINDS, on a probe a cyclic unifier never leaves;
        // where it stops short the member's variables are bound along the relation, the member
        // the subtype here (`mk[W](…) -> (a: List[T = W], b: Int64)` behind `-> (a: List[T =
        // Int64])` is `W = Int64`); and the verdict is the relation's whatever unification
        // answered — its `true` between two types holding no variable is the subtype relation in
        // argument order at every depth (`-> (x: cat) -> Int64` behind `-> (x: Animal) -> Int64`
        // and `-> Cell[V = cat]` behind `-> Cell[V = Animal]` "unified", and the caller of the
        // spec then read a `cat` where a `dog` was — MEASURED). A variable the return binds a
        // second way is the refusal it is in a parameter.
        let before = subst.contradiction_details.len();
        let mut probe = subst.clone();
        let unified = unify_types(kb, &mut probe, &got, &want);
        let mut cyclic = binds_a_cycle(kb, &probe);
        if !cyclic && !unified && !genuine_contradiction_since(kb, &probe, before) {
            bind_member_vars_along(kb, &mut probe, &want, &got, true);
            cyclic = binds_a_cycle(kb, &probe);
        }
        let fits = !cyclic && !genuine_contradiction_since(kb, &probe, before) && {
            let got = resolve_type_deep_value(kb, &probe, &got);
            let want = resolve_type_deep_value(kb, &probe, &want);
            let want_open = resolve_type_deep_value(kb, &probe, &want_open);
            // A SPEC PARAMETER THE PROVISION LEAVES UNBOUND, and nothing has bound since, is a
            // wildcard: in a spec view it stands for whatever the provider leaves there, which
            // is no binding the relation can compare — a provider that leaves `E` unbound is no
            // `Stream[E = X]` for any written `X`. Left written, a member returning its own
            // carrier behind `-> Stream[T = s.T, E = s.E]` at `provides Stream[T]` was no subtype
            // of it (MEASURED: a fixture that loaded before this ticket; the eighth pass admitted
            // it on unification's word alone).
            let unbound: SmallVec<[Symbol; 4]> = own_params_of(kb, spec_canon)
                .iter()
                .map(|&(q, _)| q)
                .filter(|q| !template.iter().any(|(p, _)| p == q))
                .collect();
            let want_open = unwrite_wildcards(kb, &want_open, spec_canon, &unbound);
            // The substitution the verdict holds under: the relation binds on its own copy.
            let related = |kb: &mut KnowledgeBase, want: &Value| {
                let mut s = probe.clone();
                (types_compatible(kb, &mut s, &got, want) && !binds_a_cycle(kb, &s)).then_some(s)
            };
            let under = if views_structurally_equal(kb, &got, &want) {
                Some(probe.clone())
            } else {
                related(kb, &want).or_else(|| related(kb, &want_open))
            };
            // A SLOT THE PROVISION LEAVES UNWRITTEN AND ONLY THE RETURN READS is no type the
            // member may FIX: nothing the caller passes says it, so the caller of the spec reads
            // it as it likes (`let x: Strm[T = String, …] = Sp.get(k)` at `T = Strm[E =
            // {Error}]`), and a member returning `Strm[T = Int64, …]` there ends that caller in a
            // run-time type error (MEASURED). It may meet only what the member leaves as open:
            // an unwritten slot of its own, or a type parameter of its own.
            under.is_some_and(|s| {
                return_only
                    .iter()
                    .all(|v| leaves_open(kb, &s, *v, &own_slot))
            })
        };
        if !fits {
            let unwritten = holds_rigid(kb, &got, &own_slot);
            return MemberFit::Narrower(Narrowing {
                at: None,
                why: Narrower::Return { unwritten },
                compared: Some((want, got)),
            });
        }
    }
    MemberFit::Fits
}

/// Each recorded argument as `subst` binds it now.
fn resolve_recorded(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    args: &mut HashMap<Symbol, Value>,
) {
    for ty in args.values_mut() {
        *ty = resolve_type_deep_value(kb, subst, ty);
    }
}

/// Does `subst` leave the variable `v` — a slot a provision's binding leaves unwritten — as OPEN
/// as the provision did: unbound, bound to another variable still open, or to a rigid that is
/// the member's own unwritten slot (`own_slot`)?
fn leaves_open(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    v: VarId,
    own_slot: &impl Fn(VarId) -> bool,
) -> bool {
    let var = Value::term(kb.alloc(Term::Var(Var::Global(v))));
    let at = resolve_type_deep_value(kb, subst, &var);
    match at.index_var(kb) {
        Some(Var::Global(_)) => true,
        Some(Var::Rigid(r)) => own_slot(r),
        _ => false,
    }
}

/// `ty` with, in each application of `spec`, the binding of a parameter the provision leaves
/// `unbound` left unwritten where it is still an open variable — the wildcard itself, or a
/// variable of the member's it met (`f: (q: K) -> W` beside the member's `f: (q: X2) -> W`).
fn unwrite_wildcards(
    kb: &mut KnowledgeBase,
    ty: &Value,
    spec: Symbol,
    unbound: &[Symbol],
) -> Value {
    map_type_bottom_up(kb, ty, &mut |kb, node| {
        let TypeExtractor::Parameterized { base, bindings } = extract_type(kb, node) else {
            return None;
        };
        if kb.canonical_sort_sym(base) != spec {
            return None;
        }
        let kept: Vec<(Symbol, Value)> = bindings
            .iter()
            .filter(|(k, v)| {
                !(matches!(v.index_var(kb), Some(Var::Global(_)))
                    && unbound.iter().any(|q| same_label(kb, *q, *k)))
            })
            .cloned()
            .collect();
        if kept.len() == bindings.len() {
            return None;
        }
        let (sp, owner) = site_of(node);
        let base_ref = kb.make_sort_ref(base);
        Some(if kept.is_empty() {
            Value::term(base_ref)
        } else {
            parameterized_value(kb, base_ref, &kept, sp, owner)
        })
    })
    .unwrap_or_else(|| ty.clone())
}

/// Does `v` hold a rigid variable `is` accepts?
fn holds_rigid(kb: &KnowledgeBase, v: &impl TermView, is: &impl Fn(VarId) -> bool) -> bool {
    if let Some(var) = v.index_var(kb) {
        return matches!(var, Var::Rigid(r) if is(r));
    }
    kb.structural_child_views(v)
        .iter()
        .any(|c| holds_rigid(kb, c, is))
}

/// Does a spec call CHECK its receiver against the spec's receiver type as written — every spec
/// parameter written (`written`), and none through a variable: an operation type parameter, a
/// `?`, another parameter's reference? The call validates an argument only against a type it has
/// determined, so over `s: Sp[T = Animal]` with a second parameter `K` left unwritten it admits
/// a provider binding `T = cat` (MEASURED: a member narrowing its receiver, which the rule had
/// stopped comparing as "reached by no call", loaded and was run on a receiver its own signature
/// excludes); the call's own gap is WI-20260929-05ZQE's.
fn receiver_type_is_closed(
    kb: &mut KnowledgeBase,
    spec_params: &[(Symbol, TermId)],
    written: &[(Symbol, Value)],
) -> bool {
    spec_params
        .iter()
        .all(|(q, _)| written.iter().any(|(k, _)| same_label(kb, *q, *k)))
        && written.iter().all(|(_, t)| {
            let mut refs = Vec::new();
            referenced_param_vars(kb, t, &mut refs);
            refs.is_empty() && kb.collect_vars(t).is_empty()
        })
}

/// Each variable `v` leaves open in `prep` a rigid of its own — ANY type — but the spec's own
/// parameters, which stay wildcards. Named after the variable without its `?` (a minted slot
/// is `?T`, and a rigid prints its own). Answers the variables it bound, each with its rigid.
fn rigidify_open(
    kb: &mut KnowledgeBase,
    prep: &mut Substitution,
    v: &Value,
    keep: &[VarId],
) -> Vec<(VarId, TermId)> {
    let r = resolve_type_deep_value(kb, prep, v);
    let mut bound = Vec::new();
    for vid in kb.collect_vars(&r) {
        if !keep.contains(&vid) && prep.resolve_as_value(vid).is_none() {
            let name = kb
                .local_name_of(vid.name())
                .trim_start_matches('?')
                .to_owned();
            let name = kb.intern(if name.is_empty() { "_" } else { &name });
            let rho = fresh_rigid_named(kb, name);
            prep.bind_term(kb, vid, rho);
            bound.push((vid, rho));
        }
    }
    bound
}

/// Does `ty` name nothing [`member_narrower_than_spec`] reads — no type parameter or variable,
/// no projection, no value or place, no instance of the `carriers` (nor an alias, which can
/// name one: `sort MyCar = Car` is THIS instance in a member)? Such a type, the same on both
/// sides, is compatible with itself whatever the provision binds.
fn plain_type(kb: &mut KnowledgeBase, ty: &Value, carriers: &[Symbol]) -> bool {
    let plain_sort = |kb: &KnowledgeBase, s: Symbol| {
        !carriers.contains(&kb.canonical_sort_sym(s))
            && resolve_alias_shape(kb, s).is_none()
            && type_param_global_var(kb, s).is_none()
    };
    match extract_type(kb, ty) {
        TypeExtractor::SortRef(s) => plain_sort(kb, s) && declared_type_param_vid(kb, ty).is_none(),
        TypeExtractor::Parameterized { base, bindings } => {
            plain_sort(kb, base) && bindings.iter().all(|(_, v)| plain_type(kb, v, carriers))
        }
        TypeExtractor::NamedTuple(fields) => {
            fields.iter().all(|(_, v)| plain_type(kb, v, carriers))
        }
        TypeExtractor::Arrow {
            param,
            result,
            effects,
            ..
        } => {
            plain_type(kb, &param, carriers)
                && plain_type(kb, &result, carriers)
                && plain_type(kb, &effects, carriers)
        }
        TypeExtractor::EffectsRows(expr) => {
            match decompose_effect_row_raw(kb, &Substitution::new(), &expr) {
                Some((present, tails, absent)) => {
                    tails.is_empty()
                        && present
                            .iter()
                            .chain(&absent)
                            .all(|l| plain_type(kb, l, carriers))
                }
                None => false,
            }
        }
        TypeExtractor::Nothing => true,
        _ => false,
    }
}

/// `sort`'s own parameters, each with its canonical variable.
pub(super) fn own_params_of(kb: &KnowledgeBase, sort: Symbol) -> SmallVec<[(Symbol, VarId); 4]> {
    sort_type_params_as_pairs(kb, sort)
        .iter()
        .filter_map(|(q, t)| match kb.get_term(*t) {
            Term::Var(Var::Global(v)) => Some((*q, *v)),
            _ => None,
        })
        .collect()
}

/// The carrier at its own parameters (`own`) MET with the carrier-param receiver's binding `b`
/// in `prep` — each of the carrier's parameters `b` names being the receiver's slot, as the
/// call grounds them (WI-593), and a foreign sort's unwritten slot in it any type (`C = Box[B =
/// List]` receives a box of any list: met as written, the bare `List` bound its one canonical
/// `T` to the member's, and a member narrower than the binding was admitted — MEASURED). A row
/// slot naming its own parameter (`EC = {EC, Error[Foo]}`) is a row that holds the rest, `{ρ,
/// Error[Foo]}`, and one that IS another parameter's row (`EC = {EF}`) is that row; a data slot
/// naming its own parameter (`B = List[T = B]`), directly or around another (`V = List[T = W],
/// W = List[T = V]`), admits no instance — `false`.
fn meet_receiver_binding(
    kb: &mut KnowledgeBase,
    prep: &mut Substitution,
    own: TermId,
    b: &Value,
    carrier_canon: Symbol,
) -> bool {
    let b = b.clone();
    let b = match sort_application_parts(kb, &b) {
        Some((base, written)) => {
            let own = own_params_of(kb, carrier_canon);
            let mut changed = false;
            let mut out: Vec<(Symbol, Value)> = Vec::with_capacity(written.len());
            for (k, v) in written {
                let short = short_name_of(kb.local_name_of(k)).to_owned();
                let own_var = own
                    .iter()
                    .find(|(q, _)| short_name_of(kb.local_name_of(*q)) == short)
                    .map(|&(_, vid)| vid);
                let is_row = sort_param_is_effect_row(kb, carrier_canon, &short);
                match own_var {
                    Some(vid) if is_row && kb.collect_vars(&v).contains(&vid) => {
                        let mut rest = Substitution::new();
                        let tail_sym = kb.intern(&short);
                        let tail = kb.fresh_var(tail_sym);
                        let tail_t = kb.alloc(Term::Var(Var::Global(tail)));
                        rest.bind_term(kb, vid, tail_t);
                        out.push((k, resolve_type_deep_value(kb, &rest, &v)));
                        changed = true;
                    }
                    // A row that is exactly ANOTHER parameter's row is that row, not a row
                    // around it: bound as `{EF}`, two such slots (`EC = {EF}, EF = {EC}`) bound
                    // each row inside the other.
                    _ if is_row
                        && braced_row_var(kb, &v)
                            .is_some_and(|w| own.iter().any(|&(_, o)| o == w)) =>
                    {
                        let w = braced_row_var(kb, &v).expect("checked above");
                        out.push((k, Value::term(kb.alloc(Term::Var(Var::Global(w))))));
                        changed = true;
                    }
                    _ => out.push((k, v)),
                }
            }
            if changed {
                let base_ref = kb.make_sort_ref(base);
                parameterized_value(
                    kb,
                    base_ref,
                    &out,
                    crate::kb::node_occurrence::empty_span(),
                    None,
                )
            } else {
                b
            }
        }
        None => b,
    };
    let b = expand_foreign_sorts_and_row_labels(kb, &b, Some(carrier_canon), SlotVar::Flexible);
    let mut probe = prep.clone();
    if unify_types(kb, &mut probe, &Value::term(own), &b) && !binds_a_cycle(kb, &probe) {
        *prep = probe;
        true
    } else {
        false
    }
}

/// Does `subst` bind a variable to a value holding that variable — directly, or through the
/// variables its bindings hold (`V ↦ List[T = W]`, `W ↦ List[T = V]`)? No finite type solves
/// such a substitution, and a deep resolve through it does not return: unification's occurs
/// check reads a binding as written, so the second of two such bindings passes it.
fn binds_a_cycle(kb: &KnowledgeBase, subst: &Substitution) -> bool {
    fn visit(
        kb: &KnowledgeBase,
        subst: &Substitution,
        v: VarId,
        path: &mut Vec<VarId>,
        done: &mut HashSet<VarId>,
    ) -> bool {
        if done.contains(&v) {
            return false;
        }
        if path.contains(&v) {
            return true;
        }
        let Some(bound) = subst.resolve_as_value(v) else {
            done.insert(v);
            return false;
        };
        path.push(v);
        let mut held: Vec<VarId> = kb.collect_vars(bound).into_iter().collect();
        referenced_param_vars(kb, bound, &mut held);
        let cyclic = held.into_iter().any(|w| visit(kb, subst, w, path, done));
        path.pop();
        done.insert(v);
        cyclic
    }
    let mut done = HashSet::new();
    let roots: Vec<VarId> = subst.iter().map(|(v, _)| *v).collect();
    roots
        .into_iter()
        .any(|v| visit(kb, subst, v, &mut Vec::new(), &mut done))
}

/// The variables `view` names by a type parameter's REFERENCE (`List[T = Car.V]`), at any
/// depth: a provision's binding writes the carrier's parameters that way, and a resolve walks
/// each reference to its parameter's variable.
pub(super) fn referenced_param_vars<V: TermView>(
    kb: &KnowledgeBase,
    view: &V,
    out: &mut Vec<VarId>,
) {
    match view.head(kb) {
        ViewHead::Ident(s)
        | ViewHead::Functor {
            functor: Some(s),
            pos_arity: 0,
            named_arity: 0,
        } => out.extend(type_param_global_var(kb, s)),
        ViewHead::Functor { pos_arity, .. } => {
            view_any_child(kb, view, pos_arity, |c| {
                referenced_param_vars(kb, c, out);
                false
            });
        }
        _ => {}
    }
}

/// `b` with every reference to `sort` — the provision's declaring sort — at that sort's OWN
/// parameters wherever the binding leaves a slot unwritten: bare `Car` is `Car[V = V]`, and
/// `Car[W = Int64]` is `Car[V = V, W = Int64]`, at any depth. This is how the sort's own
/// operations read such a reference (§3's tie, written in by WI-1082), and a `provides` clause
/// is written in the same place. A written slot is kept; the result rides the carrier its
/// rebuilt forms take (an arrow holding such a reference is an occurrence).
pub(super) fn self_references_at_own_parameters(
    kb: &mut KnowledgeBase,
    b: TermId,
    sort: Symbol,
) -> Value {
    let own = sort_type_params_as_pairs(kb, sort);
    if own.is_empty() {
        return Value::term(b);
    }
    map_type_bottom_up(kb, &Value::term(b), &mut |kb, node| {
        // Through [`sort_application_parts`]: an ALIAS of the sort (`sort MyCar = Car`) is the
        // sort, as it is in the sort's own operations — read by its own symbol it was an
        // independent instance here and this instance to the call (MEASURED: the verbatim member
        // `o: MyCar` behind `T = MyCar` was refused, two identical signatures printed).
        let (base, written) = sort_application_parts(kb, node)?;
        if kb.canonical_sort_sym(base) != sort || written.len() >= own.len() {
            return None;
        }
        let (sp, owner) = site_of(node);
        let pairs: Vec<(Symbol, Value)> = own
            .iter()
            .map(
                |&(p, own_param)| match written.iter().find(|(k, _)| same_label(kb, p, *k)) {
                    Some((_, v)) => (p, v.clone()),
                    None => (p, Value::term(own_param)),
                },
            )
            .collect();
        let base = kb.make_sort_ref(sort);
        Some(parameterized_value(kb, base, &pairs, sp, owner))
    })
    .unwrap_or_else(|| Value::term(b))
}

/// A binding of `carrier`'s OWN provision, at a receiver of type `recv_ty`, where the binding
/// refers to the carrier with a slot left to its own parameter — bare, part-written, or written
/// at them, at any depth (`T = Car`, `T = Car[W = Int64]`, `T = List[T = Car]`): THIS instance
/// there, as the declaration rule reads it ([`self_references_at_own_parameters`]) — so the
/// binding with the carrier's parameters replaced by the receiver's arguments, which is what a
/// call holds the arguments typed by that spec parameter to. `None` for any other binding (what
/// a call owes those is WI-20260929-05ZQE's), and where the receiver's type leaves a parameter
/// unwritten. ONE reading for the rule and the two call binders: held to a top-level bare or
/// own-parameter binding only, the call passed a second instance to the member the rule had
/// admitted as tied (MEASURED: `T = List[T = Car]`, `T = Car[W = Int64]`, and `B = Car[V = V]`
/// under a receiver whose argument is a type parameter — each loaded and failed at run time).
/// INTERIM (user, 2026-10-01): WI-20261001-80ZV8 makes a bare sort fresh `?` slots in a provision
/// as in an operation, and writes this instance `Self`.
pub(super) fn this_instance_binding_at(
    kb: &mut KnowledgeBase,
    carrier: Symbol,
    binding: TermId,
    recv_ty: &Value,
) -> Option<Value> {
    let carrier = kb.canonical_sort_sym(carrier);
    if !holds_carrier(kb, &Value::term(binding), carrier) {
        return None;
    }
    let read = self_references_at_own_parameters(kb, binding, carrier);
    if is_this_instance(kb, &read, carrier) {
        return Some(recv_ty.clone());
    }
    if !holds_own_instance(kb, &read, carrier) {
        return None;
    }
    binding_at_receiver(kb, carrier, recv_ty, &read)
}

/// Does `ty` hold an application of `carrier` with a slot at the carrier's own parameter, at
/// any depth?
fn holds_own_instance(kb: &mut KnowledgeBase, ty: &Value, carrier: Symbol) -> bool {
    let own = own_params_of(kb, carrier);
    let mut found = false;
    map_type_bottom_up(kb, ty, &mut |kb, node| {
        let Some((base, written)) = sort_application_parts(kb, node) else {
            return None;
        };
        if kb.canonical_sort_sym(base) == carrier {
            found |= written.is_empty()
                || written.iter().any(|(k, v)| {
                    own.iter().any(|&(q, vid)| {
                        same_label(kb, q, *k)
                            && (declared_type_param_vid(kb, v) == Some(vid)
                                || braced_row_var(kb, v) == Some(vid))
                    })
                });
        }
        None
    });
    found
}

/// `b` — written in `sort`'s own parameters — at a receiver of type `recv_ty`: each parameter
/// replaced by the receiver's slot, every one of them written, or `None`. The binding's
/// parameters are renamed apart first: a slot may hold the very parameter it fills (a member's
/// `x: Car[V = List[T = V]]` where no receiver fixes `V`), and bound directly `V ↦ List[T = V]`
/// is a substitution no resolve returns from (MEASURED: the loader's stack overflowed on a
/// member that fits).
pub(super) fn binding_at_receiver(
    kb: &mut KnowledgeBase,
    sort: Symbol,
    recv_ty: &Value,
    b: &Value,
) -> Option<Value> {
    let mut apart = Substitution::new();
    let mut at = Substitution::new();
    for (q, vid) in own_params_of(kb, sort) {
        let short = short_name_of(kb.local_name_of(q)).to_owned();
        let slot = extract_type_param(kb, recv_ty, &short)?;
        let copy = kb.fresh_var(vid.name());
        let copy_t = kb.alloc(Term::Var(Var::Global(copy)));
        apart.bind_term(kb, vid, copy_t);
        at.bind_value(kb, copy, slot);
    }
    let v = resolve_type_deep_value(kb, &apart, b);
    Some(resolve_type_deep_value(kb, &at, &v))
}

/// A projection position's order among the others: once the positions its projections read,
/// on either side, are judged.
fn projection_order(
    kb: &KnowledgeBase,
    spec_info: &crate::kb::op_info::OpInfoRecord,
    impl_info: &crate::kb::op_info::OpInfoRecord,
    projecting: &[bool],
) -> Vec<usize> {
    let reads: Vec<Vec<usize>> = (0..projecting.len())
        .map(|i| {
            let mut receivers = Vec::new();
            collect_projection_receivers(kb, &spec_info.params[i].1, &mut receivers);
            let spec_reads = receivers
                .iter()
                .filter_map(|r| spec_info.params.iter().position(|(p, _)| p == r));
            let mut receivers_m = Vec::new();
            collect_projection_receivers(kb, &impl_info.params[i].1, &mut receivers_m);
            let member_reads = receivers_m
                .iter()
                .filter_map(|r| impl_info.params.iter().position(|(p, _)| p == r));
            spec_reads
                .chain(member_reads)
                .filter(|&j| projecting[j] && j != i)
                .collect()
        })
        .collect();
    let mut done: Vec<usize> = Vec::new();
    let mut pending: Vec<usize> = (0..projecting.len()).filter(|&i| projecting[i]).collect();
    while !pending.is_empty() {
        let Some(at) = pending
            .iter()
            .position(|&i| reads[i].iter().all(|j| done.contains(j)))
        else {
            // A cycle the loader refuses on its own: in declaration order.
            done.extend(pending);
            break;
        };
        done.push(pending.remove(at));
    }
    done
}

/// WI-20260929-0RP29 — the declaration rule's reading of a projection, the call's own
/// ([`eliminate_type_projections_read`]) at the arguments the rule passes: a carrier instance
/// whose slots are rigids stands for every argument they admit, where the call's reading takes
/// a member resting on a rigid for unknown and keeps it neutral. Over a carrier instance:
/// the carrier's own parameter is its slot, any other member the binding — of the provision
/// the receiver's DECLARATION names as its lender ([`ProjectionReader::read`]: this one, the
/// sort's own by agreement, or the call's reading) — AS
/// WRITTEN at the instance's slots — as [`project_type_member`] reads it, so its unwritten
/// slots are fresh where it lands, apart from the parameters typed by it; a member the
/// provision leaves UNBOUND the spec parameter's own variable, the wildcard it is in every other
/// position; `Sort` the call's (the type itself). Over an abstract receiver (a type parameter's
/// rigid), the neutral projection itself, by the spec's names on both sides — a single
/// reference's, or a field path's (`st.provider.K`); one the call's reading leaves neutral off
/// a CONCRETE field (`h.items.T`, `items` a bare `List`) is re-keyed there, at its head.
struct ProjectionReader {
    /// The provision's spec, canonical.
    spec: Symbol,
    recv_sort: Symbol,
    /// The provision's bindings by the spec parameter's short name.
    bindings: SmallVec<[(String, TermId); 4]>,
    /// The spec's own parameters: one the provision leaves unbound reads as its variable, the
    /// wildcard it is in the rest of the check.
    spec_params: SmallVec<[(String, VarId); 4]>,
    /// A WITNESS's carrier view — the binding of the spec's carrier parameter (`C = List[T =
    /// E]`) — through which a receiver's type instantiates the witness's own parameters; `None`
    /// for a provision the receiving sort writes itself.
    witness_view: Option<TermId>,
}

impl ProjectionReader {
    fn new(
        kb: &KnowledgeBase,
        recv_sort: Symbol,
        spec_canon: Symbol,
        sigma: &[(Symbol, TermId)],
        witness_view: Option<TermId>,
    ) -> Self {
        let by_short = |kb: &KnowledgeBase, sort: Symbol| {
            own_params_of(kb, sort)
                .iter()
                .map(|&(q, v)| (short_name_of(kb.local_name_of(q)).to_owned(), v))
                .collect()
        };
        let bindings = sigma
            .iter()
            .map(|&(q, b)| (short_name_of(kb.local_name_of(q)).to_owned(), b))
            .collect();
        ProjectionReader {
            spec: spec_canon,
            recv_sort,
            bindings,
            spec_params: by_short(kb, spec_canon),
            witness_view,
        }
    }

    /// `r.member` over a receiver of type `recv_ty`, or `None` for the call's own reading.
    fn read(
        &self,
        kb: &mut KnowledgeBase,
        receiver: &Value,
        recv_ty: &Value,
        member: Symbol,
        rekey: Option<&HashMap<Symbol, Symbol>>,
        prep: &Substitution,
    ) -> Option<Value> {
        let name = kb.local_name_of(member).to_owned();
        if name == "Sort" {
            return None;
        }
        if matches!(
            type_head(kb, recv_ty),
            TypeHead::Skolem(_) | TypeHead::FlexVar(_)
        ) {
            // The neutral itself, its receiver's head by the spec's name — a single reference
            // or a field path's root (`st.provider.K`, whose abstract `provider` is the rigid
            // the rule made of `State`'s parameter: the call's reading looks for the `requires`
            // bound of a parameter and finds none for a rigid — MEASURED, a verbatim member
            // refused as unreadable).
            let mut segs = receiver_path_segs(kb, receiver)?;
            if let Some(r) = rekey.and_then(|m| m.get(&segs[0]).copied()) {
                segs[0] = r;
            }
            return Some(build_projection_from_segs(
                kb,
                &segs,
                member,
                site_of(receiver).0,
            ));
        }
        let base = sort_functor_of_view(kb, recv_ty)?;
        if kb.canonical_sort_sym(base) != self.recv_sort {
            return None;
        }
        if let Some(slot) = extract_type_param(kb, recv_ty, &name) {
            return Some(slot);
        }
        // WHICH PROVISION LENDS THE MEMBER IS THE RECEIVER'S DECLARATION'S TO SAY, as it is at
        // the call ([`projection_owner_spec`]). Only a receiver declared by THIS spec — `s: Sp`,
        // or a parameter of the spec's — reads this provision. One declared at the carrier
        // (`c: Car`) names no spec: the call, the member's own signature and its body read the
        // member from the specs the sort itself provides, by agreement. Answered from this
        // provision whatever the declaration, a member's `k: c.E` behind `Sp[…]` with `E`
        // unbound was a wildcard while its body took `Other`'s `String`, and a witness's member
        // `-> c.T` over `c: Box` the witness's `Int64` while its body returned `Box`'s own
        // (MEASURED: each loaded, and the spec call's caller failed at run time).
        match projection_owner_spec(kb, receiver, &name).map(|s| kb.canonical_sort_sym(s)) {
            Some(spec) if spec == self.spec => {}
            Some(_) => return None,
            None => return self.read_unowned(kb, recv_ty, &name, prep),
        }
        let Some(&(_, b)) = self.bindings.iter().find(|(s, _)| *s == name) else {
            // A spec parameter the provision leaves UNBOUND is a wildcard here as in every
            // other position: its own variable. Left to the call's reading, `s.K` at `Car
            // provides Sp[T = V]` was "type 'Car' has no member 'K'" and a member the spec call
            // can never reach was refused as unreadable (MEASURED).
            let &(_, v) = self.spec_params.iter().find(|(s, _)| *s == name)?;
            return Some(Value::term(kb.alloc(Term::Var(Var::Global(v)))));
        };
        match self.witness_view {
            // A witness's binding is written in the WITNESS's parameters, which the receiver
            // PROJECTED instantiates through the carrier view, as the call's reading does
            // ([`witnesses_covering`]) — not the operation's receiver: `get2(c: C, d: D) ->
            // d.U` at `ListHolder[E] provides Holder[C = List[T = E], D = List[T = Int64], U =
            // Option[T = E]]` reads `d.U` at `d`'s own element. Read at the receiver's, the
            // rule admitted a member returning `Option[T = E]` where the call read
            // `Option[T = Int64]` (MEASURED, run time).
            Some(view) => {
                let mut at = Substitution::new();
                if !unify_types(kb, &mut at, &Value::term(view), recv_ty) || binds_a_cycle(kb, &at)
                {
                    return None;
                }
                let v = resolve_type_deep_value(kb, &at, &Value::term(b));
                Some(resolve_type_deep_value(kb, prep, &v))
            }
            None => self.at_receiver(kb, recv_ty, b, prep),
        }
    }

    /// A binding the receiving sort's own provision writes — in that sort's parameters — at
    /// THIS receiver's slots ([`binding_at_receiver`]), each of them written, or `None` (the
    /// call's reading).
    fn at_receiver(
        &self,
        kb: &mut KnowledgeBase,
        recv_ty: &Value,
        b: TermId,
        prep: &Substitution,
    ) -> Option<Value> {
        let v = binding_at_receiver(kb, self.recv_sort, recv_ty, &Value::term(b))?;
        Some(resolve_type_deep_value(kb, prep, &v))
    }

    /// `r.member` where the receiver's declaration names no spec: what the receiving sort's
    /// own provisions lend, by AGREEMENT ([`unowned_member_bindings`], the call's selection),
    /// at this receiver's slots — `None` (the call's reading, which says why) where none lends
    /// it or two disagree.
    fn read_unowned(
        &self,
        kb: &mut KnowledgeBase,
        recv_ty: &Value,
        name: &str,
        prep: &Substitution,
    ) -> Option<Value> {
        let mut read: Option<Value> = None;
        for (_, written) in unowned_member_bindings(kb, self.recv_sort, name) {
            let this = self.at_receiver(kb, recv_ty, written, prep)?;
            match &read {
                None => read = Some(this),
                Some(prior) if types_agree(kb, prior, &this) => {}
                Some(_) => return None,
            }
        }
        read
    }

    /// `ty` (a spec side) with its projections read at `args`.
    #[allow(clippy::too_many_arguments)]
    fn eliminate(
        &self,
        kb: &mut KnowledgeBase,
        ty: &Value,
        args: &HashMap<Symbol, Value>,
        rekey: Option<&HashMap<Symbol, Symbol>>,
        prep: &Substitution,
        ctx: &TypeErrorContext,
    ) -> Result<Value, String> {
        let read = |kb: &mut KnowledgeBase, receiver: &Value, recv_ty: &Value, member: Symbol| {
            self.read(kb, receiver, recv_ty, member, rekey, prep)
        };
        eliminate_type_projections_read(kb, ty, args, rekey, &read, ctx).map_err(|e| match e {
            TypeError::Other { actual, .. } => actual,
            other => format!("{other:?}"),
        })
    }

    /// A member type as compared: its projections read at `member_args`, by the spec's names,
    /// and expanded as the call expands it.
    #[allow(clippy::too_many_arguments)]
    fn member_type(
        &self,
        kb: &mut KnowledgeBase,
        ty: &Value,
        member_args: &HashMap<Symbol, Value>,
        impl_to_spec: &HashMap<Symbol, Symbol>,
        prep: &Substitution,
        ctx: &TypeErrorContext,
        decl: Symbol,
        returned: bool,
    ) -> Result<Value, String> {
        let m = if value_contains_projection(kb, ty) {
            self.eliminate(kb, ty, member_args, Some(impl_to_spec), prep, ctx)?
        } else if impl_to_spec.is_empty() {
            ty.clone()
        } else {
            substitute_ref_syms_value(kb, ty, impl_to_spec)
        };
        // A parameter's unwritten slot is the member's to instantiate; a RETURN's is a type the
        // member picked, unknown to the caller — and under a returned arrow's parameter the
        // member's to instantiate again ([`expand_foreign_sorts_by_polarity`]).
        let (slot, under_param) = if returned {
            (SlotVar::Rigid, SlotVar::Flexible)
        } else {
            (SlotVar::Flexible, SlotVar::Flexible)
        };
        Ok(expand_foreign_sorts_by_polarity(
            kb,
            &m,
            Some(decl),
            slot,
            under_param,
        ))
    }
}

/// The spec's receiver type at this provision, as a member typed by the spec receives it:
/// what it writes, and each slot it leaves unwritten bound as the provision binds it (`T = V`
/// is the instance's `V`); [`member_narrower_than_spec`]'s spec side makes the rest any type.
fn spec_at_provision(
    kb: &mut KnowledgeBase,
    spec_pty: &Value,
    template: &[(Symbol, Value)],
) -> Value {
    let Some((base, mut bindings)) = sort_application_parts(kb, spec_pty) else {
        return spec_pty.clone();
    };
    for (p, b) in template {
        if binding_for_param(kb, &bindings, *p, BindingKeyMatch::Label).is_none() {
            let short = kb.local_name_of(*p).to_string();
            let short_sym = kb.intern(&short);
            bindings.push((short_sym, b.clone()));
        }
    }
    let base_ref = kb.make_sort_ref(base);
    parameterized_value(
        kb,
        base_ref,
        &bindings,
        crate::kb::node_occurrence::empty_span(),
        None,
    )
}

/// WI-20260929-0RP29 — the MEMBER's variables bound from the spec's argument along the
/// subtyping relation's own decomposition, where unification stopped short. Unification is an
/// equality and stops at the first difference, so a member wider by tuple width or order (`t:
/// (a: X)` behind `(a: Int64, b: Int64)`) or contravariantly (`f: (a: cat) -> R` behind `(a:
/// Animal) -> Int64`) kept `X` / `R` unbound — and [`types_compatible`] binds nothing, so it
/// refused them. Each member position meets the spec's: a named tuple's field by its alignment
/// ([`align_named_tuple_slots`]), an arrow's parameter and result, a same-sort application's
/// binding by label; an unbound member variable there takes the spec's type. `flipped` is the
/// relation's direction: an arrow's parameter and a `Contravariant` binding turn it, so there
/// the MEMBER's tuple is the one aligned as the subtype (a callback's parameter wider by width
/// is `(t: (a: X, b: Int64, c: Int64))` behind `(t: (a: Int64, b: Int64))`). The verdict stays
/// the relation's — this only supplies the variables it reads, and a binding the relation then
/// refuses is refused.
fn bind_member_vars_along(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    spec: &Value,
    member: &Value,
    flipped: bool,
) {
    let m = walk_view(kb, subst, member);
    if matches!(type_head(kb, &m), TypeHead::FlexVar(_)) {
        unify_types(kb, subst, &m, spec);
        return;
    }
    let s = walk_view(kb, subst, spec);
    match (extract_type(kb, &s), extract_type(kb, &m)) {
        (TypeExtractor::NamedTuple(sf), TypeExtractor::NamedTuple(mf)) => {
            bind_member_fields_along(kb, subst, &sf, &mf, TupleAlign::DATA, flipped);
        }
        (
            TypeExtractor::Arrow {
                param: sp,
                result: sr,
                arity,
                ..
            },
            TypeExtractor::Arrow {
                param: mp,
                result: mr,
                ..
            },
        ) => {
            // A parameter LIST aligns by position (WI-782); a sole parameter is its type.
            match (extract_type(kb, &sp), extract_type(kb, &mp)) {
                (TypeExtractor::NamedTuple(sf), TypeExtractor::NamedTuple(mf))
                    if arity != 1 && both_named_tuples(kb, &sp, &mp) =>
                {
                    bind_member_fields_along(kb, subst, &sf, &mf, TupleAlign::PARAM_LIST, !flipped);
                }
                _ => bind_member_vars_along(kb, subst, &sp, &mp, !flipped),
            }
            bind_member_vars_along(kb, subst, &sr, &mr, flipped);
        }
        (
            TypeExtractor::Parameterized {
                base: sb,
                bindings: sbind,
            },
            TypeExtractor::Parameterized {
                base: mb,
                bindings: mbind,
            },
        ) if kb.canonical_sort_sym(sb) == kb.canonical_sort_sym(mb) => {
            let base = kb.canonical_sort_sym(sb);
            for (k, mv) in &mbind {
                let flip = match declared_variance(kb, base, *k) {
                    Variance::Covariant | Variance::Invariant => flipped,
                    Variance::Contravariant => !flipped,
                    Variance::Bivariant => continue,
                };
                if let Some(sv) = binding_for_param(kb, &sbind, *k, BindingKeyMatch::Label).cloned()
                {
                    bind_member_vars_along(kb, subst, &sv, mv, flip);
                }
            }
        }
        _ => {}
    }
}

/// [`bind_member_vars_along`] over two field lists, each member field against the spec's it
/// aligns with — the spec's list aligned as the subtype, the member's where `flipped`.
fn bind_member_fields_along(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    spec_fields: &[(Symbol, Value)],
    member_fields: &[(Symbol, Value)],
    mode: TupleAlign,
    flipped: bool,
) {
    let pairs: Vec<(Value, Value)> = if flipped {
        let Some(slots) = align_named_tuple_slots(kb, member_fields, spec_fields, mode) else {
            return;
        };
        aligned_pairs(&slots, member_fields, spec_fields)
            .map(|(m, s)| (s.clone(), m.clone()))
            .collect()
    } else {
        let Some(slots) = align_named_tuple_slots(kb, spec_fields, member_fields, mode) else {
            return;
        };
        aligned_pairs(&slots, spec_fields, member_fields)
            .map(|(s, m)| (s.clone(), m.clone()))
            .collect()
    };
    for (s, m) in pairs {
        bind_member_vars_along(kb, subst, &s, &m, flipped);
    }
}

/// Is `ty` the carrier at its OWN parameters — bare, or each written slot its own parameter (a
/// row slot's own row variable braced, `{EC}`, included) — which inside the carrier is THIS
/// instance (§3's parametricity tie)? Slot by slot: `P2[A = B, B = A]` and `P2[A = A, B = A]`
/// are not.
pub(super) fn is_this_instance(kb: &mut KnowledgeBase, ty: &Value, carrier_canon: Symbol) -> bool {
    let Some((base, written)) = sort_application_parts(kb, ty) else {
        return false;
    };
    if kb.canonical_sort_sym(base) != carrier_canon {
        return false;
    }
    let own = own_params_of(kb, base);
    written.iter().all(|(k, v)| {
        let Some(&(_, vid)) = own.iter().find(|(q, _)| same_label(kb, *q, *k)) else {
            return false;
        };
        declared_type_param_vid(kb, v) == Some(vid) || braced_row_var(kb, v) == Some(vid)
    })
}

/// Does `ty` hold THIS instance at any depth — the carrier bare or at its own parameters, or
/// one of its own parameters (`own`)?
fn holds_this_instance(
    kb: &mut KnowledgeBase,
    ty: &Value,
    carrier_canon: Symbol,
    own: &[VarId],
) -> bool {
    if kb.collect_vars(ty).iter().any(|v| own.contains(v)) {
        return true;
    }
    let mut found = false;
    map_type_bottom_up(kb, ty, &mut |kb, node| {
        found |= is_this_instance(kb, node, carrier_canon);
        None
    });
    found
}

/// Does `ty` hold an instance of the carrier at any depth — by its own name, or an alias of it
/// (`sort MyCar = Car`)?
pub(super) fn holds_carrier(kb: &mut KnowledgeBase, ty: &Value, carrier_canon: Symbol) -> bool {
    let mut found = false;
    map_type_bottom_up(kb, ty, &mut |kb, node| {
        found |= sort_application_parts(kb, node)
            .is_some_and(|(s, _)| kb.canonical_sort_sym(s) == carrier_canon);
        None
    });
    found
}

/// The row variable a row is exactly (`{EC}`), or `None`.
fn braced_row_var(kb: &mut KnowledgeBase, v: &Value) -> Option<VarId> {
    effects_rows_inner(kb, v)?;
    let (present, tails, absent) = decompose_effect_row_raw(kb, &Substitution::new(), v)?;
    match (&present[..], &tails[..], &absent[..]) {
        ([], [t], []) => match kb.get_term(*t) {
            Term::Var(Var::Global(vid)) => Some(*vid),
            _ => None,
        },
        _ => None,
    }
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

/// A type as the member rule's refusals print it: an arrow with its effect row (`… @ {EP}`),
/// which the plain rendering leaves out and a callback's difference can lie in.
fn member_type_display(kb: &KnowledgeBase, v: &Value) -> String {
    let plain = type_display_name_value(kb, v);
    match extract_type(kb, v) {
        TypeExtractor::Arrow { effects, .. } => {
            let row = type_display_name_value(kb, &effects);
            if row == "{}" {
                plain
            } else {
                format!("{plain} @ {row}")
            }
        }
        _ => plain,
    }
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
        /// A witness's carrier — the sort its operations receive on.
        witness: Option<Symbol>,
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
                witness: witness_dispatch_carrier(kb, row.spec_base, row.provider, row.spec_view),
            }
        })
        .collect();

    let mut errors = Vec::new();
    for p in &provs {
        let (Some(spec_ops), Some(carrier_ops)) = (own.get(&p.spec), own.get(&p.carrier)) else {
            continue;
        };
        // WI-20260929-0RP29 — what the member rule reads of this provision, built on the
        // first member it compares ([`ProvisionMembers`]).
        let provision = ProvisionMembers::new(p.spec, p.carrier, &p.sigma, p.witness);
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
                &provision,
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
        let mut tails: Vec<TermId> = Vec::new();
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
            //
            // WI-20260929-0RP29 — A ROW PARAMETER WRITTEN BARE IS A TAIL, not a label: `effects
            // {Q, -Q}` over the operation's own `Q` holds the row it lacks whole (user decision,
            // 2026-10-01). Its reference heads as a sort's, so it was filed among the present
            // labels, where the denied VARIABLE equals no label — and the declaration loaded
            // while `{Error[Foo], -Error[Foo]}` was refused (MEASURED).
            let row_shaped = effect_value_is_row_shaped(kb, e);
            if row_shaped {
                if let Some((p, t, a)) = decompose_effect_row_raw(kb, &subst, e) {
                    present.extend(p);
                    tails.extend(t);
                    absent.extend(a);
                }
            } else if let Some(vid) = declared_type_param_vid(kb, e) {
                tails.push(kb.alloc(Term::Var(Var::Global(vid))));
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
        let Some(clash) = uninhabitable_row_clash(kb, &subst, &present, &tails, &absent, &effects)
        else {
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
            let Some((owner, spec_view)) = sort_clause_fields(kb, rid, spec_field) else {
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

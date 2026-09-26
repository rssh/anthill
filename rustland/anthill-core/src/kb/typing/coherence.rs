//! Load-time provider checks: requires entailment, eq/neq exclusivity, provider
//! operations, coherence groups and binding agreement.

use super::*;

/// WI-429: end-of-load formation validation for STORED `RigidTypeProjection`
/// terms. The typer validates a projection where it ELIMINATES one (op
/// signatures, call sites, let annotations — `resolve_rigid_projection`), but
/// a projection stored in a position the typer never eliminates (an entity
/// FIELD type, a fact / constraint / rule type slot) previously loaded
/// SILENTLY — a typo'd member (`MemStore.Kye`) or a bare-spec subject
/// (`Storage.Key` outside the sort) sat in the KB as a malformed type. The
/// loader records every formation (`kb.rigid_projection_formations`, with
/// source spans); this sweep re-runs the eliminator's own
/// `resolve_rigid_projection` on each — requires/provides info is complete by
/// this point in the load pipeline — and surfaces any rejection as a
/// load-blocking error. Valid outcomes (`Grounded` / `Neutral`) pass; the
/// sweep validates formation only and stores nothing, so a projection in an
/// eliminated position is at worst validated twice with the same verdict.
pub fn validate_rigid_projection_formations(
    kb: &mut KnowledgeBase,
) -> Vec<crate::kb::load::LoadError> {
    let formations = std::mem::take(&mut kb.rigid_projection_formations);
    let mut errors = Vec::new();
    let mut seen: HashSet<TermId> = HashSet::new();
    for (tid, source_span) in formations {
        // One hash-consed projection can be formed at many sites; one verdict
        // suffices (the first formation's span reports it).
        if !seen.insert(tid) {
            continue;
        }
        let TypeExtractor::RigidTypeProjection {
            sort,
            subject,
            member,
        } = extract_type(kb, &TermIdView(tid))
        else {
            unreachable!(
                "rigid_projection_formations holds a non-RigidTypeProjection term \
                 — loader recording bug"
            );
        };
        let ctx = TypeErrorContext::EntityField {
            entity: sort,
            field: member,
        };
        let span = Some(Span::new(source_span.start(), source_span.end()));
        if let Err(te) = resolve_rigid_projection(kb, sort, &subject, member, &ctx, span) {
            errors.push(te.to_load_error(kb));
        }
    }
    errors
}

/// WI-20260925-P5G39 (058 §3.10) — the ASSUMPTIONS a provision of the carrier is checked
/// under: `roots` — the carrier's sort-level `requires` and one clause's conditions — and
/// everything their specs' `requires` chains make of them.
///
/// `provides Spec[C] :- G…` claims `Spec` only where `G…` holds, and a sort-level
/// `requires` conditions EVERY provision of the carrier (its dictionaries all carry it),
/// so each is what a generic body's `requires` already is: `Candidate::Assumption`.
///
/// GROUND ONES TOO, deliberately. A second /code-review pass read `sort Cell requires
/// Lo[T = Cell]` beside `provides Hi[T = Cell]` (with `Hi requires Lo[T = T]`) as
/// CIRCULAR and had ground entries refused rather than assumed; MEASURED, that refused
/// `provides Hi[T = Cell] :- Lo[T = Cell]` — a provision whose requirement IS its written
/// condition — and every sort with an unprovided ground `requires`, through its derived
/// `Eq`, which the old check loaded. It is not unsound either way: such a provision is
/// claimed only where `Lo[Cell]` holds, i.e. VACUOUSLY, and a USE of it is refused at the
/// call site because nothing supplies `Lo[Cell]` (pinned by
/// `a_ground_requirement_is_assumed_and_its_use_is_refused`).
///
/// Each root is composed into the carrier's own terms through its own bindings —
/// `build_requires_tree` seeded from the entry, as `op_scoped_defer_location` builds an
/// operation's half.
///
/// CLOSED, because an assumption answers a goal only by COVER — the resolver's FromScope
/// lookup — and a condition implies more than it says: `Ord[A]` implies `WeakOrd[A]` (a
/// conversion), hence `Eq[A]`, `PartialOrd[A]` and `PartialEq[A]`. The resolver's own
/// through-a-slot step (`scope_chain_cover`) walks the same tree to answer a sub-goal, but
/// it runs only once no entry covers and only under σ at depth; spelling the closure out
/// here makes every implied entry a direct cover. The PAIRING survives
/// the composition: `Big[X = P, Y = Q] requires Small[X = X, Y = Y]` yields `Small[X = P,
/// Y = Q]` and not `Small[X = Q, Y = P]` (`a_permuted_inner_condition_is_not_entailed`).
fn closed_under_requires(kb: &mut KnowledgeBase, roots: Vec<RequiresEntry>) -> Vec<RequiresEntry> {
    // The roots FIRST, as a prefix: for the sort level that is the carrier's direct
    // chain in order — the frame an operation body of the carrier sees, which is what a
    // named slot's position (`NamedRequirementSlot::slot`) indexes.
    let mut closed = roots.clone();
    for root in &roots {
        let child_subst = build_child_subst_map(kb, root);
        let mut visited: Vec<Symbol> = Vec::new();
        let tree = build_requires_tree(kb, root.required_sort, &child_subst, &mut visited);
        closed.extend(flatten_requires_tree(&tree));
    }
    closed
}

/// WI-20260925-P5G39 — the carrier as its provision check reads it: at its OWN type
/// parameters, each RIGID, with what its sort-level `requires` lets every clause assume.
/// Built once per CARRIER: a carrier makes many provisions, and each mint is fresh
/// variables and terms.
///
/// A provision is checked for every instantiation of its carrier at once, so the
/// carrier's parameters are universally quantified — skolems, which unify with nothing
/// but themselves. With no σ the resolver matched a goal element head-only and read a
/// bare parameter as a wildcard: `Eq[T = Pair.A]` unified the open `A` with
/// `SortedSet`'s head `Eq[T = SortedSet[T, O]]`, "chose" `SortedSet`, and failed inside
/// it. Under σ a rigid element matches only a VARIABLE head (a generic witness,
/// `provides Mon[T = E]`) or an assumption, and a scope entry covers a goal only on
/// σ-class agreement ([`requires_entry_covers_goal`]'s σ mode).
struct CarrierAtOwnParams {
    /// Each parameter's canonical variable bridged to a fresh rigid ([`rigid_bridge`]), as
    /// an operation body of the carrier holds them. The bridge is what makes a written
    /// `Pair.A` RIGID rather than merely present: without it the element classifies as an
    /// unbound global, which the impl-param matcher accepts WITHOUT RECORDING (WI-507's
    /// sibling wildcard), so a generic witness's own conditions were instantiated at its
    /// raw parameter.
    param_rigids: Vec<(VarId, TermId)>,
    /// `C[P = C.P, …]` — the carrier APPLIED to its own parameters, which is what a bare
    /// `C` in the provision's own head denotes (`provides Eq[Pair]` is about `Pair[A = A,
    /// B = B]`). Spelled out because the resolver reads a bare `C` as saying NOTHING about
    /// the parameters: the provision match then records none of them, and a NAMED slot
    /// (`requires O: WeakOrd[T]`) — a parameter too (§4.7) — reads as a head that forgot
    /// `O = O`, which is refused (MEASURED: an entity sort declaring a named slot failed
    /// its derived `Eq`). The self-application is threaded by the match's self-provides
    /// arm, as a call's `Tagged[T = String, O = ByLength]` is. `None` for a carrier with
    /// no parameter, where a bare `C` is the whole type.
    ///
    /// WHY HERE AND NOT IN THE RESOLVER: what a bare parametric carrier denotes depends on
    /// where it is written. In a signature it leaves the parameters universally quantified
    /// — a named slot there is ERASED (WI-1094) and refusing it is right — while in the
    /// carrier's own provision it is the carrier at its own parameters. Only the check
    /// knows which reading it is asking.
    ///
    /// The named slot's sub-goal is then answered by the ASSUMPTION covering it — the
    /// sort-level `O: WeakOrd[T]`, through the scope lookup — and not bound to a frame
    /// position: the binder reaches `carried_slot` as the parameter's canonical variable,
    /// not as the rigid, so it reads as unspoken and the scope answers. That is the whole
    /// of what a load verdict asks (is the slot satisfiable here), and nothing is emitted
    /// from this tree. The assumptions' prefix IS the body's frame (the direct chain, in
    /// order), so a change that routes this binder through `own_named_frame_slot` — which
    /// indexes the frame by the slot's position — would find the slot where it looks;
    /// `a_named_slot_on_a_parametric_carrier…` is the row that would say otherwise.
    applied: Option<TermId>,
    /// The carrier's sort-level `requires`, closed ([`closed_under_requires`]) — every
    /// clause's assumptions start here, since a sort-level `requires` conditions every
    /// clause.
    sort_level: Vec<RequiresEntry>,
}

impl CarrierAtOwnParams {
    /// `Err(param)`: the carrier declares `param` with no published canonical variable
    /// (WI-954's divergence — a dotted `sort Inner.T = ?` written in a sort registers `T`
    /// on the sort while defining it elsewhere). Asked BEFORE reading the parameters,
    /// whose reader asserts on exactly that and would otherwise turn a program the load
    /// has already refused (proposal 059 R3 refuses the spelling in a secondary entry)
    /// into a crash; the caller reports it instead.
    fn of(kb: &mut KnowledgeBase, carrier: Symbol) -> Result<Self, Symbol> {
        if let Some(&unpublished) = kb
            .type_param_syms_of(carrier)
            .iter()
            .find(|p| kb.canonical_type_param_var(**p).is_none())
        {
            return Err(unpublished);
        }
        let pairs = sort_type_params_as_pairs(kb, carrier);
        let params = param_pairs_as_vars(kb, &pairs);
        let rigidify = rigidify_op_type_params(kb, &params);
        let param_rigids = rigid_bridge(&rigidify, &params);
        // Keyed by the DECLARED parameter symbol, as the loader's own self-application
        // (`domain_self_type`) keys it; the value is the parameter's reference, which
        // renders by name in a refusal where its canonical variable would print `?`.
        let applied = (!params.is_empty()).then(|| {
            let bindings: Vec<(Symbol, TermId)> = params
                .iter()
                .map(|(param, _)| (*param, kb.make_sort_ref(*param)))
                .collect();
            let base = kb.make_sort_ref(carrier);
            kb.make_parameterized_type(base, &bindings)
        });
        // The memoized tree's subtrees are already composed into the carrier's terms, so
        // they are read, not rebuilt: the direct entries first (the frame prefix, see
        // [`closed_under_requires`]), their closure after.
        let tree = requires_tree(kb, carrier);
        let mut sort_level: Vec<RequiresEntry> = tree.iter().map(|n| n.entry.clone()).collect();
        for node in tree.iter() {
            sort_level.extend(flatten_requires_tree(&node.sub_requires));
        }
        Ok(CarrierAtOwnParams {
            param_rigids,
            applied,
            sort_level,
        })
    }
}

/// [`CarrierAtOwnParams::applied`] for every BARE reference to the carrier in `goal`'s
/// bindings, at any depth (`List[T = Pair]` is a list of `Pair`s at `Pair`'s own
/// parameters too).
///
/// A `SortView` wrapper is kept WHOLE: its `pos_args[0]` is the view's BASE, not a type
/// argument, and rewriting it would leave a wrapper `unwrap_spec_view` no longer reads.
fn goal_at_own_params(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    carrier: Symbol,
    applied: TermId,
) -> SortGoal {
    let carrier_canon = kb.canonical_sort_sym(carrier);
    let bindings = goal
        .bindings
        .iter()
        .map(|(k, v)| {
            let v = rewrite_term_leaves(kb, *v, &|kb, t| {
                if let Term::Fn { functor, .. } = kb.get_term(t) {
                    if is_sort_view_functor(kb, *functor) {
                        return Some(t);
                    }
                }
                extract_sort_ref_sym(kb, &TermIdView(t))
                    .is_some_and(|s| kb.canonical_sort_sym(s) == carrier_canon)
                    .then_some(applied)
            });
            (*k, v)
        })
        .collect();
    SortGoal {
        spec_sort: goal.spec_sort,
        bindings,
        carrier: goal.carrier.clone(),
    }
}

/// WI-20260925-P5G39 — one clause of a provision, and what it lets the check assume.
struct ClauseScope {
    /// The clause's `:- goals`, as written (empty for the unconditioned clause).
    conditions: Vec<Value>,
    /// The carrier's sort-level assumptions, then this clause's conditions, closed
    /// ([`closed_under_requires`]).
    assumptions: Vec<RequiresEntry>,
}

/// WI-20260925-P5G39 — one provision's resolution context: the carrier at its own
/// parameters, and its clauses — each an ALTERNATIVE (066 §7), so the required goal must
/// hold under EVERY one, because each is a way for the provision to hold.
struct ProvisionScope {
    own: Rc<CarrierAtOwnParams>,
    clauses: Vec<ClauseScope>,
}

impl ProvisionScope {
    /// `Err` names the carrier and spec of a condition with no readable spec head. The
    /// loader refuses that at a `provides … :-` clause and asserts no fact, but a
    /// `ProvidesConditionInfo` fact can also be WRITTEN, and its decoder checks only the
    /// `provided` head (found by /code-review: a written one panicked the load).
    fn of(
        kb: &mut KnowledgeBase,
        own: Rc<CarrierAtOwnParams>,
        carrier: Symbol,
        spec: Symbol,
    ) -> Result<Self, crate::kb::load::LoadError> {
        // Keyed exactly as the resolver keys a provision's clauses at a dispatch
        // (`alternative_condition_goals`, `provider_dict_chain`): by carrier and provided
        // spec.
        let mut written: Vec<Vec<Value>> = provision_conditions(kb, carrier)
            .into_iter()
            .filter(|g| same_sort_canonical(kb, g.provided, spec))
            .map(|g| g.conditions)
            .collect();
        // A clause with no condition makes the provision hold OUTRIGHT, beside any
        // conditioned one — the dispatch reads it so — so it is checked assuming nothing
        // beyond the sort level. Without it, `provides Big[T = Box]` written beside
        // `provides Big[T = Box] :- Cond[B]` was checked only under `Cond[B]`, and adding
        // the conditioned clause turned a refusal into a load.
        if written.is_empty() || kb.provides_unconditioned_clause(carrier, spec) {
            written.push(Vec::new());
        }
        let mut clauses = Vec::with_capacity(written.len());
        for conditions in written {
            let mut roots: Vec<RequiresEntry> = Vec::with_capacity(conditions.len());
            for condition in &conditions {
                let Some(required_sort) = spec_base_functor(kb, condition) else {
                    return Err(crate::kb::load::LoadError::Other {
                        message: format!(
                            "a condition of `{} provides {}` has no readable spec head, so \
                             the provision's contract cannot be checked under it",
                            kb.qualified_name_of(carrier),
                            kb.qualified_name_of(spec),
                        ),
                    });
                };
                let entry = RequiresEntry {
                    required_sort,
                    spec: condition.clone(),
                    // A `provides … :- goals` tail is an INBOUND obligation on whoever
                    // wants the provision, not a conversion the spec supplies.
                    supply: SupplySource::Required,
                };
                roots.push(entry);
            }
            let mut assumptions = own.sort_level.clone();
            assumptions.extend(closed_under_requires(kb, roots));
            clauses.push(ClauseScope {
                conditions,
                assumptions,
            });
        }
        Ok(ProvisionScope { own, clauses })
    }
}

/// WI-20260925-P5G39 — [`CarrierAtOwnParams`] for `carrier`, built once; `None` when it
/// cannot be built, which is REPORTED the first time and only then, naming the carrier's
/// declaration.
fn carrier_at_own_params(
    kb: &mut KnowledgeBase,
    cache: &mut HashMap<Symbol, Option<Rc<CarrierAtOwnParams>>>,
    errors: &mut Vec<crate::kb::load::LoadError>,
    carrier: Symbol,
) -> Option<Rc<CarrierAtOwnParams>> {
    let key = kb.canonical_sort_sym(carrier);
    if let Some(hit) = cache.get(&key) {
        return hit.clone();
    }
    let built = match CarrierAtOwnParams::of(kb, carrier) {
        Ok(own) => Some(Rc::new(own)),
        Err(param) => {
            errors.push(crate::kb::load::LoadError::Other {
                message: format!(
                    "`{}` declares `{}` as a type parameter, but no variable was published \
                     for it, so the contracts of its provisions cannot be checked at its own \
                     parameters (WI-954)",
                    kb.qualified_name_of(carrier),
                    kb.qualified_name_of(param),
                ),
            });
            None
        }
    };
    cache.insert(key, built.clone());
    built
}

/// The clause a refusal is about, when the provision has more than one to choose from.
fn clause_of(kb: &KnowledgeBase, clause: &ClauseScope) -> crate::kb::load::ProvisionClause {
    use crate::kb::load::ProvisionClause;
    if clause.conditions.is_empty() {
        return ProvisionClause::Unconditioned;
    }
    let rendered: Vec<String> = clause
        .conditions
        .iter()
        .map(|c| match spec_base_functor(kb, c) {
            Some(required_sort) => render_requires_entry(
                kb,
                &RequiresEntry {
                    required_sort,
                    spec: c.clone(),
                    supply: SupplySource::Required,
                },
            ),
            // Unreachable here: `ProvisionScope::of` refused such a clause.
            None => format_precondition_clause(kb, c),
        })
        .collect();
    ProvisionClause::Conditioned(rendered.join(", "))
}

/// WI-343/WI-356 — provider-side requires coverage. For every provision
/// `X provides Spec[σ]`, each spec-level `requires` of `Spec`, **instantiated at the
/// provision's bindings σ**, must itself hold. An unsatisfied requirement means the
/// provision is unsound: `X` is declared to provide `Spec`, yet `Spec`'s contract (its
/// `requires`) does not hold at `X`'s bindings.
///
/// Binding-precise and transitive where the representation allows it (WI-356).
/// `provider_requires_subgoals` substitutes σ into each `requires R[…]` clause (σ keyed
/// by short *name* — see there). Each goal is then RESOLVED — through the canonical
/// resolver, binding-precise (a provider satisfying `R` at the *wrong* bindings fails)
/// AND transitive (the resolver recurses into `R`'s own `requires`). `Ord[T=Int] requires
/// Eq[T]` is checked as `Eq[T=Int]`. The carrier's parameters are its OWN, and
/// WI-20260925-P5G39 resolves under exactly what the provision may assume about them —
/// its clause's conditions and the sort-level chain, closed ([`closed_under_requires`]) —
/// with the parameters rigid ([`CarrierAtOwnParams`]). For EVERY clause of the provision
/// the goal must resolve, because each clause is a way for the provision to hold.
///
/// WITNESS-LOCALLY (058 §3.8, [`resolve_within_provider`]): the goal is a slot of the
/// carrier's OWN dictionary, and a dictionary resolves a sub-goal its provider itself
/// provides to that provider's provision. Two coexisting bundles (`ByFst`, `BySnd`, each
/// `provides WeakOrd[Duet[A, B]]` beside `provides Ord[Duet[A, B]]`) otherwise TIE on the
/// `WeakOrd` goal of each one's `Ord`.
///
/// WI-20260925-4ZZKZ — FOR EVERY GOAL, the ones σ leaves abstract included. Those used to
/// fall back to v0's base-level existence check ("some sort named in the provision
/// provides `R`", at ANY bindings), justified by two stdlib realities — the shorthand
/// `requires Ring[F]` dropping `F`→`Ring.T`, and `FiniteCollection requires Iterable[C =
/// C]` at `List` holding only through `Stream`. MEASURED under P5G39's route: neither
/// survives (the bare stdlib's precise and loose verdicts agree on every such goal). What
/// the fallback still admitted was unsound: `WTop provides Top[T = Wrap[E = E]]` with no
/// `Base[T = Wrap[E]]` anywhere loaded because `Wrap` provides `Base` at `Int64`, and the
/// absence then reached every dictionary built for it as a spec-half slot recorded absent.
///
/// A resolution that fails in the PROVIDER half of the carrier's own provision of the
/// required spec ([`unentailed_condition`]) is WI-1033's `ProvisionConditionsTooWeak`: the
/// carrier DOES provide it, only under a written condition this clause does not entail,
/// which the refusal names. Any other failure is `UnsatisfiedProviderRequires`, whose
/// [`requirement_failure_of`] says which kind — no provider, a tie, a cycle, a provider
/// that refuses the goal, or a goal beneath the chosen provider (a requirement reaching
/// the carrier nested, `Small[Seq[Box]]`, fails at `Box`'s condition beneath `Seq`). A
/// provision with several clauses names the one the requirement fails under.
///
/// The `EffectsRuntime` kind-anchor (synthesized from `effects E = ?`) is
/// skipped: it is satisfied structurally by the effect-row machinery, never
/// by a carrier `fact`.
pub fn check_provider_requires(kb: &mut KnowledgeBase) -> Vec<crate::kb::load::LoadError> {
    use crate::kb::load::LoadError;
    let effects_runtime = effects_runtime_sym(kb);

    // Snapshot each provision before the requires walk, which mutates `kb`
    // (`provider_requires_subgoals` allocates substituted terms).
    struct Provision {
        carrier: Symbol,
        spec: Symbol,
        /// σ — the spec's type-param **short name** → the provision's
        /// binding value (`"F" → Float`). Keyed by short name, not symbol:
        /// the stdlib shorthand `requires Eq[T]` stores the requires-binding
        /// value as the *required* spec's own param (`Eq.T`), linked to the
        /// enclosing param only by the shared short name, so a symbol-keyed
        /// σ would never reach it.
        sigma: SmallVec<[(String, TermId); 2]>,
        /// WI-1110 — the row this provision was decoded from, kept so a refusal can ask
        /// [`KnowledgeBase::derived_provision_origin_of`] whether the author wrote it.
        /// The relocation this ticket performs routes obligations through DERIVED rows —
        /// `Half` writes `provides Ord[T = Half]` and is refused about `WeakOrd` — so
        /// without it every such message names a clause that is not in the source. WI-1109
        /// added the provenance channel for exactly this wording one check over
        /// (`check_provider_operations`); this is its second reader.
        rid: crate::kb::RuleId,
    }
    let mut provisions: Vec<Provision> = Vec::new();
    for row in provides_rows(kb) {
        let spec_base = row.spec_base;
        let spec_qn = kb.qualified_name_of(spec_base).to_string();
        let mut sigma: SmallVec<[(String, TermId); 2]> = SmallVec::new();
        // The view's RAW arguments, not `row.bindings`: σ takes its positionals too.
        if let Term::Fn {
            functor,
            pos_args,
            named_args,
        } = kb.get_term(row.spec_view).clone()
        {
            // Named bindings (`F = Float`, `C = List[T]`).
            for (k, v) in &named_args {
                if is_type_param_binding(kb, *k, &spec_qn) {
                    sigma.push((kb.local_name_of(*k).to_string(), *v));
                }
            }
            // Positional bindings (`VectorSpace[Vec3, Float]`): `unwrap_spec_view`
            // keeps only named args, so the view's positionals are paired here, by the
            // language's rule — `KnowledgeBase::positional_param_slots`: the next param no
            // named binding took. A `SortView` wrapper carries the spec base in
            // `pos_args[0]`; a bare parameterized term does not.
            //
            // WI-20260923-N3W68 (#9) — this was the THIRD copy of that fill, and the one
            // that TRUNCATED: a `zip` against the free params dropped a positional past them
            // without a word, where its siblings refuse (`goal_from_op_requires_entry`) or
            // keep the entry as written (`normalize_op_requires_entry`). A positional with
            // no slot is now one of two things, neither of them a binding: the WI-407
            // CARRIER slot of a spec with no parameters (`NonMonotonicStore[FileStore]` —
            // the only shape a census found reaching here), or an over-application the
            // loader REFUSES where it is written (`sort_inst_to_value`, the op-contract
            // gate in `convert_term`). The `SortView` test was also the dotless
            // `ends_with("SortView")`; it is [`is_sort_view_functor`] now.
            let skip = if is_sort_view_functor(kb, functor) { 1 } else { 0 };
            if pos_args.len() > skip {
                let declared = kb.type_params_of_sort(spec_base);
                let slots = KnowledgeBase::positional_param_slots(
                    &declared,
                    |d| sigma.iter().any(|(n, _)| n == d),
                    pos_args.len() - skip,
                );
                for (val, slot) in pos_args.iter().skip(skip).zip(slots) {
                    // No slot: the carrier slot of a parameterless spec, or an over-application
                    // the loader has ALREADY REPORTED for this very load — the refused
                    // provision is still in the relation when this pass runs, so the two
                    // cannot be told apart here, and neither is a binding.
                    if let Some(i) = slot {
                        sigma.push((declared[i].clone(), *val));
                    }
                }
            }
        }
        provisions.push(Provision {
            carrier: row.provider,
            spec: spec_base,
            sigma,
            rid: row.rid,
        });
    }

    let mut errors = Vec::new();
    // WI-20260925-P5G39 — per carrier, see [`carrier_at_own_params`].
    let mut own_params: HashMap<Symbol, Option<Rc<CarrierAtOwnParams>>> = HashMap::new();
    for p in &provisions {
        // WI-1110 — A CONVERSION OWES NOTHING HERE, and the obligation is not waived but
        // RELOCATED. `Ord provides WeakOrd[T = T]` is a spec's `provides`: it says an
        // `Ord[T]` dictionary yields a `WeakOrd[T]` one, and asking whether `Ord`
        // provides `WeakOrd`'s own `requires Eq[T]` is the wrong question — `Ord` is a
        // spec, it provides nothing and never will. The obligation belongs to whatever
        // CARRIER eventually provides `Ord`, and it gets there through the chain: the
        // conversion is a chain entry of `Ord` ([`self_supplied_entries`]), so
        // `Int64 provides Ord` is checked for `WeakOrd[Int64]`, which the DERIVED row
        // `Int64 provides WeakOrd` answers — and that row is itself a provision this
        // same loop then checks for `Eq[Int64]` and `PartialOrd[Int64]`.
        //
        // THIS REPLACES WI-1109's `forwarded_to_requires`, which relocated the same
        // obligation to the forwarder's own `requires` — and so needed `Ord` to restate
        // `requires Eq[T]` / `requires PartialOrd[T]` for a floor it does not itself
        // constrain. DRIVEN: deleting those two clauses with the old escape in place
        // fails the stdlib load with two `UnsatisfiedProviderRequires`; with this skip
        // they are no longer needed and the carrier is still asked. BOTH relocated
        // obligations are driven, and they need two fixtures rather than one:
        // `an_ord_carrier_still_owes_eq` measures `PartialOrd` (its carrier is a TOTAL
        // composite, so `eq_derive` has already paid its `Eq` — the test's own doc says
        // so and forbids repairing it to `Eq`), and `a_parametric_ord_carrier_owes_eq`
        // measures `Eq` on a PARAMETRIC composite, which `eq_derive` does not classify.
        if is_conversion_edge_named(kb, p.carrier, p.spec, &p.sigma) {
            continue;
        }
        // WI-20260925-P5G39 — what this provision may assume, built on its FIRST goal: most
        // provisions have none (a spec with no `requires`), and building it mints the
        // carrier's rigids and composes a chain per condition. `Some(None)`: it could not be
        // built, and why has been reported where that was found — each goal then goes
        // unresolved.
        let mut scope_of_provision: Option<Option<ProvisionScope>> = None;
        for goal in provider_requires_subgoals(kb, p.spec, &p.sigma, &[]) {
            let required = goal.spec_sort;
            if Some(required) == effects_runtime {
                continue;
            }
            // WI-1110: `derived_from` is `Some(origin)` when the row is one this load
            // DERIVED, so the message can stop attributing a `provides` clause to an
            // author who wrote a different one.
            let derived_from = |kb: &KnowledgeBase| {
                kb.derived_provision_origin_of(p.rid)
                    .map(|o| kb.qualified_name_of(o).to_string())
            };
            if scope_of_provision.is_none() {
                let built = carrier_at_own_params(kb, &mut own_params, &mut errors, p.carrier)
                    .and_then(|own| match ProvisionScope::of(kb, own, p.carrier, p.spec) {
                        Ok(ps) => Some(ps),
                        Err(refusal) => {
                            errors.push(refusal);
                            None
                        }
                    });
                scope_of_provision = Some(built);
            }
            let Some(Some(ps)) = &scope_of_provision else {
                continue;
            };
            let goal = match ps.own.applied {
                Some(applied) => goal_at_own_params(kb, &goal, p.carrier, applied),
                None => goal,
            };
            // No call site, so nothing to chase: the whole σ context is the rigid bridge.
            let no_call = Substitution::new();
            let sigma = SigmaCtx {
                subst: &no_call,
                param_rigids: &ps.own.param_rigids,
            };
            let several = ps.clauses.len() > 1;
            for clause in &ps.clauses {
                let scope = ResolutionScope {
                    available_requires: &clause.assumptions,
                    sigma: Some(&sigma),
                    // A DECLARATION is being validated: no call site, so no selection.
                    selected: &[],
                    // The assumptions are CLOSED ([`closed_under_requires`]): the
                    // resolver's through-a-slot step, which still runs over them for a
                    // sub-goal no entry covers, cannot find what they lack.
                    sub_goal_requires: &[],
                };
                let (failure, top) = match resolve_within_provider(kb, &goal, &scope, p.carrier) {
                    (ResolutionResult::Resolved(_), _) => continue,
                    failed => failed,
                };
                let unentailed = unentailed_condition(kb, &failure, top.as_ref(), p.carrier);
                let clause = several.then(|| clause_of(kb, clause));
                errors.push(match unentailed {
                    Some(unentailed) => LoadError::ProvisionConditionsTooWeak {
                        carrier: kb.qualified_name_of(p.carrier).to_string(),
                        spec: kb.qualified_name_of(p.spec).to_string(),
                        required: kb.qualified_name_of(required).to_string(),
                        unentailed,
                        derived_from: derived_from(kb),
                        clause,
                    },
                    None => LoadError::UnsatisfiedProviderRequires {
                        carrier: kb.qualified_name_of(p.carrier).to_string(),
                        spec: kb.qualified_name_of(p.spec).to_string(),
                        required: kb.qualified_name_of(required).to_string(),
                        derived_from: derived_from(kb),
                        clause,
                        failure: requirement_failure_of(kb, &failure, top.as_ref(), &goal, p.carrier, p.spec),
                    },
                });
                // One report per requirement: a second clause failing the same goal
                // repeats the same repair.
                break;
            }
        }
    }
    errors
}

/// WI-1033 — the condition a `ProvisionConditionsTooWeak` names, when the failure is one:
/// the resolver CHOSE the carrier's own provision of the required spec, and a goal of its
/// PROVIDER half — the provision's own conditions, which this clause does not entail —
/// found nothing. Named as the resolver instantiated it, not as the innermost goal it
/// forwarded: for `provides Lo[T = Cell] :- Lawful[T = Seq[E = A]]` that innermost goal
/// is `Lawful[T = Cell.A]`, two levels below anything the author wrote. A provision decided
/// among ALTERNATIVE clauses lays no condition out as a slot; there the resolver's own
/// account (the innermost goal) is the one there is.
///
/// READ OFF THE RESOLUTION THAT FAILED ([`TopFailure`]). WI-20260925-P5G39 re-derived it —
/// collected and ranked the candidates again and re-resolved the provider half with a
/// plain `resolve` — and /code-review found both halves of that able to disagree with the
/// resolution that actually ran: no locality, no slot pins, no named-slot rung, and no
/// SPEC half, whose failure (the carrier's OTHER provision breaking its own contract) then
/// fell through and was blamed on this provision's conditions.
fn unentailed_condition(
    kb: &KnowledgeBase,
    failure: &ResolutionResult,
    top: Option<&TopFailure>,
    carrier: Symbol,
) -> Option<String> {
    let top = top.filter(|t| same_sort_canonical(kb, t.provider, carrier))?;
    match (failure, &top.at) {
        (
            ResolutionResult::NoMatch { .. },
            FailedAt::Slot {
                goal,
                provider_half: true,
            },
        ) => Some(format_goal(kb, goal)),
        (ResolutionResult::NoMatch { goal_text, .. }, FailedAt::Alternatives) => {
            Some(goal_text.clone())
        }
        _ => None,
    }
}

/// The parameters of `spec` that `goal`'s bindings still name anywhere — what a provision
/// that omitted them leaves open (the loader writes an omitted binding as the spec's own
/// parameter), qualified.
fn spec_params_named_in(kb: &KnowledgeBase, goal: &SortGoal, spec: Symbol) -> Vec<String> {
    fn walk(kb: &KnowledgeBase, t: TermId, own: &[String], out: &mut Vec<String>) {
        match kb.get_term(t) {
            Term::Ref(s) | Term::Ident(s) => {
                let qn = kb.qualified_name_of(*s);
                if own.iter().any(|p| p == qn) && !out.iter().any(|o| o == qn) {
                    out.push(qn.to_string());
                }
            }
            Term::Fn {
                functor,
                pos_args,
                named_args,
            } => {
                if pos_args.is_empty() && named_args.is_empty() {
                    let qn = kb.qualified_name_of(*functor);
                    if own.iter().any(|p| p == qn) && !out.iter().any(|o| o == qn) {
                        out.push(qn.to_string());
                    }
                }
                for a in pos_args.iter() {
                    walk(kb, *a, own, out);
                }
                for (_, a) in named_args.iter() {
                    walk(kb, *a, own, out);
                }
            }
            _ => {}
        }
    }
    let own: Vec<String> = kb
        .type_param_syms_of(spec)
        .iter()
        .map(|p| kb.qualified_name_of(*p).to_string())
        .collect();
    let mut out = Vec::new();
    for (_, v) in &goal.bindings {
        walk(kb, *v, &own, &mut out);
    }
    out
}

/// Is `goal` about `carrier` — does one of its bindings name the carrier (bare or
/// applied)? Then a provision ON the carrier is the repair a missing provider asks for.
fn goal_is_about(kb: &KnowledgeBase, goal: &SortGoal, carrier: Symbol) -> bool {
    goal.bindings.iter().any(|(_, v)| {
        unwrap_spec_view(kb, *v)
            .map(|(base, _)| base)
            .or_else(|| extract_sort_ref_sym(kb, &TermIdView(*v)))
            .is_some_and(|s| same_sort_canonical(kb, s, carrier))
    })
}

/// WI-20260925-4ZZKZ — the resolver's failure as the refusal reports it, classified by
/// WHERE it happened ([`TopFailure`]). No provider chosen: the goal's own `NoMatch` is the
/// plain absence, its own tie names the candidates. A provider chosen: it refused the goal
/// itself (a named slot its carrier's type leaves unanswerable — the hint says which), or a
/// goal beneath it failed, named as that goal. A cycle is a cycle wherever it closes.
fn requirement_failure_of(
    kb: &KnowledgeBase,
    failure: &ResolutionResult,
    top: Option<&TopFailure>,
    goal: &SortGoal,
    carrier: Symbol,
    spec: Symbol,
) -> crate::kb::load::RequirementFailure {
    use crate::kb::load::RequirementFailure;
    // An omission first: whatever else failed, a goal the provision left open cannot be
    // answered by adding a provider, and every other wording would say it could.
    let unwritten = spec_params_named_in(kb, goal, spec);
    if !unwritten.is_empty() {
        return RequirementFailure::Unwritten {
            goal: format_goal(kb, goal),
            params: unwritten,
        };
    }
    match (failure, top) {
        (ResolutionResult::Cyclic { path, .. }, _) => {
            RequirementFailure::Cyclic { path: path.clone() }
        }
        (
            ResolutionResult::NoMatch { hint, .. },
            Some(TopFailure {
                provider,
                at: FailedAt::Refused,
            }),
        ) => RequirementFailure::Refused {
            provider: kb.qualified_name_of(*provider).to_string(),
            hint: hint.clone(),
        },
        (
            ResolutionResult::NoMatch { goal_text, .. }
            | ResolutionResult::Ambiguous { goal_text, .. },
            Some(TopFailure { provider, .. }),
        ) => RequirementFailure::Below {
            provider: kb.qualified_name_of(*provider).to_string(),
            goal: goal_text.clone(),
            detail: describe_resolution_failure(kb, failure),
        },
        (ResolutionResult::NoMatch { .. }, None) => RequirementFailure::NoProvider {
            goal: format_goal(kb, goal),
            about_carrier: goal_is_about(kb, goal, carrier),
        },
        (ResolutionResult::Ambiguous { goal_text, tie, .. }, None) => {
            RequirementFailure::Ambiguous {
                goal: goal_text.clone(),
                candidates: tie_candidate_names(kb, tie),
            }
        }
        (ResolutionResult::Resolved(_), _) => {
            unreachable!("requirement_failure_of is asked only of a failed resolution")
        }
    }
}

/// WI-658: `Eq` ⊥ `NonEq` — a carrier must not provide BOTH the lawful
/// (reflexive) `Eq` and the witnessed non-reflexive `NonEq`. Walk the
/// `SortProvidesInfo` facts, group by canonical carrier, and flag any carrier
/// seen providing both. OPT-IN by construction: a carrier providing neither, or
/// only one, is untouched — the check does nothing without a `NonEq` (or `Eq`)
/// declaration to contradict. The error list is sorted by carrier name so the
/// diagnostic order is deterministic.
///
/// WI-658 / WI-664 — grouping is by the carrier's canonical BASE sort symbol,
/// which for the CONCRETE carriers in play (`Float`; the WI-664 composites `Point`
/// / … derived from `SortProvidesInfo` facts whose `sort_ref` is a nullary carrier
/// name) IS the full carrier — so a user `provides Eq[Point]` and the derived
/// `NonEq[Point]` group together and the conflict fires.
///
/// WI-20260919-9KYPA — A CONDITIONAL PAIR IS NOT A CONTRADICTION, and that is now
/// reachable rather than hypothetical. `eq_derive` derives BOTH halves for a parametric
/// carrier — `Eq[List] :- Eq[T]` and `NonEq[List] :- NonEq[T]` — and they do not
/// contradict: they hold at DIFFERENT arguments (`List[T = Int64]` lawful,
/// `List[T = Float]` partial), which is the whole point of deriving them. Grouping by
/// base symbol alone would read that pair as `List` claiming both, and refuse every
/// parametric carrier in the stdlib. So the conflict now needs an UNCONDITIONAL claim on
/// at least one side: an unconditional `Eq` asserts lawfulness at every argument, which
/// any `NonEq` contradicts, and symmetrically. Both-conditional is admitted.
///
/// That is the exact shape the older LIMITATION note here predicted and it is worth
/// saying how this differs from the remedy it prescribed ("key on the SPEC's
/// carrier-binding value, NOT `sort_ref`"). No row is per-INSTANTIATION even now: a
/// derived conditional row still spells the bare base in `sort_ref` and puts the
/// argument dependence in its `:- NonEq[T]` conditions, so the binding-aware key would
/// have nothing to separate. Reading the CONDITIONS is what separates them.
///
/// Its resolution is deliberately coarse — "does this spec have any condition clause at
/// this carrier", not "are the two sides' conditions complementary". For the derived
/// pairs they always are, by construction (one is the mirror of the other). A carrier
/// mixing an unconditional clause with a conditional one for the SAME spec would read as
/// conditional and escape; nothing writes that today, and refusing it needs the clause-
/// level accounting `provides_clause_count` would have to be made exact for first.
pub fn check_eq_noneq_exclusive(kb: &mut KnowledgeBase) -> Vec<crate::kb::load::LoadError> {
    use crate::kb::load::LoadError;
    let (Some(eq_sym), Some(noneq_sym)) = (
        kb.try_resolve_symbol("anthill.prelude.Eq"),
        kb.try_resolve_symbol("anthill.prelude.NonEq"),
    ) else {
        // No NonEq spec loaded ⇒ nothing can conflict.
        return Vec::new();
    };
    let eq_canon = kb.canonical_sort_sym(eq_sym);
    let noneq_canon = kb.canonical_sort_sym(noneq_sym);

    // canonical carrier symbol → (provides Eq, provides NonEq)
    let mut seen: std::collections::HashMap<Symbol, (bool, bool)> =
        std::collections::HashMap::new();
    for row in provides_rows(kb) {
        let spec_canon = kb.canonical_sort_sym(row.spec_base);
        let entry = seen
            .entry(kb.canonical_sort_sym(row.provider))
            .or_insert((false, false));
        if spec_canon == eq_canon {
            entry.0 = true;
        } else if spec_canon == noneq_canon {
            entry.1 = true;
        }
    }

    // WI-20260919-9KYPA — both sides present is no longer the whole test; at least one
    // must be UNCONDITIONAL. Asked only of the carriers that hold both, so the
    // `provision_conditions` scan (a per-functor fact walk) costs nothing on the
    // overwhelming majority that hold one or neither.
    let both: Vec<Symbol> = seen
        .into_iter()
        .filter(|(_, (has_eq, has_noneq))| *has_eq && *has_noneq)
        .map(|(carrier, _)| carrier)
        .collect();
    let mut conflicts: Vec<String> = both
        .into_iter()
        .filter(|&carrier| {
            !provision_is_conditional(kb, carrier, eq_canon)
                || !provision_is_conditional(kb, carrier, noneq_canon)
        })
        .map(|carrier| kb.qualified_name_of(carrier).to_string())
        .collect();
    conflicts.sort();
    conflicts.dedup();
    conflicts
        .into_iter()
        .map(|carrier| LoadError::IncompatibleEqNonEq { carrier })
        .collect()
}

/// WI-20260919-9KYPA — is the written type `ty` a PROVABLY unlawful (`NonEq`) carrier?
/// Resolved as the goal `NonEq[T = ty]` through the canonical instance resolver, the same
/// one `spec_resolves_at_bindings` runs for a field's declared spec — so an unconditional
/// provision (`Float`, a `Partial` composite) and a conditional one (`NonEq[List] :-
/// NonEq[T]`, derived by `eq_derive::derive_conditional_noneq`) are answered by one
/// question, and the conditional one descends into `ty`'s own argument.
///
/// NEGATIVE, like its caller: a `false` here is "not provably unlawful", not "lawful".
/// A named-tuple key (`Map[K = (a: Float)]`) has no sort to carry a provision at all, so
/// it answers `false` and stays the structural-reading gap WI-644's enumeration leaves
/// open (`check_use_site_requires_eq`'s non-scope item 2, and §8.3).
fn noneq_holds_at(kb: &mut KnowledgeBase, noneq_sym: Symbol, ty: TermId) -> bool {
    // The spec's own carrier parameter (`NonEq[T = …]`) — read off the declaration rather
    // than spelled, the same way `eq_derive::spec_view` builds the views these rows are
    // recorded under. The two must agree or the goal matches no provision.
    let param = {
        let name = kb
            .type_params_of_sort(noneq_sym)
            .into_iter()
            .next()
            .unwrap_or_else(|| "T".to_string());
        kb.intern(&name)
    };
    spec_resolves_at_bindings(kb, noneq_sym, smallvec::smallvec![(param, ty)])
}

/// WI-644 / WI-835 — USE-SITE `requires Eq` enforcement. A parametric sort with a
/// `requires Eq[param]` clause (`Map requires Eq[T = K]`, `Set requires Eq[T]`),
/// instantiated with `param` bound to a CONCRETE carrier that provides `NonEq`
/// (IEEE `Float`, or a Float-containing composite via WI-664), is a load error: a
/// raw `Float` key is not lawful (`nan != nan`), so `Map[K = Float]` is rejected
/// rather than silently misdeciding; `Map[K = TotalFloat]` / `Map[K = Int64]` load.
///
/// NEGATIVE by design — fire ONLY on a provably-`NonEq` binding. A positive "the
/// binding must provide `Eq`" check would be (a) VACUOUS: `spec_resolves_at_
/// bindings` treats structural eq as a universal `Eq` instance (WI-616), which is
/// exactly why `Map[K = Float]` loaded clean before WI-644; and (b) OVER-REJECTING:
/// WI-664 derives `NonEq` facts for partial composites but NOT `Eq` facts for lawful
/// all-`Eq` composites, so `sort_provides(Point, Eq)` is false for a perfectly
/// lawful key — and an abstract type-param binding provides nothing either.
/// Checking `NonEq` avoids both: only a carrier that GENUINELY lacks lawful Eq
/// (the proposal-004 §Motivation carriers) is rejected.
///
/// SCOPE (WI-835) — EVERY written parameterized type instantiation, wherever the
/// type is written. The sites are recorded at the type LOWERINGS (see
/// [`crate::kb::ParameterizedSite`]) rather than gathered from a list of storage
/// positions here, so a new type position cannot silently escape by being added
/// elsewhere. MEASURED covered, each by its own probe and pinned by its own test:
/// an entity field; an operation PARAMETER and RETURN type; a `const`'s type; a
/// `sort S = …` alias; a body `let` annotation; a typed lambda binder; a binding
/// value inside a `requires` / `provides` clause; the positional spelling
/// `Map[Float, Int64]`; a DENOTED-bearing instantiation's non-denoted siblings
/// (`Map[K = Float, V = Buf[T = Int64, N = 3]]`); and any of those NESTED inside a
/// tuple, an arrow parameter, or another instantiation (`Map[K = Set[T = Float]]`
/// refuses on the INNER `Set`, at the inner base name's own span).
///
/// WI-644 shipped this scoped to ENTITY FIELDS only, which left the ticket's own
/// acceptance program (`operation m() -> Map[K = Float, V = Int64]`) loading clean;
/// that mismatch between "the data-STORAGE position" and "the positions a Float key
/// is actually written in" is what WI-835 closes. Enumerating positions is what
/// produced the mismatch, so the scope now rides on the producers instead — plural:
/// `type_expr_to_value`'s doc calls itself "the SOLE type lowering" and it is not,
/// which is how a spec clause's `Map[K = Float]` escaped a first cut of this.
///
/// Complements the op-USE dispatch discharge (WI-300 Tier B), which already rejects
/// CALLING an `Eq`-op over a Float-collection (`eq(a: Set[Float], …)`). Runs after
/// `eq_derive::run`, so a Float-composite's derived `NonEq` is visible — which is
/// also why the check is DEFERRED to here rather than run at the lowering.
///
/// Deliberate non-scope (documented, not silently dropped):
///
/// (1) DIRECT `requires Eq` only — a container whose Eq requirement is TRANSITIVE
/// (`sort S requires Ord[T]`, and `Ord requires Eq`) is not chased; the
/// stdlib key containers (`Map`/`Set`/`Lattice`/`Ord`) all `requires Eq`
/// directly.
///
/// (2) A NAMED TUPLE key whose unlawfulness is in its ARGUMENT — `Map[K = (a: Float)]`
/// loads. A tuple functor has no SORT to carry a provision, so neither the derived
/// conditional `NonEq` nor the goal that reads it reaches it; closing it needs a
/// STRUCTURAL reading, not another provision row. It is a genuinely unlawful key (a tuple
/// of `nan` is not equal to itself), so this is a real gap. Carried over from WI-644's
/// non-scope list — a rewrite of this comment dropped it once, which is how a known gap
/// becomes an unknown one.
///
/// WI-20260919-9KYPA CLOSED THE PARAMETRIC HALF of what this item used to cover.
/// `Map[K = List[T = Float]]` was here too, on the reasoning that the check "reads the
/// key's own provisions and `List` provides no `NonEq`" — both halves of which have since
/// changed: `eq_derive::derive_conditional_noneq` derives `NonEq[List] :- NonEq[T]`, and
/// [`noneq_holds_at`] resolves the goal at the whole written key rather than reading an
/// edge.
///
/// (3) A container type the author never WRITES — one the typer infers at a call
/// site — has no written instantiation to record; the declared signature it flows
/// into or out of is what carries the refusal.
pub(crate) fn check_use_site_requires_eq(
    kb: &mut KnowledgeBase,
    sites: &[crate::kb::ParameterizedSite],
) -> Vec<crate::kb::load::LoadError> {
    use crate::kb::load::LoadError;
    let (Some(eq_sym), Some(noneq_sym)) = (
        kb.try_resolve_symbol("anthill.prelude.Eq"),
        kb.try_resolve_symbol("anthill.prelude.NonEq"),
    ) else {
        return Vec::new();
    };
    let eq_canon = kb.canonical_sort_sym(eq_sym);

    // WI-20260831-V25N3: the sites arrive from the caller's single drain (see
    // `load_phase_inner`), not from a drain of this pass's own — the written-row-label
    // check reads the SAME batch, and whichever check drained would have left the other
    // seeing nothing.

    let mut errors = Vec::new();
    // Per SITE, not per (container, carrier) pair: two `Map[K = Float]`s in two
    // places are two things to fix, and collapsing them would drop a diagnostic.
    // The key carries the whole `SourceSpan` — byte offsets alone repeat ACROSS
    // FILES, so a span-only key would silently drop the second file's refusal.
    let mut seen: HashSet<(Symbol, Symbol, Symbol, crate::span::SourceSpan)> = HashSet::new();
    // A base's `Eq` `requires` clauses with their RAW (unsubstituted) bindings — a
    // function of the BASE alone, so computed once per distinct base rather than once
    // per site. An EMPTY vec is a cached answer, not a missing one: it means "this
    // base requires no `Eq`", the overwhelmingly common case (`Option`, `List`,
    // `Result`, …), and it short-circuits the σ walk below — so those bases cost one
    // map hit per site instead of two `direct_requires_chain` clones.
    let mut eq_clauses: HashMap<Symbol, Vec<SortGoal>> = HashMap::new();
    for site in sites {
        let (base, site_span) = (site.base, site.span);
        // σ = declared param name → bound type. The lowering already mapped any
        // POSITIONAL argument onto its declared parameter (`Map[Float, Int64]` ⇒
        // `K = Float`), so this is a rename, not a re-derivation — re-deriving it
        // here would duplicate that mapping and, since the recorded bindings are
        // always named, leave the positional half unreachable.
        //
        // GROUND-ONLY, and that filter is this check's OWN (WI-20260831-V25N3 widened
        // the recorded bindings to carry a denoted one too). A `denoted` binding stands
        // a VALUE in a type-argument position — it names no carrier whose `NonEq`
        // provisions could be looked up — so it never contributed here and still does
        // not; dropping just that binding, rather than the whole site, is what keeps
        // `Map[K = Float, V = Buf[T = Int64, N = 3]]`'s `K` checked.
        let sigma: SmallVec<[(String, TermId); 2]> = site
            .bindings
            .iter()
            .filter_map(|(k, v)| match v {
                Value::Term { id, .. } => Some((kb.local_name_of(*k).to_string(), *id)),
                _ => None,
            })
            .collect();
        // Base's `requires` clauses, both σ-substituted (`Map[K=Float]` ⇒ `Eq[T =
        // Float]`) and RAW. The raw pass names the parameter the diagnostic must
        // report: the substituted binding is the carrier `Float`, while the clause
        // as written is `Eq[T = K]`, so `K` — the container's OWN parameter, which
        // is what the author has to change — is only recoverable from the raw form.
        // Reading it back out of σ by matching the carrier would misname the
        // parameter whenever two params bind the same carrier (`Map[K = Float, V =
        // Float]`). Both derive from the one `direct_requires_chain(base)`, so they
        // are clause- and binding-aligned by construction.
        //
        // The RAW pass is per-BASE and cached: it does not depend on σ, and
        // `direct_requires_chain` clones its memoized entry vector on every call, so
        // recomputing it per SITE multiplied that clone by every `Option[…]` /
        // `List[…]` written anywhere. A base with no `Eq` clause caches an empty vec
        // and every later site of it costs one map hit.
        let raw_goals = eq_clauses.entry(base).or_insert_with(|| {
            provider_requires_subgoals(kb, base, &[], &[])
                .into_iter()
                .filter(|g| kb.canonical_sort_sym(g.spec_sort) == eq_canon)
                .collect()
        });
        if raw_goals.is_empty() {
            continue;
        }
        // Re-walk with σ applied. Filtered to the `Eq` clauses the same way, so the
        // two vectors stay index-aligned with the cached raw ones.
        let goals: Vec<SortGoal> = provider_requires_subgoals(kb, base, &sigma, &[])
            .into_iter()
            .filter(|g| kb.canonical_sort_sym(g.spec_sort) == eq_canon)
            .collect();
        for (gi, goal) in goals.iter().enumerate() {
            for (bi, (key, val)) in goal.bindings.iter().enumerate() {
                if !type_value_is_ground(kb, *val) {
                    continue; // abstract binding: defer (not a concrete carrier)
                }
                let carrier = match kb.get_term(*val) {
                    Term::Fn { functor, .. } | Term::Ref(functor) | Term::Ident(functor) => {
                        *functor
                    }
                    _ => continue,
                };
                // WI-20260919-9KYPA — RESOLVE `NonEq` AT THE WHOLE BOUND TYPE, where this
                // read the head carrier's own provisions. `sort_provides(List, NonEq)` is
                // an edge in the `SortProvidesInfo` graph and says nothing about the
                // ARGUMENT, so once `eq_derive` derives the conditional row it answers
                // true for `List[T = Int64]` as readily as for `List[T = Float]` — it
                // would turn the gap into a blanket refusal of every parametric key. The
                // goal is what distinguishes them: it descends the conditional row's
                // `:- NonEq[T]` through the written argument and fails at `Int64`.
                //
                // Not a fast path plus a goal, for that same reason: an unconditional
                // `NonEq[Float]` resolves through this goal too, so a `sort_provides`
                // pre-check could only ADD the verdict the goal exists to refuse.
                if !noneq_holds_at(kb, noneq_sym, *val) {
                    continue;
                }
                // The container's own parameter, from the raw clause. A clause that
                // binds a CONCRETE carrier outright (`requires Eq[T = Float]`, an
                // ill-formed sort no instantiation can fix) has no container param
                // to name, so the spec's own binding key is reported instead.
                let raw = raw_goals
                    .get(gi)
                    .and_then(|g| g.bindings.get(bi))
                    .filter(|(k, _)| k == key)
                    .map(|(_, raw)| *raw);
                let param = raw
                    // The same "is this a bare name" rule σ-substitution applied, so
                    // the parameter reported is the one that carried the carrier in.
                    .and_then(|raw| view_ref_symbol(kb, &TermIdView(raw)))
                    // Accept the raw name only when it is the one σ actually
                    // substituted — the SAME comparison `map_requires_name` makes
                    // (bare `local_name_of` against the σ key), so the parameter
                    // reported is exactly the parameter that carried the carrier in.
                    .filter(|s| sigma.iter().any(|(n, _)| n == kb.local_name_of(*s)))
                    .unwrap_or(*key);
                if seen.insert((
                    kb.canonical_sort_sym(base),
                    kb.canonical_sort_sym(carrier),
                    param,
                    site_span,
                )) {
                    let err = LoadError::NonEqKeyRequiresLawfulEq {
                        container: kb.qualified_name_of(base).to_string(),
                        param: kb.local_name_of(param).to_string(),
                        spec: kb.qualified_name_of(goal.spec_sort).to_string(),
                        // WI-20260919-9KYPA — the WHOLE bound type, not its head sort.
                        // Now that `NonEq` is decided at the argument, naming the head
                        // would print "`anthill.prelude.List` binds a carrier that
                        // provides `NonEq`" — a claim about `List` that is FALSE (it is
                        // `List[T = Int64]`-lawful) and that points the author at a
                        // container they have no reason to stop using. The refusal is
                        // about `List[T = Float]`; say that.
                        //
                        // `format_term_for_goal`, not `type_display_name`: this message
                        // has always printed QUALIFIED carrier names, and that renderer
                        // prints local ones — switching would have silently shortened
                        // `anthill.prelude.Float` to `Float` in every pre-existing
                        // refusal. This one qualifies the base and recurses into the
                        // arguments, which is the same convention `format_goal` uses for
                        // the sibling requirement diagnostics.
                        carrier: format_term_for_goal(kb, *val),
                        span: Some(site_span.span),
                    };
                    // WI-745: attribute to the file the site's span indexes into, so
                    // the refusal renders `path:line:col` rather than naming no file.
                    errors.push(err.located_in_kb_source(kb, site_span.source));
                }
            }
        }
    }
    errors
}

/// WI-363: provider-side **operation** coverage — the op-level twin of
/// [`check_provider_requires`]. For each `fact Spec[X]` (a `SortProvidesInfo`
/// fact), every operation `Spec` declares must be *backed* for `X` by something
/// the EVALUATOR can dispatch to (WI-818): a runnable body or a builtin. An op
/// with neither resolves to nothing at runtime, so the satisfaction fact is
/// unsound — reported as a load-blocking
/// [`LoadError::UnbackedProviderOperation`].
///
/// The accepted backing kinds:
///   - **host carriers** (`Int`/`Float`/… via `provides X language rust`): their
///     ops are backed by the host artifact (`Int.compare` is `i64`'s `Ord`), so
///     the whole provision is skipped — detected by an
///     `anthill.realization.Implementation` fact targeting `X`. Mirrors how
///     [`check_provider_requires`] skips `EffectsRuntime`.
///   - **spec/carrier op body**: a runnable `operation … = …` on `Spec` or `X`
///     (resolved via `sort_ops` + `op_has_runnable_body`).
///   - **builtin**: an op mapped to a resolver builtin (`PartialEq.eq`, `Numeric.add`).
///   - **instance-fact op binding** (WI-431, checked by the caller): a
///     provision that BINDS the op (`fact Spec[X, op = boundOp]`) backs it with
///     the bound operation.
///
/// A RULE does not back an operation (WI-818, reversing WI-363's original
/// reading): an equational law (`rule op(args) <=> rhs`) or a relational clause
/// (`op(args, r) :- body`) is SPECIFICATION the SLD world resolves against, not
/// something the evaluator can run — counting them certified programs that
/// loaded clean and then died at run time (`UnknownOperation`). See
/// [`op_backed`].
///
/// SCOPE: only provisions whose carrier is CONCRETE (has constructors —
/// `sorts_with_constructors`) are checked; an abstract/value-less carrier
/// (`Set`, `Map`) is skipped, since no runtime value can dispatch through it.
///
/// WI-928 corrects one example this doc used to give: `Vec3` was named here as a
/// value-less "namespace-level provision head", and it is nothing of the kind —
/// `entity Vec3(x: Float, y: Float, z: Float)` is a §6.3 free-standing entity,
/// every bit as instantiable as the `sort` spelling. It read as abstract only
/// because a free-standing entity emitted no `SortInfo`, so the concreteness
/// question was answered by an omission.
///
/// WI-931 spent that correction: §6.3's free-standing carriers are checked here
/// like any other, with no staging left. The 12 reports the widening produced
/// were all TRUE and are all closed at their source — `Vec3` gained runnable
/// bodies for the four `VectorSpace` members its relational rules only specified
/// (a rule is not backing, WI-818), the six persistence operations moved from a
/// hardcoded eval registration no load-time reader could see to `operation_map`
/// clauses that every reader can (`rustland/anthill-stl/anthill/persistence.anthill`),
/// and `BulkStore`, whose sole member no host implemented, was deleted outright
/// by WI-932 — a spec this check forbids anyone from ever providing is a shape
/// with no realization, not a pending gap. (Rationale in full:
/// `stdlib/anthill/persistence/store.anthill`'s header.)
pub fn check_provider_operations(kb: &mut KnowledgeBase) -> Vec<crate::kb::load::LoadError> {
    use crate::kb::load::LoadError;
    // Not merely an empty relation: `check_member_blocks_have_one_clause` below runs
    // whatever the provisions are, and a KB with no `SortProvidesInfo` skips it too.
    if kb
        .try_resolve_symbol("anthill.reflect.SortProvidesInfo")
        .is_none()
    {
        return Vec::new();
    }
    let effects_runtime = effects_runtime_sym(kb);

    // Host-realized carriers (`Implementation.target` QNs) — a carrier whose
    // operations are implemented by a host artifact rather than by an anthill body.
    //
    // WI-880 — THIS IS NO LONGER A WHOLESALE SKIP, and the narrowing is the
    // per-carrier version of the very defect WI-876 fixed per-spec-op. It used to
    // read "it is a host carrier, so assume every operation is backed", which is a
    // claim about the CARRIER answering a question asked about an OPERATION. Since
    // WI-876 backing is knowable per operation, so the flag now only decides whether
    // a SPEC-LEVEL `operation_map` counts (see [`op_backed`]'s `host_realized` leg);
    // an operation this host realizes NOWHERE is refused like any other.
    //
    // MEASURED — before the narrowing, a `provides Widget3 language rust` carrier
    // with body-less, UNMAPPED, unimplemented `compare`/`eq` plus `fact Ord[Widget3]`
    // LOADED CLEAN, so `op_is_executable`'s host-mapping leg was correct by
    // construction and reached by nothing. It is reached now:
    // `wi880_arithmetic_mapping_test::a_host_carrier_still_owes_an_operation_no_host_realizes`.
    //
    // NO LANGUAGE FILTER, deliberately, and WI-886 is why the question has to be
    // answered rather than inherited: `emit_implementation_fact` emits a row for
    // EVERY `provides X language <L>` block, so a cpp-only binding puts `X` here for
    // the rust build too. That is CORRECT for this check and wrong for eval, and the
    // two now say so in the same vocabulary — a LOAD check asks "does the program
    // declare an implementation", which a cpp mapping answers (matching
    // [`op_is_executable`]'s language-agnostic `is_host_mapped_op`), while eval asks
    // "can THIS runtime call it" and reads `is_interpreter_mapped_op`
    // ([`op_is_interpretable`]). Before the narrowing the two legs of this one check
    // disagreed about what "host-realized" means and nothing noticed, because the
    // wholesale skip never consulted an operation at all.
    let mut host_targets: std::collections::HashSet<String> = std::collections::HashSet::new();
    if let Some(impl_sym) = kb.try_resolve_symbol("anthill.realization.Implementation") {
        for rid in kb.rules_by_functor(impl_sym) {
            if !kb.is_fact(rid) {
                continue;
            }
            let Some(named) = kb.fact_head_named_args(rid) else {
                continue;
            };
            let Some(target) = get_named_arg(kb, &named, "target") else {
                continue;
            };
            if let Some(qn) = impl_target_qn(kb, target) {
                host_targets.insert(qn);
            }
        }
    }

    // Every sort's own declared operations (one shared `SortInfo` scan).
    let own_ops: HashMap<Symbol, Vec<Symbol>> =
        crate::kb::load::sorts_and_own_ops(kb).into_iter().collect();
    // Concrete carriers (have constructors). An *abstract* carrier providing
    // `fact Spec[Self]` (e.g. `LogicalStream`, `Stream`-provides-`Iterable`) is a
    // sub-interface whose ops may stay primitives — only concrete carriers must
    // back every op (they are the runtime witnesses).
    let concrete = crate::kb::load::sorts_with_constructors(kb);

    // Snapshot the provisions before the per-op walk (which interns short names,
    // mutating `kb` — can't overlap the `rules_by_functor` borrow). See
    // [`Provision`] for what each field is.
    let provisions = collect_provisions(kb);

    let mut errors = Vec::new();
    check_member_blocks_have_one_clause(kb, &mut errors);
    for p in &provisions {
        if Some(p.spec) == effects_runtime {
            continue;
        }
        // WI-1103 — a row `eq_derive::run` DERIVED. Its `NonEq` witness `nonEqRefl` is
        // a propagated classification (the partial field is the witness), not a
        // hand-declared primitive, so it is not held to op-backing — the decision is
        // `eq_derive`'s module header's, and this is where it is read. It used to be
        // read from the PASS ORDER (`run` stands below this check), which protects the
        // row being created and not the row that already exists: a second
        // `load_phase_inner` over the same KB reaches these rows here, BEFORE
        // `eq_derive` re-runs, and refused a KB that had just loaded clean.
        //
        // ONLY this walk skips. The coherence grouping below and
        // `check_provision_binding_agreement` still see the derived rows, because
        // their questions — is there a second candidate for this dictionary, do the
        // bindings agree — are about what the relation SAYS, and a derived row says
        // it as loudly as a written one.
        if kb.is_unbacked_derived_provision(p.rid) {
            continue;
        }
        // Abstract carrier (no constructors) → sub-interface, ops may stay
        // primitives. Only concrete carriers are checked.
        if !concrete.contains(&p.carrier) {
            continue;
        }
        let carrier_qn = kb.qualified_name_of(p.carrier).to_string();
        let host_realized = host_targets.contains(&carrier_qn);
        let Some(spec_ops) = own_ops.get(&p.spec) else {
            continue;
        };
        for &spec_op in spec_ops {
            let op_short = kb
                .qualified_name_of(spec_op)
                .rsplit('.')
                .next()
                .unwrap_or("")
                .to_string();
            // Proposal 066 §7.3 — A MEMBER BACKS ONLY ITS OWN PROVISION. The carrier's
            // operation of this name, written in ANOTHER provision's `where` block,
            // exists only where that provision's conditions hold, so it is not this
            // provision's `op_short`. Refused rather than skipped to a default: the
            // carrier op of that name is what a dispatch by name would reach, with a
            // dictionary laid out for a provision it does not belong to.
            if let Some(foreign) = foreign_block_member(kb, &carrier_qn, &op_short, p.spec) {
                errors.push(LoadError::Other {
                    message: format!(
                        "`provides {spec}[…]` on `{carrier_qn}` has no `{op_short}`: \
                         `{carrier_qn}.{op_short}` is written in the `where` block of \
                         `provides {owner}[…]`, and a block member backs only its own \
                         provision (proposal 066 §7). Give `{spec}` its own `{op_short}` \
                         in a `where` block of its provision",
                        spec = kb.qualified_name_of(p.spec),
                        owner = kb.qualified_name_of(foreign),
                    ),
                });
                continue;
            }
            if op_backed(
                kb,
                p.carrier,
                &carrier_qn,
                spec_op,
                &op_short,
                host_realized,
            ) {
                continue;
            }
            // WI-431: a retroactive INSTANCE FACT (`fact CpsMonad[F = Option,
            // pure = optionPure, …]`) backs a spec op by BINDING it in the fact
            // — the op-valued binding IS the dictionary entry. Coverage moves to
            // the fact: an op bound here (to an operation) is backed without the
            // carrier owning it or the spec defaulting it. A type-only provision
            // (`provides Stream[T = X]`) has no op-valued binding, so this never
            // matches and pre-WI-431 coverage is unchanged.
            if op_bound_in_instance_fact(kb, p.spec_view, &op_short) {
                continue;
            }
            errors.push(LoadError::UnbackedProviderOperation {
                carrier: carrier_qn.clone(),
                spec: kb.qualified_name_of(p.spec).to_string(),
                op: op_short,
                // WI-1109: a row this loader DERIVED must not be reported as if the
                // author wrote it. The refusal itself stands — a concrete carrier owes
                // the operation however the row arrived — so this names the source
                // rather than exempting the row.
                derived_from: kb
                    .derived_provision_origin_of(p.rid)
                    .map(|origin| kb.qualified_name_of(origin).to_string()),
            });
        }
    }

    // COHERENCE (WI-431 rule 2 / WI-450 witness flavor / WI-838 the MIXED pair /
    // WI-859 the self-provider) — the VERDICT half; what is SEEN is
    // [`provider_coherence_groups_with`], whose doc owns why the two are separate.
    let groups = provider_coherence_groups_with(kb, &provisions, &own_ops, &concrete);
    for ProviderGroup {
        spec,
        carrier,
        candidates,
    } in &groups
    {
        // A group of one candidate is the ordinary single-provider case; skipping it
        // keeps the name allocations below to the erroring groups only (every load has
        // many groups and almost never an erroring one).
        if candidates.len() < 2 {
            continue;
        }
        // WI-843 (058 §4.1 tier 3 / §4.3) — THE COEXISTENCE RULE, stated once and as
        // itself rather than left to emerge from which per-kind counter happens to
        // fire. Every candidate nameable ⇒ the group is admissible, and an unselected
        // dispatch against it is refused at that CALL
        // ([`LoadError::UnselectedInstance`]) instead of here. `AmbiguousWitness` is
        // DELETED rather than gated: the group it refused is now legal, and a dormant
        // variant would invite a second grouping to grow back around it.
        //
        // Reading the rule off the counters is precisely how WI-838's blind spot was
        // built — the grouping was generalised over kinds while the verdict stayed a
        // per-kind pair, so an unenumerated combination defaulted to ADMIT. Here the
        // default is the rule, and [`Provider::is_nameable`] is a `match` that a new
        // provider kind cannot skip.
        //
        // This gate is also what makes the skip above honest again: a witness-only
        // group is now the COMMON legal case, and it no longer allocates two qualified
        // names and a `Vec` of every witness before discovering it can raise nothing.
        //
        // Coexistence past this point is only sound because every BRACKET-LESS
        // provider reader was hardened first (WI-842, §4.9): the sem-eq index and the
        // carrier-keyed provision reader still refuse at LOAD (neither has a nameable
        // candidate or a site to complain from), and the value-directed chain goes loud
        // at the read. Delete this refusal without that and coexistence lands on silent
        // first-match.
        //
        // WI-859's SECOND admission arm — see [`fact_beside_self_provider_is_one_carrier`]
        // for why a lone instance fact beside the carrier's own provision is admitted
        // rather than refused, and for the measurement that decided it.
        if candidates.iter().all(Provider::is_nameable)
            || fact_beside_self_provider_is_one_carrier(candidates)
        {
            continue;
        }
        // THE VERDICT MATRIX (WI-859) — every composition and its answer, measured cell
        // by cell over the stdlib and the whole corpus BEFORE any arm here was written.
        // The per-cell counts are the measurement record and live in
        // `docs/design/058-implementation.md` §11, where they can be dated rather than
        // rot here. Write a group as (f facts, w witnesses, s self-providers); `s` is 0
        // or 1, because a `SelfProvider`'s identity IS the group's own carrier key and
        // duplicates collapse at `record`.
        //
        //   (0, ≥1, *)  ADMIT — every candidate nameable (058 tier 3)
        //   (1,  0, 1)  ADMIT — may be ONE dictionary, see the helper above
        //   (≥2, *, *)  AmbiguousInstanceFact
        //   (1, ≥1, *)  MixedProviderKinds (whose message names the fact and the
        //               witnesses; a self-provider in that group goes unnamed)
        //
        // NO VERDICT CHANGED by adding the kind — it changes what is SEEN.
        //
        // THE SPACE IS TILED, which is what keeps the NEXT kind from defaulting to
        // ADMIT the way WI-838's did. Reaching here means f ≥ 1 (else every candidate
        // is nameable) and (f, w, s) ≠ (1, 0, 1) (the arm just above), while
        // f + w + s ≥ 2 (the size skip) — so f > 1, or f = 1 with w ≥ 1. The
        // `debug_assert` below ENFORCES that rather than leaving it argued, and is also
        // what makes the second admission arm load-bearing — DRIVEN: delete that arm and
        // this fires on the two wi837 `Pebble` fixtures — and, since that was written, on
        // `test.wi859.rival` and WI-1032's `test.wi1032.conflict` too, so "both" is a floor
        // rather than the count.
        let spec_qn = kb.qualified_name_of(*spec).to_string();
        let carrier_qn = kb.qualified_name_of(*carrier).to_string();
        let facts = candidates
            .iter()
            .filter(|c| matches!(c, Provider::Fact(_)))
            .count();
        let witnesses: Vec<String> = candidates
            .iter()
            .filter_map(|c| match c {
                Provider::Witness(w) => Some(kb.qualified_name_of(*w).to_string()),
                Provider::Fact(_) | Provider::SelfProvider(_) => None,
            })
            .collect();
        debug_assert!(
            facts > 1 || !witnesses.is_empty(),
            "coherence group ({spec_qn}, {carrier_qn}) was admitted by neither arm and is \
             named by neither diagnostic — an unenumerated composition, which is how \
             WI-838's blind spot was built. Candidates: {candidates:?}"
        );
        if facts > 1 {
            errors.push(LoadError::AmbiguousInstanceFact {
                carrier: carrier_qn.clone(),
                spec: spec_qn.clone(),
                count: facts,
            });
        }
        // WI-838 — the MIXED pair. The witness leg still RECORDS into the grouping
        // above even though two witnesses alone no longer refuse: dropping witnesses
        // from it would re-open the cross-kind blind spot, and this arm is what needs
        // to see them.
        if facts > 0 && !witnesses.is_empty() {
            errors.push(LoadError::MixedProviderKinds {
                carrier: carrier_qn.clone(),
                spec: spec_qn,
                fact_count: facts,
                witnesses,
            });
        }
    }

    errors.extend(check_provision_binding_agreement(kb, &provisions));
    errors
}

/// Every `anthill.reflect.SortProvidesInfo` fact, as [`Provision`] rows.
fn collect_provisions(kb: &KnowledgeBase) -> Vec<Provision> {
    provides_rows(kb)
        .map(|row| Provision {
            carrier: row.provider,
            spec: row.spec_base,
            spec_view: row.spec_view,
            rid: row.rid,
        })
        .collect()
}

/// One coherence group: everything that supplies a dictionary for one
/// `(spec, dispatch carrier)`. See [`provider_coherence_groups_with`].
struct ProviderGroup {
    /// The spec, canonical.
    pub(super) spec: Symbol,
    /// The DISPATCH carrier, canonical — not the provider: a witness sort groups
    /// under the carrier it names, which is the whole point of the key.
    pub(super) carrier: Symbol,
    /// The candidates, in the order the provisions were recorded.
    pub(super) candidates: SmallVec<[Provider; 2]>,
}

/// WI-859 — THE PROBE: who the coherence grouping records for one `(spec, carrier)`,
/// each candidate rendered `kind:qualified-name` (`self:ns.Leaf`,
/// `witness:ns.Rival`, `fact` — an instance fact has no name, which is the point of
/// the nameability gate). Empty when no group exists.
///
/// Rendered rather than structural, deliberately. This exists so that WHAT IS SEEN can
/// be asserted apart from WHAT IS REFUSED — the two halves whose disagreement is this
/// check's whole history, and a distinction no verdict can show, since the cells WI-859
/// populates are precisely the ones whose verdict did not change. Handing out
/// [`Provider`] instead would publish a hash-consed `spec_view` id with no meaning
/// outside this module, and `ProviderGroup`'s invariants (canonical keys, per-kind
/// dedup) live in a private closure.
///
/// NOT the reader for 058 phase 8b's `self_provides`. This carries the coherence pass's
/// POLICY — the op-less-spec exemption drops a self-provision whose spec declares no
/// ops, and the concrete-provider exemption reshapes the witness leg — and a defaults
/// relation must inherit none of it; `witness_dispatch_carrier` over
/// [`provides_rows_of_spec`] is the policy-free classifier for that.
///
/// COST: two full `SortInfo` scans, so this is a probe entry point, not a load-path
/// one. `check_provider_operations` has both in hand and calls the grouping directly.
pub fn provider_coherence_candidates(
    kb: &KnowledgeBase,
    spec_qn: &str,
    carrier_qn: &str,
) -> Vec<String> {
    let own_ops: HashMap<Symbol, Vec<Symbol>> =
        crate::kb::load::sorts_and_own_ops(kb).into_iter().collect();
    let concrete = crate::kb::load::sorts_with_constructors(kb);
    let groups = provider_coherence_groups_with(kb, &collect_provisions(kb), &own_ops, &concrete);
    groups
        .iter()
        .find(|g| {
            kb.qualified_name_of(g.spec) == spec_qn && kb.qualified_name_of(g.carrier) == carrier_qn
        })
        .map(|g| {
            g.candidates
                .iter()
                .map(|c| match c {
                    Provider::Fact(_) => "fact".to_string(),
                    Provider::Witness(w) => format!("witness:{}", kb.qualified_name_of(*w)),
                    Provider::SelfProvider(c) => format!("self:{}", kb.qualified_name_of(*c)),
                })
                .collect()
        })
        .unwrap_or_default()
}

/// The GROUPING half of the coherence check, separated from the VERDICT
/// ([`check_provider_operations`]) because the entire history of this check is a
/// grouping and a verdict that disagreed about which combinations exist. Probed
/// through [`provider_coherence_candidates`].
///
/// Two dictionaries for one `(spec, carrier)` are ambiguous whatever KIND supplies
/// them, and grouping BY KIND is exactly what let the cross-kind pair through
/// (WI-838): the instance-fact rule keyed a provision on its own `sort_ref`, and the
/// witness rule skipped every provision whose provider IS the carrier — so a
/// namespace-level `fact Combiner[T = Tag, combine = …]` (whose derived `sort_ref`
/// IS `Tag`) was invisible to the witness grouping, while `sort WitCombiner provides
/// Combiner[T = Tag]` binds no op and was invisible to the fact grouping. That pair
/// LOADED CLEAN, and the two dispatch routes did not even agree on the winner:
/// MEASURED, value-directed dispatch ran the INSTANCE FACT's op (its `or_else`
/// chain, which WI-842 replaced with a loud multi-candidate read) while the
/// THREADED-DICT route dies `EvalError::Internal("unhandled Expr variant")`. Hence
/// one group per `(spec, dispatch carrier)` holding candidates of every kind — a
/// kind can no longer have a grouping of its own to hide in.
///
/// Insertion-order grouping keeps the diagnostics deterministic.
///
/// Symbol identity: keys are CANONICAL. The instance-fact rule used to key RAW on
/// the stated ground that provider symbols are already canonical (both sides come
/// from post-load `SortProvidesInfo` facts) — MEASURED true: across the stdlib and
/// the whole test corpus, no provision has a `spec`/`carrier` that differs from its
/// canonical symbol, so canonicalizing the key changes no existing grouping while
/// giving the cross-kind check the key the witness side already used. A `spec_view`
/// is still compared RAW, so copy-divergent-but-identical facts stay idempotent
/// (`cross_namespace_identical_instances_*`).
fn provider_coherence_groups_with(
    kb: &KnowledgeBase,
    provisions: &[Provision],
    own_ops: &HashMap<Symbol, Vec<Symbol>>,
    concrete: &std::collections::HashSet<Symbol>,
) -> Vec<ProviderGroup> {
    let mut groups: Vec<ProviderGroup> = Vec::new();
    // The one insertion point, so a candidate of ANY kind dedups by the same rule:
    // an idempotent re-record (a repeated identical fact, a witness recorded twice,
    // a carrier's two self-provisions at two applications) shares its `Provider` and
    // collapses.
    let mut record = |spec: Symbol, carrier: Symbol, cand: Provider| match groups
        .iter_mut()
        .find(|g| g.spec == spec && g.carrier == carrier)
    {
        Some(g) => {
            if !g.candidates.contains(&cand) {
                g.candidates.push(cand);
            }
        }
        None => groups.push(ProviderGroup {
            spec,
            carrier,
            candidates: SmallVec::from_elem(cand, 1),
        }),
    };
    for p in provisions {
        let spec_canon = kb.canonical_sort_sym(p.spec);
        let binds_op = provision_binds_any_op(kb, p.spec_view);
        // KIND 1 — INSTANCE FACT: the provision itself BINDS an op, and that
        // op-valued binding IS the dictionary entry. A type-only provision
        // (`provides Stream[T = X]`) supplies no dictionary and never participates
        // as a fact, so existing `provides` / type-only `fact`s (e.g. `fact
        // ModifyRuntime[T = Cell, V = V]`) are never over-rejected. Its dispatch
        // carrier is the provision's own `sort_ref`: the loader DERIVES a
        // namespace-level `fact Spec[T = Carrier, …]`'s `sort_ref` from the carrier
        // binding, so `sort_ref` already IS the carrier.
        if binds_op {
            record(
                spec_canon,
                kb.canonical_sort_sym(p.carrier),
                Provider::Fact(p.spec_view),
            );
        }
        // The OP-LESS SPEC exemption, shared by kinds 2 and 3: a spec that declares
        // no ops has no dictionary to be ambiguous about — a bare carrier spec
        // (`sort W449Outer { sort C = ? }`) provided by two carriers is
        // binding-extraction plumbing, not a dispatch conflict. ASYMMETRIC with the
        // fact leg on purpose-of-record: the fact leg's peer gate is
        // `provision_binds_any_op`, which is per PROVISION rather than per SPEC, so
        // two facts binding a non-spec op on an op-less spec still collide while two
        // witnesses of it do not. Pre-existing, left as found — lifting `own_ops` to
        // the group would change the fact rule in that corner and needs its own
        // measurement.
        let spec_has_ops = own_ops.get(&p.spec).is_some_and(|ops| !ops.is_empty());
        if !spec_has_ops {
            continue;
        }
        // KINDS 2 AND 3 PARTITION the remaining provisions on ONE question — does
        // this provision name a dispatch carrier OTHER than its provider — asked
        // through the single owner of that criterion, which is also what
        // [`provision_supplier`] (dispatch) asks. A `match` rather than two `if`s so
        // the two kinds cannot both claim one provision, nor both miss it: missing it
        // is exactly what WI-859 fixes, and claiming it twice would make ONE
        // provision a group of two.
        match witness_dispatch_carrier(kb, p.spec, p.carrier, p.spec_view) {
            // KIND 2 — WITNESS SORT, under an exemption that is POLICY, not
            // classification, and so is applied here rather than hidden inside the
            // classifier: a CONCRETE provider (with constructors) is a backend whose
            // VALUES carry their own sort, so value-directed dispatch distinguishes
            // them by the value. Two concrete backends providing one spec at the same
            // bindings is the existential / manifest-provider pattern (`MemStore` /
            // `DiskStore` provide `KVStore[K = String]`, design §5 — selected by the
            // `ensures` return), NOT an ambiguity. NOTE the mismatch, since it is what
            // bounds WI-838: the RATIONALE is about the GROUP (the value picks among
            // the candidates) while the GATE is PER CANDIDATE, so a concrete witness
            // beside an instance fact is exempted too even though no value
            // distinguishes those. Pinned as-is by
            // `concrete_witness_beside_a_fact_stays_exempt`; WI-838's scope was the
            // cross-kind BLIND SPOT, not the exemption's criterion, and widening it is
            // a design increment of its own.
            Some(carrier_canon) if !concrete.contains(&p.carrier) => record(
                spec_canon,
                carrier_canon,
                Provider::Witness(kb.canonical_sort_sym(p.carrier)),
            ),
            Some(_) => {}
            // KIND 3 — SELF-PROVIDER (WI-859, the prerequisite of 058 §3.6's
            // `one_default`): the provision's dispatch carrier IS the provider, so the
            // dictionary is the CARRIER'S OWN MEMBERS —
            // `sort Leaf { fact Desc[T = Leaf]; operation describe(…) = … }`.
            //
            // The criterion is `witness_dispatch_carrier == None` and NOT a second
            // reading of "provider is carrier", deliberately: [`provision_supplier`]
            // keys exactly this case at `canonical_sort_sym(provider)`, so grouping it
            // any other way would put the load check and the dispatch reader on
            // different carriers — the disagreement WI-838 exists to prevent. That
            // folds in the bare / own-param-bound provision (`provides Spec`,
            // `provides Spec[T = OwnParam]`, where no SORT is named): dispatch keys
            // those at the provider too.
            //
            // The CONCRETE-provider exemption is NOT applied here, and the asymmetry
            // is the point. It reads a concrete provider as a manifest BACKEND whose
            // values tell it apart from a rival backend; a self-provider is not a
            // rival backend but the carrier the group is keyed ON, so no value
            // distinguishes it from anything else in its group. Applying the exemption
            // would exempt nearly every real carrier and leave the kind empty —
            // WI-855's `Leaf` is concrete.
            None if !binds_op => {
                let carrier_canon = kb.canonical_sort_sym(p.carrier);
                record(
                    spec_canon,
                    carrier_canon,
                    Provider::SelfProvider(carrier_canon),
                )
            }
            // A carrier-keyed provision that BINDS an op is kind 1, recorded above.
            None => {}
        }
    }
    groups
}

/// WI-859 — the group compositions admitted DESPITE holding an unnameable candidate:
/// exactly one instance fact beside the carrier's own provision, and nothing else.
///
/// The nameability rule (058 §4.3) refuses a group holding a candidate no bracket can
/// spell, on the ground that two dictionaries need one selected. This composition is
/// the one where there need not BE two. A `SelfProvider` supplies whatever the CARRIER
/// owns, per op — which for a given op may be nothing — so `sort Pebble { entity
/// pebble(…); provides PartialEq[T = Pebble] }` beside a namespace-level `fact
/// PartialEq[T = Pebble, eq = pebbleEq]` is ONE dictionary written in two places, the
/// retroactive-instance shape WI-431 exists to support and WI-837 pins
/// (`a_type_only_provision_does_not_hide_a_later_eq_binding`, which asserts the fact's
/// `eq` ANSWERS). The group cannot tell that shape from a rival, because the question
/// is per-OP and a group is per-SPEC.
///
/// MEASURED before it was decided, over the stdlib and the whole corpus: this
/// composition occurs exactly twice, and the two are the two shapes —
/// `test.wi837.hidden.Pebble` (the fact completes a type-only self-provision, loads
/// clean, answers) and `test.wi837.ownplusfact.Pebble` (the fact rivals the carrier's
/// OWN `eq` member, and is already refused — `AmbiguousEqDispatch`). Refusing the
/// composition would have taken the first with the second.
///
/// So the RIVAL half stays owned by the readers that can count per op, which is where
/// §3.7's discipline puts it: `EqDispatchIndex` refuses at load for the `Eq` family
/// (no call site exists — dispatch fires from unification), `spec_op_suppliers_for_
/// carrier` is loud at the value-directed read for every other spec, and a
/// typer-classified call raises `UnselectedInstance`. Each is driven in
/// `wi859_self_provider_candidate_test`. This arm therefore admits no silence: it
/// admits a group whose conflict, if it has one, is refused by a check that can see it.
///
/// ASYMMETRIC with the fact + WITNESS pair, which is still refused at load
/// ([`LoadError::MixedProviderKinds`]) even though a MEMBERLESS witness supplies no
/// dictionary either and could be a completion by the same argument. Left as WI-838
/// found it: that leg's criterion is its own to widen, and doing it here would move a
/// verdict this phase measured as unchanged.
///
/// THE DEEPER ALTERNATIVE, recorded rather than taken. This arm exists because kind 3's
/// criterion is one notch coarser than its dispatch twin: [`Provider::SelfProvider`] is
/// recorded from the PROVISION, while `SupplyRoute::Own` is derived from
/// [`carrier_own_op`] — "the carrier actually has a member". Gating kind 3 on the
/// carrier owning at least one of the spec's ops would split this cell BY
/// CONSTRUCTION: a completion becomes a group of one (the size gate admits it) and a
/// rival a group of two (seen). It is not taken here because the rival half would then
/// need a VERDICT of its own — a new load refusal, which is the one thing WI-859 scoped
/// itself out of. Phase 8b meets the same fork when `self_provides` has to say whether
/// a carrier that owns no member self-provides at all.
fn fact_beside_self_provider_is_one_carrier(candidates: &[Provider]) -> bool {
    matches!(
        candidates,
        [Provider::Fact(_), Provider::SelfProvider(_)]
            | [Provider::SelfProvider(_), Provider::Fact(_)]
    )
}

/// WI-842 (proposal 058 §4.9) — refuse two CARRIER-KEYED provisions of one spec that
/// bind one type parameter DIFFERENTLY, the ambiguity
/// [`provider_spec_view_bindings`] would otherwise decide by SOURCE ORDER.
///
/// The candidate set is exactly what that reader matches: provisions whose `sort_ref`
/// IS the carrier asked about, keyed canonically on (carrier, spec base) as the reader
/// keys them. A WITNESS provision therefore participates only under ITS OWN sort — two
/// witnesses of one spec are two carriers here, never a conflict — which is what keeps
/// this check clear of proposal 058 phase 3b: 3b lets NAMEABLE providers (witness
/// sorts) coexist and moves their refusal to the use site, while a carrier's own
/// provisions have no name to select and so stay refused at load.
///
/// SAME APPLICATION, not merely same spec — the distinction this check turns on, and
/// the one whose absence made a first cut refuse the STDLIB. A carrier may provide one
/// spec MANY times at different APPLICATIONS: `sort Console` holds
/// `provides Effect[T = ConsoleOutput]`, `[T = ConsoleError]` and `[T = ConsoleInput]`
/// (console.anthill:35-37), three genuine instances that differ in the spec's CARRIER
/// PARAM. So provisions are bucketed by that param's binding first, and only a
/// disagreement WITHIN one bucket — same application, two answers for another param —
/// is a conflict. (The Console shape leaves this reader under-determined in a way
/// this ticket does not fix: asked for `Console`'s view of `Effect` it still answers
/// the first of three. That is not §4.9's defect — no op binding is being selected,
/// and MEASURED, no consumer asks — but it is the reason this reader cannot simply
/// be made loud on a second provision.)
///
/// AGREEMENT, not identity: two provisions binding a param to the same type are one
/// view (the reader merges them), so `provides Spec[T = C]` beside
/// `fact Spec[T = C, op = f]` is admitted — that PAIR is the shape whose second
/// binding used to hide behind the first. Comparison is deliberately CONSERVATIVE
/// (hash-consed identity, or two spellings of one sort): a structured binding written
/// two equivalent ways reads as a conflict rather than being waved through.
pub(super) fn check_provision_binding_agreement(
    kb: &KnowledgeBase,
    provisions: &[Provision],
) -> Vec<LoadError> {
    // (carrier, spec base) → the provisions' bindings, in source order so the
    // diagnostic lists the conflicting types the way the author wrote them.
    let mut groups: Vec<(
        (Symbol, Symbol),
        SmallVec<[SmallVec<[(Symbol, TermId); 2]>; 2]>,
    )> = Vec::new();
    for p in provisions {
        let Some((base, bindings)) = unwrap_spec_view(kb, p.spec_view) else {
            continue;
        };
        let key = (
            kb.canonical_sort_sym(p.carrier),
            kb.canonical_sort_sym(base),
        );
        match groups.iter_mut().find(|(k, _)| *k == key) {
            Some((_, views)) => views.push(bindings),
            None => groups.push((key, SmallVec::from_elem(bindings, 1))),
        }
    }
    let mut errors = Vec::new();
    for ((carrier, spec), views) in &groups {
        if views.len() < 2 {
            continue;
        }
        // The spec's CARRIER PARAM — its first type parameter, the same one
        // [`provision_carrier_sort`] reads to decide what a provision applies to.
        // A spec with no type params leaves every provision in one bucket, which is
        // right: they name one application by having no application to differ in.
        let carrier_param = sort_type_params_as_pairs(kb, *spec)
            .first()
            .map(|(sym, _)| short_name_of(kb.local_name_of(*sym)));
        let binding_of = |view: &SmallVec<[(Symbol, TermId); 2]>, short: &str| {
            view.iter()
                .find(|(p, _)| short_name_of(kb.local_name_of(*p)) == short)
                .map(|(_, v)| *v)
        };
        // Bucket by the carrier-param binding: one bucket per APPLICATION.
        let mut buckets: Vec<(
            Option<TermId>,
            SmallVec<[&SmallVec<[(Symbol, TermId); 2]>; 2]>,
        )> = Vec::new();
        for view in views {
            let app = carrier_param.and_then(|c| binding_of(view, c));
            let slot = buckets.iter_mut().find(|(a, _)| match (a, app) {
                (Some(x), Some(y)) => provision_bindings_agree(kb, *x, y),
                (None, None) => true,
                _ => false,
            });
            match slot {
                Some((_, vs)) => vs.push(view),
                None => buckets.push((app, SmallVec::from_elem(view, 1))),
            }
        }
        for (_, bucket) in &buckets {
            if bucket.len() < 2 {
                continue;
            }
            // Per PARAM SHORT NAME, because a param resolved in two import scopes can
            // carry two Symbols for one spec parameter — the same reason the readers
            // compare `short_name_of(local_name_of(param))`.
            let mut seen: Vec<(&str, SmallVec<[TermId; 2]>)> = Vec::new();
            for view in bucket {
                for (param, value) in view.iter() {
                    let short = short_name_of(kb.local_name_of(*param));
                    match seen.iter_mut().find(|(s, _)| *s == short) {
                        Some((_, vals)) => {
                            if !vals
                                .iter()
                                .any(|v| provision_bindings_agree(kb, *v, *value))
                            {
                                vals.push(*value);
                            }
                        }
                        None => seen.push((short, SmallVec::from_elem(*value, 1))),
                    }
                }
            }
            for (param, vals) in seen {
                if vals.len() > 1 {
                    errors.push(LoadError::ConflictingProvisionBindings {
                        carrier: kb.qualified_name_of(*carrier).to_string(),
                        spec: kb.qualified_name_of(*spec).to_string(),
                        param: param.to_string(),
                        values: vals.iter().map(|v| type_display_name(kb, *v)).collect(),
                    });
                }
            }
        }
    }
    errors
}

/// WI-842 — do two provision bindings name the SAME type? Hash-consed identity
/// first (structurally identical type views share one `TermId`), then the one
/// divergence that is not a real difference: a BARE sort name interned under two
/// Symbols. Anything else answers `false` — a parameterized type, an arrow, a row, a
/// tuple or a literal agrees by identity or not at all — see
/// [`check_provision_binding_agreement`] on why the conservative direction is the
/// safe one here.
///
/// The ONE owner of the question: [`subtype_provider_view`]'s route merge asks it too,
/// of two routes' values for one spec param — and that caller is why the bare-name arm
/// exists at all: a spec bound to one sort through two import scopes carries two
/// `TermId`s for one type, and reading those as a disagreement discards a legitimate
/// merged view (found by /code-review at the merge). So do the bare-spec sugar's two
/// readers of a carrier's bindings (WI-20260923-ZBWMC) — the loader's block pre-scan
/// and [`check_bare_spec_narrowings`] — which must agree on "one binding" or the check
/// would refuse a narrowing the block made.
///
/// WI-20260923-N3W68 (#3) — "bare" is the word that was missing. Both copies of this
/// predicate compared the HEAD sort of any sort-headed type (`sort_functor_of_view`
/// here, `load::sort_ref_functor` in the route merge — which also answers the functor of
/// ANY `Term::Fn`), so `List[T = Int64]` agreed with `List[T = String]`, and in the
/// route merge any two arrows agreed. MEASURED before the fix, both copies: one carrier
/// providing `Iter[Self = C, Element = List[T = Int64]]` and `[…, Element = List[T =
/// String]]` loaded clean or was refused depending only on which line came first, and so
/// did a carrier reaching one spec through two intermediates binding `P` to those two
/// types, or to `(Int64) -> Int64` and `(String) -> String`.
pub(crate) fn provision_bindings_agree(kb: &KnowledgeBase, a: TermId, b: TermId) -> bool {
    if a == b {
        return true;
    }
    match (type_head(kb, &TermIdView(a)), type_head(kb, &TermIdView(b))) {
        (TypeHead::SortRef(x), TypeHead::SortRef(y)) => same_sort_canonical(kb, x, y),
        _ => false,
    }
}

/// One `anthill.reflect.SortProvidesInfo` fact, snapshotted before
/// [`check_provider_operations`]'s per-op walk (which interns short names,
/// mutating `kb` — it can't overlap the `rules_by_functor` borrow). `carrier` is
/// the provision's `sort_ref`: the PROVIDER sort for a `provides` block, and the
/// DERIVED carrier for a namespace-level instance fact. `spec_view` is the full
/// `SortView` term, kept so the op-coverage check can read an INSTANCE FACT's
/// op-valued bindings (`pure = optionPure`) — the dictionary entries that back a
/// spec op without the carrier owning it (WI-431).
pub(super) struct Provision {
    pub(super) carrier: Symbol,
    pub(super) spec: Symbol,
    pub(super) spec_view: TermId,
    /// WI-1103 — the row's own fact, so the op-backing walk can ask whether it was
    /// DERIVED (`KnowledgeBase::is_unbacked_derived_provision`). Only that walk asks:
    /// coherence and binding agreement are about what the relation SAYS, and a
    /// derived row says it as loudly as a written one.
    pub(super) rid: RuleId,
}

/// WI-838 / WI-859 — what supplies the dictionary for one `(spec, carrier)`. The
/// three kinds are compared by DIFFERENT identities, which is why the coherence
/// grouping holds this enum rather than a bare symbol.
#[derive(Clone, Copy, PartialEq, Debug)]
pub(super) enum Provider {
    /// WI-431 INSTANCE FACT — `fact Spec[T = Carrier, op = boundOp]`. It has NO
    /// NAME, so its identity is the full canonical application (the WI-419 / §5.4
    /// rule): spec views hash-cons, so identical facts share one `spec_view` and
    /// collapse, and only genuinely-differing facts collide.
    Fact(TermId),
    /// WI-450 WITNESS SORT — `sort W provides Spec[T = Carrier]`, whose impls are
    /// W's own members. Two witnesses for one application share ONE hash-consed
    /// `spec_view` (the ops are not in the view), so identity is the provider SORT.
    Witness(Symbol),
    /// WI-859 SELF-PROVIDER — `sort C { provides Spec[T = C]; operation op … }`,
    /// whose impls are C's OWN members. The kind this grouping was one short of:
    /// it binds no op (so the [`Provider::Fact`] leg misses it) and its provider IS
    /// its carrier (so [`witness_dispatch_carrier`] returns `None` and the
    /// [`Provider::Witness`] leg misses it too), which is why a self-provider could
    /// never be one half of a refused pair whatever the other half was — MEASURED
    /// at WI-855, where a self-provider beside a rival loaded clean and tied only
    /// at dispatch.
    ///
    /// Identity is the carrier SORT — it is also the group's own carrier key, since
    /// the dictionary is the carrier's member set. Two self-provisions of one spec
    /// by one carrier are therefore ONE candidate, which is right: they name one
    /// member set, and a disagreement between their BINDINGS is
    /// [`LoadError::ConflictingProvisionBindings`]'s (WI-842), not a second
    /// dictionary.
    SelfProvider(Symbol),
}

impl Provider {
    /// WI-843 (058 §4.1 / §4.3) — can a use site SPELL this candidate?
    ///
    /// This is the coexistence rule itself, not a property of one diagnostic: a group
    /// whose every candidate is nameable may coexist and is refused only at a dispatch
    /// that selects none, because a tier-3 message can offer each of them; a group
    /// holding an unnameable one keeps the LOAD refusal, because a diagnostic listing
    /// a candidate the author cannot write is a dead end, not a fix.
    ///
    /// A `match` on purpose. Reading the rule off which of two per-kind COUNTERS
    /// happens to fire is how WI-838's blind spot was built — the grouping was
    /// generalised over kinds while the verdict stayed per-kind pair, so an
    /// unenumerated combination defaulted to ADMIT. §4.9 recorded that this grouping
    /// was one candidate kind short (the self-provider); WI-859 added it, and this
    /// match is where it had to answer.
    fn is_nameable(&self) -> bool {
        match self {
            // An instance fact has no name at all. Naming them (`fact AddM: Monoid[…]`)
            // is a possible later increment and explicitly out of scope (§4.3).
            Provider::Fact(_) => false,
            // A witness sort's name IS the value a bracket binds.
            Provider::Witness(_) => true,
            // A self-provider is spelled by the CARRIER's own name — `[Spec = Leaf]`
            // is the bracket that selects it, the same channel §3.5 validates for a
            // witness (check 1 asks only that the named sort provides the spec at the
            // call's bindings, which a self-provider does by construction).
            Provider::SelfProvider(_) => true,
        }
    }
}

/// WI-450 — the canonical DISPATCH CARRIER a provision names when that provision
/// is a WITNESS, else `None`.
///
/// A provision is a WITNESS exactly when the spec's carrier param (its first type
/// parameter) is bound to a sort DISTINCT from the provider — `sort TagCombiner
/// provides Combiner[T = Tag]` (carrier `Tag` ≠ provider `TagCombiner`). That
/// excludes (a) instance facts and normal self-providers, whose derived/own
/// carrier IS the provider, and (b) bare / carrier-less provisions (`provides
/// Store`), which name no dispatch carrier at all.
///
/// THE ONE OWNER of that criterion, which is why it is a free function rather
/// than inline at any caller: [`provision_supplier`] (dispatch, both the load-time
/// eq index and the per-call value-directed read), [`provision_binds_param_to_carrier`]
/// (the WI-424 carrier-param classification) and [`check_provider_operations`]'s
/// coherence grouping (load time) must agree about what a witness is. Before WI-838
/// each had its own copy of the two checks, which is the shape that produced the
/// cross-kind blind spot in the first place.
///
/// Carries NO policy: the coherence pass's two exemptions (an op-less spec, a
/// concrete provider) are applied at its own call site, where they are visible.
pub(super) fn witness_dispatch_carrier(
    kb: &KnowledgeBase,
    spec: Symbol,
    provider: Symbol,
    spec_view: TermId,
) -> Option<Symbol> {
    witness_dispatch_carrier_view(kb, spec, provider, spec_view).map(|(_, base)| base)
}

/// WI-860 — [`witness_dispatch_carrier`] with the carrier's WRITTEN VIEW kept beside
/// its base: `sort ListOrd provides Ord[T = List[T = E]]` answers
/// `(List[T = E], List)` where the symbol-only reader answers `List`.
///
/// The base alone is the right key for every DISPATCH reader — a dispatch is decided by
/// the value's sort — but it is NOT enough to decide whether two 058 §3.6 default rows
/// collide: `List[T = E]` beside `List[T = Int64]` is one family and two rows, while
/// `List[T = Int64]` beside `List[T = String]` is one family and two DISJOINT rows.
/// Both pairs share a base, so a base-keyed check would refuse the second with the
/// first. Hence one function answering both, rather than a second walk in
/// `defaults.rs` that would have to re-derive the criterion — the WI-838 shape.
///
/// `None` still means exactly what it means at the symbol reader: the provision's
/// dispatch carrier IS the provider (a self-provision, an instance fact, or a
/// bare / own-param-bound provision that names no other sort).
///
/// The TERM entry point. A spec view that is itself a `TermId` has `TermId` children, so
/// the carrier view comes back term-carried by construction; a non-term answer would mean
/// the decode invented a carrier out of a view that has none, which is a bug rather than
/// a case, and it says so.
pub(crate) fn witness_dispatch_carrier_view(
    kb: &KnowledgeBase,
    spec: Symbol,
    provider: Symbol,
    spec_view: TermId,
) -> Option<(TermId, Symbol)> {
    let (view, base) = witness_dispatch_carrier_value(kb, spec, provider, &Value::term(spec_view))?;
    match view {
        Value::Term { id, .. } => Some((id, base)),
        other => panic!(
            "witness_dispatch_carrier_view: a term-carried spec view yielded a \
             non-term carrier {other:?}"
        ),
    }
}

/// WI-860 — the base SORT of a spec view, carrier-neutrally: `crate::kb::load::
/// provides_spec_base_sym`'s answer for a `TermId`, and the same answer for the
/// OCCURRENCE carrier the resolver hands a matched `SortProvidesInfo.spec` back on.
///
/// A `pub(crate)` door onto [`unwrap_spec_view_value`] rather than a fifth decode of the
/// `SortView(base, …bindings)` shape — the builtin behind
/// `anthill.reflect.typing.dispatch_carrier` needs the spec sort to ask the classifier
/// anything, and deriving it any other way would be a second reading of what a spec view
/// is. (Only the BASE is taken here, which is the half `unwrap_spec_view_value` reads
/// identically on both carriers; the BINDINGS are not — see
/// [`provision_carrier_binding`].)
pub(crate) fn spec_view_base(kb: &KnowledgeBase, spec_view: &Value) -> Option<Symbol> {
    unwrap_spec_view_value(kb, spec_view).map(|(base, _)| base)
}

/// WI-860 — THE OWNER of the witness criterion, over any carrier.
///
/// [`witness_dispatch_carrier`] and [`witness_dispatch_carrier_view`] are its two
/// term-side entry points; the `dispatch_carrier` builtin is the third caller and the
/// reason this flavour exists at all. A `SortProvidesInfo` fact's `spec` field reads as a
/// `TermId` through `fact_head_named_args` (the LOAD path) and as a `Value::Node`
/// OCCURRENCE when the resolver matches the same fact against a goal (the SLD path), so a
/// classifier reachable only from a `TermId` is reachable only from half its callers.
/// MEASURED: a first cut gated on `Value::Term` answered zero rows over 93 provisions,
/// and a second one that routed the SLD path through a decoder which DROPS non-term
/// bindings answered "self-provider" for every witness in the tree — both loading clean.
/// The agreement test in `wi860_default_provider_relations_test` is what showed each.
pub(crate) fn witness_dispatch_carrier_value(
    kb: &KnowledgeBase,
    spec: Symbol,
    provider: Symbol,
    spec_view: &Value,
) -> Option<(Value, Symbol)> {
    let (view, base) = provision_carrier_binding(kb, spec, spec_view)?;
    let carrier_canon = kb.canonical_sort_sym(base);
    // Provider IS the carrier ⇒ a fact / normal self-provider, not a witness.
    (kb.canonical_sort_sym(provider) != carrier_canon).then_some((view, carrier_canon))
}

/// WI-860 — one `anthill.reflect.SortProvidesInfo` fact as 058 §3.6's defaults substrate
/// reads it. NAMED rather than a triple, because [`Provision`]'s own `carrier` field
/// holds the `sort_ref` — i.e. the PROVIDER — and handing that misnomer out, or handing
/// out an unlabelled `(Symbol, Symbol, TermId)`, would leave the pairing to a doc comment
/// (WI-869's lesson: type the pairing).
pub(crate) struct ProvisionRow {
    /// The `sort_ref`: the providing sort for a `provides` clause, the DERIVED carrier
    /// for a namespace-level instance fact.
    pub provider: Symbol,
    /// The spec's base sort.
    pub spec: Symbol,
    /// The full `SortView` term the provision carries.
    pub spec_view: TermId,
}

/// WI-860 (058 §3.6) — do two carrier views describe any carrier IN COMMON? The
/// `one_default` check's criterion: `List[T = E]` and `List[T = Int64]` overlap and are
/// two defaults for one family, while `List[T = Int64]` and `List[T = String]` are
/// disjoint and coexist.
///
/// NOT [`unify_types`], and not because of the carrier: a type PARAMETER is not a logic
/// var in this substrate — `List[T = E]` stores `E` as a `Ref` to the param symbol — so
/// the unifier reads `E` and `Int64` as different, which is the opposite of what a
/// default row means by it. [`is_type_param_value`] is the established "abstract here"
/// reading (the dispatch matcher's candidate leniency), applied at every level.
///
/// ENROLLED IN THE BINDING-KEY RULE (WI-726/764/768/769/825/826): the per-param lookup is
/// [`binding_for_param`] under [`BindingKeyMatch::for_bases`], not a hand-rolled
/// short-name `find`. Lives HERE rather than in `kb::defaults` for that reason — the rule
/// and its base gate are this module's, and the enrollment list in `binding_for_param`'s
/// doc is only honest if a new walk joins it instead of spelling a seventh copy. A
/// label-only spelling would also miss the WI-726 pair (canonical `Relation.T` vs a
/// written bare `T`), so two colliding defaults keyed by different producers would
/// silently coexist.
///
/// The two shapes a carrier view takes are MEASURED, not assumed: over the stdlib, the
/// Rust bindings and WI-860's fixtures every carrier is either a bare name (`Ref(S)` or
/// the nullary `Fn{S}` a minted name term is — both occur, which is why the base is
/// compared rather than the term id) or an application `Fn{S, named}` with no positional
/// args. No carrier arrives `SortView`-wrapped, so no wrapper is peeled here.
///
/// An omitted binding means ANY (058 §3.4's omission-means-any, the reading
/// `check_sort_type_args` enforces), so a view binding fewer parameters is the more
/// general one and overlaps the other.
///
/// Structural, and deliberately WITHOUT a shared binding environment: `List[T = Pair[A =
/// E, B = E]]` and `List[T = Pair[A = Int64, B = String]]` read as overlapping where a
/// real unifier refuses them (one `E`, two values). That errs toward REFUSING a pair of
/// default marks, so the cost is deleting one mark on a carrier that repeats a parameter
/// — never a silent wrong answer. Stated rather than discovered.
pub(crate) fn carrier_views_overlap(kb: &KnowledgeBase, a: TermId, b: TermId) -> bool {
    if a == b {
        // Hash-consed: identical structure is one id.
        return true;
    }
    if is_type_param_value(kb, a) || is_type_param_value(kb, b) {
        return true;
    }
    let (Some((base_a, args_a)), Some((base_b, args_b))) =
        (carrier_view_parts(kb, a), carrier_view_parts(kb, b))
    else {
        return false;
    };
    // `for_bases` IS the base gate: `Label` exactly when the two bases are one canonical
    // sort, which is also the mode the per-param lookup must run in (two views of one
    // family may key one slot with the canonical param symbol and a bare last segment).
    let key_match = BindingKeyMatch::for_bases(kb, base_a, base_b);
    if !matches!(key_match, BindingKeyMatch::Label) {
        return false;
    }
    args_a.iter().all(
        |(param, va)| match binding_for_param(kb, &args_b, *param, key_match) {
            Some(vb) => carrier_views_overlap(kb, *va, *vb),
            None => true,
        },
    )
}

/// A carrier view as `(base sort, named bindings)` — [`parameterized_parts`] widened by
/// the BARE case, which that function answers `None` for (it requires named args, and a
/// bare carrier has none). Positional args are dropped rather than compared because a
/// carrier view has none; measured over the whole corpus at WI-860.
pub(super) fn carrier_view_parts(
    kb: &KnowledgeBase,
    t: TermId,
) -> Option<(Symbol, SmallVec<[(Symbol, TermId); 2]>)> {
    if let Some((base, _, named)) = parameterized_parts(kb, t) {
        return Some((base, named));
    }
    match kb.get_term(t) {
        Term::Ref(s) | Term::Ident(s) => Some((*s, SmallVec::new())),
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => Some((*functor, SmallVec::new())),
        _ => None,
    }
}

/// WI-860 — every provision, as [`ProvisionRow`]s.
///
/// A thin wrapper over [`collect_provisions`] so the defaults pass walks the provision
/// relation through THIS module's decoder rather than spelling a fourth one.
pub(crate) fn all_provisions(kb: &KnowledgeBase) -> Vec<ProvisionRow> {
    collect_provisions(kb)
        .into_iter()
        .map(|p| ProvisionRow {
            provider: p.carrier,
            spec: p.spec,
            spec_view: p.spec_view,
        })
        .collect()
}

//! Explicit obligations on rule carrier type variables. A carrier's type and
//! the spec instance it must provide are separate terms in the same frame.
use super::*;

pub(crate) const PROVIDER_CARRIER_TYPE_LABEL: &str = "carrier_type";

/// Check the obligations on an opened type variable without changing how any
/// nominal type is interpreted elsewhere in the comparison.
pub(crate) fn carrier_requirements_hold(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    carrier: VarId,
    ty: &Value,
) -> TypeBoundVerdict {
    // A requirement whose dictionary the clause was handed — a citation bound it when the
    // clause opened — is the caller's to decide, as an operation's `requires` is: the value's
    // own type is not asked it (`[]`'s open `List` has no `TypeValue`, the caller's
    // `List[T = Int64]` has).
    let requirements: Vec<TermId> = kb
        .type_var_provider_requirement_entries(carrier)
        .into_iter()
        .filter(|(_, dictionary, _)| subst.resolve_as_value(*dictionary).is_none())
        .map(|(instance, _, _)| instance)
        .collect();
    if requirements.is_empty() {
        return TypeBoundVerdict::Holds;
    }
    if type_is_undetermined(kb, ty) {
        return TypeBoundVerdict::Suspend;
    }
    let mut scope_subst = Substitution::with_parent(subst.clone());
    scope_subst.bind_value(kb, carrier, ty.clone());
    for instance in requirements {
        let instance = walk_type_deep_value(kb, &scope_subst, &Value::term(instance));
        let goal = match provider_requirement_goal(kb, subst, ty, &instance) {
            Ok(goal) => goal,
            Err(verdict) => return verdict,
        };
        // The empty scope's question, read through its memo, as the clause's read of the same
        // requirement is ([`resolve_in_empty_scope`]).
        match resolve_in_empty_scope(kb, &goal, DefaultRung::Consult) {
            ResolutionResult::Resolved(_) => {}
            ResolutionResult::NoMatch { .. } => return TypeBoundVerdict::Refuted,
            ResolutionResult::Ambiguous { .. } | ResolutionResult::Cyclic { .. } => {
                return TypeBoundVerdict::Suspend
            }
        }
    }
    TypeBoundVerdict::Holds
}

/// Read obligations before losing the carrier variable to a type substitution.
/// Citation inference may already have pinned a column, but that does not erase
/// the requirement attached to its original declared type variable.
pub(crate) fn carrier_requirements_in_type(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    declared: &Value,
) -> TypeBoundVerdict {
    let mut stack = vec![declared.clone()];
    let mut verdict = TypeBoundVerdict::Holds;
    while let Some(ty) = stack.pop() {
        if let ViewHead::Var(Var::Global(v)) = ty.head(kb) {
            let actual = walk_type_deep_value(kb, subst, &ty);
            match carrier_requirements_hold(kb, subst, v, &actual) {
                TypeBoundVerdict::Refuted => return TypeBoundVerdict::Refuted,
                TypeBoundVerdict::Suspend => verdict = TypeBoundVerdict::Suspend,
                TypeBoundVerdict::Holds => {}
            }
        } else {
            if let ViewHead::Functor { pos_arity, .. } = ty.head(kb) {
                for i in 0..pos_arity {
                    if let Some(child) = ty.pos_arg(kb, i) {
                        stack.push(child.to_value());
                    }
                }
            }
            for key in ty.named_keys(kb) {
                if let Some(child) = ty.named_arg(kb, key) {
                    stack.push(child.to_value());
                }
            }
        }
    }
    verdict
}

/// Build the same instance for static conformance and dictionary lookup. An
/// omitted sibling is read from the carrier's unique instantiated provision;
/// written siblings remain restrictions and are never overwritten.
pub(crate) fn provider_requirement_goal(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    ty: &Value,
    instance: &Value,
) -> Result<SortGoal, TypeBoundVerdict> {
    provider_requirement_goal_with_provider(kb, subst, ty, instance, None)
}

pub(crate) fn provider_requirement_goal_with_provider(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    ty: &Value,
    instance: &Value,
    provider: Option<Symbol>,
) -> Result<SortGoal, TypeBoundVerdict> {
    if type_is_undetermined(kb, ty) {
        return Err(TypeBoundVerdict::Suspend);
    }
    let Some(spec) = sort_functor_of_view(kb, instance) else {
        return Err(TypeBoundVerdict::Refuted);
    };
    let carrier_param = spec_carrier_param_or_sole(kb, spec);
    let mut written = requirement_bracket(kb, &instance);
    // A sibling written as a variable nothing has bound — `Sp[C = A, P = ?]`, `P = ?p` — says
    // nothing of the instance (`X[T = ?]` is `X`, WI-20261024-DK83Q; a variable is the
    // unwritten case, WI-20260922-QHDGC), so it is read off the provision as an omitted one
    // is. Kept as written, the goal held the variable and no provision's concrete binding
    // met it: the guard answered nothing.
    written.written.retain(|(key, value)| {
        carrier_param.is_some_and(|p| same_label(kb, p, *key))
            || !matches!(walk_type_deep_value(kb, subst, value).head(kb), ViewHead::Var(_))
    });
    let Some(WitnessGoal { mut goal, .. }) =
        anchor_sort_goal(kb, spec, std::slice::from_ref(ty), &written.written)
    else {
        return Err(TypeBoundVerdict::Suspend);
    };
    for (key, _) in &mut goal.bindings {
        if carrier_param.is_some_and(|p| same_label(kb, p, *key)) {
            if let Some((_, written_ty)) = written
                .written
                .iter()
                .find(|(k, _)| same_label(kb, *k, *key))
            {
                let actual = dealiased(kb, ty);
                let demanded = dealiased(kb, written_ty);
                if let (Some(a), Some(b)) = (
                    sort_functor_of_view(kb, &actual),
                    sort_functor_of_view(kb, &demanded),
                ) {
                    // A spec's carrier element is its actual type constructor,
                    // not an abstract spec that the actual type also provides.
                    if !same_sort_canonical(kb, a, b) {
                        return Err(TypeBoundVerdict::Refuted);
                    }
                }
                if !unify_types(kb, &mut Substitution::new(), &actual, &demanded) {
                    return Err(TypeBoundVerdict::Refuted);
                }
            }
        }
    }
    let omitted: Vec<Symbol> = goal
        .bindings
        .iter()
        .filter_map(|(key, _)| {
            (!carrier_param.is_some_and(|p| same_label(kb, p, *key))
                && !written
                    .written
                    .iter()
                    .any(|(k, _)| same_label(kb, *k, *key)))
            .then_some(*key)
        })
        .collect();
    if !omitted.is_empty() {
        let Some(base) = provider.or_else(|| sort_functor_of_view(kb, ty)) else {
            return Err(TypeBoundVerdict::Suspend);
        };
        let Some((view, _)) = subtype_provider_view(kb, base, spec) else {
            return Err(TypeBoundVerdict::Suspend);
        };
        let args = receiver_type_args(kb, ty);
        let (view, _) = provider_view_at_instance(kb, subst, base, &args, view);
        for key in omitted {
            let Some((_, value)) = view.iter().find(|(k, _)| same_label(kb, *k, key)) else {
                return Err(TypeBoundVerdict::Suspend);
            };
            let slot = goal
                .bindings
                .iter_mut()
                .find(|(k, _)| same_label(kb, *k, key))
                .expect("an omitted element belongs to the goal");
            slot.1 = value.clone();
        }
    }
    Ok(goal)
}

/// The type a `TypeValue` dictionary is the evidence of — the one walk `TypeValue.type_value`
/// reads its answer off (`eval::builtins::type_of_dictionary`) and a dictionary handed to a
/// rule's guard binds its carrier by. `impl` names the head, and the subs after the head's own
/// sort-level requirements carry one argument each, in declaration order. A pattern's open slot
/// (proposal 071 §1.6) is `open_slot`, which only the evaluator's error layer names. `Err` with
/// why where the layout does not fit, or a slot is met with no `open_slot` to give it.
pub(crate) fn type_of_type_value_dictionary(
    kb: &mut KnowledgeBase,
    dict: &crate::eval::dictionary::Dictionary,
    open_slot: Option<TermId>,
) -> Result<TermId, String> {
    let head = dict.impl_sort();
    if kb.minted_param(head) == Some(crate::kb::MintedParam::PatternSlot) {
        return open_slot.ok_or_else(|| "a pattern's open slot read with no error layer".to_string());
    }
    let arity = dict.arity();
    if arity == 0 {
        // `Ref(S)`, the bare sort's one term (`KnowledgeBase::make_sort_ref`): an `Fn` head
        // does not unify with it.
        return Ok(kb.make_sort_ref(head));
    }
    // The head's own type parameters in DECLARATION order — the order `type_value_derive`
    // emits the conditions in — after the carrier's own sort-level `requires`, which come
    // first in a provision's chain (`provider_dict_chain`): `Map requires Eq[T = K]` shifts
    // every condition by one.
    let params: Vec<String> = kb.type_params_of_sort(head);
    let base = provider_dict_entries(kb, head, None).len();
    if base + params.len() != arity {
        return Err(format!(
            "`{}` has {} type parameter(s) after {base} sort-level requirement(s), but its \
             dictionary carries {arity} sub-instance(s); `type_value_derive` and this reader \
             disagree about the layout",
            kb.qualified_name_of(head),
            params.len(),
        ));
    }
    let mut bindings: Vec<(Symbol, TermId)> = Vec::with_capacity(params.len());
    for (i, name) in params.iter().enumerate() {
        let sub = dict
            .sub(base + i)
            .ok_or_else(|| format!("dictionary sub {i} missing below arity {arity}"))?;
        let ty = type_of_type_value_dictionary(kb, &sub, open_slot)?;
        bindings.push((kb.intern(name), ty));
    }
    // Each argument keyed by its parameter's declared name, through the one canonical builder,
    // as a type written in value position is (`Interpreter::finish_sort_type`).
    let base_ref = kb.make_sort_ref(head);
    Ok(kb.make_parameterized_type(base_ref, &bindings))
}

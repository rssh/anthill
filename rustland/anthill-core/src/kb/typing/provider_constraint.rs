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
    let requirements = kb.type_var_provider_requirements(carrier).to_vec();
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
        let scope = ResolutionScope {
            available_requires: &[],
            sigma: None,
            selected: &[],
            sub_goal_requires: &[],
        };
        match resolve_with_rung(kb, &goal, &scope, DefaultRung::Consult) {
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
    let written = requirement_bracket(kb, &instance);
    let Some(WitnessGoal { mut goal, .. }) =
        anchor_sort_goal(kb, spec, std::slice::from_ref(ty), &written.written)
    else {
        return Err(TypeBoundVerdict::Suspend);
    };
    let carrier_param = spec_carrier_param_or_sole(kb, spec);
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

//! A body held to the guarded elements of its own effect row (kernel-language.md §5.5).
//!
//! `L :- g` in an operation's row says that after a call `L` is possible only where `g`
//! holds. The boundary's coverage check ([`undeclared_effects`]) reads a guarded element as
//! its label, so it cannot see where in the body `L` is incurred; the check is made at each
//! call instead, where Γ says what holds.

use super::*;

/// The elements of an operation's declared row that admit a label only under a guard,
/// beside those that admit one unconditionally: what each call in its body is held to
/// ([`hold_call_to_guarded_row`]). Read as the boundary's coverage check reads the row —
/// every projection eliminated, through the operation's rigidify and through aliases.
pub(crate) struct GuardedRow {
    op: Symbol,
    rigidify: Rc<Substitution>,
    unguarded: Vec<Value>,
    guarded: Vec<GuardedElement>,
}

struct GuardedElement {
    label: Value,
    /// `None` for a guard whose conjuncts cannot be read, which is then never shown to hold.
    conjuncts: Option<Vec<Value>>,
    /// The label as the row writes it, for the refusal.
    written: String,
}

impl GuardedRow {
    /// The row `effective_effects` of the operation `op`, or `None` where it holds no guarded
    /// element.
    pub(super) fn of(
        kb: &mut KnowledgeBase,
        op: Symbol,
        rigidify: &Rc<Substitution>,
        effective_effects: &[Value],
    ) -> Option<GuardedRow> {
        let guard_key = kb.intern("guard");
        let mut unguarded = Vec::new();
        let mut guarded = Vec::new();
        for e in effective_effects {
            if let Some(label) = guarded_effect_label(kb, e) {
                let conjuncts =
                    named_child_value(kb, e, guard_key).and_then(|g| guard_conjuncts(kb, &g));
                guarded.push(GuardedElement {
                    written: type_display_name_value(kb, &label),
                    label: in_body_vocabulary(kb, rigidify, &label),
                    conjuncts,
                });
                continue;
            }
            let Some((mut admitting, _absent)) = explode_declared_effect_row(kb, e) else {
                unguarded.push(in_body_vocabulary(kb, rigidify, e));
                continue;
            };
            // A row element flattens a guarded atom inside it to its label; one occurrence of
            // that label is the guarded atom's, as at a call's discharge.
            for (label, guard) in collect_guarded_atoms(kb, &Substitution::new(), e) {
                if let Some(at) = admitting
                    .iter()
                    .position(|a| views_structurally_equal(kb, a, &label))
                {
                    admitting.remove(at);
                }
                guarded.push(GuardedElement {
                    written: type_display_name_value(kb, &label),
                    label: in_body_vocabulary(kb, rigidify, &label),
                    conjuncts: guard_conjuncts(kb, &guard),
                });
            }
            for a in &admitting {
                unguarded.push(in_body_vocabulary(kb, rigidify, a));
            }
        }
        (!guarded.is_empty()).then(|| GuardedRow {
            op,
            rigidify: Rc::clone(rigidify),
            unguarded,
            guarded,
        })
    }
}

fn in_body_vocabulary(kb: &mut KnowledgeBase, rigidify: &Substitution, v: &Value) -> Value {
    let v = walk_type_deep_value(kb, rigidify, v);
    dealiased(kb, &v)
}

/// Does a row element with the label `declared` admit the incurred label `incurred`? As the
/// boundary's coverage check decides it: the same label, or an `Error` label a boundary at the
/// declared payload catches.
fn admits(
    kb: &mut KnowledgeBase,
    rigidify: &Substitution,
    declared: &Value,
    incurred: &Value,
) -> bool {
    views_structurally_equal(kb, incurred, declared)
        || error_label_admits(kb, rigidify, declared, incurred)
}

/// Hold the effects one call of an operation incurs (`kept`, each a label or a guarded atom of
/// the callee's row, after the call's own discharge) to the guarded elements of the enclosing
/// operation's row ([`hold_incurred`]), the callee's parameters substituted in its guards by
/// `sigma`.
#[allow(clippy::too_many_arguments)]
pub(super) fn hold_call_to_guarded_row(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    flow: &FlowEnv,
    sigma: &HashMap<Symbol, TermId>,
    kept: &[Value],
    callee: Symbol,
    span: Option<Span>,
) -> Result<(), TypeError> {
    if env.guarded_row().is_none() {
        return Ok(());
    }
    let guard_key = kb.intern("guard");
    let incurred: Vec<(Value, Option<Vec<Value>>)> = kept
        .iter()
        .map(|effect| match guarded_effect_label(kb, effect) {
            Some(label) => {
                let guard =
                    named_child_value(kb, effect, guard_key).and_then(|g| guard_conjuncts(kb, &g));
                (label, guard)
            }
            None => (effect.clone(), None),
        })
        .collect();
    hold_incurred(kb, env, flow, sigma, &incurred, callee, span)
}

/// Hold the application of a function value `f` (`callee`, of type `fn_type`) to the guarded
/// elements of the enclosing operation's row ([`hold_incurred`]). `labels` is the row the
/// application incurs, flattened; a label a guarded element of the function's row flattened to
/// keeps that guard, its binders — the places of a callback parameter — substituted by the
/// arguments.
#[allow(clippy::too_many_arguments)]
pub(super) fn hold_application_to_guarded_row(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    flow: &FlowEnv,
    fn_type: &Value,
    labels: &[Value],
    callee: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    span: Option<Span>,
) -> Result<(), TypeError> {
    if env.guarded_row().is_none() {
        return Ok(());
    }
    let mut incurred: Vec<(Value, Option<Vec<Value>>)> =
        labels.iter().map(|l| (l.clone(), None)).collect();
    let row = arrow_parts(kb, fn_type).and_then(|(_, _, row)| row);
    for (label, guard) in row
        .map(|row| collect_guarded_atoms(kb, &Substitution::new(), &row))
        .unwrap_or_default()
    {
        if let Some((_, slot)) = incurred
            .iter_mut()
            .find(|(l, g)| g.is_none() && views_structurally_equal(kb, l, &label))
        {
            *slot = guard_conjuncts(kb, &guard);
        }
    }
    // A guard in a function's row names a binder as it is written (`eq(x, 0)` reads `x`).
    let binders: Vec<Symbol> = kb
        .symbols
        .arg_places(callee)
        .to_vec()
        .into_iter()
        .map(|place| {
            let name = short_name_of(kb.local_name_of(place)).to_owned();
            kb.intern(&name)
        })
        .collect();
    let mut sigma: HashMap<Symbol, TermId> = HashMap::new();
    // Each positional argument fills the slot the call's ranking gives it.
    let slots = positional_param_indices(kb, &binders, pos_args.len(), named_args);
    for (arg, slot) in pos_args.iter().zip(slots) {
        if let Some(binder) = slot.and_then(|p| binders.get(p)) {
            if let Some(t) = guard_arg_term(kb, arg) {
                sigma.insert(*binder, t);
            }
        }
    }
    for (label, arg) in named_args {
        let name = short_name_of(kb.local_name_of(*label)).to_owned();
        let binder = kb.intern(&name);
        if binders.contains(&binder) {
            if let Some(t) = guard_arg_term(kb, arg) {
                sigma.insert(binder, t);
            }
        }
    }
    hold_incurred(kb, env, flow, &sigma, &incurred, callee, span)
}

/// Where the enclosing operation's row admits a label `L` a call incurs only under guards, one
/// of them must be proved at the call: from Γ (`flow` — branch conditions, match arms, the
/// knowledge base's laws), with the callee's own guard for `L` as a hypothesis, its parameters
/// substituted by `sigma`. A write through a local name is read as the memory it reaches at the
/// call (§5.6). Otherwise the call is refused, naming `L` and the guard.
fn hold_incurred(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    flow: &FlowEnv,
    sigma: &HashMap<Symbol, TermId>,
    incurred: &[(Value, Option<Vec<Value>>)],
    callee: Symbol,
    span: Option<Span>,
) -> Result<(), TypeError> {
    let Some(row) = env.guarded_row() else {
        return Ok(());
    };
    let row = Rc::clone(row);
    for (label, own_guard) in incurred {
        let reached = charge_local_writes(
            kb,
            env,
            &flow.branch,
            ScopeEnd::Arm,
            0,
            std::slice::from_ref(label),
        );
        for charged in reached {
            let key = in_body_vocabulary(kb, &row.rigidify, &charged);
            if row
                .unguarded
                .iter()
                .any(|d| admits(kb, &row.rigidify, d, &key))
            {
                continue;
            }
            let held: Vec<&GuardedElement> = row
                .guarded
                .iter()
                .filter(|g| admits(kb, &row.rigidify, &g.label, &key))
                .collect();
            // A label no element admits is the boundary's to report.
            let Some(first) = held.first() else {
                continue;
            };
            let mut at_call = flow.clone();
            for conjunct in own_guard.iter().flatten() {
                if let Some(hypothesis) = guard_at_call(kb, conjunct, sigma) {
                    at_call = at_call.assume(kb, hypothesis);
                }
            }
            let shown = held.iter().any(|g| {
                g.conjuncts.as_ref().is_some_and(|conjuncts| {
                    conjuncts.iter().all(|c| {
                        let goal = goal_form(kb, c.clone());
                        prove_from_gamma(kb, &at_call, &goal)
                    })
                })
            });
            if shown {
                continue;
            }
            let refusal = guarded_row_refusal(kb, row.op, first, callee, &charged, span);
            if let Some(err) = env.defer_precondition(refusal) {
                return Err(err);
            }
        }
    }
    Ok(())
}

/// A conjunct of the callee's own guard as it reads at the call, `sigma` substituted — or
/// `None` where it names a parameter `sigma` binds no argument for. That parameter is the
/// callee's, and it is the caller's own where the call is recursive: `f(if c then 0 else 1)`
/// in `f(n) effects { E :- eq(n, 0) }` would assume `eq(n, 0)` of the caller's `n`.
fn guard_at_call(
    kb: &mut KnowledgeBase,
    conjunct: &Value,
    sigma: &HashMap<Symbol, TermId>,
) -> Option<Value> {
    let placeholder = kb.alloc(Term::Const(Literal::Bool(true)));
    let bound: HashMap<Symbol, TermId> = sigma.keys().map(|p| (*p, placeholder)).collect();
    let probe = substitute_ref_terms(kb, conjunct, &bound);
    if kb.value_has_open_world_ref(&probe, &Substitution::new()) {
        return None;
    }
    Some(substitute_ref_terms(kb, conjunct, sigma))
}

fn guarded_row_refusal(
    kb: &KnowledgeBase,
    op: Symbol,
    element: &GuardedElement,
    callee: Symbol,
    label: &Value,
    span: Option<Span>,
) -> TypeError {
    let label = type_display_name_value(kb, label);
    let guard = guard_display(kb, element.conjuncts.as_deref());
    TypeError::Other {
        site: TypeError::here(),
        span,
        context: TypeErrorContext::OperationEffects { op_name: op },
        expected: format!(
            "`{label}` only where `{guard}` holds, as the row declares `{} :- {guard}`",
            element.written
        ),
        actual: format!(
            "the call of `{}` incurs `{label}` where nothing shows `{guard}`",
            short_name_of(kb.local_name_of(callee))
        ),
    }
}

fn guard_display(kb: &KnowledgeBase, conjuncts: Option<&[Value]>) -> String {
    match conjuncts {
        Some(conjuncts) => conjuncts
            .iter()
            .map(|c| format_precondition_clause(kb, c))
            .collect::<Vec<_>>()
            .join(", "),
        None => "a guard that cannot be read".to_string(),
    }
}

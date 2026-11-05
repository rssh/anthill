//! Rule-body requirement checks: find-dictionary grounding, spec-op requirements,
//! eq-override backing, covered calls.

use super::*;

/// The operation an application calls, where `call` is one.
fn call_functor(call: &NodeOccurrence) -> Option<Symbol> {
    match call.as_expr() {
        Some(Expr::Apply { functor, .. }) => Some(*functor),
        _ => None,
    }
}

/// Compile carrier obligations into reads of their separate dictionary slots.
/// Written dictionary calls have already been woven and retain their selection.
pub(super) fn install_rule_provider_dictionaries(kb: &mut KnowledgeBase) -> Vec<TypeError> {
    let mut errors = Vec::new();
    let Some(fd) = find_dictionary_symbol(kb) else {
        return errors;
    };
    let pass = kb.register_pass("anthill.kb.passes.carrier_provider_dictionary");
    let out_label = kb.intern("out");
    let carrier_label = kb.intern(PROVIDER_CARRIER_TYPE_LABEL);
    for rid in kb.live_rule_ids() {
        let requirements = kb.rule_provider_requirements(rid).to_vec();
        if requirements.is_empty() {
            continue;
        }
        let equation = kb.is_directional_equation(rid);
        let body = if equation {
            vec![kb
                .rule_equation_rhs_node(rid)
                .expect("a source equation retains its RHS")]
        } else {
            kb.rule_body_nodes(rid).to_vec()
        };
        if body.iter().any(|n| n.synthesized_by() == Some(pass)) {
            continue;
        }
        let anchor = body.first().cloned().unwrap_or_else(|| {
            NodeOccurrence::new_expr(
                Expr::Bottom,
                kb.rule_head_span(rid)
                    .expect("a typed source clause has a span"),
                Some(kb.rule_domain(rid)),
            )
        });
        let mut goals = Vec::new();
        let mut targets: Vec<WeaveTarget> = Vec::new();
        // The instance each target's dictionary is a requirement at, and its name.
        let mut target_instances: Vec<(TermId, Option<Symbol>)> = Vec::new();
        for requirement in requirements {
            let instance = requirement.instance;
            let spec = sort_functor_of_view(kb, &Value::term(instance))
                .expect("provider obligation names a spec");
            let out = NodeOccurrence::new_expr(
                Expr::Var(Var::DeBruijn(requirement.dictionary)),
                anchor.span,
                anchor.owner,
            );
            let at: Vec<_> = kb.rule_type_bounds(rid).iter().filter_map(|(v,t)|
                matches!(t.head(kb), ViewHead::Var(Var::DeBruijn(i)) if i == requirement.carrier)
                    .then(|| NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(*v)), anchor.span, anchor.owner))).collect();
            for call in collect_covered_calls(kb, &body, kb.canonical_sort_sym(spec), &at) {
                if let Some(at) = targets
                    .iter()
                    .position(|(previous, _, _)| Rc::ptr_eq(previous, &call))
                {
                    // Two requirements of one spec at one type, written twice: either is the
                    // call's, as in an operation's body under two equal `requires` lines
                    // (060.1 §8.5). The first stands.
                    let (first_instance, first_name) = target_instances[at];
                    if first_instance == instance && first_name.is_none() && requirement.name.is_none() {
                        continue;
                    }
                    // Two names are two dictionaries (§8.6), and the call says neither, as an
                    // operation's body call under two named `requires` lines is refused.
                    if let (Some(first), Some(second)) = (first_name, requirement.name) {
                        let member = kb.local_name_of(call_functor(&call).unwrap_or(spec)).to_string();
                        errors.push(TypeError::Other {
                            site: TypeError::here(),
                            span: Some(call.span.span),
                            context: TypeErrorContext::Rule {
                                name: spec,
                                field: RuleField::Body,
                            },
                            expected: "a call that names the requirement it reads".into(),
                            actual: format!(
                                "two requirements of the clause cover it, `{f}` and `{s}`, and \
                                 the call names neither: write `{f}.{member}(…)` or \
                                 `{s}.{member}(…)`",
                                f = kb.local_name_of(first),
                                s = kb.local_name_of(second),
                            ),
                        });
                        continue;
                    }
                    errors.push(TypeError::Other {
                        site: TypeError::here(),
                        span: Some(call.span.span),
                        context: TypeErrorContext::Rule {
                            name: spec,
                            field: RuleField::Body,
                        },
                        expected: "one carrier requirement to select this call's dictionary".into(),
                        actual: {
                            let member = kb.local_name_of(call_functor(&call).unwrap_or(spec)).to_string();
                            format!(
                                "the call is covered by distinct carrier requirements: name the \
                                 one it reads, `require s: {spec}[…]`, and call `s.{member}(…)`",
                                spec = short_name_of(kb.qualified_name_of(spec)),
                            )
                        },
                    });
                } else {
                    targets.push((call, vec![out.clone()], None));
                    target_instances.push((instance, requirement.name));
                }
            }
            let spec_node = NodeOccurrence::new_expr(
                Expr::Spliced(Value::term(kb.alloc(Term::Ref(spec)))),
                anchor.span,
                anchor.owner,
            );
            let mut read_args = vec![
                NodeOccurrence::new_expr(Expr::Spliced(Value::term(instance)), anchor.span, anchor.owner),
                spec_node,
                NodeOccurrence::new_expr(
                    Expr::Var(Var::DeBruijn(requirement.carrier)),
                    anchor.span,
                    anchor.owner,
                ),
            ];
            // The clause's other type parameters the instance names at elements (`B = U` of
            // `Conv[A = X, B = U]`): the read waits until each is known, as it does for its
            // carrier, so the element selects the instance.
            read_args.extend(
                guard_element_vars(kb, rid, instance, requirement.carrier)
                    .into_iter()
                    .map(|v| NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(v)), anchor.span, anchor.owner)),
            );
            goals.push(NodeOccurrence::synthesized_expr(
                Expr::Apply {
                    recv_type: None,
                    functor: fd,
                    pos_args: read_args,
                    named_args: vec![
                        (out_label, out),
                        (
                            carrier_label,
                            NodeOccurrence::new_expr(
                                Expr::Const(Literal::Bool(true)),
                                anchor.span,
                                anchor.owner,
                            ),
                        ),
                    ],
                    type_args: Vec::new(),
                },
                anchor.clone(),
                pass,
                anchor.owner,
            ));
        }
        let mut reached = vec![false; targets.len()];
        let body: Vec<_> = body
            .iter()
            .map(|n| weave_calls(n, &targets, &mut reached))
            .collect();
        assert!(
            reached.iter().all(|r| *r),
            "every covered call belongs to the clause body"
        );
        if equation {
            let rhs = body.into_iter().next().expect("an equation has one RHS");
            kb.replace_closed_rule_equation_rhs_node(rid, rhs);
        } else {
            kb.set_rule_body_nodes(rid, body);
            kb.prepend_generated_body_goals(rid, goals);
        }
    }
    errors
}

/// The frame slots of clause `rid`'s declared type parameters that `instance` names at an
/// element, other than its `carrier` — whether a column is typed at the parameter itself or
/// only around it (`?us: List[T = U]`).
pub(super) fn guard_element_vars(kb: &KnowledgeBase, rid: RuleId, instance: TermId, carrier: u32) -> Vec<u32> {
    let params: Vec<u32> = kb
        .rule_type_params(rid)
        .iter()
        .map(|(_, slot)| *slot)
        .filter(|slot| *slot != carrier)
        .collect();
    let mut found: Vec<u32> = Vec::new();
    if let Term::Fn { named_args, .. } = kb.get_term(instance) {
        for (_, value) in named_args.iter() {
            if let Term::Var(Var::DeBruijn(t)) = kb.get_term(*value) {
                if params.contains(t) && !found.contains(t) {
                    found.push(*t);
                }
            }
        }
    }
    found
}

/// The synthesizing pass that owns every INFERRED requirement read — the provenance stamp,
/// and with it both the idempotence test of [`infer_rule_body_requirements`] and the
/// line between a read the author WROTE and one the typer inferred, which the two static
/// checks below ([`check_rule_body_requirements`], [`check_rule_body_operation_requires`])
/// must keep drawing: an inferred read is not the author acknowledging an obligation.
pub(crate) fn inferred_requirement_pass(kb: &mut KnowledgeBase) -> crate::kb::occurrence::PassId {
    kb.register_pass(INFERRED_REQUIREMENT_PASS)
}

const INFERRED_REQUIREMENT_PASS: &str = "anthill.kb.passes.inferred_requirement";

/// The pass of the `and(read, …, goal)` that puts a read beside a goal in a connective's slot
/// ([`place_nested_reads`]). Not the read's own pass: the conjunction is no read, and a reader
/// that skips a read ([`is_inferred_requirement_read`]) would skip the goal inside it.
const INFERRED_CONJUNCTION_PASS: &str = "anthill.kb.passes.inferred_requirement_conjunction";

/// The pass that marks a woven call carrying the SLOTS of its callee's chain, one per entry —
/// the clause's conditions for an operation's `requires` — rather than one dictionary its
/// member is dispatched through ([`weave_calls`]).
pub(crate) fn woven_slots_pass(kb: &mut KnowledgeBase) -> crate::kb::occurrence::PassId {
    kb.register_pass(WOVEN_SLOTS_PASS)
}

const WOVEN_SLOTS_PASS: &str = "anthill.kb.passes.woven_slots";

/// Does this woven call carry its callee's slots ([`woven_slots_pass`])? Read on a shared
/// borrow, by the pass name's intern entry, as [`is_inferred_requirement_read`] reads its own.
pub(crate) fn is_woven_slots_call(kb: &KnowledgeBase, node: &NodeOccurrence) -> bool {
    node.synthesized_by().is_some_and(|by| {
        kb.symbols
            .lookup(WOVEN_SLOTS_PASS)
            .is_some_and(|s| crate::kb::occurrence::PassId::from_symbol(s) == by)
    })
}

/// Did [`infer_rule_body_requirements`] synthesize this body goal? The read-only face of
/// [`inferred_requirement_pass`], for the checks that run on a shared borrow.
///
/// The pass name is looked up in the symbol table's INTERN map (`lookup`), which is where
/// `register_pass` puts it — not through `try_resolve_symbol`, which searches DECLARED
/// qualified names and never finds a pass: MEASURED, that spelling answered `false` for
/// every inferred read, so each one counted as the author's declaration and silenced
/// NR6FJ's refusal of a slot nothing can fill.
pub fn is_inferred_requirement_read(kb: &KnowledgeBase, node: &NodeOccurrence) -> bool {
    node.synthesized_by().is_some_and(|by| {
        kb.symbols
            .lookup(INFERRED_REQUIREMENT_PASS)
            .is_some_and(|s| crate::kb::occurrence::PassId::from_symbol(s) == by)
    })
}

/// WI-20260925-P7VP4 — A RULE-BODY CALL'S REQUIREMENT BECOMES A CONDITION OF THE CLAUSE
/// (`docs/design/requirement-channel.md` §5, "The call site drives it; `require[X]` is
/// only the explicit form"). For a call to a spec operation whose carrier is not known at
/// load, the clause gets the read its author would have written —
///
/// ```text
///   Desc.describe(?x, ?r)   ⇒   find_dictionary(Desc, Desc.describe, ?x, out: ?d),
///                                apply_within(fn = Desc.describe, args = (?x, ?r),
///                                             requirements = [?d])
/// ```
///
/// — immediately before the goal holding the call, with the call woven to dispatch
/// through it. The read is an ordinary one: a citation routes the caller's dictionary to
/// it (060-implementation §7.3, S2) and an uncited clause derives it from the carrier's
/// value, as value-directed dispatch did. So what inference changes is WHO MAY SUPPLY the
/// instance; for a clause no caller hands one to, the answers are the ones value dispatch
/// gives — a goal-position call whose arguments are not yet ground waits either way since
/// WI-20260926-CYNPE, measured for a spec-op goal and a slot goal
/// (`wi_p7vp4_rule_body_requirements_test`'s two delay rows). Decided by the user,
/// 2026-09-25: INFER, rather than refuse the clause until the author restates it.
///
/// WHERE A CALL GETS ONE: the read runs immediately before the goal holding the call — a body
/// goal, or a goal in a connective's proved slot (a branch, a negand, a quantifier's body, a
/// discharge's consequent), beside which it is placed, so a variable bound in that scope alone
/// is bound when the read runs. The walk reaches a call in the goal's value positions through
/// the argument lists of calls and data constructors, and under a lambda, `let`, `match` or
/// `if` ([`demand_walk_enters`]): the form runs with the dictionaries its goal's reads bound,
/// and a lambda's closure keeps them. A read every call of which is under a form is labelled
/// `in_form` ([`REQUIREMENT_IN_FORM_LABEL`]): where no provider is at the carrier it binds the
/// absence instead of failing, so a branch the form does not take costs the clause nothing. A
/// call naming a form's own binder is not the clause's to supply
/// ([`TypingEnv::clause_supplies_requirements`]) and gets none.
///
/// WHICH CALLS GET ONE is the typer's decision, read here and not made again
/// (requirement-channel.md §5.2): a call the typer leaves to its clause carries a
/// [`ClauseCondition`] — the dictionary of the spec it is dispatched through, or the slots of
/// its chain — and the typer refuses, pins or leaves alone every other. What is declined here is
/// the weave's own business:
///   * a spec the author already wrote a `require` for in this clause — that read covers its
///     calls exactly as it did (WI-1040);
///   * a callee with no reader for a woven call ([`collect_covered_calls`]' first gate), and a
///     call whose arguments do not align to its parameters, the typer's to refuse.
///
/// ONE READ PER CARRIER: calls sharing their carrier arguments share one dictionary, as
/// one written `require` covers every call at its carrier; calls at different carriers
/// get one each, since nothing says they are one instance.
pub(super) fn infer_rule_body_requirements(
    kb: &mut KnowledgeBase,
    // Calls refused already, by their clause and span: one call gets one diagnosis.
    refused_calls: &[(RuleId, Span)],
) -> Vec<(TypeError, Option<crate::span::SourceId>)> {
    let mut refused = Vec::new();
    let Some(fd_sym) = find_dictionary_symbol(kb) else {
        return refused; // no `find_dictionary` — no clause can hold a read
    };
    let pass = inferred_requirement_pass(kb);
    let slots_pass = woven_slots_pass(kb);
    let conjunction_pass = kb.register_pass(INFERRED_CONJUNCTION_PASS);
    let labels = ReadLabels {
        in_form: kb.intern(REQUIREMENT_IN_FORM_LABEL),
        out: kb.intern(REQUIREMENT_OUT_LABEL),
        slot: kb.intern(REQUIREMENT_SLOT_LABEL),
        dict: kb.intern("dict"),
    };
    for rid in kb.live_rule_ids() {
        // An EQUATION is no clause whose body runs as goals: an untagged one is an inert
        // law (`rule isEmpty(?s) <=> eq(length(?s), 0)`, which this pass wove before it
        // was excluded), and a guarded one's guard is run by the rewriter at match time,
        // which binds no read.
        if kb.is_fact(rid) || kb.has_equational_head(rid) {
            continue;
        }
        let body: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
        // IDEMPOTENT by provenance: the typer is not guaranteed to run once per KB. A read
        // may stand in a connective's goal slot as well as at the top.
        if clause_requirement_reads(kb, fd_sym, &body)
            .iter()
            .any(|n| n.synthesized_by() == Some(pass))
        {
            continue;
        }
        let mut written: SmallVec<[Symbol; 2]> = SmallVec::new();
        for node in &body {
            collect_find_dictionary_bases(kb, node, fd_sym, &mut written);
        }
        // The goals a read can stand before: the body's own, and every goal in a connective's
        // PROVED slot beneath them — an `|` / `&` branch, a negand, a quantifier's body, a
        // discharge's consequent ([`nested_goals`]). Sites `0..body.len()` are the body's goals,
        // in order; the rest are nested ones.
        let mut sites: Vec<Rc<NodeOccurrence>> = body.clone();
        for goal in &body {
            nested_goals(kb, goal, &mut sites);
        }
        // Per SPEC-OP demand `(site, the demand)`, and per SLOT demand `(site, the call, its
        // arguments, its callee's chain)`, in site order.
        let mut demands: Vec<(usize, SpecDemand)> = Vec::new();
        let mut slot_calls: Vec<(usize, SlotDemand)> = Vec::new();
        for (gi, goal) in sites.iter().enumerate() {
            // `(node, is it the goal itself, is it under a form)` — a call under a `let`,
            // `match`, `if` or `lambda` is run by the evaluator inside that form, where only
            // a slot its read has bound reaches it.
            let mut stack: Vec<(Rc<NodeOccurrence>, bool, bool)> = vec![(Rc::clone(goal), true, false)];
            let mut found: Vec<SpecDemand> = Vec::new();
            let mut found_slots: Vec<SlotDemand> = Vec::new();
            while let Some((o, top, in_form)) = stack.pop() {
                let Some(expr) = o.as_expr() else { continue };
                if top || demand_walk_enters(expr) {
                    let under_form = in_form
                        || matches!(
                            expr,
                            Expr::Let { .. } | Expr::Match { .. } | Expr::If { .. } | Expr::Lambda { .. }
                        );
                    let mut children: SmallVec<[Rc<NodeOccurrence>; 8]> = SmallVec::new();
                    for_each_child(expr, |c| children.push(Rc::clone(c)));
                    let pos = if top {
                        BodyPos::Goal(GoalCommit::Top)
                    } else {
                        BodyPos::Value
                    };
                    let positions = child_body_positions(kb, expr, pos, children.len());
                    stack.extend(
                        children
                            .into_iter()
                            .zip(positions)
                            .filter(|(_, p)| *p == BodyPos::Value)
                            .map(|(c, _)| (c, false, under_form)),
                    );
                }
                let Expr::Apply {
                    functor,
                    pos_args,
                    named_args,
                    ..
                } = expr
                else {
                    continue;
                };
                // A call AT GOAL POSITION is woven only where a reader reads it woven
                // ([`woven_goal_has_reader`]).
                if top && !woven_goal_has_reader(kb, &o, *functor, pos_args, named_args) {
                    continue;
                }
                if let Some(mut demand) =
                    inferred_demand(kb, &o, *functor, pos_args, named_args, &written)
                {
                    demand.in_form = in_form;
                    found.push(demand);
                } else if let Some(mut demand) =
                    inferred_slot_demand(kb, &o, *functor, pos_args, named_args)
                {
                    demand.in_form = in_form;
                    found_slots.push(demand);
                }
            }
            // The walk pops children first; restore SOURCE order within the goal so the
            // witness of a shared read is the call written first.
            found.sort_by_key(|d| d.call.call.span.span.start);
            found_slots.sort_by_key(|d| d.call.call.span.span.start);
            demands.extend(found.into_iter().map(|d| (gi, d)));
            slot_calls.extend(found_slots.into_iter().map(|d| (gi, d)));
        }
        if demands.is_empty() && slot_calls.is_empty() {
            continue;
        }
        // Group by (spec, carrier arguments); the first call of a group is its witness. The
        // body's own goals share a read across goals, which runs before the first; a nested
        // goal's reads are its own, standing beside it in its slot, where the variables it
        // reads are bound.
        let top = body.len();
        // 060.1 §1 — a call at a type parameter the clause declares a guard of the spec at is
        // dispatched through that guard's dictionary, as one at a column typed by it is: `?h`
        // of `?l <=> cons(?h, ?t)` under `rule evenS[E](?l: List[T = E]) :- WeakOrd[T = E]`
        // is an `E`. It takes no read of its own.
        let guards: Vec<(Symbol, u32, Rc<NodeOccurrence>)> = if kb.rule_type_params(rid).is_empty() {
            Vec::new()
        } else {
            clause_requirement_reads(kb, fd_sym, &body)
                .iter()
                .filter_map(|read| {
                    let (spec, carrier, _) = guard_read_parts(kb, read)?;
                    let out = requirement_read_out(kb, fd_sym, read)?;
                    Some((spec, carrier, Rc::clone(out)))
                })
                .collect()
        };
        // A clause whose guard the loader refused is refused for it, and what it lacks follows.
        let refused_load = kb.has_a_refused_guard(rid);
        let mut guarded: Vec<WeaveTarget> = Vec::new();
        let mut groups: Vec<(usize, SpecDemand, Vec<Rc<NodeOccurrence>>)> = Vec::new();
        for (gi, demand) in demands {
            if let Some(out) = declared_guard_of(kb, rid, &guards, &demand) {
                guarded.push((demand.call.call, vec![out], None));
                continue;
            }
            // A receiver bracket that writes the spec's carrier at a concrete type fixes the
            // instance at the call (`FiniteCollection[C = List[T = String]].size(?ls, ?n)`), as
            // an argument at a concrete type does.
            let fixed_at_the_call = call_recv_type_of(&demand.call.call).cloned().is_some_and(|instance| {
                spec_carrier_param_or_sole(kb, kb.canonical_sort_sym(demand.spec))
                    .and_then(|key| spec_binding_value(kb, &instance, kb.local_name_of(key)))
                    .is_some_and(|carrier| instance_is_concrete(kb, &carrier))
            });
            // A carrier typed at the spec itself — a spec that receives on itself, `size(s:
            // Sp)` — is dispatched by its value's sort, as an operation's parameter of that type
            // is (`operation viaSp(s: Sp) -> Int64 = Sp.dflt(s)` declares nothing): there is no
            // type parameter to declare it at.
            let typed_at_the_spec = demand.carriers.first().and_then(|c| c.inferred_type()).is_some_and(|ty| {
                sort_functor_of_view(kb, &ty).is_some_and(|s| same_sort_canonical(kb, s, demand.spec))
            });
            if !demand.of_the_sort
                && !fixed_at_the_call
                && !typed_at_the_spec
                && !clause_sort_supplies(kb, rid, demand.spec)
                && !declared_guard_requires(kb, rid, &guards, &demand)
                && !carried_by_a_named_slot(kb, rid, &demand)
                && demand
                    .carriers
                    .first()
                    .and_then(|c| c.inferred_type())
                    .is_some_and(|at| type_reaches_the_head(kb, rid, &at))
            {
                if !refused_load && !refused_calls.contains(&(rid, demand.call.call.span.span)) {
                    refused.push(undeclared_requirement(kb, rid, &demand.call, demand.spec));
                }
                continue;
            }
            let same = groups.iter_mut().find(|(g, w, _)| {
                (gi < top && *g < top || *g == gi)
                    && w.spec == demand.spec
                    && w.carriers.len() == demand.carriers.len()
                    && w.carriers
                        .iter()
                        .zip(&demand.carriers)
                        .all(|(a, b)| views_structurally_equal(kb, a, b))
            });
            match same {
                Some((_, w, calls)) => {
                    w.in_form &= demand.in_form;
                    calls.push(demand.call.call)
                }
                None => {
                    let call = Rc::clone(&demand.call.call);
                    groups.push((gi, demand, vec![call]));
                }
            }
        }
        let mut reads_before: Vec<Vec<Rc<NodeOccurrence>>> = vec![Vec::new(); sites.len()];
        let mut targets: Vec<WeaveTarget> = guarded;
        for (gi, witness, calls) in groups {
            let (read, out) = inferred_read(
                kb,
                rid,
                fd_sym,
                pass,
                &labels,
                witness.spec,
                &witness.call,
                None,
                witness.in_form,
            );
            reads_before[gi].push(read);
            for call in calls {
                targets.push((call, vec![Rc::clone(&out)], None));
            }
        }
        // A SLOT demand gets one read per slot of the callee's chain, and the call carries
        // all of them, in chain order — the layout `call_op_bridged` reads them back in.
        for (gi, demand) in slot_calls {
            // 060.1 §1 — a slot at a type parameter the clause declares a guard of its spec at
            // is filled by that guard's dictionary; one the callee states at a concrete
            // instance, or one the clause's sort supplies, takes a read of its own; any other,
            // at a type the call's arguments give, is the clause's refusal.
            let entries = op_dict_entries(kb, demand.call.functor).entries().to_vec();
            let routes: Vec<SlotRoute> = entries
                .iter()
                .map(|entry| slot_route(kb, rid, &guards, &demand.call, entry))
                .collect();
            if let Some(entry) = entries
                .iter()
                .zip(&routes)
                .find(|(_, r)| matches!(r, SlotRoute::Undeclared))
                .map(|(e, _)| e)
            {
                if !refused_load && !refused_calls.contains(&(rid, demand.call.call.span.span)) {
                    refused.push(undeclared_requirement(kb, rid, &demand.call, entry.required_sort));
                }
                continue;
            }
            let mut outs: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(demand.chain.len());
            for (k, spec) in demand.chain.iter().enumerate() {
                if let Some(SlotRoute::Guard(out)) = routes.get(k) {
                    outs.push(Rc::clone(out));
                    continue;
                }
                let (read, out) = inferred_read(
                    kb,
                    rid,
                    fd_sym,
                    pass,
                    &labels,
                    *spec,
                    &demand.call,
                    Some(k),
                    demand.in_form,
                );
                reads_before[gi].push(read);
                outs.push(out);
            }
            targets.push((demand.call.call, outs, Some(slots_pass)));
        }
        // ONE pass over the ORIGINAL body, every target matched by identity there. Weaving
        // call after call instead lost any call whose subtree an earlier weave had rebuilt —
        // an outer call around a woven inner one — which `reassemble` hands back as a NEW
        // node the later identity match cannot find.
        //
        // A nested goal's reads are placed first, rebuilding the connectives above it
        // ([`place_nested_reads`]); the rebuild keeps every other node, so the weave below
        // still finds each call by identity.
        let nested: Vec<(Rc<NodeOccurrence>, Vec<Rc<NodeOccurrence>>)> = sites[top..]
            .iter()
            .cloned()
            .zip(reads_before.split_off(top))
            .filter(|(_, reads)| !reads.is_empty())
            .collect();
        let placed: Vec<Rc<NodeOccurrence>> = if nested.is_empty() {
            body.clone()
        } else {
            let and_sym = kb
                .try_resolve_symbol("anthill.kernel.and")
                .expect("a clause with a connective's goal slot has the kernel's `and`");
            body.iter()
                .map(|g| place_nested_reads(kb, g, &nested, and_sym, conjunction_pass))
                .collect()
        };
        let mut reached = vec![false; targets.len()];
        let new_body: Vec<Rc<NodeOccurrence>> =
            placed.iter().map(|g| weave_calls(g, &targets, &mut reached)).collect();
        debug_assert!(
            reached.iter().all(|r| *r),
            "P7VP4: an inferred demand's call was not found in its body"
        );
        let mut body_out: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(new_body.len() + 2);
        for (goal, reads) in new_body.into_iter().zip(reads_before) {
            body_out.extend(reads);
            body_out.push(goal);
        }
        kb.set_rule_body_nodes(rid, body_out);
    }
    refused
}

/// 060.1 §8.2 and §3 — does the sort clause `rid` is written in supply `spec` with nothing
/// declared: the spec itself, whose laws read it at its own parameter, or a sort that
/// requires it, whose rules read its requirement as its operations do?
pub(super) fn clause_sort_supplies(kb: &KnowledgeBase, rid: RuleId, spec: Symbol) -> bool {
    let domain = kb.rule_domain(rid);
    same_sort_canonical(kb, domain, spec)
        || transitive_required_sorts(kb, domain)
            .iter()
            .any(|s| same_sort_canonical(kb, *s, spec))
}

/// 060.1 §1 — the refusal of a rule-body call that needs a dictionary of `spec` at a type the
/// clause declares no requirement at: a rule takes a dictionary only where it declares one.
fn undeclared_requirement(
    kb: &KnowledgeBase,
    rid: RuleId,
    call: &DemandCall,
    spec: Symbol,
) -> (TypeError, Option<crate::span::SourceId>) {
    let spec_name = short_name_of(kb.qualified_name_of(spec));
    let relation = match kb.rule_head_value(rid) {
        Value::Term { id, .. } => kb.head_functor(*id).unwrap_or(spec),
        _ => spec,
    };
    (
        TypeError::Other {
            site: TypeError::here(),
            span: Some(call.call.span.span),
            context: TypeErrorContext::Rule {
                name: relation,
                field: RuleField::Body,
            },
            expected: format!(
                "a requirement of `{spec_name}` the clause declares, at the type the call of \
                 `{op}` is at",
                op = kb.qualified_name_of(call.functor),
            ),
            actual: format!(
                "the clause declares none, and a rule takes no dictionary it does not declare: {}",
                crate::parse::desugar_target::DECLARE_A_REQUIREMENT,
            ),
        },
        Some(call.call.span.source),
    )
}

/// The goals in a connective's PROVED slots beneath `goal`, at every depth, pushed onto `out`
/// in pre-order: an `|` / `&` branch, a negand, a quantifier's body and a discharge's consequent
/// (each component of a slot the table wraps in `tuple(…)`), but no hypothesis and no binder
/// ([`proved_goal_children`]).
pub(super) fn nested_goals(kb: &KnowledgeBase, goal: &Rc<NodeOccurrence>, out: &mut Vec<Rc<NodeOccurrence>>) {
    let Some(expr) = goal.as_expr() else { return };
    for child in proved_goal_children(kb, expr) {
        out.push(Rc::clone(&child));
        nested_goals(kb, &child, out);
    }
}

/// `goal` with each nested goal of `nested` given its reads, as `and(read, …, goal)` where the
/// goal stands — a component of a slot the table wraps in `tuple(…)`, or the slot itself. The
/// connectives above a placement are rebuilt; every other node is kept, so a call is still found
/// by identity.
fn place_nested_reads(
    kb: &KnowledgeBase,
    goal: &Rc<NodeOccurrence>,
    nested: &[(Rc<NodeOccurrence>, Vec<Rc<NodeOccurrence>>)],
    and_sym: Symbol,
    pass: crate::kb::occurrence::PassId,
) -> Rc<NodeOccurrence> {
    map_proved_children(kb, goal, &|kb, n| place_reads_at(kb, n, nested, and_sym, pass))
}

/// One goal of a connective's slot with its reads before it ([`place_nested_reads`]), its own
/// slots placed in turn; `None` for a goal given no reads, whose slots the walk descends.
fn place_reads_at(
    kb: &KnowledgeBase,
    goal: &Rc<NodeOccurrence>,
    nested: &[(Rc<NodeOccurrence>, Vec<Rc<NodeOccurrence>>)],
    and_sym: Symbol,
    pass: crate::kb::occurrence::PassId,
) -> Option<Rc<NodeOccurrence>> {
    let (_, reads) = nested.iter().find(|(site, _)| Rc::ptr_eq(site, goal))?;
    let inner = map_proved_children(kb, goal, &|kb, n| place_reads_at(kb, n, nested, and_sym, pass));
    Some(reads.iter().rev().fold(inner, |rest, read| {
        NodeOccurrence::synthesized_expr(
            Expr::Apply {
                recv_type: None,
                functor: and_sym,
                pos_args: vec![Rc::clone(read), rest],
                named_args: Vec::new(),
                type_args: Vec::new(),
            },
            Rc::clone(goal),
            pass,
            goal.owner,
        )
    }))
}

/// `goal` with every goal `f` answers for replaced by its answer, descending through the
/// proved slots of the connectives above it ([`map_proved_children`]); every other node is
/// kept, so a goal is found by identity.
pub(super) fn map_proved_goals(
    kb: &KnowledgeBase,
    goal: &Rc<NodeOccurrence>,
    f: &dyn Fn(&KnowledgeBase, &Rc<NodeOccurrence>) -> Option<Rc<NodeOccurrence>>,
) -> Rc<NodeOccurrence> {
    match f(kb, goal) {
        Some(replaced) => replaced,
        None => map_proved_children(kb, goal, f),
    }
}

/// `goal` with each goal in its proved slots — each component of a slot the table wraps in
/// `tuple(…)`, or the slot itself — mapped by [`map_proved_goals`]; `goal` itself is not asked.
/// The connectives above a replaced goal are rebuilt, and a goal nothing under it moved is
/// handed back as it is.
pub(super) fn map_proved_children(
    kb: &KnowledgeBase,
    goal: &Rc<NodeOccurrence>,
    f: &dyn Fn(&KnowledgeBase, &Rc<NodeOccurrence>) -> Option<Rc<NodeOccurrence>>,
) -> Rc<NodeOccurrence> {
    let Some((functor, pos_args, _)) = goal.as_expr().and_then(expr_call_parts) else {
        return Rc::clone(goal);
    };
    let slots = kb.goal_slot_readings(functor, pos_args.len());
    if slots.is_empty() {
        return Rc::clone(goal);
    }
    // A node's children in `for_each_child` order: its positional arguments first.
    let children_of = |n: &Rc<NodeOccurrence>| {
        let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
        if let Some(expr) = n.as_expr() {
            for_each_child(expr, |c| children.push(Rc::clone(c)));
        }
        children
    };
    let mut children = children_of(goal);
    let mut changed = false;
    for slot in slots.iter().filter(|s| s.reading == crate::kb::SlotReading::Proved) {
        let Some(child) = pos_args.get(slot.index) else {
            continue;
        };
        let parts = slot.tuple_wrapped.then(|| goal_tuple_parts(kb, child)).flatten();
        let mapped = match parts {
            Some(parts) => {
                let mut parts_now = children_of(child);
                let mut moved = false;
                for (i, part) in parts.iter().enumerate() {
                    let m = map_proved_goals(kb, part, f);
                    moved |= !Rc::ptr_eq(&m, part);
                    parts_now[i] = m;
                }
                if moved {
                    crate::kb::simp_rewrite::reassemble(child, &parts_now)
                } else {
                    Rc::clone(child)
                }
            }
            None => map_proved_goals(kb, child, f),
        };
        changed |= !Rc::ptr_eq(&mapped, child);
        children[slot.index] = mapped;
    }
    if changed {
        crate::kb::simp_rewrite::reassemble(goal, &children)
    } else {
        Rc::clone(goal)
    }
}

/// A clause's requirement reads, in the one order every reader takes them in: the body's goals
/// in order, each preceded by the reads that stand before it, and within a goal the reads in its
/// connectives' PROVED slots, in pre-order. The citation computes a route per read in this order
/// (`citation_requirement_routes`), the resolver binds the routes in it (`bind_citation_reads`),
/// and the routes are counted and their specs read by it ([`requirement_read_counts`],
/// [`requirement_read_specs`]).
pub(crate) fn clause_requirement_reads(
    kb: &KnowledgeBase,
    fd: Symbol,
    body: &[Rc<NodeOccurrence>],
) -> Vec<Rc<NodeOccurrence>> {
    fn visit(
        kb: &KnowledgeBase,
        fd: Symbol,
        node: &Rc<NodeOccurrence>,
        out: &mut Vec<Rc<NodeOccurrence>>,
    ) {
        if requirement_read_out(kb, fd, node).is_some() {
            out.push(Rc::clone(node));
            return;
        }
        if let Some(expr) = node.as_expr() {
            for child in proved_goal_children(kb, expr) {
                visit(kb, fd, &child, out);
            }
        }
    }
    let mut out = Vec::new();
    for node in body {
        visit(kb, fd, node, &mut out);
    }
    out
}

/// A rule-body goal riding in its citation marker, `__within_requirements(goal, relation, d₀
/// … dₙ₋₁)` (WI-20261102-ATVC1), read off the occurrence: one slot per position of
/// `relation`'s layout.
pub(crate) struct GoalMarker<'a> {
    pub(crate) goal: &'a Rc<NodeOccurrence>,
    pub(crate) relation: Symbol,
    pub(crate) slots: &'a [Rc<NodeOccurrence>],
}

/// The citation marker `node` is, or `None` for any other node.
pub(crate) fn goal_marker<'a>(kb: &KnowledgeBase, node: &'a NodeOccurrence) -> Option<GoalMarker<'a>> {
    let Some(Expr::Apply {
        functor, pos_args, ..
    }) = node.as_expr()
    else {
        return None;
    };
    if pos_args.len() < 2
        || kb.builtin_of(*functor) != Some(crate::kb::resolve::BuiltinTag::WithinRequirements)
    {
        return None;
    }
    let Some(Expr::Ref(relation)) = pos_args[1].as_expr() else {
        unreachable!("a goal's citation marker names its relation by a symbol");
    };
    Some(GoalMarker {
        goal: &pos_args[0],
        relation: *relation,
        slots: &pos_args[2..],
    })
}

/// The labels an inferred read is spelled with, interned once per pass.
struct ReadLabels {
    /// The read of a call under a form ([`REQUIREMENT_IN_FORM_LABEL`]).
    in_form: Symbol,
    out: Symbol,
    slot: Symbol,
    dict: Symbol,
}

/// A call [`infer_rule_body_requirements`] reads a condition for: the occurrence, its
/// operation, and its arguments in the operation's PARAMETER order — aligned once, by the
/// predicate that admitted the call ([`align_call_args_to_params`]), and read as they stand
/// by everything after it.
struct DemandCall {
    call: Rc<NodeOccurrence>,
    functor: Symbol,
    args: Vec<Rc<NodeOccurrence>>,
}

/// A SPEC-OP demand ([`inferred_demand`]): the spec its instance is read at, and the call's
/// CARRIER arguments, which say which calls share one read.
struct SpecDemand {
    call: DemandCall,
    spec: Symbol,
    carriers: Vec<Rc<NodeOccurrence>>,
    /// The call stands under a form, which may not run it: its read binds the absence a
    /// missing provider leaves instead of failing ([`REQUIREMENT_IN_FORM_LABEL`]). A group's
    /// read is so only when every call it serves is.
    in_form: bool,
    /// A read of the requirement of the sort the rule is written in, at no carrier
    /// ([`ClauseCondition::SortRequires`]).
    of_the_sort: bool,
}

/// The dictionary of the guard of clause `rid` (`guards`: its spec, its carrier's frame slot
/// and its read's `out`) that `demand`'s call is at: the type the clause's typing stamped on
/// the call's carrier argument is the parameter the guard states the call's spec at. `None`
/// for a call at any other type.
fn declared_guard_of(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    guards: &[(Symbol, u32, Rc<NodeOccurrence>)],
    demand: &SpecDemand,
) -> Option<Rc<NodeOccurrence>> {
    if guards.is_empty() {
        return None;
    }
    let at = demand.carriers.first()?.inferred_type()?;
    let param = caller_param_at(kb, rid, &at)?;
    guards
        .iter()
        .find(|(spec, carrier, _)| *carrier == param && same_sort_canonical(kb, *spec, demand.spec))
        .map(|(_, _, out)| Rc::clone(out))
}

/// How slot `entry` of a rule-body call's dictionary chain is filled ([`slot_route`]).
enum SlotRoute {
    /// By the dictionary of a guard the clause declares at the slot's instance.
    Guard(Rc<NodeOccurrence>),
    /// By a read of its own: the callee states the slot at a concrete instance, the call's
    /// arguments fix it, or the clause's sort supplies its spec.
    Read,
    /// At a type of the clause that the clause declares no requirement at: refused.
    Undeclared,
}

/// [`SlotRoute`] of slot `entry` of `call`'s chain in clause `rid`. The slot's carrier binding
/// is the declared type of some of the callee's parameters, and the types the clause's typing
/// stamped on the arguments there say where the slot is: at a parameter the clause states a
/// guard of the slot's spec at (`guards`: spec, carrier frame slot, the read's `out`), at a
/// concrete type, or at another type of the clause.
fn slot_route(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    guards: &[(Symbol, u32, Rc<NodeOccurrence>)],
    call: &DemandCall,
    entry: &RequiresEntry,
) -> SlotRoute {
    if type_is_ground(kb, &entry.spec) || clause_sort_supplies(kb, rid, entry.required_sort) {
        return SlotRoute::Read;
    }
    let Some(key) = spec_carrier_param_or_sole(kb, kb.canonical_sort_sym(entry.required_sort)) else {
        return SlotRoute::Read;
    };
    let Some(binding) = spec_binding_value(kb, &entry.spec, kb.local_name_of(key)) else {
        return SlotRoute::Read;
    };
    // The binding names a type parameter of the callee or of its sort, by its name or by its
    // variable, and so may a parameter's type: each is read as the parameter's variable.
    let as_param_var = |kb: &KnowledgeBase, v: &Value| match view_ref_symbol(kb, v).and_then(|s| kb.canonical_type_param_var(s)) {
        Some(var) => Value::term(var),
        None => v.clone(),
    };
    let binding = as_param_var(kb, &binding);
    let Some(rec) = crate::kb::op_info::lookup_operation_info(kb, call.functor) else {
        return SlotRoute::Read;
    };
    let at: Vec<Value> = rec
        .params
        .iter()
        .zip(&call.args)
        .filter(|((_, ty), _)| {
            let ty = as_param_var(kb, ty);
            crate::kb::term_view::views_structurally_equal(kb, &ty, &binding)
        })
        .filter_map(|(_, arg)| arg.inferred_type())
        .collect();
    // No parameter is typed by the binding alone (`List[T = A]`): no argument says the slot's
    // instance, which the read derives from the values where the call runs.
    if at.is_empty() {
        return SlotRoute::Read;
    }
    for ty in &at {
        if let Some(param) = caller_param_at(kb, rid, ty) {
            if let Some((_, _, out)) = guards
                .iter()
                .find(|(spec, carrier, _)| *carrier == param && same_sort_canonical(kb, *spec, entry.required_sort))
            {
                return SlotRoute::Guard(Rc::clone(out));
            }
        }
    }
    if at.iter().any(|ty| instance_is_concrete(kb, ty))
        || !at.iter().any(|ty| type_reaches_the_head(kb, rid, ty))
    {
        return SlotRoute::Read;
    }
    SlotRoute::Undeclared
}

/// Is `demand`'s call at the element of a NAMED requirement slot a variable of clause `rid` is
/// typed with (kernel-language §8.1): `?p <=> box(a: ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)`
/// over `sort Box requires O: WeakOrd[T = T]`, `?p` a `Box[T = t, O = o]` and `?x` a `t` — the
/// read is filled from that slot as the citation fixes it, as a call reads the slot off its
/// argument, and nothing is declared for it.
fn carried_by_a_named_slot(kb: &mut KnowledgeBase, rid: RuleId, demand: &SpecDemand) -> bool {
    let Some(at) = demand.carriers.first().and_then(|c| c.inferred_type()) else {
        return false;
    };
    let Some(carrier_key) = spec_carrier_param_or_sole(kb, kb.canonical_sort_sym(demand.spec))
        .map(|k| kb.local_name_of(k).to_owned())
    else {
        return false;
    };
    clause_var_stamps(kb, rid).into_iter().any(|(_, ty)| {
        let TypeExtractor::Parameterized { base, bindings } = extract_type(kb, &ty) else {
            return false;
        };
        let entries = provider_dict_entries(kb, base, None);
        kb.named_requirement_slots(base).to_vec().into_iter().any(|slot| {
            if !slot.spec_base.is_some_and(|s| same_sort_canonical(kb, s, demand.spec)) {
                return false;
            }
            // The slot's requirement at the type's bindings, as a citation reads it
            // (`carried_slot_reading`): it carries the call where its carrier is the call's.
            let Some(entry) = dict_chain_index(kb, base, &slot).and_then(|i| entries.entries().get(i).cloned())
            else {
                return false;
            };
            slot_spec_at_bindings(kb, base, &entry.spec, &bindings)
                .and_then(|spec| spec_binding_value(kb, &spec, &carrier_key))
                .is_some_and(|carrier| crate::kb::term_view::views_structurally_equal(kb, &carrier, &at))
        })
    })
}

/// Does a guard of clause `rid` at the type `demand`'s call is at state a spec that requires the
/// call's: `Base.op(?x, ?r)` under `Derived[T = A]`, `?x: A`, where `Derived` requires `Base`. The
/// declared requirement holds its spec's chain (§8.7), and the call's read is routed through it.
fn declared_guard_requires(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    guards: &[(Symbol, u32, Rc<NodeOccurrence>)],
    demand: &SpecDemand,
) -> bool {
    if guards.is_empty() {
        return false;
    }
    let Some(at) = demand.carriers.first().and_then(|c| c.inferred_type()) else {
        return false;
    };
    let Some(param) = caller_param_at(kb, rid, &at) else {
        return false;
    };
    guards.iter().any(|(spec, carrier, _)| {
        *carrier == param
            && transitive_required_sorts(kb, *spec)
                .iter()
                .any(|s| same_sort_canonical(kb, *s, demand.spec))
    })
}

/// A SLOT demand ([`inferred_slot_demand`]): the spec of each slot of the callee's dictionary
/// chain, in chain order.
struct SlotDemand {
    call: DemandCall,
    chain: Vec<Symbol>,
    /// The call stands under a form the evaluator runs whole, where nothing derives an
    /// unfilled slot ([`REQUIREMENT_IN_FORM_LABEL`]).
    in_form: bool,
}

/// One INFERRED read for [`infer_rule_body_requirements`], and the clause variable it binds:
/// `find_dictionary(Spec, op, args…, out: ?d)` for a spec-op demand, with `slot: k` besides
/// for slot `k` of an ordinary operation's chain. `?d` is a NEW clause variable, PREPENDED to
/// the frame so every existing De Bruijn index stays where it is
/// ([`KnowledgeBase::extend_rule_frame_with_bounds`]).
#[allow(clippy::too_many_arguments)]
fn inferred_read(
    kb: &mut KnowledgeBase,
    rid: crate::kb::RuleId,
    fd_sym: Symbol,
    pass: crate::kb::occurrence::PassId,
    labels: &ReadLabels,
    spec: Symbol,
    witness: &DemandCall,
    slot: Option<usize>,
    // The read of a call under a form ([`REQUIREMENT_IN_FORM_LABEL`]).
    in_form: bool,
) -> (Rc<NodeOccurrence>, Rc<NodeOccurrence>) {
    let DemandCall {
        call: witness,
        functor,
        args,
    } = witness;
    let d_index = kb.rule_globals(rid).len() as u32;
    let d = kb.fresh_var(labels.dict);
    let bounds = kb.rule_type_bounds(rid).to_vec();
    kb.extend_rule_frame_with_bounds(rid, &[d], bounds);
    let span = witness.span;
    let owner = witness.owner;
    let node = |e: Expr| NodeOccurrence::new_expr(e, span, owner);
    let out = node(Expr::Var(Var::DeBruijn(d_index)));
    let mut read_args = vec![node(Expr::Ref(spec)), node(Expr::Ref(*functor))];
    read_args.extend(args.iter().cloned());
    let mut read_named = Vec::with_capacity(2);
    if let Some(k) = slot {
        read_named.push((labels.slot, node(Expr::Const(Literal::Int(k as i64)))));
    }
    if in_form {
        read_named.push((labels.in_form, node(Expr::Const(Literal::Bool(true)))));
    }
    read_named.push((labels.out, Rc::clone(&out)));
    let read = NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: None,
            functor: fd_sym,
            pos_args: read_args,
            named_args: read_named,
            type_args: Vec::new(),
        },
        Rc::clone(witness),
        pass,
        owner,
    );
    (read, out)
}

/// A call to weave, by identity in the original body, and the requirements it carries.
/// A call to weave, by identity in the original body, the requirements it carries, and — for a
/// call carrying the SLOTS of its chain rather than one dispatch dictionary — the pass that
/// marks it so ([`woven_slots_pass`]).
type WeaveTarget = (Rc<NodeOccurrence>, Vec<Rc<NodeOccurrence>>, Option<crate::kb::occurrence::PassId>);

/// Weave every target under `node` in ONE walk of the original tree, a target's own
/// arguments included — so a woven call nested in another woven call is found either way
/// round. `reached[i]` is set once `targets[i]` is found.
///
/// The ONE weave, for both producers: WI-1040's covered calls (one DISPATCH dictionary per
/// spec-op call, which instance it dispatches on) and [`infer_rule_body_requirements`]'
/// demands (that, or one per SLOT of an ordinary operation's dictionary chain, the clause's
/// conditions for the callee's own `requires`). A slot weave's call is built as a node of the
/// slot-weave pass, and the resolver tells the two apart by that mark
/// ([`is_woven_slots_call`]), not by the callee: one operation may be woven either way, a
/// `require[X]` covering a defaulted member of `X` with one dictionary where the clause's
/// inferred condition for `Holder.hsign`, a sort's own member, carries its sort's slots.
///
/// ```text
///     Desc.describe(?x, ?r)  ⇒  apply_within(fn = Desc.describe, args = (?x, ?r),
///                                            requirements = [?d])
/// ```
///
/// `apply_within` is the EXISTING carrier — `req_insertion` emits exactly this shape for
/// operation bodies, and eval's `start_apply_within` reads a dictionary out of that
/// channel. Identity, not structure: two calls to the same operation on the same arguments
/// are distinct occurrences, and only the ones a scan chose are woven.
fn weave_calls(
    node: &Rc<NodeOccurrence>,
    targets: &[WeaveTarget],
    reached: &mut [bool],
) -> Rc<NodeOccurrence> {
    let Some(expr) = node.as_expr() else {
        return Rc::clone(node);
    };
    if let (
        Some(i),
        Expr::Apply {
            functor,
            pos_args,
            named_args,
            type_args,
            ..
        },
    ) = (targets.iter().position(|(t, _, _)| Rc::ptr_eq(t, node)), expr)
    {
        reached[i] = true;
        let woven = Expr::ApplyWithin {
            functor: *functor,
            args: pos_args.iter().map(|a| weave_calls(a, targets, reached)).collect(),
            named_args: named_args
                .iter()
                .map(|(k, a)| (*k, weave_calls(a, targets, reached)))
                .collect(),
            requirements: targets[i].1.clone(),
            type_args: type_args.clone(),
        };
        return match targets[i].2 {
            None => node.rebuilt_expr(woven),
            Some(pass) => {
                let marked = NodeOccurrence::synthesized_expr(woven, Rc::clone(node), pass, node.owner);
                marked.carry_typer_stamps_from(node);
                marked
            }
        };
    }
    let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
    for_each_child(expr, |c| children.push(Rc::clone(c)));
    if children.is_empty() {
        return Rc::clone(node);
    }
    let new_children: Vec<Rc<NodeOccurrence>> =
        children.iter().map(|c| weave_calls(c, targets, reached)).collect();
    crate::kb::simp_rewrite::reassemble(node, &new_children)
}

/// Does a woven call at GOAL position have a reader? The resolver reads two call shapes
/// there, and both read a woven head (`resolve::goal_call_head`):
///   * the FUNCTIONAL-RELATION form `f(args…, result)` of a callee that form reads — a
///     rule-less bodied operation, or WI-1057's body-less spec op (the WI-938 hook);
///   * the BOOL VIEW — a bodied `Bool` operation at its declared arity, `eq(f(args…), true)`
///     (WI-583) — which is how `rule less(?a, ?b) :- Util.isLess(?a, ?b)` answers.
///
/// Anything else at goal position — a non-`Bool` call at its declared arity — is WI-583's
/// load error, and a woven call would slip past that check.
///
/// Each shape is counted as its reader counts it: the functional-relation hook reads a
/// POSITIONAL call only (its result column is positional and last), while the Bool view
/// counts every argument, named ones included — so `Util.isLess(x: ?a, y: ?b)` is the Bool
/// view it is at run time, and is woven like its positional twin.
///
/// THE FUNCTIONAL-RELATION LEG IS THE HOOK'S OWN GATE, asked of the goal
/// ([`KnowledgeBase::functional_relation_goal`], which `step_init`'s hook and WI-670's
/// refutation ask too) — a hand-spelled copy here skipped the gate's pinned-call branch, a
/// drift harmless only because a pinned call is declined later (WI-20260925-PRVA2). One
/// counting difference is inherited and unreachable: read through the view, an `Apply`
/// carrying CALL-SITE type arguments reports one more named slot than its woven twin — and
/// the loader refuses a written bracket on a rule-body goal (see the note at the Bool hook
/// in `step_init`).
fn woven_goal_has_reader(
    kb: &KnowledgeBase,
    goal: &Rc<NodeOccurrence>,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> bool {
    let relational = kb
        .functional_relation_goal(&crate::eval::Value::Node(Rc::clone(goal)))
        .is_some();
    let bool_view = kb.bare_bodied_bool_relation(functor)
        && kb
            .op_record(functor)
            .and_then(|r| r.signature.as_ref())
            .is_some_and(|sig| sig.params.len() == pos_args.len() + named_args.len());
    relational || bool_view
}

/// Does the demand walk of [`infer_rule_body_requirements`] look inside this DATA-position
/// node? A call's arguments and a data constructor's fields are evaluated where the goal
/// holding them runs; a lambda's, `let`'s, `match`'s or `if`'s calls later, inside the form,
/// with the dictionaries the goal's reads bound — the walk marks what it finds there `in_form`.
fn demand_walk_enters(expr: &Expr) -> bool {
    matches!(
        expr,
        Expr::Apply { .. }
            | Expr::Let { .. }
            | Expr::Match { .. }
            | Expr::If { .. }
            | Expr::Lambda { .. }
            | Expr::ApplyWithin { .. }
            | Expr::DotApply { .. }
            | Expr::Constructor { .. }
            | Expr::ConstructorWithin { .. }
            | Expr::TupleLit { .. }
            | Expr::ListLit(_)
            | Expr::SetLit(_)
    )
}

/// WI-20260925-P7VP4 — the SLOT demand of a rule-body call the typer left to its clause as the
/// slots of its chain ([`ClauseCondition::Slots`]): the spec of each slot, in chain order, with
/// the call's aligned arguments ([`SlotDemand`]), or `None` where the call carries no such
/// condition or nothing reads it woven.
///
/// Each slot becomes a condition of the clause, and the call carries them. A condition no
/// citation fills stays UNBOUND, and the bridge then derives that slot from the argument
/// values as it did before ([`resolve_bridge_requirements`]). A woven call whose arguments
/// are not yet ground DELAYS (the WI-938 hook routes a woven goal to `unify`, which waits on
/// an unevaluated call), as the same call unwoven does since WI-20260926-CYNPE — increment
/// 1's `an_unground_woven_call_delays`, and `an_unground_slot_call_delays` for this one.
///
/// Which calls carry the condition is the typer's decision, written on the call where it
/// leaves a half of the chain to the clause (`leave_to_the_clause`); what is asked here is the
/// weave's own: a callee the bridge runs from a rule body (`functional_relation_arity`), and
/// arguments that align to its parameters.
fn inferred_slot_demand(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Option<SlotDemand> {
    if occ.clause_condition() != Some(ClauseCondition::Slots)
        || kb.functional_relation_arity(functor).is_none()
    {
        return None;
    }
    let rec = crate::kb::op_info::lookup_operation_info(kb, functor)?;
    let args = align_call_args_to_params(kb, &rec.params, pos_args, named_args)?;
    let chain = op_dict_entries(kb, functor);
    (!chain.is_empty()).then(|| SlotDemand {
        in_form: false,
        chain: chain.iter().map(|e| e.required_sort).collect(),
        call: DemandCall {
            call: Rc::clone(occ),
            functor,
            args,
        },
    })
}

/// The spec a rule-body call DEMANDS a condition for under [`infer_rule_body_requirements`] —
/// one the typer left to its clause as the dictionary of a spec it is dispatched through
/// ([`ClauseCondition::Dispatch`]) — with the call's aligned and carrier arguments
/// ([`SpecDemand`]), or `None` where the call carries no such condition or the weave declines
/// it (see that function's list).
fn inferred_demand(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    written: &[Symbol],
) -> Option<SpecDemand> {
    let (spec, of_the_sort) = match occ.clause_condition() {
        Some(ClauseCondition::Dispatch { spec }) => (spec, false),
        Some(ClauseCondition::SortRequires { spec }) => (spec, true),
        _ => return None,
    };
    // The clause's own `require[…]` reads it, and covers its calls (WI-1040).
    if written.contains(&kb.canonical_sort_sym(spec)) {
        return None;
    }
    // A call that does not ALIGN to its operation's parameters (an argument missing, a
    // label naming no parameter) is the typer's to refuse.
    let rec = crate::kb::op_info::lookup_operation_info(kb, functor)?;
    let args = align_call_args_to_params(kb, &rec.params, pos_args, named_args)?;
    // A BODY-LESS spec op is read — dispatched — wherever the goal runs it: at goal position,
    // WI-1057's functional-relation form, and in a value slot, where an operation application
    // is a computation (proposal 068 §1) and a woven call is dispatched through its
    // dictionary (`reduce_op_value`).
    let reader = kb.functional_relation_arity(functor).is_some()
        || kb.body_less_relation_arity(functor).is_some();
    if !reader {
        return None;
    }
    // A read of the clause sort's requirement has no carrier and no witness: every such call
    // in the clause reads the one instance the citation fixes, and nothing the call is given
    // says which — a supplied dictionary decides it, and an uncited clause waits.
    let (carriers, args) = if of_the_sort {
        (Vec::new(), Vec::new())
    } else {
        (aligned_carrier_args(kb, &rec.params, &args, spec), args)
    };
    Some(SpecDemand {
        call: DemandCall {
            call: Rc::clone(occ),
            functor,
            args,
        },
        spec,
        carriers,
        in_form: false,
        of_the_sort,
    })
}

/// WI-642 — the STATIC face of the WI-300 rule-body dictionary. Walk every rule
/// clause body for spec-op calls (`eq(?x, ?y)` from `Eq[T]`, a user spec's op, …)
/// and flag any whose requirement is *statically missing*: a concrete carrier
/// argument whose sort provides no instance of the spec AND no in-body
/// `requires(Spec[…])` covers it. Such a call can never dispatch — at resolution
/// the WI-300 `find_dictionary` guard `DontFire`s and the clause silently fails
/// (proposal 052 §"Requirements in a clause body"). Making it a load error is the
/// repo's "loud error over a silent skip".
///
/// The WI-292 distinction is load-bearing, and this reads [`simp_guard_holds_core`], as the
/// `@[simp]` guard does, so the two cannot disagree on which argument carries the spec or
/// on the outcome:
///   * **`Fire`** — the carrier provides the spec → satisfiable, no error.
///   * **`Suspend`** — the carrier is under-determined (an abstract type-param: a
///     polymorphic rule that legitimately propagates its requirement to whoever
///     queries it under a concrete type) → NOT an error; it suspends as a residual
///     at fire time, never NAF-decided (WI-067). This is why an ABSTRACT rule-body
///     carrier is treated OPPOSITELY to an abstract OP-body carrier (WI-325): an op
///     has a caller who must thread the dictionary, a rule resolves its own from
///     the concrete query values at fire time.
///   * **`DontFire`** — a ground concrete carrier that provides no instance → the
///     statically-missing case → `UnfillableOperationRequirement`, naming the carrier
///     (WI-883; `MissingRequiresForSpecOp`, the abstract case's sentence, only where no
///     carrier was read).
///
/// WI-883 widened the population from body-less members to a DEFAULTED member of a spec
/// with an abstract one — its default's sibling calls need the instance just the same —
/// and made this pass the owner of a rule-body spec-op call: the typer's operation-body
/// refusal stays out of rule bodies, so one call gets one diagnosis. One refusal is the
/// typer's there too, for a call this pass reads no carrier of: a bracket that names no one
/// instance (`Pc[C = Bag].both()` beside two provisions saying `Element` apart, `Pc[C = Foo,
/// Element = Int64].both()` beside none), a rule body's call being typed as an operation
/// body is (068 §3).
///
/// Read-only: the arg carrier sorts come from the `inferred_type` the preceding
/// `type_rule_bodies` stamped onto each body `Var` (WI-603), exactly as the typer's
/// `@[simp]` guard [`simp_fire_guard_holds`] reads them.
///
/// CONSERVATIVE BOUNDARY (deliberate — the "static face of WI-300"): satisfiability
/// is decided by [`simp_guard_holds_core`], the SAME core the runtime `find_dictionary`
/// guard uses, asking [`carrier_provides_spec`]: direct, transitive and instance-fact
/// (WI-431) provisions, and a WI-450 witness-sort provision (`sort W provides Spec[T =
/// Carrier]`, impl owned by `W`) — though here a witness-supplied carrier only DECLINES
/// ([`spec_op_call_carrier_outcome`]). A denoted/value-fact provision is seen by neither
/// (`sort_provides` skips it): a rule relying on one without an in-body `requires` is
/// (rarely) flagged, and the escape is to declare the requirement or add a
/// direct/instance provision. Only ever a false POSITIVE risk on that shape — never a
/// spurious accept.
/// Answers the refusals, and each call it refused by its clause and span — one call, a clause's
/// body being written in one file — so a later pass does not refuse it again.
pub(super) fn check_rule_body_requirements(kb: &KnowledgeBase) -> (Vec<TypeError>, Vec<(RuleId, Span)>) {
    let mut errors: Vec<TypeError> = Vec::new();
    let mut refused_calls: Vec<(RuleId, Span)> = Vec::new();
    // Absent when the builtin is unregistered (a minimal KB); then no rule can
    // carry a declared `requires`, so `declared` simply stays empty.
    let fd_sym = kb.try_resolve_symbol(crate::parse::desugar_target::qualified(
        crate::parse::desugar_target::FIND_DICTIONARY,
    ));
    for rid in kb.live_rule_ids() {
        if kb.is_fact(rid) {
            continue; // facts have no body
        }
        // Read-only pass — no `set_rule_body_nodes`, so hold the stored slice
        // directly (both walkers take `&Rc<NodeOccurrence>`) rather than cloning.
        let body_nodes = kb.rule_body_nodes(rid);
        // The spec bases the rule declares an explicit in-body `requires(Spec[…])`
        // for (desugared to `find_dictionary`, in the un-rewritten 1-arg OR the
        // WI-300-rewritten ≥2-arg form). A declared requirement is the rule's OWN
        // dictionary mechanism (WI-300) — respect it and never flag its ops, even at
        // a concrete carrier that cannot satisfy it (the guard decides that at fire
        // time; the user has explicitly acknowledged the obligation). A Horn rule
        // does NOT inherit its enclosing sort's `requires` chain (that gates
        // `@[simp]`/`@[unfold]` equations, not clause bodies), so the in-body goal is
        // the only declaration site.
        let mut declared: SmallVec<[Symbol; 2]> = SmallVec::new();
        if let Some(fd) = fd_sym {
            // An INFERRED read (WI-20260925-P7VP4) is not a declaration: the author
            // acknowledged nothing, and it covers only calls this pass leaves undecided —
            // counting it would silence the refusal of a sibling call at a ground carrier.
            for node in body_nodes.iter().filter(|n| !is_inferred_requirement_read(kb, n)) {
                collect_find_dictionary_bases(kb, node, fd, &mut declared);
            }
        }
        let before = errors.len();
        for node in body_nodes {
            check_occ_spec_op_requirements(kb, node, fd_sym, &declared, &mut errors);
        }
        refused_calls.extend(errors[before..].iter().filter_map(|e| e.span(kb)).map(|span| (rid, span)));
    }
    (errors, refused_calls)
}

/// WI-20260917-NR6FJ — the OPERATION-CALL twin of [`check_rule_body_requirements`].
///
/// That pass refuses a rule-body call to a SPEC OP whose concrete carrier provides no
/// instance. This one refuses a rule-body call to an ORDINARY OPERATION that DECLARED the
/// same obligation — `operation viaop(x: Plain) requires Desc[T = Plain]` — where nothing
/// can fill the slot. A `requires` is an inbound slot the CALLER fills; at a rule-body
/// call the caller is this clause, and if the named carrier provides nothing and the
/// clause declares no requirement of its own, the slot has no filler anywhere.
///
/// # What happened before, and why it is load-blocking
///
/// MEASURED, and the outcome depended on an irrelevance — whether the spec op carries a
/// DEFAULT body:
///
///   * BODY-LESS: the callee's body classifies as `DeferToRequirement`, reads a slot the
///     frame never bound, and `bridge_op_to_eval` raises `EvalError::Internal` — a
///     debug-build ABORT from a program that type-checked;
///   * DEFAULTED: the call silently folds the spec's default and ANSWERS, where the same
///     demand written `requires(Desc[T = Plain])` in the clause correctly declines.
///
/// The eval site's own comment asks for this refusal by name: *"it wants a LOAD refusal
/// naming the carrier sort and the missing provision … WI-1102 puts the refusal at the
/// CALL, at load, where the typer has both."*
///
/// # Why here and not at WI-1102's park
///
/// That park lives inside [`build_op_scoped_dicts`], which — MEASURED, by instrumenting
/// its first line — is NEVER CALLED for a rule-body caller. A rule-body call is a GOAL,
/// not an expression call, so it never reaches the expression typer at all. The park's
/// own rule-body gate (`OpSlotParkSite::for_call`'s `enclosing_op.is_some()`) is a
/// second, independent reason and not the operative one: removing it moves zero rows.
///
/// # The boundaries, each a population this must not swallow
///
///   * AT THE CALL, NEVER AT THE DECLARATION — `wi840_named_requires_slot_test` declares
///     a two-slot op over a spec nothing provides and never calls it. Legitimate: the
///     provision may come from whoever loads the file;
///   * A DECLARED IN-BODY `requires` SUPPRESSES IT, exactly as in the sibling pass — the
///     author has acknowledged the obligation and the guard decides at fire time;
///   * A TYPE-PARAMETER or PROJECTION carrier is skipped: there the caller supplies, and
///     WI-20260909-S8CBV's caller-coverage refusal already owns the undischargeable case;
///   * A RESOLVER BUILTIN is skipped, the same exemption and the same witness the sibling
///     pass takes (`PartialOrd.gt` never consults an `Ord` instance);
///   * `carrier_provides_spec`, not a bare `sort_provides`, so a WITNESS-supplied
///     provision counts.
pub(super) fn check_rule_body_operation_requires(kb: &mut KnowledgeBase) -> Vec<TypeError> {
    let mut errors: Vec<TypeError> = Vec::new();
    let fd_sym = kb.try_resolve_symbol(crate::parse::desugar_target::qualified(
        crate::parse::desugar_target::FIND_DICTIONARY,
    ));
    let rids: Vec<crate::kb::RuleId> = kb.live_rule_ids();
    for rid in rids {
        if kb.is_fact(rid) {
            continue;
        }
        let body_nodes: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
        let mut declared: SmallVec<[Symbol; 2]> = SmallVec::new();
        if let Some(fd) = fd_sym {
            // Written reads only, as in the sibling pass: an inferred one declares nothing.
            for node in body_nodes.iter().filter(|n| !is_inferred_requirement_read(kb, n)) {
                collect_find_dictionary_bases(kb, node, fd, &mut declared);
            }
        }
        let mut calls: Vec<(Symbol, Option<Span>)> = Vec::new();
        for node in &body_nodes {
            let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(node)];
            while let Some(o) = stack.pop() {
                let Some(expr) = o.as_expr() else { continue };
                // A WOVEN call is still a call (WI-20260925-P7VP4 weaves an ordinary
                // operation's call through the clause's slot conditions before this runs),
                // and it owes the same slots.
                if let Expr::Apply { functor, .. } | Expr::ApplyWithin { functor, .. } = expr {
                    if Some(*functor) != fd_sym {
                        calls.push((*functor, Some(o.span.span)));
                    }
                }
                for_each_child(expr, |c| stack.push(Rc::clone(c)));
            }
        }
        for (functor, span) in calls {
            // AN OPERATION, and asked FIRST: a rule body is full of entity
            // constructors and data functors, and `op_dict_entries` would build a chain
            // for every one of them to answer "empty". The filter is the cheap read.
            if !crate::kb::op_info::operation_is_declared(kb, functor) {
                continue;
            }
            // The SPEC-OP population belongs to the sibling pass, which decides it from
            // the CALL's own carrier arguments; a builtin never consults an instance.
            if kb.is_builtin(functor) || lookup_spec_op_dispatch(kb, functor).is_some() {
                continue;
            }
            let entries: Vec<RequiresEntry> = op_dict_entries(kb, functor).op_entries().to_vec();
            for entry in entries {
                let spec_canon = kb.canonical_sort_sym(entry.required_sort);
                if declared
                    .iter()
                    .any(|d| kb.canonical_sort_sym(*d) == spec_canon)
                {
                    continue;
                }
                if spec_is_self_representing(kb, spec_canon) {
                    continue;
                }
                let Some(param) = spec_carrier_param_or_sole(kb, spec_canon) else {
                    continue;
                };
                let Some((_, bindings)) = unwrap_spec_view_value(kb, &entry.spec) else {
                    continue;
                };
                let Some(bound) = binding_for_param(kb, &bindings, param, BindingKeyMatch::Label)
                else {
                    continue;
                };
                if is_type_param_view(kb, bound) {
                    continue;
                }
                let Some(carrier) = sort_functor_of_view(kb, bound) else {
                    continue;
                };
                if carrier_provides_spec(kb, carrier, spec_canon) {
                    continue;
                }
                errors.push(TypeError::UnfillableOperationRequirement {
                    span,
                    callee_op: functor,
                    spec_sort_sym: entry.required_sort,
                    carrier_sym: carrier,
                });
            }
        }
    }
    errors
}

/// WI-583 / WI-20260822-J38JE item 4 — refuse every rule-body GOAL that has no goal
/// reading. Two shapes reach that verdict, and the pass is one because the question is
/// one: *is this term readable as a goal at all?*
///
///   * a rule-less OPERATION with a CONCRETE non-`Bool` return, used bare at its
///     declared arity (WI-583). A `Bool`-returning op there IS meaningful — it is the
///     operation's relational view, gated to `eq(op(args), true)` by WI-580's
///     [`KnowledgeBase::bare_bodied_bool_relation`] at resolve time (true ⇒ success,
///     false ⇒ fail, unground ⇒ suspend) — but a concrete non-`Bool` op falls through
///     to a silent failed relation lookup.
///   * a non-BOOLEAN CONSTANT (`:- 42`, `:- "hello"`), which names no predicate at all
///     (item 4). `true` / `false` ARE readable and are not flagged: a boolean constant
///     in goal position is a SEARCH, answered in `SearchStream::step_init` — `true`
///     succeeds, `false` fails, at every goal position (spec §5.3).
///
/// Both are what the repo principle "prefer a loud error over a silent skip" rejects,
/// and both were SILENT before their respective fixes: the op fell through to a failed
/// relation lookup, the constant to no lookup at all. This is the static, load-time
/// face of the resolver's goal routing — the sibling of [`check_rule_body_requirements`]
/// (WI-642), run in the same phase so `build_op_signatures` has settled every op's
/// return type.
///
/// Each error carries the `SourceId` of the occurrence it was raised on, which is what
/// makes it render `path:line:col` — the surrounding block's other passes are whole-KB
/// and push untagged errors (see the `sources.resize` at the call site).
///
/// DELIBERATELY NOT flagged (each is either correct or pre-existing, never a
/// regression): a `Bool`-returning op whose body is absent (an abstract spec op,
/// which dispatches through its `requires` dictionary — WI-573) or effectful
/// (which `bare_bodied_bool_relation` already declines to route on purity
/// grounds); a NON-concrete return (a bare type parameter that may instantiate
/// to `Bool`); the functional-relation form `f(args, result)` (arity + 1); a
/// rule-backed functor (a genuine relation). See `check_goal_atom_reading`.
///
/// A THIRD SHAPE: a goal on a rule-less operation whose ARGUMENT LIST is neither the
/// operation's parameter list nor that list and one positional result column
/// ([`operation_goal_arity_error`]). It is the operation's call — there is no clause to
/// prove it against — and no call has that shape, so it is refused wherever a goal is
/// proved, a `|` branch and a quantifier's body included.
///
/// A FOURTH SHAPE: a `const` at a goal (WI-20260822-NDG34). A `Bool` const with a
/// load-time value is folded by the loader to the literal it holds, a search
/// (`Loader::goal_const_value`), so one that reaches here is either of another type,
/// which names no truth, or a `Bool` with no value to fold
/// ([`crate::kb::load::ConstGoalProblem`]). Applied (`flag()`), it is the call the typer
/// refuses in a value slot and an operation body, [`TypeError::UnknownApplyFunctor`]. No
/// clause is filed under a const (`Loader::refuse_if_head_names_no_relation`), so a const is never a
/// relation's name here.
pub(super) fn check_rule_body_goal_readings(
    kb: &mut KnowledgeBase,
) -> Vec<(TypeError, Option<crate::span::SourceId>)> {
    let mut errors: Vec<(TypeError, Option<crate::span::SourceId>)> = Vec::new();
    let mut held_to_parameters: Vec<Rc<NodeOccurrence>> = Vec::new();
    let mut const_goals: Vec<Rc<NodeOccurrence>> = Vec::new();
    for rid in kb.live_rule_ids() {
        if kb.is_fact(rid) {
            continue; // facts have no body
        }
        for atom in kb.rule_body_nodes(rid) {
            check_goal_atom_reading(
                kb,
                atom,
                &mut errors,
                &mut held_to_parameters,
                &mut const_goals,
            );
        }
    }
    for goal in held_to_parameters {
        if let Some(e) = operation_goal_arity_error(kb, &goal) {
            errors.push((e, Some(goal.span.source)));
        }
    }
    for goal in const_goals {
        if let Some(e) = const_goal_error(kb, &goal) {
            errors.push((e, Some(goal.span.source)));
        }
    }
    // ONE GOAL IN THE TEXT REPORTS ONCE — WI-1034's rule for `check_rule_body_goals`,
    // which this pass did not obey (WI-20260902-8K4RB). A `-:` multi-head rule desugars
    // to one clause per conclusion SHARING THE BODY, so a single bad goal arrives here
    // through N `RuleId`s and every variant this pass raises was printed N times, at one
    // byte-identical `line:col`. MEASURED, `rule banded: 42 -: gte(?d, 0), lte(?d, 9)`
    // reported the constant refusal TWICE at `4:5` — a pre-existing defect of the two
    // older members, found while checking that the new one obeyed the rule.
    //
    // KEYED ON (variant, source, span) and not on the rendered message: rendering needs a
    // `&KnowledgeBase` walk per error, and the identity that matters is the POSITION plus
    // WHICH refusal it is — two different verdicts about one span would still both
    // survive, and each of these variants is a function of the goal written there.
    let mut seen: HashSet<(
        std::mem::Discriminant<TypeError>,
        Option<crate::span::SourceId>,
        Option<(u32, u32)>,
    )> = HashSet::new();
    errors.retain(|(e, src)| {
        seen.insert((
            std::mem::discriminant(e),
            *src,
            e.span(kb).map(|sp| (sp.start, sp.end)),
        ))
    });
    errors
}

/// The children of `expr` the resolver PROVES as goals, `tuple(…)` wrapper unwrapped —
/// the occurrence-side reading of the ONE slot table
/// ([`KnowledgeBase::goal_slot_readings`]), filtered to [`SlotReading::Proved`].
///
/// READ FROM THE TABLE, not written here. This pass used to carry a hand-written
/// allowlist of three symbols (`reflect.not`, `kernel.or`, `kernel.push_choice`) and
/// that list was WRONG BY OMISSION: a bounded quantifier's body and a discharge's
/// consequent are goal positions the resolver runs, and neither was entered — so
/// `(forall ?x in [1]: 42)` loaded clean and answered nothing while `not(42)` was
/// refused, one spelling with two readings decided by depth, which is the exact defect
/// WI-20260822-J38JE exists to remove. Found by /code-review. WI-1058 built the table
/// for this reason and `child_body_positions` (`rule_dispatch.rs`) already reads it; this is the
/// last hand-written copy retired.
///
/// `Assumed` is deliberately NOT here. A discharge's ANTECEDENTS are hypotheses — the
/// predicates its consequent proves against — so they are a binding position, not a
/// proved one, and the walks that refuse a dead goal have always left them alone
/// ([`GoalCommit`]'s doc carries the measurement). `Binders` is not a goal at all.
///
/// The three functor-bearing shapes are all read, because the SAME connective arrives
/// as an `Apply` when the loader lowered it from source and as a `Constructor` when it
/// was materialized from a term (`forall_impl` names no operation) — the point
/// `assumed_body_functors` makes about its own head test.
pub(super) fn proved_goal_children(kb: &KnowledgeBase, expr: &Expr) -> Vec<Rc<NodeOccurrence>> {
    let Some((functor, pos_args, _)) = expr_call_parts(expr) else {
        return Vec::new();
    };
    let mut out = Vec::new();
    for slot in kb.goal_slot_readings(functor, pos_args.len()) {
        if slot.reading != crate::kb::SlotReading::Proved {
            continue;
        }
        let Some(child) = pos_args.get(slot.index) else {
            continue;
        };
        if slot.tuple_wrapped {
            out.extend(tuple_goal_children_occ(kb, child));
        } else {
            out.push(Rc::clone(child));
        }
    }
    out
}

/// The components of a tuple-wrapped goal slot — the occurrence-side peer of
/// `KnowledgeBase::tuple_goal_children`, and the same defensive fallback: a body that
/// is not a `tuple` is ONE goal, returned as-is rather than dropped, so no goal escapes
/// the walk. Reached only from the slot table's `tuple_wrapped` rows, which is what
/// keeps a user functor named `tuple` from having its data arguments walked as goals.
fn tuple_goal_children_occ(
    kb: &KnowledgeBase,
    body: &Rc<NodeOccurrence>,
) -> Vec<Rc<NodeOccurrence>> {
    match goal_tuple_parts(kb, body) {
        Some(args) => args.iter().map(Rc::clone).collect(),
        None => vec![Rc::clone(body)],
    }
}

/// The components of a tuple-wrapped goal slot's `tuple(g₁, …, gₙ)` wrapper, or `None` for a
/// body that is one goal ([`tuple_goal_children_occ`]).
pub(super) fn goal_tuple_parts<'a>(
    kb: &KnowledgeBase,
    body: &'a Rc<NodeOccurrence>,
) -> Option<&'a [Rc<NodeOccurrence>]> {
    body.as_expr()
        .and_then(expr_call_parts)
        .filter(|(f, _, _)| kb.local_name_of(*f) == "tuple")
        .map(|(_, pos_args, _)| pos_args)
}

/// Classify one goal-position occurrence for [`check_rule_body_goal_readings`]:
/// recurse THROUGH a goal connective into its (goal) arguments, else flag a head with
/// no goal reading — a rule-less non-Bool operation, a non-boolean constant, or (since
/// WI-20260902-8K4RB) the subject of a bodyless EQUATION, whose clauses index under the
/// `eq`/`unify` connective so the name owns none.
/// Iterative (explicit worklist) so a deeply-nested connective body cannot overflow the
/// host stack — mirrors [`check_occ_spec_op_requirements`].
///
/// THE DESCENT IS THIS PASS'S OWN, and it is WIDER than `undefined_rule_body_goals`'
/// (WI-863/WI-1034): every PROVED goal slot is checked here — a bare `or` /
/// `push_choice` branch, a bounded quantifier's body, a discharge's consequent — where
/// a goal that merely NAMES NOTHING in one of those is tolerated. The two rules are not
/// in conflict; they answer different questions. A name in a branch that may never need
/// to answer might exist in another program or another load phase, and refusing it
/// would reject a program that computes the right answer (`push_choice_test` names
/// undefined branches on purpose). A term with NO READING has no such defence: `42` is
/// not a goal in any program, in any branch, under any binding. MEASURED before this:
/// `:- base(9) | 42` and `:- (forall ?x in [1]: 42)` both loaded clean.
///
/// The slots come from [`proved_goal_children`], which reads the ONE table. A
/// hand-written list is what made the quantifier hole, so the list is not written here.
fn check_goal_atom_reading(
    kb: &KnowledgeBase,
    atom: &Rc<NodeOccurrence>,
    errors: &mut Vec<(TypeError, Option<crate::span::SourceId>)>,
    // The goals [`operation_goal_arity_error`] is asked about once the walk is over: it
    // interns, and this walk holds the KB shared.
    held_to_parameters: &mut Vec<Rc<NodeOccurrence>>,
    // The const goals [`const_goal_error`] judges once the walk is over, for the same
    // reason: it reads the const's load-time value, which memoizes.
    const_goals: &mut Vec<Rc<NodeOccurrence>>,
) {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(atom)];
    while let Some(o) = stack.pop() {
        let Some(expr) = o.as_expr() else {
            // A non-`Expr` occurrence kind (Pattern / Type / EffectExpr) — never a goal.
            // A LITERAL goal is NOT here: it arrives as `Expr::Const`, which the match
            // below reads (WI-20260822-J38JE item 4); this arm's old comment claimed it,
            // and that claim is what let `:- 42` through.
            continue;
        };
        // DESCEND FIRST, and unconditionally. The old order asked "is this a
        // connective?" against a three-symbol allowlist and `continue`d, which meant a
        // goal-bearing functor OUTSIDE that list (`forall_in`, `forall_impl`) fell to
        // the `is_builtin` skip below with its goal slots never visited. Reading the
        // slot table instead makes the descent total over the connectives the resolver
        // actually runs, and costs nothing on a plain atom — whose arguments are DATA,
        // so the table answers empty.
        stack.extend(proved_goal_children(kb, expr));
        // A goal with a column named `result:` (proposal 069 §1.1) binds the call's
        // result, as the functional view does.
        let mut names_result = false;
        let (f, provided) = if let Some((f, pos, named)) = expr_call_parts(expr) {
            names_result = named.iter().any(|(label, _)| is_result_label(kb, *label));
            (f, pos.len() + named.len())
        } else {
            match expr {
                Expr::Ref(s) | Expr::Ident(s) => (*s, 0), // a nullary reference
                // WI-20260822-J38JE item 4 — a CONSTANT goal. The BOOLEAN one has a
                // reading and is not this pass's business: `true` succeeds and `false`
                // fails, at every goal position, answered in `SearchStream::step_init`.
                // Every other constant has no reading, and before this had no diagnostic
                // either — the goal-position gates all key on a FUNCTOR (this pass's op
                // record, WI-1034's `undefined_functor`), and a constant has none.
                Expr::Const(lit) => {
                    if !matches!(lit, Literal::Bool(_)) {
                        errors.push((
                            TypeError::ConstantInGoalPosition {
                                span: Some(o.span.span),
                                literal: {
                                    let mut buf = String::new();
                                    crate::persistence::print::write_literal(lit, &mut buf);
                                    buf
                                },
                            },
                            Some(o.span.source),
                        ));
                    }
                    continue;
                }
                _ => continue,
            }
        };
        // WI-20261029-50361 — a namespace is no relation, and its goal answered `true`
        // through the clause its declaration files under its own name.
        if kb.is_namespace_only(f) {
            errors.push((
                TypeError::NamespaceAsGoal {
                    span: Some(o.span.span),
                    namespace: f,
                },
                Some(o.span.source),
            ));
            continue;
        }
        if kb.has_kind(f, crate::intern::SymbolKind::Const) {
            const_goals.push(Rc::clone(&o));
            continue;
        }
        // A resolver builtin (`eq`/`neq`/`gt`/`find_dictionary`/…) has its own
        // goal semantics — skip. We deliberately do NOT recurse into its value
        // operands: a non-Bool op-call inside `eq(length(?l), 3)` is a value, not
        // a goal.
        if kb.is_builtin(f) {
            continue;
        }
        // Is it an operation with a built signature? (cheap map lookup) A
        // non-operation (unresolved name / relation-only functor) is not this
        // pass's concern — an unresolved name is diagnosed elsewhere.
        let Some(sig) = kb.op_record(f).and_then(|r| r.signature.as_ref()) else {
            // WI-20260902-8K4RB — EXCEPT for one non-operation that IS this pass's
            // concern: the subject of a bodyless EQUATION. It has no op record (the
            // equation declares no operation) and it RESOLVES (the mint stamped it
            // `EquationFunctor`), so it fell through this gate AND through WI-1034's
            // "names nothing" refusal, and the goal answered the empty relation in
            // silence — `not(…)` around it answering ONE.
            //
            // ASKED THROUGH [`KnowledgeBase::cites_a_relation`], never as a kind test,
            // because a scope may write one name in BOTH head shapes and then a
            // predicate clause IS indexed under it; that function is WI-898's single
            // owner of "does this name denote a relation" and deriving the answer from
            // the clause index is what keeps this from being a second, order-dependent
            // one. Driven in both directions by
            // `a_predicate_clause_on_the_same_name_keeps_the_goal_legal`.
            if kb.has_kind(f, crate::intern::SymbolKind::EquationFunctor) && !kb.cites_a_relation(f)
            {
                errors.push((
                    TypeError::EquationSubjectInGoalPosition {
                        span: Some(o.span.span),
                        functor: f,
                    },
                    Some(o.span.source),
                ));
            }
            continue;
        };
        // A goal on a RULE-LESS operation is that operation's call, and its argument list
        // is held to the parameter list ([`operation_goal_arity_error`]) — unless it is one
        // of the two spellings with nothing to hold: every parameter positional, alone
        // (the declared arity, read below) or with one more positional column (the
        // functional-relation view). A spec operation's goal is typed as a call where it
        // stands, and its verdict is raised there.
        if let Some((_, pos, named)) = expr_call_parts(expr) {
            let declared = sig.params.len();
            let positional_and_whole =
                named.is_empty() && (pos.len() == declared || pos.len() == declared + 1);
            if !positional_and_whole
                && spec_op_call_parent(kb, f).is_none()
                && kb.rules_by_functor_iter(f).next().is_none()
            {
                held_to_parameters.push(Rc::clone(&o));
            }
        }
        // Only the BARE / DIRECT goal form — the op used at its DECLARED arity —
        // is gated as a condition (`f(args)` ≡ `eq(f(args), true)` for a Bool op).
        // The FUNCTIONAL-RELATION form `f(args, result)` (arity + 1, the extra arg
        // is the result column — e.g. stdlib `needs_rebuild`'s
        // `status(?fs, ?p, FileStatus(…))` ≡ `eq(status(?fs, ?p), result)`) is a
        // pre-existing relational pattern WI-583 does not touch, and any other count is
        // the arity verdict's, taken above — skip any call whose arity ≠ the op's
        // parameter count.
        if provided != sig.params.len() || names_result {
            continue;
        }
        // Classify the return sort HEAD. Only a CONCRETE non-Bool sort is a
        // category error. A non-concrete return (a bare type parameter or
        // projection — `sort_functor_of_view` = `None`) cannot be proven non-Bool
        // (it may instantiate to `Bool` at a call site), so it is left alone, not
        // flagged — avoiding a false positive on a generic op like
        // `run[T](t: Thunk[T]) -> T`. A `Bool` return (by short name, exactly as
        // `bare_bodied_bool_relation` compares) is gated to `eq(op(args), true)`
        // by the resolver, so it is not an error either.
        let Some(return_sort) = sort_functor_of_view(kb, &sig.return_type) else {
            continue;
        };
        if kb.sort_sym_is_bool(return_sort) {
            continue;
        }
        // A non-Bool op that is ALSO rule-backed reads as the RELATION (the
        // rule-less gate of design §3.3 / `bare_bodied_bool_relation`): its rules
        // are its relational definition, so it resolves relationally, not an
        // error. The borrowing `rules_by_functor_iter` short-circuits at the first
        // rule — no `Vec` alloc for this cold, per-op check.
        if kb.rules_by_functor_iter(f).next().is_some() {
            continue;
        }
        errors.push((
            TypeError::NonBoolOpInGoalPosition {
                span: Some(o.span.span),
                op_sym: f,
                return_sort,
            },
            Some(o.span.source),
        ));
    }
}

/// WI-20260822-NDG34 — the verdict on a const written as a goal that the loader left
/// standing (see [`check_rule_body_goal_readings`]'s fourth shape). An applied `Bool` const
/// (`flag()`), or one of a function type, is the call refused everywhere else; any other
/// const of another type names no truth, applied or not, and its repairs are the data
/// ones. `None` for a `Bool` const whose known value is of another type: its declaration
/// is refused for that already, and a second error here would say the same thing worse.
fn const_goal_error(kb: &mut KnowledgeBase, goal: &Rc<NodeOccurrence>) -> Option<TypeError> {
    use crate::kb::load::ConstGoalProblem;
    let span = Some(goal.span.span);
    let expr = goal.as_expr()?;
    let (name, applied) = match expr {
        Expr::Ref(c) | Expr::Ident(c) => (*c, false),
        _ => (expr_call_parts(expr)?.0, true),
    };
    let ty = kb
        .const_type(name)
        .cloned()
        .expect("a loaded const has its declared type (`Loader::load_const`)");
    let problem = if kb.const_type_is_bool(name) {
        if applied {
            return Some(TypeError::UnknownApplyFunctor { span, name });
        }
        match kb.const_slot_value(name) {
            Err(unavailable) => ConstGoalProblem::ValueUnavailable {
                reason: unavailable.describe(kb, name),
            },
            Ok(Literal::Bool(_)) => ConstGoalProblem::NotFolded,
            Ok(_) => return None,
        }
    } else if applied && type_is_callable(kb, &ty) {
        return Some(TypeError::UnknownApplyFunctor { span, name });
    } else {
        ConstGoalProblem::NotBool {
            ty: type_display_name_value(kb, &ty),
        }
    };
    Some(TypeError::ConstInGoalPosition {
        span,
        name,
        problem,
    })
}

/// The verdict on a QUERY's call of the operation `functor`: its arguments fill the parameter
/// list, as a clause's call is judged at load — by the same binder and verdict
/// ([`bind_call_arguments`], [`call_arity_error`]), so the two cannot come to admit different
/// spellings. A query has no typer and no other check; before this, a call with too few was
/// folded to the name or left undecided, and one with too many was read by its first
/// arguments (WI-20261030-4BXDW). At a goal (`at_goal`) the positional result column is
/// admitted, and a `result:` label, which a query does not read, is refused; in a value slot a
/// `result:` label names no parameter, as anywhere. One refusal is the query's own: a parameter
/// left out for its default, which the typer fills (proposal 069) and nothing does in a query —
/// `?r <=> g()` over `g(n: Int64 = 5)` bound the name `g`. Declined, as at a clause's goal: an
/// operation with a variadic capture, whose labels the typed call folds into the capture.
pub(crate) fn query_call_arity_error(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    pos_count: usize,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    at_goal: bool,
    span: Span,
) -> Option<TypeError> {
    if kb.op_capture_param(functor).is_some() {
        return None;
    }
    let rec = crate::kb::op_info::lookup_operation_info(kb, functor)?;
    let span = Some(span);
    if at_goal && named_args.iter().any(|(label, _)| is_result_label(kb, *label)) {
        return Some(TypeError::Other {
            site: TypeError::here(),
            span,
            context: TypeErrorContext::OperationArgument {
                op_name: functor,
                param: kb.intern("result"),
            },
            expected: "the result written as one more positional argument, after the call's \
                       own — a query reads no `result:` column"
                .to_string(),
            actual: "a `result:` label".to_string(),
        });
    }
    let mut binding =
        bind_call_arguments(kb, &rec.params, pos_count, named_args, functor, "this operation", span);
    let mut found = std::mem::take(&mut binding.label_errors);
    let pos = if at_goal { NodePos::RuleBodyGoal } else { NodePos::Value };
    found.extend(call_arity_error(
        kb,
        &rec.params,
        &binding,
        pos_count + named_args.len(),
        None,
        functor,
        pos,
        span,
    ));
    if found.is_empty() {
        // Positional arguments rank among the parameters no label names
        // ([`positional_param_indices`]), so the one left out is the first of those past them.
        let left_out = rec
            .params
            .iter()
            .filter(|(param, _)| !named_args.iter().any(|(label, _)| same_label(kb, *param, *label)))
            .nth(pos_count);
        if let Some((param, _)) = left_out {
            found.push(TypeError::Other {
                site: TypeError::here(),
                span,
                context: TypeErrorContext::OperationArgument {
                    op_name: functor,
                    param: *param,
                },
                expected: "an argument for every parameter — a query has no typer to fill a \
                           parameter's default: write the argument"
                    .to_string(),
                actual: format!(
                    "the call leaving `{}` out",
                    short_name_of(kb.local_name_of(*param))
                ),
            });
        }
    }
    (!found.is_empty()).then(|| aggregate_errors(found))
}

/// The verdict on a goal that CALLS a rule-less operation: its arguments fill the
/// operation's parameter list (kernel §5.4) — at the declared arity, a `Bool` operation's
/// condition, or, with no label, with one positional argument more: the functional-relation
/// view's result column (§5.3). Judged by the binder and the verdict a spec operation's goal
/// gets from the typer ([`bind_call_arguments`], [`call_arity_error`]), so the two kinds of
/// callee cannot come to admit different spellings.
///
/// Such a goal reached no check before: the rule-body walk leaves a subgoal no clause
/// heads to the pass that owns a name defined nowhere, which an operation is not, and
/// [`check_goal_atom_reading`] read a goal at the declared arity only. So
/// `Util.sub2(1, ?r, y: 5)` — a label, and a positional argument no parameter takes —
/// loaded and answered nothing, where the same spelling on a spec operation was refused.
///
/// Declined: an operation with a variadic capture, whose labels the typed call path folds
/// into the capture — a goal on one is read as before.
fn operation_goal_arity_error(
    kb: &mut KnowledgeBase,
    goal: &Rc<NodeOccurrence>,
) -> Option<TypeError> {
    let Some(Expr::Apply {
        functor,
        pos_args,
        named_args,
        ..
    }) = goal.as_expr()
    else {
        return None;
    };
    if kb.op_capture_param(*functor).is_some() {
        return None;
    }
    let rec = crate::kb::op_info::lookup_operation_info(kb, *functor)?;
    let span = Some(goal.span.span);
    // A column named `result:` is the goal's result, not an argument (proposal 069 §1.1).
    let named_args: Vec<(Symbol, Rc<NodeOccurrence>)> = named_args
        .iter()
        .filter(|(label, _)| !is_result_label(kb, *label))
        .cloned()
        .collect();
    let named_args = named_args.as_slice();
    let mut binding = bind_call_arguments(
        kb,
        &rec.params,
        pos_args.len(),
        named_args,
        *functor,
        "this operation",
        span,
    );
    let mut found = std::mem::take(&mut binding.label_errors);
    found.extend(call_arity_error(
        kb,
        &rec.params,
        &binding,
        pos_args.len() + named_args.len(),
        None,
        *functor,
        NodePos::RuleBodyGoal,
        span,
    ));
    (!found.is_empty()).then(|| aggregate_errors(found))
}

/// WI-20260923-32XFQ — every in-body `find_dictionary(instance, …)` read under `occ` a
/// declaration gave — a guard's — handed its slot-0 INSTANCE, in the walk's order. An inferred
/// read is no declaration, at the top of a body or in a connective's goal slot
/// ([`is_inferred_requirement_read`]).
/// Iterative (explicit stack) so a deeply-nested body cannot overflow the host stack.
fn for_each_find_dictionary_instance(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    fd_sym: Symbol,
    mut visit: impl FnMut(&Rc<NodeOccurrence>),
) {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(occ)];
    while let Some(o) = stack.pop() {
        if is_inferred_requirement_read(kb, &o) {
            continue;
        }
        let Some(expr) = o.as_expr() else { continue };
        if let Expr::Apply {
            functor, pos_args, ..
        } = expr
        {
            if *functor == fd_sym {
                if let Some(instance) = pos_args.first() {
                    visit(instance);
                }
            }
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
}

/// Push the canonical spec base of every in-body `find_dictionary` read reachable under
/// `occ` into `out` (see [`check_rule_body_requirements`]). The spec base is the read's first
/// positional arg, reduced to `Eq` via [`occ_head_symbol`]. Iterative walk so a
/// deeply-nested body cannot overflow the host stack.
fn collect_find_dictionary_bases(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    fd_sym: Symbol,
    out: &mut SmallVec<[Symbol; 2]>,
) {
    for_each_find_dictionary_instance(kb, occ, fd_sym, |instance| {
        if let Some(base) = occ_head_symbol(instance) {
            let canon = kb.canonical_sort_sym(base);
            if !out.contains(&canon) {
                out.push(canon);
            }
        }
    });
}

/// Walk `occ` for spec-op Apply calls and push a `MissingRequiresForSpecOp` for
/// each whose requirement is statically missing (see
/// [`check_rule_body_requirements`]). Iterative (explicit stack) so a deeply-nested
/// body cannot overflow the host stack.
fn check_occ_spec_op_requirements(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    fd_sym: Option<Symbol>,
    declared: &[Symbol],
    errors: &mut Vec<TypeError>,
) {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(occ)];
    while let Some(o) = stack.pop() {
        let Some(expr) = o.as_expr() else { continue };
        // A spec-op call carries a functor + args in any of the three functor-bearing
        // forms `occ_head_symbol` / the sibling `simp_fire_guard_holds` recognize
        // (Apply, plus a Constructor/Instantiation that materialized a spec-op head).
        // `find_dictionary` is itself a builtin goal (its args carry the witness
        // `Ref(op)` and carrier vars, not a call) — never a spec op, so skip it.
        if let Some((functor, pos_args, named_args)) = expr_call_parts(expr) {
            if Some(functor) != fd_sym {
                // WI-883 — a DEFAULTED member too: its default's sibling calls need the
                // carrier's instance exactly as a body-less call does, when the spec has an
                // ABSTRACT member — asked on the failure path only, inside.
                let spec_sort = lookup_spec_op_dispatch(kb, functor)
                    .map(|s| (s, false))
                    .or_else(|| defaulted_spec_op_parent(kb, functor).map(|s| (s, true)));
                if let Some((spec_sort, defaulted)) = spec_sort {
                    check_one_spec_op_requirement(
                        kb, &o, functor, pos_args, named_args, spec_sort, defaulted, declared,
                        errors,
                    );
                }
            }
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
}

/// Decide one rule-body spec-op call (see [`check_rule_body_requirements`]),
/// pushing `MissingRequiresForSpecOp` iff its requirement is statically missing.
pub(super) fn check_one_spec_op_requirement(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    spec_sort: Symbol,
    // WI-883 — `functor` has a body: a DEFAULTED member, which owes an instance only when
    // its spec has an abstract member ([`spec_has_an_abstract_member`]).
    defaulted: bool,
    declared: &[Symbol],
    errors: &mut Vec<TypeError>,
) {
    // A spec op registered as a resolver BUILTIN never fails for a *missing spec
    // instance*, so it is not this pass's concern — skip it. Two disjoint reasons,
    // both `is_builtin`:
    //   * `PartialEq.eq`/`PartialEq.neq` (SemEq) — structural equality IS the default
    //     `PartialEq` instance (kernel-language.md §equality / proposal 051 / WI-616: "a
    //     carrier with no override keeps the structural compare — structural equality
    //     *is* its instance"), so EVERY carrier already satisfies `PartialEq`; a carrier
    //     wanting non-structural equality *overrides* it (`Set.eq`/`Map.eq`, `Float`'s
    //     IEEE `eq`), and the explicitly structural test is `===`/`struct_eq`. Never a
    //     missing requirement.
    //
    //     `PartialEq`, NOT `Eq`, AND THE DIFFERENCE IS NOT PEDANTRY. This sentence said
    //     "EVERY carrier already satisfies `Eq`" until WI-879, and that is FALSE — the
    //     tree ENFORCES that it is false. `Float` provides `PartialEq`, `PartialOrd` and
    //     `NonEq` and deliberately not `Eq` (WI-644 / proposal 004), to the point that
    //     WI-658 makes a user's `provides Eq[Float]` a LOAD ERROR; and WI-664 derives
    //     `NonEq` for every COMPOSITE carrying a `Float` field, so a plain
    //     `Point(x: Float, y: Float)` is one too. A class, not one carrier. The claim
    //     this early return NEEDS is the one about the partial BASE, which is total and
    //     which `PartialEq.eq` is the operation of — so the return was always safe and
    //     only its reason was wrong. A WI-644 leftover: the citation is WI-616, which
    //     predates the split that the registration site states two lines above ("eq/neq
    //     live on PartialEq, gt/lt/gte/lte on PartialOrd (the partial bases); Eq/Ord are
    //     the lawful/total markers").
    //   * `Ord.gt`/`lt`/`gte`/`lte`, `Numeric.add`/`sub`/`mul` — numeric-constant
    //     builtins (`builtin_cmp` / arithmetic) that NEVER consult an `Ord`/
    //     `Numeric` instance, so a `requires Ord[…]` could not even fix them; a
    //     non-numeric carrier is a plain resolution failure, not a missing dictionary.
    //     (Why stdlib `needs_rebuild`'s `gt` on two `Timestamp`s must not be flagged.)
    //   * WI-883 — and any callee the HOST owes ([`host_implements`]): an `operation_map`
    //     entry or `@[host_implemented]` claim on the operation itself serves every
    //     carrier, as the operation-body refusal already reads it. Two predicates for one
    //     question made a call's verdict depend on which body it was written in.
    if host_implements(kb, functor) {
        return;
    }
    // Only a spec op with a CARRIER parameter grounds its instance from its
    // arguments; a nullary / all-content op (`Monoid.unit()`) never can, so its
    // requirement is not decidable from a body call — the same op the WI-300
    // witness scan skips ([`op_has_spec_carrier_param`]).
    if !op_has_spec_carrier_param(kb, functor, spec_sort) {
        return;
    }
    // Host built-ins (stdlib specs with zero providers by design — `Map`, `List`,
    // `Stream`) resolve their ops directly at runtime; only a spec that warrants
    // the abstract check (≥1 provider, or a user-defined spec) can be statically
    // missing. The SAME gate the WI-325 op-body diagnostic uses.
    if !spec_warrants_abstract_check(kb, spec_sort) {
        return;
    }
    // The rule explicitly declares this requirement in its body — its own WI-300
    // dictionary. Respect it (never flag; the fire-time guard handles satisfaction).
    //
    // Exact-symbol match, NOT transitive coverage: a declared `requires(Eq[T])` does
    // NOT suppress a call to a non-builtin op whose spec merely lies in `Eq`'s
    // requires-chain, because `declared` carries only spec SYMBOLS (no type-args) — it
    // cannot tell that the declared `Eq[T]` and the op's carrier are the SAME type. A
    // carrier-blind transitive suppression would hide a genuine missing instance when
    // the op is applied to a different carrier than the declared requirement ranges
    // over (`requires(Ord[A])` does not cover a `PartialEq` op applied to some
    // unrelated `B`). This exact-match is SOUND (it never wrongly suppresses) but
    // INCOMPLETE (it over-diagnoses a transitively-covered non-builtin op). Direction
    // A's own witnesses (`eq`/`gt`) are builtins, returned above at the `is_builtin`
    // gate, so they never reach here regardless — hence no current driver.
    //
    // WI-653 DELIVERED the reusable carrier-alignment mechanism this needs
    // ([`op_requires_covers`] / [`compose_reached_carrier_map`] /
    // [`reached_carrier_matches_call`] — thread the declared requirement's carrier
    // through the requires chain and σ-align it with the call's). Wiring it here (a
    // carrier-aware transitive suppression: collect `declared` WITH carriers in
    // `collect_find_dictionary_bases`, read the call carrier as this fn already does
    // below) is a clean follow-up gated on an actual driver — deferred to keep the
    // exact-match's soundness until one exists.
    if declared.contains(&kb.canonical_sort_sym(spec_sort)) {
        return;
    }
    let (outcome, refusal) =
        spec_op_call_carrier_outcome(kb, functor, pos_args, named_args, spec_sort);
    // `Fire` (satisfiable) and `Suspend` (under-determined) are never errors —
    // only a ground carrier that provides no instance is statically missing.
    if !matches!(outcome, FindDictOutcome::DontFire) {
        return;
    }
    // WI-883 — A CONCRETE CARRIER IS SAID SO. `MissingRequiresForSpecOp` is the ABSTRACT
    // case's sentence ("covering abstract type parameter … on enclosing sort"), which is
    // wrong on both counts here: the carrier is a ground sort and a rule has no enclosing
    // sort to annotate. `UnfillableOperationRequirement` is the rule-body sentence for
    // exactly this — the carrier provides no such spec and the clause declares no
    // `requires(…)` — and its two repairs are the two that exist. The degenerate
    // `DontFire` (no operation record) names no carrier and keeps the old one.
    // WI-883 — A DEFAULTED member is owed an instance only when its spec has an ABSTRACT
    // one, and never at the REFLEXIVE carrier: a sort's own member on its own value
    // (`Box.twice(box(1))`) reads the self-receiver `b: Box` as the carrier, and
    // `sort_provides(Box, Box)` is false — so without this it was refused "`Box` provides no
    // `Box`", a repair that is not one (measured). Asked HERE, on the failure path, because
    // the abstract-member walk visits every operation of the spec (found by /code-review:
    // every rule-body call to a defaulted `List` member paid it).
    if defaulted
        && (!spec_has_an_abstract_member(kb, spec_sort)
            || matches!(refusal, Some(GuardRefusal::Carrier(c)) if same_sort_canonical(kb, c, spec_sort)))
    {
        return;
    }
    match refusal {
        Some(GuardRefusal::Carrier(carrier_sym)) => {
            errors.push(TypeError::UnfillableOperationRequirement {
                span: Some(occ.span.span),
                callee_op: functor,
                spec_sort_sym: spec_sort,
                carrier_sym,
            });
            return;
        }
        // WI-20260925-PRVA2 (c) — carriers no provision binds TOGETHER are said so: the
        // per-carrier sentence named whichever carrier was read last, and "`String` provides
        // no `Conv`" is false of a provision's second binding (and of a sort that does provide
        // `Conv`, at other bindings).
        Some(GuardRefusal::NoProvision(bindings)) => {
            errors.push(TypeError::NoProvisionAtCarriers {
                span: Some(occ.span.span),
                callee_op: functor,
                spec_sort_sym: spec_sort,
                bindings: bindings.into_vec(),
            });
            return;
        }
        None => {}
    }
    // Statically missing → `MissingRequiresForSpecOp` (WI-325), the same diagnostic
    // the op-body pass raises; the spec's type-param short names drive the
    // `requires {Spec}[{T = …}]` suggestion.
    let spec_qn = kb.qualified_name_of(spec_sort).to_string();
    let abstract_params: SmallVec<[Symbol; 2]> = kb
        .type_params_of_sort(spec_sort)
        .iter()
        .filter_map(|short| kb.try_resolve_symbol(&format!("{spec_qn}.{short}")))
        .collect();
    errors.push(TypeError::MissingRequiresForSpecOp {
        span: Some(occ.span.span),
        spec_op_sym: functor,
        spec_sort_sym: spec_sort,
        abstract_params,
        site: RequiresSite::Clause,
    });
}

/// The CARRIER DECISION for one rule-body call to a spec operation — `Fire` (its carriers have
/// an instance), `Suspend` (a carrier is not known at load) or `DontFire` (the known carriers
/// can have none) — with what decided a `DontFire` ([`GuardRefusal`]): the carrier that
/// provides nothing, or the carriers no provision binds together (WI-20260925-PRVA2 (c)).
///
/// Read by [`check_one_spec_op_requirement`], which refuses the `DontFire` ones: a known
/// carrier no provision binds. The calls it leaves are the typer's to classify; the inference
/// weaves the ones the typer leaves to the clause ([`ClauseCondition`]).
fn spec_op_call_carrier_outcome(
    kb: &KnowledgeBase,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    spec_sort: Symbol,
) -> (FindDictOutcome, Option<GuardRefusal>) {
    // Fold the call's positional + named arguments into the op's declared PARAMETER
    // order, so the carrier reader indexes them the way `simp_guard_holds_core`
    // iterates parameters, so the static and runtime carrier decisions cannot disagree. A
    // partial call (some parameter unprovided) aligns to `None`; every arg then reads
    // headless → `Suspend` (declined, never a spurious error). Without this, a carrier
    // supplied BY NAME (or a positional arg displaced by an earlier named one) would
    // be read at the wrong index — missing a real requirement, or flagging the wrong
    // argument's sort.
    let aligned = crate::kb::op_info::lookup_operation_info(kb, functor)
        .and_then(|rec| align_call_args_to_params(kb, &rec.params, pos_args, named_args));
    aligned_carrier_outcome(kb, functor, aligned.as_deref(), spec_sort)
}

/// [`spec_op_call_carrier_outcome`] over arguments already in PARAMETER order — `None` for
/// a partial call, whose every argument then reads headless.
fn aligned_carrier_outcome(
    kb: &KnowledgeBase,
    functor: Symbol,
    aligned: Option<&[Rc<NodeOccurrence>]>,
    spec_sort: Symbol,
) -> (FindDictOutcome, Option<GuardRefusal>) {
    // Read each carrier parameter's argument sort head from the `inferred_type`
    // `type_rule_bodies` stamped (WI-603), like [`simp_fire_guard_holds`], and treat
    // two carrier shapes as headless (`None` → `Suspend`), never as a concrete sort
    // failing `sort_provides` (`Some(_)` → a spurious `DontFire`):
    //   * an ABSTRACT type-param (`?x : Eq.T`) — a legitimately-polymorphic rule
    //     that propagates its requirement (WI-292; `is_sort_param_symbol`);
    //   * an ABSTRACT SPEC sort (`s : Stream`, the spec's own interface with no
    //     concrete representation) — the runtime value is some concrete provider, so
    //     the real impl is resolved by eval's value-directed dispatch, not by the
    //     spec sort's own (unsatisfiable) provider set. This is the rule-body peer of
    //     the finiteness-cluster deferrals (WI-598/601/608/609) `check_apply_iter`
    //     takes before its `NoCandidates` arm; `sort_provides` sees a sort as NOT
    //     providing ITSELF, so without this a self-receiver call (`splitFirst(s)` on
    //     a `Stream`) reads as a spurious `DontFire` ([`carrier_is_abstract_spec`]).
    //
    // A WITNESS-PROVIDED carrier is KNOWN here, as it is to the run-time read. It was filed
    // as unknown (P7VP4's third review round) because the per-carrier question then walked
    // on to a multi-parameter provision's other carriers and refused them; the core asks the
    // provision there now (WI-20260925-PRVA2 (c)), and the filter had turned into a hidden
    // refusal: with `sort W provides Conv[A = Leaf, B = Int64]` beside `sort Meters provides
    // Conv[A = Meters, B = String]`, a rule-body `Conv.conv(leaf(), "s", ?r)` read `Leaf` as
    // unknown, `B = String` matched Meters' row, and the call LOADED — and answered `9`,
    // `W.conv` dispatched at `(Leaf, String)`.
    simp_guard_decision(kb, functor, spec_sort, |i| {
        aligned
            .and_then(|args| args.get(i))
            .and_then(|a| a.inferred_type())
            .and_then(|t| sort_functor_of_view(kb, &t))
            .filter(|s| !is_sort_param_symbol(kb, *s) && !carrier_is_abstract_spec(kb, *s))
    })
}

/// WI-1043 — is `carrier` an instance of `spec_sort` through a WITNESS provision, i.e.
/// one that ANOTHER sort declares for it (`sort Rival provides Desc[T = Leaf]`, WI-450)?
///
/// [`sort_provides`] walks the CARRIER'S OWN out-edges, and a witness provision is not
/// one of them — it is filed under the witness. So the two answers differ exactly on
/// this shape, and a guard asking `sort_provides` alone reads a witness-supplied carrier
/// as having no instance.
///
/// ONE READER: the shared guard core's per-carrier question ([`simp_guard_decision`]) asks
/// [`carrier_provides_spec`] — own edges OR this — since WI-20260925-P7VP4, so the WI-300/1040
/// run-time read, the load check ([`spec_op_call_carrier_outcome`]) and BOTH `@[simp]` guards
/// (the typer's `simp_fire_guard_holds`, the resolver's `simp_requires_guard_holds`) FIRE for
/// a witness-supplied carrier: this ACCEPTS a dispatch, and a law rewrites at it. The core asks
/// it only of carriers at the spec's CARRIER parameter; a carrier elsewhere asks the provision
/// (WI-20260925-PRVA2 (c)). The load check no longer files such a carrier as unknown — see
/// [`aligned_carrier_outcome`].
///
/// A LOAD REFUSAL OF A LEGAL PROGRAM, MEASURED both before and after WI-1043's widening:
/// `sort Rival provides Desc[T = Leaf]` supplying a body-less `Desc.describe`, called as
/// `leaf().describe(?r)` from a rule body, was refused with "missing `requires Desc[T =
/// …]`" — while the SAME call in an operation body loads and answers the supplied `9`.
///
/// `witness_dispatch_carrier` is the ONE owner of "what counts as a witness, and for
/// which carrier", shared with [`provision_supplier`]; it answers `None` for a provider
/// that IS its own carrier, which is `sort_provides`' own case.
///
/// BINDING-BLIND, EXACTLY AS [`sort_provides`] IS. This asks whether SOME witness provision
/// of the spec names this carrier, not whether one does at the call's other type arguments
/// — so for a multi-parameter spec a provision at `Desc[T = Leaf, U = Int64]` answers for a
/// call whose `U` is `String`, when no CARRIER of the call stands at `U` (one that does is
/// asked the provision instead, WI-20260925-PRVA2 (c)). Through the guard core it FIRES the
/// guard, and the dictionary is then resolved at the call's own types (`fetch_dictionary`),
/// where a provision at other arguments answers nothing and the read is UNDECIDED rather
/// than wrong; a `@[simp]` law has no such second step, and rewrites. Closing it means giving
/// the check the call's σ, which the guard reads only as argument SORT HEADS today — the same
/// input WI-653's carrier-alignment machinery wants (see the WI-653 note in
/// [`check_one_spec_op_requirement`]).
pub(super) fn carrier_provided_by_witness(
    kb: &KnowledgeBase,
    spec_sort: Symbol,
    carrier: Symbol,
) -> bool {
    let carrier_canon = kb.canonical_sort_sym(carrier);
    if let Some(carriers) = remembered_witness_carriers(kb, spec_sort) {
        // WI-20261010-ANK4X — the memo held to its definition, under the index's control.
        if agreement_on() {
            let walked = witness_carriers_of(kb, spec_sort);
            assert!(
                carriers.as_ref() == walked.as_slice(),
                "ANTHILL_PROVIDES_INDEX_AGREEMENT: the witness carriers remembered for \
                 `{}` are {:?}, and its provision rows give {:?}",
                kb.qualified_name_of(spec_sort),
                carriers,
                walked,
            );
        }
        return carriers.contains(&carrier_canon);
    }
    let carriers: Rc<[Symbol]> = witness_carriers_of(kb, spec_sort).into();
    let hit = carriers.contains(&carrier_canon);
    remember_witness_carriers(kb, spec_sort, carriers);
    hit
}

/// The canonical carriers `spec_sort`'s WITNESS provisions dispatch at — the one criterion,
/// `witness_dispatch_carrier`, over each of its rows. See [`ProvidesIndex`]'s
/// `witness_carriers`, which memoizes it.
fn witness_carriers_of(kb: &KnowledgeBase, spec_sort: Symbol) -> Vec<Symbol> {
    provides_rows_of_spec(kb, spec_sort)
        .filter_map(|row| witness_dispatch_carrier(kb, spec_sort, row.provider, &row.spec_view))
        .collect()
}

/// Is `spec` a `SortView` wrapper? [`is_sort_view_functor`] of its head, so the witness-gate
/// helper and the unwrapper cannot disagree on what counts as a view. Carrier-agnostic
/// (WI-662): one discriminant for a ground `Value::Term` spec and a denoted `Value::Entity`
/// spec carrier alike.
pub(super) fn view_is_sort_view(kb: &KnowledgeBase, spec: &impl TermView) -> bool {
    matches!(spec.head(kb), ViewHead::Functor { functor: f, .. } if is_sort_view_functor(kb, f))
}

/// The spec + short symbols for the `eq`/`neq` family, resolved once per
/// [`check_eq_override_backing`] run. `eq_short` is the sort-ops key
/// (`kb.intern("eq")`, as [`carrier_own_op`]'s callers use); the `*_spec`s are
/// the canonical `PartialEq.eq`/`PartialEq.neq` builtins the call functor is matched against.
/// Only the EQ override's backing is probed — a `neq` call dispatches through the
/// carrier's `eq` override too (`sem_eq_dispatch` resolves `eq_dispatch_target`
/// for both, negating the verdict), so there is no distinct `neq` override to key.
/// Since WI-1125 that last clause is ENFORCED rather than merely true in practice:
/// a carrier supplying its own `neq` is refused at load
/// ([`crate::kb::load::LoadError::CarrierSuppliesNeq`]), so no program reaching this
/// pass can hold one for this probe to have missed.
pub(super) struct EqFamilySyms {
    eq_spec: Symbol,
    eq_short: Symbol,
    neq_spec: Option<Symbol>,
    /// The `PartialEq` / `Eq` spec sorts. A carrier is only a genuine unbacked-eq
    /// OVERRIDE if it SELF-PROVIDES one of these (Map's `provides Eq[T = Map]`); a
    /// spec that merely DECLARES its own `eq` op does not, and must not be flagged.
    partial_eq_sort: Option<Symbol>,
    eq_sort: Option<Symbol>,
}

/// WI-650 — flag a semantic `PartialEq.eq`/`PartialEq.neq` (`=`/`neq`) call whose operand's
/// inferred sort declares its OWN `eq` override with NO backing (a bodyless
/// placeholder — `Map` once its relational eq/binds/strip_is apparatus was dropped
/// in favor of the WI-625 host bridge). Such a call type-checks (`PartialEq.eq` is a total
/// builtin, so [`check_one_spec_op_requirement`] — this pass's `is_builtin`-skipped
/// sibling — never flags a missing requirement) yet would SILENTLY misdecide at
/// resolution: `sem_eq_dispatch` targets the empty override, exhausts, and returns
/// "not equal". `BuiltinResult` has no error channel, so this is the loud TYPE-TIME
/// face (`EqOverrideUnbacked`).
///
/// Walks BOTH rule bodies (operand types stamped by [`type_rule_bodies`], WI-603)
/// and operation bodies (stamped by the `push_visit` Stamp frame), reading each
/// operand's `inferred_type` head exactly as `check_one_spec_op_requirement` reads
/// its carrier args. Per use-site: the stdlib never compares maps, so it stays
/// clean; only user code comparing an unbacked-override carrier errors.
///
/// Both `eq` AND `neq` over two Maps are flagged: `neq(?a, ?b)`'s var operands are
/// stamped `Map` by the same WI-603 var-leaf inference `eq` uses, so a `neq(map, map)`
/// goal or op body errors identically (WI-651 — an earlier worry that `neq`
/// under-determines its operand to the abstract param `Map.K` was investigated and
/// found false; that `Map.K` was Map's OWN key comparison `neq(?k, ?k2)`, where the
/// operands genuinely ARE keys of type `K`).
///
/// Three detection channels close the WI-652 gaps over WI-650's original var-leaf
/// case:
///   - the STAMPED type of a var-leaf operand ([`operand_unbacked_eq_carrier`], A1);
///   - a COMPOUND operand's head result sort (`put(…)`, `build_map(x)` — un-stamped
///     in a rule body, A2), same helper;
///   - a DOT-form `m.eq(n)`, rewritten to `Map.eq(m, n)` whose functor is the
///     carrier's own `eq` op, read straight off the functor ([`own_eq_op_carrier`]).
/// These run over rule bodies, op bodies, AND constraint/guard bodies (the last
/// carrier-agnostically over the untyped `LogicalQuery` Value — [`check_value_eq_override_backing`]).
///
/// Two escape routes remain deliberately OPEN (both need a concrete operand sort
/// this load-time check cannot see): a POLYMORPHIC operand typed by an abstract `T`
/// (`same(a: T, b: T) = eq(a, b)` at `T = Map`) never concretizes to `Map`; and a
/// BARE-VAR operand inside a CONSTRAINT (`constraint c :- eq(?m, ?n)`) has no stamped
/// type — a guard stores an untyped `Value`, so only the compound/dot channels reach
/// it. A future WI-625 host bridge that registers `Map.eq` AS a resolver builtin
/// must update the backing predicate ([`eq_override_backed`] deliberately drops the
/// builtin leg today, so it would then read a bridged `Map.eq` as still-unbacked).
pub(super) fn check_eq_override_backing(kb: &mut KnowledgeBase) -> Vec<TypeError> {
    let mut errors: Vec<TypeError> = Vec::new();
    // The semantic eq/neq spec symbols. WI-644 split: the `eq`/`neq` ops live on
    // `PartialEq` (Eq is the lawful marker that requires it), so a body `eq`/`neq`
    // call carries `PartialEq.eq`/`PartialEq.neq` (== `kb.eq_functor()`), NOT the
    // pre-split `Eq.eq`/`Eq.neq` — keying on `Eq.eq` here would resolve to `None`
    // and silently disable the guard. Absent on a prelude-less minimal KB — then no
    // call can be one of them, so bail. The short name keys `sort_ops` (mirroring
    // `carrier_own_op`'s `kb.intern` callers); intern up front so the loops below
    // stay `&self`-read-only.
    let Some(eq_spec) = kb.try_resolve_symbol("anthill.prelude.PartialEq.eq") else {
        return errors;
    };
    let neq_spec = kb.try_resolve_symbol("anthill.prelude.PartialEq.neq");
    let syms = EqFamilySyms {
        eq_spec,
        eq_short: kb.intern("eq"),
        neq_spec,
        partial_eq_sort: impl_parent_of_op(kb, eq_spec),
        eq_sort: kb.try_resolve_symbol("anthill.prelude.Eq"),
    };
    // `PartialEq.neq` is matched alongside `PartialEq.eq` so a `neq(map, map)` goal or op body is
    // flagged identically — its var operands are stamped `Map` by the same WI-603
    // inference `eq` uses, and it misdecides through the SAME empty `Map.eq`
    // override (`sem_eq_dispatch` negates the verdict). WI-651 confirmed neq does
    // not escape (the `Map.K` an earlier note worried about was Map's own KEY
    // comparison `neq(?k, ?k2)`, correctly typed `K` and correctly not flagged).
    let is_eq_call = |f: Symbol| f == syms.eq_spec || Some(f) == syms.neq_spec;
    // WI-652 — equational-definition backing set (this guard's `eq=` leg; since
    // WI-818 narrowed `op_backed` to body│builtin, [`eq_override_backed`] is its
    // only reader), so a carrier that defines `eq` via `eq(?a,?b) = rhs` is not
    // flagged spuriously.
    let eq_defined = collect_eq_defined_ops(kb);
    // Memo per carrier sort — the same sort recurs across many call sites, and
    // the backing probe allocates a `rules_by_functor` Vec.
    let mut memo: std::collections::HashMap<Symbol, bool> = std::collections::HashMap::new();

    // Rule bodies (non-fact rules only; facts have no body to compare in).
    for rid in kb.live_rule_ids() {
        if kb.is_fact(rid) {
            continue;
        }
        for node in kb.rule_body_nodes(rid) {
            check_occ_eq_override_backing(
                kb,
                node,
                &is_eq_call,
                &syms,
                &eq_defined,
                &mut memo,
                &mut errors,
            );
        }
    }
    // Operation bodies — free namespace-level ops and sort ops alike (every op
    // with a body is type-checked and its occurrences stamped).
    for (_, body) in kb.op_bodies_iter() {
        check_occ_eq_override_backing(
            kb,
            body,
            &is_eq_call,
            &syms,
            &eq_defined,
            &mut memo,
            &mut errors,
        );
    }
    // WI-652 — constraint/guard bodies. A guard stores an untyped `LogicalQuery`
    // Value (no `NodeOccurrence`, no stamped `inferred_type`), never visited by
    // `live_rule_ids`, so it walks carrier-agnostically via `TermView`, reaching
    // the compound-operand and dot-form/own-op channels (a bare-var operand there
    // has no type to read — documented open above).
    for query in kb.guard_queries() {
        check_value_eq_override_backing(
            kb,
            &query,
            &is_eq_call,
            &syms,
            &eq_defined,
            &mut memo,
            &mut errors,
        );
    }
    errors
}

/// Walk `occ` for eq calls and push an `EqOverrideUnbacked` per call whose carrier
/// has an unbacked own `eq` override (see [`check_eq_override_backing`]). Iterative
/// (explicit stack) so a deeply-nested body cannot overflow the host stack. At most
/// one error per call site.
///
/// Two channels: (B) the call's OWN functor is an unbacked carrier's `eq` override
/// (`m.eq(n)` rewritten to `Map.eq(m, n)` — the dot-form gap), read via
/// [`own_eq_op_carrier`]; else (A) a semantic `PartialEq.eq`/`neq` call, whose
/// operands are probed by [`operand_unbacked_eq_carrier`] (stamped var-leaf type OR
/// compound-operand head result sort).
fn check_occ_eq_override_backing(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    is_eq_call: &impl Fn(Symbol) -> bool,
    syms: &EqFamilySyms,
    eq_defined: &std::collections::HashSet<Symbol>,
    memo: &mut std::collections::HashMap<Symbol, bool>,
    errors: &mut Vec<TypeError>,
) {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(occ)];
    while let Some(o) = stack.pop() {
        let Some(expr) = o.as_expr() else { continue };
        // A functor-bearing form, in any of the three shapes `occ_head_symbol`
        // recognizes (Apply, plus a Constructor/Instantiation that materialized a
        // spec-op head).
        if let Some((functor, pos_args, named_args)) = expr_call_parts(expr) {
            // (B) dot-form / direct own-op call: carrier read off the functor.
            if let Some(carrier) = own_eq_op_carrier(kb, functor, syms, eq_defined, memo) {
                errors.push(TypeError::EqOverrideUnbacked {
                    span: Some(o.span.span),
                    carrier_sort: carrier,
                });
            } else if is_eq_call(functor) {
                // (A) semantic eq/neq call: probe operands.
                for operand in pos_args.iter().chain(named_args.iter().map(|(_, a)| a)) {
                    if let Some(carrier) =
                        operand_unbacked_eq_carrier(kb, operand, syms, eq_defined, memo)
                    {
                        errors.push(TypeError::EqOverrideUnbacked {
                            span: Some(o.span.span),
                            carrier_sort: carrier,
                        });
                        break; // one diagnostic per call site
                    }
                }
            }
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
}

/// The operand's carrier sort IF it declares an unbacked own `eq` override
/// ([`carrier_has_unbacked_eq_override`]), else `None`. The carrier is read from
/// (A1) the operand's stamped `inferred_type` — a var leaf typed via a `Map`
/// param, the common shape shared with `check_one_spec_op_requirement` — OR, when
/// that is absent, (A2, WI-652) the operand HEAD's result sort for a COMPOUND
/// operand (`put(…)`, `build_map(x)`), which WI-603 leaves un-stamped in a rule
/// body. An abstract sort-param / abstract-spec carrier is ignored (a polymorphic
/// `T` never concretizes to `Map` at load time — a documented WI-652 open gap),
/// mirroring the sibling's operand filter.
fn operand_unbacked_eq_carrier(
    kb: &KnowledgeBase,
    operand: &Rc<NodeOccurrence>,
    syms: &EqFamilySyms,
    eq_defined: &std::collections::HashSet<Symbol>,
    memo: &mut std::collections::HashMap<Symbol, bool>,
) -> Option<Symbol> {
    let carrier = operand
        .inferred_type()
        .and_then(|ty| sort_functor_of_view(kb, &ty))
        .or_else(|| operand_head_result_carrier(kb, operand))?;
    unbacked_eq_carrier(kb, carrier, syms, eq_defined, memo)
}

/// WI-652 — `carrier` IF its own `eq` override is unbacked
/// ([`carrier_has_unbacked_eq_override`], memoized), else `None`. Shared by ALL
/// three detection channels (var-leaf / compound-head / dot-form own-op) so the
/// eligibility rule and the memo cannot drift between them. The eligibility gate —
/// the carrier must SELF-PROVIDE an Eq/PartialEq instance, which excludes an
/// abstract sort-param `T` and a spec that merely declares its own `eq` — lives in
/// [`carrier_has_unbacked_eq_override`] so the memo caches the full verdict.
fn unbacked_eq_carrier(
    kb: &KnowledgeBase,
    carrier: Symbol,
    syms: &EqFamilySyms,
    eq_defined: &std::collections::HashSet<Symbol>,
    memo: &mut std::collections::HashMap<Symbol, bool>,
) -> Option<Symbol> {
    let unbacked = *memo
        .entry(carrier)
        .or_insert_with(|| carrier_has_unbacked_eq_override(kb, carrier, syms, eq_defined));
    unbacked.then_some(carrier)
}

/// WI-652 (compound-operand gap) — the sort an operand's HEAD produces, for a
/// COMPOUND operand (`put(empty(), 1, 2)`, `build_map(x)`) that carries no stamped
/// `inferred_type` (WI-603 stamps only var leaves in a rule body). An operation
/// apply reads its declared `return_type`; a constructor/entity reads the sort it
/// builds. `None` for a var leaf / literal / abstract-headed result (the latter
/// correctly left unflagged — the abstract `T` open gap).
fn operand_head_result_carrier(kb: &KnowledgeBase, operand: &Rc<NodeOccurrence>) -> Option<Symbol> {
    let (head, _, _) = expr_call_parts(operand.as_expr()?)?;
    head_result_carrier(kb, head)
}

/// WI-652 — the sort produced by an operand HEAD functor: an operation's declared
/// `return_type`, or the sort a constructor/entity builds. Shared by the occurrence
/// probe ([`operand_head_result_carrier`]) and the guard-Value probe
/// ([`check_value_eq_override_backing`]). `None` for a functor that is neither an
/// operation nor a constructor, or whose result is abstract.
fn head_result_carrier(kb: &KnowledgeBase, head: Symbol) -> Option<Symbol> {
    if let Some(rec) = crate::kb::op_info::lookup_operation_info(kb, head) {
        return sort_functor_of_view(kb, &rec.return_type);
    }
    // BEHAVIOUR CHANGE, deliberate. This was
    // `sort_functor_of_view(kb, &kb.strict_parent_sort(head)?)`, and the strict
    // accessor then returned the parent TERM — usually the
    // nullary `Fn{P}` that `type_head` classifies as `TypeHead::Error` ("a bare
    // sort is `Ref(S)`, never `Fn{S}`"), so the branch answered `None`. But only
    // USUALLY: when the parent symbol was itself a constructor, WI-511's canon
    // stored `Ref(P)` and the same branch answered `Some(P)`. The result depended
    // on registration ORDER — the exact defect this migration removes. A
    // constructor's result carrier IS its sort (what the doc above already
    // claims). Consequence to know: a constructor-headed operand can resolve a
    // carrier in `check_value_eq_override_backing`, so a carrier with an unbacked
    // `eq` override can raise `EqOverrideUnbacked` at load where it previously
    // could not. The suite is green, i.e. no in-repo carrier is in that state.
    //
    // WI-946: the TOTAL belongs-to, and the "uniformly" this comment used to
    // claim was FALSE until then — the strict view still answered `None` for an
    // EPONYMOUS carrier, so exactly the under-report the migration set out to
    // remove survived for one §6.3 spelling. Measured: `eq(Boxy(v: 1), Boxy(v:
    // 2))` over a `sort Boxy { entity Boxy(…) }` whose own `eq` override is
    // unbacked loaded clean, while the sort-nested spelling raised
    // `EqOverrideUnbacked`.
    kb.sort_of_constructor(head)
}

/// WI-652 — walk a constraint/guard's untyped `LogicalQuery` Value for eq calls,
/// carrier-agnostically via [`TermView`]. A guard has no `NodeOccurrence` and no
/// stamped operand types, so only two channels apply: (B) the call's own functor is
/// an unbacked carrier's `eq` override ([`own_eq_op_carrier`]); and (A2) a
/// `PartialEq.eq`/`neq` call with a COMPOUND operand whose head produces an
/// unbacked-eq carrier ([`head_result_carrier`]). A bare-var operand
/// (`constraint c :- eq(?m, ?n)`) carries no type here and is left unflagged — a
/// documented WI-652 open gap. Iterative (explicit stack) to bound host-stack depth;
/// guard-derived diagnostics carry no span (guards store no source occurrence).
fn check_value_eq_override_backing(
    kb: &KnowledgeBase,
    query: &Value,
    is_eq_call: &impl Fn(Symbol) -> bool,
    syms: &EqFamilySyms,
    eq_defined: &std::collections::HashSet<Symbol>,
    memo: &mut std::collections::HashMap<Symbol, bool>,
    errors: &mut Vec<TypeError>,
) {
    let mut stack: Vec<Value> = vec![query.clone()];
    while let Some(v) = stack.pop() {
        let ViewHead::Functor {
            functor,
            pos_arity,
            ..
        } = v.head(kb)
        else {
            continue;
        };
        // (B) dot-form / own-op call: carrier read off the functor. Else (A2) a
        // semantic eq/neq call whose COMPOUND operand's head produces the carrier
        // (Values carry no stamped var-leaf type, so channel A1 does not apply).
        let mut probe_operands = false;
        if let Some(carrier) = own_eq_op_carrier(kb, functor, syms, eq_defined, memo) {
            errors.push(TypeError::EqOverrideUnbacked {
                span: None,
                carrier_sort: carrier,
            });
        } else if is_eq_call(functor) {
            probe_operands = true;
        }
        // Single pass over positional args: probe each as an (A2) operand (until the
        // one per-call-site diagnostic fires) AND push it for recursion.
        let mut flagged_operand = false;
        for i in 0..pos_arity {
            let Some(operand) = v.pos_arg(kb, i).map(|it| it.to_value()) else {
                continue;
            };
            if probe_operands && !flagged_operand {
                if let Some(carrier) = operand
                    .head(kb)
                    .functor_sym()
                    .and_then(|h| head_result_carrier(kb, h))
                    .and_then(|c| unbacked_eq_carrier(kb, c, syms, eq_defined, memo))
                {
                    errors.push(TypeError::EqOverrideUnbacked {
                        span: None,
                        carrier_sort: carrier,
                    });
                    flagged_operand = true;
                }
            }
            stack.push(operand);
        }
        for key in v.named_keys(kb) {
            if let Some(item) = v.named_arg(kb, key) {
                stack.push(item.to_value());
            }
        }
    }
}

/// WI-652 (dot-form gap) — if `functor` is a carrier's OWN `eq` override that is
/// UNBACKED, return that carrier, else `None`. A `receiver.eq(arg)` dot call is
/// rewritten to `op(receiver, arg)` with `op` the carrier's own `eq` op (`Map.eq`,
/// not `PartialEq.eq`), so the semantic `is_eq_call` functor test misses it; this
/// reads the carrier straight off the functor via [`impl_parent_of_op`]. The
/// `carrier_own_op` re-check pins `functor` as genuinely that carrier's `eq`
/// override (not a coincidentally `eq`-named op elsewhere), then defers to the
/// shared [`unbacked_eq_carrier`] — whose self-provides gate drops a spec that
/// merely declares its own `eq` (a `PartialEq.eq` default target reached via a
/// distinct spec's `MyEq.eq` functor) rather than spuriously flagging it.
pub(super) fn own_eq_op_carrier(
    kb: &KnowledgeBase,
    functor: Symbol,
    syms: &EqFamilySyms,
    eq_defined: &std::collections::HashSet<Symbol>,
    memo: &mut std::collections::HashMap<Symbol, bool>,
) -> Option<Symbol> {
    // Cheap pre-filter: only an op whose short name is `eq` can be an eq override.
    if short_name_of(kb.qualified_name_of(functor)) != "eq" {
        return None;
    }
    let carrier = impl_parent_of_op(kb, functor)?;
    if carrier_own_op(kb, carrier, syms.eq_spec, syms.eq_short) != Some(functor) {
        return None;
    }
    unbacked_eq_carrier(kb, carrier, syms, eq_defined, memo)
}

/// WI-650 — does `carrier` declare its OWN `eq` override (per [`carrier_own_op`])
/// that is UNBACKED — no runnable body AND no GENERAL SLD clause defining it?
///
/// Only the EQ override is probed, for both `eq` and `neq` call sites: `neq`
/// dispatches through the SAME carrier `eq` override (`sem_eq_dispatch` resolves
/// `eq_dispatch_target` and negates the verdict), so an unbacked `eq` is exactly
/// what makes a `neq(map, map)` misdecide too — there is no distinct carrier `neq`
/// override to consult.
///
/// Deliberately does NOT consult the spec-op builtin path (`is_builtin`, as
/// [`op_backed`] does): `PartialEq.eq` IS a resolver builtin, and admitting that backing
/// would mask exactly the empty override this check exists to catch. The carrier's
/// own op symbol (`Map.eq`) is itself never a builtin.
///
/// "Backed by rules" is NARROWER than "`rules_by_functor(own)` is non-empty" — see
/// [`rule_is_general_eq_clause`]: a rule counts only if it is a CATCH-ALL clause
/// (head positional args all variables), like `Set.eq`'s `eq(?a,?b) :- subset(…)`.
/// A compound-headed rule does NOT count, because `rules_by_functor(Map.eq)` is
/// polluted by Map's untagged `get(put(?m,?k2,?v),?k) = get(?m,?k) :- neq(?k,?k2)`
/// rewrite law: that law's `=` connective resolves to the in-scope `Map.eq` (WI-627's
/// short-name trap in reverse — `Map.eq` shadows `PartialEq.eq` inside the Map sort), so it
/// lands under `Map.eq` with a `get`-shaped head. It fires only for `get`-shaped
/// operands, never for two normal-form (`put`/`empty`) maps, so it provides no
/// general map equality — Map.eq stays genuinely unbacked.
///
/// WI-652 — probes via [`eq_override_backed`], whose legs (eq= admitted, builtin
/// dropped, rule tightened to a general clause) are documented there.
pub(super) fn carrier_has_unbacked_eq_override(
    kb: &KnowledgeBase,
    carrier: Symbol,
    syms: &EqFamilySyms,
    eq_defined: &std::collections::HashSet<Symbol>,
) -> bool {
    // A genuine unbacked-eq OVERRIDE requires the carrier to SELF-PROVIDE an
    // Eq/PartialEq instance (Map's `provides Eq[T = Map]`) — only then is its own
    // bodyless `eq` op an unimplemented instance override. A sort that merely
    // DECLARES its own `eq` (a spec's abstract requirement / default target — e.g.
    // a user `sort MyEq` with `operation eq(a: T, b: T) -> Bool`, or an abstract `T`
    // that provides nothing) is not a self-provided instance and must not be flagged.
    if !carrier_self_provides_eq(kb, carrier, syms) {
        return false;
    }
    let Some(own) = carrier_own_op(kb, carrier, syms.eq_spec, syms.eq_short) else {
        return false;
    };
    !eq_override_backed(kb, own, eq_defined)
}

/// WI-652 — does `carrier` SELF-PROVIDE an `Eq` or `PartialEq` instance (a
/// `provides Eq[T = carrier]` / `provides PartialEq[T = carrier]` fact)? Only then
/// does its own bodyless `eq` op denote an unimplemented instance OVERRIDE (the
/// `Map` case) rather than a spec's abstract `eq` DECLARATION. The check narrows the
/// guard (never widens it): every carrier it excludes was never a self-provided
/// instance, so no real misdecide is masked. `sort_provides` is transitive over
/// `provides` edges, so a carrier providing `Eq[carrier]` satisfies the `Eq` leg.
fn carrier_self_provides_eq(kb: &KnowledgeBase, carrier: Symbol, syms: &EqFamilySyms) -> bool {
    syms.eq_sort.is_some_and(|e| sort_provides(kb, carrier, e))
        || syms
            .partial_eq_sort
            .is_some_and(|pe| sort_provides(kb, carrier, pe))
}

/// WI-650 — is rule `r` a GENERAL clause defining `own`'s equality — head
/// `own(a, b, …)` whose positional args are ALL variables, so it matches any
/// operands (`Set.eq`'s `eq(?a, ?b) :- subset(…)`)? A compound-headed rule
/// (`Map.eq(get(…), get(…))`, the mis-attributed `=` rewrite law — see
/// [`carrier_has_unbacked_eq_override`]) is NOT general: it only fires for
/// operands of that shape, so it does not back the carrier's equality. Named
/// head args (none on the eq family) are ignored — a `?a`/`?b` positional eq
/// never carries them. An empty positional list does NOT count as general — the
/// `all` predicate is vacuously true over it, but a 0-ary `own` head is not an
/// equality clause; the eq family is always binary.
pub(super) fn rule_is_general_eq_clause(
    kb: &KnowledgeBase,
    r: crate::kb::RuleId,
    own: Symbol,
) -> bool {
    let Value::Term { id, .. } = kb.rule_head_value(r) else {
        return false;
    };
    let Term::Fn {
        functor, pos_args, ..
    } = kb.get_term(*id)
    else {
        return false;
    };
    *functor == own
        && !pos_args.is_empty()
        && pos_args
            .iter()
            .all(|&a| matches!(kb.get_term(a), Term::Var(_)))
}

/// The CARRIER ARGUMENTS of a call to one of `spec_canon`'s operations — the arguments
/// whose type decides the instance, by the guard's own rule ([`param_is_spec_carrier`] /
/// [`spec_self_represented_by`], WI-596's two shapes). Empty for a carrier-less op and for
/// a PARTIAL call, whose arguments cannot be aligned to the parameters that say which
/// ones carry.
///
/// Read by [`call_names_carrier`] (which of them statically names a sort) and by
/// [`collect_covered_calls`] (which of them IS the argument a dictionary was read from).
pub(super) fn call_carrier_args(
    kb: &KnowledgeBase,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    spec_canon: Symbol,
) -> Vec<Rc<NodeOccurrence>> {
    let Some(rec) = crate::kb::op_info::lookup_operation_info(kb, functor) else {
        return Vec::new();
    };
    let Some(args) = align_call_args_to_params(kb, &rec.params, pos_args, named_args) else {
        return Vec::new();
    };
    aligned_carrier_args(kb, &rec.params, &args, spec_canon)
}

/// [`call_carrier_args`] over arguments already in the order of `params`.
fn aligned_carrier_args(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    args: &[Rc<NodeOccurrence>],
    spec_canon: Symbol,
) -> Vec<Rc<NodeOccurrence>> {
    let type_params = kb.type_params_of_sort(spec_canon);
    let self_representing = spec_self_represented_by(kb, params, spec_canon);
    params
        .iter()
        .zip(args)
        .filter(|((_n, pty), _)| {
            param_is_spec_carrier(kb, spec_canon, &type_params, self_representing, pty)
        })
        .map(|(_, arg)| Rc::clone(arg))
        .collect()
}

/// WI-1040 — every call in `body_nodes` this spec's dictionary COVERS and CAN be
/// threaded into. Whole-body DFS, so a nested call is reached too.
///
/// THREE GATES, and each was measured before it was written.
///
/// * **A reader must exist for a woven goal.** [`weave_calls`] produces an
///   `Expr::ApplyWithin`, whose `TermView` head is `Opaque` — so at GOAL position it
///   is invisible to builtin dispatch (`get_builtin_view` keys on a `Functor` head),
///   to the discrim query, and to the WI-938 functional-relation hook unless that
///   hook recognizes the callee. `functional_relation_arity(..).is_some()` is exactly
///   that recognition: a rule-less BODIED operation. Without this gate,
///   `require[PartialEq[T]], eq(?x, ?y)` — the ordinary typeclass shape, where `eq`
///   is body-less AND builtin-tagged — went from ONE solution to ZERO, a clause that
///   worked before the weave silently failing after it.
///
///   **WI-20260909-NAR1X ADDED A SECOND READER TEST BESIDE IT, AND THE SENTENCE THIS
///   NOTE USED TO CARRY IS NO LONGER TRUE OF EVERY BODY-LESS OP** — kept corrected
///   rather than deleted, because the reasoning is what a reader needs. It said: "a
///   **body-less** spec op (the typeclass norm) and a **builtin-backed** one are
///   deliberately NOT woven … threading a dictionary into them needs a reader that
///   does not exist yet". WI-1057 BUILT that reader —
///   [`KnowledgeBase::body_less_relation_arity`], read through
///   `dispatched_relation_arity`'s woven-head arm in `step_init` — so the gate now
///   asks BOTH predicates, and a body-less callee is admitted where that one answers.
///
///   The **builtin-backed** half is untouched and stays refused, by the reader test
///   itself: `body_less_relation_arity` bails on `builtins.get(&f).is_some()`, so
///   `eq` never reaches the carrier test below and WI-1040's measured regression
///   cannot come back (`nar1x_carrier_less_spec_op_test::a_builtin_backed_spec_op_is_
///   still_not_woven`).
///
/// * **A CARRIER-BEARING callee is covered only AT THE DICTIONARY'S OWN
///   CARRIER** — where one of its carrier arguments IS one of `at`, the arguments the
///   dictionary was read from (the witness's carrier arguments, or the anchored head
///   variable). A carrier-LESS one (`Zeroable.zero()`, WI-20260909-NAR1X) is covered
///   wherever the spec's dictionary is: it has no operand for the value route to read,
///   so the clause's dictionary is not a better answer there, it is the only one.
///
///   NAR1X drew the line at carrier-less, and said so as a choice rather than a
///   finding: a carrier-bearing call's own operand already decided it, and weaving it
///   changed no row. WI-20260911-5G28A S2 made the choice live. A citation now HANDS a
///   clause the dictionary its caller chose (`ruleDesc` selects `Descending` for
///   `WeakOrd[T = Int64]`), which the operand cannot name — so the call at that
///   carrier must dispatch through it, or the caller's choice reaches the read and
///   stops there (`wi_5g28a_rule_dictionary_test`'s Ord and Rank rows).
///
///   AT ITS CARRIER, NOT EVERYWHERE, because the weave is otherwise CARRIER-BLIND and a
///   carrier-bearing call has a correct route of its own. MEASURED with the carrier
///   test absent: `rule two(?x, ?y, ?r1, ?r2) :- ?d = require[Desc[T]],
///   Desc.describe(?x, ?r1), Desc.describe(?y, ?r2)` answered `7, 7` for `(thing(),
///   gadget())` — the witness's `Thing` dictionary threaded into `gadget()`'s call —
///   where value dispatch answers `7, 9`; and two bracket-chosen `require`s
///   (`wi_hrfr5…::a_typed_head_carrier_is_readable_too`) were REFUSED, each call
///   covered by both. A call at another argument keeps the value route it had.
///
///   ARGUMENT IDENTITY is what "at its carrier" can mean at load: a rule body's
///   variables are untyped, so a call sharing the witness's carrier VARIABLE is the
///   one call known to be at the dictionary's type. A PROJECTED anchor (`p.E`) names no
///   argument at all, so it covers no carrier-bearing call.
///
///   A BODIED (defaulted) callee is held to the same direction: uncovered, it runs the
///   member its carrier's value supplies, and the default only where the carrier supplies
///   none, as a body-less call dispatches on its value. MEASURED carrier-blind, the same
///   `two` with a defaulted `describe` answered `7, 7` (`wi_gp8jc_defaulted_weave_test`).
///
/// * **Only where the typer did not already pin** (channel doc §5). Where
///   `check_apply_iter` resolved the call at compile stage the dispatch is decided
///   and installed; weaving it would put a run-time dictionary read in front of a
///   solved case — and the resolver honours the pin
///   (`classified_apply_target`), so the two would also disagree about which
///   decision wins.
pub(super) fn collect_covered_calls(
    kb: &KnowledgeBase,
    body_nodes: &[Rc<NodeOccurrence>],
    spec_canon: Symbol,
    at: &[Rc<NodeOccurrence>],
) -> Vec<Rc<NodeOccurrence>> {
    let mut out: Vec<Rc<NodeOccurrence>> = Vec::new();
    let mut stack: Vec<Rc<NodeOccurrence>> = body_nodes.iter().cloned().collect();
    while let Some(cand) = stack.pop() {
        let Some(expr) = cand.as_expr() else { continue };
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
        let Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        } = expr
        else {
            continue;
        };
        if spec_op_parent_sort(kb, *functor).is_none_or(|p| kb.canonical_sort_sym(p) != spec_canon)
        {
            continue;
        }
        // A reader must exist for the woven goal: a rule-less BODIED op
        // (`functional_relation_arity`), or a BODY-LESS spec op
        // (`body_less_relation_arity`, WI-1057's woven-head arm in `step_init`). A
        // builtin-tagged op answers neither — `body_less_relation_arity` bails on
        // `self.builtins.get(&f).is_some()` — which is what keeps WI-1040's measured
        // regression out: `require[PartialEq[T]], eq(?x, ?y)` went from ONE solution to
        // ZERO when `eq` was woven, an `Expr::ApplyWithin` at goal position being
        // `ViewHead::Opaque` to builtin dispatch. Driven by
        // `nar1x_carrier_less_spec_op_test`.
        //
        // BODIED, read off the body and not off `functional_relation_arity` alone: since
        // the ACG10 review that view also admits a HOST-MAPPED op (`String.length("abc",
        // ?n)`), and a host-mapped op whose parent is a parametric sort (`Map.size`) would
        // then read as bodied here and skip the carrier check below — woven with the
        // clause's dictionary at a call on another carrier, the regression
        // `wi_5g28a_rule_dictionary_test::a_call_at_another_carrier_keeps_its_own_dispatch`
        // guards for a body-less op. The goal-position view widened; the weaving
        // population did not, and weaving a host op is unmeasured.
        let bodied =
            kb.op_body_node(*functor).is_some() && kb.functional_relation_arity(*functor).is_some();
        if !bodied && kb.body_less_relation_arity(*functor).is_none() {
            continue;
        }
        // …and a CARRIER-BEARING call only AT THE DICTIONARY'S CARRIER — one of its
        // carrier arguments is one `at` names. See this function's doc for why. Driven by
        // `wi_5g28a_rule_dictionary_test::a_call_at_another_carrier_keeps_its_own_dispatch`
        // (`7, 7` without it), `wi_hrfr5…::a_typed_head_carrier_is_readable_too` (refused
        // without it) and, for a defaulted callee, `wi_gp8jc_defaulted_weave_test`.
        if op_has_spec_carrier_param(kb, *functor, spec_canon)
            && !call_carrier_args(kb, *functor, pos_args, named_args, spec_canon)
                .iter()
                .any(|arg| at.iter().any(|a| views_structurally_equal(kb, arg, a)))
        {
            continue;
        }
        // WI-1037 — the NARROW read (`PinNow` alone), deliberately, now that
        // `apply_dispatch` can tell the two apart. A `ConcreteApplyWithin` site is
        // ALSO one the typer decided, so §5's sentence above ("only where the typer
        // did not already pin") would exclude it too. It is admitted here anyway:
        // MEASURED, 14 occurrences in the corpus reach this filter as `NeedsDict`
        // (`test.wi1045.Desc.tag`) and they are woven, which is the behaviour
        // `wi1045_one_dictionary_representation_test` pins.
        //
        // THE PRECEDENCE THAT MAKES THAT SAFE IS WRITTEN AT THE OTHER SITE, not here,
        // and it is not the ordering of `reduce_op_value`'s arms: that function's
        // `Expr::ApplyWithin` arm RECURSES on a rebuilt `Expr::Apply`, and
        // `rebuilt_expr` carries the CallClass, so the woven node reaches the
        // `Expr::Apply` decode carrying whatever the spec-op site said. The arm
        // therefore RE-STAMPS the rebuilt node `PinNow(dictionary target)` — see the
        // comment there. Without that, admitting a `NeedsDict` site here would let a
        // static pin override the member the caller's dictionary selected.
        //
        // Narrowing this to `apply_dispatch() != Unclassified` remains a live choice
        // about which route OWNS these calls; it belongs to whoever revisits WI-1040's
        // weaving population, and that test is what would move.
        if cand.classified_apply_target().is_some() {
            continue;
        }
        if out.iter().any(|c| Rc::ptr_eq(c, &cand)) {
            continue;
        }
        out.push(Rc::clone(&cand));
    }
    out
}

/// WI-20260911-5G28A S2 — the `out` argument of a REQUIREMENT READ, or `None` for any other
/// body node. A read is the goal `?d = require[X]` becomes once the typing sweep has
/// rewritten it — `find_dictionary(spec, op, args…, out: ?d)`, positional spec and witness,
/// and the dictionary variable under the `out` label.
///
/// THE ONE PREDICATE both ends of a citation's implicit arguments read, and POSITION is the
/// identity between them: the typer's edge check ([`citation_requirement_routes`]) routes a
/// clause's reads in body order, and the resolver finds the same reads, in the same order,
/// in the clause it has just opened, to bind each `out` to the dictionary routed for it.
/// Matched by LOCAL NAME for `out`, as [`REQUIREMENT_OUT_LABEL`]'s other readers match it.
pub(crate) fn requirement_read_out<'a>(
    kb: &KnowledgeBase,
    find_dictionary: Symbol,
    node: &'a Rc<NodeOccurrence>,
) -> Option<&'a Rc<NodeOccurrence>> {
    let Some(Expr::Apply {
        functor,
        pos_args,
        named_args,
        ..
    }) = node.as_expr()
    else {
        return None;
    };
    if *functor != find_dictionary || pos_args.len() < 2 {
        return None;
    }
    named_args
        .iter()
        .find(|(k, _)| kb.local_name_of(*k) == REQUIREMENT_OUT_LABEL)
        .map(|(_, out)| out)
}

/// WI-20260911-5G28A S3 — the SPEC each requirement read of `relation`'s clauses reads, in
/// the flat layout [`requirement_read_counts`] indexes (clause after clause, read after
/// read — [`clause_requirement_reads`]): the head of a read's written instance, or `None`
/// where it has none a reader can name.
///
/// What `apply_domain` asks to decide which of a provider's reads its dictionary is FOR —
/// the same enumeration, so the positions it fills are the positions the resolver binds.
pub(crate) fn requirement_read_specs(kb: &KnowledgeBase, relation: Symbol) -> Vec<Option<Symbol>> {
    let Some(fd) = find_dictionary_symbol(kb) else {
        return Vec::new();
    };
    let qn = kb.qualified_name_of(relation).to_string();
    let mut out: Vec<Option<Symbol>> = Vec::new();
    for rid in kb.rule_ids_by_qn(&qn) {
        for read in clause_requirement_reads(kb, fd, kb.rule_body_nodes(rid)) {
            out.push(match read.as_expr() {
                Some(Expr::Apply { pos_args, .. }) => {
                    sort_functor_of_view(kb, &Value::Node(pos_args[0].clone()))
                }
                _ => None,
            });
        }
    }
    out
}

/// The `find_dictionary` symbol [`requirement_read_out`] keys on, or `None` in a KB that
/// never registered it — where no clause can hold a read.
pub(crate) fn find_dictionary_symbol(kb: &KnowledgeBase) -> Option<Symbol> {
    kb.try_resolve_symbol(crate::parse::desugar_target::qualified(
        crate::parse::desugar_target::FIND_DICTIONARY,
    ))
}

/// WI-20260911-5G28A S2 — how many requirement reads ([`clause_requirement_reads`]) each
/// clause of `relation` holds, in the order the relation's clauses are enumerated
/// (`rule_ids_by_qn`). The FLAT layout of a citation's implicit arguments is clause after
/// clause, parameter after parameter; this is what turns a clause's `RuleId` into its offset
/// in that layout.
pub(crate) fn requirement_read_counts(
    kb: &KnowledgeBase,
    relation: Symbol,
) -> Vec<(RuleId, usize)> {
    let Some(fd) = find_dictionary_symbol(kb) else {
        return Vec::new();
    };
    let qn = kb.qualified_name_of(relation).to_string();
    kb.rule_ids_by_qn(&qn)
        .into_iter()
        .map(|rid| {
            let params = clause_requirement_reads(kb, fd, kb.rule_body_nodes(rid)).len();
            (rid, params)
        })
        .collect()
}

//! WI-20261102-ATVC1 — RULE → RULE IMPLICIT ARGUMENTS (060-implementation §7.3, S7).
//!
//! A rule-body goal whose callee's clauses take dictionaries — their requirement reads —
//! carries what it passes them in the citation marker the resolver already reads for a
//! citation's root goal ([`crate::kb::resolve::WITHIN_REQUIREMENTS`]):
//!
//! ```text
//!   rule outer(?a, ?b, ?c) :- cmp(?a, ?b, ?c)
//!     ⇒   __within_requirements(cmp(?a, ?b, ?c), cmp, ?f)
//! ```
//!
//! one slot per position of the callee's layout ([`requirement_read_counts`]). A slot is
//!  * a requirement the clause declares, at the instance the goal is at (060.1 §1), or one its
//!    sort states, at the type the goal puts at the sort's parameter, which the clause reads
//!    for the goal ([`install_sort_requirement_reads`]), or, for a goal of the clause's own
//!    relation at the clause's own column types, what the clause took, handed on down the
//!    recursion — the variable the clause's read binds;
//!  * a dictionary built at load, where the goal's bracket or its arguments fix the instance
//!    (`Wrap[T = Int64].el(?x)`, `cmp(1, 2, ?c)`);
//!  * `__unrouted`, where nothing is passed: a read that is no guard. A guard at a type nothing
//!    at the goal fixes is refused instead (proposal 073 §6.2), and so is one at a type the
//!    clause declares nothing at, its sort's requirement at another instance included; a
//!    citation that leaves the callee's sort parameter free there is refused
//!    (`refuse_goals_left_free`).
//!
//! REPLACE, NOT INHERIT (op-to-rule-requirement-channel.md §1): what a goal passes is what
//! the typer routes to it here, never what its clause happened to receive.

use super::*;

/// The pass that wraps a goal in its citation marker.
const RULE_GOAL_ROUTES_PASS: &str = "anthill.kb.passes.rule_goal_routes";

/// The pass that gives a sort's clause the read of a requirement its sort states, for a goal
/// ([`install_sort_requirement_reads`]).
pub(super) const SORT_REQUIREMENT_READ_PASS: &str = "anthill.kb.passes.sort_requirement_read";

/// What one slot of a goal's marker passes ([`route_goal`]).
enum GoalSlot {
    /// A requirement the clause reads: its variable.
    Own(Rc<NodeOccurrence>),
    /// A dictionary built at load: from the goal's bracket, or at a concrete instance.
    Built(Value),
    Unrouted,
}

/// WI-20261102-ATVC1 — give every rule-body goal whose callee takes dictionaries the ones its
/// clause routes to it. AFTER [`infer_rule_body_requirements`] and the guards' installation,
/// whose reads are what a callee takes; routing adds no read, so no clause's layout depends on
/// the order its callers are routed in.
///
/// Idempotent: a clause already routed is left as it is, unless a callee's layout has changed
/// under it since (a later load added clauses), when its goals are routed again.
///
/// Answers the bracketed goals refused, each at its goal ([`bracketed_goal_routes`]).
pub(super) fn route_rule_goal_requirements(
    kb: &mut KnowledgeBase,
) -> Vec<(TypeError, Option<crate::span::SourceId>)> {
    let mut refused = Vec::new();
    let Some(mut routing) = Routing::new(kb) else {
        return refused;
    };
    install_sort_requirement_reads(kb, routing.syms.fd);
    // The clauses this run routes, by relation.
    let mut clauses: Vec<(RuleId, Symbol)> = Vec::new();
    for rid in kb.live_rule_ids() {
        if kb.is_fact(rid) || rule_body_is_typed_once(kb, rid) {
            continue;
        }
        // An equation's guard is run by the rewriter, which passes nothing: a bracket there,
        // or in its right-hand side, is read by no one. Not a LAW's guard (WI-20261117-8J8NG):
        // an untagged guarded `=` law is run by a proof from Γ, which passes it the instances
        // it holds (`law_type_instantiation`), and its goals are routed them as a clause's are
        // — so `nz(?b)` in `div[A](mul(?a, ?b: A), ?b) = ?a :- EuclideanDomain[T = A], …,
        // nz(?b)` is passed the law's `EuclideanDomain`, where it was passed nothing in any
        // load and the proof was undecided. Its right-hand side is still read by no one.
        if kb.has_equational_head(rid) {
            let law = kb.is_guarded_eq_law(rid) && !kb.is_directional_equation(rid);
            if !kb.is_clause_of_a_refused_load(rid) {
                let mut written: Vec<Rc<NodeOccurrence>> =
                    if law { Vec::new() } else { kb.rule_body_nodes(rid).to_vec() };
                written.extend(kb.rule_equation_rhs_node(rid));
                refuse_unread_brackets(kb, &written, &[], &mut refused);
            }
            if !law {
                continue;
            }
        }
        let Value::Term { id: head, .. } = kb.rule_head_value(rid).clone() else {
            continue;
        };
        let Some(relation) = kb.head_functor(head) else {
            continue;
        };
        if holds_goal_marker(kb, rid) {
            if !routing.has_stale_marker(kb, rid) {
                continue;
            }
            let body = body_without_goal_markers(kb, kb.rule_body_nodes(rid));
            kb.set_rule_body_nodes(rid, body);
        }
        clauses.push((rid, relation));
    }
    for (rid, relation) in clauses {
        if !kb.is_clause_of_a_refused_load(rid) {
            let written: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
            refuse_unread_brackets(kb, &written, &goal_sites(kb, rid), &mut refused);
        }
        route_clause_goals(kb, &mut routing, rid, relation, &mut refused);
    }
    refused
}

/// What [`route_rule_goal_requirements`] carries from clause to clause.
struct Routing {
    syms: RouteSyms,
    /// Each callee's layout ([`requirement_read_counts`]), read once per pass.
    layouts: HashMap<Symbol, Rc<[(RuleId, usize)]>>,
}

impl Routing {
    /// `None` in a KB that never loaded the requirement reads' kernel.
    fn new(kb: &mut KnowledgeBase) -> Option<Self> {
        let fd = find_dictionary_symbol(kb)?;
        let within = kb.try_resolve_symbol(crate::kb::resolve::WITHIN_REQUIREMENTS)?;
        let marker_pass = kb.register_pass(RULE_GOAL_ROUTES_PASS);
        let unrouted = match crate::kb::resolve::unrouted_read(kb) {
            Value::SymbolRef(s) => s,
            other => unreachable!("the unrouted slot is a symbol, got {other:?}"),
        };
        Some(Routing {
            syms: RouteSyms {
                fd,
                within,
                marker_pass,
                unrouted,
            },
            layouts: HashMap::new(),
        })
    }

    fn layout(&mut self, kb: &KnowledgeBase, relation: Symbol) -> Rc<[(RuleId, usize)]> {
        Rc::clone(
            self.layouts
                .entry(relation)
                .or_insert_with(|| requirement_read_counts(kb, relation).into()),
        )
    }

    /// Does a marker of `rid` hold another number of slots than its callee's layout has
    /// positions now — a callee given clauses by a later load?
    fn has_stale_marker(&mut self, kb: &KnowledgeBase, rid: RuleId) -> bool {
        goal_sites(kb, rid).iter().any(|n| {
            goal_marker(kb, n).is_some_and(|m| {
                let total: usize = self.layout(kb, m.relation).iter().map(|(_, c)| c).sum();
                m.slots.len() != total
            })
        })
    }
}

/// The symbols [`route_rule_goal_requirements`] builds markers with, resolved once.
struct RouteSyms {
    fd: Symbol,
    within: Symbol,
    marker_pass: crate::kb::occurrence::PassId,
    unrouted: Symbol,
}

/// Proposal 073 §6.2 — a query is typed where it is read, as a rule body is: each goal of the
/// conjunction `query` whose callee's clauses read a dictionary rides in its citation marker,
/// as a rule body's goal does, carrying the dictionary the goal's own types build at load — its
/// arguments, its bracket, and a variable at the type the query's goals give it, where their
/// columns agree on one (`src(?x), keep(?x, ?t)` over an `Int64` `src`). A query has no caller,
/// so a requirement at a type the query leaves open is refused, naming it, and none is read from
/// a value when the goal runs. `Err` with the refusals.
pub(crate) fn route_query_goals(
    kb: &mut KnowledgeBase,
    query: &[Rc<NodeOccurrence>],
) -> Result<Vec<Rc<NodeOccurrence>>, Vec<TypeError>> {
    let Some(mut routing) = Routing::new(kb) else {
        return Ok(query.to_vec());
    };
    let mut sites = query.to_vec();
    for goal in query {
        nested_goals(kb, goal, &mut sites);
    }
    stamp_query_variable_types(kb, query, &sites);
    // A bracket nothing reads — on a goal of a relation that declares nothing for it, or on a
    // relation that is no goal — is refused, as in a rule body (060.1 §2), never dropped.
    let mut refused = Vec::new();
    refuse_unread_brackets(kb, query, &sites, &mut refused);
    refuse_misfitting_typed_variables(kb, query, &sites, &mut refused);
    stamp_typed_variable_types(kb, query, &sites, &mut refused);
    // A goal riding in its citation marker was routed where its citation was typed — a
    // relation's query a typed body returned, drained later with the conditions run-time code
    // added to it: the marker is its routing, and routing it again would wrap the marker in
    // another. Its variables are still typed by it, above.
    let marked: Vec<Rc<NodeOccurrence>> = sites
        .iter()
        .filter_map(|s| goal_marker(kb, s).map(|m| Rc::clone(m.goal)))
        .collect();
    let sites: Vec<Rc<NodeOccurrence>> = sites
        .into_iter()
        .filter(|s| !marked.iter().any(|g| Rc::ptr_eq(g, s)))
        .collect();
    let mut wraps: Vec<(Rc<NodeOccurrence>, Rc<NodeOccurrence>)> = typed_spec_op_calls(kb, &sites, &mut refused);
    for site in sites {
        let Some(callee) = relation_goal_callee(kb, &site) else {
            continue;
        };
        if call_type_args_of(&site).is_some() && !relation_declares_type_params(kb, callee) {
            continue;
        }
        if let Some(marker) = route_goal(kb, &mut routing, GoalWriter::Query, &site, callee, &mut refused) {
            wraps.push((site, marker));
        }
    }
    if !refused.is_empty() {
        return Err(refused.into_iter().map(|(e, _)| e).collect());
    }
    Ok(query
        .iter()
        .map(|goal| {
            map_proved_goals(kb, goal, &|_, n| {
                wraps
                    .iter()
                    .find(|(site, _)| Rc::ptr_eq(site, n))
                    .map(|(_, marker)| Rc::clone(marker))
            })
        })
        .collect())
}

/// Does `arg` hold, at any depth, an application of an operation — a call, not a construction?
fn holds_an_operation_call(kb: &KnowledgeBase, arg: &Rc<NodeOccurrence>) -> bool {
    let mut stack = vec![Rc::clone(arg)];
    while let Some(node) = stack.pop() {
        let Some(expr) = node.as_expr() else { continue };
        if matches!(expr, Expr::Apply { functor, .. }
            if kb.entity_field_types(*functor).is_none() && kb.op_record(*functor).is_some())
        {
            return true;
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    false
}

/// Proposal 073 §6.2 — each goal of a query (`sites`, its goals and the goals in their proved
/// slots) that calls a spec operation owing an instance or an operation that takes dictionaries
/// ([`takes_dictionaries`]), or is a `<=>` holding such a call, typed
/// as a rule body's goal is ([`dispatch_calls_in_occ`]), each query variable at the type its goals
/// give it: a call at a type a provider answers is decided here, as the member it
/// reaches; one at a type nothing provides, or at a type nothing fixes, is refused, a query having
/// no caller to pass the instance. `Marker.tag(1, ?t)` is `Int64.tag`; `Marker.tag(1.5, ?t)`,
/// `Marker.tag(?x, ?t)` and `?t <=> Marker.tag(?x)` are refused. Each typed goal paired with the
/// site it stands for.
fn typed_spec_op_calls(
    kb: &mut KnowledgeBase,
    sites: &[Rc<NodeOccurrence>],
    refused: &mut Vec<(TypeError, Option<crate::span::SourceId>)>,
) -> Vec<(Rc<NodeOccurrence>, Rc<NodeOccurrence>)> {
    // A spec-op call written as a goal, a comparison included, and a `<=>` one stands in: what a
    // call owes an instance at. A connective is the query's own term, typed here no further.
    let unify = kb.unify_functor();
    let calls: Vec<Rc<NodeOccurrence>> = sites
        .iter()
        .filter(|site| match site.as_expr() {
            Some(Expr::Apply { functor, .. }) if *functor == unify => calls_an_operation_owing_a_dictionary(kb, site),
            Some(Expr::Apply { functor, .. }) => {
                owes_an_instance(kb, *functor) || takes_dictionaries(kb, *functor)
            }
            _ => false,
        })
        .cloned()
        .collect();
    if calls.is_empty() {
        return Vec::new();
    }
    // Each variable at the type its goals give it, bound by its name, the key the typer reads a
    // query's variable by. A name two variables share — the anonymous `?` — binds neither: one
    // `?`'s type is no other's.
    let mut by_name: HashMap<Symbol, (VarId, Option<Value>, bool)> = HashMap::new();
    for site in sites {
        for_each_var_leaf(site, &mut |var, leaf| {
            let Var::Global(vid) = var else { return };
            let entry = by_name.entry(vid.name()).or_insert((vid, None, false));
            entry.2 |= entry.0 != vid;
            if entry.1.is_none() {
                entry.1 = leaf.inferred_type();
            }
        });
    }
    // The typed variables (`?x: T`), each read at its type in the goal it types
    // ([`stamp_typed_variable_types`]); a name several variables share is none of them.
    let declared: Vec<VarId> = sites
        .iter()
        .filter_map(|site| typed_query_variable_of(kb, site).map(|(var, _, _)| var))
        .filter(|var| by_name.get(&var.name()).is_some_and(|(_, _, shared)| !*shared))
        .collect();
    let mut env = TypingEnv::empty();
    env.mark_rule_body_dispatch();
    // A variable no goal types is at a type of its own, open, which the call it is an argument
    // of may fix from its other arguments, as a clause variable's type is: `?x = 3` compares at
    // `Int64`, and `?a = ?b` is at a type nothing fixes. A name several variables share is at an
    // open type, never at another's.
    for (name, (_, ty, shared)) in by_name {
        let ty = ty
            .filter(|_| !shared)
            .unwrap_or_else(|| Value::Var(Var::Global(kb.fresh_var(name))));
        env.bind_var(name, ty);
    }
    let simp = simp_gate(kb);
    let fd = find_dictionary_symbol(kb);
    let mut out = Vec::new();
    for call in calls {
        // A typed variable at the type its occurrences in the call carry, over the type the
        // query's first occurrence gives the name: one written under `not` or in a branch of `|`
        // is stamped at its type in that goal alone, so two branches typing it differently each
        // read their own (WI-20261124-C6VN0).
        let mut call_env = env.clone();
        for_each_var_leaf(&call, &mut |var, leaf| {
            let Var::Global(vid) = var else { return };
            if let Some(ty) = leaf.inferred_type().filter(|_| declared.contains(&vid)) {
                call_env.bind_var(vid.name(), ty);
            }
        });
        let env = &call_env;
        let mut errors = Vec::new();
        let typed = dispatch_calls_in_occ(
            kb,
            env,
            &simp,
            &call,
            BodyPos::Goal(GoalCommit::Top),
            None,
            None,
            None,
            &mut errors,
        );
        // What a query's call may perform is not this pass's question: the run time declines
        // an effectful goal, as it did before a query was typed.
        errors.retain(|e| !matches!(e, TypeError::RuleBodyEffect { .. }));
        let mut applications = Vec::new();
        check_occ_spec_op_requirements(kb, &typed, fd, &[], &mut errors, &mut applications);
        errors.extend(applications.iter().filter_map(|a| a.refusal(kb)));
        if errors.is_empty() {
            errors.extend(calls_left_to_a_clause(kb, &typed));
        }
        if errors.is_empty() {
            out.push((call, typed));
        } else {
            refused.extend(errors.into_iter().map(|e| (e, Some(call.span.source))));
        }
    }
    out
}

/// Is `functor` a spec operation whose call owes an instance — a body-less member or a defaulted
/// one, which no host code or resolver builtin answers for every carrier? A comparison
/// (`PartialOrd.gt`) is one: at a type the query leaves open it is refused, as in a clause.
fn owes_an_instance(kb: &KnowledgeBase, functor: Symbol) -> bool {
    (lookup_spec_op_dispatch(kb, functor).is_some() || defaulted_spec_op_parent(kb, functor).is_some())
        && (!kb.is_builtin(functor) || is_semantic_equality(kb, functor))
        && !host_implements(kb, functor)
}

/// Is `functor` an operation whose call is handed dictionaries — its sort's `requires` or its
/// own: a call the typer passes them to, as a rule body's call ([`dispatch_calls_in_occ`]), so
/// none is built from the values when it runs.
fn takes_dictionaries(kb: &mut KnowledgeBase, functor: Symbol) -> bool {
    kb.op_record(functor).is_some()
        && !kb.is_entity_constructor(functor)
        && !op_dict_entries(kb, functor).is_empty()
}

/// Does `goal` call, anywhere in it, a spec operation that owes an instance ([`owes_an_instance`])
/// or an operation that takes dictionaries ([`takes_dictionaries`])? Inside a compound form — a
/// `let`, an `if`, a `match`, a `lambda` — any spec operation's call owes one, a resolver builtin's
/// too (WI-20261105-CBRD2): the interpreter evaluates the form, where no builtin answers it, so
/// `6 <=> (let a = 5  a + 1)` is typed as a rule body's form is and its `a + 1` is `Int64.add`'s
/// call, where the run dispatched `Additive.add` from the value.
fn calls_an_operation_owing_a_dictionary(kb: &mut KnowledgeBase, goal: &Rc<NodeOccurrence>) -> bool {
    let mut stack = vec![(Rc::clone(goal), false)];
    while let Some((node, in_form)) = stack.pop() {
        let Some(expr) = node.as_expr() else { continue };
        if matches!(expr, Expr::Apply { functor, .. }
            if owes_an_instance(kb, *functor)
                || takes_dictionaries(kb, *functor)
                || (in_form && spec_op_in_a_form(kb, *functor)))
        {
            return true;
        }
        let in_form = in_form || !pattern_child_indices(expr).is_empty() || node.is_compound_syntax();
        for_each_child(expr, |c| stack.push((Rc::clone(c), in_form)));
    }
    false
}

/// Is `functor` a spec operation the interpreter dispatches when a compound form calls it: a
/// body-less member or a defaulted one, whatever a resolver builtin or a host binding answers for
/// it elsewhere — `Additive.add`, which the run dispatched to `Int64.add` from the value
/// ([`calls_an_operation_owing_a_dictionary`]).
fn spec_op_in_a_form(kb: &KnowledgeBase, functor: Symbol) -> bool {
    lookup_spec_op_dispatch(kb, functor).is_some() || defaulted_spec_op_parent(kb, functor).is_some()
}

/// The calls in a query's typed goal `typed` that the typer left open — to a clause's condition,
/// or unresolved at a type nothing at the call fixes (`Marker.tag(?x, ?t)`) — each refused: a query has no clause
/// to supply the dictionary and no caller to pass it, and none is read from the value when the
/// goal runs (proposal 073 §6.2).
fn calls_left_to_a_clause(kb: &KnowledgeBase, typed: &Rc<NodeOccurrence>) -> Vec<TypeError> {
    let mut out = Vec::new();
    let mut stack = vec![Rc::clone(typed)];
    while let Some(node) = stack.pop() {
        let Some(expr) = node.as_expr() else { continue };
        let Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        } = expr
        else {
            for_each_child(expr, |c| stack.push(Rc::clone(c)));
            continue;
        };
        let spec_text = |spec: Symbol| format!("`{}`", short_name_of(kb.qualified_name_of(spec)));
        let open = match (node.clause_condition(), node.call_class()) {
            (Some(ClauseCondition::Dispatch { spec } | ClauseCondition::SortRequires { spec }), _)
            | (None, Some(CallClass::UnresolvedSpecOp { spec_sort_sym: spec, .. })) => Some(spec_text(spec)),
            (Some(ClauseCondition::Slots), _) => {
                Some(format!("the requirements of `{}`", kb.qualified_name_of(*functor)))
            }
            (None, _) => spec_at_an_unknown_carrier(kb, *functor, pos_args, named_args).map(spec_text),
        };
        if let Some(requirement) = open {
            out.push(TypeError::Other {
                site: TypeError::here(),
                span: Some(node.span.span),
                context: TypeErrorContext::Rule {
                    name: *functor,
                    field: RuleField::Body,
                },
                expected: format!(
                    "a requirement, {requirement}, fixed where the call of `{}` is written",
                    kb.qualified_name_of(*functor)
                ),
                actual: format!(
                    "the query puts it at a type nothing fixes, and a query has no caller to \
                     pass the dictionary: give the argument a known type{}",
                    structural_equality_hint(kb, *functor)
                ),
            });
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    out
}

/// Each variable of a query's goals `sites` given the type the columns its relation goals put
/// it at agree on, where that is a concrete type — what a clause's typing gives the same
/// variable of the same goals in a rule body. Two columns, one at a sort with abstract values and
/// one at a type that provides it, meet at the provider (`carSrc(?s), dflted(?s, ?r)`: a `Car`).
/// A variable two columns put at other different types, or one only an open column reaches,
/// stays untyped. One no column types takes the type the query's goals `query` give it as a
/// clause's typing reads them ([`query_goal_var_types`]), where that is fixed: `?x` of `?x = 3`
/// is an `Int64`.
fn stamp_query_variable_types(
    kb: &mut KnowledgeBase,
    query: &[Rc<NodeOccurrence>],
    sites: &[Rc<NodeOccurrence>],
) {
    let mut types: HashMap<VarId, Option<Value>> = HashMap::new();
    for site in sites {
        let Some(Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        }) = site.as_expr()
        else {
            continue;
        };
        if !kb.cites_a_relation(*functor) || kb.has_kind(*functor, crate::intern::SymbolKind::Operation) {
            continue;
        }
        let args = pos_args
            .iter()
            .enumerate()
            .map(|(i, a)| (SlotKey::Pos(i), a))
            .chain(named_args.iter().map(|(k, a)| (SlotKey::Named(*k), a)));
        for (slot, arg) in args {
            let Some(Expr::Var(Var::Global(vid))) = arg.as_expr() else {
                continue;
            };
            let Some(ty) = stamped_column_type(kb, *functor, &slot) else {
                continue;
            };
            let agreed = types.entry(*vid).or_insert_with(|| Some(ty.clone()));
            if let Some(seen) = agreed.clone().filter(|seen| !views_structurally_equal(kb, seen, &ty)) {
                // Two columns meet where one is a sort with abstract values the other's type
                // provides: the variable is the provider's value, as in a clause.
                let none = Substitution::new();
                *agreed = if provides_the_slot(kb, &none, &ty, &seen) {
                    Some(ty.clone())
                } else if provides_the_slot(kb, &none, &seen, &ty) {
                    Some(seen)
                } else {
                    None
                };
            }
        }
    }
    let walked = query_goal_var_types(kb, query);
    for site in sites {
        for_each_var_leaf(site, &mut |var, leaf| {
            if let Var::Global(vid) = var {
                let ty = match types.get(&vid) {
                    Some(Some(ty)) => Some(ty),
                    _ => walked.get(&vid.raw()),
                };
                if let Some(ty) = ty.filter(|_| leaf.inferred_type().is_none()) {
                    leaf.set_inferred_type(ty.clone());
                }
            }
        });
    }
}

/// The type of each variable of the query's goals `query` that the goals fix, read as a clause's
/// typing reads a rule body's goals ([`collect_occurrence_type_constraints`]): what a call's
/// declared parameters and its other arguments say of it. Keyed by the variable's raw id; none
/// where the goals disagree.
/// A query's typed variable (proposal 010.1 §3.1) is held to the type the query's columns give
/// it, as a rule head's bound is held to the type its body gives (`settle_head_bounds`): one
/// whose type does not fit is refused where the query is read, rather than answering nothing.
/// Its goals stand around the goal it is written in, so one written at the query's top level is
/// held to the whole query, as a head's bound is to the whole body, and one written in a negand
/// or a branch to the goal it is written in.
fn refuse_misfitting_typed_variables(
    kb: &mut KnowledgeBase,
    query: &[Rc<NodeOccurrence>],
    sites: &[Rc<NodeOccurrence>],
    refused: &mut Vec<(TypeError, Option<crate::span::SourceId>)>,
) {
    let typed: Vec<(Rc<NodeOccurrence>, VarId, Value, Rc<NodeOccurrence>)> = sites
        .iter()
        .filter_map(|site| {
            typed_query_variable_of(kb, site)
                .map(|(var, bound, written_in)| (Rc::clone(site), var, bound, written_in))
        })
        .collect();
    if typed.is_empty() {
        return;
    }
    let mut top_level = Vec::new();
    for goal in query {
        conjuncts(kb, goal, &mut top_level);
    }
    let whole = query_goal_var_types(kb, query);
    for (check, var, bound, written_in) in typed {
        let own;
        let columns = if top_level.iter().any(|g| Rc::ptr_eq(g, &check)) {
            &whole
        } else {
            own = query_goal_var_types(kb, std::slice::from_ref(&written_in));
            &own
        };
        let Some(column) = columns.get(&var.raw()) else {
            continue;
        };
        if unify_types(kb, &mut Substitution::new(), column, &bound) {
            continue;
        }
        // The goal the type is written in names the relation; a value-built one may be a
        // connective's spine, and then the guard does, which is a call by construction.
        let relation = written_in
            .as_expr()
            .and_then(expr_call_parts)
            .or_else(|| check.as_expr().and_then(expr_call_parts))
            .map(|(functor, _, _)| functor)
            .expect("a typed variable's guard is a call: `typed_query_variable_of` read it as one");
        let printer = crate::persistence::print::TermPrinter::new(kb);
        let (column, bound) = (printer.print_value(column), printer.print_value(&bound));
        refused.push((
            TypeError::Other {
                site: TypeError::here(),
                span: Some(written_in.span.span),
                context: TypeErrorContext::Rule {
                    name: relation,
                    field: RuleField::Whole,
                },
                expected: format!(
                    "`?{}` at the type its column holds, `{column}`",
                    kb.local_name_of(var.name())
                ),
                actual: format!("the query types it `{bound}`"),
            },
            Some(written_in.span.source),
        ));
    }
}

/// WI-20261124-C6VN0 — A QUERY'S TYPED VARIABLE IS READ AT ITS TYPE in the goal it is written in
/// (kernel-language §5.3), as a rule body reads a head variable at its bound: every occurrence
/// of the variable there — and in the guard its type added — is stamped with the type, over what
/// the columns gave it. [`refuse_misfitting_typed_variables`] has refused a column the type does
/// not fit, so what is written over is an open slot (`List[T = ?]` under `List[Int64]`), never
/// another type. At the top of the query the goal is the whole query, as a head's bound reaches
/// the whole body; under `not` or in a branch of `|` it is that negand or branch. Before this only
/// the guard read the type, and `PartialEq.eq(?xs: List[Int64], ?ys: List[Int64])` was refused,
/// nothing fixing the element.
///
/// A variable is read at one type where it is read: two types for it whose goals meet — both at
/// the top, or one inside the goal the other types — are refused, naming both, and nothing is
/// stamped. Two branches of `|` may each type it, each branch reading its own.
fn stamp_typed_variable_types(
    kb: &mut KnowledgeBase,
    query: &[Rc<NodeOccurrence>],
    sites: &[Rc<NodeOccurrence>],
    refused: &mut Vec<(TypeError, Option<crate::span::SourceId>)>,
) {
    let typed: Vec<(Rc<NodeOccurrence>, VarId, Value, Rc<NodeOccurrence>)> = sites
        .iter()
        .filter_map(|site| {
            typed_query_variable_of(kb, site)
                .map(|(var, bound, written_in)| (Rc::clone(site), var, bound, written_in))
        })
        .collect();
    if typed.is_empty() {
        return;
    }
    let mut top_level = Vec::new();
    for goal in query {
        conjuncts(kb, goal, &mut top_level);
    }
    // Each typed variable's scope: `None` is the whole query.
    let scopes: Vec<Option<&Rc<NodeOccurrence>>> = typed
        .iter()
        .map(|(check, _, _, written_in)| {
            (!top_level.iter().any(|g| Rc::ptr_eq(g, check))).then_some(written_in)
        })
        .collect();
    let meet = |a: Option<&Rc<NodeOccurrence>>, b: Option<&Rc<NodeOccurrence>>| match (a, b) {
        (Some(a), Some(b)) => holds_node(a, b) || holds_node(b, a),
        _ => true,
    };
    let mut clash = false;
    for i in 0..typed.len() {
        for j in i + 1..typed.len() {
            let ((_, var_i, bound_i, written_i), (_, var_j, bound_j, _)) = (&typed[i], &typed[j]);
            if var_i != var_j || views_structurally_equal(kb, bound_i, bound_j) || !meet(scopes[i], scopes[j]) {
                continue;
            }
            clash = true;
            // The goal the type is written in names the relation; a value-built one may be a
            // connective's spine, and then the guard does, which is a call by construction.
            let relation = written_i
                .as_expr()
                .and_then(expr_call_parts)
                .or_else(|| typed[i].0.as_expr().and_then(expr_call_parts))
                .map(|(f, _, _)| f)
                .expect("a typed variable's guard is a call: `typed_query_variable_of` read it as one");
            let printer = crate::persistence::print::TermPrinter::new(kb);
            let (first, second) = (printer.print_value(bound_i), printer.print_value(bound_j));
            refused.push((
                TypeError::Other {
                    site: TypeError::here(),
                    span: Some(written_i.span.span),
                    context: TypeErrorContext::Rule {
                        name: relation,
                        field: RuleField::Whole,
                    },
                    expected: format!(
                        "`?{}` at one type where it is read",
                        kb.local_name_of(var_i.name())
                    ),
                    actual: format!("the query types it `{first}` and `{second}` there"),
                },
                Some(written_i.span.source),
            ));
        }
    }
    if clash {
        return;
    }
    let pass = typed_query_variable_pass(kb);
    for ((_, var, bound, _), scope) in typed.iter().zip(&scopes) {
        // In a negand or a branch: the goal and every goal its typed variables added around it —
        // the guard and the type's `fill` — each synthesized from that goal.
        let roots: Vec<Rc<NodeOccurrence>> = match scope {
            None => query.to_vec(),
            Some(written_in) => std::iter::once(Rc::clone(written_in))
                .chain(sites.iter().filter(|site| {
                    site.synthesized_by() == Some(pass)
                        && site.synthesized_from().is_some_and(|from| Rc::ptr_eq(from, written_in))
                }).cloned())
                .collect(),
        };
        for root in &roots {
            for_each_var_leaf(root, &mut |v, leaf| {
                if v == Var::Global(*var) {
                    leaf.set_inferred_type(bound.clone());
                }
            });
        }
    }
}

/// Is `node` `root` or a node under it?
fn holds_node(root: &Rc<NodeOccurrence>, node: &Rc<NodeOccurrence>) -> bool {
    let mut stack = vec![Rc::clone(root)];
    while let Some(n) = stack.pop() {
        if Rc::ptr_eq(&n, node) {
            return true;
        }
        if let Some(expr) = n.as_expr() {
            for_each_child(expr, |c| stack.push(Rc::clone(c)));
        }
    }
    false
}

/// The goals `goal` holds together, through its conjunctions (`KnowledgeBase::is_goal_conjunction`),
/// `goal` itself where it is no conjunction.
fn conjuncts(kb: &KnowledgeBase, goal: &Rc<NodeOccurrence>, out: &mut Vec<Rc<NodeOccurrence>>) {
    match goal.as_expr().and_then(expr_call_parts) {
        Some((functor, pos_args, _)) if kb.is_goal_conjunction(functor, pos_args.len()) => {
            for arg in pos_args {
                conjuncts(kb, arg, out);
            }
        }
        _ => out.push(Rc::clone(goal)),
    }
}

fn query_goal_var_types(kb: &mut KnowledgeBase, query: &[Rc<NodeOccurrence>]) -> HashMap<u32, Value> {
    let mut st = ClauseConstraints::new();
    for goal in query {
        collect_occurrence_type_constraints(kb, goal, None, BodyPos::Goal(GoalCommit::Top), true, &mut st);
    }
    if st.subst.is_contradiction() {
        return HashMap::new();
    }
    // What the walk leaves for after it — a call's result column (`Driver.flat(0, ?s)`), a
    // `<=>`'s call — read as a clause's body reads it, so a variable a call's result binds is at
    // that result's type, with the named slots it writes (WI-20260923-DK0QJ, [`ClauseSite`]). A
    // position that does not fit is kept out, as in a clause, and its disagreement is NOT
    // reported: this map gives the query's variables their types and has no refusal channel. A
    // call that owes an instance or takes dictionaries is refused at its misfit where the
    // query's calls are typed ([`typed_spec_op_calls`]); any other misfit a query's late
    // position finds was reported by nothing before this either, as no late position was read.
    let domain = kb.global_scope().owner();
    settle_late_positions(kb, ClauseSite::Query { domain, goals: query }, &mut st, &mut Vec::new());
    let subst = std::mem::take(&mut st.subst);
    st.var_types
        .into_iter()
        .filter_map(|(var, mut ty)| {
            loop {
                let (resolved, changed) = crate::kb::node_occurrence::subst_value_type(kb, &ty, &subst);
                ty = resolved;
                if !changed {
                    break;
                }
            }
            type_is_fixed(kb, &ty).then_some((var, ty))
        })
        .collect()
}

/// The concrete type every clause of `relation` gives its column `slot`, as the load typed it:
/// a fact's argument at that slot, a rule's head variable there as its clause's typing stamped
/// it. `None` where a clause gives none, gives an open type, or two clauses differ. Read off
/// what the load stamped, not by typing the stored bodies again: a body the requirement weave
/// elaborated no longer types its variables as the clause was written.
fn stamped_column_type(kb: &mut KnowledgeBase, relation: Symbol, slot: &SlotKey) -> Option<Value> {
    let rids: Vec<RuleId> = kb.rules_by_functor_iter(relation).collect();
    let mut agreed: Option<Value> = None;
    for rid in rids {
        let head = kb.fact_head_term(rid)?;
        let Term::Fn { pos_args, named_args, .. } = kb.get_term(head).clone() else {
            return None;
        };
        let arg = match slot {
            SlotKey::Pos(i) => pos_args.get(*i).copied(),
            SlotKey::Named(k) => named_args
                .iter()
                .find(|(n, _)| kb.local_name_of(*n) == kb.local_name_of(*k))
                .map(|(_, a)| *a),
        }?;
        let ty = match kb.get_term(arg) {
            Term::Var(Var::DeBruijn(d)) => {
                let d = *d;
                clause_var_stamps(kb, rid).into_iter().find(|(seen, _)| *seen == d)?.1
            }
            // A term's type, which the check below keeps only where it is concrete.
            _ => value_type_term(kb, &Substitution::new(), &Value::term(arg)),
        };
        if !instance_is_concrete(kb, &ty) {
            return None;
        }
        match &agreed {
            Some(seen) if !views_structurally_equal(kb, seen, &ty) => return None,
            Some(_) => {}
            None => agreed = Some(ty),
        }
    }
    agreed
}

/// Proposal 073 §2 — the columns of `relation` that hold instances: a column the clause typing
/// puts at a sort with abstract values (`?s` of `dflted(?s, ?x) :- Sp.dflt(?s, ?x)`, an `Sp`)
/// and each clause writes as a variable, with that type.
pub(super) fn instance_columns(kb: &mut KnowledgeBase, relation: Symbol) -> Vec<(SlotKey, Value)> {
    let Some(columns) = rule_goal_columns(kb, relation) else {
        return Vec::new();
    };
    let rids: Vec<RuleId> = kb.rules_by_functor_iter(relation).collect();
    columns
        .into_iter()
        .filter_map(|(slot, ty)| {
            let ColumnType::Of(ty) = ty else {
                return None;
            };
            abstract_carrier_of(kb, &ty)?;
            rids.iter()
                .all(|&rid| head_slot_is_a_variable(kb, rid, &slot))
                .then_some((slot, ty))
        })
        .collect()
}

/// Does the clause `rid` write its head slot `slot` as a variable?
fn head_slot_is_a_variable(kb: &KnowledgeBase, rid: RuleId, slot: &SlotKey) -> bool {
    let Some(head) = kb.fact_head_term(rid) else {
        return false;
    };
    let Term::Fn { pos_args, named_args, .. } = kb.get_term(head) else {
        return false;
    };
    let arg = match slot {
        SlotKey::Pos(i) => pos_args.get(*i).copied(),
        SlotKey::Named(k) => named_args
            .iter()
            .find(|(n, _)| kb.local_name_of(*n) == kb.local_name_of(*k))
            .map(|(_, a)| *a),
    };
    arg.is_some_and(|a| matches!(kb.get_term(a), Term::Var(_)))
}

/// One head slot, a named one by its field's name.
pub(super) fn same_slot(kb: &KnowledgeBase, a: &SlotKey, b: &SlotKey) -> bool {
    match (a, b) {
        (SlotKey::Pos(i), SlotKey::Pos(j)) => i == j,
        (SlotKey::Named(x), SlotKey::Named(y)) => kb.local_name_of(*x) == kb.local_name_of(*y),
        _ => false,
    }
}

/// Proposal 073 §2 — `site`, a goal of `callee`, with each argument at a column that holds
/// instances ([`instance_columns`]) paired with its sort's dictionary, built at load, as an
/// operation body pairs an argument at a parameter of that type: `dflted(car(n: 1), ?r)`
/// passes `Instance(<Car's Sp>, car(n: 1))`. A value at the column's own sort is an instance
/// already and passes as it is, as does a clause's variable no position types, which the column
/// types. A query's variable there is refused: a query has no caller to pass the instance, and
/// another of its goals that would bind it is no caller either. `Ok(None)` where nothing is
/// paired; refused where the argument's type is open there, or its sort has no instance of the
/// column's.
fn pack_instance_arguments(
    kb: &mut KnowledgeBase,
    site: &Rc<NodeOccurrence>,
    callee: Symbol,
    in_query: bool,
) -> Result<Option<Rc<NodeOccurrence>>, TypeError> {
    let Some(Expr::Apply {
        recv_type,
        functor,
        pos_args,
        named_args,
        type_args,
    }) = site.as_expr()
    else {
        return Ok(None);
    };
    let columns = instance_columns(kb, callee);
    if columns.is_empty() {
        return Ok(None);
    }
    let Some(instance_sym) = kb.try_resolve_symbol("anthill.realization.runtime.Instance") else {
        return Ok(None);
    };
    let mut changed = false;
    let mut pack = |kb: &mut KnowledgeBase, slot: SlotKey, arg: &Rc<NodeOccurrence>| {
        let Some((_, column)) = columns.iter().find(|(s, _)| same_slot(kb, s, &slot)) else {
            return Ok(Rc::clone(arg));
        };
        let packed = pack_instance_argument(kb, callee, column, arg, instance_sym, in_query)?;
        changed |= !Rc::ptr_eq(&packed, arg);
        Ok(packed)
    };
    let pos: Vec<Rc<NodeOccurrence>> = pos_args
        .iter()
        .enumerate()
        .map(|(i, a)| pack(kb, SlotKey::Pos(i), a))
        .collect::<Result<_, TypeError>>()?;
    let named: Vec<(Symbol, Rc<NodeOccurrence>)> = named_args
        .iter()
        .map(|(k, a)| Ok((*k, pack(kb, SlotKey::Named(*k), a)?)))
        .collect::<Result<_, TypeError>>()?;
    Ok(changed.then(|| {
        site.rebuilt_expr(Expr::Apply {
            recv_type: recv_type.clone(),
            functor: *functor,
            pos_args: pos,
            named_args: named,
            type_args: type_args.clone(),
        })
    }))
}

/// [`pack_instance_arguments`] for one argument `arg` at a column of type `column`.
fn pack_instance_argument(
    kb: &mut KnowledgeBase,
    callee: Symbol,
    column: &Value,
    arg: &Rc<NodeOccurrence>,
    instance_sym: Symbol,
    in_query: bool,
) -> Result<Rc<NodeOccurrence>, TypeError> {
    // A pair already: a goal routed again once a callee's layout changed.
    if matches!(arg.as_expr(), Some(Expr::Apply { functor, .. }) if *functor == instance_sym) {
        return Ok(Rc::clone(arg));
    }
    let sort = abstract_carrier_of(kb, column).expect("an instance column is at an abstract sort");
    let refusal = |kb: &mut KnowledgeBase, why: String| TypeError::Other {
        site: TypeError::here(),
        span: Some(arg.span.span),
        context: TypeErrorContext::Rule {
            name: callee,
            field: RuleField::Body,
        },
        expected: format!(
            "a value whose sort provides `{}`, the type of the column of `{}` it is passed at",
            short_name_of(kb.qualified_name_of(sort)),
            kb.qualified_name_of(callee),
        ),
        actual: why,
    };
    let is_var = matches!(arg.as_expr(), Some(Expr::Var(_)));
    let untyped_var = is_var && arg.inferred_type().is_none();
    let ty = goal_arg_type(kb, arg).filter(|_| !untyped_var);
    // An instance already, or a variable the column types: as it is — but in a query, which no
    // caller passes one to.
    if ty.as_ref().is_none_or(|ty| abstract_carrier_of(kb, ty).is_some()) {
        if in_query && is_var {
            let why = format!(
                "a variable of the query, for which no caller passes an instance of `{}`: pass a \
                 value of a sort that provides it",
                short_name_of(kb.qualified_name_of(sort)),
            );
            return Err(refusal(kb, why));
        }
        return Ok(Rc::clone(arg));
    }
    let ty = ty.expect("read above");
    if sort_functor_of_view(kb, &ty).is_none() || !instance_is_concrete(kb, &ty) {
        let why = format!(
            "a value at `{}`, a type nothing at the goal fixes, so no instance of `{}` is known \
             for it",
            type_display_name_value(kb, &ty),
            short_name_of(kb.qualified_name_of(sort)),
        );
        return Err(refusal(kb, why));
    }
    let context = TypeErrorContext::Rule {
        name: callee,
        field: RuleField::Body,
    };
    let dict = match instance_dictionary_at_place(kb, sort, &ty, column, context) {
        Ok(dict) => dict,
        Err(why) => {
            let why = format!("a `{}`: {why}", type_display_name_value(kb, &ty));
            return Err(refusal(kb, why));
        }
    };
    Ok(instance_pair_node(instance_sym, dict, arg))
}

/// The dictionary a value of the concrete type `ty` is paired with at a place of type `column`,
/// headed by `sort`, a sort with abstract values (073 §2): the place's own written type first —
/// `Car provides Sp[T = Int64]` is no `Sp[T = String]`, though `Car`'s provision answers for
/// `Sp` — and then the instance `ty`'s provision answers with. `context` is read only where the
/// type does not fit, to build a message this does not keep.
fn instance_dictionary_at_place(
    kb: &mut KnowledgeBase,
    sort: Symbol,
    ty: &Value,
    column: &Value,
    context: TypeErrorContext,
) -> Result<Value, String> {
    let fits = matches!(
        validate_arg_against_param(kb, &mut Substitution::new(), ty, column, None, context, None),
        ArgValidation::Ok
    );
    if !fits {
        return Err(format!("it is no `{}`", type_display_name_value(kb, column)));
    }
    let carrier = sort_functor_of_view(kb, ty)
        .ok_or_else(|| format!("`{}` names no sort", type_display_name_value(kb, ty)))?;
    let carrier = kb.canonical_sort_sym(kb.type_arg_owner(carrier).unwrap_or(carrier));
    instance_dictionary_at(kb, sort, carrier, ty, column)
}

/// The dictionary `value`, read from outside any body at its declared type `column` — a type
/// headed by a sort with abstract values (073 §2) — is paired with: the pair an operation body
/// builds where a value of a provider is used at the abstract sort, and a rule body's argument at
/// such a column ([`pack_instance_argument`]). For `term_ser`'s decoder. The value's type is the
/// one a host's value reads as ([`host_value_type`]); refused where it is no `column`, or where no
/// provision answers for it.
pub(crate) fn instance_dictionary_of_read_value(
    kb: &mut KnowledgeBase,
    value: &Value,
    column: &Value,
) -> Result<Value, String> {
    let sort = abstract_carrier_of(kb, column).ok_or_else(|| {
        format!("`{}` is no sort with abstract values", type_display_name_value(kb, column))
    })?;
    let ty = host_value_type(kb, value);
    if !instance_is_concrete(kb, &ty) {
        return Err(format!(
            "a value at `{}`, a type nothing fixes, so no instance of `{}` is known for it",
            type_display_name_value(kb, &ty),
            short_name_of(kb.qualified_name_of(sort)),
        ));
    }
    // No operation, rule or field is being checked: the place is the value's own.
    let context = TypeErrorContext::LetBinding { var: sort };
    instance_dictionary_at_place(kb, sort, &ty, column, context)
}

/// Proposal 073 §2 — the body of `rid` with each argument of an operation's call at a parameter
/// typed by a sort with abstract values paired with its sort's dictionary at load, as an
/// operation body's argument is: `head(cons(7, nil))` passes `Instance(<List's Stream>, cons(7,
/// nil))`, and `total([car(n: 1), van(n: 2)])` at `xs: List[T = Sp]` each element at `Sp`. A
/// value whose type the clause does not know is passed as it is, and nothing pairs it when the
/// call runs. `None` where nothing is paired.
fn pack_call_arguments(kb: &mut KnowledgeBase, rid: RuleId) -> Option<Vec<Rc<NodeOccurrence>>> {
    let instance_sym = kb.try_resolve_symbol("anthill.realization.runtime.Instance")?;
    let body: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
    let packed: Vec<Rc<NodeOccurrence>> =
        body.iter().map(|g| pack_calls_under(kb, g, instance_sym, &[])).collect();
    packed
        .iter()
        .zip(&body)
        .any(|(a, b)| !Rc::ptr_eq(a, b))
        .then_some(packed)
}

/// [`pack_call_arguments`] for the tree under `node`, children first. `known` gives the type of
/// an argument by its term where the caller knows more of it than the argument itself says (a
/// call's argument substituted into its callee's guard).
pub(super) fn pack_calls_under(
    kb: &mut KnowledgeBase,
    node: &Rc<NodeOccurrence>,
    instance_sym: Symbol,
    known: &[(TermId, Value)],
) -> Rc<NodeOccurrence> {
    let Some(expr) = node.as_expr() else {
        return Rc::clone(node);
    };
    let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
    for_each_child(expr, |c| children.push(Rc::clone(c)));
    let rebuilt: Vec<Rc<NodeOccurrence>> =
        children.iter().map(|c| pack_calls_under(kb, c, instance_sym, known)).collect();
    let node = crate::kb::simp_rewrite::reassemble(node, &rebuilt);
    let (functor, pos_args, named_args) = match node.as_expr() {
        Some(Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        }) => (*functor, pos_args.clone(), named_args.clone()),
        Some(Expr::ApplyWithin {
            functor,
            args,
            named_args,
            ..
        }) => (*functor, args.clone(), named_args.clone()),
        _ => return node,
    };
    let target = node.classified_target().unwrap_or(functor);
    let params: Vec<(Symbol, Value)> = match node.call_params().filter(|_| target == functor) {
        Some(at_call) => at_call.to_vec(),
        None => match crate::kb::op_info::lookup_operation_info(kb, target) {
            Some(info) => info.params.clone(),
            None => return node,
        },
    };
    if !params.iter().any(|(_, ty)| type_names_abstract_carrier(kb, ty)) {
        return node;
    }
    let pos_params = positional_param_indices(kb, &params, pos_args.len(), &named_args);
    let mut changed = false;
    let pos: Vec<Rc<NodeOccurrence>> = pos_args
        .iter()
        .enumerate()
        .map(|(i, a)| {
            let at = pos_params.get(i).copied().flatten().and_then(|p| params.get(p));
            match at.and_then(|(_, ty)| pack_at_type(kb, a, ty, instance_sym, known)) {
                Some(packed) => {
                    changed = true;
                    packed
                }
                None => Rc::clone(a),
            }
        })
        .collect();
    let named: Vec<(Symbol, Rc<NodeOccurrence>)> = named_args
        .iter()
        .map(|(k, a)| {
            let at = params.iter().find(|(p, _)| kb.local_name_of(*p) == kb.local_name_of(*k));
            match at.map(|(_, ty)| ty.clone()).and_then(|ty| pack_at_type(kb, a, &ty, instance_sym, known)) {
                Some(packed) => {
                    changed = true;
                    (*k, packed)
                }
                None => (*k, Rc::clone(a)),
            }
        })
        .collect();
    if !changed {
        return node;
    }
    let expr = match node.as_expr().expect("read above").clone() {
        Expr::Apply {
            recv_type,
            functor,
            type_args,
            ..
        } => Expr::Apply {
            recv_type,
            functor,
            pos_args: pos,
            named_args: named,
            type_args,
        },
        Expr::ApplyWithin {
            functor,
            requirements,
            type_args,
            ..
        } => Expr::ApplyWithin {
            functor,
            args: pos,
            named_args: named,
            requirements,
            type_args,
        },
        _ => unreachable!("a call, read above"),
    };
    node.rebuilt_expr(expr)
}

/// `arg` as a value at type `expected`: paired where `expected` is a sort with abstract values
/// and `arg` is of a sort that provides it, its fields so where it is a construction at a type
/// that holds such a sort (`cons(car(n: 1), nil)` at `List[T = Sp]`). `None` where nothing is
/// paired: a value at the abstract sort already, or one whose type is not known here.
fn pack_at_type(
    kb: &mut KnowledgeBase,
    arg: &Rc<NodeOccurrence>,
    expected: &Value,
    instance_sym: Symbol,
    known: &[(TermId, Value)],
) -> Option<Rc<NodeOccurrence>> {
    match arg.as_expr()? {
        Expr::Apply { functor, .. } if *functor == instance_sym => return None,
        _ => {}
    }
    if let Some(sort) = abstract_carrier_of(kb, expected) {
        let untyped_var = matches!(arg.as_expr(), Some(Expr::Var(_))) && arg.inferred_type().is_none();
        // A type the typer gave the argument where its value alone says less (`[]` handed to a
        // `List[T = Int64]`) is the argument's: its own stamp, or the one `known` gives its term.
        let known_ty = (!known.is_empty())
            .then(|| {
                let term = crate::kb::node_occurrence::occurrence_to_term(kb, arg);
                known.iter().find(|(t, _)| *t == term).map(|(_, ty)| ty.clone())
            })
            .flatten();
        let ty = match arg.inferred_type().or(known_ty).filter(|t| instance_is_concrete(kb, t)) {
            Some(t) => t,
            None => goal_arg_type(kb, arg).filter(|_| !untyped_var)?,
        };
        // A type its element leaves open (`[]`'s `List[T = ?]`) still names its carrier, and a
        // provision that does not read the open part builds there (`List provides Stream`);
        // one that does (`ListShow` over `Show[T = E]`) fails to, and the value is left as it is.
        if abstract_carrier_of(kb, &ty).is_some() {
            return None;
        }
        let carrier = sort_functor_of_view(kb, &ty)?;
        let carrier = kb.canonical_sort_sym(kb.type_arg_owner(carrier).unwrap_or(carrier));
        let dict = instance_dictionary_at(kb, sort, carrier, &ty, expected).ok()?;
        return Some(instance_pair_node(instance_sym, dict, arg));
    }
    if !type_names_abstract_carrier(kb, expected) {
        return None;
    }
    let (_, type_args) = parametric_view_parts(kb, expected)?;
    match arg.as_expr()? {
        Expr::ListLit(elems) => {
            let elem = type_args.first().map(|(_, t)| t.clone())?;
            let mut changed = false;
            let packed: Vec<Rc<NodeOccurrence>> = elems
                .iter()
                .map(|e| match pack_at_type(kb, e, &elem, instance_sym, known) {
                    Some(p) => {
                        changed = true;
                        p
                    }
                    None => Rc::clone(e),
                })
                .collect();
            changed.then(|| arg.rebuilt_expr(Expr::ListLit(packed)))
        }
        Expr::Apply {
            recv_type,
            functor,
            pos_args,
            named_args,
            type_args: written,
        } => {
            let sort = kb.sort_of_constructor(*functor)?;
            let fields = kb.entity_field_types(*functor)?.to_vec();
            let mut changed = false;
            let mut field_at = |kb: &mut KnowledgeBase, field: Option<&(Symbol, Value)>, a: &Rc<NodeOccurrence>| {
                let packed = field
                    .and_then(|(_, fty)| field_type_at(kb, sort, fty, expected, &type_args))
                    .and_then(|ty| pack_at_type(kb, a, &ty, instance_sym, known));
                match packed {
                    Some(p) => {
                        changed = true;
                        p
                    }
                    None => Rc::clone(a),
                }
            };
            let pos: Vec<Rc<NodeOccurrence>> =
                pos_args.iter().enumerate().map(|(i, a)| field_at(kb, fields.get(i), a)).collect();
            let named: Vec<(Symbol, Rc<NodeOccurrence>)> = named_args
                .iter()
                .map(|(k, a)| {
                    let field = fields.iter().find(|(f, _)| kb.local_name_of(*f) == kb.local_name_of(*k));
                    (*k, field_at(kb, field, a))
                })
                .collect();
            changed.then(|| {
                arg.rebuilt_expr(Expr::Apply {
                    recv_type: recv_type.clone(),
                    functor: *functor,
                    pos_args: pos,
                    named_args: named,
                    type_args: written.clone(),
                })
            })
        }
        _ => None,
    }
}

/// Route the goals of `rid`, and store the body.
fn route_clause_goals(
    kb: &mut KnowledgeBase,
    routing: &mut Routing,
    rid: RuleId,
    relation: Symbol,
    refused: &mut Vec<(TypeError, Option<crate::span::SourceId>)>,
) {
    if let Some(body) = pack_call_arguments(kb, rid) {
        kb.set_rule_body_nodes(rid, body);
    }
    let mut wraps: Vec<(Rc<NodeOccurrence>, Rc<NodeOccurrence>)> = Vec::new();
    for site in goal_sites(kb, rid) {
        let Some(callee) = relation_goal_callee(kb, &site) else {
            continue;
        };
        let writer = GoalWriter::Clause { rid, relation };
        if let Some(marker) = route_goal(kb, routing, writer, &site, callee, refused) {
            wraps.push((site, marker));
        }
    }
    if wraps.is_empty() {
        return;
    }
    let body: Vec<Rc<NodeOccurrence>> = kb
        .rule_body_nodes(rid)
        .iter()
        .map(|g| {
            map_proved_goals(kb, g, &|_, n| {
                wraps
                    .iter()
                    .find(|(site, _)| Rc::ptr_eq(site, n))
                    .map(|(_, marker)| Rc::clone(marker))
            })
        })
        .collect();
    kb.set_rule_body_nodes(rid, body);
}

/// Where a routed goal is written: a clause of `relation`, or a query, which no caller passes
/// a requirement and which is typed where it is read (proposal 073 §6.2).
#[derive(Clone, Copy)]
enum GoalWriter {
    Clause { rid: RuleId, relation: Symbol },
    Query,
}

impl GoalWriter {
    fn clause(self) -> Option<RuleId> {
        match self {
            GoalWriter::Clause { rid, .. } => Some(rid),
            GoalWriter::Query => None,
        }
    }
}

/// The marker `site` — a goal of `callee` written by `writer` — rides in, or `None` where it
/// passes its callee nothing.
fn route_goal(
    kb: &mut KnowledgeBase,
    routing: &mut Routing,
    writer: GoalWriter,
    site: &Rc<NodeOccurrence>,
    callee: Symbol,
    refused: &mut Vec<(TypeError, Option<crate::span::SourceId>)>,
) -> Option<Rc<NodeOccurrence>> {
    let packed = match pack_instance_arguments(kb, site, callee, matches!(writer, GoalWriter::Query)) {
        Ok(packed) => packed,
        Err(refusal) => {
            refused.push((refusal, Some(site.span.source)));
            return None;
        }
    };
    let counts = routing.layout(kb, callee);
    let total: usize = counts.iter().map(|(_, n)| n).sum();
    if total == 0 && packed.is_none() {
        return None;
    }
    // The bracket's instance, built here: nothing a caller passes can change it — a sort's
    // bracket on the relation, or the goal's own on what the relation declares (060.1 §2).
    // Beside it, what the goal fixes each parameter of the callee's sort to — its bracket, an
    // argument at a column typed with it, the parameter's default — which a guard of the callee
    // that names one is built at; read for a goal with no bracket where a guard is built.
    let bracketed = call_recv_type_of(site).is_some() || call_type_args_of(site).is_some();
    let (built, mut sort_params): (_, Option<Vec<CitedParam>>) = if bracketed {
        let mut misfits = Vec::new();
        let (routes, params) = match bracketed_goal_routes(kb, site, callee, &mut misfits) {
            Ok(routes) => routes,
            Err(refusal) => {
                refused.push((refusal, Some(site.span.source)));
                return None;
            }
        };
        for misfit in misfits {
            refused.push(citation_misfit_error(kb, callee, site.span, misfit));
        }
        (routes, Some(params))
    } else {
        (SmallVec::new(), None)
    };
    // A goal of the clause's own relation at its own column types: the clause's parameters,
    // at its own offset in the layout.
    let own: Option<(usize, Vec<Rc<NodeOccurrence>>)> = match writer {
        GoalWriter::Clause { rid, relation } if callee == relation => Some(rid),
        _ => None,
    }
    .map(|rid| {
            let at = counts.iter().position(|(r, _)| *r == rid)?;
            if !keeps_its_column_types(kb, rid, site) {
                return None;
            }
            let offset: usize = counts[..at].iter().map(|(_, n)| n).sum();
            let fd = routing.syms.fd;
            let vars = clause_requirement_reads(kb, fd, kb.rule_body_nodes(rid))
                .iter()
                .map(|read| Rc::clone(requirement_read_out(kb, fd, read).expect("a read has an `out`")))
                .collect();
            Some((offset, vars))
        })
    .flatten();
    // Each position of the layout as the clause and the read it is, for the routes a declared
    // requirement of the clause gives (`declared_route`).
    let positions: Vec<(RuleId, usize)> = counts
        .iter()
        .flat_map(|&(r, n)| (0..n).map(move |k| (r, k)))
        .collect();
    let mut callee_reads: HashMap<RuleId, Vec<Rc<NodeOccurrence>>> = HashMap::new();
    let mut tie: Option<(Symbol, Symbol)> = None;
    // Two requirements the caller's sort states with no name at instances the goal's both fit.
    let mut instances_tie: Option<(String, String)> = None;
    // Where the goal cannot be read as a citation of its callee, for the guard it builds.
    let mut unread: Option<TypeError> = None;
    // The caller's frame slots for its sort's parameters, which a requirement it hands on is at.
    let caller_sort_slots: Vec<u32> = writer.clause().map(|rid| sort_param_slots(kb, rid)).unwrap_or_default();
    let declared: Vec<GuardRoute> = positions
        .iter()
        .map(|&(crid, k)| {
            let fd = routing.syms.fd;
            let params = callee_reads
                .entry(crid)
                .or_insert_with(|| clause_requirement_reads(kb, fd, kb.rule_body_nodes(crid)));
            let Some(read) = params.get(k) else {
                return GuardRoute::NoGuard;
            };
            let read = Rc::clone(read);
            let Some((spec, carrier, instance)) = guard_read_parts(kb, &read) else {
                // A read the callee takes for a call is passed the requirement the caller's sort
                // states at the call's receiver, which the caller reads for it
                // (`install_sort_requirement_reads`); a slot read, the slot's requirement at the
                // goal's types where they make it concrete, or the caller's own guard where its
                // carrier is a parameter of the caller ([`slot_read_at_goal`]); any other passes
                // what it did.
                let handed = writer.clause().and_then(|rid| {
                    let (spec, at_goal) = call_read_at_goal(kb, rid, &caller_sort_slots, site, crid, &read)?;
                    sort_requirement_read(kb, fd, rid, spec, &at_goal)
                });
                if let Some(var) = handed {
                    return GuardRoute::Declared(var);
                }
                // A read the callee takes for a call that is its sort's requirement (060.1
                // §8.2; a spec's own rule reads the spec, §3), at a concrete type the goal puts
                // the call's receiver at: built here, as a guard's at that type is.
                // `viaGood(?y) :- src(?y), Pred.good(?y)` over `sort Pred { rule good(?x: T) :-
                // ok(?x) }` passes `Pred[T = Leaf]`'s. Where the provisions build none there, the
                // goal is refused as for a guard.
                if let Some((read_spec, slot, stated)) = sorts_call_read_instance(kb, crid, &read) {
                    let at = guard_carrier_at_goal(kb, site, crid, slot);
                    // At a type parameter of the caller, the requirement its one element: the
                    // caller's own guard of the spec there, as for a slot read.
                    let only_the_carrier = debruijn_vars(kb, stated) == [slot];
                    if let Some(var) = at
                        .as_ref()
                        .filter(|_| only_the_carrier)
                        .zip(writer.clause())
                        .and_then(|(at, caller)| callers_own_guard(kb, fd, caller, read_spec, at))
                    {
                        return GuardRoute::Declared(var);
                    }
                    if let Some(at) = at.filter(|at| instance_is_concrete(kb, at)) {
                        if sort_params.is_none() {
                            match goal_sort_param_values(kb, site, callee) {
                                Ok(params) => sort_params = Some(params),
                                Err(refusal) => {
                                    unread.get_or_insert(refusal);
                                    return GuardRoute::NoGuard;
                                }
                            }
                        }
                        let sort_params = sort_params.as_deref().expect("read above");
                        return match dictionary_at_goal(kb, site, callee, crid, slot, &Value::term(stated), &at, sort_params) {
                            Ok(dict) => GuardRoute::Concrete(dict),
                            Err(GoalDictMiss::Unfixed(_)) if bracketed => GuardRoute::NoGuard,
                            Err(GoalDictMiss::Unfixed(why) | GoalDictMiss::Fetch(why)) => GuardRoute::Unbuilt(read_spec, why),
                        };
                    }
                }
                return slot_read_at_goal(kb, fd, writer.clause(), site, crid, &read)
                    .unwrap_or(GuardRoute::NoGuard);
            };
            let at = guard_carrier_at_goal(kb, site, crid, carrier);
            // Each other type parameter the guard names at an element, with the caller's
            // parameter the goal puts there (`Conv[A = X, B = U]` reached at the caller's `U`).
            let elements: Vec<(u32, u32)> = guard_element_vars(kb, crid, instance.expect_term(), carrier)
                .into_iter()
                .filter_map(|e| {
                    let rid = writer.clause()?;
                    let at_e = guard_carrier_at_goal(kb, site, crid, e)?;
                    Some((e, caller_param_at(kb, rid, &at_e)?))
                })
                .collect();
            if let Some(var) = at.as_ref().zip(writer.clause()).and_then(|(at, rid)| {
                declared_route(kb, fd, rid, spec, carrier, &elements, &instance, at, &mut tie)
            }) {
                return GuardRoute::Declared(var);
            }
            match at {
                Some(at) if instance_is_concrete(kb, &at) => {
                    if sort_params.is_none() {
                        match goal_sort_param_values(kb, site, callee) {
                            Ok(params) => sort_params = Some(params),
                            Err(refusal) => {
                                unread.get_or_insert(refusal);
                                return GuardRoute::NoGuard;
                            }
                        }
                    }
                    let sort_params = sort_params.as_deref().expect("read above");
                    let dict = dictionary_at_goal(
                        kb,
                        site,
                        callee,
                        crid,
                        carrier,
                        &instance,
                        &at,
                        sort_params,
                    );
                    match dict {
                        Ok(dict) => GuardRoute::Concrete(dict),
                        // A bracket's citation has refused the parameter it leaves unfixed
                        // (`CarriedMisfit::Unfixed`, above): one fault, one refusal.
                        Err(GoalDictMiss::Unfixed(_)) if bracketed => GuardRoute::NoGuard,
                        Err(GoalDictMiss::Unfixed(why) | GoalDictMiss::Fetch(why)) => {
                            GuardRoute::Unbuilt(spec, why)
                        }
                    }
                }
                // A requirement the clause's sort states at the goal's instance is read by the
                // clause and passed (`install_sort_requirement_reads`); one it states at another
                // is no more the clause's than one it does not state, and one it states under two
                // names is two the goal says neither of.
                Some(at)
                    if writer
                        .clause()
                        .is_some_and(|rid| type_reaches_the_head(kb, rid, &at)) =>
                {
                    let rid = writer.clause().expect("the guard reaches the clause's head");
                    let at_goal = guard_instance_at_goal(
                        kb,
                        rid,
                        &caller_sort_slots,
                        site,
                        crid,
                        carrier,
                        instance.expect_term(),
                    );
                    let states = match &at_goal {
                        Some(at_goal) => sort_states_requirement(kb, rid, spec, &Value::term(at_goal.instance)),
                        None => SortStates::No,
                    };
                    match (states, at_goal) {
                        // The requirement the sort states there, which the clause reads for the goal.
                        (SortStates::Once(_), Some(at_goal)) => match sort_requirement_read(kb, fd, rid, spec, &at_goal) {
                            Some(out) => GuardRoute::Declared(out),
                            None => GuardRoute::Undeclared(spec, None),
                        },
                        (SortStates::Twice(first, second), _) => {
                            tie.get_or_insert((first, second));
                            GuardRoute::NoGuard
                        }
                        (SortStates::TwoInstances(first, second), _) => {
                            instances_tie.get_or_insert((first, second));
                            GuardRoute::NoGuard
                        }
                        (SortStates::No, _) if clause_sort_supplies(kb, rid, spec) => {
                            GuardRoute::Undeclared(spec, Some(kb.rule_domain(rid)))
                        }
                        _ => GuardRoute::Undeclared(spec, None),
                    }
                }
                at => GuardRoute::Open(OpenGuard {
                    spec,
                    clause: crid,
                    carrier,
                    instance,
                    at,
                }),
            }
        })
        .collect();
    if let Some(refusal) = unread {
        refused.push((refusal, Some(site.span.source)));
        return None;
    }
    // 060.1 §8.2 (the user, 2026-11-04; and 2026-11-19 for a goal with no bracket) — a read the
    // callee's clause takes off a NAMED requirement slot of a variable's type (`?p <=> box(a:
    // ?x, b: ?y), WeakOrd.compare(?x, ?y, ?c)` in `sort Box` with `requires O: WeakOrd[T]`) is
    // filled only by what the citation writes for the slot. A bracketed goal is read so above;
    // one with no bracket is read the same way for those reads, and is refused, naming the
    // slot, where its arguments' types leave it unwritten (`Box.order(Box.box(a: 1, b: 5),
    // ?c)`), as the bracket that leaves it out is. Nothing is read from the value.
    let carried: Vec<usize> = if bracketed {
        Vec::new()
    } else {
        positions
            .iter()
            .enumerate()
            .filter(|(j, _)| matches!(declared.get(*j), Some(GuardRoute::NoGuard)))
            .filter(|(_, &(crid, k))| {
                callee_reads
                    .get(&crid)
                    .and_then(|reads| reads.get(k))
                    .is_some_and(|read| read_off_a_named_slot(kb, crid, read))
            })
            .map(|(j, _)| j)
            .collect()
    };
    let mut carried_built: SmallVec<[Option<TermId>; 2]> = SmallVec::new();
    if !carried.is_empty() {
        let mut misfits = Vec::new();
        let routes = match bracketed_goal_routes(kb, site, callee, &mut misfits) {
            Ok((routes, _)) => routes,
            Err(refusal) => {
                refused.push((refusal, Some(site.span.source)));
                return None;
            }
        };
        let mut slot_refused = false;
        for misfit in misfits {
            if matches!(
                misfit,
                CarriedMisfit::SlotUnwritten { .. }
                    | CarriedMisfit::NotAnswered { .. }
                    | CarriedMisfit::TwoProviders { .. }
            ) {
                refused.push(citation_misfit_error(kb, callee, site.span, misfit));
                slot_refused = true;
            }
        }
        if slot_refused {
            return None;
        }
        carried_built = (0..total)
            .map(|j| if carried.contains(&j) { routes.get(j).copied().flatten() } else { None })
            .collect();
    }
    if let Some((first, second)) = tie {
        refused.push((
            TypeError::Other {
                site: TypeError::here(),
                span: Some(site.span.span),
                context: TypeErrorContext::Rule {
                    name: callee,
                    field: RuleField::Whole,
                },
                expected: format!(
                    "one requirement of the clause for the goal of `{}`",
                    kb.qualified_name_of(callee)
                ),
                actual: format!(
                    "the goal needs a requirement two of the clause's hold, `{}` and `{}` — one \
                     sort at one type under two names, two dictionaries — and nothing at the goal \
                     says which",
                    kb.local_name_of(first),
                    kb.local_name_of(second),
                ),
            },
            Some(site.span.source),
        ));
        return None;
    }
    if let Some((first, second)) = instances_tie {
        refused.push((
            TypeError::Other {
                site: TypeError::here(),
                span: Some(site.span.span),
                context: TypeErrorContext::Rule {
                    name: callee,
                    field: RuleField::Whole,
                },
                expected: format!(
                    "one requirement of the clause's sort for the goal of `{}`",
                    kb.qualified_name_of(callee)
                ),
                actual: format!(
                    "the sort states two the goal fits, `{first}` and `{second}` — two \
                     dictionaries — and nothing at the goal says which"
                ),
            },
            Some(site.span.source),
        ));
        return None;
    }
    // 060.1 §1 — at a concrete instance the requirement is built from the provisions at
    // load, and the goal is refused where none builds it, as an operation's call is.
    // A clause whose guard the loader refused is refused for it, and what it lacks follows.
    let refused_load = writer.clause().is_some_and(|rid| kb.has_a_refused_guard(rid));
    // The relation the refusals below are about: the clause's own, or the query's callee.
    let relation = match writer {
        GoalWriter::Clause { relation, .. } => relation,
        GoalWriter::Query => callee,
    };
    if let Some((spec, why)) = declared.iter().find_map(|g| match g {
        GuardRoute::Unbuilt(spec, why) if !refused_load => Some((*spec, why.clone())),
        _ => None,
    }) {
        refused.push((
            TypeError::Other {
                site: TypeError::here(),
                span: Some(site.span.span),
                context: TypeErrorContext::Rule {
                    name: relation,
                    field: RuleField::Body,
                },
                expected: format!(
                    "a `{spec_name}` the provisions build at the types the goal of `{callee_name}` \
                     is at",
                    spec_name = short_name_of(kb.qualified_name_of(spec)),
                    callee_name = kb.qualified_name_of(callee),
                ),
                actual: why,
            },
            Some(site.span.source),
        ));
        return None;
    }
    // 060.1 §1 — a goal at an instance that names a type variable of the clause is supplied
    // by what the clause declares, and refused where it declares nothing there.
    if let Some((spec, sort_states)) = declared.iter().find_map(|g| match g {
        GuardRoute::Undeclared(spec, sort_states) if !refused_load => Some((*spec, *sort_states)),
        _ => None,
    }) {
        let spec_name = short_name_of(kb.qualified_name_of(spec)).to_owned();
        let sort_states = match sort_states {
            Some(sort) => format!(
                "the clause's sort `{}` states `{spec_name}` at another instance, ",
                short_name_of(kb.qualified_name_of(sort)),
            ),
            None => String::new(),
        };
        refused.push((
            TypeError::Other {
                site: TypeError::here(),
                span: Some(site.span.span),
                context: TypeErrorContext::Rule {
                    name: relation,
                    field: RuleField::Body,
                },
                expected: format!(
                    "a requirement of `{spec_name}` the clause declares, at the type the goal of \
                     `{callee_name}` is at",
                    callee_name = kb.qualified_name_of(callee),
                ),
                actual: format!(
                    "{sort_states}the clause declares none, and a rule takes no dictionary it \
                     does not declare: {}",
                    crate::parse::desugar_target::DECLARE_A_REQUIREMENT,
                ),
            },
            Some(site.span.source),
        ));
        return None;
    }
    // 073 §6.2 — a requirement at a type nothing at the goal fixes is refused: a variable the
    // clause's body binds, which no head column reaches and so no caller can type, or a query's
    // variable, a query having no caller. Nothing is read from the value when the goal runs.
    if let Some(open) = declared.iter().enumerate().find_map(|(j, g)| match g {
        GuardRoute::Open(open) if !refused_load && !matches!(built.get(j), Some(Some(_))) => {
            Some(open.clone())
        }
        _ => None,
    }) {
        let refusal = open_requirement_refusal(kb, writer, relation, callee, site, &open);
        refused.push((refusal, Some(site.span.source)));
        return None;
    }
    let slots: Vec<GoalSlot> = (0..total)
        .map(|j| {
            if let Some(Some(t)) = built.get(j).or(carried_built.get(j)) {
                GoalSlot::Built(Value::term(*t))
            } else if let Some(GuardRoute::Declared(var)) = declared.get(j) {
                GoalSlot::Own(Rc::clone(var))
            } else if let Some(GuardRoute::Concrete(dict)) = declared.get(j) {
                GoalSlot::Built(dict.clone())
            } else if let Some(var) = own
                .as_ref()
                .and_then(|(offset, vars)| vars.get(j.checked_sub(*offset)?))
            {
                GoalSlot::Own(Rc::clone(var))
            } else {
                GoalSlot::Unrouted
            }
        })
        .collect();
    // The goal's own bracket (060.1 §2) rides on the marker, not on the goal it wraps: a
    // goal is matched as the term it writes, and the bracket is no argument of it. The goal
    // gets it back where the marker is read as the goal written ([`body_without_goal_markers`]).
    let bracket: Vec<(Option<Symbol>, Value)> = match site.as_expr() {
        Some(Expr::Apply { type_args, .. }) => type_args.clone(),
        _ => Vec::new(),
    };
    if bracket.is_empty() && packed.is_none() && slots.iter().all(|s| matches!(s, GoalSlot::Unrouted)) {
        return None;
    }
    // The type the goal's bracket fixes a guard's parameter at (060.1 §8.10), which the clause
    // is read at: `keep[A = Int64](?x, ?t)` checks `?x` at `Int64`. A type the goal's arguments
    // give needs none — each column then holds its own argument — and binding one column's
    // there would narrow another column typed at their join.
    let carriers: Vec<(usize, Value)> = positions
        .iter()
        .enumerate()
        .filter(|(j, _)| matches!(built.get(*j), Some(Some(_))))
        .filter_map(|(j, &(crid, k))| {
            let read = callee_reads.get(&crid)?.get(k)?;
            let (_, carrier, _) = guard_read_parts(kb, read)?;
            let param = kb.rule_type_params(crid).iter().position(|(_, d)| *d == carrier)?;
            let name = kb.rule_type_params(crid)[param].0;
            bracket_binding(kb, &bracket, name, param).map(|ty| (j, ty))
        })
        .collect();
    let (span, owner) = (site.span, site.owner);
    let node = |e: Expr| NodeOccurrence::new_expr(e, span, owner);
    let mut pos_args: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(total + 2);
    pos_args.push(with_type_args(packed.as_ref().unwrap_or(site), Vec::new()));
    pos_args.push(node(Expr::Ref(callee)));
    for slot in slots {
        pos_args.push(match slot {
            GoalSlot::Own(var) => node(var.as_expr().expect("a parameter's variable").clone()),
            GoalSlot::Built(dict) => node(Expr::Spliced(dict)),
            GoalSlot::Unrouted => node(Expr::Ref(routing.syms.unrouted)),
        });
    }
    let named_args: Vec<(Symbol, Rc<NodeOccurrence>)> = carriers
        .into_iter()
        .map(|(j, ty)| {
            let key = kb.intern(&format!("{}{j}", crate::kb::resolve::WITHIN_CARRIER_PREFIX));
            (key, node(Expr::Spliced(ty)))
        })
        .collect();
    Some(NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: None,
            functor: routing.syms.within,
            pos_args,
            named_args,
            type_args: bracket,
        },
        Rc::clone(site),
        routing.syms.marker_pass,
        owner,
    ))
}

/// A guard the goal puts at a type nothing fixes ([`GuardRoute::Open`]): its spec, the callee's
/// clause and the frame slot of its carrier, its instance, and the type the goal puts there,
/// where it says one.
#[derive(Clone)]
struct OpenGuard {
    spec: Symbol,
    clause: RuleId,
    carrier: u32,
    instance: Value,
    at: Option<Value>,
}

/// The refusal of a goal of `callee` whose guard `open` it puts at a type nothing fixes: a
/// requirement no caller passes (proposal 073 §6.2), named with the type it is open at and, at a
/// type with a head, what the provisions say there (`ListShow`'s `E` at `List[T = ?]`).
fn open_requirement_refusal(
    kb: &mut KnowledgeBase,
    writer: GoalWriter,
    relation: Symbol,
    callee: Symbol,
    site: &Rc<NodeOccurrence>,
    open: &OpenGuard,
) -> TypeError {
    let OpenGuard { spec, clause, carrier, instance, at } = open;
    let (spec, at) = (*spec, at.clone());
    let param = kb
        .rule_type_params(*clause)
        .iter()
        .find(|(_, d)| d == carrier)
        .map(|(name, _)| *name);
    let why = at
        .clone()
        .filter(|t| !matches!(t.head(kb), ViewHead::Var(_)))
        .and_then(|t| dictionary_at_goal(kb, site, callee, *clause, *carrier, instance, &t, &[]).err())
        .map(|miss| match miss {
            GoalDictMiss::Unfixed(why) | GoalDictMiss::Fetch(why) => why,
        });
    let spec_name = short_name_of(kb.qualified_name_of(spec)).to_string();
    let callee_name = kb.local_name_of(callee).to_string();
    let param_name = param.map(|p| kb.local_name_of(p).to_string());
    let requirement = match &param_name {
        Some(p) => format!("`{spec_name}` at `{callee_name}`'s `{p}`"),
        None => format!("`{spec_name}`"),
    };
    let open_at = match at.as_ref().filter(|t| !matches!(t.head(kb), ViewHead::Var(_))) {
        Some(t) => match &why {
            Some(why) => format!(
                "at `{}`, which leaves a type open ({why})",
                type_display_name_value(kb, t)
            ),
            None => format!("at `{}`, which leaves a type open", type_display_name_value(kb, t)),
        },
        None => "at a type nothing fixes".to_string(),
    };
    let bracket = match &param_name {
        Some(p) => format!(", or write the goal's bracket, `{callee_name}[{p} = …](…)`"),
        None => String::new(),
    };
    let actual = match writer {
        GoalWriter::Clause { .. } => format!(
            "the goal puts it {open_at}: a variable the clause's body binds, which no head column \
             reaches, so no caller can pass the dictionary, and none is read from the value when \
             the goal runs — give the argument a type{bracket}"
        ),
        GoalWriter::Query => format!(
            "the query puts it {open_at}, and a query has no caller to pass the dictionary: give \
             the argument a known type{bracket}"
        ),
    };
    TypeError::Other {
        site: TypeError::here(),
        span: Some(site.span.span),
        context: TypeErrorContext::Rule {
            name: relation,
            field: RuleField::Body,
        },
        expected: format!("a requirement, {requirement}, fixed where the goal is written"),
        actual,
    }
}

/// The type a goal's bracket binds a rule's declared type parameter `name` to — by its name,
/// or positionally at `index` of the declared list (positional = named) — or `None` where it
/// binds none.
fn bracket_binding(
    kb: &KnowledgeBase,
    bracket: &[(Option<Symbol>, Value)],
    name: Symbol,
    index: usize,
) -> Option<Value> {
    if let Some((_, ty)) = bracket
        .iter()
        .find(|(k, _)| k.is_some_and(|k| kb.local_name_of(k) == kb.local_name_of(name)))
    {
        return Some(ty.clone());
    }
    bracket.iter().filter(|(k, _)| k.is_none()).nth(index).map(|(_, ty)| ty.clone())
}

/// What one position of a callee's layout is given by the goal ([`route_goal`]), where it is
/// a guard the callee's clause declares.
enum GuardRoute {
    /// The caller's own guard of the requirement at the goal's instance ([`declared_route`]).
    Declared(Rc<NodeOccurrence>),
    /// A concrete instance: the dictionary built there at load.
    Concrete(Value),
    /// An instance that names a type variable of the caller, which declares nothing there, and
    /// the caller's sort where it states the spec at another instance.
    Undeclared(Symbol, Option<Symbol>),
    /// An instance at a type nothing at the goal fixes — a type no head column of the caller
    /// reaches, or a query's variable — which no caller can pass.
    Open(OpenGuard),
    /// A concrete instance nothing provides, or two providers answer: why, as the fetch says.
    Unbuilt(Symbol, String),
    /// No guard: the route is what it was.
    NoGuard,
}

/// Why [`dictionary_at_goal`] builds no dictionary, said as the goal's refusal.
enum GoalDictMiss {
    /// The guard names a parameter of the callee's sort and the goal fixes nothing for it.
    Unfixed(String),
    /// The fetch's account: no provision there, or two that answer.
    Fetch(String),
}

/// The dictionary of the callee's guard `instance` (closed over `callee_clause`'s frame) at
/// the types goal `site` gives its carrier — `at` — and its elements, built from the
/// provisions as a read at those types would fetch it. An element at a parameter of the sort
/// `callee` is written in stands where the goal fixes it (`sort_params`, [`cited_param_values`]):
/// `Box[P = Bool].g(…)` builds `g`'s `Sp[C = A, P = P]` at `P = Bool`. `Err` with what the fetch
/// says where it fetches none — no provision there, or two that answer — and where the goal
/// fixes nothing for such a parameter.
#[allow(clippy::too_many_arguments)]
fn dictionary_at_goal(
    kb: &mut KnowledgeBase,
    site: &Rc<NodeOccurrence>,
    callee: Symbol,
    callee_clause: RuleId,
    carrier: u32,
    instance: &Value,
    at: &Value,
    sort_params: &[CitedParam],
) -> Result<Value, GoalDictMiss> {
    let name = kb.intern("goal_instance");
    let frame_len = (kb.rule_arity(callee_clause) as usize).max(kb.rule_globals(callee_clause).len());
    let fresh: Vec<VarId> = (0..frame_len).map(|_| kb.fresh_var(name)).collect();
    let mut pins = Substitution::new();
    pins.bind_value(kb, fresh[carrier as usize], at.clone());
    let instance_term = instance.expect_term();
    for element in guard_element_vars(kb, callee_clause, instance_term, carrier) {
        match guard_carrier_at_goal(kb, site, callee_clause, element) {
            Some(ty) if instance_is_concrete(kb, &ty) => {
                pins.bind_value(kb, fresh[element as usize], ty);
            }
            _ => {
                return Err(GoalDictMiss::Fetch(
                    "the goal's arguments fix no type at the guard's elements".to_string(),
                ))
            }
        }
    }
    let (opened, _) = crate::kb::node_occurrence::open_value_type(kb, instance, &fresh);
    let ground = walk_type_deep_value(kb, &pins, &opened);
    let (ground, unfixed) =
        cited_sort_params(kb, sort_params, callee_clause, &fresh, &pins, &ground);
    if let Some(param) = unfixed {
        let sort = kb.local_name_of(kb.rule_domain(callee_clause)).to_owned();
        let param = kb.local_name_of(param).to_owned();
        return Err(GoalDictMiss::Unfixed(format!(
            "the guard names `{sort}`'s `{param}`, and nothing at the goal fixes it: write it in \
             the goal's bracket, `{sort}[{param} = …].{}(…)`, or pass an argument at a column \
             typed `{param}`",
            kb.local_name_of(callee),
        )));
    }
    fetch_at_goal(kb, &ground, at).map_err(GoalDictMiss::Fetch)
}

/// The dictionary of the ground `spec` at its carrier's type `at`, built from the provisions as
/// a read at those types fetches it; `Err` with what the fetch says where it fetches none — no
/// provision there, or two that answer — said of the goal at load.
pub(super) fn fetch_at_goal(kb: &mut KnowledgeBase, spec: &Value, at: &Value) -> Result<Value, String> {
    let none = Substitution::new();
    match fetch_dictionary_from_type(kb, &none, spec, at, DefaultRung::Consult, None) {
        FindDictFetch::Fetched(dict) => Ok(dict),
        FindDictFetch::Guard(FindDictOutcome::DontFire) => {
            Err(format!("nothing provides `{}` there", type_display_name_value(kb, spec)))
        }
        // The fetch's account, said of a read at run time; here it is the goal's, at load.
        FindDictFetch::Undecided { detail } | FindDictFetch::Defect { detail } => {
            Err(detail.replace(" at run time:", ":"))
        }
        FindDictFetch::Guard(_) => {
            Err(format!("`{}` is not decided by the goal's types", type_display_name_value(kb, spec)))
        }
    }
}

/// A slot read `callee_clause` takes for a call it wove — `find_dictionary(Desc, pick, ?#0, slot:
/// 0, out: ?#2)` for `pick(?b, ?r)` over `pick(x: Box) requires Desc[T = x.E]` — at goal `site`,
/// written by clause `caller` where it is one: the slot's requirement at the types the goal gives
/// the call's arguments. Where those types fix it, its dictionary built from the provisions as the
/// call's own would be (`r(box(v: red()), ?r)` builds `Desc[T = Red]`), or what the fetch says
/// where nothing provides it there; where its carrier, its only element, is a parameter of the
/// caller, the caller's own guard of the spec there (`r(?b, ?r)` in `g[A](?b: Box[E = A], ?r) :-
/// Desc[T = A], …`), as [`declared_route`] hands a guard read. `None` for any other read, a read
/// under a form (which derives its own), an argument that is no head column of the callee or that
/// the goal gives no type, and a requirement left open otherwise: the bridge derives that one when
/// the call runs.
fn slot_read_at_goal(
    kb: &mut KnowledgeBase,
    fd: Symbol,
    caller: Option<RuleId>,
    site: &Rc<NodeOccurrence>,
    callee_clause: RuleId,
    read: &Rc<NodeOccurrence>,
) -> Option<GuardRoute> {
    let Some(Expr::Apply {
        pos_args, named_args, ..
    }) = read.as_expr()
    else {
        return None;
    };
    if named_args.iter().any(|(k, _)| kb.local_name_of(*k) == REQUIREMENT_IN_FORM_LABEL) {
        return None;
    }
    let slot = named_args
        .iter()
        .find(|(k, _)| kb.local_name_of(*k) == REQUIREMENT_SLOT_LABEL)
        .and_then(|(_, v)| match v.as_expr() {
            Some(Expr::Const(crate::kb::term::Literal::Int(n))) => usize::try_from(*n).ok(),
            _ => None,
        })?;
    let Some(Expr::Ref(op)) = pos_args.get(1).and_then(|o| o.as_expr()) else {
        return None;
    };
    let op = *op;
    let entry = op_dict_entries(kb, op).entries().get(slot)?.clone();
    let rec = crate::kb::op_info::lookup_operation_info(kb, op)?;
    let args = pos_args.get(2..)?;
    if args.len() != rec.params.len() {
        return None;
    }
    let Some(Expr::Apply {
        pos_args: goal_pos,
        named_args: goal_named,
        ..
    }) = site.as_expr()
    else {
        return None;
    };
    // Each argument of the call, a head column of the callee, at the type the goal gives it.
    let columns = rule_head_var_slots(kb, callee_clause);
    let mut types: Vec<Value> = Vec::with_capacity(args.len());
    for arg in args {
        let Some(Expr::Var(Var::DeBruijn(d))) = arg.as_expr() else {
            return None;
        };
        let column = columns.iter().find(|(_, _, v)| v == d).map(|(key, _, _)| *key)?;
        let at = match column {
            SlotKey::Pos(i) => goal_pos.get(i),
            SlotKey::Named(k) => goal_named.iter().find(|(n, _)| same_label(kb, *n, k)).map(|(_, a)| a),
        }
        .cloned()?;
        types.push(goal_arg_type(kb, &at)?);
    }
    let (subst, param_arg_types) = pin_params_from_args(kb, op, &rec.params, &[], Some(&types), true);
    let spec = ground_entry_spec(kb, op, &entry, &param_arg_types, &subst).ok()?;
    let carrier = spec_carrier_param_or_sole(kb, kb.canonical_sort_sym(entry.required_sort))?;
    // The grounding answers the spec on the carrier its entry is written on (a sort view); the
    // fetch reads the application, which the entry's goal spells.
    let concrete = instance_is_concrete(kb, &spec);
    let goal = goal_from_requires_entry(
        kb,
        &RequiresEntry {
            spec,
            ..entry.clone()
        },
    )?;
    let at = goal.bindings.iter().find(|(k, _)| same_label(kb, *k, carrier)).map(|(_, v)| v.clone())?;
    if !concrete {
        // At a parameter of the caller, its only element: the caller's own guard of the spec there.
        if goal.bindings.len() != 1 {
            return None;
        }
        return callers_own_guard(kb, fd, caller?, entry.required_sort, &at).map(GuardRoute::Declared);
    }
    let base = kb.make_sort_ref(goal.spec_sort);
    let spec = parameterized_value(kb, base, &goal.bindings, crate::kb::node_occurrence::empty_span(), None);
    Some(match fetch_at_goal(kb, &spec, &at) {
        Ok(dict) => GuardRoute::Concrete(dict),
        Err(why) => GuardRoute::Unbuilt(entry.required_sort, why),
    })
}

/// The dictionary variable of the one guard of `spec` clause `caller` declares at its type
/// parameter `at`, a type its typing stamped: what a goal of `caller` passes for a requirement
/// of `spec` its callee reads there. `None` where `at` is no parameter of `caller`, or where no
/// guard or two hold it — which of two is the goal's to say, and it says neither.
fn callers_own_guard(
    kb: &mut KnowledgeBase,
    fd: Symbol,
    caller: RuleId,
    spec: Symbol,
    at: &Value,
) -> Option<Rc<NodeOccurrence>> {
    let caller_carrier = caller_param_at(kb, caller, at)?;
    let body: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(caller).to_vec();
    let held: Vec<Rc<NodeOccurrence>> = clause_requirement_reads(kb, fd, &body)
        .into_iter()
        .filter_map(|own| {
            let (own_spec, own_carrier, _) = guard_read_parts(kb, &own)?;
            (own_carrier == caller_carrier && same_sort_canonical(kb, own_spec, spec))
                .then(|| requirement_read_out(kb, fd, &own).map(Rc::clone))
                .flatten()
        })
        .collect();
    match held.as_slice() {
        [one] => Some(Rc::clone(one)),
        _ => None,
    }
}

/// The type the type variable at frame slot `carrier` of `callee_clause` — its guard's carrier
/// or an element — stands at in the goal `site`: the callee column whose bound names it, met
/// with the type of the goal's argument there ([`goal_arg_type`]). `None` where no column says.
fn guard_carrier_at_goal(
    kb: &mut KnowledgeBase,
    site: &Rc<NodeOccurrence>,
    callee_clause: RuleId,
    carrier: u32,
) -> Option<Value> {
    let Some(Expr::Apply {
        pos_args: goal_pos,
        named_args: goal_named,
        ..
    }) = site.as_expr()
    else {
        return None;
    };
    let name = kb.intern("declared_route");
    let frame_len = (kb.rule_arity(callee_clause) as usize).max(kb.rule_globals(callee_clause).len());
    let fresh: Vec<VarId> = (0..frame_len).map(|_| kb.fresh_var(name)).collect();
    let slots = rule_head_var_slots(kb, callee_clause);
    // A column whose argument is an untyped variable puts the carrier at a variable, or at its
    // placeholder (`TypeVar(?logical_var)`), which fixes nothing: another column's type is read
    // first (`related(?x, 3)` is at `Int64`, as `related(3, ?x)` is).
    let mut placeholder = None;
    for (column, bound) in kb.rule_type_bounds(callee_clause).to_vec() {
        if !kb.mentions_var(&bound, &|v| v == Var::DeBruijn(carrier)) {
            continue;
        }
        let Some((key, _, _)) = slots.iter().find(|(_, _, d)| *d == column) else {
            continue;
        };
        let arg = match key {
            SlotKey::Pos(i) => goal_pos.get(*i),
            SlotKey::Named(k) => goal_named
                .iter()
                .find(|(n, _)| kb.local_name_of(*n) == kb.local_name_of(*k))
                .map(|(_, a)| a),
        };
        let Some(arg_ty) = arg.and_then(|a| goal_arg_type(kb, a)) else {
            continue;
        };
        let (opened, _) = crate::kb::node_occurrence::open_value_type(kb, &bound, &fresh);
        let mut pins = Substitution::new();
        if !pin_type_vars(kb, &mut pins, &arg_ty, &opened) {
            continue;
        }
        let x = walk_type_deep_value(kb, &pins, &Value::Var(Var::Global(fresh[carrier as usize])));
        if !matches!(&x, Value::Var(Var::Global(v)) if *v == fresh[carrier as usize]) {
            if matches!(x.head(kb), ViewHead::Var(_)) || type_mentions_type_var(kb, &x) {
                placeholder.get_or_insert(x);
                continue;
            }
            return Some(x);
        }
    }
    placeholder
}

/// Does `ty` — a type the typing of clause `rid` gives a call's or goal's argument — name a
/// variable of the type of one of the clause's head columns? Such a type is one a caller can
/// fix, and a requirement at it is the clause's to declare; a type no head column reaches is
/// fixed by no caller, and a requirement at it is refused (proposal 073 §6.2). A type with no
/// variable in it reaches no head.
pub(super) fn type_reaches_the_head(kb: &mut KnowledgeBase, rid: RuleId, ty: &Value) -> bool {
    fn collect_vars<V: TermView>(kb: &KnowledgeBase, ty: &V, out: &mut Vec<Var>) {
        match ty.head(kb) {
            ViewHead::Var(v) => out.push(v),
            ViewHead::Functor { pos_arity, .. } => {
                view_any_child(kb, ty, pos_arity, |c| {
                    collect_vars(kb, c, out);
                    false
                });
            }
            _ => {}
        }
    }
    let mut vars = Vec::new();
    collect_vars(kb, ty, &mut vars);
    if vars.is_empty() {
        return false;
    }
    let columns: Vec<u32> = rule_head_var_slots(kb, rid).iter().map(|(_, _, d)| *d).collect();
    clause_var_stamps(kb, rid)
        .into_iter()
        .filter(|(d, _)| columns.contains(d))
        .any(|(_, stamp)| kb.mentions_var(&stamp, &|v| vars.contains(&v)))
}

/// Is `ty` a type the clause has fixed: no variable, no wildcard and no unwritten slot in it?
pub(super) fn instance_is_concrete(kb: &mut KnowledgeBase, ty: &Value) -> bool {
    fn names_a_variable<V: TermView>(kb: &KnowledgeBase, ty: &V) -> bool {
        if type_var_name_of_view(kb, ty).is_some() {
            return true;
        }
        match ty.head(kb) {
            ViewHead::Var(_) => true,
            ViewHead::Functor { pos_arity, .. } => view_any_child(kb, ty, pos_arity, |c| names_a_variable(kb, c)),
            _ => false,
        }
    }
    type_is_ground(kb, ty) && !names_a_variable(kb, ty) && !leaves_a_slot_open(kb, ty)
}

/// The type of a rule-body goal's argument that is a construction (`pr(a: 4, b: 5)`, `[5]`),
/// at its arguments' types; `None` for any other argument, and for a construction whose fields
/// that does not fix. An entity's is left open where nothing in it writes a parameter — a named
/// requirement slot (`Pair2[…, O = ?]`) — for the column it meets to say ([`goal_arg_type`]
/// requires it concrete).
pub(super) fn construction_type_at_goal(kb: &mut KnowledgeBase, arg: &Rc<NodeOccurrence>) -> Option<Value> {
    match arg.as_expr() {
        Some(Expr::Constructor { .. } | Expr::Apply { .. }) if !holds_an_operation_call(kb, arg) => {
            entity_construction_type(kb, arg)
        }
        Some(Expr::ListLit(_) | Expr::SetLit(_)) => goal_arg_type(kb, arg),
        Some(Expr::Ref(ctor)) if kb.entity_field_types(*ctor).is_some_and(|f| f.is_empty()) => goal_arg_type(kb, arg),
        _ => None,
    }
}

/// The type of `arg`, a construction of an entity, at its fields' types ([`goal_arg_type`]), each
/// concrete; the parameters no field fixes left open. `None` for any other argument, and where a
/// field's type is not concrete.
fn entity_construction_type(kb: &mut KnowledgeBase, arg: &Rc<NodeOccurrence>) -> Option<Value> {
    let Some(
        Expr::Constructor {
            name: functor,
            pos_args,
            named_args,
            ..
        }
        | Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        },
    ) = arg.as_expr()
    else {
        return None;
    };
    kb.entity_field_types(*functor)?;
    let pos: Vec<Value> = pos_args.iter().map(|a| goal_arg_type(kb, a)).collect::<Option<_>>()?;
    let named: Vec<(Symbol, Value)> = named_args
        .iter()
        .map(|(k, a)| Some((*k, goal_arg_type(kb, a)?)))
        .collect::<Option<_>>()?;
    if pos.iter().chain(named.iter().map(|(_, t)| t)).any(|t| !instance_is_concrete(kb, t)) {
        return None;
    }
    Some(constructor_value_type(kb, *functor, &pos, &named))
}

/// The type of a rule-body goal's argument: a variable's, as the clause's typing stamps it (a
/// fresh variable where it stamps none: a type the clause has not fixed), a literal's, and a
/// constructor's at its arguments' types. `None` for a constructor whose type the value typer
/// reads with a wildcard: it cannot tell a variable of the clause there from any other type.
fn goal_arg_type(kb: &mut KnowledgeBase, arg: &Rc<NodeOccurrence>) -> Option<Value> {
    // A ground construction is at the type its value carries — `[5]`, a `cons` over `nil`,
    // whose `nil` alone leaves the element open.
    let construction = match arg.as_expr() {
        Some(Expr::Constructor { .. } | Expr::ListLit(_) | Expr::SetLit(_)) => true,
        Some(Expr::Apply { functor, .. }) => kb.entity_field_types(*functor).is_some(),
        _ => false,
    };
    // Not one holding a call: the value's type reads an unreduced call as its functor
    // (`some(Set.insert(…))` at `Option[T = Set.insert]`).
    if construction && !holds_an_operation_call(kb, arg) {
        let carried = value_type_term(kb, &Substitution::new(), &Value::Node(Rc::clone(arg)));
        // A collection literal is at its carried type even where that leaves the element open
        // (`[]` at `List[T = ?]`): the type a requirement at it is open at.
        if instance_is_concrete(kb, &carried)
            || matches!(arg.as_expr(), Some(Expr::ListLit(_) | Expr::SetLit(_)))
        {
            return Some(carried);
        }
    }
    match arg.as_expr() {
        Some(Expr::Const(lit)) => Some(literal_sort(kb, lit)),
        Some(Expr::Constructor { name: functor, .. } | Expr::Apply { functor, .. })
            if kb.entity_field_types(*functor).is_some() =>
        {
            let ty = entity_construction_type(kb, arg)?;
            instance_is_concrete(kb, &ty).then_some(ty)
        }
        // A constructor written with no field, `rod()`, is its bare name.
        // Its type even where it leaves a parameter open (`nil` at `List[T = ?]`): the type a
        // requirement at it is open at, which no caller fixes.
        Some(Expr::Ref(ctor)) if kb.entity_field_types(*ctor).is_some_and(|f| f.is_empty()) => {
            Some(constructor_value_type(kb, *ctor, &[], &[]))
        }
        _ => Some(arg.inferred_type().unwrap_or_else(|| {
            let name = kb.intern("goal_arg");
            Value::Var(Var::Global(kb.fresh_var(name)))
        })),
    }
}

/// 060.1 §1 — A GOAL AT THE CALLER'S INSTANCE PASSES THE CALLER'S REQUIREMENT: where the
/// callee's `read` is a guard its clause declares (`rule oddS[E](?l: List[T = E]) :- WeakOrd[T
/// = E], …`) and the goal `site` writes it at a type parameter of the caller's clause `rid`
/// that the caller's own guard states the same requirement at, the dictionary of the
/// caller's guard read, `out` of its read. So `oddS(?t)` in `evenS[E](?l: List[T = E]) :-
/// WeakOrd[T = E], ?l <=> cons(?h, ?t), …`, `?t` a `List[T = E]`, hands `oddS` what `evenS`
/// holds, at every turn of the recursion, and a citation's bracket on `outer[A]` reaches the
/// `cmp[A]` its body calls.
///
/// `at` is the type the guard's carrier stands at in the goal ([`guard_carrier_at_goal`]).
/// `None` where it is another type than a parameter of the caller (a concrete one, `cmp(1, 2,
/// ?c)`, or a larger one, `List[T = E]`), or where the caller declares no guard of the spec
/// there.
fn declared_route(
    kb: &mut KnowledgeBase,
    fd: Symbol,
    rid: RuleId,
    spec: Symbol,
    carrier: u32,
    elements: &[(u32, u32)],
    instance: &Value,
    at: &Value,
    tie: &mut Option<(Symbol, Symbol)>,
) -> Option<Rc<NodeOccurrence>> {
    // The caller's parameter the carrier stands at, as its frame numbers it.
    let caller_carrier = caller_param_at(kb, rid, at)?;
    let body: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
    let held: Vec<(Rc<NodeOccurrence>, Option<Symbol>)> = clause_requirement_reads(kb, fd, &body)
        .into_iter()
        .filter_map(|own| {
            let (own_spec, own_carrier, own_instance) = guard_read_parts(kb, &own)?;
            if own_carrier != caller_carrier
                || !same_sort_canonical(kb, own_spec, spec)
                || !same_instance_at_the_goal(kb, instance, carrier, &own_instance, own_carrier, elements)
            {
                return None;
            }
            let out = Rc::clone(requirement_read_out(kb, fd, &own)?);
            let name = match out.as_expr() {
                Some(Expr::Var(Var::DeBruijn(d))) => kb
                    .rule_provider_requirements(rid)
                    .iter()
                    .find(|r| r.dictionary == *d)
                    .and_then(|r| r.name),
                _ => None,
            };
            Some((out, name))
        })
        .collect();
    // Two of the caller's requirements under two names hold it: two dictionaries, and the goal
    // says which of neither (§8.6), as a citation two named requirements answer is refused.
    if let [(_, Some(first)), (_, Some(second)), ..] = held.as_slice() {
        *tie = Some((*first, *second));
        return None;
    }
    held.into_iter().next().map(|(out, _)| out)
}

/// The type the clause's typing stamped on each of `rid`'s variables, read off its first
/// leaf in the body, by De Bruijn index.
pub(super) fn clause_var_stamps(kb: &KnowledgeBase, rid: RuleId) -> Vec<(u32, Value)> {
    let mut stamps: Vec<(u32, Value)> = Vec::new();
    for g in kb.rule_body_nodes(rid) {
        for_each_var_leaf(g, &mut |var, leaf| {
            let Var::DeBruijn(d) = var else { return };
            if stamps.iter().any(|(seen, _)| *seen == d) {
                return;
            }
            if let Some(ty) = leaf.inferred_type() {
                stamps.push((d, ty));
            }
        });
    }
    stamps
}

/// The type parameter of clause `rid` that `at` — a type its typing stamped on a body leaf —
/// is, by its frame slot: each bound of the clause's head columns is met with the stamp on its
/// column's variable, which is how the typing's variable for a parameter is told. `None` for
/// any other type.
pub(super) fn caller_param_at(kb: &mut KnowledgeBase, rid: RuleId, at: &Value) -> Option<u32> {
    let params: Vec<u32> = kb.rule_type_params(rid).iter().map(|(_, d)| *d).collect();
    caller_slot_at(kb, rid, at, &params)
}

/// The frame slot among `params` of clause `rid` that `at` — a type its typing stamped on a
/// body leaf — is, read as [`caller_param_at`] reads a declared type parameter.
pub(super) fn caller_slot_at(kb: &mut KnowledgeBase, rid: RuleId, at: &Value, params: &[u32]) -> Option<u32> {
    let crate::kb::term_view::ViewHead::Var(target) = crate::kb::term_view::TermView::head(at, kb) else {
        return None;
    };
    let stamps = clause_var_stamps(kb, rid);
    let name = kb.intern("declared_route");
    let frame_len = (kb.rule_arity(rid) as usize).max(kb.rule_globals(rid).len());
    // One frame for every bound: each is pinned in a substitution of its own.
    let fresh: Vec<VarId> = (0..frame_len).map(|_| kb.fresh_var(name)).collect();
    for (column, bound) in kb.rule_type_bounds(rid).to_vec() {
        let Some((_, stamp)) = stamps.iter().find(|(d, _)| *d == column) else {
            continue;
        };
        let (opened, _) = crate::kb::node_occurrence::open_value_type(kb, &bound, &fresh);
        let mut pins = Substitution::new();
        if !pin_type_vars(kb, &mut pins, stamp, &opened) {
            continue;
        }
        for &c in params {
            let x = walk_type_deep_value(kb, &pins, &Value::Var(Var::Global(fresh[c as usize])));
            if matches!(crate::kb::term_view::TermView::head(&x, kb), crate::kb::term_view::ViewHead::Var(v) if v == target) {
                return Some(c);
            }
        }
    }
    None
}

/// The De Bruijn index of frame global `var` among `globals`, a clause's frame: the position
/// counted from the frame's end ([`KnowledgeBase::extend_rule_frame_with_bounds`]).
pub(super) fn frame_slot_of(globals: &[VarId], var: VarId) -> Option<u32> {
    let position = globals.iter().position(|g| *g == var)?;
    Some((globals.len() - 1 - position) as u32)
}

/// The frame slots of clause `rid` that stand for parameters of the sort it is written in: the
/// clause variable a typed head at the parameter (`?x: T`) is bound to. A parameter no typed
/// head names has none.
pub(super) fn sort_param_slots(kb: &KnowledgeBase, rid: RuleId) -> Vec<u32> {
    let globals = kb.rule_globals(rid);
    kb.type_param_syms_of(kb.rule_domain(rid))
        .iter()
        .filter_map(|&param| frame_slot_of(globals, type_param_global_var(kb, param)?))
        .collect()
}

/// 060.1 §1, §8.2 — A REQUIREMENT THE CLAUSE'S SORT STATES, HANDED ON TO A GOAL. A rule of a
/// sort declares no requirement its sort states. Where a goal's callee guards one at the type the
/// goal puts at the sort's parameter — `rule viaH(?x: T, ?t) :- keep(?x, ?t)` in `sort Holder`
/// with `requires Marker[T = T]`, under `rule keep[A](?x: A, ?t) :- Marker[A], …` — the clause
/// reads the requirement as a guard of its own is read, and the goal passes that read
/// ([`declared_route`]). A citation fixing the sort's parameter fills it as it fills any guard
/// at a typed head: `Holder[T = Int64].viaH(1, ?t)` passes `Int64`'s `Marker`. A requirement the
/// sort states under a name is read under it, so a citation's bracket selects it by the name.
///
/// Before any goal is routed, so a read given here is in its clause's layout when the clause's
/// callers are routed; to a fixed point, since a clause given one is a callee whose callers in
/// the sort may take one in turn — a later round asks only the goals of a relation an earlier
/// one gave a read. A clause routed already is left as it is, unless a callee's layout has
/// changed under it, when it is routed again ([`route_rule_goal_requirements`]) and read here
/// first.
fn install_sort_requirement_reads(kb: &mut KnowledgeBase, fd: Symbol) {
    let pass = kb.register_pass(SORT_REQUIREMENT_READ_PASS);
    // The relations given a read in the round before; `None` in the first round, which asks
    // every goal.
    let mut grown: Option<HashSet<Symbol>> = None;
    loop {
        let mut grew: HashSet<Symbol> = HashSet::new();
        for rid in kb.live_rule_ids() {
            if kb.is_fact(rid)
                || kb.has_equational_head(rid)
                || rule_body_is_typed_once(kb, rid)
                || (holds_goal_marker(kb, rid) && !holds_stale_marker(kb, rid))
            {
                continue;
            }
            let slots = sort_param_slots(kb, rid);
            if slots.is_empty() {
                continue;
            }
            for (site, callee) in cited_goals(kb, rid) {
                if grown.as_ref().is_some_and(|grown| !grown.contains(&callee)) {
                    continue;
                }
                for (crid, _) in requirement_read_counts(kb, callee) {
                    let reads = clause_requirement_reads(kb, fd, &kb.rule_body_nodes(crid).to_vec());
                    for read in reads {
                        if let Some(handed) = handed_on_requirement(kb, fd, rid, &slots, &site, crid, &read) {
                            add_sort_requirement_read(kb, rid, fd, pass, &handed);
                            if let Value::Term { id, .. } = kb.rule_head_value(rid).clone() {
                                grew.extend(kb.head_functor(id));
                            }
                        }
                    }
                }
            }
        }
        if grew.is_empty() {
            break;
        }
        grown = Some(grew);
    }
}

/// Each goal of clause `rid` that cites a relation, with the relation: a goal as written, or the
/// goal a citation marker wraps.
fn cited_goals(kb: &KnowledgeBase, rid: RuleId) -> Vec<(Rc<NodeOccurrence>, Symbol)> {
    goal_sites(kb, rid)
        .into_iter()
        .filter_map(|site| match goal_marker(kb, &site) {
            Some(marker) => Some((Rc::clone(marker.goal), marker.relation)),
            None => relation_goal_callee(kb, &site).map(|callee| (site, callee)),
        })
        .collect()
}

/// Does a citation marker of `rid` hold another number of slots than its callee's layout has
/// positions now ([`Routing::has_stale_marker`], read without its memo, which a read added here
/// would leave behind)?
fn holds_stale_marker(kb: &KnowledgeBase, rid: RuleId) -> bool {
    goal_sites(kb, rid).iter().any(|n| {
        goal_marker(kb, n).is_some_and(|m| {
            let total: usize = requirement_read_counts(kb, m.relation).iter().map(|(_, c)| c).sum();
            m.slots.len() != total
        })
    })
}

/// The requirement of its sort that clause `rid` reads for goal `site` to pass `read`, a guard
/// of `callee_clause` or a read it takes for a call ([`install_sort_requirement_reads`]): the
/// requirement as the sort states it, in `rid`'s frame, where the sort states one that the read's
/// instance at the goal ([`guard_instance_at_goal`], [`call_read_at_goal`]) is
/// ([`sort_states_requirement`]) and the clause does not read it already.
fn handed_on_requirement(
    kb: &mut KnowledgeBase,
    fd: Symbol,
    rid: RuleId,
    slots: &[u32],
    site: &Rc<NodeOccurrence>,
    callee_clause: RuleId,
    read: &Rc<NodeOccurrence>,
) -> Option<HandedOn> {
    let (spec, at_goal) = match guard_read_parts(kb, read) {
        Some((spec, carrier, instance)) => (
            spec,
            guard_instance_at_goal(kb, rid, slots, site, callee_clause, carrier, instance.expect_term())?,
        ),
        None => call_read_at_goal(kb, rid, slots, site, callee_clause, read)?,
    };
    let SortStates::Once(stated) = sort_states_requirement(kb, rid, spec, &Value::term(at_goal.instance)) else {
        return None;
    };
    if sort_requirement_read(kb, fd, rid, spec, &at_goal).is_some() {
        return None;
    }
    let elements = debruijn_vars(kb, stated).into_iter().filter(|v| *v != at_goal.carrier).collect();
    Some(HandedOn {
        spec,
        at_goal: GuardAtGoal {
            carrier: at_goal.carrier,
            elements,
            instance: stated,
        },
    })
}

/// The dictionary variable of clause `rid`'s read of a requirement of `spec` that `need` — a
/// callee's read at the goal, in `rid`'s frame — is: one at `need`'s carrier that binds as `need`
/// does every parameter `need` writes ([`install_sort_requirement_reads`]). A parameter `need`
/// leaves unwritten the read may bind: the sort's requirement fixes what the callee leaves open.
fn sort_requirement_read(
    kb: &mut KnowledgeBase,
    fd: Symbol,
    rid: RuleId,
    spec: Symbol,
    need: &GuardAtGoal,
) -> Option<Rc<NodeOccurrence>> {
    let wanted = named_bindings(kb, &Value::term(need.instance));
    clause_requirement_reads(kb, fd, &kb.rule_body_nodes(rid).to_vec())
        .into_iter()
        .find(|own| match guard_read_parts(kb, own) {
            Some((own_spec, own_carrier, own_instance)) => {
                own_carrier == need.carrier
                    && same_sort_canonical(kb, own_spec, spec)
                    && wanted.iter().all(|(name, value)| {
                        spec_binding_value(kb, &own_instance, name)
                            .is_some_and(|own| views_structurally_equal(kb, value, &own))
                    })
            }
            // The clause's read for a call of its own, where it is the requirement the sort
            // states at the same parameter: one dictionary, which a citation fills as the
            // sort's (`route_requirement_read`), and `need` asks of the sort's requirement.
            None => own_call_read_is_the_sorts(kb, rid, spec, need.carrier, own),
        })
        .and_then(|own| requirement_read_out(kb, fd, &own).cloned())
}

/// Is `read`, a read clause `rid` takes for a call, the requirement of `spec` its sort states
/// with the carrier at frame slot `carrier` ([`sorts_requirement_call_read_slot`])?
fn own_call_read_is_the_sorts(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    spec: Symbol,
    carrier: u32,
    read: &Rc<NodeOccurrence>,
) -> bool {
    let Some((own_spec, op, args)) = call_read_parts(kb, read) else {
        return false;
    };
    same_sort_canonical(kb, own_spec, spec)
        && sorts_requirement_call_read_slot(kb, rid, spec, op, args) == Some(carrier)
}

/// A read for a call of a spec's member — `find_dictionary(Marker, tag, ?#2, out: ?#4)` — as
/// its spec, the member and the call's arguments. `None` for a guard's read and a slot read.
fn call_read_parts<'a>(
    kb: &KnowledgeBase,
    read: &'a Rc<NodeOccurrence>,
) -> Option<(Symbol, Symbol, &'a [Rc<NodeOccurrence>])> {
    let Some(Expr::Apply {
        pos_args, named_args, ..
    }) = read.as_expr()
    else {
        return None;
    };
    if named_args.iter().any(|(k, _)| {
        let label = kb.local_name_of(*k);
        label == PROVIDER_CARRIER_TYPE_LABEL || label == REQUIREMENT_SLOT_LABEL
    }) {
        return None;
    }
    match (pos_args.first()?.as_expr(), pos_args.get(1)?.as_expr()) {
        (Some(Expr::Ref(spec)), Some(Expr::Ref(op))) => Some((*spec, *op, &pos_args[2..])),
        _ => None,
    }
}

/// `spec[carrier = ?#slot]`: the spec with its carrier parameter at frame slot `slot`, what a
/// read for a call at a receiver there needs.
fn carrier_instance(kb: &mut KnowledgeBase, spec: Symbol, slot: u32) -> Option<TermId> {
    let carrier_key = spec_carrier_param_or_sole(kb, kb.canonical_sort_sym(spec))?;
    let at_carrier = kb.alloc(Term::Var(Var::DeBruijn(slot)));
    Some(kb.alloc(Term::Fn {
        functor: spec,
        pos_args: SmallVec::new(),
        named_args: SmallVec::from_slice(&[(carrier_key, at_carrier)]),
    }))
}

/// Each binding an instance writes, by its parameter's local name.
fn named_bindings(kb: &KnowledgeBase, instance: &Value) -> Vec<(String, Value)> {
    instance
        .named_keys(kb)
        .into_iter()
        .filter_map(|k| Some((kb.local_name_of(k).to_owned(), named_child_value(kb, instance, k)?)))
        .collect()
}

/// A guard's instance at a goal, in the citing clause's frame ([`guard_instance_at_goal`]): the
/// slots of its carrier and of each element the goal puts at a parameter of the clause's sort,
/// and the instance with each of them there and each element the goal fixes at a concrete type.
struct GuardAtGoal {
    carrier: u32,
    elements: Vec<u32>,
    instance: TermId,
}

/// The instance `instance` of `callee_clause`'s guard at `carrier` stands at in goal `site` of
/// clause `rid`, written in `rid`'s frame: the carrier at the parameter of `rid`'s sort the goal
/// puts it at — one of `slots` — and each other variable of the instance at a parameter of the
/// sort or at the concrete type the goal puts it at. `None` where the goal puts one at another
/// type.
fn guard_instance_at_goal(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    slots: &[u32],
    site: &Rc<NodeOccurrence>,
    callee_clause: RuleId,
    carrier: u32,
    instance: TermId,
) -> Option<GuardAtGoal> {
    if slots.is_empty() {
        return None;
    }
    let carrier_at = guard_carrier_at_goal(kb, site, callee_clause, carrier)?;
    let carrier_slot = caller_slot_at(kb, rid, &carrier_at, slots)?;
    let mut placed: Vec<(u32, TermId)> = vec![(carrier, kb.alloc(Term::Var(Var::DeBruijn(carrier_slot))))];
    let mut elements = Vec::new();
    for var in debruijn_vars(kb, instance) {
        if var == carrier {
            continue;
        }
        let at = guard_carrier_at_goal(kb, site, callee_clause, var)?;
        if let Some(slot) = caller_slot_at(kb, rid, &at, slots) {
            elements.push(slot);
            placed.push((var, kb.alloc(Term::Var(Var::DeBruijn(slot)))));
        } else if instance_is_concrete(kb, &at) {
            let ty = crate::kb::node_occurrence::value_to_term(kb, &at)
                .expect("a type the goal puts a guard's element at is a type, which has a term");
            placed.push((var, ty));
        } else {
            return None;
        }
    }
    Some(GuardAtGoal {
        carrier: carrier_slot,
        elements,
        instance: place_debruijn(kb, instance, &placed),
    })
}

/// A read `callee_clause` takes for a call of a spec's member — `find_dictionary(Marker, tag,
/// ?#2, out: ?#4)` for `Marker.tag(?x, ?t)` — at goal `site` of clause `rid`: the spec, and the
/// instance the read is at in `rid`'s frame, the spec with its carrier at the parameter of `rid`'s
/// sort — one of `slots` — the goal puts the call's receiver at. `None` for a guard's read, which
/// carries its instance ([`guard_instance_at_goal`]), a slot read and a `SortDomain` read, a
/// read whose receiver is no head column of the callee, and where the goal puts the receiver at
/// another type.
fn call_read_at_goal(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    slots: &[u32],
    site: &Rc<NodeOccurrence>,
    callee_clause: RuleId,
    read: &Rc<NodeOccurrence>,
) -> Option<(Symbol, GuardAtGoal)> {
    if slots.is_empty() {
        return None;
    }
    let (spec, op, args) = call_read_parts(kb, read)?;
    if is_sort_domain_spec(kb, spec) {
        return None;
    }
    let info = crate::kb::op_info::lookup_operation_info(kb, op)?;
    let receiver = receiver_param_index(kb, &info.params, spec)?;
    let Some(Expr::Var(Var::DeBruijn(witness))) = args.get(receiver).and_then(|a| a.as_expr()) else {
        return None;
    };
    let witness = *witness;
    // The goal's argument at the callee's column the receiver is.
    let Some(Expr::Apply {
        pos_args: goal_pos,
        named_args: goal_named,
        ..
    }) = site.as_expr()
    else {
        return None;
    };
    let column = rule_head_var_slots(kb, callee_clause)
        .into_iter()
        .find(|(_, _, d)| *d == witness)
        .map(|(key, _, _)| key)?;
    let arg = match column {
        SlotKey::Pos(i) => goal_pos.get(i),
        SlotKey::Named(k) => goal_named
            .iter()
            .find(|(n, _)| kb.local_name_of(*n) == kb.local_name_of(k))
            .map(|(_, a)| a),
    }
    .cloned()?;
    let at = goal_arg_type(kb, &arg)?;
    let carrier = caller_slot_at(kb, rid, &at, slots)?;
    let instance = carrier_instance(kb, spec, carrier)?;
    Some((
        spec,
        GuardAtGoal {
            carrier,
            elements: Vec::new(),
            instance,
        },
    ))
}

/// Is the read clause `rid` takes for a call of `op`, a member of `spec`, whose arguments are
/// `read_args` (the read's from its third on), the requirement `rid`'s sort states — the call's
/// receiver a head column typed at a parameter of the sort that the sort's requirement of `spec`
/// has as its carrier? `Conv.conv(?x, ?r)` with `?x: T` in `sort Two2` with `requires Conv[A = T,
/// B = U]` is (060.1 §8.2).
pub(super) fn call_read_is_the_sorts_requirement(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    spec: Symbol,
    op: Symbol,
    read_args: &[Rc<NodeOccurrence>],
) -> bool {
    sorts_requirement_call_read_slot(kb, rid, spec, op, read_args).is_some()
}

/// [`call_read_is_the_sorts_requirement`], answering the frame slot of the sort's parameter the
/// call's receiver is typed at.
fn sorts_requirement_call_read_slot(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    spec: Symbol,
    op: Symbol,
    read_args: &[Rc<NodeOccurrence>],
) -> Option<u32> {
    let slots = sort_param_slots(kb, rid);
    if slots.is_empty() {
        return None;
    }
    let receiver = crate::kb::op_info::lookup_operation_info(kb, op)
        .and_then(|info| receiver_param_index(kb, &info.params, spec))?;
    let Some(Expr::Var(Var::DeBruijn(witness))) = read_args.get(receiver).and_then(|a| a.as_expr()) else {
        return None;
    };
    let at_param = kb
        .rule_type_bounds(rid)
        .iter()
        .find(|(column, _)| column == witness)
        .and_then(|(_, bound)| match bound.head(kb) {
            ViewHead::Var(Var::DeBruijn(slot)) => Some(slot),
            _ => None,
        })
        .filter(|slot| slots.contains(slot));
    let slot = at_param?;
    let need = carrier_instance(kb, spec, slot)?;
    matches!(sort_states_requirement(kb, rid, spec, &Value::term(need)), SortStates::Once(_)).then_some(slot)
}

/// Is `read`, a read clause `rid` takes for a call, one a named requirement slot of a type its
/// typing gives a variable may state — the slot's spec the read's, its sort the head of the type
/// (`Box[T = t, O = o]` for `?p` beside `WeakOrd.compare(?x, ?y, ?c)` under `requires O:
/// WeakOrd[T]`)? The citation's reading ([`bracketed_goal_routes`]) decides whether one does.
fn read_off_a_named_slot(kb: &mut KnowledgeBase, rid: RuleId, read: &Rc<NodeOccurrence>) -> bool {
    let Some((spec, _, _)) = call_read_parts(kb, read) else {
        return false;
    };
    clause_var_stamps(kb, rid).into_iter().any(|(_, ty)| {
        let TypeExtractor::Parameterized { base, .. } = extract_type(kb, &ty) else {
            return false;
        };
        kb.named_requirement_slots(base)
            .iter()
            .any(|slot| slot.spec_base.is_some_and(|s| same_sort_canonical(kb, s, spec)))
    })
}

/// The requirement of its sort that `read`, a read clause `rid` takes for a call, is
/// ([`call_read_is_the_sorts_requirement`]): its spec, the frame slot of the sort's parameter the
/// call's receiver is typed at, and the requirement as the sort states it there, in `rid`'s frame.
fn sorts_call_read_instance(kb: &mut KnowledgeBase, rid: RuleId, read: &Rc<NodeOccurrence>) -> Option<(Symbol, u32, TermId)> {
    let (spec, op, args) = call_read_parts(kb, read)?;
    let args = args.to_vec();
    let slot = sorts_requirement_call_read_slot(kb, rid, spec, op, &args)?;
    let need = carrier_instance(kb, spec, slot)?;
    match sort_states_requirement(kb, rid, spec, &Value::term(need)) {
        SortStates::Once(stated) => Some((spec, slot, stated)),
        _ => None,
    }
}

/// The De Bruijn indices `term` names, each once, in the order met.
fn debruijn_vars(kb: &KnowledgeBase, term: TermId) -> Vec<u32> {
    fn walk(kb: &KnowledgeBase, term: TermId, out: &mut Vec<u32>) {
        match kb.get_term(term) {
            Term::Var(Var::DeBruijn(i)) => {
                if !out.contains(i) {
                    out.push(*i);
                }
            }
            Term::Fn {
                pos_args, named_args, ..
            } => {
                for a in pos_args.iter().chain(named_args.iter().map(|(_, a)| a)) {
                    walk(kb, *a, out);
                }
            }
            _ => {}
        }
    }
    let mut out = Vec::new();
    walk(kb, term, &mut out);
    out
}

/// `term` with each De Bruijn index `from` of `placed` replaced by its term, all at once.
fn place_debruijn(kb: &mut KnowledgeBase, term: TermId, placed: &[(u32, TermId)]) -> TermId {
    match kb.get_term(term) {
        Term::Var(Var::DeBruijn(i)) => match placed.iter().find(|(from, _)| from == i) {
            Some((_, to)) => *to,
            None => term,
        },
        Term::Fn { .. } => kb.map_fn_children(term, |kb, child| place_debruijn(kb, child, placed)),
        _ => term,
    }
}

/// A requirement of its sort a clause reads for a goal ([`handed_on_requirement`]): its spec and
/// its instance at the goal.
struct HandedOn {
    spec: Symbol,
    at_goal: GuardAtGoal,
}

/// What the sort a clause is written in states of a requirement ([`sort_states_requirement`]).
enum SortStates {
    /// Nothing at that instance.
    No,
    /// One requirement: its instance in the clause's frame, each of the sort's parameters at the
    /// clause variable standing for it, and as written where it has none.
    Once(TermId),
    /// Two, each under a name of its own: two dictionaries, and nothing says which.
    Twice(Symbol, Symbol),
    /// Two with no name, at two instances the goal's both fit: two dictionaries, as written.
    TwoInstances(String, String),
}

/// What the sort clause `rid` is written in states of the requirement `instance` of `spec`,
/// written in `rid`'s frame: the requirements of the sort's chain that bind as `instance` does
/// every parameter `instance` writes — a clause variable standing for the sort's parameter where
/// `instance` writes that variable — or, in a spec's own rule, the spec at its own parameters.
/// One `instance` leaves unwritten the sort may fix: a guard's omitted element restricts nothing,
/// and the read the clause takes is the sort's requirement as stated. Two such requirements
/// under two names are two (§8.6); one beside unnamed ones is that one.
fn sort_states_requirement(kb: &mut KnowledgeBase, rid: RuleId, spec: Symbol, instance: &Value) -> SortStates {
    let written = named_bindings(kb, instance);
    let globals = kb.rule_globals(rid).to_vec();
    // The frame slot of the sort's parameter a binding names.
    let slot_of = |kb: &KnowledgeBase, binding: &Value| -> Option<u32> {
        let var = match binding.head(kb) {
            ViewHead::Var(Var::Global(v)) => v,
            _ => type_param_global_var(kb, ref_or_nullary_name_view(kb, binding)?)?,
        };
        frame_slot_of(&globals, var)
    };
    let domain = kb.rule_domain(rid);
    // A spec's own rule reads the spec at its own parameters (060.1 §3): each binding the
    // instance writes is the clause variable standing for the parameter of that name.
    if same_sort_canonical(kb, domain, spec) {
        let params: Vec<Symbol> = kb.type_param_syms_of(domain).to_vec();
        let own = written.iter().all(|(name, value)| {
            let ViewHead::Var(Var::DeBruijn(at)) = value.head(kb) else {
                return false;
            };
            params
                .iter()
                .find(|p| kb.local_name_of(**p) == name.as_str())
                .and_then(|p| frame_slot_of(&globals, type_param_global_var(kb, *p)?))
                == Some(at)
        });
        if !own {
            return SortStates::No;
        }
        let named: Vec<(Symbol, TermId)> = params
            .iter()
            .map(|&p| {
                let at = type_param_global_var(kb, p)
                    .and_then(|v| frame_slot_of(&globals, v))
                    .map(|slot| kb.alloc(Term::Var(Var::DeBruijn(slot))));
                (p, at.unwrap_or_else(|| kb.alloc(Term::Ref(p))))
            })
            .collect();
        return SortStates::Once(instance_term(kb, spec, named));
    }
    let mut stated: Vec<RequiresEntry> = Vec::new();
    for entry in requires_chain(kb, domain) {
        let at_instance = same_sort_canonical(kb, entry.required_sort, spec)
            && written.iter().all(|(name, value)| {
                let Some(stated) = spec_binding_value(kb, &entry.spec, name) else {
                    return false;
                };
                match value.head(kb) {
                    ViewHead::Var(Var::DeBruijn(at)) => slot_of(kb, &stated) == Some(at),
                    _ => views_structurally_equal(kb, value, &stated),
                }
            });
        let again = stated.iter().any(|e| {
            e.binder == entry.binder && (e.binder.is_some() || same_type_bindings(kb, spec, &e.spec, &entry.spec))
        });
        if at_instance && !again {
            stated.push(entry);
        }
    }
    let mut names = stated.iter().filter_map(|e| e.binder);
    if let (Some(first), Some(second)) = (names.next(), names.next()) {
        return SortStates::Twice(first, second);
    }
    // One named beside unnamed ones is that one; the named one states it. Two unnamed at two
    // instances the goal's both fit are two requirements, and the goal says neither.
    let entry = match stated.iter().find(|e| e.binder.is_some()) {
        Some(named) => named.clone(),
        None => match stated.as_slice() {
            [] => return SortStates::No,
            [one] => one.clone(),
            [first, second, ..] => {
                return SortStates::TwoInstances(
                    render_requires_entry(kb, first),
                    render_requires_entry(kb, second),
                )
            }
        },
    };
    let entry = entry.spec;
    let params: Vec<Symbol> = kb.type_param_syms_of(kb.canonical_sort_sym(spec)).to_vec();
    let mut named: Vec<(Symbol, TermId)> = Vec::with_capacity(params.len());
    for p in params {
        let Some(binding) = spec_binding_value(kb, &entry, kb.local_name_of(p)) else {
            continue;
        };
        let term = crate::kb::node_occurrence::value_to_term(kb, &binding)
            .expect("a requirement's binding is a type, which has a term");
        named.push((p, place_sort_params(kb, &globals, term)));
    }
    SortStates::Once(instance_term(kb, spec, named))
}

/// Do two requirements of `spec` bind each of its type parameters alike — one instance, whatever
/// members each binds?
fn same_type_bindings(kb: &KnowledgeBase, spec: Symbol, a: &Value, b: &Value) -> bool {
    kb.type_param_syms_of(kb.canonical_sort_sym(spec)).iter().all(|p| {
        let name = kb.local_name_of(*p);
        match (spec_binding_value(kb, a, name), spec_binding_value(kb, b, name)) {
            (Some(x), Some(y)) => views_structurally_equal(kb, &x, &y),
            (None, None) => true,
            _ => false,
        }
    })
}

/// `spec[…named]`, its bindings in the order the store keeps a record's.
fn instance_term(kb: &mut KnowledgeBase, spec: Symbol, mut named: Vec<(Symbol, TermId)>) -> TermId {
    kb.canonicalize_record_named_args(spec, &mut named);
    kb.alloc(Term::Fn {
        functor: spec,
        pos_args: SmallVec::new(),
        named_args: named.into_iter().collect(),
    })
}

/// `term` with each parameter of a clause's sort it names — by its name or as its variable — at
/// the clause variable standing for it, where the frame `globals` has one.
fn place_sort_params(kb: &mut KnowledgeBase, globals: &[VarId], term: TermId) -> TermId {
    let param_var = match kb.get_term(term) {
        Term::Var(Var::Global(v)) => Some(*v),
        Term::Ref(s) | Term::Ident(s) => type_param_global_var(kb, *s),
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => type_param_global_var(kb, *functor),
        _ => None,
    };
    if let Some(slot) = param_var.and_then(|v| frame_slot_of(globals, v)) {
        return kb.alloc(Term::Var(Var::DeBruijn(slot)));
    }
    match kb.get_term(term) {
        Term::Fn { .. } => kb.map_fn_children(term, |kb, child| place_sort_params(kb, globals, child)),
        _ => term,
    }
}

/// Give clause `rid` the read of the requirement `handed` names, in the form a written guard's
/// read has (`install_rule_provider_dictionaries`) — `find_dictionary(Marker[T = ?#0], Marker,
/// ?#0, out: ?#d, carrier_type: true)`, each element's variable after the carrier's — before the
/// body's goals.
fn add_sort_requirement_read(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    fd: Symbol,
    pass: crate::kb::occurrence::PassId,
    handed: &HandedOn,
) {
    let anchor = Rc::clone(kb.rule_body_nodes(rid).first().expect("a clause with a goal has a body"));
    let (read, _) = sort_requirement_read_node(kb, rid, fd, pass, handed, &anchor);
    kb.prepend_generated_body_goals(rid, vec![read]);
}

/// The read of the requirement `handed` names, for clause `rid`, in the form a written guard's
/// read has ([`add_sort_requirement_read`]), anchored at `anchor`, and the variable its `out`
/// binds — a new clause variable, the frame extended by it. The caller places the read.
fn sort_requirement_read_node(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    fd: Symbol,
    pass: crate::kb::occurrence::PassId,
    handed: &HandedOn,
    anchor: &Rc<NodeOccurrence>,
) -> (Rc<NodeOccurrence>, Rc<NodeOccurrence>) {
    let HandedOn {
        spec,
        at_goal: GuardAtGoal {
            carrier,
            ref elements,
            instance,
        },
    } = *handed;
    let d_index = kb.rule_globals(rid).len() as u32;
    let dict_name = kb.intern("dict");
    let d = kb.fresh_var(dict_name);
    let bounds = kb.rule_type_bounds(rid).to_vec();
    kb.extend_rule_frame_with_bounds(rid, &[d], bounds);
    let (span, owner) = (anchor.span, anchor.owner);
    let node = |e: Expr| NodeOccurrence::new_expr(e, span, owner);
    let spec_ref = Value::term(kb.alloc(Term::Ref(spec)));
    let out_label = kb.intern(REQUIREMENT_OUT_LABEL);
    let carrier_label = kb.intern(PROVIDER_CARRIER_TYPE_LABEL);
    let out = node(Expr::Var(Var::DeBruijn(d_index)));
    let named_args = vec![
        (out_label, Rc::clone(&out)),
        (carrier_label, node(Expr::Const(Literal::Bool(true)))),
    ];
    let read = NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: None,
            functor: fd,
            pos_args: [
                node(Expr::Spliced(Value::term(instance))),
                node(Expr::Spliced(spec_ref)),
                node(Expr::Var(Var::DeBruijn(carrier))),
            ]
            .into_iter()
            .chain(elements.iter().map(|e| node(Expr::Var(Var::DeBruijn(*e)))))
            .collect(),
            named_args,
            type_args: Vec::new(),
        },
        Rc::clone(anchor),
        pass,
        owner,
    );
    (read, out)
}

/// What the sort clause `rid` is written in states for a call of a member of `spec` at the
/// sort's parameter at frame slot `slot`, the call's bracket (`bracket`, its receiver's written
/// type) writing what else it says ([`sort_requirement_for_call`]).
pub(super) enum SortCallRequirement {
    /// Nothing the call's bracket writes picks among what the sort states: the read the clause
    /// takes for it is routed where the rule is cited, as before.
    Unpicked,
    /// The one requirement the bracket picks, in the clause's frame.
    Picked(TermId),
    /// Two with no name the call fits, rendered: refused, nothing at the call saying which.
    Two(String, String),
}

/// [`SortCallRequirement`] of a call of `spec` at the sort parameter at frame slot `slot` of
/// clause `rid`, written with the receiver bracket `bracket` (`Conv[A = T, B = Bool]`) or none.
pub(super) fn sort_requirement_for_call(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    spec: Symbol,
    slot: u32,
    bracket: Option<&Value>,
) -> SortCallRequirement {
    let Some(carrier_key) = spec_carrier_param_or_sole(kb, kb.canonical_sort_sym(spec)) else {
        return SortCallRequirement::Unpicked;
    };
    let globals = kb.rule_globals(rid).to_vec();
    let mut named: Vec<(Symbol, TermId)> = vec![(carrier_key, kb.alloc(Term::Var(Var::DeBruijn(slot))))];
    let mut written = false;
    for (key, value) in bracket.map(|b| named_bindings(kb, b)).unwrap_or_default() {
        if key == kb.local_name_of(carrier_key) {
            continue;
        }
        let Some(param) = sort_type_params_as_pairs(kb, kb.canonical_sort_sym(spec))
            .iter()
            .map(|(p, _)| *p)
            .find(|p| kb.local_name_of(*p) == key)
        else {
            continue;
        };
        let Ok(term) = crate::kb::node_occurrence::value_to_term(kb, &value) else {
            continue;
        };
        named.push((param, place_sort_params(kb, &globals, term)));
        written = true;
    }
    let asked = instance_term(kb, spec, named);
    match sort_states_requirement(kb, rid, spec, &Value::term(asked)) {
        SortStates::TwoInstances(first, second) => SortCallRequirement::Two(first, second),
        SortStates::Once(stated) if written => SortCallRequirement::Picked(stated),
        _ => SortCallRequirement::Unpicked,
    }
}

/// The clause's read of its sort's requirement `stated` of `spec` at frame slot `slot` — the
/// one it holds, or a new one ([`sort_requirement_read_node`], anchored at `anchor`) with the
/// read to place before the body — and the variable its `out` binds.
pub(super) fn sort_requirement_read_of(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    fd: Symbol,
    spec: Symbol,
    slot: u32,
    stated: TermId,
    anchor: &Rc<NodeOccurrence>,
) -> (Rc<NodeOccurrence>, Option<Rc<NodeOccurrence>>) {
    let elements = debruijn_vars(kb, stated).into_iter().filter(|v| *v != slot).collect();
    let handed = HandedOn {
        spec,
        at_goal: GuardAtGoal {
            carrier: slot,
            elements,
            instance: stated,
        },
    };
    if let Some(var) = sort_requirement_read(kb, fd, rid, spec, &handed.at_goal) {
        return (var, None);
    }
    let pass = kb.register_pass(SORT_REQUIREMENT_READ_PASS);
    let (read, var) = sort_requirement_read_node(kb, rid, fd, pass, &handed, anchor);
    (var, Some(read))
}

/// Kernel-language §5.3, 060.1 §8.2 — THE REQUIREMENTS CLAUSE `rid`'S SORT STATES AT ITS
/// PARAMETER at frame slot `slot`, with no name and once, each as the guard the clause reads it
/// as: its spec, its instance in the clause's frame and the variable its read binds, and the read
/// itself where the clause holds none yet ([`sort_requirement_read_node`], anchored at
/// `anchor`), for the caller to place. `PartialEq[T = T]` of `sort Box requires PartialEq[T =
/// T]` at `T`'s slot: the condition `Box`'s equality at `Self` is built over in its rules, as in
/// its operations. A requirement stated under a name is the citation's to write (§8.2), and two
/// the slot's instance both fit are no one requirement: neither is returned.
pub(super) fn sort_requirements_at_slot(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    fd: Symbol,
    slot: u32,
    anchor: &Rc<NodeOccurrence>,
) -> Vec<(Symbol, Value, Rc<NodeOccurrence>, Option<Rc<NodeOccurrence>>)> {
    let pass = kb.register_pass(SORT_REQUIREMENT_READ_PASS);
    let domain = kb.rule_domain(rid);
    let globals = kb.rule_globals(rid).to_vec();
    let mut specs: Vec<Symbol> = Vec::new();
    for entry in requires_chain(kb, domain) {
        if entry.binder.is_some() || specs.iter().any(|s| same_sort_canonical(kb, *s, entry.required_sort)) {
            continue;
        }
        let Some(key) = spec_carrier_param_or_sole(kb, kb.canonical_sort_sym(entry.required_sort)) else {
            continue;
        };
        let at_slot = spec_binding_value(kb, &entry.spec, kb.local_name_of(key)).is_some_and(|binding| {
            let var = match binding.head(kb) {
                ViewHead::Var(Var::Global(v)) => Some(v),
                _ => ref_or_nullary_name_view(kb, &binding).and_then(|s| type_param_global_var(kb, s)),
            };
            var.and_then(|v| frame_slot_of(&globals, v)) == Some(slot)
        });
        if at_slot {
            specs.push(entry.required_sort);
        }
    }
    let mut out = Vec::new();
    for spec in specs {
        let Some(key) = spec_carrier_param_or_sole(kb, kb.canonical_sort_sym(spec)) else {
            continue;
        };
        let at = kb.alloc(Term::Var(Var::DeBruijn(slot)));
        let asked = instance_term(kb, spec, vec![(key, at)]);
        let SortStates::Once(stated) = sort_states_requirement(kb, rid, spec, &Value::term(asked)) else {
            continue;
        };
        let elements = debruijn_vars(kb, stated).into_iter().filter(|v| *v != slot).collect();
        let handed = HandedOn {
            spec,
            at_goal: GuardAtGoal {
                carrier: slot,
                elements,
                instance: stated,
            },
        };
        match sort_requirement_read(kb, fd, rid, spec, &handed.at_goal) {
            Some(var) => out.push((spec, Value::term(stated), var, None)),
            None => {
                let (read, var) = sort_requirement_read_node(kb, rid, fd, pass, &handed, anchor);
                out.push((spec, Value::term(stated), var, Some(read)));
            }
        }
    }
    out
}

/// A guard's read (`find_dictionary(WeakOrd[T = ?#1], WeakOrd, ?#1, out: ?#0, carrier_type:
/// true)`) as its spec, the frame slot of its carrier and its instance; `None` for any other
/// read.
pub(super) fn guard_read_parts(kb: &KnowledgeBase, read: &Rc<NodeOccurrence>) -> Option<(Symbol, u32, Value)> {
    let Some(Expr::Apply {
        pos_args,
        named_args,
        ..
    }) = read.as_expr()
    else {
        return None;
    };
    if !named_args
        .iter()
        .any(|(k, _)| kb.local_name_of(*k) == PROVIDER_CARRIER_TYPE_LABEL)
    {
        return None;
    }
    let Some(Expr::Spliced(instance)) = pos_args.first()?.as_expr() else {
        return None;
    };
    let Some(Expr::Var(Var::DeBruijn(carrier))) = pos_args.get(2)?.as_expr() else {
        return None;
    };
    let spec = sort_functor_of_view(kb, instance)?;
    Some((spec, *carrier, instance.clone()))
}

/// Are two guards' instances one requirement up to where each puts its carrier — `a`'s at
/// slot `ca` of its frame, `b`'s at `cb` of its own — and its elements — each `(e, p)` of
/// `elements` an element `a` names at `e` and `b` at `p`? Every other binding is the same
/// type, with no other variable of either frame.
fn same_instance_at_the_goal(
    kb: &KnowledgeBase,
    a: &Value,
    ca: u32,
    b: &Value,
    cb: u32,
    elements: &[(u32, u32)],
) -> bool {
    let carriers = (Var::DeBruijn(ca), Var::DeBruijn(cb));
    let mut renamed = vec![carriers];
    views_alike_up_to_renaming(kb, a, b, &mut renamed)
        && renamed.iter().all(|pair| {
            *pair == carriers
                || elements
                    .iter()
                    .any(|(e, p)| *pair == (Var::DeBruijn(*e), Var::DeBruijn(*p)))
        })
}

/// A sort's bracket on a relation named in `written` — a clause's body, or an equation's —
/// where no routing reads it: anywhere but at one of the clause's goal `sites`
/// (`?r <=> Wrap[T = Int64].el`), or as a goal of a relation with no clause of its own
/// (`SortDomain[T = Colour].fill(?x)`, a spec's rule). Refused: read by no one, the relation
/// would answer at every instance.
fn refuse_unread_brackets(
    kb: &mut KnowledgeBase,
    written: &[Rc<NodeOccurrence>],
    sites: &[Rc<NodeOccurrence>],
    refused: &mut Vec<(TypeError, Option<crate::span::SourceId>)>,
) {
    let mut stack: Vec<Rc<NodeOccurrence>> = written.to_vec();
    let mut unread: Vec<(Rc<NodeOccurrence>, Symbol, bool)> = Vec::new();
    while let Some(node) = stack.pop() {
        let Some(expr) = node.as_expr() else { continue };
        if let Expr::Apply {
            recv_type,
            functor,
            type_args,
            ..
        } = expr
        {
            let relation = kb.cites_a_relation(*functor)
                && !kb.has_kind(*functor, crate::intern::SymbolKind::Operation);
            let goal = relation && sites.iter().any(|s| Rc::ptr_eq(s, &node));
            if relation && recv_type.is_some() && (!goal || !kb.has_clauses_under(*functor)) {
                unread.push((Rc::clone(&node), *functor, goal));
            }
            // The goal's own bracket (060.1 §2) is read where the goal is routed, on a relation
            // that declares type parameters; anywhere else, nothing reads it.
            if relation && !type_args.is_empty() && !(goal && relation_declares_type_params(kb, *functor)) {
                let error = if goal {
                    TypeError::TypeArgsOnNonOperation {
                        span: Some(node.span.span),
                        callee: *functor,
                    }
                } else {
                    let name = kb.qualified_name_of(*functor).to_string();
                    TypeError::Other {
                        site: TypeError::here(),
                        span: Some(node.span.span),
                        context: TypeErrorContext::Rule {
                            name: *functor,
                            field: RuleField::Whole,
                        },
                        expected: format!("the relation written without the bracket, `{name}(…)`"),
                        actual: format!(
                            "a bracket on `{name}` in a rule body is read where the relation is a \
                             goal, and is not here — the binding would be dropped. Write it as a \
                             goal, or cite it from an operation body"
                        ),
                    }
                };
                refused.push((error, Some(node.span.source)));
            }
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    for (node, relation, goal) in unread {
        let name = kb.qualified_name_of(relation).to_string();
        let actual = if goal {
            // A spec's rule: what answers it is a provider's clause, and a goal reaches none.
            let fill = kb.try_resolve_symbol("anthill.reflect.Fillable.fill");
            let domain = if fill.map(|f| kb.canonical_sym(f)) == Some(kb.canonical_sym(relation)) {
                "; a variable typed at the sort is filled by its `SortDomain` — write \
                 `rule colours(?x: Colour) :- true` and the goal `colours(?x)` for \
                 `SortDomain[T = Colour].fill(?x)`"
            } else {
                ""
            };
            format!(
                "a sort's type bracket on `{name}` in a rule body is not read — `{name}` has no \
                 clause of its own, so the goal reaches none the bracket could select{domain}"
            )
        } else {
            format!(
                "a sort's type bracket on `{name}` in a rule body is not read where the relation \
                 is no goal — a value is passed no type argument, so the binding would be \
                 dropped and the relation read at every instance. Write it as a goal, where the \
                 bracket selects the instance, cite it from an operation body, or write it \
                 without the bracket"
            )
        };
        refused.push((
            TypeError::Other {
                site: TypeError::here(),
                span: Some(node.span.span),
                context: TypeErrorContext::Rule {
                    name: relation,
                    field: RuleField::Whole,
                },
                expected: format!("the relation written without the bracket, `{name}(…)`"),
                actual,
            },
            Some(node.span.source),
        ));
    }
}

/// The goals of clause `rid` a marker may stand for: the body's own and every goal in a
/// connective's proved slot beneath them, in the order [`infer_rule_body_requirements`] takes
/// them.
fn goal_sites(kb: &KnowledgeBase, rid: RuleId) -> Vec<Rc<NodeOccurrence>> {
    let body: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
    let mut sites = body.clone();
    for goal in &body {
        nested_goals(kb, goal, &mut sites);
    }
    sites
}

/// The goals of clause `rid` that pass their callee nothing at some position of its layout,
/// each with its callee: a goal in its citation marker with an `__unrouted` slot, and a bare goal
/// of a relation whose clauses read a dictionary, which its marker would have passed nothing
/// at all.
pub(super) fn goals_passing_nothing(kb: &mut KnowledgeBase, rid: RuleId) -> Vec<(Rc<NodeOccurrence>, Symbol)> {
    let unrouted = match crate::kb::resolve::unrouted_read(kb) {
        Value::SymbolRef(s) => s,
        other => unreachable!("the unrouted slot is a symbol, got {other:?}"),
    };
    let mut goals = Vec::new();
    for site in goal_sites(kb, rid) {
        if let Some(marker) = goal_marker(kb, &site) {
            if marker
                .slots
                .iter()
                .any(|slot| matches!(slot.as_expr(), Some(Expr::Ref(s)) if *s == unrouted))
            {
                goals.push((Rc::clone(marker.goal), marker.relation));
            }
        } else if let Some(callee) = relation_goal_callee(kb, &site) {
            if requirement_read_counts(kb, callee).iter().any(|(_, n)| *n > 0) {
                goals.push((site, callee));
            }
        }
    }
    goals
}

/// The relation `site` is a goal of — a name with clauses, and no operation's — or `None`.
fn relation_goal_callee(kb: &KnowledgeBase, site: &NodeOccurrence) -> Option<Symbol> {
    if goal_marker(kb, site).is_some() {
        return None;
    }
    let Some(Expr::Apply { functor, .. }) = site.as_expr() else {
        return None;
    };
    (kb.cites_a_relation(*functor)
        && !kb.has_kind(*functor, crate::intern::SymbolKind::Operation)
        && kb.builtin_of(*functor).is_none())
    .then_some(*functor)
}

/// Does `rid`'s body hold a goal's citation marker?
fn holds_goal_marker(kb: &KnowledgeBase, rid: RuleId) -> bool {
    kb.rule_body_nodes(rid).iter().any(|n| occ_holds_goal_marker(kb, n))
}

/// Does this body goal hold a goal's citation marker — itself, or in a connective's proved
/// slot beneath it?
pub(super) fn occ_holds_goal_marker(kb: &KnowledgeBase, goal: &Rc<NodeOccurrence>) -> bool {
    let mut sites = vec![Rc::clone(goal)];
    nested_goals(kb, goal, &mut sites);
    sites.iter().any(|n| goal_marker(kb, n).is_some())
}

/// Does `goal` hold a value the routing paired with its dictionary ([`pack_call_arguments`])?
/// A body holding one was typed by the load that routed it.
pub(super) fn occ_holds_instance_pair(kb: &KnowledgeBase, goal: &Rc<NodeOccurrence>) -> bool {
    let Some(instance) = kb.try_resolve_symbol("anthill.realization.runtime.Instance") else {
        return false;
    };
    let mut stack = vec![Rc::clone(goal)];
    while let Some(n) = stack.pop() {
        let Some(expr) = n.as_expr() else { continue };
        if matches!(expr, Expr::Apply { functor, .. } if *functor == instance) {
            return true;
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    false
}


/// Does `goal` — a goal of `rid`'s own relation — write each argument at the type the clause
/// gives the head column it binds? Then each of the callee clause's parameters is at the type
/// of the clause's own, and the clause hands on what it took. Every head position must be a
/// variable with a stamped type, and the argument for it must have the same.
fn keeps_its_column_types(kb: &KnowledgeBase, rid: RuleId, goal: &Rc<NodeOccurrence>) -> bool {
    let Some(Expr::Apply {
        pos_args,
        named_args,
        ..
    }) = goal.as_expr()
    else {
        return false;
    };
    let Value::Term { id: head, .. } = kb.rule_head_value(rid) else {
        return false;
    };
    let (head_pos, head_named) = match kb.get_term(*head) {
        Term::Fn {
            pos_args,
            named_args,
            ..
        } => (pos_args.clone(), named_args.clone()),
        _ => (SmallVec::new(), SmallVec::new()),
    };
    if head_pos.len() != pos_args.len() || head_named.len() != named_args.len() {
        return false;
    }
    let stamps = clause_var_stamps(kb, rid);
    let same = |column: TermId, arg: &Rc<NodeOccurrence>| {
        let Term::Var(Var::DeBruijn(d)) = kb.get_term(column) else {
            return false;
        };
        let Some((_, at_head)) = stamps.iter().find(|(seen, _)| seen == d) else {
            return false;
        };
        arg.inferred_type()
            .is_some_and(|at_goal| views_structurally_equal(kb, at_head, &at_goal))
    };
    head_pos.iter().zip(pos_args).all(|(c, a)| same(*c, a))
        && head_named.iter().all(|(k, c)| {
            named_args
                .iter()
                .find(|(n, _)| kb.local_name_of(*n) == kb.local_name_of(*k))
                .is_some_and(|(_, a)| same(*c, a))
        })
}

/// `body` with each goal riding in its citation marker read as the goal it carries — the clause
/// as written, for a reader outside the resolver (`KnowledgeBase::program_clause`), to which the
/// dictionaries a marker passes are no part of the clause's meaning.
pub(crate) fn body_without_goal_markers(
    kb: &KnowledgeBase,
    body: &[Rc<NodeOccurrence>],
) -> Vec<Rc<NodeOccurrence>> {
    body.iter()
        .map(|g| {
            map_proved_goals(kb, g, &|kb, n| {
                let m = goal_marker(kb, n)?;
                Some(match n.as_expr() {
                    Some(Expr::Apply { type_args, .. }) if !type_args.is_empty() => {
                        with_type_args(m.goal, type_args.clone())
                    }
                    _ => Rc::clone(m.goal),
                })
            })
        })
        .collect()
}

/// `goal`, an application, with the bracket `type_args` in place of its own; `goal` itself
/// where the two are both empty.
fn with_type_args(goal: &Rc<NodeOccurrence>, type_args: Vec<(Option<Symbol>, Value)>) -> Rc<NodeOccurrence> {
    match goal.as_expr() {
        Some(Expr::Apply {
            recv_type,
            functor,
            pos_args,
            named_args,
            type_args: own,
        }) if !(own.is_empty() && type_args.is_empty()) => goal.rebuilt_expr(Expr::Apply {
            recv_type: recv_type.clone(),
            functor: *functor,
            pos_args: pos_args.clone(),
            named_args: named_args.clone(),
            type_args,
        }),
        _ => Rc::clone(goal),
    }
}


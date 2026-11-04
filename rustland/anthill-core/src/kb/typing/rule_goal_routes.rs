//! WI-20261102-ATVC1 — RULE → RULE IMPLICIT ARGUMENTS (060-implementation §7.3, S7).
//!
//! A rule-body goal whose callee's clauses take dictionaries — requirement reads, and the
//! callee's own forward slots — carries what it passes them in the citation marker the
//! resolver already reads for a citation's root goal ([`crate::kb::resolve::WITHIN_REQUIREMENTS`]):
//!
//! ```text
//!   rule outer(?a, ?b, ?c) :- cmp(?a, ?b, ?c)
//!     ⇒   __within_requirements(cmp(?a, ?b, ?c), cmp, ?f)
//! ```
//!
//! one slot per position of the callee's layout ([`requirement_read_counts`]). A slot is
//!  * a FORWARD slot ([`FORWARD_SLOT_PASS`]) — `?f`, a variable of the clause and one of its
//!    own implicit parameters ([`clause_implicit_params`]): a citation of the clause routes it
//!    as the callee's position would be routed were the citing operation to cite the callee
//!    itself (`forwarded_routes`), a goal of another clause forwards it in turn, and the
//!    resolver binds it when the clause opens. Unbound, the callee derives its own;
//!  * a parameter the clause already has, for a goal of the clause's own relation at the
//!    clause's own column types: what the clause took, handed on down the recursion;
//!  * a dictionary built at load, where the goal's sort bracket fixes the instance
//!    (`Wrap[T = Int64].el(?x)`);
//!  * `__unrouted`, where nothing is passed and the callee derives its own.
//!
//! REPLACE, NOT INHERIT (op-to-rule-requirement-channel.md §1): what a goal passes is what
//! the typer routes to it here, never what its clause happened to receive.

use super::*;
use std::collections::VecDeque;

/// The pass that wraps a goal in its citation marker.
const RULE_GOAL_ROUTES_PASS: &str = "anthill.kb.passes.rule_goal_routes";

/// What one slot of a goal's marker passes ([`route_goal`]).
enum GoalSlot {
    /// A new implicit parameter of the clause.
    Forward,
    /// A parameter the clause already has: its variable.
    Own(Rc<NodeOccurrence>),
    /// A dictionary built at load.
    Built(TermId),
    Unrouted,
}

/// Which of a clause's goals a pass over its strongly connected component routes: those whose
/// callee lies outside the component, whose layout is final, or those inside it, routed once
/// every clause of the component has its forward slots.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Reach {
    Outside,
    Inside,
}

/// WI-20261102-ATVC1 — give every rule-body goal whose callee takes dictionaries the ones its
/// clause routes to it. AFTER [`infer_rule_body_requirements`], whose reads are what a callee
/// takes, and BEFORE `settle_citation_routes`, which routes the forward slots this mints.
///
/// The clauses are routed callee first, by the strongly connected components of the call graph
/// between relations: a forward slot hands on a position of a callee outside the caller's own
/// recursion, whose layout is final by then. Inside a component a goal of the clause's own
/// relation passes on what the clause took where it calls at the clause's own column types;
/// every other goal inside it passes nothing, and its callee derives its own, as before.
///
/// Idempotent: a clause already routed is left as it is, unless a callee's layout has changed
/// under it since (a later load added clauses), when its goals are routed again.
///
/// Answers the bracketed goals refused, each at its goal ([`bracketed_goal_routes`]).
pub(super) fn route_rule_goal_requirements(
    kb: &mut KnowledgeBase,
) -> Vec<(TypeError, Option<crate::span::SourceId>)> {
    let mut refused = Vec::new();
    let Some(fd) = find_dictionary_symbol(kb) else {
        return refused;
    };
    let Some(within) = kb.try_resolve_symbol(crate::kb::resolve::WITHIN_REQUIREMENTS) else {
        return refused;
    };
    let marker_pass = kb.register_pass(RULE_GOAL_ROUTES_PASS);
    let forward_pass = kb.register_pass(FORWARD_SLOT_PASS);
    let unrouted = match crate::kb::resolve::unrouted_read(kb) {
        Value::SymbolRef(s) => s,
        other => unreachable!("the unrouted slot is a symbol, got {other:?}"),
    };
    let mut routing = Routing {
        syms: RouteSyms {
            fd,
            within,
            marker_pass,
            forward_pass,
            unrouted,
        },
        layouts: HashMap::new(),
        reused: HashMap::new(),
    };
    // The clauses this run routes, by relation, each with its goal sites.
    let mut clauses: Vec<(RuleId, Symbol)> = Vec::new();
    for rid in kb.live_rule_ids() {
        if kb.is_fact(rid) || rule_body_is_typed_once(kb, rid) {
            continue;
        }
        // An equation's guard is run by the rewriter, which passes nothing: a bracket there,
        // or in its right-hand side, is read by no one.
        if kb.has_equational_head(rid) {
            if !kb.is_clause_of_a_refused_load(rid) {
                let mut written: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
                written.extend(kb.rule_equation_rhs_node(rid));
                refuse_unread_brackets(kb, &written, &[], &mut refused);
            }
            continue;
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
            // Routed again, with the forward slots it has, in their order, before any new one.
            let forwards: VecDeque<Rc<NodeOccurrence>> =
                clause_implicit_params(kb, fd, kb.rule_body_nodes(rid))
                    .iter()
                    .filter(|p| matches!(p, ImplicitParam::Forward { .. }))
                    .map(|p| p.var_node(kb, fd))
                    .collect();
            routing.reused.insert(rid, forwards);
            let body = body_without_goal_markers(kb, kb.rule_body_nodes(rid));
            kb.set_rule_body_nodes(rid, body);
            routing.layouts.remove(&relation);
        }
        clauses.push((rid, relation));
    }
    if clauses.is_empty() {
        return refused;
    }
    let relations: Vec<Symbol> = {
        let mut seen = HashSet::new();
        clauses.iter().map(|(_, r)| *r).filter(|r| seen.insert(*r)).collect()
    };
    let index: HashMap<Symbol, usize> = relations.iter().enumerate().map(|(i, r)| (*r, i)).collect();
    let mut edges: Vec<Vec<usize>> = vec![Vec::new(); relations.len()];
    for (rid, relation) in &clauses {
        let from = index[relation];
        let sites = goal_sites(kb, *rid);
        for site in &sites {
            if let Some(callee) = relation_goal_callee(kb, site) {
                if let Some(&to) = index.get(&callee) {
                    edges[from].push(to);
                }
            }
        }
        if !kb.is_clause_of_a_refused_load(*rid) {
            let written: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(*rid).to_vec();
            refuse_unread_brackets(kb, &written, &sites, &mut refused);
        }
    }
    for component in strongly_connected(&edges) {
        let members: HashSet<Symbol> = component.iter().map(|&i| relations[i]).collect();
        let in_component: Vec<(RuleId, Symbol)> = clauses
            .iter()
            .filter(|(_, r)| members.contains(r))
            .copied()
            .collect();
        for reach in [Reach::Outside, Reach::Inside] {
            for &(rid, relation) in &in_component {
                route_clause_goals(kb, &mut routing, rid, relation, &members, reach, &mut refused);
            }
        }
    }
    refused
}

/// What [`route_rule_goal_requirements`] carries from clause to clause.
struct Routing {
    syms: RouteSyms,
    /// Each callee's layout ([`requirement_read_counts`]), read once per pass and forgotten
    /// when a clause of it is stored again.
    layouts: HashMap<Symbol, Rc<[(RuleId, usize)]>>,
    /// The forward slots of a clause routed again, which its new markers take before any
    /// variable is minted: its frame does not grow each time a later load routes it.
    reused: HashMap<RuleId, VecDeque<Rc<NodeOccurrence>>>,
}

impl Routing {
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
    forward_pass: crate::kb::occurrence::PassId,
    unrouted: Symbol,
}

/// Route the goals of `rid` whose callee lies where `reach` says, and store the body.
#[allow(clippy::too_many_arguments)]
fn route_clause_goals(
    kb: &mut KnowledgeBase,
    routing: &mut Routing,
    rid: RuleId,
    relation: Symbol,
    component: &HashSet<Symbol>,
    reach: Reach,
    refused: &mut Vec<(TypeError, Option<crate::span::SourceId>)>,
) {
    let mut wraps: Vec<(Rc<NodeOccurrence>, Rc<NodeOccurrence>)> = Vec::new();
    for site in goal_sites(kb, rid) {
        let Some(callee) = relation_goal_callee(kb, &site) else {
            continue;
        };
        let inside = component.contains(&callee);
        if inside != (reach == Reach::Inside) {
            continue;
        }
        if let Some(marker) = route_goal(kb, routing, rid, relation, &site, callee, inside, refused) {
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
    routing.layouts.remove(&relation);
}

/// The marker `site` — a goal of `callee` in clause `rid` — rides in, or `None` where it passes
/// its callee nothing.
#[allow(clippy::too_many_arguments)]
fn route_goal(
    kb: &mut KnowledgeBase,
    routing: &mut Routing,
    rid: RuleId,
    relation: Symbol,
    site: &Rc<NodeOccurrence>,
    callee: Symbol,
    inside: bool,
    refused: &mut Vec<(TypeError, Option<crate::span::SourceId>)>,
) -> Option<Rc<NodeOccurrence>> {
    let counts = routing.layout(kb, callee);
    let total: usize = counts.iter().map(|(_, n)| n).sum();
    if total == 0 {
        return None;
    }
    // The bracket's instance, built here: nothing a caller passes can change it — a sort's
    // bracket on the relation, or the goal's own on what the relation declares (060.1 §2).
    let built = if call_recv_type_of(site).is_some() || call_type_args_of(site).is_some() {
        let mut misfits = Vec::new();
        let routes = match bracketed_goal_routes(kb, site, callee, &mut misfits) {
            Ok(routes) => routes,
            Err(refusal) => {
                refused.push((refusal, Some(site.span.source)));
                return None;
            }
        };
        for misfit in misfits {
            refused.push(citation_misfit_error(kb, callee, site.span, misfit));
        }
        routes
    } else {
        SmallVec::new()
    };
    // A goal of the clause's own relation at its own column types: the clause's parameters,
    // at its own offset in the layout.
    let own: Option<(usize, Vec<Rc<NodeOccurrence>>)> = (inside && callee == relation)
        .then(|| {
            let at = counts.iter().position(|(r, _)| *r == rid)?;
            if !keeps_its_column_types(kb, rid, site) {
                return None;
            }
            let offset: usize = counts[..at].iter().map(|(_, n)| n).sum();
            let fd = routing.syms.fd;
            let vars = clause_implicit_params(kb, fd, kb.rule_body_nodes(rid))
                .iter()
                .map(|p| p.var_node(kb, fd))
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
    let mut callee_reads: HashMap<RuleId, Vec<ImplicitParam>> = HashMap::new();
    let mut tie: Option<(Symbol, Symbol)> = None;
    let declared: Vec<Option<Rc<NodeOccurrence>>> = positions
        .iter()
        .map(|&(crid, k)| {
            let fd = routing.syms.fd;
            let params = callee_reads
                .entry(crid)
                .or_insert_with(|| clause_implicit_params(kb, fd, kb.rule_body_nodes(crid)));
            match params.get(k) {
                Some(ImplicitParam::Read(read)) => {
                    let read = Rc::clone(read);
                    declared_route(kb, fd, rid, site, crid, &read, &mut tie)
                }
                _ => None,
            }
        })
        .collect();
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
    let slots: Vec<GoalSlot> = (0..total)
        .map(|j| {
            if let Some(Some(t)) = built.get(j) {
                GoalSlot::Built(*t)
            } else if let Some(Some(var)) = declared.get(j) {
                GoalSlot::Own(Rc::clone(var))
            } else if !inside {
                GoalSlot::Forward
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
    if bracket.is_empty() && slots.iter().all(|s| matches!(s, GoalSlot::Unrouted)) {
        return None;
    }
    let (span, owner) = (site.span, site.owner);
    let node = |e: Expr| NodeOccurrence::new_expr(e, span, owner);
    let mut pos_args: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(total + 2);
    pos_args.push(with_type_args(site, Vec::new()));
    pos_args.push(node(Expr::Ref(callee)));
    for slot in slots {
        pos_args.push(match slot {
            GoalSlot::Forward => match routing.reused.get_mut(&rid).and_then(VecDeque::pop_front) {
                Some(reused) => reused,
                None => {
                    let index = kb.rule_globals(rid).len() as u32;
                    let name = kb.intern("forward");
                    let var = kb.fresh_var(name);
                    let bounds = kb.rule_type_bounds(rid).to_vec();
                    kb.extend_rule_frame_with_bounds(rid, &[var], bounds);
                    NodeOccurrence::synthesized_expr(
                        Expr::Var(Var::DeBruijn(index)),
                        Rc::clone(site),
                        routing.syms.forward_pass,
                        owner,
                    )
                }
            },
            GoalSlot::Own(var) => node(var.as_expr().expect("a parameter's variable").clone()),
            GoalSlot::Built(t) => node(Expr::Spliced(Value::term(t))),
            GoalSlot::Unrouted => node(Expr::Ref(routing.syms.unrouted)),
        });
    }
    Some(NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: None,
            functor: routing.syms.within,
            pos_args,
            named_args: Vec::new(),
            type_args: bracket,
        },
        Rc::clone(site),
        routing.syms.marker_pass,
        owner,
    ))
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
/// The instance is read off the goal: the callee column whose bound names the guard's
/// carrier, met with the type the clause's typing stamps on the goal's argument there. `None`
/// where no column says, where the carrier stands at another type than a parameter of the
/// caller (a concrete one, `cmp(1, 2, ?c)`, or a larger one, `List[T = E]`), or where the
/// caller declares no guard of the spec there: the route is then what it was.
fn declared_route(
    kb: &mut KnowledgeBase,
    fd: Symbol,
    rid: RuleId,
    site: &Rc<NodeOccurrence>,
    callee_clause: RuleId,
    read: &Rc<NodeOccurrence>,
    tie: &mut Option<(Symbol, Symbol)>,
) -> Option<Rc<NodeOccurrence>> {
    let (spec, carrier, instance) = guard_read_parts(kb, read)?;
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
    let mut at: Option<Value> = None;
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
        let Some(arg_ty) = arg.and_then(|a| a.inferred_type()) else {
            continue;
        };
        let (opened, _) = crate::kb::node_occurrence::open_value_type(kb, &bound, &fresh);
        let mut pins = Substitution::new();
        if !pin_type_vars(kb, &mut pins, &arg_ty, &opened) {
            continue;
        }
        let x = walk_type_deep_value(kb, &pins, &Value::Var(Var::Global(fresh[carrier as usize])));
        if !matches!(&x, Value::Var(Var::Global(v)) if *v == fresh[carrier as usize]) {
            at = Some(x);
            break;
        }
    }
    // The caller's parameter the carrier stands at, as its frame numbers it.
    let caller_carrier = caller_param_at(kb, rid, &at?)?;
    if !kb.rule_type_params(rid).iter().any(|(_, d)| *d == caller_carrier) {
        return None;
    }
    let body: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
    let held: Vec<(Rc<NodeOccurrence>, Option<Symbol>)> = clause_requirement_reads(kb, fd, &body)
        .into_iter()
        .filter_map(|own| {
            let (own_spec, own_carrier, own_instance) = guard_read_parts(kb, &own)?;
            if own_carrier != caller_carrier
                || !same_sort_canonical(kb, own_spec, spec)
                || !same_instance_but_carrier(kb, &instance, carrier, &own_instance, own_carrier)
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

/// The type parameter of clause `rid` that `at` — a type its typing stamped on a body leaf —
/// is, by its frame slot: each bound of the clause's head columns is met with the stamp on its
/// column's variable, which is how the typing's variable for a parameter is told. `None` for
/// any other type.
/// The type the clause's typing stamped on each of `rid`'s variables, read off its first
/// leaf in the body, by De Bruijn index.
fn clause_var_stamps(kb: &KnowledgeBase, rid: RuleId) -> Vec<(u32, Value)> {
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

pub(super) fn caller_param_at(kb: &mut KnowledgeBase, rid: RuleId, at: &Value) -> Option<u32> {
    let crate::kb::term_view::ViewHead::Var(target) = crate::kb::term_view::TermView::head(at, kb) else {
        return None;
    };
    let params: Vec<u32> = kb.rule_type_params(rid).iter().map(|(_, d)| *d).collect();
    let stamps = clause_var_stamps(kb, rid);
    let name = kb.intern("declared_route");
    let frame_len = (kb.rule_arity(rid) as usize).max(kb.rule_globals(rid).len());
    for (column, bound) in kb.rule_type_bounds(rid).to_vec() {
        let Some((_, stamp)) = stamps.iter().find(|(d, _)| *d == column) else {
            continue;
        };
        let fresh: Vec<VarId> = (0..frame_len).map(|_| kb.fresh_var(name)).collect();
        let (opened, _) = crate::kb::node_occurrence::open_value_type(kb, &bound, &fresh);
        let mut pins = Substitution::new();
        if !pin_type_vars(kb, &mut pins, stamp, &opened) {
            continue;
        }
        for &c in &params {
            let x = walk_type_deep_value(kb, &pins, &Value::Var(Var::Global(fresh[c as usize])));
            if matches!(crate::kb::term_view::TermView::head(&x, kb), crate::kb::term_view::ViewHead::Var(v) if v == target) {
                return Some(c);
            }
        }
    }
    None
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
/// slot `ca` of its frame, `b`'s at `cb` of its own? Every other binding is the same type,
/// with no other variable of either frame.
fn same_instance_but_carrier(kb: &KnowledgeBase, a: &Value, ca: u32, b: &Value, cb: u32) -> bool {
    let carriers = (Var::DeBruijn(ca), Var::DeBruijn(cb));
    let mut renamed = vec![carriers];
    views_alike_up_to_renaming(kb, a, b, &mut renamed) && renamed == [carriers]
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

/// The strongly connected components of `edges` (a graph over `0..edges.len()`), each emitted
/// after every component it reaches — callees first. Tarjan's, iterative.
fn strongly_connected(edges: &[Vec<usize>]) -> Vec<Vec<usize>> {
    let n = edges.len();
    let mut index: Vec<Option<usize>> = vec![None; n];
    let mut low: Vec<usize> = vec![0; n];
    let mut on_stack = vec![false; n];
    let mut stack: Vec<usize> = Vec::new();
    let mut next = 0usize;
    let mut out: Vec<Vec<usize>> = Vec::new();
    for root in 0..n {
        if index[root].is_some() {
            continue;
        }
        // (node, the next edge of it to visit)
        let mut work: Vec<(usize, usize)> = vec![(root, 0)];
        index[root] = Some(next);
        low[root] = next;
        next += 1;
        stack.push(root);
        on_stack[root] = true;
        while let Some(&(v, e)) = work.last() {
            if let Some(&w) = edges[v].get(e) {
                work.last_mut().expect("the node just read").1 += 1;
                match index[w] {
                    None => {
                        index[w] = Some(next);
                        low[w] = next;
                        next += 1;
                        stack.push(w);
                        on_stack[w] = true;
                        work.push((w, 0));
                    }
                    Some(iw) if on_stack[w] => low[v] = low[v].min(iw),
                    Some(_) => {}
                }
                continue;
            }
            work.pop();
            if let Some(&(parent, _)) = work.last() {
                low[parent] = low[parent].min(low[v]);
            }
            if Some(low[v]) == index[v] {
                let mut component = Vec::new();
                loop {
                    let w = stack.pop().expect("the component's root is on the stack");
                    on_stack[w] = false;
                    component.push(w);
                    if w == v {
                        break;
                    }
                }
                out.push(component);
            }
        }
    }
    out
}

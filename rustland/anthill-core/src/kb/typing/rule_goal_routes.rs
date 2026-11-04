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
    // The bracket's instance, built here: nothing a caller passes can change it.
    let built = if call_recv_type_of(site).is_some() {
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
    let slots: Vec<GoalSlot> = (0..total)
        .map(|j| {
            if let Some(Some(t)) = built.get(j) {
                GoalSlot::Built(*t)
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
    if slots.iter().all(|s| matches!(s, GoalSlot::Unrouted)) {
        return None;
    }
    let (span, owner) = (site.span, site.owner);
    let node = |e: Expr| NodeOccurrence::new_expr(e, span, owner);
    let mut pos_args: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(total + 2);
    pos_args.push(Rc::clone(site));
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
            type_args: Vec::new(),
        },
        Rc::clone(site),
        routing.syms.marker_pass,
        owner,
    ))
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
            recv_type: Some(_),
            functor,
            ..
        } = expr
        {
            let relation = kb.cites_a_relation(*functor)
                && !kb.has_kind(*functor, crate::intern::SymbolKind::Operation);
            let goal = sites.iter().any(|s| Rc::ptr_eq(s, &node));
            if relation && (!goal || !kb.has_clauses_under(*functor)) {
                unread.push((Rc::clone(&node), *functor, goal));
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
        .map(|g| map_proved_goals(kb, g, &|kb, n| goal_marker(kb, n).map(|m| Rc::clone(m.goal))))
        .collect()
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

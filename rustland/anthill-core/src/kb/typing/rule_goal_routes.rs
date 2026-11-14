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
//!  * a requirement the clause declares, at the instance the goal is at (060.1 §1), or, for a
//!    goal of the clause's own relation at the clause's own column types, what the clause
//!    took, handed on down the recursion — the variable the clause's read binds;
//!  * a dictionary built at load, where the goal's bracket or its arguments fix the instance
//!    (`Wrap[T = Int64].el(?x)`, `cmp(1, 2, ?c)`);
//!  * `__unrouted`, where nothing is passed: a read that is no guard, or a guard at a spec the
//!    clause's sort supplies. A guard at a type nothing at the goal fixes is refused instead
//!    (proposal 073 §6.2), and a citation that leaves the callee's sort parameter free there
//!    is refused (`refuse_goals_left_free`).
//!
//! REPLACE, NOT INHERIT (op-to-rule-requirement-channel.md §1): what a goal passes is what
//! the typer routes to it here, never what its clause happened to receive.

use super::*;

/// The pass that wraps a goal in its citation marker.
const RULE_GOAL_ROUTES_PASS: &str = "anthill.kb.passes.rule_goal_routes";

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
    // The clauses this run routes, by relation.
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
    stamp_query_variable_types(kb, &sites);
    // A bracket nothing reads — on a goal of a relation that declares nothing for it, or on a
    // relation that is no goal — is refused, as in a rule body (060.1 §2), never dropped.
    let mut refused = Vec::new();
    refuse_unread_brackets(kb, query, &sites, &mut refused);
    let mut wraps: Vec<(Rc<NodeOccurrence>, Rc<NodeOccurrence>)> = Vec::new();
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

/// Each variable of a query's goals `sites` given the type the columns its relation goals put
/// it at agree on, where that is a concrete type — what a clause's typing gives the same
/// variable of the same goals in a rule body. A variable two columns put at different types, or
/// one only an open column reaches, stays untyped.
fn stamp_query_variable_types(kb: &mut KnowledgeBase, sites: &[Rc<NodeOccurrence>]) {
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
            if agreed.as_ref().is_some_and(|seen| !views_structurally_equal(kb, seen, &ty)) {
                *agreed = None;
            }
        }
    }
    for site in sites {
        for_each_var_leaf(site, &mut |var, leaf| {
            if let Var::Global(vid) = var {
                if let Some(Some(ty)) = types.get(&vid) {
                    if leaf.inferred_type().is_none() {
                        leaf.set_inferred_type(ty.clone());
                    }
                }
            }
        });
    }
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

/// Route the goals of `rid`, and store the body.
fn route_clause_goals(
    kb: &mut KnowledgeBase,
    routing: &mut Routing,
    rid: RuleId,
    relation: Symbol,
    refused: &mut Vec<(TypeError, Option<crate::span::SourceId>)>,
) {
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
    let counts = routing.layout(kb, callee);
    let total: usize = counts.iter().map(|(_, n)| n).sum();
    if total == 0 {
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
    // Where the goal cannot be read as a citation of its callee, for the guard it builds.
    let mut unread: Option<TypeError> = None;
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
                return GuardRoute::NoGuard;
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
                _ if writer.clause().is_some_and(|rid| clause_sort_supplies(kb, rid, spec)) => {
                    GuardRoute::NoGuard
                }
                Some(at)
                    if writer
                        .clause()
                        .is_some_and(|rid| type_reaches_the_head(kb, rid, &at)) =>
                {
                    GuardRoute::Undeclared(spec)
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
    if let Some(spec) = declared.iter().find_map(|g| match g {
        GuardRoute::Undeclared(spec) if !refused_load => Some(*spec),
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
                    "a requirement of `{spec_name}` the clause declares, at the type the goal of \
                     `{callee_name}` is at",
                    spec_name = short_name_of(kb.qualified_name_of(spec)),
                    callee_name = kb.qualified_name_of(callee),
                ),
                actual: format!(
                    "the clause declares none, and a rule takes no dictionary it does not \
                     declare: {}",
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
            if let Some(Some(t)) = built.get(j) {
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
    if bracket.is_empty() && slots.iter().all(|s| matches!(s, GoalSlot::Unrouted)) {
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
    pos_args.push(with_type_args(site, Vec::new()));
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
    /// An instance that names a type variable of the caller, which declares nothing there.
    Undeclared(Symbol),
    /// An instance at a type nothing at the goal fixes — a type no head column of the caller
    /// reaches, or a query's variable — which no caller can pass.
    Open(OpenGuard),
    /// A concrete instance nothing provides, or two providers answer: why, as the fetch says.
    Unbuilt(Symbol, String),
    /// No guard, or one the caller's sort supplies: the route is what it was.
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
    let none = Substitution::new();
    let fetched = fetch_dictionary_from_type(kb, &none, &ground, at, DefaultRung::Consult, None);
    match fetched {
        FindDictFetch::Fetched(dict) => Ok(dict),
        FindDictFetch::Guard(FindDictOutcome::DontFire) => Err(GoalDictMiss::Fetch(format!(
            "nothing provides `{}` there",
            type_display_name_value(kb, &ground)
        ))),
        // The fetch's account, said of a read at run time; here it is the goal's, at load.
        FindDictFetch::Undecided { detail } | FindDictFetch::Defect { detail } => {
            Err(GoalDictMiss::Fetch(detail.replace(" at run time:", ":")))
        }
        FindDictFetch::Guard(_) => Err(GoalDictMiss::Fetch(format!(
            "`{}` is not decided by the goal's types",
            type_display_name_value(kb, &ground)
        ))),
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
            return Some(x);
        }
    }
    None
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
    if construction {
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
        Some(
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
        ) if kb.entity_field_types(*functor).is_some() => {
            let pos: Vec<Value> = pos_args.iter().map(|a| goal_arg_type(kb, a)).collect::<Option<_>>()?;
            let named: Vec<(Symbol, Value)> = named_args
                .iter()
                .map(|(k, a)| Some((*k, goal_arg_type(kb, a)?)))
                .collect::<Option<_>>()?;
            if pos.iter().chain(named.iter().map(|(_, t)| t)).any(|t| !instance_is_concrete(kb, t)) {
                return None;
            }
            let ty = constructor_value_type(kb, *functor, &pos, &named);
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
    let crate::kb::term_view::ViewHead::Var(target) = crate::kb::term_view::TermView::head(at, kb) else {
        return None;
    };
    let params: Vec<u32> = kb.rule_type_params(rid).iter().map(|(_, d)| *d).collect();
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


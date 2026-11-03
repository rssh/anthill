//! Proposal 062 — the goals a sort declares over its type parameters (`requires
//! is_entity_of(Trust, TrustLevel)`), and their discharge at an instance of the sort.
//!
//! ONE JUDGE, [`sort_goal_failures`], asked wherever a parameter of such a sort is
//! bound: a written type ([`check_sort_goals_at_written_sites`]), a call that instantiates
//! an operation's type parameters ([`check_call_sort_goals`]), a construction
//! ([`construction_sort_goal_failure`]), and once at the declaration for a goal that names
//! none of the parameters ([`check_sort_goal_declarations`]). The goal is read off its `SortGoalInfo` fact, the
//! parameters it names are substituted with the instance's arguments, and it is resolved.
//!
//! A goal is resolved only once every parameter it names is bound to a CONCRETE type —
//! no variable and no type parameter in it ([`type_is_ground`]). Before that it is not
//! decided at all: resolving `flows_to(Untrusted, ?to)` would answer by binding `?to`, and
//! a skolem stands for every type, so no verdict at one is a verdict about the program.
//! Of a goal that is resolved: a definite solution holds; a complete search with none
//! refutes; a cut search, a fault or a floundered answer decides nothing and is refused
//! as undecided, never read as either.

use super::*;
use crate::kb::resolve::ResolveConfig;

/// A goal of a sort that does not hold at one of its instances, or cannot be decided
/// there.
pub(crate) struct SortGoalFailure {
    /// The goal as the sort declares it.
    pub goal: TermId,
    /// The parameters the goal names, each at its argument.
    pub bindings: Vec<(Symbol, Value)>,
    /// `None` where the search was complete and found nothing; else why it decided
    /// nothing.
    pub undecided: Option<String>,
}

/// Does any loaded sort declare a goal? The common answer is no, and it is the one every
/// reader asks first.
pub(crate) fn sorts_declare_goals(kb: &KnowledgeBase) -> bool {
    kb.sort_goal_info_sym()
        .is_some_and(|info| kb.rules_by_functor_iter(info).next().is_some())
}

/// The goals `sort` declares, from its `SortGoalInfo` facts, in declaration order.
pub(crate) fn sort_goals_of(kb: &KnowledgeBase, sort: Symbol) -> Vec<TermId> {
    let Some(info) = kb.sort_goal_info_sym() else {
        return Vec::new();
    };
    let sort = kb.canonical_sort_sym(sort);
    let mut goals = Vec::new();
    for rid in kb.rules_by_functor_iter(info) {
        if !kb.is_fact(rid) {
            continue;
        }
        let head = kb.rule_head_value(rid);
        let (Some(owner), Some(goal)) = (
            crate::kb::op_info::head_field_term(kb, head, "sort_ref"),
            crate::kb::op_info::head_field_term(kb, head, "goal"),
        ) else {
            continue;
        };
        if crate::kb::load::sort_ref_functor(kb, owner)
            .is_some_and(|owner| kb.canonical_sort_sym(owner) == sort)
        {
            goals.push(goal);
        }
    }
    goals
}

/// The parameters of `sort` that `goal` names, in the sort's declaration order.
pub(crate) fn goal_params(kb: &KnowledgeBase, sort: Symbol, goal: TermId) -> Vec<Symbol> {
    let params = kb.type_param_syms_of(sort);
    params
        .iter()
        .copied()
        .filter(|&p| {
            let p = kb.canonical_sort_sym(p);
            term_any_subterm(kb, goal, &|t, _| {
                view_ref_symbol(kb, &TermIdView(t)).is_some_and(|s| kb.canonical_sort_sym(s) == p)
            })
        })
        .collect()
}

/// The type parameters `goal` names that are not `sort`'s own — an enclosing sort's, which
/// an instance of `sort` binds nothing to.
fn foreign_params(kb: &KnowledgeBase, sort: Symbol, goal: TermId) -> Vec<Symbol> {
    let own: Vec<Symbol> = kb
        .type_param_syms_of(sort)
        .iter()
        .map(|&p| kb.canonical_sort_sym(p))
        .collect();
    let mut out = Vec::new();
    let mut walk = vec![goal];
    while let Some(t) = walk.pop() {
        if let Some(s) = view_ref_symbol(kb, &TermIdView(t)) {
            if is_sort_param_symbol(kb, s)
                && !own.contains(&kb.canonical_sort_sym(s))
                && !out.contains(&s)
            {
                out.push(s);
            }
        }
        if let Term::Fn {
            pos_args,
            named_args,
            ..
        } = kb.get_term(t)
        {
            walk.extend(pos_args.iter().copied());
            walk.extend(named_args.iter().map(|(_, a)| *a));
        }
    }
    out
}

/// The parameter of `sort` a binding of an application of it is keyed by — a written
/// binding is keyed by the parameter's name, looked up among the sort's own parameters.
fn binding_param(kb: &KnowledgeBase, sort: Symbol, key: Symbol) -> Option<Symbol> {
    kb.type_param_sym_of(sort, kb.local_name_of(key))
        .map(|p| kb.canonical_sort_sym(p))
}

/// Every goal of `sort` that does not hold, or cannot be decided, at the instance whose
/// arguments are `bindings` (keyed by parameter name; a parameter left out takes its
/// declared default). A goal naming a parameter the instance leaves open, or binds to a
/// type that is not concrete, is not resolved and yields nothing here.
pub(crate) fn sort_goal_failures(
    kb: &mut KnowledgeBase,
    sort: Symbol,
    bindings: &[(Symbol, Value)],
) -> Vec<SortGoalFailure> {
    let goals = sort_goals_of(kb, sort);
    if goals.is_empty() {
        return Vec::new();
    }
    let mut at_site: Vec<(Symbol, Value)> = bindings
        .iter()
        .filter_map(|(k, v)| binding_param(kb, sort, *k).map(|p| (p, v.clone())))
        .collect();
    for fill in crate::kb::load::parameter_default_fills(kb, sort, bindings) {
        if fill.default_of.is_some() {
            if let Some(p) = binding_param(kb, sort, fill.key) {
                at_site.push((p, fill.value));
            }
        }
    }
    let mut failures = Vec::new();
    'goal: for goal in goals {
        let params = goal_params(kb, sort, goal);
        // A goal over none of the parameters holds of every instance or of none, and is
        // decided where it is declared ([`check_sort_goal_declarations`]).
        if params.is_empty() {
            continue;
        }
        let mut named: Vec<(Symbol, Value)> = Vec::new();
        for p in params {
            let p = kb.canonical_sort_sym(p);
            let Some((_, v)) = at_site.iter().find(|(q, _)| *q == p) else {
                continue 'goal;
            };
            if !type_is_ground(kb, v) {
                continue 'goal;
            }
            named.push((p, v.clone()));
        }
        // Refused at its declaration; deciding it here would report the same mistake once
        // per instance.
        if !goal_names_what_it_writes(kb, sort, goal) {
            continue;
        }
        if let Some(undecided) = decide_sort_goal(kb, goal, &named) {
            failures.push(SortGoalFailure {
                goal,
                bindings: named,
                undecided,
            });
        }
    }
    failures
}

/// `goal` with each of `named`'s parameters replaced by its argument, resolved: `None`
/// where it holds, `Some(None)` where a complete search finds no solution, and
/// `Some(Some(why))` where the search decides nothing.
fn decide_sort_goal(
    kb: &mut KnowledgeBase,
    goal: TermId,
    named: &[(Symbol, Value)],
) -> Option<Option<String>> {
    let leaf = |kb: &mut KnowledgeBase, v: &Value| -> Option<Value> {
        let s = kb.canonical_sort_sym(view_ref_symbol(kb, v)?);
        named
            .iter()
            .find(|(p, _)| *p == s)
            .map(|(_, arg)| arg.clone())
    };
    let substituted = rewrite_type_leaves(kb, &Value::term(goal), &leaf)
        .unwrap_or_else(|| Value::term(goal));
    // The goal's own variables are existential, so one definite answer is the proof.
    let definite = ResolveConfig {
        max_solutions: 1,
        definite_only: true,
        ..ResolveConfig::default()
    };
    let (solutions, stats) = kb.resolve_goals_with_stats(vec![substituted.clone()], &definite);
    if !solutions.is_empty() {
        return None;
    }
    // None: whether it answered under a goal it could not decide is the next question.
    let any = ResolveConfig {
        max_solutions: 1,
        ..ResolveConfig::default()
    };
    let (answered, _) = kb.resolve_goals_with_stats(vec![substituted], &any);
    if let Some(s) = answered.first() {
        let printer = crate::persistence::print::TermPrinter::quoting_source(kb);
        let open: Vec<String> = s
            .residual
            .iter()
            .chain(s.undecided.iter().map(|(g, _)| g))
            .map(|g| printer.print_value(g))
            .collect();
        return Some(Some(format!(
            "its search answered only under goals it could not decide ({})",
            open.join(", ")
        )));
    }
    if !stats.errors.is_empty() {
        let errors: Vec<&str> = stats.errors.iter().map(|e| e.message.as_str()).collect();
        return Some(Some(format!("its search faulted ({})", errors.join("; "))));
    }
    if stats.truncated {
        return Some(Some(format!(
            "its search was cut at depth {}",
            definite.max_depth
        )));
    }
    Some(None)
}

/// The refusal of `failure`, a goal of `sort`, at `span` — the typer's face; the loader's
/// is its [`TypeError::to_load_error`], so the two read alike.
pub(crate) fn sort_goal_unmet_error(
    kb: &KnowledgeBase,
    sort: Symbol,
    failure: &SortGoalFailure,
    span: Option<Span>,
) -> TypeError {
    let printer = crate::persistence::print::TermPrinter::quoting_source(kb);
    let bindings: Vec<String> = failure
        .bindings
        .iter()
        .map(|(p, v)| format!("{} = {}", kb.local_name_of(*p), printer.print_value(v)))
        .collect();
    TypeError::SortGoalUnmet {
        sort: kb.qualified_name_of(sort).to_string(),
        goal: printer.print_term(failure.goal),
        bindings: bindings.join(", "),
        reason: match &failure.undecided {
            Some(why) => format!("cannot be decided: {why}"),
            None => {
                let admissible = admissible_entities(kb, failure);
                format!("does not hold{admissible}")
            }
        },
        span,
    }
}

/// For a goal `is_entity_of(P, E)`, what `P` may be: the entities of the sort `E` is at the
/// instance (a parameter read at its argument), as a clause to append to the refusal. Empty
/// for any other goal.
fn admissible_entities(kb: &KnowledgeBase, failure: &SortGoalFailure) -> String {
    let Some(is_entity_of) = kb.try_resolve_symbol("anthill.reflect.typing.is_entity_of") else {
        return String::new();
    };
    let Term::Fn {
        functor, pos_args, ..
    } = kb.get_term(failure.goal)
    else {
        return String::new();
    };
    if kb.canonical_sort_sym(*functor) != kb.canonical_sort_sym(is_entity_of) || pos_args.len() != 2
    {
        return String::new();
    }
    let Some(written) = view_ref_symbol(kb, &TermIdView(pos_args[1])) else {
        return String::new();
    };
    let at_instance = failure
        .bindings
        .iter()
        .find(|(p, _)| *p == kb.canonical_sort_sym(written))
        .map(|(_, arg)| view_ref_symbol(kb, arg));
    let Some(of) = at_instance.unwrap_or(Some(written)) else {
        return String::new();
    };
    let entities = sort_constructor_syms(kb, of);
    if entities.is_empty() {
        return String::new();
    }
    let names: Vec<String> = entities
        .iter()
        .map(|e| format!("`{}`", kb.local_name_of(*e)))
        .collect();
    format!(
        "; the entities of `{}` are {}",
        kb.local_name_of(of),
        names.join(", ")
    )
}

/// The first goal that fails at an instance of a sort `ty` holds, at any depth
/// (`List[T = Text[Int64]]` holds `Text[Int64]`), with the sort that declares it. `ty` is
/// read as it stands: a caller resolves it through its substitution first.
pub(crate) fn first_sort_goal_failure_in_type(
    kb: &mut KnowledgeBase,
    ty: &Value,
) -> Option<(Symbol, SortGoalFailure)> {
    let ViewHead::Functor {
        functor,
        pos_arity,
        named_arity,
    } = ty.head(kb)
    else {
        return None;
    };
    let named = view_named_children(kb, ty);
    if named_arity > 0 {
        if let Some(sort) = kb.type_arg_owner(functor) {
            if let Some(failure) = sort_goal_failures(kb, sort, &named).into_iter().next() {
                return Some((sort, failure));
            }
        }
    }
    let pos = view_pos_children(kb, ty, pos_arity);
    pos.iter()
        .chain(named.iter().map(|(_, v)| v))
        .find_map(|child| first_sort_goal_failure_in_type(kb, child))
}

/// The construction's half: what a construction makes, read through `subst` — the instance
/// of its sort, `own` (`box(v: 5)` makes `Box[V = Int64]`), and each of its fields' declared
/// types at the parameters the construction binds, `fields` (`wrap(t: …, v: 5)` over `t:
/// Text[V]` makes a `Text[V = Int64]`). Both are written over the variables `subst` binds.
/// Not the types handed to it — an expected type, an argument's — which are judged where
/// they are made, and a field type concrete as declared was judged where it is written.
pub(crate) fn construction_sort_goal_failure(
    kb: &mut KnowledgeBase,
    sort: Symbol,
    own: &Value,
    fields: &[Value],
    subst: &Substitution,
) -> Option<(Symbol, SortGoalFailure)> {
    let instance = resolve_type_deep_value(kb, subst, own);
    let named = view_named_children(kb, &instance);
    if let Some(failure) = sort_goal_failures(kb, sort, &named).into_iter().next() {
        return Some((sort, failure));
    }
    for field in fields {
        if type_is_ground(kb, field) {
            continue;
        }
        let resolved = resolve_type_deep_value(kb, subst, field);
        if let Some(found) = first_sort_goal_failure_in_type(kb, &resolved) {
            return Some(found);
        }
    }
    None
}

/// The call's half: an operation's declared type that is not concrete as written names a
/// type parameter, so the call decides which instance it is — `mk[X](x: X) -> Text[X]`
/// called as `mk(5)` makes a `Text[Int64]`. Each such type of `op` is read at what the
/// call's substitution binds, and the first instance whose goal fails refuses the call at
/// `span`. A type that is concrete as written was judged where it is written.
pub(super) fn check_call_sort_goals(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    op: &OperationInfoFull,
    span: Option<Span>,
) -> Result<(), TypeError> {
    let declared = op
        .params
        .iter()
        .map(|(_, ty)| ty)
        .chain(std::iter::once(&op.return_type));
    for ty in declared {
        if type_is_ground(kb, ty) {
            continue;
        }
        let resolved = resolve_type_deep_value(kb, subst, ty);
        if let Some((sort, failure)) = first_sort_goal_failure_in_type(kb, &resolved) {
            return Err(sort_goal_unmet_error(kb, sort, &failure, span));
        }
    }
    Ok(())
}

/// The written half: every written instance of a sort with a goal (`Text[Int64]` in a
/// signature, a field, an alias, a `const`, an annotation, a `requires` binding), judged
/// at the span of its base name. After the load, so a relation a goal calls that a later
/// file declares is there.
pub(crate) fn check_sort_goals_at_written_sites(
    kb: &mut KnowledgeBase,
    sites: &[crate::kb::ParameterizedSite],
) -> Vec<LoadError> {
    if !sorts_declare_goals(kb) {
        return Vec::new();
    }
    let mut errors = Vec::new();
    for site in sites {
        for failure in sort_goal_failures(kb, site.base, &site.bindings) {
            errors.push(
                sort_goal_unmet_error(kb, site.base, &failure, Some(site.span.span))
                    .to_load_error(kb)
                    .located_in_kb_source(kb, site.span.source),
            );
        }
    }
    errors
}

/// Does `goal`, of `sort`, name only what is declared — no namespace as a goal, no relation
/// and no argument that nothing declares, no type parameter but `sort`'s own? One answer for
/// the declaration's refusal and for every instance, which skips a goal its declaration
/// refuses.
fn goal_names_what_it_writes(kb: &KnowledgeBase, sort: Symbol, goal: TermId) -> bool {
    kb.namespace_goals(&goal).is_empty()
        && kb.undefined_query_goal_functors(&goal).is_empty()
        && undefined_argument_names(kb, goal).is_empty()
        && foreign_params(kb, sort, goal).is_empty()
}

/// The names `goal`'s arguments write, at any depth, that nothing declares
/// ([`KnowledgeBase::symbol_declares_nothing`]): `TrustLevl` in `is_entity_of(Trust,
/// TrustLevl)`. A rule body's argument may hold such a name and only never match; a
/// goal over a sort's parameters that names one would refuse every instance of the sort
/// for a reason no instance could repair, so it is refused where it is written.
fn undefined_argument_names(kb: &KnowledgeBase, goal: TermId) -> Vec<Symbol> {
    fn walk(kb: &KnowledgeBase, t: TermId, out: &mut Vec<Symbol>) {
        let (sym, children): (Option<Symbol>, Vec<TermId>) = match kb.get_term(t) {
            Term::Ident(s) | Term::Ref(s) => (Some(*s), Vec::new()),
            Term::Fn {
                functor,
                pos_args,
                named_args,
            } => (
                Some(*functor),
                pos_args
                    .iter()
                    .copied()
                    .chain(named_args.iter().map(|(_, a)| *a))
                    .collect(),
            ),
            _ => (None, Vec::new()),
        };
        if let Some(s) = sym.filter(|&s| kb.symbol_declares_nothing(s)) {
            if !out.contains(&s) {
                out.push(s);
            }
        }
        for child in children {
            walk(kb, child, out);
        }
    }
    let mut out = Vec::new();
    if let Term::Fn {
        pos_args,
        named_args,
        ..
    } = kb.get_term(goal)
    {
        for arg in pos_args.iter().chain(named_args.iter().map(|(_, a)| a)) {
            walk(kb, *arg, &mut out);
        }
    }
    out
}

/// The declared half: a goal that names a relation nothing declares, a namespace, or a
/// type parameter of another declaration is refused where it is written; and a goal that
/// names none of its sort's parameters holds of every instance or of none, so it is decided
/// once, here.
pub(crate) fn check_sort_goal_declarations(
    kb: &mut KnowledgeBase,
    declarations: Vec<crate::kb::SortGoalDeclaration>,
) -> Vec<LoadError> {
    let mut errors = Vec::new();
    for decl in declarations {
        let at = decl.at;
        let mut named_nothing = false;
        for namespace in kb.namespace_goals(&decl.goal) {
            named_nothing = true;
            errors.push(
                LoadError::NamespaceAsGoal {
                    position: "sort goal",
                    namespace: kb.qualified_name_of(namespace).to_string(),
                    span: at.span,
                }
                .located_in_kb_source(kb, at.source),
            );
        }
        let mut undefined = kb.undefined_query_goal_functors(&decl.goal);
        for name in undefined_argument_names(kb, decl.goal) {
            if !undefined.contains(&name) {
                undefined.push(name);
            }
        }
        for functor in undefined {
            named_nothing = true;
            errors.push(
                LoadError::UndefinedSortGoal {
                    sort: kb.qualified_name_of(decl.sort).to_string(),
                    functor: kb.qualified_name_of(functor).to_string(),
                    span: at.span,
                }
                .located_in_kb_source(kb, at.source),
            );
        }
        for param in foreign_params(kb, decl.sort, decl.goal) {
            named_nothing = true;
            errors.push(
                LoadError::SortGoalNamesAnotherParameter {
                    sort: kb.qualified_name_of(decl.sort).to_string(),
                    param: kb.qualified_name_of(param).to_string(),
                    span: at.span,
                }
                .located_in_kb_source(kb, at.source),
            );
        }
        if named_nothing || !goal_params(kb, decl.sort, decl.goal).is_empty() {
            continue;
        }
        if let Some(undecided) = decide_sort_goal(kb, decl.goal, &[]) {
            let failure = SortGoalFailure {
                goal: decl.goal,
                bindings: Vec::new(),
                undecided,
            };
            errors.push(
                sort_goal_unmet_error(kb, decl.sort, &failure, Some(at.span))
                    .to_load_error(kb)
                    .located_in_kb_source(kb, at.source),
            );
        }
    }
    errors
}

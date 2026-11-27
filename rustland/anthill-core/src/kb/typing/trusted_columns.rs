//! WI-20261124-YFD7F S2 — THE EVIDENCE RULE: which argument of a rule-body goal a typed column
//! of its callee need not check, nor fill, again.
//!
//! A typed column `?x: B` of a relational clause runs two goals at every call
//! ([`install_typed_head_domain_goals`]): the guard in front of the body, and the fill after it,
//! which walks a ground value whole. A recursion on a part of a value its clause has already
//! checked walked that part again at every level — `mem(?x, ?l: List[T = Int64])` on its own
//! tail was quadratic in steps. What a call carries to its callee is the citation marker's
//! slots, one per requirement read of the callee's layout, and every fillable typed column
//! has a read (S1). So the caller says what it knows there: the slot `__trusted(d)`
//! ([`crate::kb::resolve::TRUSTED_READ`]) hands the column's dictionary AND the fact that the
//! argument conforms and that its generation is owned upstream; the callee's guard and fill
//! then run as no goal (S3, the resolver's body open).
//!
//! A call passes `__trusted` only for an argument the caller has ESTABLISHED, at a type that
//! is the callee's bound:
//!  * a typed column of the caller that has a fill — the caller's own check and fill cover
//!    it, or its caller's where it was trusted in turn, down to a clause that was handed a
//!    plain slot or none, whose fill runs: a query's goal, a host's call, a citation;
//!  * a part of an established value destructured by a committed `<=>` on the way to the
//!    goal — a conjunct of the clause, or of the branch of `|` the goal is in, never one
//!    under a negation or a quantifier, nor one of another branch (WI-20261124-C6VN0) — at
//!    the type of its field in the established type ([`field_type_at`]): `?t` of
//!    `?l <=> cons(head: ?, tail: ?t)`, `?l` a `List[T = Int64]`, is a `List[T = Int64]`; the
//!    root's fill fills every hole of it;
//!  * a literal, typed at load.
//!
//! The established type is the one the CHECK established — the caller column's stored bound
//! and the fields of it — never the typer's stamp at the goal, which the goal's own column
//! may have unified into the argument (`?l: List[T = ?e]` passed to a `List[T = Int64]`
//! column reads `?e` as `Int64` there, and the caller's check admits a `List[T = String]`).
//! It matches the callee's bound where that is ground and the established type is ground
//! and compatible with it; where the bound mentions a variable, only in a goal of the
//! clause's own relation that reaches the clause itself, at the bound with the same
//! variables (memU's `List[T = ?e]` on its own tail). Every other argument is passed what it
//! was before: a check.
//!
//! NOT COVERED, each keeping its check: an operation body's citation of a rule (an operation
//! parameter is established too, by the design; not routed here); a construction with a
//! variable in it; a column with no fill (no domain, or a bound that states a requirement),
//! which has no read to route to.

use super::*;

/// What clause `rid` has established of its variables on the way to one of its goals
/// ([`Evidence::at_goal`]): each variable's type, as its check established it, closed in the
/// clause's frame.
pub(super) struct Evidence {
    types: HashMap<u32, Value>,
}

impl Evidence {
    /// What clause `rid` has established on the way to its goal `site`; `None` where `site`
    /// stands under a goal other than a conjunction or a disjunction — a negation, a quantifier
    /// — where nothing the clause established is carried to it, and where `site` is no goal of
    /// the clause's body at all.
    pub(super) fn at_goal(kb: &mut KnowledgeBase, rid: RuleId, site: &Rc<NodeOccurrence>) -> Option<Self> {
        let fd = find_dictionary_symbol(kb)?;
        let unify = kb.try_resolve_symbol("anthill.kernel.unify")?;
        let body: Vec<Rc<NodeOccurrence>> = kb.rule_body_nodes(rid).to_vec();
        // A CUT commits past whatever the clause's goals left open, and trust moves the
        // callee's fill to the clause's own, after the body: `once(len1(?l))` would commit to
        // `len1`'s first proof with the list's cells still open, and the clause's fill then
        // enumerate them all, where the callee's fill had committed to its first. A clause
        // holding a cut — `once`, an `if`, a priority rule expand to one — trusts nothing.
        if holds_a_cut(kb, &body) {
            return None;
        }
        let on_path = unifications_on_path(kb, &body, site, unify)?;
        let bounds: Vec<(u32, Value)> = kb.rule_type_bounds(rid).to_vec();
        let mut types: HashMap<u32, Value> = HashMap::new();
        // The columns with a fill: those the typed-head pass gave a read.
        for goal in &body {
            if !is_typed_head_domain_goal(kb, goal) {
                continue;
            }
            let Some(Expr::Apply { functor, pos_args, .. }) = goal.as_expr() else {
                continue;
            };
            if *functor != fd {
                continue;
            }
            let Some(Expr::Var(Var::DeBruijn(d))) = pos_args.get(2).and_then(|a| a.as_expr()) else {
                unreachable!("a typed column's read is of its column variable");
            };
            let Some((_, bound)) = bounds.iter().find(|(b, _)| b == d) else {
                unreachable!("a typed column's read is of a column with a bound");
            };
            types.insert(*d, dealiased(kb, bound));
        }
        // Through the `<=>` goals on the path, to a fixpoint: each pass that types no new
        // variable ends it.
        loop {
            let known = types.len();
            for goal in &on_path {
                let Some(Expr::Apply { pos_args, .. }) = goal.as_expr() else {
                    continue;
                };
                let [left, right] = pos_args.as_slice() else {
                    continue;
                };
                if let Some(t) = var_type(&types, left) {
                    bind_pattern(kb, &mut types, &t, right);
                }
                if let Some(t) = var_type(&types, right) {
                    bind_pattern(kb, &mut types, &t, left);
                }
            }
            if types.len() == known {
                break;
            }
        }
        Some(Evidence { types })
    }

    /// The type `arg`, an argument of the goal, is established at: a variable the clause
    /// established, or a literal at its sort.
    fn of_arg(&self, kb: &mut KnowledgeBase, arg: &Rc<NodeOccurrence>) -> Option<Value> {
        match arg.as_expr()? {
            Expr::Var(Var::DeBruijn(d)) => self.types.get(d).cloned(),
            Expr::Const(lit) => Some(literal_sort(kb, lit)),
            _ => None,
        }
    }
}

/// Does `body` hold a cut, at any depth?
fn holds_a_cut(kb: &KnowledgeBase, body: &[Rc<NodeOccurrence>]) -> bool {
    let mut stack: Vec<Rc<NodeOccurrence>> = body.to_vec();
    while let Some(node) = stack.pop() {
        if kb.get_builtin_view(&Value::Node(Rc::clone(&node))) == Some(crate::kb::resolve::BuiltinTag::Cut) {
            return true;
        }
        if let Some(expr) = node.as_expr() {
            for_each_child(expr, |c| stack.push(Rc::clone(c)));
        }
    }
    false
}

/// The established type of `side`, where it is a variable of the clause.
fn var_type(types: &HashMap<u32, Value>, side: &Rc<NodeOccurrence>) -> Option<Value> {
    match side.as_expr()? {
        Expr::Var(Var::DeBruijn(d)) => types.get(d).cloned(),
        _ => None,
    }
}

/// `ty` with the alias at its head read as its target, as the typed-head pass reads a bound.
fn dealiased(kb: &mut KnowledgeBase, ty: &Value) -> Value {
    let t = crate::kb::node_occurrence::value_to_term(kb, ty).expect("a bound is a type, which has a term");
    Value::term(dealias_type(kb, t))
}

/// Type the variables of `pattern`, a side of a `<=>` whose other side is established at `ty`:
/// a variable at `ty` itself, the first type it is given; a construction of a constructor of
/// `ty`'s sort, each argument at its field's type in `ty` ([`field_type_at`]), where the field
/// says one. Anything else — an operation's call, a list literal, a constructor of another sort
/// — types nothing.
fn bind_pattern(kb: &mut KnowledgeBase, types: &mut HashMap<u32, Value>, ty: &Value, pattern: &Rc<NodeOccurrence>) {
    let Some(expr) = pattern.as_expr() else { return };
    if let Expr::Var(Var::DeBruijn(d)) = expr {
        types.entry(*d).or_insert_with(|| ty.clone());
        return;
    }
    let Some((ctor, pos_args, named_args)) = expr_call_parts(expr) else {
        return;
    };
    let Some(fields) = kb.entity_field_types(ctor).map(<[_]>::to_vec) else {
        return;
    };
    let Some(sort) = kb.sort_of_constructor(ctor) else {
        return;
    };
    if sort_functor_of_view(kb, ty).map(|s| kb.canonical_sort_sym(s)) != Some(kb.canonical_sort_sym(sort)) {
        return;
    }
    let args: Vec<(Symbol, Value)> = parametric_view_parts(kb, ty)
        .map(|(_, args)| args.into_vec())
        .unwrap_or_default();
    let (pos_args, named_args) = (pos_args.to_vec(), named_args.to_vec());
    // A field written by name is that argument; the positional ones fill the fields no name
    // writes, in declared order.
    let mut positional = pos_args.iter();
    let at_fields: Vec<Option<Rc<NodeOccurrence>>> = fields
        .iter()
        .map(|(name, _)| {
            named_args
                .iter()
                .find(|(k, _)| kb.local_name_of(*k) == kb.local_name_of(*name))
                .map(|(_, a)| Rc::clone(a))
                .or_else(|| positional.next().cloned())
        })
        .collect();
    for ((_, fty), arg) in fields.iter().zip(at_fields) {
        let Some(arg) = arg else { continue };
        if let Some(field_ty) = field_type_at(kb, sort, fty, ty, &args) {
            bind_pattern(kb, types, &field_ty, &arg);
        }
    }
}

/// The `<=>` goals on the path from the top of `goals` (a conjunction) to `site`: the conjuncts
/// of every conjunction it stands in, through the branch of each `|` it is in. `None` where
/// `site` is not reached through conjunctions and disjunctions alone.
fn unifications_on_path(
    kb: &KnowledgeBase,
    goals: &[Rc<NodeOccurrence>],
    site: &Rc<NodeOccurrence>,
    unify: Symbol,
) -> Option<Vec<Rc<NodeOccurrence>>> {
    let mut flat: Vec<Rc<NodeOccurrence>> = Vec::new();
    for goal in goals {
        conjuncts(kb, goal, &mut flat);
    }
    let mut on_path: Vec<Rc<NodeOccurrence>> = flat
        .iter()
        .filter(|g| matches!(g.as_expr(), Some(Expr::Apply { functor, pos_args, .. }) if *functor == unify && pos_args.len() == 2))
        .cloned()
        .collect();
    for goal in &flat {
        if Rc::ptr_eq(goal, site) {
            return Some(on_path);
        }
        let Some((functor, pos_args, _)) = goal.as_expr().and_then(expr_call_parts) else {
            continue;
        };
        // A disjunction (a conjunction was flattened above): the branch `site` is in.
        if kb.is_goal_connective(functor, pos_args.len()) {
            for branch in pos_args {
                if let Some(more) = unifications_on_path(kb, std::slice::from_ref(branch), site, unify) {
                    on_path.extend(more);
                    return Some(on_path);
                }
            }
        }
    }
    None
}

/// The slot a goal of clause `rid` passes the typed column whose `SortDomain` read is `read`, of
/// the callee's clause `callee`, where the evidence rule trusts the argument at it: `__trusted(d)`,
/// `d` the dictionary the goal's bracket built for the column where it built one (`bracket`),
/// else the bound's dictionary built at load where the bound is ground, else the caller's own
/// read of the same column. `None` where it does not, and for a read that is no typed column's.
pub(super) fn trusted_slot(
    kb: &mut KnowledgeBase,
    evidence: &Evidence,
    rid: RuleId,
    site: &Rc<NodeOccurrence>,
    callee: RuleId,
    read: &Rc<NodeOccurrence>,
    bracket: Option<Value>,
) -> Option<Value> {
    if !is_typed_head_domain_goal(kb, read) {
        return None;
    }
    let fd = find_dictionary_symbol(kb)?;
    let Some(Expr::Apply { pos_args, .. }) = read.as_expr() else {
        return None;
    };
    let Some(Expr::Var(Var::DeBruijn(column))) = pos_args.get(2).and_then(|a| a.as_expr()) else {
        return None;
    };
    let column = *column;
    let bound = kb.rule_type_bounds(callee).iter().find(|(d, _)| *d == column)?.1.clone();
    let bound = dealiased(kb, &bound);
    let key = rule_head_var_slots(kb, callee).into_iter().find(|(_, _, d)| *d == column)?.0;
    let arg = goal_arg_at(kb, site, &key)?;
    let established = evidence.of_arg(kb, &arg)?;
    let trusted = crate::kb::resolve::trusted_read_symbol(kb);
    let bound_term = crate::kb::node_occurrence::value_to_term(kb, &bound).expect("a bound has a term");
    let inner = if !term_mentions_var(kb, bound_term) {
        let established_term = crate::kb::node_occurrence::value_to_term(kb, &established).ok()?;
        if term_mentions_var(kb, established_term)
            || !types_compatible(kb, &mut Substitution::new(), &established, &bound)
        {
            return None;
        }
        ground_domain_dictionary(kb, bound_term)?
    } else {
        // At a bound with a variable, the clause's own column at its own variables: the
        // caller's read of it is the callee's, handed on.
        if callee != rid || !crate::kb::term_view::views_structurally_equal(kb, &established, &bound) {
            return None;
        }
        let Some(Expr::Var(Var::DeBruijn(d))) = requirement_read_out(kb, fd, read).and_then(|o| o.as_expr()) else {
            unreachable!("a typed column's read has a variable `out`");
        };
        let d = *d;
        kb.alloc(Term::Var(Var::DeBruijn(d)))
    };
    let inner = match bracket {
        Some(dict) => crate::kb::node_occurrence::value_to_term(kb, &dict).expect("a built dictionary is a term"),
        None => inner,
    };
    Some(Value::term(kb.alloc(Term::Fn {
        functor: trusted,
        pos_args: SmallVec::from_slice(&[inner]),
        named_args: SmallVec::new(),
    })))
}

/// The argument goal `site` writes at its callee's column `key`.
fn goal_arg_at(kb: &KnowledgeBase, site: &Rc<NodeOccurrence>, key: &SlotKey) -> Option<Rc<NodeOccurrence>> {
    let Some(Expr::Apply { pos_args, named_args, .. }) = site.as_expr() else {
        return None;
    };
    match key {
        SlotKey::Pos(i) => pos_args.get(*i).cloned(),
        SlotKey::Named(k) => named_args.iter().find(|(n, _)| same_label(kb, *n, *k)).map(|(_, a)| Rc::clone(a)),
    }
}

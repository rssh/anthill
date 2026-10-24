//! Proposal 069 §1.1 / §3 — an operation's value-parameter defaults at a call: the
//! argument a call leaves out is the parameter's default, spliced into the call and typed
//! where the call is, so every call reaches its callee at full arity.
//!
//! The default is inserted where the call's inference is done (§2, §7 step 4): after the
//! arguments, the bracket, the receiver, the expected result and the type parameters'
//! own defaults, so it is typed at the instance the call has fixed and contributes no
//! evidence of its own. A parameter it names is the argument the call gives that
//! parameter. In an operation body an argument a default names is evaluated once, before
//! the arguments after it: a compound one is bound to a local first
//! ([`bind_arguments_a_default_names`]), and the default then names the local. In a rule
//! body the argument is a term, copied into the default.

use super::*;

/// The defaults a call of an operation takes, by parameter position: the operation's own,
/// or — the operation a provider's member — those of the spec operation it provides,
/// which owns them (§3; user, 2026-10-24: `box(n: 10).scale()` takes `Scaler.scale`'s).
/// `params` are the parameters of the operation that declares them, which a default names.
pub(crate) struct CallDefaults {
    pub(crate) params: Vec<Symbol>,
    pub(crate) by_position: Vec<Option<Rc<NodeOccurrence>>>,
}

impl CallDefaults {
    /// Whether the parameter at `position` declares a default.
    pub(crate) fn has(&self, position: usize) -> bool {
        self.by_position.get(position).is_some_and(Option::is_some)
    }
}

/// [`CallDefaults`] of `op`, or `None` when neither it nor a spec operation its sort
/// provides by its name declares one. A member is paired with the spec operation as the
/// member check pairs it (`check_override_refinement`): the provided spec's operation of the
/// member's name, at the member's arity — a member of another arity is refused there. Read
/// only for a call that leaves a parameter out, so the member's walk is not paid by a call
/// that writes them all.
pub(crate) fn call_defaults(kb: &KnowledgeBase, op: Symbol) -> Option<CallDefaults> {
    let arity = kb.op_record(op)?.signature.as_ref()?.params.len();
    let declared_by = |owner: Symbol| -> Option<CallDefaults> {
        let defaults = kb.op_param_defaults(owner);
        if defaults.is_empty() {
            return None;
        }
        let params: Vec<Symbol> = kb
            .op_record(owner)?
            .signature
            .as_ref()?
            .params
            .iter()
            .map(|(p, _)| *p)
            .collect();
        if params.len() != arity {
            return None;
        }
        let by_position = params
            .iter()
            .map(|p| defaults.iter().find(|(q, _)| q == p).map(|(_, d)| Rc::clone(d)))
            .collect();
        Some(CallDefaults {
            params,
            by_position,
        })
    };
    if let Some(own) = declared_by(op) {
        return Some(own);
    }
    let carrier = impl_parent_sort_of_op(kb, op)?;
    let short = short_name_of(kb.qualified_name_of(op)).to_owned();
    provides_rows_of_provider(kb, carrier).find_map(|row| {
        let spec_op = kb.try_resolve_symbol(&format!(
            "{}.{short}",
            kb.qualified_name_of(row.spec_base)
        ))?;
        (spec_op != op).then(|| declared_by(spec_op)).flatten()
    })
}

thread_local! {
    /// The defaults being typed at a call, innermost last, each by its stored node: a
    /// default that calls its own operation leaving its parameter out — directly, or
    /// through another operation's default — would be taken again while it is typed.
    static TAKING: std::cell::RefCell<Vec<usize>> = const { std::cell::RefCell::new(Vec::new()) };
}

/// The entry [`TAKING`] holds for one default while it is typed, popped when it is done.
struct Taking;

impl Drop for Taking {
    fn drop(&mut self) {
        TAKING.with(|t| {
            t.borrow_mut().pop();
        });
    }
}

/// What [`complete_defaulted_arguments`] makes of a call: the call at full arity, its
/// arguments positional in declaration order (the result column after them, for a goal
/// that names one), and the effects the defaults it took incur.
pub(super) struct CompletedCall {
    pub(super) node: Rc<NodeOccurrence>,
    /// The call's arguments as `node` holds them, and each one's typed result: a written
    /// argument's as the call typed it, a default's as the completion did. What a reader of
    /// the call's arguments past the completion reads (a value precondition's σ, the
    /// carrier a dispatch reads off its receiver), so it reads the call the callee is given.
    pub(super) args: Vec<Rc<NodeOccurrence>>,
    pub(super) results: Vec<Result<TypeResult, TypeError>>,
    pub(super) effects: Vec<Value>,
}

/// A rule-body goal's RESULT COLUMN named `result:` (proposal 069 §1.1), set aside from
/// the call's arguments: the call as written without it, and the column — its typed node
/// and its type. Kernel-language §5.4 reserves the name, so no parameter is called
/// `result` and the label never means one.
pub(super) struct ResultColumn {
    pub(super) occ: Rc<NodeOccurrence>,
    pub(super) named_args: Vec<(Symbol, Rc<NodeOccurrence>)>,
    pub(super) named_results: Vec<Result<TypeResult, TypeError>>,
    pub(super) column: TypeResult,
}

/// Whether a call's label is `result`, the name kernel-language §5.4 reserves for the
/// return value: in a rule-body goal, the result column (proposal 069 §1.1).
pub(crate) fn is_result_label(kb: &KnowledgeBase, label: Symbol) -> bool {
    short_name_of(kb.local_name_of(label)) == "result"
}

/// The `result:` column of the goal `occ`, when it names one. `named_results` are the
/// typed named arguments, every one `Ok` (the caller has refused the call otherwise).
pub(super) fn split_result_column(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    named_results: &[Result<TypeResult, TypeError>],
) -> Option<ResultColumn> {
    let k = named_args.iter().position(|(label, _)| is_result_label(kb, *label))?;
    let Some(Expr::Apply {
        functor,
        pos_args,
        named_args: written,
        type_args,
        recv_type,
    }) = occ.as_expr()
    else {
        return None;
    };
    let mut args = named_args.to_vec();
    args.remove(k);
    let mut results: Vec<Result<TypeResult, TypeError>> =
        named_results.iter().map(clone_arg_result).collect();
    let column = results
        .remove(k)
        .expect("every argument result is `Ok` past `collect_arg_errors`");
    let mut kept = written.clone();
    kept.remove(k);
    let occ = occ.rebuilt_expr(Expr::Apply {
        functor: *functor,
        pos_args: pos_args.clone(),
        named_args: kept,
        type_args: type_args.clone(),
        recv_type: recv_type.clone(),
    });
    Some(ResultColumn {
        occ,
        named_args: args,
        named_results: results,
        column,
    })
}

/// A rule-body goal on an operation that does not return `Bool`, written shorter than its
/// parameter list with no result column: the call is not a goal, and the functional view
/// needs every parameter written (proposal 069 §1.1). Refused, naming `result:` — and
/// naming the parameter its last positional argument fills, which is what that argument
/// reads as. `None` for every other goal.
#[allow(clippy::too_many_arguments)]
pub(super) fn short_goal_without_result(
    kb: &mut KnowledgeBase,
    fn_sym: Symbol,
    params: &[(Symbol, Value)],
    return_type: &Value,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    span: Option<Span>,
) -> Option<TypeError> {
    if pos_args.len() + named_args.len() >= params.len() {
        return None;
    }
    let returns = sort_functor_of_view(kb, return_type)?;
    if kb.sort_sym_is_bool(returns) || kb.rules_by_functor_iter(fn_sym).next().is_some() {
        return None;
    }
    // The last positional argument, as written — a rule's variable has no name left to
    // print, so it is described.
    let last = pos_args.len().checked_sub(1).and_then(|j| {
        let filled = positional_param_indices(kb, params, pos_args.len(), named_args)[j]?;
        let written = match pos_args[j].as_expr() {
            Some(Expr::Var(_)) => None,
            _ => Some(crate::persistence::print::TermPrinter::new(kb).print_occurrence(&pos_args[j])),
        };
        Some((written, short_name_of(kb.local_name_of(params[filled].0)).to_owned()))
    });
    let actual = match last {
        Some((Some(written), param)) => format!(
            "`{written}` fills `{param}`, and the call leaves the parameters after it to their \
             defaults; write `result: {written}` for the call's result"
        ),
        Some((None, param)) => format!(
            "its last positional argument, a variable, fills `{param}`, and the call leaves the \
             parameters after it to their defaults; write it as `result: ?r` for the call's \
             result"
        ),
        None => "a call with no result column; write `result: ?r` for the call's result".into(),
    };
    Some(TypeError::Other {
        site: TypeError::here(),
        span,
        context: TypeErrorContext::OperationArgument {
            op_name: fn_sym,
            param: kb.intern("result"),
        },
        expected: format!(
            "a goal on `{}`, which returns `{}`, to bind its result: every parameter \
             written and one positional column more, or a column named `result:`",
            kb.qualified_name_of(fn_sym),
            kb.qualified_name_of(returns),
        ),
        actual,
    })
}

/// The call `occ` of `fn_sym`, every parameter no argument fills given its default.
///
/// `params` are the callee's parameters as this call reads them, and `subst` the call's
/// substitution once its inference is done: a default is typed against its parameter's
/// type under `subst`, and an operation or enclosing-sort type parameter it writes is the
/// one the call has. `written` is the call as it was typed — its positional results and
/// its labelled arguments with their results — which a written argument's result is read
/// from. `result_column` is the goal's `result:` argument, appended after the parameters
/// (the functional-relation view, kernel-language §5.3).
///
/// `None` when there is nothing to complete: no parameter is left out and no result
/// column was named. A parameter left out with no default is not this function's to
/// report — the arity verdict ([`call_arity_error`]) refused the call before it is
/// reached.
#[allow(clippy::too_many_arguments)]
pub(super) fn complete_defaulted_arguments(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    fn_sym: Symbol,
    params: &[(Symbol, Value)],
    subst: &Substitution,
    written: (
        &[Result<TypeResult, TypeError>],
        &[(Symbol, Rc<NodeOccurrence>)],
        &[Result<TypeResult, TypeError>],
    ),
    result_column: Option<&TypeResult>,
    span: Option<Span>,
) -> Result<Option<CompletedCall>, TypeError> {
    let Some(Expr::Apply {
        functor,
        pos_args,
        named_args,
        type_args,
        recv_type,
    }) = occ.as_expr()
    else {
        return Ok(None);
    };
    // The call every argument of which is written positionally — nearly every call —
    // leaves nothing out.
    if result_column.is_none() && named_args.is_empty() && pos_args.len() >= params.len() {
        return Ok(None);
    }
    let pos_params = positional_param_indices(kb, params, pos_args.len(), named_args);
    let mut args: Vec<Option<Rc<NodeOccurrence>>> = (0..params.len())
        .map(|i| {
            bound_arg(kb, params, &pos_params, i, named_args)
                .map(|b| Rc::clone(b.of(pos_args, named_args)))
        })
        .collect();
    if args.iter().all(Option::is_some) && result_column.is_none() {
        return Ok(None);
    }
    let (written_pos, written_named, written_named_results) = written;
    let written_params = positional_param_indices(kb, params, written_pos.len(), written_named);
    let mut results: Vec<Result<TypeResult, TypeError>> = (0..params.len())
        .map(|i| match bound_arg(kb, params, &written_params, i, written_named) {
            Some(BoundArg::Pos(j)) => clone_arg_result(&written_pos[j]),
            Some(BoundArg::Named(k)) => clone_arg_result(&written_named_results[k]),
            // Left out: its default's, below.
            None => Err(TypeError::Other {
                site: TypeError::here(),
                span,
                context: TypeErrorContext::OperationArgument {
                    op_name: fn_sym,
                    param: params[i].0,
                },
                expected: "a default".into(),
                actual: "none typed yet".into(),
            }),
        })
        .collect();
    let defaults = call_defaults(kb, fn_sym);
    let pass = crate::kb::simp_rewrite::simp_pass(kb);
    let mut effects: Vec<Value> = Vec::new();
    for i in 0..params.len() {
        if args[i].is_some() {
            continue;
        }
        let (param, declared) = &params[i];
        let context = TypeErrorContext::OperationArgument {
            op_name: fn_sym,
            param: *param,
        };
        let Some((names, default)) = defaults
            .as_ref()
            .and_then(|d| d.by_position[i].as_ref().map(|default| (&d.params, default)))
        else {
            return Err(TypeError::Other {
                site: TypeError::here(),
                span,
                context,
                expected: "an argument or a default for every parameter".into(),
                actual: "a parameter the call leaves out and the declaration gives no default, \
                         past the arity verdict — an internal error"
                    .into(),
            });
        };
        // The call's own instance first, then the arguments the default names: the
        // substitution reaches the type positions the default writes, and the arguments
        // are the caller's text, which it must not touch.
        let at_instance = crate::kb::node_occurrence::substitute_occurrence(kb, default, subst);
        let named: HashMap<Symbol, Rc<NodeOccurrence>> = names[..i]
            .iter()
            .zip(&args[..i])
            .filter_map(|(p, a)| a.as_ref().map(|a| (*p, Rc::clone(a))))
            .collect();
        let spliced = splice_default(&at_instance, &named, occ, pass);
        // A rule body has no channel for a call's bracket yet (`CallTypeArgsNotSupportedHere`,
        // the refusal a written one gets there): its requirement weave reads the argument
        // values, not the typer's σ the bracket binds, so a default writing one would have it
        // dropped where the call is. Lifted with the written one's (WI-20261024-TC54R, after
        // WI-20261013-RYDNV).
        if env.in_rule_body() {
            if let Some(callee) = bracketed_call(&spliced) {
                return Err(TypeError::Other {
                    site: TypeError::here(),
                    span,
                    context,
                    expected: "a default a rule body can run: one that writes no call-site \
                               type arguments"
                        .into(),
                    actual: format!(
                        "the default of `{}` writes `{}[…](…)`, and a rule body has no channel \
                         for a call's bracket; write the argument, or make the call in an \
                         operation body",
                        short_name_of(kb.local_name_of(*param)),
                        kb.qualified_name_of(callee),
                    ),
                });
            }
        }
        let expected = walk_type_deep_value(kb, subst, declared);
        let key = Rc::as_ptr(default) as usize;
        if TAKING.with(|t| t.borrow().contains(&key)) {
            let name = short_name_of(kb.local_name_of(*param)).to_owned();
            return Err(TypeError::Other {
                site: TypeError::here(),
                span,
                context,
                expected: format!("a default for `{name}` that a call can be completed with"),
                actual: format!(
                    "the default of `{name}` takes itself: a call it makes leaves `{name}` out \
                     again, so completing the call would never end"
                ),
            });
        }
        TAKING.with(|t| t.borrow_mut().push(key));
        let taking = Taking;
        let typed = type_check_node_at(kb, env, &spliced, Some(expected.clone()), NodePos::Value);
        drop(taking);
        let typed = typed?;
        let mut sigma = Substitution::new();
        let node = match validate_arg_against_param(
            kb,
            &mut sigma,
            &typed.ty,
            &expected,
            span,
            context,
            Some(&typed.node),
        ) {
            ArgValidation::Ok => typed.node,
            ArgValidation::WrapSome { declared } => synthesize_some_wrap(kb, &typed.node, &declared),
            ArgValidation::Fail(err) => return Err(err),
        };
        merge_effects_into(kb, &mut effects, &typed.effects);
        args[i] = Some(Rc::clone(&node));
        results[i] = Ok(TypeResult { node, ..typed });
    }
    let mut full: Vec<Rc<NodeOccurrence>> = args
        .into_iter()
        .map(|a| a.expect("every parameter is filled: by an argument, else by its default"))
        .collect();
    if let Some(column) = result_column {
        full.push(Rc::clone(&column.node));
        results.push(clone_arg_result(&Ok(TypeResult {
            ty: column.ty.clone(),
            env: column.env.clone(),
            effects: column.effects.clone(),
            node: Rc::clone(&column.node),
        })));
    }
    let node = NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: recv_type.clone(),
            functor: *functor,
            pos_args: full.clone(),
            named_args: Vec::new(),
            type_args: type_args.clone(),
        },
        Rc::clone(occ),
        pass,
        occ.owner,
    );
    Ok(Some(CompletedCall {
        node,
        args: full,
        results,
        effects,
    }))
}

/// The callee of the first call or construction in `occ` that writes call-site type
/// arguments or a receiver bracket.
fn bracketed_call(occ: &Rc<NodeOccurrence>) -> Option<Symbol> {
    let mut work: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(occ)];
    while let Some(node) = work.pop() {
        if let Some(expr) = node.as_expr() {
            match expr {
                Expr::Apply {
                    functor,
                    type_args,
                    recv_type,
                    ..
                } if !type_args.is_empty() || recv_type.is_some() => return Some(*functor),
                Expr::ApplyWithin {
                    functor, type_args, ..
                } if !type_args.is_empty() => return Some(*functor),
                Expr::Constructor {
                    name,
                    type_args,
                    recv_type,
                    ..
                } if !type_args.is_empty() || recv_type.is_some() => return Some(*name),
                _ => {}
            }
            crate::kb::node_occurrence::for_each_child(expr, |c| work.push(Rc::clone(c)));
        } else if node.as_pattern().is_some() {
            crate::kb::node_occurrence::for_each_pattern_child(&node, |c| work.push(Rc::clone(c)));
        }
    }
    None
}

/// A copy of the stored default `default` spliced at the call `at`, every reference to a
/// parameter `named` holds replaced by a copy of the argument the call gives it — a call
/// of a function-typed parameter (`y: Int64 = f(10)`) is a call of that argument. Nothing
/// is shared with the stored default or with the call's arguments: the typer stamps what
/// it types, and the default is typed again at every call that takes it.
///
/// An argument is the caller's text, copied as it is and never searched for a parameter:
/// a call the callee makes of itself (`range3(first)` in `range3`'s body) passes one that
/// names the callee's own parameter, which is the caller's there.
///
/// ITERATIVE, for the reason the other splices are: a default is author-written and nests
/// as deeply as the source does.
fn splice_default(
    default: &Rc<NodeOccurrence>,
    named: &HashMap<Symbol, Rc<NodeOccurrence>>,
    at: &Rc<NodeOccurrence>,
    pass: crate::kb::occurrence::PassId,
) -> Rc<NodeOccurrence> {
    enum Op {
        /// A node to copy, and whether it is the default's own text, whose references to
        /// a parameter are replaced.
        Visit(Rc<NodeOccurrence>, bool),
        Build {
            node: Rc<NodeOccurrence>,
            child_count: usize,
        },
    }
    let mut work: Vec<Op> = vec![Op::Visit(Rc::clone(default), true)];
    let mut results: Vec<Rc<NodeOccurrence>> = Vec::new();
    while let Some(op) = work.pop() {
        match op {
            Op::Visit(node, own) => {
                let mut node = node;
                // The children whose copy is the caller's argument, by position.
                let mut caller_children: Vec<usize> = Vec::new();
                if own {
                    match node.as_expr() {
                        Some(Expr::Ref(s) | Expr::Ident(s) | Expr::VarRef { name: s }) => {
                            if let Some(arg) = named.get(s) {
                                work.push(Op::Visit(Rc::clone(arg), false));
                                continue;
                            }
                        }
                        Some(Expr::Apply {
                            functor,
                            pos_args,
                            named_args,
                            ..
                        }) if named.contains_key(functor) && named_args.is_empty() => {
                            let arg = &named[functor];
                            node = match arg.as_expr() {
                                // A local, or a parameter: the call names it.
                                Some(Expr::Ref(s) | Expr::Ident(s) | Expr::VarRef { name: s }) => {
                                    let mut expr = node.as_expr().expect("matched above").clone();
                                    if let Expr::Apply { functor, .. } = &mut expr {
                                        *functor = *s;
                                    }
                                    node.rebuilt_expr(expr)
                                }
                                // Any other argument is the value applied.
                                _ => {
                                    caller_children.push(0);
                                    node.rebuilt_expr(Expr::HoApply {
                                        predicate: Rc::clone(arg),
                                        args: pos_args.clone(),
                                    })
                                }
                            };
                        }
                        _ => {}
                    }
                }
                let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
                if let Some(expr) = node.as_expr() {
                    crate::kb::node_occurrence::for_each_child(expr, |c| children.push(Rc::clone(c)));
                } else if node.as_pattern().is_some() {
                    crate::kb::node_occurrence::for_each_pattern_child(&node, |c| {
                        children.push(Rc::clone(c))
                    });
                }
                work.push(Op::Build {
                    child_count: children.len(),
                    node,
                });
                for (k, c) in children.into_iter().enumerate().rev() {
                    work.push(Op::Visit(c, own && !caller_children.contains(&k)));
                }
            }
            Op::Build { node, child_count } => {
                let start = results.len() - child_count;
                let children: Vec<Rc<NodeOccurrence>> = results.split_off(start);
                let rebuilt = if node.as_expr().is_some() {
                    let reassembled = crate::kb::simp_rewrite::reassemble(&node, &children);
                    let expr = reassembled
                        .as_expr()
                        .expect("an expression node reassembles to one")
                        .clone();
                    node.spliced_at(expr, at, pass)
                } else if node.as_pattern().is_some() {
                    crate::kb::node_occurrence::reassemble_pattern_at(&node, &children, at.owner)
                } else {
                    // A type or effect spine: no stamps to keep apart, and the call's
                    // substitution has already reached inside it.
                    node
                };
                results.push(rebuilt);
            }
        }
    }
    results
        .pop()
        .expect("the splice of a default yields the default's root")
}

/// The parameters each default the call `occ` leaves out names, given by an argument
/// that is not a plain value (a literal, a variable, a local), bound to a local first: in
/// an operation body, `range(next(i))` under `range(first: Int64, last: Int64 = first)`
/// is read as `let first$… = next(i) in range(first$…)`, so the default names the local
/// and the argument is evaluated once. Every compound argument up to the last one so
/// named is bound, in declaration order, so the arguments are evaluated in the order the
/// call evaluates them unbound. `None` when no default the call takes names a compound
/// argument — every call written today.
///
/// A rule body is not given this: its arguments are terms, copied into the default, and
/// a call there performs no effect to evaluate twice.
pub(super) fn bind_arguments_a_default_names(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
) -> Option<Rc<NodeOccurrence>> {
    if env.in_rule_body() {
        return None;
    }
    let Some(Expr::Apply {
        functor,
        pos_args,
        named_args,
        type_args,
        recv_type,
    }) = occ.as_expr()
    else {
        return None;
    };
    if env.lookup_var(*functor).is_some() {
        return None;
    }
    // The call every argument of which is written positionally — nearly every call —
    // leaves nothing out.
    let arity = kb.op_record(*functor)?.signature.as_ref()?.params.len();
    if named_args.is_empty() && pos_args.len() >= arity {
        return None;
    }
    let params: Vec<Symbol> = kb
        .op_record(*functor)?
        .signature
        .as_ref()?
        .params
        .iter()
        .map(|(p, _)| *p)
        .collect();
    let pos_params = positional_param_indices(kb, &params, pos_args.len(), named_args);
    let bound: Vec<Option<BoundArg>> = (0..params.len())
        .map(|i| bound_arg(kb, &params, &pos_params, i, named_args))
        .collect();
    if bound.iter().all(Option::is_some) {
        return None;
    }
    let defaults = call_defaults(kb, *functor)?;
    // The last parameter a default the call takes names.
    let mut last_named: Option<usize> = None;
    for (i, slot) in bound.iter().enumerate() {
        if slot.is_some() {
            continue;
        }
        let Some(default) = &defaults.by_position[i] else {
            continue;
        };
        let mut names: Vec<Symbol> = Vec::new();
        crate::kb::node_occurrence::for_each_named_reference(default, |s| names.push(s));
        if let Some(j) = (0..i).rev().find(|&j| names.contains(&defaults.params[j])) {
            last_named = Some(last_named.map_or(j, |k| k.max(j)));
        }
    }
    let last = last_named?;
    let compound: Vec<(usize, BoundArg)> = bound[..=last]
        .iter()
        .enumerate()
        .filter_map(|(i, b)| match b {
            Some(BoundArg::Pos(j)) if !is_plain_value(env, &pos_args[*j]) => Some((i, BoundArg::Pos(*j))),
            Some(BoundArg::Named(k)) if !is_plain_value(env, &named_args[*k].1) => {
                Some((i, BoundArg::Named(*k)))
            }
            _ => None,
        })
        .collect();
    if compound.is_empty() {
        return None;
    }
    let pass = crate::kb::simp_rewrite::simp_pass(kb);
    let mut pos: Vec<Rc<NodeOccurrence>> = pos_args.clone();
    let mut named: Vec<(Symbol, Rc<NodeOccurrence>)> = named_args.clone();
    let mut lets: Vec<(Symbol, Rc<NodeOccurrence>)> = Vec::new();
    for (i, b) in &compound {
        let arg = Rc::clone(b.of(pos_args, named_args));
        // A name no source can write (`$` is no identifier character) and no other local
        // has: eval reads a local by its name.
        let short = short_name_of(kb.local_name_of(params[*i])).to_owned();
        let local = kb.intern_unique(&format!("{short}${}", kb.symbols.symbol_count()));
        let read = NodeOccurrence::synthesized_expr(Expr::Ref(local), Rc::clone(&arg), pass, arg.owner);
        match b {
            BoundArg::Pos(j) => pos[*j] = read,
            BoundArg::Named(k) => named[*k].1 = read,
        }
        lets.push((local, arg));
    }
    let mut node = NodeOccurrence::synthesized_expr(
        Expr::Apply {
            recv_type: recv_type.clone(),
            functor: *functor,
            pos_args: pos,
            named_args: named,
            type_args: type_args.clone(),
        },
        Rc::clone(occ),
        pass,
        occ.owner,
    );
    for (local, arg) in lets.into_iter().rev() {
        let pattern = NodeOccurrence::new_pattern(Pattern::Var { name: local }, arg.span, arg.owner);
        node = NodeOccurrence::synthesized_expr(
            Expr::Let {
                pattern,
                value: arg,
                body: node,
            },
            Rc::clone(occ),
            pass,
            occ.owner,
        );
    }
    Some(node)
}

/// An argument a default may name by copying it: a literal, a logical variable, or a
/// reference to a local the environment binds. Anything else is evaluated where it is
/// written, and is bound to a local before a default names it.
fn is_plain_value(env: &TypingEnv, arg: &Rc<NodeOccurrence>) -> bool {
    match arg.as_expr() {
        Some(Expr::Const(_) | Expr::Var(_)) => true,
        Some(Expr::Ref(s) | Expr::Ident(s) | Expr::VarRef { name: s }) => env.lookup_var(*s).is_some(),
        _ => false,
    }
}

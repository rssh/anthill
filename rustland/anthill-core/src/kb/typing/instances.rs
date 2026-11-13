//! Proposal 073 §2 — a value of an abstract type is an instance of its sort.
//!
//! A sort that receives on itself is its own carrier (kernel-language §8.1): `List provides
//! Stream`, and a `List` is a `Stream`. A value typed at such a sort, when the sort has no
//! constructors of its own (`Stream`, `FiniteStream`, a user's `Mergeable`), is some
//! provider's value, and it is an instance: the pair of the provider's dictionary, fixed where
//! the provider was known, and the provider's value (`anthill.realization.runtime.Instance`).
//! Nothing at run time reads the value to find the dictionary.
//!
//! The pair is made where a value of a known sort is used at the abstract type — an argument,
//! a result, a field, an element — and taken apart where a call on it enters the member its
//! dictionary names. Which values are pairs is decided by the static type alone: a value typed
//! at the abstract sort is one, a value typed at a provider is not.

use super::*;

/// What a value becomes where it is used (073 §2, §6.4). Stamped by the typer on the node
/// whose value it converts, and on a member reached through a dictionary for the member's
/// result; applied by eval.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum InstanceConversion {
    /// Pair the value with the dictionary `dict` evaluates to where the conversion runs — a
    /// `Dictionary(…)` construction, or a `var_ref` forward of the frame's own slot.
    Pack { dict: TermId },
    /// Pair the value with the dictionary of the instance the call was made on — a member's
    /// result typed `Self` at a call on an instance (`Mergeable.merge(x, y)` answers a
    /// `Mergeable`, `Bag.merge` a `Bag`).
    PackAtReceiver,
    /// An entity of `sort` whose fields typed at a parameter of the sort are converted by
    /// that parameter's conversion (`Option[T = List]` used at `Option[T = Stream]`), at any
    /// depth of the sort's own recursion (`List`'s `tail`): for each constructor, the fields
    /// converted and how. A constructor not listed converts nothing (`none`, `nil`).
    Fields {
        sort: Symbol,
        ctors: Vec<(Symbol, Vec<(Symbol, FieldConversion)>)>,
    },
    /// A tuple whose components are converted, each under its label (`_1`, … for a positional
    /// one): `(a: Box, b: Int64)` used at `(a: Describe, b: Int64)`.
    Tuple {
        components: Vec<(Symbol, InstanceConversion)>,
    },
    /// A function whose result is converted: `Car.mk`'s `(xs: List) -> Carrier` used at the
    /// spec's `(xs: List) -> Base` answers a `Base` instance where it is applied.
    Function { result: Box<InstanceConversion> },
}

/// Is `sort` an abstract sort whose values are instances (073 §2): it receives on itself
/// ([`spec_is_self_representing`]) and has no constructors of its own — `Stream`,
/// `FiniteStream`, a user's `Mergeable`, and a spec whose members are all defaults its
/// carriers may override. A user's
/// own sort is one before any provider of it is in sight: a later load may add one, and a body
/// typed once before it (a sealed load's) must already treat the sort's values as instances. A
/// library sort no one provides is the host's (`Function`, `Set`;
/// [`spec_warrants_abstract_check`]). A sort
/// that receives on a parameter (`Iterable`'s `C`, `Additive`'s `T`) is not one: its providers'
/// values are not its values (kernel-language §8.2). Nor is a sort whose values the host
/// represents ([`host_represents`]: `LogicalStream`, whose values are the host's stream handles,
/// though `Relation` provides it). Memoized on the knowledge base; eval asks it where it pairs a value.
pub fn is_abstract_carrier_sort(kb: &KnowledgeBase, sort: Symbol) -> bool {
    let canon = kb.canonical_sort_sym(sort);
    if let Some(&cached) = kb.abstract_carrier_cache.borrow().get(&canon) {
        return cached;
    }
    let answer = spec_warrants_abstract_check(kb, canon)
        && !kb.sort_has_constructors(canon)
        && receives_on_itself(kb, canon)
        && !host_represents(kb, canon);
    kb.abstract_carrier_cache.borrow_mut().insert(canon, answer);
    answer
}

/// Does `sort` receive on itself — an operation of its own takes one ([`spec_is_self_representing`]),
/// or it provides, for its carriers, a sort that does and has no constructors (`Mid` with no
/// operation of its own, `provides Strm[T = T]`: a `Mid` is a `Strm`)?
fn receives_on_itself(kb: &KnowledgeBase, sort: Symbol) -> bool {
    if spec_is_self_representing(kb, sort) {
        return true;
    }
    provides_rows_of_provider(kb, sort).any(|row| {
        !same_sort_canonical(kb, row.spec_base, sort)
            && spec_is_self_representing(kb, row.spec_base)
            && !kb.sort_has_constructors(row.spec_base)
    })
}

/// Does the host represent the values of `sort`: does it implement an operation receiving one
/// (`LogicalStream.splitFirst`, over the host's stream handles)?
fn host_represents(kb: &KnowledgeBase, sort: Symbol) -> bool {
    crate::kb::op_requirements::operations_of_sort(kb, sort)
        .iter()
        .any(|&op| {
            host_implements(kb, op)
                && lookup_operation_info_full(kb, op)
                    .and_then(|info| self_receiver_param_index(kb, &info.params, sort))
                    .is_some()
        })
}

/// The goal a provision `provider provides spec[C = Self]` answers with at the carrier the goal
/// writes for `spec`'s carrier column, where `provider` is a sort with abstract values
/// ([`is_abstract_carrier_sort`]) and that carrier is a concrete sort providing it (073 §2):
/// `Stream provides Iterable[C = Self]` asked at `Iterable[C = List[T = Int64], …]` is
/// `Stream[T = Int64, E = …]` at `List`. The instance of `spec` there is that carrier's
/// instance of `provider`: `Stream`'s default bodies, reached as `Iterable`'s members, run
/// at it, and the carrier's own member answers where it writes one. `None` for any other
/// candidate, and at a carrier that is itself abstract (`Iterable[C = Stream]`), whose values
/// are instances already.
pub(super) fn carrier_own_instance_goal(
    kb: &mut KnowledgeBase,
    goal: &SortGoal,
    provider: Symbol,
    impl_subst: &[(Symbol, Value)],
) -> Option<SortGoal> {
    if same_sort_canonical(kb, provider, goal.spec_sort) || !is_abstract_carrier_sort(kb, provider)
    {
        return None;
    }
    // The carrier the goal is asked at: a self-receiver spec's own (`Walk` at `Deep`), else the
    // value of the spec's carrier parameter (`Iterable[C = List]`).
    let (head, args) = match &goal.carrier {
        Some(c) => (kb.canonical_sort_sym(c.sort), c.args.clone()),
        None => {
            let column = spec_carrier_param_or_sole(kb, goal.spec_sort)?;
            let carrier_ty = goal_binding_value(kb, goal, column)?.clone();
            let head = sort_functor_of_view(kb, &carrier_ty)?;
            let head = kb.canonical_sort_sym(kb.type_arg_owner(head).unwrap_or(head));
            (head, receiver_type_args(kb, &carrier_ty))
        }
    };
    if same_sort_canonical(kb, head, provider)
        || is_sort_param_symbol(kb, head)
        || !kb.has_kind(head, crate::kb::SymbolKind::Sort)
        || is_abstract_carrier_sort(kb, head)
        || !sort_provides(kb, head, provider)
    {
        return None;
    }
    let provider_qn = kb.qualified_name_of(provider).to_string();
    // The provider's parameters as the carrier's own provision says them at the carrier's
    // type (`List provides Stream[T = T, E = {}]` at `List[T = Int64]`), else as the candidate
    // matched them.
    let mut visited: SmallVec<[Symbol; 4]> = SmallVec::new();
    let through = bindings_through_provisions(kb, head, provider, &args, &mut visited);
    let own: Vec<Symbol> = kb.type_param_syms_of(provider).to_vec();
    let raw: Vec<(Symbol, Value)> = match through {
        Some(bindings) => bindings.into_iter().collect(),
        None => impl_subst
            .iter()
            .filter(|(p, _)| own.contains(p))
            .cloned()
            .collect(),
    };
    let bindings: SmallVec<[(Symbol, Value); 2]> = raw
        .into_iter()
        .map(|(p, v)| {
            let short = kb.local_name_of(p).to_owned();
            (spec_param_key(kb, &provider_qn, &short, p), v)
        })
        .collect();
    Some(SortGoal {
        spec_sort: provider,
        bindings,
        carrier: Some(GoalCarrier { sort: head, args }),
        left_open: SmallVec::new(),
    })
}

/// The sort with abstract values through whose provision for its carriers `provider` reaches
/// `spec` (`Mid` for `Box` at `Top`, over `Box provides Mid` and `Mid provides Top[C = Self]`),
/// where `provider` provides `spec` by no provision of its own. `None` otherwise.
pub(super) fn spec_reached_through_abstract_provision(
    kb: &KnowledgeBase,
    spec: Symbol,
    provider: Symbol,
) -> Option<Symbol> {
    if same_sort_canonical(kb, spec, provider)
        || provides_rows_of_provider(kb, provider).any(|row| {
            same_sort_canonical(kb, row.spec_base, spec)
                && !kb
                    .derived_provision_origin_of(row.rid)
                    .is_some_and(|origin| is_abstract_carrier_sort(kb, origin))
        })
    {
        return None;
    }
    provides_rows_of_provider(kb, provider)
        .map(|row| row.spec_base)
        .find(|&a| {
            !same_sort_canonical(kb, a, spec)
                && is_abstract_carrier_sort(kb, a)
                && sort_provides(kb, a, spec)
        })
}

/// How one field of a constructor is converted inside [`InstanceConversion::Fields`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum FieldConversion {
    /// A field typed at the sort's parameter: that parameter's conversion.
    Param(Box<InstanceConversion>),
    /// A field typed at the sort itself at its own parameters (`List`'s `tail`): the whole
    /// conversion again.
    Recur,
}

/// The conversion of a value of type `actual` used at type `expected` (073 §2): a pair where a
/// value of another sort meets an abstract sort, a constructor's fields where the two types are
/// one sort whose parameters differ that way (`Option[T = Pair[A, B = List]]` at `Option[T =
/// Pair[A, B = Stream]]`), and `None` where the value is used as it is. `receiver` is the sort
/// of the instance a call was made on, whose values typed `Self` are paired with that instance
/// ([`InstanceConversion::PackAtReceiver`]); `None` outside a member's result.
///
/// An `Err` names a type the value cannot be converted at: a field whose type uses a converted
/// parameter other than as itself, or a dictionary no provision answers.
pub(crate) fn conversion_between(
    kb: &mut KnowledgeBase,
    actual: &Value,
    expected: &Value,
    receiver: Option<Symbol>,
    scope: &DictChain,
    rigids: &[(VarId, TermId)],
) -> Result<Option<InstanceConversion>, String> {
    // A function: its result converted where it is applied. A parameter it would have to
    // take converted is refused, not dropped.
    if let (Some((act_param, act_result, _)), Some((exp_param, exp_result, _))) =
        (arrow_parts(kb, actual), arrow_parts(kb, expected))
    {
        if let (Some(a), Some(e)) = (&act_param, &exp_param) {
            if conversion_between(kb, e, a, None, scope, rigids)?.is_some() {
                return Err(format!(
                    "a function taking `{}` used where one taking `{}` is wanted: its argument \
                     would have to be converted where it is applied",
                    type_display_name_value(kb, a),
                    type_display_name_value(kb, e),
                ));
            }
        }
        return Ok(
            conversion_between(kb, &act_result, &exp_result, receiver, scope, rigids)?.map(
                |result| InstanceConversion::Function {
                    result: Box::new(result),
                },
            ),
        );
    }
    let (exp_fields, act_fields) = (
        named_tuple_fields(kb, expected),
        named_tuple_fields(kb, actual),
    );
    if !exp_fields.is_empty() && !act_fields.is_empty() {
        let mut components: Vec<(Symbol, InstanceConversion)> = Vec::new();
        for (i, (label, ety)) in exp_fields.iter().enumerate() {
            let name = kb.local_name_of(*label).to_owned();
            let at = act_fields
                .iter()
                .find(|(l, _)| kb.local_name_of(*l) == name)
                .or_else(|| {
                    crate::intern::positional_label_index(&name).and_then(|_| act_fields.get(i))
                })
                .map(|(l, t)| (*l, t.clone()));
            let Some((act_label, aty)) = at else {
                continue;
            };
            if let Some(c) = conversion_between(kb, &aty, ety, receiver, scope, rigids)? {
                components.push((act_label, c));
            }
        }
        return Ok((!components.is_empty()).then_some(InstanceConversion::Tuple { components }));
    }
    let (Some(exp_head), Some(act_head)) = (
        sort_functor_of_view(kb, expected),
        sort_functor_of_view(kb, actual),
    ) else {
        return Ok(None);
    };
    let exp_head = kb.canonical_sort_sym(kb.type_arg_owner(exp_head).unwrap_or(exp_head));
    let act_head = kb.canonical_sort_sym(kb.type_arg_owner(act_head).unwrap_or(act_head));
    if is_abstract_carrier_sort(kb, exp_head) {
        if exp_head == act_head {
            return Ok(None);
        }
        if receiver.is_some_and(|r| kb.canonical_sort_sym(r) == act_head) {
            return Ok(Some(InstanceConversion::PackAtReceiver));
        }
        // A type parameter, or a type that names no sort, is used as it is.
        if !kb.has_kind(act_head, crate::kb::SymbolKind::Sort) || is_sort_param_symbol(kb, act_head)
        {
            return Ok(None);
        }
        let available: Vec<RequiresEntry> = scope.entries().to_vec();
        let dict = dictionary_at_in_scope(
            kb, exp_head, act_head, actual, expected, &available, scope, rigids,
        )?;
        return Ok(Some(InstanceConversion::Pack { dict }));
    }
    if exp_head != act_head || !kb.sort_has_constructors(exp_head) {
        return Ok(None);
    }
    let (Some((_, act_args)), Some((_, exp_args))) = (
        parametric_view_parts(kb, actual),
        parametric_view_parts(kb, expected),
    ) else {
        return Ok(None);
    };
    let params: Vec<Symbol> = kb.type_param_syms_of(exp_head).to_vec();
    let mut per_param: Vec<(Symbol, InstanceConversion)> = Vec::new();
    for (index, &param) in params.iter().enumerate() {
        let (Some(a), Some(e)) = (
            type_arg_of(kb, &act_args, param, index),
            type_arg_of(kb, &exp_args, param, index),
        ) else {
            continue;
        };
        if let Some(c) = conversion_between(kb, &a, &e, receiver, scope, rigids)? {
            per_param.push((param, c));
        }
    }
    if per_param.is_empty() {
        return Ok(None);
    }
    let param_vars: Vec<(Symbol, VarId)> = sort_type_params_as_pairs(kb, exp_head)
        .iter()
        .filter_map(|(p, t)| Some((*p, declared_type_param_vid(kb, &Value::term(*t))?)))
        .collect();
    let mut ctors: Vec<(Symbol, Vec<(Symbol, FieldConversion)>)> = Vec::new();
    for ctor in kb.constructors_of_sort(exp_head) {
        let Some(fields) = kb.entity_field_types(ctor).map(|f| f.to_vec()) else {
            continue;
        };
        let mut converted: Vec<(Symbol, FieldConversion)> = Vec::new();
        for (field, fty) in fields {
            match field_shape(kb, exp_head, &fty) {
                FieldShape::Param { param, .. } => {
                    if let Some((_, c)) = per_param.iter().find(|(p, _)| *p == param) {
                        converted.push((field, FieldConversion::Param(Box::new(c.clone()))));
                    }
                    continue;
                }
                // The sort at its own parameters (`List`'s `tail`): the whole conversion.
                FieldShape::Own => {
                    converted.push((field, FieldConversion::Recur));
                    continue;
                }
                FieldShape::Other => {}
            }
            let mentions = per_param.iter().any(|(p, _)| {
                type_mentions_var(
                    kb,
                    &fty,
                    param_vars.iter().find(|(q, _)| q == p).map(|(_, v)| *v),
                )
            });
            if mentions {
                return Err(format!(
                    "field `{}` of `{}` holds `{}` other than as itself",
                    kb.local_name_of(field),
                    kb.qualified_name_of(ctor),
                    type_display_name_value(kb, &fty),
                ));
            }
        }
        if !converted.is_empty() {
            ctors.push((ctor, converted));
        }
    }
    Ok(Some(InstanceConversion::Fields {
        sort: exp_head,
        ctors,
    }))
}

/// Does the type `ty` mention the type variable `var` anywhere?
fn type_mentions_var(kb: &KnowledgeBase, ty: &Value, var: Option<VarId>) -> bool {
    let Some(var) = var else {
        return false;
    };
    if declared_type_param_vid(kb, ty) == Some(var) {
        return true;
    }
    parametric_view_parts(kb, ty).is_some_and(|(_, args)| {
        args.iter()
            .any(|(_, v)| type_mentions_var(kb, v, Some(var)))
    })
}

/// The dictionary expression of the abstract sort `abstract_sort` at a value of type `actual`,
/// whose sort is `carrier`: the instance of `carrier`'s provision, built at load, resolved in a
/// scope — `available` is the enclosing chain the resolution may forward from, `chain` its
/// frame names.
pub(crate) fn dictionary_at_in_scope(
    kb: &mut KnowledgeBase,
    abstract_sort: Symbol,
    carrier: Symbol,
    actual: &Value,
    expected: &Value,
    available: &[RequiresEntry],
    chain: &DictChain,
    // The body's type parameters as its rigids: a requirement in scope at one of them covers
    // that parameter only (`Iterable[C = Source]` is no `Iterable[C = Stream]`).
    rigids: &[(VarId, TermId)],
) -> Result<TermId, String> {
    let args = receiver_type_args(kb, actual);
    // The abstract sort's parameters as the carrier's own provision says them at the value's
    // type (`List[T = Int64]`, `List provides Stream[T = T, E = {}]`: `T = Int64, E = {}`);
    // where the carrier provides the sort only through another, as the type the value is used
    // at writes them.
    let spec_qn = kb.qualified_name_of(abstract_sort).to_string();
    let mut visited: SmallVec<[Symbol; 4]> = SmallVec::new();
    let raw: SmallVec<[(Symbol, Value); 2]> =
        match bindings_through_provisions(kb, carrier, abstract_sort, &args, &mut visited) {
            Some(bindings) => bindings,
            None => parametric_view_parts(kb, expected)
                .map(|(_, args)| args)
                .unwrap_or_default(),
        };
    let bindings: SmallVec<[(Symbol, Value); 2]> = raw
        .into_iter()
        .map(|(p, v)| {
            let short = kb.local_name_of(p).to_owned();
            (spec_param_key(kb, &spec_qn, &short, p), v)
        })
        .collect();
    // A parameter neither the provision nor the slot writes — one a chain of provisions says
    // (`Deep` at `Walk` through `Mid`) — is left open: the goal holds a variable there, which
    // the provision answering it binds.
    let mut bindings = bindings;
    open_unwritten_params(kb, abstract_sort, &mut bindings);
    let goal = SortGoal {
        spec_sort: abstract_sort,
        bindings,
        carrier: Some(GoalCarrier {
            sort: carrier,
            args,
        }),
        left_open: SmallVec::new(),
    };
    let subst = Substitution::new();
    let sigma = SigmaCtx {
        subst: &subst,
        param_rigids: rigids,
    };
    let scope = ResolutionScope {
        available_requires: available,
        sigma: Some(&sigma),
        pin: None,
        sub_goal_requires: &[],
    };
    let why = |kb: &KnowledgeBase, what: &str| {
        format!(
            "`{}` used at `{}`: {what}",
            kb.qualified_name_of(carrier),
            kb.qualified_name_of(abstract_sort)
        )
    };
    match resolve(kb, &goal, &scope) {
        ResolutionResult::Resolved(tree) => {
            let syms = ProjectionSyms::resolve(kb)
                .ok_or_else(|| why(kb, "no dictionary can be built in this knowledge base"))?;
            emit_tree_as_projection(kb, chain, &tree, &syms).ok_or_else(|| {
                why(
                    kb,
                    "its instance reads a requirement this scope does not hold",
                )
            })
        }
        // Two instances of the sort answer for the carrier — one provider reaching it through
        // two sorts that provide it (`Carrier provides MidA`, `Carrier provides MidB`, each
        // providing `Spec`): the value has no one instance, and typing it at one of those
        // sorts where it is used says which.
        ResolutionResult::Ambiguous { tie, .. }
            if tie.at_call_goal
                && tie
                    .candidates
                    .iter()
                    .all(|c| is_abstract_carrier_sort(kb, *c)) =>
        {
            let names = tie_candidate_names(kb, &tie);
            let first = tie
                .candidates
                .first()
                .map(|c| kb.local_name_of(*c).to_string())
                .unwrap_or_default();
            Err(why(
                kb,
                &format!(
                    "{} instances of `{}` answer for it ({}), and nothing says which — type \
                     the value at one of them where it is used (`let v: {first}[…] = …`)",
                    names.len(),
                    kb.qualified_name_of(abstract_sort),
                    names.join(", "),
                ),
            ))
        }
        other => Err(why(kb, &describe_resolution_failure(kb, &other))),
    }
}

/// How the type `fty` of a field of a constructor of `sort` reads the sort's parameters.
enum FieldShape {
    /// A parameter of the sort, written as the parameter's own variable (`cons`'s `head`).
    Param { index: usize, param: Symbol },
    /// The sort at its own parameters, each at its own name or position (`cons`'s `tail`).
    Own,
    /// Anything else: a ground type, or the sort at other arguments.
    Other,
}

fn field_shape(kb: &KnowledgeBase, sort: Symbol, fty: &Value) -> FieldShape {
    let param_at = |ty: &Value| -> Option<(usize, Symbol)> {
        let vid = declared_type_param_vid(kb, ty)?;
        sort_type_params_as_pairs(kb, sort)
            .iter()
            .enumerate()
            .find(|(_, (_, t))| declared_type_param_vid(kb, &Value::term(*t)) == Some(vid))
            .map(|(i, (p, _))| (i, *p))
    };
    if let Some((index, param)) = param_at(fty) {
        return FieldShape::Param { index, param };
    }
    let head = sort_functor_of_view(kb, fty)
        .map(|h| kb.canonical_sort_sym(kb.type_arg_owner(h).unwrap_or(h)));
    if head != Some(kb.canonical_sort_sym(sort)) {
        return FieldShape::Other;
    }
    let own = parametric_view_parts(kb, fty)
        .map(|(_, args)| args)
        .unwrap_or_default();
    // Every parameter written, each at the parameter's own name or its own position.
    let at_own = own.len() == sort_type_params_as_pairs(kb, sort).len()
        && own.iter().all(|(label, v)| {
            param_at(v).is_some_and(|(index, param)| {
                let label = kb.local_name_of(*label);
                label == kb.local_name_of(param)
                    || crate::intern::positional_label_index(label) == Some(index)
            })
        });
    if at_own {
        FieldShape::Own
    } else {
        FieldShape::Other
    }
}

/// The argument `args` give the sort's parameter `param`, declared `index`-th: by name, or by
/// position where the type writes its arguments positionally (`Option[Pair[…]]`).
fn type_arg_of(
    kb: &KnowledgeBase,
    args: &[(Symbol, Value)],
    param: Symbol,
    index: usize,
) -> Option<Value> {
    let name = kb.local_name_of(param);
    args.iter()
        .find(|(p, _)| {
            let label = kb.local_name_of(*p);
            label == name || crate::intern::positional_label_index(label) == Some(index)
        })
        .map(|(_, v)| v.clone())
}

/// The type of a field typed `fty` of a constructor of `sort`, in a value of type `ty`
/// (`sort` applied to `args`): a parameter of the sort is its argument there (`cons`'s `head`
/// at `List[T = Sp]` is `Sp`), the sort at its own parameters is `ty` (`tail`); `None` for a
/// field whose type is neither.
pub(crate) fn field_type_at(
    kb: &KnowledgeBase,
    sort: Symbol,
    fty: &Value,
    ty: &Value,
    args: &[(Symbol, Value)],
) -> Option<Value> {
    match field_shape(kb, sort, fty) {
        FieldShape::Param { index, param } => type_arg_of(kb, args, param, index),
        FieldShape::Own => Some(ty.clone()),
        FieldShape::Other => None,
    }
}

/// The dictionary a value that is an instance (`Instance(dict, value)`, 073 §2) carries, read
/// through the view on any carrier; `None` for any other value.
pub(crate) fn instance_dictionary_of<V: TermView>(kb: &KnowledgeBase, v: &V) -> Option<Value> {
    let instance = kb.try_resolve_symbol("anthill.realization.runtime.Instance")?;
    match v.head(kb) {
        ViewHead::Functor {
            functor,
            pos_arity: 2,
            named_arity: 0,
        } if functor == instance => v.pos_arg(kb, 0).map(|d| d.to_value()),
        _ => None,
    }
}

/// Does the type `ty` name a sort with abstract values, at its head or in an argument
/// (`Stream[…]`, `List[T = Sp]`)? What decides that a value at `ty` holds instances.
pub(crate) fn type_names_abstract_carrier(kb: &KnowledgeBase, ty: &Value) -> bool {
    if let Some(head) = sort_functor_of_view(kb, ty) {
        let head = kb.canonical_sort_sym(kb.type_arg_owner(head).unwrap_or(head));
        if is_abstract_carrier_sort(kb, head) {
            return true;
        }
    }
    parametric_view_parts(kb, ty)
        .is_some_and(|(_, args)| args.iter().any(|(_, a)| type_names_abstract_carrier(kb, a)))
}

/// A goal's bindings of `spec` with each parameter they leave unwritten (an effect row
/// apart) bound to a fresh variable: the goal leaves it open, and the provision answering it
/// binds it. A goal missing a binding matches no provision at all.
pub(super) fn open_unwritten_params(
    kb: &mut KnowledgeBase,
    spec: Symbol,
    bindings: &mut SmallVec<[(Symbol, Value); 2]>,
) {
    let spec_qn = kb.qualified_name_of(spec).to_string();
    for param in kb.type_param_syms_of(spec).to_vec() {
        let short = kb.local_name_of(param).to_owned();
        if bindings.iter().any(|(k, _)| kb.local_name_of(*k) == short)
            || sort_param_is_effect_row(kb, spec, &short)
        {
            continue;
        }
        let name = kb.intern(&short);
        let var = kb.fresh_var(name);
        let open = Value::term(kb.alloc(Term::Var(Var::Global(var))));
        bindings.push((spec_param_key(kb, &spec_qn, &short, param), open));
    }
}

/// The parameters of `spec` as the provisions from `carrier` to it say them at a value of
/// `carrier` whose type writes `args` (keyed by the parameter the type wrote, or positionally):
/// the carrier's own provision (`List provides Stream[T = T, E = {}]` at `List[T = Int64]`), or
/// one composed along a chain of them (`Carrier provides Mid[A = T]`, `Mid provides Spec[P = A,
/// Q = Int64]` at `Carrier[T = Int64]`: `P = Int64, Q = Int64`). `None` where no provision
/// leads from the carrier to the spec.
fn bindings_through_provisions(
    kb: &mut KnowledgeBase,
    carrier: Symbol,
    spec: Symbol,
    args: &[(Symbol, Value)],
    visited: &mut SmallVec<[Symbol; 4]>,
) -> Option<SmallVec<[(Symbol, Value); 2]>> {
    let carrier = kb.canonical_sort_sym(carrier);
    if visited.contains(&carrier) {
        return None;
    }
    visited.push(carrier);
    // The carrier's own parameters at the value: what its provisions' views are written in.
    let own: Vec<Symbol> = kb.type_param_syms_of(carrier).to_vec();
    let at_value: Vec<(Symbol, Value)> = own
        .iter()
        .enumerate()
        .filter_map(|(i, p)| {
            let name = kb.local_name_of(*p);
            args.iter()
                .find(|(k, _)| {
                    let label = kb.local_name_of(*k);
                    label == name || crate::intern::positional_label_index(label) == Some(i)
                })
                .map(|(_, v)| (*p, v.clone()))
        })
        .collect();
    if let Some(view) = provider_spec_view_bindings(kb, carrier, spec) {
        return Some(
            view.into_iter()
                .map(|(k, v)| {
                    let v = sigma_subst_type(kb, &v, &at_value);
                    (k, v)
                })
                .collect(),
        );
    }
    let rows: Vec<(Symbol, SmallVec<[(Symbol, Value); 2]>)> =
        provides_rows_of_provider(kb, carrier)
            .map(|row| (row.spec_base, row.bindings(kb)))
            .collect();
    for (middle, view) in rows {
        if same_sort_canonical(kb, middle, spec) || !sort_provides(kb, middle, spec) {
            continue;
        }
        // The middle sort's parameters at this value, keyed by its own parameters.
        let middle_args: Vec<(Symbol, Value)> = view
            .into_iter()
            .map(|(k, v)| {
                let v = sigma_subst_type(kb, &v, &at_value);
                (k, v)
            })
            .collect();
        if let Some(found) = bindings_through_provisions(kb, middle, spec, &middle_args, visited) {
            return Some(found);
        }
    }
    None
}

/// The conversion of the result of `member`, reached by a call of `spec_op` made on an
/// instance (073 §2), to the result type the call was typed at: `spec_op`'s own, at the
/// abstract sort. `Relation.splitFirst` answers `B = LogicalStream[…]` where `Stream.splitFirst`
/// says `B = Stream[…]`; `Bag.merge` answers a `Bag` where `Mergeable.merge` says `Self`.
pub(crate) fn member_result_conversion(
    kb: &mut KnowledgeBase,
    spec_op: Symbol,
    member: Symbol,
) -> Result<Option<InstanceConversion>, String> {
    let (Some(spec_info), Some(member_info)) = (
        crate::kb::op_info::lookup_operation_info(kb, spec_op),
        crate::kb::op_info::lookup_operation_info(kb, member),
    ) else {
        return Ok(None);
    };
    let receiver = impl_parent_sort_of_op(kb, member);
    conversion_between(
        kb,
        &member_info.return_type,
        &spec_info.return_type,
        receiver,
        &DictChain::empty(),
        &[],
    )
}

/// The parameter of `params`, an operation of `spec_sort`, a call is made on: the one declared
/// at the sort itself (`splitFirst(s: Self)`), or else the one declared at the sort's carrier
/// parameter (`FiniteCollection.collect(c: C)`).
pub fn receiver_param_index(
    kb: &KnowledgeBase,
    params: &[(Symbol, Value)],
    spec_sort: Symbol,
) -> Option<usize> {
    if let Some(i) = self_receiver_param_index(kb, params, spec_sort) {
        return Some(i);
    }
    let carrier = spec_carrier_param(kb, spec_sort)?;
    let carrier_var = sort_type_params_as_pairs(kb, spec_sort)
        .iter()
        .find(|(p, _)| *p == carrier)
        .and_then(|(_, t)| declared_type_param_vid(kb, &Value::term(*t)))?;
    params
        .iter()
        .position(|(_, ty)| declared_type_param_vid(kb, ty) == Some(carrier_var))
}

/// The abstract sort a call of `op`, an operation of `spec_sort`, is made on (073 §2): the
/// static sort of the argument at the operation's receiver ([`receiver_param_index`]), where
/// that is an abstract carrier sort ([`is_abstract_carrier_sort`]) providing `spec_sort` or
/// being it. `None` for a receiver of a known sort, a type parameter's value, or an operation
/// with no receiver.
#[allow(clippy::too_many_arguments)]
pub(super) fn instance_receiver_sort(
    kb: &KnowledgeBase,
    op: &OperationInfoFull,
    spec_sort: Symbol,
    pos_params: &[Option<usize>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> Option<Symbol> {
    let idx = receiver_param_index(kb, &op.params, spec_sort)?;
    let ty = supplied_arg_type(
        kb,
        &op.params,
        pos_params,
        idx,
        pos_results,
        named_args,
        named_results,
    )?;
    let head = carrier_sort_of_value(kb, &ty)?;
    let head = kb.canonical_sort_sym(kb.type_arg_owner(head).unwrap_or(head));
    (is_abstract_carrier_sort(kb, head)
        && (same_sort_canonical(kb, head, spec_sort) || sort_provides(kb, head, spec_sort)))
    .then_some(head)
}

/// Stamp, on every node of the typed body `body` whose value is used at an abstract type, the
/// conversion that makes it the instance it is there (073 §2, §6.4): the body's value against
/// the declared result, an argument against the parameter of the operation the call goes to, a
/// field or a list element against its slot at the constructed type, a branch against the type
/// of the expression it is a branch of. And on a call the typer sent to a member of another
/// sort than the operation it names, the conversion of the member's result to the type the
/// call was typed at. The dictionaries are built here, in the body's scope (`env`).
pub(super) fn stamp_instance_conversions(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    // Where the body's value is used: an operation's result, a const's value.
    at: TypeErrorContext,
    body: &Rc<NodeOccurrence>,
    declared: &Value,
) -> Vec<TypeError> {
    let mut errors = Vec::new();
    let chain = env.enclosing_frame_chain().clone();
    let rigids: Vec<(VarId, TermId)> = env.param_rigids().to_vec();
    let mut walk = InstanceWalk {
        chain: &chain,
        rigids: &rigids,
        env,
        locals: Vec::new(),
        param_conversions: Vec::new(),
        errors: &mut errors,
    };
    walk.node(kb, body, Some(declared.clone()), &at);
    errors
}

struct InstanceWalk<'a> {
    chain: &'a DictChain,
    rigids: &'a [(VarId, TermId)],
    /// The body's environment: the types of its parameters.
    env: &'a TypingEnv,
    /// The types of the binders the walk is under, innermost last: a lambda's parameter, a
    /// `let`'s variable — what a call of a function value reads its parameter types from.
    locals: Vec<(Symbol, Value)>,
    /// The lambda parameters handed a provider's value where the lambda reads an instance:
    /// each read of one converts it.
    param_conversions: Vec<(Symbol, InstanceConversion)>,
    errors: &'a mut Vec<TypeError>,
}

impl InstanceWalk<'_> {
    /// `slot` is the type the value of `occ` is used at, and `site` where: what a refusal of
    /// the value there is located by.
    fn node(
        &mut self,
        kb: &mut KnowledgeBase,
        occ: &Rc<NodeOccurrence>,
        slot: Option<Value>,
        site: &TypeErrorContext,
    ) {
        let NodeKind::Expr { expr, .. } = &occ.kind else {
            return;
        };
        let own = occ.inferred_type();
        let mut edge: Option<InstanceConversion> = None;
        // A lambda met at an arrow slot converts its own body at the slot's result and its
        // parameter where it is read (the `Lambda` arm below): it takes no conversion whole.
        let converts_itself = matches!(expr, Expr::Lambda { .. });
        if let (Some(slot), Some(actual), false) = (slot.as_ref(), own.as_ref(), converts_itself) {
            match conversion_between(kb, actual, slot, None, self.chain, self.rigids) {
                Ok(c) => edge = c,
                Err(why) => self.refuse(occ, site, why),
            }
        }
        let member = self.member_result(kb, occ, site);
        match (member, edge) {
            (Some(m), None) => occ.set_instance_conversion(m),
            (None, Some(e)) => occ.set_instance_conversion(e),
            (Some(_), Some(_)) => self.refuse(
                occ,
                site,
                "a member's result converted to the call's type and again where it is used".into(),
            ),
            (None, None) => {}
        }
        match expr {
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => {
                self.node(kb, condition, None, site);
                self.node(kb, then_branch, own.clone(), site);
                self.node(kb, else_branch, own, site);
            }
            Expr::Match {
                scrutinee,
                branches,
            } => {
                self.node(kb, scrutinee, None, site);
                for b in branches {
                    if let Some(g) = &b.guard {
                        self.node(kb, g, None, site);
                    }
                    self.node(kb, &b.body, own.clone(), site);
                }
            }
            Expr::Let {
                pattern,
                value,
                body,
            } => {
                // A `let` that writes the type of its variable is where its value meets that
                // type (`let p: Peek[…] = h`).
                let written = pattern
                    .pattern_type_ann()
                    .map(|ann| Value::Node(Rc::clone(ann)));
                let at_let = match pattern_var(pattern) {
                    Some(var) => TypeErrorContext::LetBinding { var },
                    None => site.clone(),
                };
                self.node(kb, value, written.clone(), &at_let);
                let bound = pattern_var(pattern).zip(written.or_else(|| value.inferred_type()));
                let pushed = bound.is_some();
                if let Some(b) = bound {
                    self.locals.push(b);
                }
                self.node(kb, body, own, site);
                if pushed {
                    self.locals.pop();
                }
            }
            Expr::Lambda { param, body } => {
                let parts = own.as_ref().and_then(|t| arrow_parts(kb, t));
                // Met at an arrow slot (an argument the callee types as a function), the
                // lambda answers the slot's result, and is handed the slot's parameter: where
                // that is a provider's value its own type reads as an instance, each use of the
                // parameter converts it.
                let at_slot = slot.as_ref().and_then(|t| arrow_parts(kb, t));
                let own_param = parts.as_ref().and_then(|(p, _, _)| p.clone());
                let handed = at_slot.as_ref().and_then(|(p, _, _)| p.clone());
                let param_conversion = match (pattern_var(param), &own_param, &handed) {
                    (Some(name), Some(own_ty), Some(handed_ty)) => {
                        match conversion_between(
                            kb,
                            handed_ty,
                            own_ty,
                            None,
                            self.chain,
                            self.rigids,
                        ) {
                            Ok(Some(c)) => Some((name, c)),
                            Ok(None) => None,
                            Err(why) => {
                                self.refuse(occ, site, why);
                                None
                            }
                        }
                    }
                    _ => None,
                };
                let bound = pattern_var(param).zip(own_param);
                let pushed = bound.is_some();
                if let Some(b) = bound {
                    self.locals.push(b);
                }
                let converted_param = param_conversion.is_some();
                if let Some(pc) = param_conversion {
                    self.param_conversions.push(pc);
                }
                let result_slot = at_slot.map(|(_, r, _)| r).or(parts.map(|(_, r, _)| r));
                self.node(kb, body, result_slot, site);
                if converted_param {
                    self.param_conversions.pop();
                }
                if pushed {
                    self.locals.pop();
                }
            }
            Expr::VarRef { name } | Expr::Ref(name) | Expr::Ident(name)
                if self.param_conversions.iter().any(|(n, _)| n == name) =>
            {
                let conv = self
                    .param_conversions
                    .iter()
                    .rev()
                    .find(|(n, _)| n == name)
                    .map(|(_, c)| c.clone())
                    .expect("found above");
                if occ.has_instance_conversion() {
                    self.refuse(
                        occ,
                        site,
                        "a lambda's parameter converted where it is read and again where it is used"
                            .into(),
                    );
                } else {
                    occ.set_instance_conversion(conv);
                }
            }
            Expr::Apply {
                functor,
                pos_args,
                named_args,
                ..
            } => {
                let target = occ.classified_target().unwrap_or(*functor);
                // A call through a dictionary (a requirement, a lambda's) enters the member the
                // dictionary names where it runs, which takes its arguments as the call has them;
                // a default body it lands on pairs its receiver there (`positions_to_pair`).
                let through_dictionary = matches!(
                    occ.call_class(),
                    Some(
                        CallClass::DeferToRequirement { .. } | CallClass::DeferToDictionary { .. }
                    )
                );
                // A constructor applied by its name (`H.holder([a, 5])` a rewrite leaves in a
                // body) takes its arguments at its fields, as its construction does.
                if crate::kb::op_info::lookup_operation_info(kb, target).is_none()
                    && kb.entity_field_types(*functor).is_some()
                {
                    self.constructor_fields(kb, *functor, own.as_ref(), pos_args, named_args, site);
                    return;
                }
                let mut params: Vec<(Symbol, Value)> = if through_dictionary {
                    Vec::new()
                } else if let Some(at_call) = occ.call_params().filter(|_| target == *functor) {
                    // The parameters of the operation the call names, as its σ reads them —
                    // where the call enters that operation; a call the typer sent to a member
                    // takes the member's.
                    at_call.to_vec()
                } else {
                    match crate::kb::op_info::lookup_operation_info(kb, target) {
                        Some(info) => info.params.clone(),
                        // A call of a function value: the parameters its arrow type says.
                        None => {
                            self.callable_params(kb, *functor, pos_args.len() + named_args.len())
                        }
                    }
                };
                // A call decided at load through a provision that answers the spec for values
                // of an abstract type (`StrmIter provides Iter[C = Strm[T = A]]`) takes its
                // receiver at that type: the `One` it is given is a `Strm` there.
                if let Some((index, at)) = provision_carrier_slot(kb, occ, target) {
                    if let Some(slot) = params.get_mut(index) {
                        slot.1 = at;
                    }
                }
                let at_param = |param: Symbol| TypeErrorContext::OperationArgument {
                    op_name: target,
                    param,
                };
                // A positional argument takes the parameter the labels leave it, as the call
                // binds it (`Sp.op(o, 2, s: w)`: `o` is `a`).
                let pos_params = positional_param_indices(kb, &params, pos_args.len(), named_args);
                for (i, a) in pos_args.iter().enumerate() {
                    let (slot, at) = match pos_params
                        .get(i)
                        .copied()
                        .flatten()
                        .and_then(|p| params.get(p))
                    {
                        Some((p, t)) => (Some(t.clone()), at_param(*p)),
                        None => (None, site.clone()),
                    };
                    self.node(kb, a, slot, &at);
                }
                for (name, a) in named_args {
                    let slot = params
                        .iter()
                        .find(|(p, _)| kb.local_name_of(*p) == kb.local_name_of(*name))
                        .map(|(_, t)| t.clone());
                    self.node(kb, a, slot, &at_param(*name));
                }
            }
            Expr::Constructor {
                name,
                pos_args,
                named_args,
                ..
            } => {
                if is_list_literal_functor(kb, *name) {
                    let elem = own
                        .as_ref()
                        .and_then(|t| parametric_view_parts(kb, t))
                        .and_then(|(_, args)| args.into_iter().next().map(|(_, v)| v));
                    for (index, a) in pos_args.iter().enumerate() {
                        let at = TypeErrorContext::CollectionElement {
                            construct: "list",
                            index,
                            source: ElementTypeSource::Declared,
                        };
                        self.node(kb, a, elem.clone(), &at);
                    }
                    for (_, a) in named_args {
                        self.node(kb, a, None, site);
                    }
                } else {
                    self.constructor_fields(kb, *name, own.as_ref(), pos_args, named_args, site);
                }
            }
            other => {
                let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
                for_each_child(other, |c| children.push(Rc::clone(c)));
                for c in children {
                    self.node(kb, &c, None, site);
                }
            }
        }
    }

    /// The arguments of a construction of `ctor`, each at its field's type in the constructed
    /// type `own` ([`field_type_at`]: a field typed at a parameter of the sort is at the
    /// parameter's argument there).
    fn constructor_fields(
        &mut self,
        kb: &mut KnowledgeBase,
        ctor: Symbol,
        own: Option<&Value>,
        pos_args: &[Rc<NodeOccurrence>],
        named_args: &[(Symbol, Rc<NodeOccurrence>)],
        site: &TypeErrorContext,
    ) {
        let fields: Vec<(Symbol, Value)> = kb
            .entity_field_types(ctor)
            .map(|f| f.to_vec())
            .unwrap_or_default();
        let sort = kb.sort_of_constructor(ctor);
        let inst: SmallVec<[(Symbol, Value); 2]> = own
            .and_then(|t| parametric_view_parts(kb, t))
            .map(|(_, args)| args)
            .unwrap_or_default();
        let at = |kb: &KnowledgeBase, fty: &Value| -> Value {
            match (sort, own) {
                (Some(sort), Some(own)) => {
                    field_type_at(kb, sort, fty, own, &inst).unwrap_or_else(|| fty.clone())
                }
                _ => fty.clone(),
            }
        };
        let at_field = |field: Symbol| TypeErrorContext::EntityField {
            entity: ctor,
            field,
        };
        for (i, a) in pos_args.iter().enumerate() {
            let (slot, site) = match fields.get(i) {
                Some((f, t)) => (Some(at(kb, t)), at_field(*f)),
                None => (None, site.clone()),
            };
            self.node(kb, a, slot, &site);
        }
        for (fname, a) in named_args {
            let slot = fields
                .iter()
                .find(|(f, _)| kb.local_name_of(*f) == kb.local_name_of(*fname))
                .map(|(_, t)| at(kb, t));
            self.node(kb, a, slot, &at_field(*fname));
        }
    }

    /// The parameter types of the function value `name` binds, called with `arity` arguments:
    /// its arrow's parameter, or that tuple's components.
    fn callable_params(
        &self,
        kb: &mut KnowledgeBase,
        name: Symbol,
        arity: usize,
    ) -> Vec<(Symbol, Value)> {
        let ty = self
            .locals
            .iter()
            .rev()
            .find(|(n, _)| *n == name)
            .map(|(_, t)| t.clone())
            .or_else(|| self.env.lookup_var(name));
        let Some(ty) = ty else {
            return Vec::new();
        };
        let Some((Some(param), _, _)) = arrow_parts(kb, &ty) else {
            return Vec::new();
        };
        if arity == 1 {
            return vec![(name, param)];
        }
        named_tuple_fields(kb, &param)
    }

    /// A call the typer sent to a member of another sort than the operation it names, typed at
    /// that operation: the member's result converted to it.
    fn member_result(
        &mut self,
        kb: &mut KnowledgeBase,
        occ: &Rc<NodeOccurrence>,
        site: &TypeErrorContext,
    ) -> Option<InstanceConversion> {
        let (spec_op, member) = match occ.call_class()? {
            CallClass::PinNow {
                spec_op_sym,
                impl_op_sym,
            } => (spec_op_sym, impl_op_sym),
            CallClass::ConcreteApplyWithin {
                spec_op_sym,
                fn_target_sym,
                ..
            } => (spec_op_sym, fn_target_sym),
            _ => return None,
        };
        if spec_op == member {
            return None;
        }
        let (Some(spec_info), Some(member_info)) = (
            crate::kb::op_info::lookup_operation_info(kb, spec_op),
            crate::kb::op_info::lookup_operation_info(kb, member),
        ) else {
            return None;
        };
        match conversion_between(
            kb,
            &member_info.return_type,
            &spec_info.return_type,
            None,
            self.chain,
            self.rigids,
        ) {
            Ok(c) => c,
            Err(why) => {
                self.refuse(occ, site, why);
                None
            }
        }
    }

    fn refuse(&mut self, occ: &Rc<NodeOccurrence>, site: &TypeErrorContext, why: String) {
        self.errors.push(TypeError::Other {
            site: TypeError::here(),
            span: Some(occ.span.span),
            context: site.clone(),
            expected: "one instance for a value used at an abstract type".into(),
            actual: why,
        });
    }
}

/// For a call classified through a provision (its resolved tree's provider `P`, spec `B`): the
/// index of `target`'s parameter at `B`'s carrier parameter and the type `P`'s provision binds
/// that carrier to, where that type is a sort with abstract values. `None` otherwise.
fn provision_carrier_slot(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    target: Symbol,
) -> Option<(usize, Value)> {
    let tree = match occ.call_class()? {
        CallClass::ConcreteApplyWithin {
            resolved_tree: Some(tree),
            ..
        } => tree,
        _ => return None,
    };
    let provider = tree.impl_sort()?;
    let spec = tree.spec_sort();
    let carrier_param = spec_carrier_param(kb, spec)?;
    let view = provider_spec_view_bindings(kb, provider, spec)?;
    let name = kb.local_name_of(carrier_param).to_owned();
    let at = view
        .iter()
        .find(|(k, _)| kb.local_name_of(*k) == name)
        .map(|(_, v)| v.clone())?;
    let head = sort_functor_of_view(kb, &at)?;
    let head = kb.canonical_sort_sym(kb.type_arg_owner(head).unwrap_or(head));
    if !is_abstract_carrier_sort(kb, head) {
        return None;
    }
    let info = crate::kb::op_info::lookup_operation_info(kb, target)?;
    let index = receiver_param_index(kb, &info.params, spec)?;
    Some((index, at))
}

/// The variable a binder pattern binds, where it binds one plainly (`x`, `x: T`).
fn pattern_var(pattern: &Rc<NodeOccurrence>) -> Option<Symbol> {
    match pattern.as_pattern()? {
        Pattern::Var { name } => Some(*name),
        _ => None,
    }
}

/// Is `functor` the constructor a list literal is read as in an operation body?
fn is_list_literal_functor(kb: &KnowledgeBase, functor: Symbol) -> bool {
    kb.qualified_name_of(functor) == "anthill.reflect.ListLiteral"
}

/// Proposal 073 §3 — in a spec's own default body, a call of the spec's operation at the
/// body's own carrier (`size(c)` in `Holder.size2(c: C) = size(c)`) takes the instance the body
/// runs at: the dictionary the body was entered with (`__req_self`). The call's class, or `None`
/// for any other call: one outside the spec's own body, or at a carrier the call names.
#[allow(clippy::too_many_arguments)]
pub(super) fn call_at_own_instance(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    op: &OperationInfoFull,
    fn_sym: Symbol,
    spec_sort: Symbol,
    pos_params: &[Option<usize>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    pos_results: &[Result<TypeResult, TypeError>],
    named_results: &[Result<TypeResult, TypeError>],
) -> Option<CallClass> {
    let own = env.enclosing_sort()?;
    if !same_sort_canonical(kb, own, spec_sort) {
        return None;
    }
    let carrier = spec_carrier_param(kb, spec_sort)?;
    let carrier_var = sort_type_params_as_pairs(kb, spec_sort)
        .iter()
        .find(|(p, _)| *p == carrier)
        .and_then(|(_, t)| declared_type_param_vid(kb, &Value::term(*t)))?;
    let rigid = env
        .param_rigids()
        .iter()
        .find(|(v, _)| *v == carrier_var)
        .map(|(_, r)| *r)?;
    let idx = receiver_param_index(kb, &op.params, spec_sort)?;
    let ty = supplied_arg_type(
        kb,
        &op.params,
        pos_params,
        idx,
        pos_results,
        named_args,
        named_results,
    )?;
    if !views_structurally_equal(kb, &ty, &Value::term(rigid)) {
        return None;
    }
    let syms = ProjectionSyms::resolve(kb)?;
    let req_self = kb.intern("__req_self");
    let dict = build_req_var_ref(kb, &syms, req_self);
    let short = short_name_of(kb.qualified_name_of(fn_sym)).to_owned();
    let op_short_sym = kb.intern(&short);
    Some(CallClass::DeferToDictionary {
        spec_op_sym: fn_sym,
        op_short_sym,
        dict,
    })
}

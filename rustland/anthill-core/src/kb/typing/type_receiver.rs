//! A dot on a receiver that denotes a sort (WI-20260824-PAPX0; proposal 055, design
//! `055-implementation.md` §4).
//!
//! `let t = Box[V = Int64]` gives `t` the type `Type`, and `t.m(…)` means what the written
//! `Box[V = Int64].m(…)` means: `m` is looked up among the members of `Box`, the arguments
//! are the call's as written, and the bracket binds `Box`'s parameters for the call. The
//! members of `Type` itself — the `Eq` and `Lattice` operations it provides — are not
//! reached through a receiver that denotes a sort, so every spelling of one type value
//! gives one answer:
//!
//! ```text
//! Box[V = Int64].tag()        (Box[V = Int64]).tag()        let t = Box[V = Int64]
//!                                                           t.tag()
//! ```
//!
//! A receiver of type `Type` that denotes nothing known at the dot — an operation's
//! parameter, a call's result — is a value like any other, and its dot is `Type`'s.

use super::*;

/// What a dot does when its receiver may denote a sort.
pub(super) enum DenotedDot {
    /// The receiver denotes no sort known at this dot; it is dispatched as a value.
    NotDenoting,
    /// The call the written spelling of this dot makes, to be typed in its place.
    Call(Rc<NodeOccurrence>),
    Refused(TypeError),
}

/// Resolve `receiver.member(args)` for a receiver that denotes a sort: the written type
/// itself, or a name a `let` bound to one.
///
/// The member is an operation or a constructor declared in the denoted sort. It is called
/// with the arguments as written — the receiver is a type, not a value of the sort, so it
/// fills no parameter — which is the call `Sort.member(args)` makes. A member the sort
/// does not declare is refused about that sort, whether or not `Type` has one of the name.
pub(super) fn denoted_sort_dot(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    receiver: &Rc<NodeOccurrence>,
    recv_sort: Option<Symbol>,
    member: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    occ: &Rc<NodeOccurrence>,
) -> DenotedDot {
    let Some(type_sym) = kb.try_resolve_symbol("anthill.prelude.Type") else {
        return DenotedDot::NotDenoting;
    };
    if recv_sort != Some(type_sym) {
        return DenotedDot::NotDenoting;
    }
    let Some(denotation) = denotation_of(kb, env, receiver) else {
        return DenotedDot::NotDenoting;
    };
    let Some(Expr::TypeValue {
        head,
        pos_args: type_pos,
        named_args: type_named,
    }) = denotation.as_expr()
    else {
        unreachable!("a denotation is a classified type value")
    };
    let bracketed = !(type_pos.is_empty() && type_named.is_empty());
    // An alias is read as a name path reads it (`read_path_through_aliases`): a pure
    // alias is the sort it stands for, and one that owns members of its own — a
    // `namespace CA` beside `sort CA = Box[V = Int64]` — is read as written. A call
    // through it is at the parameters it fixes, as the written `CA.m(…)` is. (An alias
    // is written bare; an applied one is refused where the type value is typed.)
    let (head, alias) = match *head {
        alias if !bracketed && kb.is_scan_alias(alias) && !owns_members(kb, alias) => {
            (kb.alias_head(alias).unwrap_or(alias), Some(alias))
        }
        written => (written, None),
    };
    let short = short_name_of(kb.local_name_of(member)).to_string();
    let span = Some(occ.span.span);
    // `site` is the caller's, so each refusal below records its own line.
    let refused = |site, expected: String, actual: String| {
        DenotedDot::Refused(TypeError::Other {
            site,
            span,
            context: TypeErrorContext::DotProjection { member },
            expected,
            actual,
        })
    };

    // An `internal` member is hidden from this dot where its written name would be.
    let from_scope = visibility_scope(kb, env.referencing_scope());
    let hidden = |kb: &KnowledgeBase, found: Symbol| {
        (!kb.symbols.internal_visible_from(found, from_scope)).then(|| {
            DenotedDot::Refused(TypeError::ForbiddenInternalMember {
                span,
                member: found,
                from_scope,
            })
        })
    };

    // The receiver the call is made at: the bracket rides it as the written companion
    // receiver's does, and so do the parameters an alias fixes. A bare sort says nothing
    // of its parameters, and neither does the call.
    let receiver = |kb: &mut KnowledgeBase| -> Result<Option<Value>, DenotedDot> {
        if !bracketed {
            return Ok(alias
                .and_then(|alias| alias_receiver_type(kb, alias))
                .map(Value::term));
        }
        match type_value_denoted_type(kb, env, &denotation) {
            Some(id) => Ok(Some(Value::term(id))),
            None => {
                let written =
                    crate::persistence::print::TermPrinter::new(kb).print_occurrence(&denotation);
                Err(refused(
                    TypeError::here(),
                    "a receiver whose type arguments are written types".to_string(),
                    format!(
                        "`{written}` has an argument that names no type here; write the call on the type itself, `{written}.{short}(…)`"
                    ),
                ))
            }
        }
    };

    if let Some(op) = crate::kb::load::find_operation_in_sort(kb, head, &short) {
        if let Some(refusal) = hidden(kb, op) {
            return refusal;
        }
        let recv_type = match receiver(kb) {
            Ok(recv_type) => recv_type,
            Err(refusal) => return refusal,
        };
        let pass = crate::kb::simp_rewrite::simp_pass(kb);
        return DenotedDot::Call(NodeOccurrence::synthesized_expr(
            Expr::Apply {
                recv_type,
                functor: op,
                pos_args: pos_args.to_vec(),
                named_args: named_args.to_vec(),
                type_args: Vec::new(),
            },
            Rc::clone(occ),
            pass,
            occ.owner,
        ));
    }

    let constructor = kb
        .constructors_of_sort(head)
        .into_iter()
        .find(|c| short_name_of(kb.local_name_of(*c)) == short);
    if let Some(constructor) = constructor {
        if let Some(refusal) = hidden(kb, constructor) {
            return refusal;
        }
        let recv_type = match receiver(kb) {
            Ok(recv_type) => recv_type,
            Err(refusal) => return refusal,
        };
        let pass = crate::kb::simp_rewrite::simp_pass(kb);
        return DenotedDot::Call(NodeOccurrence::synthesized_expr(
            Expr::Constructor {
                name: constructor,
                pos_args: pos_args.to_vec(),
                named_args: named_args.to_vec(),
                from_projection: false,
                recv_type,
                // A dot carries no bracket.
                type_args: Vec::new(),
            },
            Rc::clone(occ),
            pass,
            occ.owner,
        ));
    }

    let denoted = kb.local_name_of(head).to_string();
    // Declared in the sort, but not something a call reaches: a constant, a nested sort,
    // a rule. Saying "no such member" of it would be false.
    let qualified = format!("{}.{short}", kb.qualified_name_of(head));
    if kb.symbols.by_qualified_name.contains_key(&qualified) {
        return refused(
            TypeError::here(),
            format!("an operation or a constructor of `{denoted}`"),
            format!(
                "`{short}` is declared in `{denoted}` and is neither; a receiver that denotes a sort reaches the sort's operations and constructors only"
            ),
        );
    }
    // A member of `Type` of this name is not an answer, and the refusal says where it is.
    if head != type_sym {
        if let Some(on_type) = type_value_member(kb, type_sym, &short) {
            let on_type = kb.qualified_name_of(on_type).to_string();
            return refused(
                TypeError::here(),
                format!("a member of `{denoted}`, the sort this receiver denotes"),
                format!(
                    "`{denoted}` declares no `{short}`; `{on_type}` is a member of `Type`, which a receiver that denotes a sort does not reach — call it by name with the type as its first argument, `{on_type}(…)`"
                ),
            );
        }
    }
    DenotedDot::Refused(TypeError::DotDispatchNoMatch {
        span,
        member,
        receiver_sort: Some(head),
        receiver_param: None,
    })
}

/// The written type `receiver` denotes: itself when it is one, else the type a `let` bound
/// its name to. One alias hop is read through (`let u = t`), as a receiver path is.
fn denotation_of(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    receiver: &Rc<NodeOccurrence>,
) -> Option<Rc<NodeOccurrence>> {
    if let Some(Expr::TypeValue { .. }) = receiver.as_expr() {
        return Some(Rc::clone(receiver));
    }
    stable_receiver_path(kb, receiver)
        .map(|p| env.canonicalize_receiver_path(p))
        .filter(|p| p.len() == 1)
        .and_then(|p| env.type_denotation(p[0]).cloned())
}

/// The member of the `Type` value a dot on a non-denoting receiver would reach: one
/// declared in `Type`, or an operation of a spec `Type` provides.
fn type_value_member(kb: &mut KnowledgeBase, type_sym: Symbol, short: &str) -> Option<Symbol> {
    crate::kb::load::find_operation_in_sort(kb, type_sym, short)
        .or_else(|| find_spec_op_for_provided_sort(kb, type_sym, short))
}

/// The type a written type value denotes — the term the same text lowers to in a type
/// position, which is what a companion receiver's bracket is read as.
///
/// A positional argument binds the next parameter no name took (`Box[Int64]` is
/// `Box[V = Int64]`), and a type parameter of the enclosing declaration is that
/// parameter, whether typing left the read as written or lowered it to its slot. `None`
/// when an argument names no type.
pub(super) fn type_value_denoted_type(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
) -> Option<TermId> {
    if let Some(param) = value_read_type_param(kb, env.enclosing_frame_chain(), occ) {
        return Some(kb.alloc(Term::Var(Var::Global(param))));
    }
    let Some(Expr::TypeValue {
        head,
        pos_args,
        named_args,
    }) = occ.as_expr()
    else {
        // A constant in a type (`Vec[N = 3]`), a tuple type: the shapes a type argument
        // can be besides a nominal type.
        return crate::kb::node_occurrence::type_denoted_by(kb, &Value::Node(Rc::clone(occ)));
    };
    let head = *head;
    if pos_args.is_empty() && named_args.is_empty() {
        return Some(kb.make_sort_ref(head));
    }
    let declared = kb.type_params_of_sort(head);
    let mut bindings: Vec<(Symbol, TermId)> = Vec::with_capacity(pos_args.len() + named_args.len());
    for (name, arg) in named_args {
        bindings.push((*name, type_value_denoted_type(kb, env, arg)?));
    }
    let slots = KnowledgeBase::positional_param_slots(
        &declared,
        |d| named_args.iter().any(|(n, _)| kb.local_name_of(*n) == d),
        pos_args.len(),
    );
    for (arg, slot) in pos_args.iter().zip(slots) {
        // Typing the type value refused a positional with no parameter left to bind.
        let param = kb.intern(&declared[slot?]);
        bindings.push((param, type_value_denoted_type(kb, env, arg)?));
    }
    let base = kb.make_sort_ref(head);
    Some(kb.make_parameterized_type(base, &bindings))
}

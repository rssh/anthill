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
//! A type member is read the same way, in a type as well as a value: `dd.T` under `let dd =
//! D` is `D.T` ([`denoted_member_type`]), and a parameter the bracket binds is the type it
//! binds.
//!
//! A receiver of type `Type` that denotes nothing known at the dot — an operation's
//! parameter, a call's result — is a value like any other, and its dot is `Type`'s.
//!
//! A rule body reads a receiver written as a type the same way. The loader builds it as
//! the type value (`written_type_receiver_occurrence`), and the dot is replaced by its
//! written call before anything else reads the rule body
//! ([`written_type_dots_as_calls`]), so the two spellings are one node there. One
//! difference: a constructor is refused. In a rule body's own term a constructor is the
//! term the clause matches, which the loader builds from the written `Sort.ctor(…)`.

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
/// The member is an operation, a constructor, a rule or a type member declared in the
/// denoted sort. It is called with the arguments as written — the receiver is a type, not a
/// value of the sort, so it fills no parameter — which is the call `Sort.member(args)` makes;
/// a rule is the relation `Sort.member(args)` cites; a type member is the type value
/// `Sort.Member` is. Without parentheses the member is the same call with no arguments,
/// which `Sort.member` is too. A member the sort does not declare is refused about that sort,
/// whether or not `Type` has one of the name. A constructor is refused in a rule body's own
/// term, with its written spelling.
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
    written_sort_dot(kb, env, type_sym, &denotation, member, pos_args, named_args, occ)
}

/// [`denoted_sort_dot`] for the type value the receiver denotes: the call the written
/// `Sort[…].member(args)` makes, or its refusal.
fn written_sort_dot(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    type_sym: Symbol,
    denotation: &Rc<NodeOccurrence>,
    member: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    occ: &Rc<NodeOccurrence>,
) -> DenotedDot {
    let sort = denoted_sort(kb, denotation);
    let (head, alias, bracketed) = (sort.head, sort.alias, sort.bracketed);
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
    let from_scope = written_scope(kb, env, occ);
    let hidden = |kb: &KnowledgeBase, found: Symbol| {
        hidden_dot_member(kb, found, from_scope, span).map(DenotedDot::Refused)
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
        match type_value_denoted_type(kb, env, denotation) {
            Some(id) => Ok(Some(Value::term(id))),
            None => {
                let written =
                    crate::persistence::print::TermPrinter::new(kb).print_occurrence(denotation);
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
        if let Some(e) = effectful_rewrite_call(kb, occ, op) {
            return DenotedDot::Refused(e);
        }
        let recv_type = match receiver(kb) {
            Ok(recv_type) => recv_type,
            Err(refusal) => return refusal,
        };
        let pass = crate::kb::simp_rewrite::simp_pass(kb);
        // The call reads as the dot was written: `t.inc` without parentheses is a
        // function value where one is expected, as `Box.inc` is.
        return DenotedDot::Call(NodeOccurrence::synthesized_expr_written(
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
            occ.is_paren_less(),
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
        // In a rule body's own term a constructor is the term the clause matches, and
        // the loader builds that term from the written name: it names the positional
        // arguments by their fields and leaves an omitted field open. The construction
        // built below is a call, and stored in a rule body it would match as a different
        // term.
        if !env.written_as_an_operation_body() {
            // Its qualified name, which is written the same from every scope: the
            // receiver may have been a path, or an alias, that the sort's short name is
            // not.
            let written = kb.qualified_name_of(constructor).to_string();
            return refused(
                TypeError::here(),
                format!("the constructor written by its name, `{written}(…)`"),
                format!(
                    "`{short}` reached by a dot on a receiver that denotes a sort; in a rule body a constructor is the term the clause matches, which its written name builds and this dot does not"
                ),
            );
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

    let qualified = format!("{}.{short}", kb.qualified_name_of(head));
    let declared = kb.symbols.by_qualified_name.get(&qualified).copied();

    // A rule of the sort is the relation the written `Sort.rule(…)` cites, and `Sort.rule`
    // without parentheses is that relation itself, which the call with no arguments is
    // too. In an operation body the bracket selects the instance; in a rule body a
    // relation is passed no type argument, and the bracket is refused as the written
    // spelling's is.
    if let Some(rule) = declared.filter(|d| kb.cites_a_relation(*d)) {
        if let Some(refusal) = hidden(kb, rule) {
            return refusal;
        }
        let recv_type = match receiver(kb) {
            Ok(recv_type) => recv_type,
            Err(refusal) => return refusal,
        };
        if recv_type.is_some() && !env.written_as_an_operation_body() {
            let written = kb.qualified_name_of(rule).to_string();
            return refused(
                TypeError::here(),
                format!("the relation written without the bracket, `{written}(…)`"),
                crate::kb::load::rule_body_relation_bracket_detail(kb, rule),
            );
        }
        let pass = crate::kb::simp_rewrite::simp_pass(kb);
        return DenotedDot::Call(NodeOccurrence::synthesized_expr(
            Expr::Apply {
                recv_type,
                functor: rule,
                pos_args: pos_args.to_vec(),
                named_args: named_args.to_vec(),
                type_args: Vec::new(),
            },
            Rc::clone(occ),
            pass,
            occ.owner,
        ));
    }

    let denoted = kb.local_name_of(head).to_string();

    // A type member of the sort is the type value the written `Sort.Member` is, and a
    // parameter the bracket binds is the type the bracket gives it: `dd.T` under `let dd =
    // D` is `D.T`, and `pp.T` under `let pp = P[T = String]` is `String`.
    if let Some(found) = declared.filter(|d| kb.has_kind(*d, crate::intern::SymbolKind::Sort)) {
        if let Some(refusal) = hidden(kb, found) {
            return refusal;
        }
        if !occ.is_paren_less() || !pos_args.is_empty() || !named_args.is_empty() {
            return refused(
                TypeError::here(),
                format!("the type member written without parentheses, `{denoted}.{short}`"),
                format!("`{short}` is a type member of `{denoted}`, and a type is no call"),
            );
        }
        let node = match denoted_type_member(kb, denotation, &sort, found) {
            DenotedMember::Entry(entry) => match entry.as_expr() {
                Some(expr) => NodeOccurrence::synthesized_expr(
                    expr.clone(),
                    Rc::clone(occ),
                    crate::kb::simp_rewrite::simp_pass(kb),
                    occ.owner,
                ),
                None => unreachable!("an entry of a type value's bracket is an expression"),
            },
            DenotedMember::Fixed(ty) => {
                crate::kb::load::type_value_occurrence(kb, ty, occ.span, occ.owner)
            }
            kind @ (DenotedMember::Open | DenotedMember::Member) => {
                // A parameter left open is its written name; another member is read at the
                // parameters the receiver binds.
                let at = match kind {
                    DenotedMember::Open => MemberAt::Name,
                    _ => match denoted_receiver_type(kb, env, denotation, &sort) {
                        Some(receiver) => member_at(kb, head, found, receiver.as_ref()),
                        None => {
                            return refused(
                                TypeError::here(),
                                "a receiver whose type arguments are written types".to_string(),
                                unnamed_argument(kb, denotation),
                            )
                        }
                    },
                };
                match at {
                    // The type value the written `Sort.Member` is, as the loader builds a
                    // written type — with the operation-body walk, in a rule body too
                    // (`Loader::written_type_receiver_occurrence`), so a structural alias is
                    // the type it stands for.
                    MemberAt::Name => {
                        let within =
                            crate::kb::load::written_within_declaring_scope(kb, found, from_scope);
                        crate::kb::load::name_type_value_occurrence(
                            kb, found, within, true, occ.span, occ.owner,
                        )
                    }
                    MemberAt::Definition(ty) => type_value_of(kb, &ty, occ),
                    MemberAt::Open => {
                        let (expected, actual) = open_member_refusal(kb, head, found);
                        return refused(TypeError::here(), expected, actual);
                    }
                }
            }
        };
        return DenotedDot::Call(node);
    }
    // Declared in the sort, but not something a dot reaches: a constant. Saying "no such
    // member" of it would be false.
    if declared.is_some() {
        return refused(
            TypeError::here(),
            format!("an operation, a constructor, a rule or a type member of `{denoted}`"),
            format!(
                "`{short}` is declared in `{denoted}` and is none of them; a receiver that denotes a sort reaches the sort's operations, constructors, rules and type members only"
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

/// The sort a type value denotes, read as a name path reads it
/// (`read_path_through_aliases`): a pure alias is the sort it stands for, and one that owns
/// members of its own — a `namespace CA` beside `sort CA = Box[V = Int64]` — is read as
/// written. A member reached through it is at the parameters it fixes, as the written `CA.m`
/// is. (An alias is written bare; an applied one is refused where the type value is typed.)
struct DenotedSort {
    head: Symbol,
    /// The alias the value names, where `head` is the sort it stands for.
    alias: Option<Symbol>,
    /// The value writes type arguments.
    bracketed: bool,
}

impl DenotedSort {
    /// The parameters the alias the value names fixes.
    fn alias_fixed(&self, kb: &KnowledgeBase) -> SmallVec<[(Symbol, TermId); 2]> {
        self.alias
            .and_then(|alias| alias_type_application(kb, alias))
            .map(|(_, fixed)| fixed)
            .unwrap_or_default()
    }
}

fn denoted_sort(kb: &KnowledgeBase, denotation: &Rc<NodeOccurrence>) -> DenotedSort {
    let Some(Expr::TypeValue {
        head,
        pos_args,
        named_args,
    }) = denotation.as_expr()
    else {
        unreachable!("a denotation is a classified type value")
    };
    let bracketed = !(pos_args.is_empty() && named_args.is_empty());
    let (head, alias) = match *head {
        alias if !bracketed && kb.is_scan_alias(alias) && !owns_members(kb, alias) => {
            (kb.alias_head(alias).unwrap_or(alias), Some(alias))
        }
        written => (written, None),
    };
    DenotedSort {
        head,
        alias,
        bracketed,
    }
}

/// What the type member `member` of a denoted sort is, read through the receiver.
enum DenotedMember {
    /// A parameter of the sort the receiver's bracket binds: the entry the bracket writes.
    Entry(Rc<NodeOccurrence>),
    /// A parameter the alias the receiver names fixes: the type it fixes.
    Fixed(TermId),
    /// A parameter the receiver leaves open, which the written `Sort.Member` names.
    Open,
    /// Any other member, which the written `Sort.Member` names.
    Member,
}

fn denoted_type_member(
    kb: &KnowledgeBase,
    denotation: &Rc<NodeOccurrence>,
    sort: &DenotedSort,
    member: Symbol,
) -> DenotedMember {
    let Some(Expr::TypeValue {
        pos_args,
        named_args,
        ..
    }) = denotation.as_expr()
    else {
        unreachable!("a denotation is a classified type value")
    };
    let short = short_name_of(kb.local_name_of(member));
    let declared = kb.type_params_of_sort(sort.head);
    let Some(slot) = declared.iter().position(|d| d == short) else {
        return DenotedMember::Member;
    };
    let named_short = |k: &Symbol| short_name_of(kb.local_name_of(*k));
    if let Some((_, entry)) = named_args.iter().find(|(k, _)| named_short(k) == short) {
        return DenotedMember::Entry(Rc::clone(entry));
    }
    let slots = KnowledgeBase::positional_param_slots(
        &declared,
        |d| named_args.iter().any(|(k, _)| named_short(k) == d),
        pos_args.len(),
    );
    if let Some((entry, _)) = pos_args.iter().zip(slots).find(|(_, s)| *s == Some(slot)) {
        return DenotedMember::Entry(Rc::clone(entry));
    }
    match sort.alias_fixed(kb).into_iter().find(|(k, _)| named_short(k) == short) {
        Some((_, ty)) => DenotedMember::Fixed(ty),
        None => DenotedMember::Open,
    }
}

/// The type member `member` declares in `sort` — a nested sort, an alias, a parameter — by its
/// qualified name, as the written `Sort.Member` names it. An eponymous sort's name is its
/// constructor's, as the loader's `sort_named` reads it.
pub(super) fn declared_type_member(kb: &KnowledgeBase, sort: Symbol, member: &str) -> Option<Symbol> {
    let qualified = format!("{}.{member}", kb.qualified_name_of(sort));
    kb.symbols
        .by_qualified_name
        .get(&qualified)
        .copied()
        .filter(|d| kb.has_kind(*d, crate::intern::SymbolKind::Sort) && !kb.is_entity_constructor(*d))
}

/// What `Alias.Member` names in a clause's term, a rule body's data slot or a query, where
/// `Alias` is a type alias that owns no members and fixes parameters of the sort it stands
/// for (`CA.T` over `sort CA = P[T = String]`): that sort's member read at the parameters the
/// alias fixes, as a dot on the alias's type value reads it in an operation body
/// ([`denoted_sort_dot`]). For the walks that build a term with no typer after them.
pub(crate) enum AliasMember {
    /// The member, read as its written name is.
    Name(Symbol),
    /// The type it is at the alias's parameters.
    Type(TermId),
    /// Its definition names a parameter the alias leaves open: the refusal's sentence.
    Open(String),
}

/// [`AliasMember`] of `alias` and `member`; `None` where `alias` is no such alias or its
/// sort declares no type member `member`.
pub(crate) fn alias_member(kb: &mut KnowledgeBase, alias: Symbol, member: &str) -> Option<AliasMember> {
    if !kb.is_scan_alias(alias) || owns_members(kb, alias) {
        return None;
    }
    let (base, fixed) = alias_type_application(kb, alias)?;
    if fixed.is_empty() {
        return None;
    }
    let found = declared_type_member(kb, base, member)?;
    if kb.type_params_of_sort(base).iter().any(|p| p == member) {
        return Some(
            match fixed.iter().find(|(k, _)| short_name_of(kb.local_name_of(*k)) == member) {
                Some((_, ty)) => AliasMember::Type(*ty),
                None => AliasMember::Name(found),
            },
        );
    }
    let base_ref = kb.make_sort_ref(base);
    let receiver = Value::term(kb.make_parameterized_type(base_ref, &fixed));
    Some(match member_at(kb, base, found, Some(&receiver)) {
        MemberAt::Name => AliasMember::Name(found),
        MemberAt::Definition(ty) => match crate::kb::node_occurrence::value_to_term(kb, &ty) {
            Ok(id) => AliasMember::Type(id),
            Err(_) => AliasMember::Open(format!(
                "`{alias}.{member}` is a type that holds a value, which a clause's term does not hold",
                alias = kb.local_name_of(alias),
            )),
        },
        MemberAt::Open => {
            let (_, actual) = open_member_refusal(kb, base, found);
            AliasMember::Open(actual)
        }
    })
}

/// What a type member of a sort that is no parameter is through a receiver of the sort.
pub(super) enum MemberAt {
    /// The member as its written name reads: one whose definition names none of the sort's
    /// parameters, or one reached through a receiver that binds none of them.
    Name,
    /// Its definition, the parameters the receiver binds read into it: `L` over `sort L =
    /// List[T = A]` through a receiver of `Q[A = Int64]` is `List[T = Int64]`.
    Definition(Value),
    /// Its definition names a parameter the receiver leaves open.
    Open,
}

/// The type member `member` of `sort`, a member that is no parameter, through a receiver of
/// the type `receiver`: its definition at the parameters the receiver binds, as a field's
/// type is read at them ([`build_pattern_subst`]). `None` for a receiver that says nothing of
/// the sort's parameters — a bare sort — which reads the member as its written name does.
pub(super) fn member_at(
    kb: &mut KnowledgeBase,
    sort: Symbol,
    member: Symbol,
    receiver: Option<&Value>,
) -> MemberAt {
    let Some(definition) = kb.alias_types.get(&member).cloned() else {
        return MemberAt::Name;
    };
    if !holds_type_parameter_var(kb, &definition) {
        return MemberAt::Name;
    }
    let Some(subst) = receiver.and_then(|r| build_pattern_subst(kb, r, sort)) else {
        return MemberAt::Name;
    };
    let at = walk_pattern_field_type_deep(kb, &subst, &definition);
    if holds_type_parameter_var(kb, &at) {
        MemberAt::Open
    } else {
        MemberAt::Definition(at)
    }
}

/// The refusal of [`MemberAt::Open`]. `(expected, actual)`.
pub(super) fn open_member_refusal(kb: &KnowledgeBase, sort: Symbol, member: Symbol) -> (String, String) {
    let sort = kb.local_name_of(sort);
    let short = short_name_of(kb.local_name_of(member));
    (
        format!("a member of `{sort}` the receiver's type arguments determine"),
        format!(
            "`{short}` is defined over a parameter of `{sort}` the receiver leaves open; bind it, `{sort}[…]`"
        ),
    )
}

/// The type a receiver that denotes a sort is, at which a member reached through it is read:
/// its bracket, as the written companion receiver's is, or the parameters its alias fixes.
/// `Some(None)` for a bare sort, which says nothing of its parameters; `None` where an
/// argument of the bracket names no type.
fn denoted_receiver_type(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    denotation: &Rc<NodeOccurrence>,
    sort: &DenotedSort,
) -> Option<Option<Value>> {
    if !sort.bracketed {
        return Some(sort.alias.and_then(|alias| alias_receiver_type(kb, alias)).map(Value::term));
    }
    type_value_denoted_type(kb, env, denotation).map(|id| Some(Value::term(id)))
}

/// The refusal's text of a bracket an argument of which names no type.
fn unnamed_argument(kb: &KnowledgeBase, denotation: &Rc<NodeOccurrence>) -> String {
    let written = crate::persistence::print::TermPrinter::new(kb).print_occurrence(denotation);
    format!("`{written}` has an argument that names no type here")
}

/// `x.T` read as a value, where `x` is a value of `sort` and `T` a type member of it: the type
/// value of the type the projection off `x` is, when it names no type parameter. A type
/// member is no call: `called` refuses `x.T()`.
pub(super) fn type_member_as_value(
    kb: &mut KnowledgeBase,
    receiver_ty: &Value,
    sort: Symbol,
    member_short: &str,
    member: Symbol,
    called: bool,
    occ: &Rc<NodeOccurrence>,
) -> Result<Rc<NodeOccurrence>, TypeError> {
    let span = Some(occ.span.span);
    let ctx = TypeErrorContext::DotProjection { member };
    let denoted = kb.local_name_of(sort).to_string();
    let refused = |expected: String, actual: String| TypeError::Other {
        site: TypeError::here(),
        span,
        context: TypeErrorContext::DotProjection { member },
        expected,
        actual,
    };
    if called {
        return Err(refused(
            format!("the type member written without parentheses, `.{member_short}`"),
            format!("`{member_short}` is a type member of `{denoted}`, and a type is no call"),
        ));
    }
    // Known at load: no variable, no projection off a value, no parameter of the body.
    let known = |kb: &KnowledgeBase, ty: &Value| {
        kb.collect_vars(ty).is_empty()
            && !value_contains_projection(kb, ty)
            && !value_contains_rigid(kb, ty)
    };
    match project_type_member(kb, receiver_ty, member_short, None, None, &[], &ctx, span)? {
        ProjResult::Grounded(ty) if known(kb, &ty) => Ok(type_value_of(kb, &ty, occ)),
        _ => Err(refused(
            format!("a type member of `{denoted}` the receiver's type determines"),
            format!(
                "`{member_short}` is a type member of `{denoted}`, and the receiver's type leaves it open here, so it is no type value"
            ),
        )),
    }
}

/// The type value of the type `ty`, built where `occ` stands: as the walks build a type written
/// in value position (`load::type_value_occurrence`).
fn type_value_of(kb: &mut KnowledgeBase, ty: &Value, occ: &Rc<NodeOccurrence>) -> Rc<NodeOccurrence> {
    match crate::kb::node_occurrence::value_to_term(kb, ty) {
        Ok(id) => crate::kb::load::type_value_occurrence(kb, id, occ.span, occ.owner),
        // A type that holds a value rides an occurrence, and is spliced as the type itself.
        Err(_) => {
            let node = NodeOccurrence::new_expr(Expr::Spliced(ty.clone()), occ.span, occ.owner);
            let type_ty = kb.make_sort_ref_by_name("anthill.prelude.Type");
            node.set_inferred_type(Value::term(type_ty));
            node
        }
    }
}

/// `name.member` in a type, where a `let` bound `name` to a written type: the type the
/// written `Sort.member` is, and a parameter the bracket binds is the type the bracket gives
/// it — `let y: dd.T = 5` under `let dd = D` is `let y: D.T = 5`. A parameter left open is
/// refused as `Sort.member` written out is. `scope` is where the text is written
/// ([`written_scope`]). `None` when `name` denotes no sort here.
pub(super) fn denoted_member_type(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    scope: ScopeId,
    receiver: &Value,
    member: Symbol,
    ctx: &TypeErrorContext,
    span: Option<Span>,
) -> Option<Result<Value, TypeError>> {
    let name = extract_sort_ref_sym(kb, receiver)?;
    let denotation = denotation_of_name(env, name)?;
    let sort = denoted_sort(kb, &denotation);
    let head = sort.head;
    let short = short_name_of(kb.local_name_of(member)).to_string();
    let Some(found) = declared_type_member(kb, head, &short) else {
        return Some(Err(projection_type_error(
            ctx,
            span,
            &format!(
                "type '{}' has no member '{short}'",
                kb.qualified_name_of(head).to_owned()
            ),
        )));
    };
    if let Some(e) = hidden_dot_member(kb, found, scope, span) {
        return Some(Err(e));
    }
    Some(match denoted_type_member(kb, &denotation, &sort, found) {
        DenotedMember::Entry(entry) => match type_value_denoted_type(kb, env, &entry) {
            Some(ty) => Ok(Value::term(ty)),
            None => {
                let written =
                    crate::persistence::print::TermPrinter::new(kb).print_occurrence(&entry);
                Err(projection_type_error(
                    ctx,
                    span,
                    &format!("`{written}`, which `{short}` is bound to, names no type here"),
                ))
            }
        },
        DenotedMember::Fixed(ty) => Ok(Value::term(ty)),
        // The projection the written `Sort.member` is: off the sort itself it grounds, or is
        // refused as not manifest.
        DenotedMember::Open => {
            let subject = Value::term(kb.make_sort_ref(head));
            match resolve_rigid_projection(kb, head, &subject, member, ctx, span) {
                Ok(ProjResult::Grounded(v)) => Ok(v),
                Ok(ProjResult::Neutral) => Err(projection_type_error(
                    ctx,
                    span,
                    &format!("'{}.{short}' is not manifest here", kb.local_name_of(head)),
                )),
                Err(e) => Err(e),
            }
        }
        DenotedMember::Member => {
            let Some(at) = denoted_receiver_type(kb, env, &denotation, &sort) else {
                return Some(Err(projection_type_error(
                    ctx,
                    span,
                    &unnamed_argument(kb, &denotation),
                )));
            };
            match member_at(kb, head, found, at.as_ref()) {
                // The member as the written name reads in a type: an alias is the type it
                // stands for, its name kept beside it.
                MemberAt::Name => {
                    let within = crate::kb::load::written_within_declaring_scope(kb, found, scope);
                    Ok(written_member_type(kb, found, within, site_of(receiver)))
                }
                MemberAt::Definition(ty) => Ok(ty),
                MemberAt::Open => {
                    let (expected, actual) = open_member_refusal(kb, head, found);
                    Err(TypeError::Other {
                        site: TypeError::here(),
                        span,
                        context: ctx.clone(),
                        expected,
                        actual,
                    })
                }
            }
        }
    })
}

/// The type member `member` as its written name reads in a type: an alias is the type it
/// stands for, its name kept beside it (`load::alias_read`).
pub(super) fn written_member_type(
    kb: &mut KnowledgeBase,
    member: Symbol,
    within: bool,
    site: (crate::span::SourceSpan, Option<Symbol>),
) -> Value {
    match crate::kb::load::alias_read(kb, member, within, true, site.0, site.1) {
        Some(child) => crate::kb::node_occurrence::type_child_as_value(&child),
        None => Value::term(kb.make_sort_ref(member)),
    }
}

/// Is `expr` a dot whose receiver is a written type?
fn is_written_type_dot(expr: &Expr) -> bool {
    matches!(expr, Expr::DotApply { receiver, .. }
        if matches!(receiver.as_expr(), Some(Expr::TypeValue { .. })))
}

/// Does a rule body's node hold a dot on a written type in the rule's own term? What
/// stands under a compound expression is written as an operation body is, and the typer
/// reads its dots where it types it.
pub(super) fn holds_written_type_dot(occ: &Rc<NodeOccurrence>) -> bool {
    let mut stack: Vec<Rc<NodeOccurrence>> = vec![Rc::clone(occ)];
    while let Some(o) = stack.pop() {
        let Some(expr) = o.as_expr() else { continue };
        if is_compound_expression(expr) {
            continue;
        }
        if is_written_type_dot(expr) {
            return true;
        }
        for_each_child(expr, |c| stack.push(Rc::clone(c)));
    }
    false
}

/// A rule body's node with every dot on a written type in the rule's own term replaced by
/// the call its written spelling makes: `(Box[V = Int64]).wrap(?y)` by the node of
/// `Box[V = Int64].wrap(?y)`.
///
/// Done before anything else reads the rule body, so that the two spellings are one node
/// to every reader: the collection of variable types reads the call's parameters, the
/// dispatch walk gives it the written call's shape, and the resolver evaluates what the
/// written call stores. Left a dot, it was typed as a dot is — checked and rewritten at
/// load where the written call in the same place is a data term — and the two spellings
/// gave one rule two verdicts.
///
/// A refusal ([`denoted_sort_dot`]) is reported and leaves the dot in place.
pub(super) fn written_type_dots_as_calls(
    kb: &mut KnowledgeBase,
    env: &TypingEnv,
    occ: &Rc<NodeOccurrence>,
    errors: &mut Vec<TypeError>,
) -> Rc<NodeOccurrence> {
    let Some(expr) = occ.as_expr() else {
        return Rc::clone(occ);
    };
    if is_compound_expression(expr) {
        return Rc::clone(occ);
    }
    let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
    for_each_child(expr, |c| children.push(Rc::clone(c)));
    let children: Vec<Rc<NodeOccurrence>> = children
        .iter()
        .map(|c| written_type_dots_as_calls(kb, env, c, errors))
        .collect();
    let walked = crate::kb::simp_rewrite::reassemble(occ, &children);
    let Some(Expr::DotApply {
        receiver,
        name,
        pos_args,
        named_args,
    }) = walked.as_expr().filter(|e| is_written_type_dot(e))
    else {
        return walked;
    };
    // A program that loads without the standard library has no `Type`, and no type value.
    let Some(type_sym) = kb.try_resolve_symbol("anthill.prelude.Type") else {
        return walked;
    };
    match written_sort_dot(kb, env, type_sym, receiver, *name, pos_args, named_args, &walked) {
        DenotedDot::Call(call) => call,
        DenotedDot::Refused(e) => {
            errors.push(e);
            Rc::clone(&walked)
        }
        DenotedDot::NotDenoting => unreachable!("a written type denotes its sort"),
    }
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
    let path = stable_receiver_path(kb, receiver)?;
    match path[..] {
        [name] => denotation_of_name(env, name),
        _ => None,
    }
}

/// The written type a `let` bound `name` to, read through one alias hop (`let u = t`).
fn denotation_of_name(env: &TypingEnv, name: Symbol) -> Option<Rc<NodeOccurrence>> {
    let path = env.canonicalize_receiver_path(vec![name]);
    match path[..] {
        [name] => env.type_denotation(name).cloned(),
        _ => None,
    }
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

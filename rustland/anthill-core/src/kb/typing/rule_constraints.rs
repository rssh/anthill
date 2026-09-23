//! Collecting type constraints on rule variables from declared types.

use super::*;

/// WI-9C2PZ — ONE APPLICATION's instantiation of the type parameters its callee's
/// signature binds: canonical parameter variable (`VarId::raw()`) → the fresh variable
/// THIS call site stands it up as.
///
/// Per APPLICATION, not per parameter position, which is the whole point: `eq(?x, ?y)`
/// declares both arguments at one `T`, so both must land on ONE fresh variable and stay
/// correlated, while the NEXT `eq` in the same rule body gets a different one and is
/// independent.
///
/// Usually empty and allocated lazily for that reason — a concrete signature
/// (`parent(of: String, is: String)`, `Int64.lt(a: Int64, b: Int64)`) mentions no
/// parameter and mints nothing.
pub(super) type ParamInstantiation = HashMap<u32, TermId>;

/// WI-9C2PZ — the variables whose recorded type came from a callee's INSTANTIATED
/// PARAMETER, i.e. from a call, rather than from a declared position of the variable
/// itself.
///
/// The distinction decides who owns a disagreement, and getting it wrong loses a located
/// error. `var_types` answers "what do this variable's own positions say"; a per-call
/// parameter says nothing about the variable and is recorded only as a placeholder — so
/// when a declared position arrives it takes over, and when the two cannot be reconciled
/// the fault is the CALL's, not the variable's. See [`constrain_vid`].
pub(super) type ParamBackedVars = HashSet<u32>;

/// WI-9C2PZ — the canonical type-parameter VARIABLE a declared-type node denotes, if it
/// denotes one.
///
/// Named `declared_type_param_var` until WI-20260923-N3W68, which is also the name of
/// [`crate::kb::op_info::declared_type_param_var`] — a DIFFERENT question (the variable an
/// operation's own bracket declares, by short name) asked of different arguments. Two
/// functions, one name, in one crate.
///
/// The question is NOT "does this look like a type parameter" but "is this a VARIABLE
/// that [`walk_type`] collapses into one canonical identity KB-wide" — because that
/// collapse is exactly the conflation being repaired, so its set is exactly the set to
/// instantiate. Two spellings reach it and both answer here: a parameter already stored
/// as a `Var::Global` (an operation's bracket parameter, WI-1082's elaborated self
/// slot), and one written as its NAME (`T`, `List.T`), which the loader records against
/// its canonical variable through the WI-954 channel [`type_param_global_var`] reads.
///
/// A name with NO canonical variable — a namespace-level opaque `sort Term = ?` — is
/// `None`, and that is a real distinction rather than a miss: it denotes a rigid abstract
/// type, one thing for every reader, so nothing about it conflates and instantiating it
/// would DESTROY information. `walk_type` leaves it alone for the same reason.
///
/// A HIGHER-KINDED PARAMETER IN FUNCTOR POSITION (`M[T = A]`, where `M` is the `Monad`
/// spec's own parameter — `stdlib/anthill/prelude/delay.anthill` writes it) is likewise
/// `None`, and it is the one spelling this cannot reach. Raised by /code-review; the
/// answer is that there is nothing to reach: `Term::Fn`'s functor is a `Symbol`, not a
/// child term, so no variable is representable there — and `walk_type` does not collapse
/// it either (its `extract_sort_ref_sym` answers `None` for a parameterized type and it
/// returns the term unchanged), so the position never conflates in the first place. The
/// ARGUMENTS of such a type are ordinary children and ARE instantiated. Reaching the
/// functor would take a representation change, not a wider predicate here.
///
/// THE FUNCTOR OF A PARAMETERIZED TYPE IS NOT REACHED, and that is a representation limit
/// rather than an omission (found by /code-review). `Monad.flatMap(m: M[T = A], …)` writes
/// its own parameter `M` in the functor position of a `Term::Fn`, which holds a `Symbol`
/// — there is no term there for a variable to occupy, so a higher-kinded parameter cannot
/// be instantiated in this spelling at all. Nothing conflates through it either:
/// `walk_type` reaches its collapse only via `extract_sort_ref_sym`, which answers `None`
/// for anything parameterized, so `M` is left as itself on both paths. The type's
/// ARGUMENTS are ordinary types and are instantiated normally. Making the functor
/// instantiable is a change to `Term::Fn`, not to this function.
///
/// THE TWO CHANNELS AGREE, MEASURED rather than argued. `walk_type` decides "this name is
/// a variable" by `is_sort_param_symbol` plus a `resolve_sort_alias` target that IS a
/// `Var::Global`; this reads the WI-954 canonical map instead, which WI-954 made the
/// single channel precisely so that route would stop being re-derived. A name the first
/// test accepts and the map does not answer for would be a residual conflation, so it was
/// counted: instrumented across the whole `wi_tests` corpus (3151 tests, full stdlib plus
/// every fixture), ZERO names diverged.
pub(super) fn denoted_type_param_var(kb: &KnowledgeBase, t: TermId) -> Option<VarId> {
    match kb.get_term(t) {
        Term::Var(Var::Global(v)) => Some(*v),
        Term::Ref(sym) | Term::Ident(sym) => type_param_global_var(kb, *sym),
        // WI-359: a bare parameter name also surfaces as a nullary `Fn` — the third
        // spelling WI-359 records for a bare parameter name, for the same reason.
        Term::Fn {
            functor,
            pos_args,
            named_args,
        } if pos_args.is_empty() && named_args.is_empty() => type_param_global_var(kb, *functor),
        _ => None,
    }
}

/// WI-9C2PZ — does `t` mention anything [`instantiate_declared_term`] would rewrite?
///
/// A NON-ALLOCATING pre-scan, and it earns its place: the rewrite has to clone a `Fn`'s
/// argument vectors to release the `kb` borrow before recursing, so without this gate
/// every concrete parameter type in every rule-body call would pay a rebuild to produce
/// itself. Measured on a full stdlib load, the large majority of declared parameter /
/// field types mention no parameter at all (`String`, `Int64`, `List[Term]`).
fn declared_type_mentions_param(kb: &KnowledgeBase, t: TermId) -> bool {
    term_any_subterm(kb, t, &|t, _| denoted_type_param_var(kb, t).is_some())
}

/// WI-9C2PZ — the fresh variable `inst` stands `canonical` up as, minted on first use.
///
/// Named after the parameter it instantiates, so a diagnostic reading the resulting type
/// still says `?T` rather than an anonymous id.
fn instantiated_param_var(
    kb: &mut KnowledgeBase,
    canonical: VarId,
    inst: &mut ParamInstantiation,
) -> TermId {
    if let Some(t) = inst.get(&canonical.raw()) {
        return *t;
    }
    let v = kb.fresh_var(canonical.name());
    let t = kb.alloc(Term::Var(Var::Global(v)));
    inst.insert(canonical.raw(), t);
    t
}

/// WI-9C2PZ — [`instantiate_declared_type`]'s term half: rebuild `t` with every type
/// parameter it mentions replaced by this application's fresh variable for it.
fn instantiate_declared_term(
    kb: &mut KnowledgeBase,
    t: TermId,
    inst: &mut ParamInstantiation,
) -> TermId {
    if let Some(canonical) = denoted_type_param_var(kb, t) {
        return instantiated_param_var(kb, canonical, inst);
    }
    let Term::Fn {
        functor,
        pos_args,
        named_args,
    } = kb.get_term(t)
    else {
        return t;
    };
    let functor = *functor;
    let pos_args = pos_args.clone();
    let named_args = named_args.clone();
    let pos_args: SmallVec<[TermId; 4]> = pos_args
        .into_iter()
        .map(|a| instantiate_declared_term(kb, a, inst))
        .collect();
    let named_args: SmallVec<[(Symbol, TermId); 2]> = named_args
        .into_iter()
        .map(|(k, a)| (k, instantiate_declared_term(kb, a, inst)))
        .collect();
    kb.alloc(Term::Fn {
        functor,
        pos_args,
        named_args,
    })
}

/// WI-9C2PZ — a callee's declared parameter / field type with ITS OWN type parameters
/// instantiated by `inst`, so what this call site records is a type of something HERE.
///
/// WHAT WAS WRONG WITHOUT IT. [`collect_rule_var_types`] reads the declared type straight
/// out of the signature, and every written occurrence of one parameter denotes ONE
/// canonical variable KB-wide (WI-954). So every `eq` call in every rule in the KB
/// recorded the same `anthill.prelude.PartialEq.T` — for variables of unrelated types.
/// WI-741 made that survivable (a bare parameter neither displaces nor contradicts a
/// concrete type, and [`relation_clause_columns`] normalized it to a variable keyed BY
/// THE PARAMETER SYMBOL so column correlation survived) without touching the conflation
/// itself, which cost three things: two independent calls were treated as ONE correlation
/// class (`rule twoeq(?x, ?n) :- gen(?x, ?n), eq(?x, "a"), eq(?n, 1)` gave its two columns
/// one variable, so the CORRECT citation `twoeq("a", 1)` was refused); a variable forced
/// equal to a concrete one did not inherit its type; and which correlation class a
/// variable joined was decided by whichever parameter reached it first.
///
/// Instantiating per application retires all three at the producer, and retires WI-741's
/// two special cases with them: a per-call variable is an ordinary unification variable,
/// so [`constrain_vid`] can just unify. That unification is where `eq(?x, ?y), parent(of:
/// ?x, is: ?)` learns that BOTH variables are `String` — but it learns it into the
/// SUBSTITUTION, so the answer only reaches `var_types` because
/// [`collect_rule_var_types`] now resolves the map through it. The two halves are one
/// change and neither is separately correct; the measurement is at
/// `wi_9c2pz_per_application_type_params_test`'s control table.
///
/// The second half of the answer is WHETHER anything was instantiated — the gate on
/// [`constrain_literal_arg`]'s channel. It is threaded rather than re-derived by walking
/// the result for variables: the two questions have the same answer (after this runs, a
/// declared type carries a flexible variable exactly when this call minted one for it),
/// and only the threaded one says which question is being asked.
///
/// A `Value::Node` type carrier goes through the shared σ walk rather than the term
/// rebuild — the same [`crate::kb::node_occurrence::subst_value_type`] that
/// [`instantiate_poly_type`] freshens a ∀'s binders with, and for its reason: a
/// hand-rolled Node walk drifts from the σ every other rewriter uses.
///
/// NOTHING DRIVES THAT ARM, and saying so is better than letting the green suite imply
/// otherwise. Instrumented across the whole `wi_tests` corpus, a Node-carried declared
/// type reached here exactly TWICE, both times carrying zero variables — so both took the
/// early return and the freshening below has never run. Two bounds follow and neither is
/// a silent skip: the arm is written for the case rather than verified on it, and it
/// reaches the VARIABLE spelling ONLY — a parameter NAME nested inside a Node-carried type
/// (an arrow parameter's `S`, say) would not be reached, and would stay conflated as it is
/// today. Both become live together, when the WI-342 P4 producers start handing this
/// collector Node-carried parameterized types; the population to re-measure is this
/// counter.
pub(super) fn instantiate_declared_type(
    kb: &mut KnowledgeBase,
    ty: &Value,
    inst: &mut ParamInstantiation,
) -> (Value, bool) {
    if std::env::var("NO_INST_9C2PZ").is_ok() {
        return (ty.clone(), false);
    }
    match ty {
        Value::Term { id, .. } => {
            if !declared_type_mentions_param(kb, *id) {
                return (ty.clone(), false);
            }
            (Value::term(instantiate_declared_term(kb, *id, inst)), true)
        }
        _ => {
            let mut vars: Vec<VarId> = Vec::new();
            let mut seen = HashSet::new();
            crate::kb::node_occurrence::collect_value_type(kb, ty, &mut vars, &mut seen);
            if vars.is_empty() {
                return (ty.clone(), false);
            }
            let mut sigma = Substitution::new();
            for v in vars {
                let t = instantiated_param_var(kb, v, inst);
                sigma.bind_term(kb, v, t);
            }
            (
                crate::kb::node_occurrence::subst_value_type(kb, ty, &sigma).0,
                true,
            )
        }
    }
}

/// WI-9C2PZ — term-side twin of [`constrain_occ_arg_type`]: [`constrain_var_type`] for a
/// variable, plus the LITERAL channel. Kept in step with its occurrence sibling on
/// purpose — the two walkers ask the same question of the same declarations, and a
/// channel present in only one of them is exactly the drift the twinning exists to
/// prevent. Both delegate the literal half to [`constrain_literal_arg`], which states the
/// gate once.
pub(super) fn constrain_arg_type(
    kb: &mut KnowledgeBase,
    term: TermId,
    expected_type: &Value,
    instantiated: bool,
    var_types: &mut HashMap<u32, Value>,
    param_backed: &mut ParamBackedVars,
    subst: &mut Substitution,
) {
    if let Term::Const(lit) = kb.get_term(term) {
        let lit = lit.clone();
        constrain_literal_arg(kb, &lit, expected_type, instantiated, subst);
        return;
    }
    constrain_var_type(
        kb,
        term,
        expected_type,
        instantiated,
        var_types,
        param_backed,
        subst,
    );
}

/// If `term` is a variable, record that it should have `expected_type`.
/// If the variable already has a type, unify the two.
fn constrain_var_type(
    kb: &mut KnowledgeBase,
    term: TermId,
    expected_type: &Value,
    from_param: bool,
    var_types: &mut HashMap<u32, Value>,
    param_backed: &mut ParamBackedVars,
    subst: &mut Substitution,
) {
    let vid = match kb.get_term(term) {
        Term::Var(Var::Global(vid)) => vid.raw(),
        Term::Var(Var::DeBruijn(idx)) => *idx,
        _ => return,
    };
    constrain_vid(
        kb,
        vid,
        expected_type,
        from_param,
        var_types,
        param_backed,
        subst,
    );
}

/// Shared core of `constrain_var_type` / `constrain_occ_var_type`: record the
/// var's expected type, or unify against an existing one (keyed by the var's
/// raw id / De Bruijn idx — the same key space for a rule's head term and its
/// body occurrences, both closed against the same `vars`).
///
/// WI-9C2PZ — A PER-CALL PARAMETER IS A PLACEHOLDER, NOT A STATEMENT ABOUT THE VARIABLE,
/// and the two arms below are what that costs. Every position is UNIFIED now (WI-741's
/// "a bare parameter never unifies" arms are gone — they existed because the parameter
/// was one variable shared by every call in the KB, and [`instantiate_declared_type`]
/// removed that), but two things still turn on where a type came from:
///
///   * A DECLARED position TAKES OVER from a parameter placeholder. `var_types` answers
///     "what do this variable's own positions say", and a callee's parameter says
///     nothing — it is recorded so the correlation survives (`eq(?x, ?y)` puts both
///     variables on one variable), not as an answer.
///   * A DISAGREEMENT INVOLVING A PARAMETER IS THE CALL'S FAULT, NOT THE VARIABLE'S, so
///     it must NOT set `subst.contradiction`. That flag makes [`type_rule_bodies`] skip
///     the rule entirely — no dispatch, no WI-603 stamping, and for a namespace-level
///     rule no report at all — which SUPPRESSES the located error the ordinary call
///     check would raise. MEASURED, three shapes, all found by /code-review after the
///     first cut set the flag unconditionally:
///
///     | rule | before | first cut |
///     |---|---|---|
///     | `row(a: ?a, s: ?s), eq(?a, ?s)` | `eq.b (op-arg): expected Int64, got String` | LOADS CLEAN |
///     | `holder(f: ?f), eq(?f, 0)` | `eq.b (op-arg): expected Float, got Int64` | LOADS CLEAN |
///     | `eq(?x, "s"), scored(pts: ?x)` | `eq.b (op-arg): expected Int64, got String` | LOADS CLEAN |
///
///     The third is why the test is on the RECORD's provenance and not just on this
///     call's: the placeholder was pinned to `String` by a literal, and it is the
///     `scored` position arriving afterwards that must take over so the `eq` call is
///     still checked against `Int64`.
///
/// What still sets the flag is what always did and what nothing else reports: two
/// DECLARED positions of one variable that disagree (`parent(of: ?x, is: ?), scored(who:
/// ?, pts: ?x)`). Entity constructors in goal position are not calls, so no located check
/// covers them — measured, that shape loads clean at namespace level on both trees.
fn constrain_vid(
    kb: &mut KnowledgeBase,
    vid: u32,
    expected_type: &Value,
    from_param: bool,
    var_types: &mut HashMap<u32, Value>,
    param_backed: &mut ParamBackedVars,
    subst: &mut Substitution,
) {
    let Some(existing) = var_types.get(&vid).cloned() else {
        // Nothing known yet — record what this position says.
        var_types.insert(vid, expected_type.clone());
        if from_param {
            param_backed.insert(vid);
        }
        return;
    };
    let mut existing_from_param = param_backed.contains(&vid);
    let mut from_param = from_param;
    if std::env::var("FIRST_CUT_9C2PZ").is_ok() {
        existing_from_param = false;
        from_param = false;
    }
    // Unify either way: that is what binds a call's parameter to the variable's concrete
    // type, so a SIBLING argument of the same call inherits it.
    if !unify_types(kb, subst, &existing, expected_type) && !from_param && !existing_from_param {
        subst.contradiction = true;
    }
    // A declared position takes over from a placeholder — including when the two just
    // disagreed, because the declared type is what the variable is and recording it is
    // what leaves the offending CALL checkable.
    if !from_param && existing_from_param {
        var_types.insert(vid, expected_type.clone());
        param_backed.remove(&vid);
    }
}

/// WI-246: occurrence-body twin of [`collect_term_type_constraints`] — walk a
/// rule-body goal OCCURRENCE, constraining op-arg (positional) / entity-field
/// (named) var positions to their declared types. Mirrors the term walker's
/// op/entity functor dispatch and recursion, reading `Expr` instead of
/// `Term::Fn` so the typer no longer reads the term body. Control-flow / reflect
/// forms add no constraints themselves but are recursed into via their children.
///
/// Reflect-data forms carry their sub-pattern / param / type-annotation as
/// `TermId` fields (not occ children), which `for_each_child` does not
/// enumerate. They are closed to the rule's De Bruijn space by
/// `node_to_debruijn`, so we type-check them via the term collector — covering
/// op/entity calls nested in a pattern/param exactly as the term walker did.
pub(super) fn collect_occurrence_type_constraints(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    var_types: &mut HashMap<u32, Value>,
    param_backed: &mut ParamBackedVars,
    subst: &mut Substitution,
) {
    // WI-298: descend into Pattern children so a var living in a pattern's
    // nested type-annotation Expr leaf gets the same op-arg / entity-field
    // constraint walk applied to the rest of the rule. Symmetric with
    // `node_to_debruijn` and `collect_occurrence_global_vars_ordered`.
    if occ.as_pattern().is_some() {
        for_each_pattern_child(occ, |c| {
            collect_occurrence_type_constraints(kb, c, var_types, param_backed, subst)
        });
        return;
    }
    let Some(expr) = occ.as_expr() else { return };
    match expr {
        Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        } => {
            constrain_application(
                kb,
                *functor,
                pos_args,
                named_args,
                var_types,
                param_backed,
                subst,
            );
        }
        Expr::Constructor {
            name,
            pos_args,
            named_args,
            ..
        }
        | Expr::Instantiation {
            name,
            pos_args,
            named_args,
        } => {
            constrain_application(
                kb,
                *name,
                pos_args,
                named_args,
                var_types,
                param_backed,
                subst,
            );
        }
        // WI-819: `Expr::Let` no longer has a type-positional field. Its
        // annotation is an Expr-kind child of the PATTERN occurrence, and the
        // pattern arm at the top of this function already descends into it — so
        // a ground annotation's nested op/entity calls are constrained through
        // the SAME recursion, not a parallel term-collector call.
        // WI-318: Lambda / LambdaWithin params AND MatchBranch.pattern
        // are now Pattern-kind occurrences walked by `for_each_child`
        // below. Any nested TermId-typed children (e.g. a Var pattern's
        // type_ann Expr-kind occurrence) are reached via that recursion;
        // no explicit term-level call needed here.
        _ => {}
    }
    for_each_child(expr, |c| {
        collect_occurrence_type_constraints(kb, c, var_types, param_backed, subst)
    });
}

/// Constrain the op-arg (positional) / entity-field (named) var positions of one
/// applied occurrence — the occurrence analog of the op/entity dispatch in
/// [`collect_term_type_constraints`].
fn constrain_application(
    kb: &mut KnowledgeBase,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
    var_types: &mut HashMap<u32, Value>,
    param_backed: &mut ParamBackedVars,
    subst: &mut Substitution,
) {
    // WI-9C2PZ: ONE [`ParamInstantiation`] per application — see
    // [`instantiate_declared_type`].
    let mut inst = ParamInstantiation::new();
    if let Some(op) = lookup_operation_info_full(kb, functor) {
        for (i, arg) in pos_args.iter().enumerate() {
            // WI-341 Stage A: seed inference from the param type carrier-agnostically.
            if let Some((_, param_type)) = op.params.get(i) {
                let (param_type, instantiated) =
                    instantiate_declared_type(kb, param_type, &mut inst);
                constrain_occ_arg_type(
                    kb,
                    arg,
                    &param_type,
                    instantiated,
                    var_types,
                    param_backed,
                    subst,
                );
            }
        }
    } else if let Some(field_types) = kb.entity_field_types(functor) {
        let field_types = field_types.to_vec();
        for (field_sym, field_type) in &field_types {
            if let Some((_, arg)) = named_args.iter().find(|(s, _)| s == field_sym) {
                // WI-341 Stage A: field type is a carrier-agnostic `Value` —
                // constrain directly, no re-grounding to a term.
                let (field_type, instantiated) =
                    instantiate_declared_type(kb, field_type, &mut inst);
                constrain_occ_arg_type(
                    kb,
                    arg,
                    &field_type,
                    instantiated,
                    var_types,
                    param_backed,
                    subst,
                );
            }
        }
    }
}

/// WI-9C2PZ — constrain one applied ARGUMENT position: [`constrain_occ_var_type`] for a
/// variable, plus the LITERAL channel a variable position does not need.
///
/// A literal argument is not a variable, so it recorded nothing at all — and for a
/// parameter that is the difference between knowing the parameter's type and never
/// knowing it. `rule twoeq(?x, ?n) :- gen(?x, ?n), eq(?x, "a"), eq(?n, 1)` has no other
/// typing source for either column (a rule subgoal types nothing), so without this the
/// two columns instantiate to two unconstrained variables — independent, which is the
/// repair, but also untyped, so `twoeq(1, "a")` would be accepted as readily as
/// `twoeq("a", 1)`. Reading the literal makes the columns `String` and `Int64`.
///
/// GATED ON `expected` MENTIONING A VARIABLE, deliberately, and the gate is not caution
/// but scope: against a CONCRETE parameter an argument's own type is the ordinary
/// type-check's business, which this pre-pass has no standing to re-decide (and could
/// not, for anything but a literal — every other argument shape still contributes
/// nothing here). Against an INSTANTIATED one this pre-pass owns the only channel that
/// says what the parameter is. Ungated it would also start manufacturing refusals in
/// reflect-shaped code, where a `Bool` literal in a `Term` slot is ordinary.
fn constrain_occ_arg_type(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    expected_type: &Value,
    instantiated: bool,
    var_types: &mut HashMap<u32, Value>,
    param_backed: &mut ParamBackedVars,
    subst: &mut Substitution,
) {
    if let Some(Expr::Const(lit)) = occ.as_expr() {
        let lit = lit.clone();
        constrain_literal_arg(kb, &lit, expected_type, instantiated, subst);
        return;
    }
    constrain_occ_var_type(
        kb,
        occ,
        expected_type,
        instantiated,
        var_types,
        param_backed,
        subst,
    );
}

/// WI-9C2PZ — the LITERAL channel itself, one copy for both walkers so the gate that
/// scopes it cannot come to mean two things. Pins `expected_type` to the literal's own
/// sort, and a disagreement is a genuine contradiction in the rule.
///
/// `instantiated` is that gate: the literal is read ONLY into a parameter THIS application
/// just instantiated. That is scope, not caution — against a concrete parameter an
/// argument's type is the ordinary type-check's business, which this pre-pass has no
/// standing to re-decide (and could not, for anything but a literal); against an
/// instantiated one this pre-pass owns the only channel that says what the parameter is.
/// Ungated it would also start manufacturing refusals in reflect-shaped code, where a
/// `Bool` literal in a `Term` slot is ordinary.
fn constrain_literal_arg(
    kb: &mut KnowledgeBase,
    lit: &Literal,
    expected_type: &Value,
    instantiated: bool,
    subst: &mut Substitution,
) {
    if !instantiated || std::env::var("NO_LITERAL_9C2PZ").is_ok() {
        return;
    }
    // A DISAGREEMENT HERE IS NOT RECORDED as a rule-wide contradiction — see
    // [`constrain_vid`], whose table's second row is exactly this shape. `eq(?f, 0)`
    // beside `holder(f: Float)` is an argument error at the `eq` call, which the ordinary
    // call check reports at the literal's own span; flagging the rule would skip that
    // check and lose it. The failed unification simply pins nothing.
    let lit_type = literal_sort(kb, lit);
    let ok = unify_types(kb, subst, expected_type, &lit_type);
    if !ok && std::env::var("FIRST_CUT_9C2PZ").is_ok() {
        subst.contradiction = true;
    }
}

/// Occurrence analog of [`constrain_var_type`]: if `occ` is a var leaf, record /
/// unify its expected type.
fn constrain_occ_var_type(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    expected_type: &Value,
    from_param: bool,
    var_types: &mut HashMap<u32, Value>,
    param_backed: &mut ParamBackedVars,
    subst: &mut Substitution,
) {
    let vid = match occ.as_expr() {
        Some(Expr::Var(Var::Global(vid))) => vid.raw(),
        Some(Expr::Var(Var::DeBruijn(idx))) => *idx,
        _ => return,
    };
    constrain_vid(
        kb,
        vid,
        expected_type,
        from_param,
        var_types,
        param_backed,
        subst,
    );
}

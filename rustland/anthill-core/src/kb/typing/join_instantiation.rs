//! WI-20260926-NEKR0 — a type parameter bound by several arguments takes their JOIN
//! (kernel-language §8.1, *A type parameter bound by several arguments takes their join*).
//!
//! Every call site used to pin an operation's own `[A]` by unifying its parameters in
//! PARAMETER ORDER, so the first argument decided `A` and every later one had to be its
//! subtype: `cmp2[A](x: A, y: A)` loaded as `cmp2(s, c)` and was refused as `cmp2(c, s)`
//! (`Circle provides Shape`). The collection literal had the same order-dependence and closed
//! it with the join (WI-20260829-WBXGX); this is that relation asked of a call.
//!
//! ONE OWNER, asked BEFORE each site's own pinning loop: the operation-body call
//! (`check_apply_iter`), the lambda-binder hint (`hint_instantiation_into`), a rule
//! citation's column typing (`relation_reference_type_applied`) and the rule-body slot route
//! (`op_slot_route`). Each then pins and checks as before, against a σ that already holds the
//! join — so the per-argument conformance check (`validate_arg_against_param`) is what judges
//! the occurrences that contributed nothing, and the four cannot disagree about `A`.

use super::*;

/// How an occurrence of a variable may relate to the argument standing opposite it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Polarity {
    /// The argument may be a SUBTYPE of the instantiation — it contributes to the join.
    Covariant,
    /// The argument must BE the instantiation — it fixes the variable outright.
    Invariant,
}

/// The types the arguments give each candidate variable, at its covariant and invariant
/// occurrences: `(variable, parameter, polarity, type)`.
type Contributions = Vec<(VarId, Symbol, Polarity, Value)>;

/// Collect, from one (declared parameter type, argument type) pair, what each candidate
/// variable receives, and at which polarity. The parameter type IS the variable, or the
/// variable sits in an arrow's RESULT, or under a sort parameter declared `Covariant` of a
/// sort both sides apply: covariant. Under a sort parameter with no declared
/// variance — invariant — it is invariant, and so is everything beneath it. A callback's
/// PARAMETER (contravariant, like a `Contravariant` sort parameter) and a bivariant sort
/// parameter contribute nothing:
/// neither widening nor fixing `A` from it is sound, so it is CHECKED against the result
/// afterwards, by the site's own conformance loop.
///
/// A head the two sides do not share contributes nothing either: the argument is then some
/// subtype or conversion of the parameter, and deciding what it gives `A` would be a second
/// opinion about a relation `validate_arg_against_param` already owns.
#[allow(clippy::too_many_arguments)]
fn collect(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    // `None`: every variable still free in σ is one (a citation).
    candidates: Option<&[(Symbol, VarId)]>,
    param: Symbol,
    polarity: Polarity,
    declared: &Value,
    actual: &Value,
    out: &mut Contributions,
    opaque: &mut Vec<VarId>,
) {
    let d = walk_view(kb, subst, declared);
    if let Some(vid) = resolved_var(kb, &d) {
        let wanted = match candidates {
            Some(c) => c.iter().any(|(_, v)| *v == vid),
            None => true,
        };
        if wanted {
            let ty = walk_type_deep_value(kb, subst, actual);
            out.push((vid, param, polarity, ty));
        }
        return;
    }
    let a = walk_view(kb, subst, actual);
    if let (Some((d_base, d_bindings)), Some((a_base, a_bindings))) =
        (nominal_head_parts(kb, &d), nominal_head_parts(kb, &a))
    {
        if !same_sort_canonical(kb, d_base, a_base) {
            mark_opaque(kb, subst, &d, opaque);
            return;
        }
        for (label, dv) in &d_bindings {
            // A BIVARIANT (phantom) parameter relates nothing — any two instances conform — so,
            // like a contravariant one, it neither contributes nor fixes: `f[A](x: A, t: Tag[T =
            // A])` given an `Int64` and a `Tag[T = String]` is `A = Int64`, as it always was.
            let inner = match declared_variance(kb, d_base, *label) {
                Variance::Covariant => polarity,
                Variance::Invariant => Polarity::Invariant,
                Variance::Contravariant | Variance::Bivariant => continue,
            };
            if let Some((_, av)) = a_bindings.iter().find(|(l, _)| same_label(kb, *l, *label)) {
                collect(kb, subst, candidates, param, inner, dv, av, out, opaque);
            }
        }
        return;
    }
    if let (Some((_, d_result, _)), Some((_, a_result, _))) = (arrow_parts(kb, &d), arrow_parts(kb, &a)) {
        collect(kb, subst, candidates, param, polarity, &d_result, &a_result, out, opaque);
        return;
    }
    if resolved_var(kb, &a).is_none() {
        mark_opaque(kb, subst, &d, opaque);
    }
}

/// THE ARGUMENT RELATES TO THE PARAMETER THROUGH SOMETHING THIS PASS DOES NOT READ — a
/// provision (`List[T = Shape]` for `s: Stream[T = A]`), a conversion, a subtype with another
/// head — so what it gives each variable in `declared` is not known here. Every such variable
/// is left to the site's own pinning, which reads that relation, exactly as before the join
/// existed: instantiating it from its other arguments first would decide it without the one
/// that may fix it (`push[A](s: Stream[T = A], x: A)` given a `List[T = Shape]` and a `Circle`
/// would take `A = Circle` and refuse the list).
fn mark_opaque(kb: &mut KnowledgeBase, subst: &Substitution, declared: &Value, opaque: &mut Vec<VarId>) {
    let deep = walk_type_deep_value(kb, subst, declared);
    let mut seen = HashSet::new();
    crate::kb::node_occurrence::collect_value_type(kb, &deep, opaque, &mut seen);
}

/// WI-20261001-80ZV8 (user, 2026-10-04: "we have this decision for list constants, so yes") —
/// A SORT'S PARAMETER SEVERAL ARGUMENTS BIND IS INSTANTIATED AS AN OPERATION'S OWN `[A]` IS
/// ([`join_repeated_type_params`]): at an invariant occurrence where there is one, else at the
/// join of the covariant ones. A sort's parameters are type parameters of its operations and
/// of its constructors (proposal 070 §1.1).
///
/// A call used to let the FIRST argument naming the sort's parameter decide it — the receiver,
/// through its carrier (`bind_spec_params_from_carrier`), or a constructor's first field — and
/// held every later one to that (each MEASURED):
///
/// * `List.append([1], acc)` loaded over a list of nothing `acc`, and `List.append(acc, [1])`
///   was refused, `expected List[T = nothing], got List[T = Int64]`;
/// * over an INVARIANT `Stack`, `push(top: c, rest: shapes)` — a `Circle` on a `Stack[T =
///   Shape]` — was refused, `push.rest: expected Stack[T = Circle], got Stack[T = Shape]`,
///   and `Stack.put(c, shapes)` with it, where `put2(shapes, c)` loaded.
///
/// Asked BEFORE the receiver binds, which fills only what is still free.
///
/// WHERE THERE IS NO JOIN, NOTHING IS BOUND — and that is not a silent skip. The call's own
/// loop then lets the first argument decide, exactly as before, and refuses the argument that
/// disagrees with the message it always had (`cons.tail (entity-field): expected List[T =
/// String], got List[T = Int64]`), which names the argument; a "no common type" refusal here
/// would say less and reword every such row. So this only ever ADMITS: a program that loaded
/// before has every later argument a subtype of the first, whose type is then the join, or
/// equal to it where the occurrence is invariant.
///
/// WHAT A REFUSAL NAMES DOES MOVE, where an invariant occurrence comes after a covariant one:
/// the invariant one says the parameter, so the covariant argument is the one that does not
/// fit. `mcons(head: 1, tail: strings)` over an invariant `MyList` is refused `mcons.head:
/// expected String, got Int64`, where the head used to decide and the tail was refused.
///
/// EACH PARAMETER BY ITSELF, so that one with no join does not keep another from its own. A
/// single candidate is bound only when its instantiation succeeds, which is what makes
/// dropping the refusal safe: nothing was written into σ on the way to it.
///
/// OF A DATA SORT ONLY — every site asks [`sort_params_join`] first.
///
/// AT THE OPERATION-BODY CALL, AT A CONSTRUCTOR, AND IN THE HINT A LAMBDA ARGUMENT IS TYPED
/// FROM (`check_apply_iter`, `check_constructor_iter`, `join_sort_params_for_hint`) — the
/// hint has to carry the instantiation the call will check the lambda against. A rule
/// citation's columns join every variable they share already ([`JoinCandidates::AnyFree`];
/// MEASURED: `via(c, s)` and `via(s, c)` both load over `rule via(?a, ?b, ?c) :-
/// Stack.pick2(?a, ?b, ?c)`). The rule-body slot route (`op_slot_route`) still pins a SORT
/// parameter in argument order; no program reaching it with two arguments that differ was
/// found — a goal over a sort that `requires` something of its parameter is refused before
/// it, where the clause declares no `require[…]`.
pub(super) fn join_repeated_sort_params(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    sort: Symbol,
    pairs: &[(Symbol, &Value, &Value)],
) {
    if pairs.len() < 2 {
        return;
    }
    let params: SmallVec<[(Symbol, Var); 2]> = sort_type_params_as_pairs(kb, sort)
        .iter()
        .filter_map(|(name, canonical)| match kb.get_term(*canonical) {
            Term::Var(var @ Var::Global(_)) => Some((*name, *var)),
            _ => None,
        })
        .collect();
    for param in &params {
        let _no_join_is_the_call_sites_to_report = join_repeated_type_params(
            kb,
            subst,
            JoinCandidates::TypeParams(std::slice::from_ref(param)),
            pairs,
        );
    }
}

/// DOES A CALL INTO `sort` INSTANTIATE ITS PARAMETERS BY [`join_repeated_sort_params`] — is
/// it a DATA sort, and has it a parameter? The one gate of the three sites that ask.
///
/// A data sort declares a constructor, and nothing can provide one (`ProvidesNamesDataSort`),
/// so its parameters are type parameters of its operations and nothing else. A SPEC's are a
/// provision's: a call reads them off the receiver's carrier or off the enclosing `requires`
/// clause, and the provider that then runs is the receiver's — `Cmp.cmp(c, s)` joined at `T =
/// Shape` would hand a `Shape` to the `cmp` that `Circle` provides at `T = Circle`. Whether
/// anything provides the spec YET is not the question: asked that way, a call licensed by
/// `requires Cmp[T = Circle]` loaded with a `Shape` at `T` while no provider of `Cmp` existed,
/// and a provision declared elsewhere then refused it (MEASURED).
///
/// Read off the sort → constructors index, complete once every sort body has loaded, which
/// the typer runs after; `KnowledgeBase::sort_has_constructors` answers the same question
/// DURING the load, by a scan of the symbol table no call site could afford.
pub(super) fn sort_params_join(kb: &KnowledgeBase, sort: Symbol) -> bool {
    !kb.sort_children(sort).is_empty() && !sort_type_params_as_pairs(kb, sort).is_empty()
}

/// Which variables the join instantiates.
pub(super) enum JoinCandidates<'a> {
    /// An operation's own `[A]`s — a call site.
    TypeParams(&'a [(Symbol, Var)]),
    /// Every variable still free in σ — a rule CITATION, whose columns share a rule-scoped
    /// variable (`rule via(?a, ?b, ?c) :- cmp2(?a, ?b, ?c)` types `a` and `b` at one) rather
    /// than a declared parameter. The variables are this citation's own: the loop that pins
    /// them threads a σ local to it.
    AnyFree,
}

/// A variable whose covariant contributions have NO join — `same(1, "a")`.
pub(super) struct NoJoin {
    /// The type parameter's written name; `None` for a citation's column variable, which has
    /// none.
    pub type_param: Option<Symbol>,
    /// Each contribution in argument order: the parameter or column it came through, and its
    /// type.
    pub contributions: Vec<(Symbol, Value)>,
}

impl NoJoin {
    /// `Int64 (x), String (y)` — each contribution and where it came from.
    pub(super) fn listed(&self, kb: &KnowledgeBase) -> String {
        self.contributions
            .iter()
            .map(|(p, ty)| format!("{} ({})", type_display_name_value(kb, ty), kb.local_name_of(*p)))
            .collect::<Vec<_>>()
            .join(", ")
    }

    /// The refusal of a CALL, at its span. `OperationTypeParams` is the context WI-374's
    /// parametricity-tie refusal already uses for "the arguments bind one parameter
    /// inconsistently", which is what this is.
    pub(super) fn into_call_error(self, kb: &KnowledgeBase, op: Symbol, span: Option<Span>) -> TypeError {
        let name = self.type_param.map(|s| kb.local_name_of(s).to_string()).unwrap_or_default();
        TypeError::Other {
            site: TypeError::here(),
            span,
            context: TypeErrorContext::OperationTypeParams { op_name: op },
            expected: format!("one type for `{name}`: the join of the arguments that bind it"),
            actual: format!(
                "no common type for type parameter `{name}` of `{}`: {}",
                kb.local_name_of(op),
                self.listed(kb)
            ),
        }
    }
}

/// Bind each candidate variable still FREE in `subst` that some argument contributes a
/// DETERMINED type to: at an INVARIANT argument's type where there is one (the others are then
/// checked against it), else at the join of the COVARIANT ones ([`join_types`], the
/// `if`/`match` arm and collection-literal join). A parameter the site already fixed — an explicit `op[A = …]`
/// bracket, a receiver, the caller's `requires` — is not a candidate: what was written or
/// inherited wins, and the site's conformance check judges the arguments against it exactly
/// as before.
///
/// A contribution that is not yet determined (a flexible variable, an un-annotated lambda's
/// binder) is left to the site's own unification. ONE contribution is bound too, although the
/// join is then that type: otherwise an occurrence that contributes nothing but comes FIRST —
/// `apply2[A](f: (v: A) -> Int64, x: A)` — still pins `A` from the callback's parameter, and the
/// call stays order-dependent.
///
/// `pairs` is `(parameter or column, declared type, argument type)` for every argument the
/// site typed.
pub(super) fn join_repeated_type_params(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    candidates: JoinCandidates<'_>,
    pairs: &[(Symbol, &Value, &Value)],
) -> Result<(), NoJoin> {
    let is_free = |kb: &KnowledgeBase, subst: &Substitution, vid: VarId| {
        resolved_var(kb, &walk_view(kb, subst, &Value::Var(Var::Global(vid)))) == Some(vid)
    };
    let named: Option<Vec<(Symbol, VarId)>> = match candidates {
        JoinCandidates::TypeParams(tps) => Some(
            tps.iter()
                .filter_map(|(n, v)| match v {
                    Var::Global(vid) if is_free(kb, subst, *vid) => Some((*n, *vid)),
                    _ => None,
                })
                .collect(),
        ),
        JoinCandidates::AnyFree => None,
    };
    if named.as_ref().is_some_and(|n| n.is_empty()) {
        return Ok(());
    }
    let mut contributions = Contributions::new();
    let mut opaque: Vec<VarId> = Vec::new();
    for (param, declared, actual) in pairs {
        collect(
            kb,
            subst,
            named.as_deref(),
            *param,
            Polarity::Covariant,
            declared,
            actual,
            &mut contributions,
            &mut opaque,
        );
    }
    // Each variable once, in the order its first contribution was met.
    let mut order: Vec<(Option<Symbol>, VarId)> = Vec::new();
    for (vid, _, _, _) in &contributions {
        if !order.iter().any(|(_, v)| v == vid) {
            let name = named.as_ref().and_then(|n| n.iter().find(|(_, v)| v == vid).map(|(s, _)| *s));
            order.push((name, *vid));
        }
    }
    for (name, vid) in order {
        if opaque.contains(&vid) {
            continue;
        }
        let determined = |kb: &KnowledgeBase, pol: Polarity| -> Vec<(Symbol, Value)> {
            contributions
                .iter()
                .filter(|(v, _, p, ty)| *v == vid && *p == pol && resolved_type_is_determined(kb, ty))
                .map(|(_, p, _, ty)| (*p, ty.clone()))
                .collect()
        };
        // AN INVARIANT OCCURRENCE FIXES THE VARIABLE, and the covariant arguments are then
        // checked against it: `put[A](b: Box[T = A], y: A)` given a `Box[T = Shape]` and a
        // `Circle` is `A = Shape`, which the `Circle` conforms to — the join of the covariant
        // arguments alone (`Circle`) would refuse the box. Invariant occurrences that DISAGREE
        // fix nothing here; the site's own checks refuse them, as they always did.
        let invariant = determined(kb, Polarity::Invariant);
        if let Some((_, first)) = invariant.first() {
            let first = first.clone();
            let mut agree = true;
            for (_, ty) in &invariant[1..] {
                agree &= types_equivalent(kb, &first, ty);
            }
            if agree {
                bind_resolved(kb, subst, vid, first);
            }
            continue;
        }
        let mine = determined(kb, Polarity::Covariant);
        let Some((_, first)) = mine.first() else { continue };
        let mut acc = first.clone();
        for (_, ty) in &mine[1..] {
            match join_types(kb, acc, ty.clone()) {
                Some(j) => acc = j,
                None => {
                    return Err(NoJoin {
                        type_param: name,
                        contributions: mine,
                    })
                }
            }
        }
        bind_resolved(kb, subst, vid, acc);
    }
    Ok(())
}

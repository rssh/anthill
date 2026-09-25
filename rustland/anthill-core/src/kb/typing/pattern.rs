//! Pattern env extension: binding and labelling pattern variables, and operation-info
//! lookups.

use super::*;

// ── Pattern env extension ──────────────────────────────────────

/// Build a `Substitution` from a `parameterized(base, bindings)` type
/// for a constructor pattern's field types: each scrutinee binding's
/// param symbol maps to the type-param `Var(Global)` registered for
/// `parent_sort`, bound to the binding's value type. So
/// `case some(name)` over `Option[T = String]` resolves `some.value`'s
/// declared type to `String`, binding `name: String`.
///
/// Lookup is scoped to `parent_sort` via [`type_param_vid_in_sort`];
/// short-name resolution is ambiguous when many sorts declare
/// `sort T = ?`.
pub(super) fn build_pattern_subst(
    kb: &KnowledgeBase,
    scrutinee_type: &impl TermView,
    parent_sort: Symbol,
) -> Option<Substitution> {
    // WI-361: read the bindings form-agnostically — deep `parameterized(base,
    // bindings)` or term-backed `Fn{S, named}`. A non-parameterized scrutinee
    // (bare sort, arrow, …) yields no pattern subst. WI-342: carrier-agnostic
    // over [`TermView`] so a `Value::Node` scrutinee builds the subst too.
    let TypeExtractor::Parameterized { bindings, .. } = extract_type(kb, scrutinee_type) else {
        return None;
    };

    let mut subst = Substitution::new();
    let mut any = false;
    for (param, value) in &bindings {
        if let Some(vid) = type_param_vid_in_sort(kb, parent_sort, *param) {
            // WI-342: bind the type-param value carrier-agnostically (`bind_value`),
            // so a `Value::Node` (denoted-bearing) type-param is preserved rather
            // than re-grounded. `walk_type_value` resolves a field type through this
            // binding via `resolve_as_value` (it may surface the Node); a ground
            // `Value::Term` binding is still read by `walk_type` (which narrows
            // to `Value::Term`).
            subst.bind_value(kb, vid, value.clone());
            any = true;
        }
    }
    if any {
        Some(subst)
    } else {
        None
    }
}

/// WI-424 — a parametric sort's declared type parameters as `(param symbol,
/// canonical Var term)` pairs, source order — the same shape an operation's own
/// `type_params` take, so [`rigidify_op_type_params`] consumes either. Empty for a
/// non-sort or non-parametric `sort_sym`. Memoized on `kb.sort_param_pairs_cache`
/// because it is consulted per apply call site (receiver classification) and per eval
/// dispatch.
///
/// WI-954 — TWO MAP READS, and the `filter_map` is no longer a filter on anything.
/// This used to rebuild `<sort qn>.<param>` per parameter, re-resolve it globally, and
/// then chase its `SortAlias`, dropping any parameter whose alias was not a plain
/// `Var::Global` — a case that never arose (`add_type_param` is gated on
/// `TypeExpr::Variable`, so a declared parameter's alias IS a variable) and which the
/// loader now refuses outright. Both halves come straight from the declaration:
/// [`KnowledgeBase::type_param_syms_of`] for the parameters in source order,
/// [`KnowledgeBase::canonical_type_param_var`] for each one's variable.
///
/// ITS DOMAIN WIDENED, deliberately and without a gate. Passed an OPERATION symbol this
/// used to answer empty — a bracket parameter has no `SortAlias` for the old route to
/// chase — and now answers that operation's bracket parameters. That is coherent with
/// what this function is for (the doc above: "the same shape an operation's own
/// `type_params` take"), and adding a kind gate to preserve the old emptiness would be
/// a new rule with nothing asking for it. Every production caller passes a SORT or a
/// namespace; the one that could see the difference is `sort_application_parts`, whose
/// two branches produce the same `Some((sym, vec![]))` either way.
pub(super) fn sort_type_params_as_pairs(
    kb: &KnowledgeBase,
    sort_sym: Symbol,
) -> Rc<Vec<(Symbol, TermId)>> {
    if let Some(cached) = kb.sort_param_pairs_cache.borrow().get(&sort_sym) {
        return cached.clone();
    }
    let pairs: Vec<(Symbol, TermId)> = kb
        .type_param_syms_of(sort_sym)
        .iter()
        .filter_map(|&param| Some((param, published_param_var(kb, sort_sym, param)?)))
        .collect();
    let rc = Rc::new(pairs);
    kb.sort_param_pairs_cache
        .borrow_mut()
        .insert(sort_sym, rc.clone());
    rc
}

/// [`sort_type_params_as_pairs`]' pairs with each variable as the `Var` it is — the shape
/// [`rigidify_op_type_params`] takes. TOTAL, because that function admits an entry only
/// when it IS a `Term::Var(Global)` (WI-849: the op table is `Var`-typed, the sort table
/// still `TermId`-typed); a non-var would mean that filter changed under us.
pub(super) fn param_pairs_as_vars(
    kb: &KnowledgeBase,
    pairs: &[(Symbol, TermId)],
) -> Vec<(Symbol, Var)> {
    pairs
        .iter()
        .map(|(n, t)| match kb.get_term(*t) {
            Term::Var(v) => (*n, *v),
            other => unreachable!(
                "sort_type_params_as_pairs admits only `Term::Var(Global)`, got {other:?}"
            ),
        })
        .collect()
}

/// WI-954 — the canonical variable of a parameter its OWNER has declared, with the
/// miss made LOUD. The two readers that enumerate `type_param_syms_of` and then look
/// each entry up ([`sort_type_params_as_pairs`], [`reconstruct_sort_params`]) would
/// otherwise drop a parameter silently, and dropping one is exactly what WI-384 says
/// must never happen — the built type would carry fewer named args than the sort
/// declares.
///
/// THE TWO GATES ARE NOT THE SAME PREDICATE, which is why this can miss at all.
/// Publication (`load`'s `assert_sort_alias`) is gated on [`is_sort_param_symbol`] —
/// the parameter's own DECLARING scope — while these readers enumerate the OWNER's
/// scope. They coincide because three of the four `add_type_param` sites register into
/// the scope the symbol was defined in; the `Item::AbstractSort` arm does not, since a
/// DOTTED `sort a.b.T = ?` written in a sort body defines `T` into the namespace
/// `ensure_intermediate_namespaces` made and registers it on the SORT. What that
/// spelling should mean is a separate question; this makes sure it cannot be answered
/// by quietly losing the parameter.
///
/// LATENT, NOT LIVE: the assertion does not fire anywhere in the workspace suite
/// (measured — 29 binaries, 4441 tests), so no corpus program writes that shape. It is
/// here because the divergence is reachable in principle and its symptom — a built type
/// with fewer named args than the sort declares — is silent by nature.
pub(super) fn published_param_var(
    kb: &KnowledgeBase,
    owner: Symbol,
    param: Symbol,
) -> Option<TermId> {
    let published = kb.canonical_type_param_var(param);
    debug_assert!(
        published.is_some(),
        "WI-954: `{}` declares `{}` as a type parameter but no canonical variable was \
         published for it — the type built for `{0}` would silently lose the parameter",
        kb.qualified_name_of(owner),
        kb.qualified_name_of(param),
    );
    published
}

/// The canonical `Var::Global` `parent_sort` declares for the parameter NAMED by
/// `param_sym` (a bare `T` off a binding key, or a qualified one). The resolution
/// itself is [`type_param_global_var`] — the same one the σ-class side uses, so a
/// carrier grounded here and a requirement attributed there speak of one variable.
///
/// Anchoring to `parent_sort` is what makes it hygienic: `sort T = ?` recurs across
/// List, Option, Stream …, so a name alone identifies nothing. WI-954 —
/// [`KnowledgeBase::type_param_sym_of`] anchors it by asking the OWNER for its own
/// declared parameters, where the pre-WI-954 spelling rebuilt `<parent qn>.<name>` and
/// re-resolved it against the whole table.
pub(super) fn type_param_vid_in_sort(
    kb: &KnowledgeBase,
    parent_sort: Symbol,
    param_sym: Symbol,
) -> Option<crate::kb::term::VarId> {
    let declared = kb.type_param_sym_of(parent_sort, kb.local_name_of(param_sym))?;
    type_param_global_var(kb, declared)
}

/// WI-20260827-EJ5F5 — what a pattern is being asked to do, which decides whether a bare
/// name in it is a CONSTRUCTOR or a BINDER.
///
/// The two are genuinely different questions and only the writing position separates
/// them, since the kernel spells a pattern binder as a bare identifier (`pattern_var` in
/// `grammar.js`) and spells a nullary constructor the same way.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum PatternRole {
    /// A `match` arm — REFUTABLE, so a bare name that names one of the position's own
    /// nullary constructors is that constructor (kernel-language.md, "Constructor
    /// patterns resolve against the scrutinee, not the scope").
    MatchArm,
    /// A `let` or `lambda` binder — IRREFUTABLE by construction, so every bare name is a
    /// binder however the surrounding scope spells its constructors. Rewriting one would
    /// turn a total binding into a partial match that fails at run time.
    Binder,
}

/// WI-20260904-50B2K — WHAT AN ABSENT TYPE AT A SUB-PATTERN POSITION MEANS, which is the
/// one thing that decides what a binder with no type mints.
///
/// [`bind_and_label_pattern`] reaches its fallback whenever no type threads into a
/// binder's slot, and until now it minted the same inert `type_var` for BOTH reasons an
/// absence can have. That is the conflation this ticket separates one level up, found one
/// level down, and it was MEASURED: flipping the fallback wholesale to the engine's own
/// variable failed four rows, all `match s case SetLiteral(a, _, _) -> a` over a
/// `Set[T = Int64]`, with "expected Int64, got ??pat".
///
/// The two questions, and why the answer differs:
///
///   * `Unnameable` — the DECLARATION is what is missing. `SetLiteral` is a parse-level
///     marker with no declared field types, so its sub-patterns arrive with no context
///     type and NOTHING CAN EVER PIN THEM. An inference variable here stays unsolved
///     forever and reaches a conformance check unbound, which is a fail-open; the inert
///     form is structurally ground, so the check runs and compatible-with-anything is
///     exactly the M6 flounder posture `make_type_var` documents.
///   * `ToBeInferred` — a type EXISTS one level up and is itself a hole. `lambda (a, b)`
///     whose param type is rung 3's fresh variable is the case: the components are
///     precisely what inference must solve, and inference must COMMIT.
///
/// Not derivable at the fallback itself — it is a property of the PARENT, and by then the
/// parent's type is gone. So it is threaded, and each recursing arm answers for its own
/// children: a constructor field always `Unnameable` (no parent type can supply a
/// declaration the entity does not have), a tuple component from whether the parent type
/// is an unsolved variable, and either arm INHERITS when it has no type of its own — a
/// tuple nested in an undeclared constructor field is still unnameable.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum UnpinnedBinder {
    /// Nothing can ever supply a type here. Keep the inert form.
    Unnameable,
    /// The type is to be INFERRED. Mint the engine's own variable, as the lambda's
    /// rung 3 does.
    ToBeInferred,
}

/// WI-20260904-50B2K — is a sub-pattern's PARENT type itself an inference hole, so that
/// its components are to be inferred rather than unnameable?
///
/// `Var::Global` ONLY. A `Var::Rigid` is a type parameter rigidified for the duration of
/// a body check (WI-392 / WI-1059) — a type that IS named, just abstract — and its
/// components are no more solvable than an undeclared field's. A concrete parent type
/// that simply is not a tuple is not a hole either: that is an arity or shape defect
/// belonging to whichever check owns it, and minting a bindable variable there would
/// invent evidence.
///
/// BOTH CARRIERS, because a type value is carrier-neutral in the typer: rung 3 mints a
/// `Value::Term` wrapping a `Term::Var` (a variable in TYPE position is interned by
/// construction — `TypeChild::Interned` holds a `TermId`), while WI-109's `Value::Var` is
/// the same variable spelled at the value level. Reading only one of them would answer
/// `false` for a hole depending on which side built it.
fn parent_type_is_inference_hole(kb: &KnowledgeBase, parent: &Value) -> bool {
    match parent {
        Value::Var(Var::Global(_)) => true,
        Value::Term { id, .. } => matches!(kb.get_term(*id), Term::Var(Var::Global(_))),
        _ => false,
    }
}

/// WI-20260827-EJ5F5 — re-point an arm's body / guard at the constructors the pattern
/// rewrite resolved, replacing every reference to a binder the rewrite REMOVED.
///
/// WHY THIS IS NEEDED AT ALL, and why it is not the pattern's job: the LOADER pushes a
/// `match_branch`'s written binder names onto its local-name frame before any type
/// exists (`load.rs`'s `binder_syms` / `local_names_stack`), so an arm body's `red`
/// inside `case red -> red` was already remapped to that binder's FRESH symbol. Rewriting
/// the pattern removes the binding; without this the reference resolves to nothing and
/// the program that used to load — wrongly, as a catch-all — stops loading. MEASURED:
/// `11:21: type mismatch in red.name: expected resolved name, got unresolved`.
///
/// The substitution is the arm's own meaning, and it is exactly what the PARENTHESIZED
/// spelling already gets for free: `case red() -> red` loads today and reads `red` as the
/// constructor, because the loader pushes no frame entry for a `pattern_constructor`.
/// Leaving the bare spelling to refuse would put a difference back between two spellings
/// this ticket exists to make identical.
///
/// NO CAPTURE. Each binding site mints its OWN symbol (WI-550), so an inner
/// `let red = …` / `lambda red -> …` inside the arm binds a DIFFERENT symbol and its
/// references remap to that one; `dead` reaches only the references the loader pointed at
/// the removed binder. A nested pattern is `NodeKind::Pattern`, whose `as_expr` is `None`,
/// so the walk returns it untouched rather than rewriting a binder into a constructor.
pub(super) fn repoint_arm_binders(
    node: &Rc<NodeOccurrence>,
    pairs: &[(Symbol, Symbol)],
) -> Rc<NodeOccurrence> {
    if pairs.is_empty() {
        return Rc::clone(node);
    }
    let Some(expr) = node.as_expr() else {
        return Rc::clone(node);
    };
    let hit = |sym: Symbol| pairs.iter().find(|(dead, _)| *dead == sym).map(|(_, c)| *c);
    // The three leaf spellings a body reference to a binder can arrive in — the same
    // three `body_specialize::reduce` substitutes for an inlined parameter.
    let leaf = match expr {
        Expr::VarRef { name } => hit(*name).map(|c| Expr::VarRef { name: c }),
        Expr::Ref(sym) => hit(*sym).map(Expr::Ref),
        Expr::Ident(sym) => hit(*sym).map(Expr::Ident),
        _ => None,
    };
    if let Some(e) = leaf {
        return NodeOccurrence::new_expr(e, node.span, node.owner);
    }
    let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
    crate::kb::node_occurrence::for_each_child(expr, |c| {
        children.push(repoint_arm_binders(c, pairs))
    });
    let rebuilt = crate::kb::simp_rewrite::reassemble(node, &children);
    // `red()` — the APPLIED spelling of the same reference. The loader saw the binder,
    // not a constructor, so it built an `Apply` whose FUNCTOR is the binder symbol; the
    // functor is not a child, so the walk above cannot reach it. Re-pointed after the
    // rebuild so the arguments are already done. Driven by
    // `an_arm_body_may_name_its_own_constructor`'s applied row.
    //
    // The other symbol-carrying `Expr` shapes are NOT reference positions for a binder
    // and are deliberately left alone: `Constructor.name` and `TypeValue.head` are
    // resolved declarations the loader only mints for a name it already resolved,
    // `DotApply.name` is a member selected ON the receiver (which IS a child, so the
    // walk reaches it), and every `*Within` form is post-elaboration — none can carry a
    // binder symbol here, and none could be driven if it were written.
    if let Some(Expr::Apply {
        functor,
        pos_args,
        named_args,
        type_args,
        recv_type,
    }) = rebuilt.as_expr()
    {
        if let Some(ctor) = hit(*functor) {
            return NodeOccurrence::new_expr(
                Expr::Apply {
                    // WI-20260829-W6JH0: re-pointing the FUNCTOR does not change what the
                    // call's result was claimed to be — carry it.
                    recv_type: recv_type.clone(),
                    functor: ctor,
                    pos_args: pos_args.clone(),
                    named_args: named_args.clone(),
                    type_args: type_args.clone(),
                },
                rebuilt.span,
                rebuilt.owner,
            );
        }
    }
    rebuilt
}

/// WI-20260827-EJ5F5 — the nullary constructor a `Pattern::Var` OCCURRENCE denotes, or
/// `None` when it is an ordinary binder. The occurrence-level wrapper of
/// [`pattern_var_ctor_sym`], and the one all three readers go through.
///
/// The `: T` gate lives HERE rather than at the rewrite because it is a property of what
/// the name MEANS, not of what one reader does with it. When it sat at the rewrite alone,
/// `case (red: C) -> …` was a catch-all at run time while `collect_covered_entities`
/// recorded `red` as COVERED (so a genuinely non-exhaustive match reported nothing) and
/// `pattern_match_value` put the ground `eq(s, Ref(red))` into an arm that runs for every
/// OTHER constructor too — a false fact feeding guard and proof checking. An annotation is
/// only ever written on a binder, so it answers the question for every reader at once.
pub(super) fn var_pattern_ctor(
    kb: &KnowledgeBase,
    pattern: &NodeOccurrence,
    name: Symbol,
    scrutinee_ctors: &[Symbol],
) -> Option<Symbol> {
    if pattern.pattern_type_ann().is_some() {
        return None;
    }
    pattern_var_ctor_sym(kb, name, scrutinee_ctors)
}

/// The nullary constructor a bare `match`-arm name denotes at a position of type
/// `position_type`, or `None` when it is an ordinary binder.
///
/// The candidate set is derived HERE from the position's own type, by the same two calls
/// the enclosing `match` uses for its top-level scrutinee (`sort_functor_of_view` then
/// [`sort_constructor_syms`]) — so a NESTED position (`case some(red)`, `case (red, n)`)
/// asks the question of the type actually threaded to it, which is what makes the
/// resolution uniform with depth instead of stopping at the arm's outermost pattern.
pub(super) fn match_arm_nullary_ctor(
    kb: &KnowledgeBase,
    pattern: &NodeOccurrence,
    name: Symbol,
    position_type: Option<&Value>,
) -> Option<Symbol> {
    let ctors: Vec<Symbol> = position_type
        .and_then(|t| sort_functor_of_view(kb, t))
        .map(|s| sort_constructor_syms(kb, s))
        .unwrap_or_default();
    // The rewrite asks one question MORE than the other two readers — see
    // [`declares_a_nullary_entity`] for why that is a second question and not a second
    // answer to the shared one.
    var_pattern_ctor(kb, pattern, name, &ctors).filter(|c| declares_a_nullary_entity(kb, *c))
}

/// Bind a pattern's variables into `env`, AND record each tuple binder's component
/// label on the pattern (WI-803). Named for both jobs: as `extend_env_from_pattern`
/// it advertised only the first, so the second — whose result a caller must thread
/// onward or silently lose — lived only in the `#[must_use]` message.
///
/// WI-511 (WI-348): reads the `Pattern` occurrence DIRECTLY (no `pattern_to_term`
/// lowering, no `Ref`/`Fn` carrier to disambiguate). The sub-patterns are
/// already `Rc<NodeOccurrence>` children, so the recursion threads occurrences.
///
/// WI-803: RETURNS the pattern, relabelled — the same `Rc` when nothing changed,
/// a rebuilt one when a tuple binder list learned its components' LABELS from
/// `scrutinee_type` (`Pattern::Tuple.labels`, which `match_tuple_pattern` then
/// destructures by). The comment this function's three callers used to carry, "the
/// typer doesn't rewrite patterns", is no longer true, and the caller must thread
/// the result into its `reassemble` — a dropped result is not a compile error, it
/// is a binder list that silently falls back to reading by SLOT, which is the
/// WI-788 wrong answer the labels exist to prevent.
#[must_use = "WI-803: the relabelled pattern must reach the reassembled node, or \
              destructuring silently falls back to positional"]
pub(super) fn bind_and_label_pattern(
    kb: &mut KnowledgeBase,
    env: &mut TypingEnv,
    pattern: &Rc<NodeOccurrence>,
    scrutinee_type: Option<Value>,
    // WI-20260827-EJ5F5: which QUESTION this pattern is being read as. Threaded
    // unchanged into every sub-pattern — a `match` arm's whole pattern is refutable,
    // so each position inside it is too.
    role: PatternRole,
    // WI-20260827-EJ5F5: every `(dead binder, constructor)` pair this call rewrote, at
    // any depth. The caller MUST apply them to the arm's body and guard
    // ([`repoint_arm_binders`]) — the loader captured the written name into the arm's
    // local-name frame before any type was known, so a body reference to it is a
    // `VarRef` at the now-removed binder's fresh symbol and resolves to nothing. Empty
    // for `PatternRole::Binder`, which never rewrites.
    repointed: &mut Vec<(Symbol, Symbol)>,
    // WI-20260904-50B2K: what an ABSENT type at THIS position means — see
    // [`UnpinnedBinder`]. Read only by the `Pattern::Var` fallback; every recursing arm
    // answers it afresh for its own children, or inherits when it has no type either.
    unpinned: UnpinnedBinder,
    // WI-794: contradictions between a binder's WRITTEN annotation and the type the
    // context threads into its slot. An out-param rather than a `Result` because
    // env-extension must CONTINUE past a bad binder — every other binder in the same
    // pattern still has to land in the env, or the body reports a cascade of
    // `UnresolvedName`s that hide the real diagnostic.
    errors: &mut Vec<TypeError>,
) -> Rc<NodeOccurrence> {
    let Some(pat) = pattern.as_pattern() else {
        return Rc::clone(pattern);
    };
    // WI-819: the binder's own annotation hangs on the pattern OCCURRENCE, not
    // on `Pattern::Var` — so it is read the same way for every variant.
    let type_ann = pattern.pattern_type_ann();
    match pat {
        Pattern::Var { name } => {
            // WI-20260827-EJ5F5: A BARE NAME THAT NAMES ONE OF THIS POSITION'S OWN
            // NULLARY CONSTRUCTORS IS THAT CONSTRUCTOR, not a binder — the spec rule
            // "Constructor patterns resolve against the scrutinee, not the scope", which
            // until now the typer applied to EXHAUSTIVENESS and to the arm's Γ fact and
            // to nothing that runs. The evaluator and `folded_call_match` read the stored
            // `Pattern`, so a `Var` there bound the whole scrutinee: `case red -> 1` was a
            // catch-all, every later arm was dead, and `pick(green())` answered 1.
            //
            // Rewriting HERE, rather than in the loader, is what the spec says and the
            // only place it can be done: which constructors are in view is a property of
            // the scrutinee's TYPE, which no load pass holds. The rewritten pattern
            // reaches everything downstream because the typer is tree-producing —
            // `MatchFinal` reassembles the match from `branch_patterns` and
            // `set_op_body_node` writes the result back.
            //
            // A WRITTEN ANNOTATION opts out (`case (red: C) -> …`): `: T` is only ever
            // written on a binder, so it is the author saying which of the two they meant,
            // and it is the repair for a binder whose name collides with a constructor.
            if role == PatternRole::MatchArm {
                if let Some(ctor) =
                    match_arm_nullary_ctor(kb, pattern, *name, scrutinee_type.as_ref())
                {
                    repointed.push((*name, ctor));
                    return NodeOccurrence::new_pattern(
                        Pattern::Constructor {
                            name: ctor,
                            pos_args: Vec::new(),
                            named_args: Vec::new(),
                        },
                        pattern.span,
                        pattern.owner,
                    );
                }
            }
            // Bind the pattern var even when its type is unknown — a
            // pattern-bound name is in scope regardless. Without this,
            // tuple-destructuring lambda params (`lambda (a, b) -> ...`, whose
            // sub-patterns recurse here with no component type) and match vars
            // over an un-inferred scrutinee stayed unbound and every reference
            // failed as `UnresolvedName`. (WI-289)
            // WI-517: a binder may carry its own `: Type` annotation
            // (`lambda (a: A, b: B) -> ...`). The type threaded from the
            // surrounding context (`scrutinee_type` — a constructor field, a
            // tuple component of a KNOWN scrutinee/expected type) takes
            // PRIORITY: it is what the value actually is, and the body is
            // checked against it. The binder's own annotation is used only as a
            // FALLBACK when the context type is unknown — the no-expected-arrow
            // case the WI targets (`let f = lambda (a: A, b: B) -> add(a, b)`),
            // where the threaded type is None and each element would otherwise
            // mint a fresh var and leave `add` dispatch-ambiguous. Letting the
            // context win (not the annotation) keeps this sound: a contradicting
            // annotation in a known-context position surfaces loudly through the
            // body's own use of the binder (bound to the real type), instead of
            // the lambda's arrow advertising one type while its body assumes
            // another. (The single-binder `lambda (x: T) -> ...` path pins
            // `param_type` from the annotation at the lambda level, so its arrow
            // reflects the annotation and a mismatch is caught by subsumption.)
            //
            // WI-794 — THE CONTEXT STILL WINS, but the losing annotation is no longer
            // DISCARDED SILENTLY. WI-517's claim above, that a contradiction "surfaces
            // loudly through the body's own use of the binder", holds only when the body
            // actually USES that binder at a type-constraining position: in
            // `lambda (a: Int64, b: String) -> a` nothing ever reads `b`, so the `String`
            // was accepted and ignored. That is the silent skip CLAUDE.md rules out — the
            // annotation is the user's explicit statement of intent, so a contradicting
            // one is now reported here, where the two types are both in hand.
            // WI-342: the env binds a carrier-agnostic `Value`, so a
            // `Value::Node` component type is preserved, not re-grounded.
            // The annotation occurrence rides alongside its `Value` to carry the span.
            // MEASURED: that span is currently the enclosing lambda's, not the written
            // type's — `term_to_expr_leaf_occ` stamps the annotation with its PARENT
            // pattern's span (node_occurrence.rs), because the loader lowers the
            // annotation through hash-consed KB terms, which own no span (one shared term,
            // many sites). So the diagnostic locates the lambda and names the BINDER to
            // disambiguate which annotation is meant. Reading it from the occurrence
            // anyway rather than hard-coding the pattern's: if per-annotation spans are
            // ever preserved, this sharpens with no change here.
            // INTERNED, not carried as a `Value::Node`, and that is load-bearing rather
            // than incidental. Comparing on the occurrence carrier was TRIED and makes
            // `resolved_type_is_ground` answer false — `node_type_is_ground` walks a
            // `Type`/`EffectExpression` spine, and a pattern's `type_ann` child is not yet
            // in that form (hence the "ground it to a `Value::Term`" step the lambda arm
            // performs on the same child). The gate then stands the check DOWN and every
            // contradiction loads clean again. Measured: 6 of the 11 WI-794 tests failed,
            // and precisely the rejection ones — a silent no-op of exactly the kind this
            // ticket exists to remove, caught only because those tests assert the
            // `binder-annotation` TAG rather than a bare `is_err`.
            //
            // One term per annotated binder is therefore the price of the check, and
            // nothing is wasted: when the context wins, this term answers the comparison;
            // when it does not, the same term becomes the binder's type below.
            // WI-819: decoded by `pattern_annotation_value`, the one reader —
            // carrier-preserving, so a `denoted`-bearing binder annotation is
            // compared as itself rather than flattened.
            // WI-1059: the annotation is discharged to the SAME level as the context
            // before the two are compared. `let seed: List[T = xs.T]` states a
            // projection; the context that reaches here has already had its projections
            // eliminated at the let site, so comparing the two raw reports a
            // contradiction between a type and itself — `expected List[T = ?T], got
            // List[T = xs.T]`. WI-819 avoided that by writing the ELIMINATED form back
            // onto the pattern, but that form can hold a pass-local skolem and the
            // pattern lands in the stored tree ([`value_contains_rigid`]), so the
            // discharge belongs here, where it is read, rather than in what is kept. The
            // env is the same `Symbol -> type` resolver the let site used.
            //
            // An undischargeable projection keeps the RAW annotation, and the reason is not
            // "the let site already raised on it" — that covers `Expr::Let` only, while this
            // function also serves LAMBDA and MATCH-BRANCH binders, which have no such site.
            // The reason is that this call only COMPARES: it feeds
            // `binder_annotation_conflict`, whose job is to report a contradiction the
            // author wrote, and refusing here would report the ELIMINATION's failure under
            // the binder-annotation context — a worse message for a different defect.
            // Whoever owns a binder-annotation projection that cannot be discharged (no
            // caller does today — the lambda paths thread a context type instead) should
            // raise it where the projection is FORMED, not here.
            let ann_ty: Option<(&Rc<NodeOccurrence>, Value)> = type_ann.map(|ann| {
                let v = pattern_annotation_value(kb, ann);
                let v = if value_contains_projection(kb, &v) {
                    let ctx = TypeErrorContext::LetBinding { var: *name };
                    eliminate_type_projections(
                        kb,
                        &v,
                        &env.var_bindings,
                        None,
                        &ctx,
                        Some(ann.span.span),
                    )
                    .unwrap_or(v)
                } else {
                    v
                };
                (ann, v)
            });
            if let (Some(ctx), Some((ann_occ, ann))) = (scrutinee_type.as_ref(), ann_ty.as_ref()) {
                if let Some(err) =
                    binder_annotation_conflict(kb, *name, ctx, ann, Some(ann_occ.span.span))
                {
                    errors.push(err);
                }
            }
            let ty = scrutinee_type
                .or_else(|| ann_ty.map(|(_, v)| v))
                .unwrap_or_else(|| {
                    // WI-20260904-50B2K — THIS SITE SERVED BOTH QUESTIONS AT ONCE, the
                    // same conflation the ticket separates one level up, found one level
                    // down. It is now SPLIT, and [`UnpinnedBinder`] carries which one is
                    // being asked; the split is what the first attempt lacked, measured:
                    // flipping the whole site to the engine's variable failed FOUR rows,
                    // all `match s case SetLiteral(a, _, _) -> a` over a `Set[T = Int64]`
                    // with "type mismatch in match.rule (rule): expected Int64, got
                    // ??pat".
                    //
                    // THE NAME IS SHARED and only the FORM differs, which is the point:
                    // both are still "the sub-pattern's type", so a diagnostic that
                    // prints one reads the same as before.
                    let fresh = kb.intern("?pat");
                    match unpinned {
                        // A type EXISTS one level up and is itself a hole — a tuple
                        // binder whose param type is the lambda's own rung 3. The
                        // components are exactly what inference must solve, so this mints
                        // what rung 3 mints — including its CARRIER: WI-20260904-02ERR
                        // removed the interning caveat this comment used to record, so a
                        // per-site inference variable is no longer pinned in the term
                        // store. The two producers must move together; fixing only rung 3
                        // would leave every tuple-binder component still interned.
                        UnpinnedBinder::ToBeInferred => {
                            let vid = kb.fresh_var(fresh);
                            Value::Var(Var::Global(vid))
                        }
                        // The DECLARATION is what is missing and no parent can supply it.
                        // `SetLiteral` is a parse-level marker with no declared field
                        // types, so nothing will ever pin this; the inert form is
                        // structurally ground, which keeps the conformance check RUNNING
                        // and compatible-with-anything rather than withheld on an
                        // unsolvable variable.
                        UnpinnedBinder::Unnameable => Value::term(kb.make_type_var(fresh)),
                    }
                });
            env.bind_var(*name, ty);
            // Pattern-bound names are local — effects on them shouldn't escape
            // the surrounding match/case scope (matches `check_let_expr`'s
            // declare_local_resource for let bindings). Without this, a body
            // like `match Cell.get(s) case wis(b, _) -> persist(b, ...)` would
            // surface persist's `Modify[b]` as an external effect even though
            // b's lifetime ends at case end.
            env.declare_local_resource(*name);
            // A binder writes no labels of its own; its `type_ann` is an Expr-kind
            // child the typer does not rewrite here.
            Rc::clone(pattern)
        }
        Pattern::Constructor {
            name,
            pos_args,
            named_args,
        } => {
            let ctor_sym = *name;
            let field_types = kb.entity_field_types(ctor_sym).map(|f| f.to_vec());
            // Substitute the scrutinee's type args into the constructor's
            // declared field types. For `case some(name)` over
            // `Option[T = String]`, `some.value`'s declared type `T` resolves
            // to `String` — without this `name` binds to the raw type-param
            // term and surfaces as a bare `TermId` in later return-type checks.
            //
            // WI-946: the TOTAL belongs-to. For an EPONYMOUS parametric sort
            // (`sort Box { sort T = ?; entity Box(v: T) }`) the strict view
            // answered `None`, `build_pattern_subst` was never run, and `v` stayed
            // the abstract `T` — so `case Box(v) -> v` in an op returning `Int64`
            // over a `Box[T = Int64]` scrutinee was FALSELY REJECTED, while the
            // sort-nested spelling of the same declaration type-checked.
            let parent_sort = kb.sort_of_constructor(ctor_sym);
            let subst = scrutinee_type
                .as_ref()
                .zip(parent_sort)
                .and_then(|(st, p)| build_pattern_subst(kb, st, p));
            // WI-803: a constructor's sub-patterns may THEMSELVES be tuple binder
            // lists (`case Box((a, b)) ->`), so the rebuilt children are collected
            // in `for_each_pattern_child` order — positional then named — and
            // handed to `reassemble_pattern`, which returns this same `Rc` when
            // none of them moved.
            let mut rebuilt: Vec<Rc<NodeOccurrence>> =
                Vec::with_capacity(pos_args.len() + named_args.len());
            // WI-20260827-1F0QP: WHICH field a positional sub-pattern takes is the
            // rank-among-NOT-named rule, one owner
            // ([`KnowledgeBase::rank_positional_among_unnamed`]) — not a leading-index
            // copy. In `case two(y, a: 1)`, `y` is field `b`, so it must be typed from
            // `b`'s declared type. Zipping by index typed it from `a` instead, which is
            // invisible while an entity's fields share a type and a WRONG BINDER TYPE
            // the moment they don't (`a_mixed_pattern_binder_is_typed_from_the_field_it_takes`).
            let named_syms: SmallVec<[Symbol; 2]> = named_args.iter().map(|(s, _)| *s).collect();
            let pos_fields = match field_types.as_ref().map(|f| {
                let decl: SmallVec<[Symbol; 4]> = f.iter().map(|(s, _)| *s).collect();
                KnowledgeBase::rank_positional_among_unnamed(
                    &decl,
                    |fs| named_syms.contains(&fs),
                    pos_args.len(),
                )
            }) {
                Some(PositionalPlan::Assign(fields)) => Some(fields),
                // No declared field types to rank among, or more positional
                // sub-patterns than unfilled fields — an ill-formed pattern the
                // arity checks refuse elsewhere. Fall back to the slot, which types
                // what it can and leaves the rest `None`, as before.
                _ => None,
            };
            // POSITIONAL sub-patterns: the field each one RANKS to (its declared type).
            for (i, sub_pat) in pos_args.iter().enumerate() {
                // WI-342: the field type is a carrier-agnostic `Value`
                // (`entity_field_types`); resolve its sort-level type params
                // through the pattern subst without re-grounding. Deep-walk: a
                // parameterized field type (`source: Stream[T = T, E = E]`)
                // carries its type params NESTED in the `Fn`, which the shallow
                // `walk_type_value` left unsubstituted — so the destructure did
                // not thread the scrutinee's element / effect into the
                // sub-pattern var (WI-413).
                let declared = match &pos_fields {
                    Some(fields) => field_types
                        .as_ref()
                        .and_then(|f| f.iter().find(|(fs, _)| *fs == fields[i])),
                    None => field_types.as_ref().and_then(|f| f.get(i)),
                };
                let field_type = match (declared, &subst) {
                    (Some((_, ty)), Some(s)) => Some(walk_pattern_field_type_deep(kb, s, ty)),
                    (Some((_, ty)), None) => Some(ty.clone()),
                    (None, _) => None,
                };
                rebuilt.push(bind_and_label_pattern(
                    kb,
                    env,
                    sub_pat,
                    field_type,
                    role,
                    repointed,
                    // WI-20260904-50B2K: a constructor field with no declared type is
                    // UNNAMEABLE whatever the scrutinee is — the missing thing is the
                    // ENTITY's declaration, and no parent type can supply it. Not
                    // inherited and not computed from `scrutinee_type`: a `SetLiteral`
                    // under an as-yet-unsolved scrutinee is no more solvable than one
                    // under a concrete `Set[T = Int64]`.
                    UnpinnedBinder::Unnameable,
                    errors,
                ));
            }
            // WI-445: NAMED sub-patterns (`case Box(v: some(x))`) bind by FIELD
            // NAME — order-independent, so robust to declaration order. The
            // field type is resolved here, where the typer pass always has the
            // entity in hand.
            for (field_sym, sub_pat) in named_args {
                let found = field_types
                    .as_ref()
                    .and_then(|fields| fields.iter().find(|(fname, _)| *fname == *field_sym));
                let field_type = match (found, &subst) {
                    (Some((_, ty)), Some(s)) => Some(walk_pattern_field_type_deep(kb, s, ty)),
                    (Some((_, ty)), None) => Some(ty.clone()),
                    (None, _) => None,
                };
                rebuilt.push(bind_and_label_pattern(
                    kb,
                    env,
                    sub_pat,
                    field_type,
                    role,
                    repointed,
                    // The positional loop's reason, unchanged by binding position.
                    UnpinnedBinder::Unnameable,
                    errors,
                ));
            }
            // WI-819: `rebuilt` holds SUB-PATTERNS only — the pattern's own `: T`
            // is carried across by the reassembler, since binding rewrites
            // sub-patterns and never the annotation.
            crate::kb::node_occurrence::reassemble_pattern_subpatterns(pattern, &rebuilt)
        }
        Pattern::Tuple {
            positional,
            labels: old_labels,
        } => {
            // When the scrutinee is a tuple type, bind each sub-pattern to its
            // component type — so `lambda (a, b) -> a + b` checked against
            // `Function[(Int, Int), Int]` types a/b as Int and `+` dispatches
            // uniquely. Otherwise the component type is unknown and the
            // sub-pattern var mints a fresh type var.
            // WI-803: keep the component NAMES, which this read used to discard
            // (`named_tuple_field_types` maps them away). They are what binder `i`
            // is typed FROM, and recording them on the pattern is what lets the
            // matcher fetch that same component at run time instead of trusting
            // slot `i` of whatever value arrives — the WI-788 disagreement.
            let fields: Option<Vec<(Symbol, Value)>> = scrutinee_type
                .as_ref()
                .and_then(|t| named_tuple_field_pairs(kb, t));
            // WI-794: the index zip pairs binder `i` with component `i`, which is a
            // TRUSTWORTHY correspondence only at EQUAL arity — the rule
            // `validate_callback_effect_row` already follows for its place map. At
            // unequal arity binder `i` sits against an unrelated component, so an
            // annotation check there blames the annotation for what is really a missing
            // or extra parameter. MEASURED on the first cut of this fix:
            // `lambda (x: Int64, y: Int64)` at a `(a: Int64, b: String, c: Int64)` slot
            // reported "binder y: expected String, got Int64".
            //
            // Only the CHECK stands down; the BINDING is deliberately left exactly as it
            // was. Withholding the components instead was tried and REVERTED — it broke
            // `arity_mismatch_still_refuses_to_match`, where `lambda (p, q)` against a
            // 3-component tuple must LOAD clean (the arity is a runtime pattern-match
            // property there, not a load error) and fresh binder vars made `p - q`
            // dispatch-ambiguous. So a misaligned component still types its binder, and
            // the arity defect is left to whichever check genuinely owns it.
            let aligned = fields.as_ref().is_none_or(|f| f.len() == positional.len());
            // WI-20260904-50B2K: a component with no type of its own asks the question its
            // PARENT's type answers — an unsolved variable one level up makes every
            // component an inference hole (`lambda (a, b) -> a + b` at rung 3), while no
            // parent type at all leaves the question exactly as it reached here (a tuple
            // nested in an undeclared constructor field is still unnameable).
            //
            // Computed ONCE, above the loop: it is a property of this node, not of slot
            // `i`. And read only when `fields` gave the child nothing — a component that
            // IS typed never reaches the fallback.
            //
            // EACH COMPONENT GETS ITS OWN INDEPENDENT VARIABLE, AND NOTHING TIES IT TO
            // THE PARENT'S — /code-review, and it is the LIMIT of what this change buys.
            // Solving the parent at a use site (`?p := (a: Int64, b: Int64)`) therefore
            // does not solve `?a` / `?b`, so a tuple binder is still reached by inference
            // only through its own BODY. Tying them means minting the parent as a
            // `named_tuple` OVER these variables — which is the same repair the arity
            // disagreement at [`arrow_positional_param_slots`] wants, and it is
            // WI-20260904-34J8Z because it must first answer where the tuple's LABELS
            // come from (WI-803: from the EXPECTED type, never from the binder names).
            let child_unpinned = match scrutinee_type.as_ref() {
                Some(t) if parent_type_is_inference_hole(kb, t) => UnpinnedBinder::ToBeInferred,
                Some(_) => UnpinnedBinder::Unnameable,
                None => unpinned,
            };
            let mut rebuilt: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(positional.len());
            for (i, sub_pat) in positional.iter().enumerate() {
                let comp = fields
                    .as_ref()
                    .and_then(|f| f.get(i))
                    .map(|(_, v)| v.clone());
                rebuilt.push(if aligned {
                    bind_and_label_pattern(
                        kb,
                        env,
                        sub_pat,
                        comp,
                        role,
                        repointed,
                        child_unpinned,
                        errors,
                    )
                } else {
                    let mut misaligned = Vec::new();
                    bind_and_label_pattern(
                        kb,
                        env,
                        sub_pat,
                        comp,
                        role,
                        repointed,
                        child_unpinned,
                        &mut misaligned,
                    )
                });
            }
            // WI-803: the LABELS, recorded only when there is one component per
            // binder. `aligned` is exactly that condition, and it is the right gate
            // for two independent reasons:
            //
            //  * a MISALIGNED list has no correspondence to record — binder `i`
            //    already sits against an unrelated component, which is what the
            //    WI-794 note above is about;
            //  * leaving the labels empty there keeps the POSITIONAL path, whose
            //    count test is the only thing that refuses the shape at run time.
            //    `arity_mismatch_still_refuses_to_match` pins that: `lambda (p, q)`
            //    against a 3-component tuple must LOAD clean and fail at the MATCH.
            //    A by-label read would not care about the extra component and would
            //    quietly succeed — turning a loud arity failure into an accepted
            //    program, which is the wrong direction.
            //
            // Width subtyping is unaffected: it makes the VALUE wider than the
            // type, never the type wider than the binder list, so a value with
            // extra components still meets a labelled pattern and its extras go
            // unread — exactly as a `.a` / `.c` reader would leave them.
            let labels: Vec<Symbol> = match &fields {
                Some(f) if aligned => f.iter().map(|(name, _)| *name).collect(),
                _ => Vec::new(),
            };
            if labels == *old_labels {
                // Nothing new to record, so the "reuse `occ` when no child moved"
                // rule stays under its owner — the same call the Constructor arm
                // above makes. Hand-rolling the `Rc::ptr_eq` scan here as well left
                // two copies of that rule in one function, free to drift apart.
                crate::kb::node_occurrence::reassemble_pattern_subpatterns(pattern, &rebuilt)
            } else {
                // The labels changed, so `reassemble_pattern`'s "reuse when no
                // child moved" rule cannot apply — rebuild directly. WI-819: the
                // annotation is read straight off the occurrence, not recovered
                // from `rebuilt`, which holds sub-patterns only.
                NodeOccurrence::new_pattern_annotated(
                    Pattern::Tuple {
                        positional: rebuilt,
                        labels,
                    },
                    type_ann.map(Rc::clone),
                    pattern.span,
                    pattern.owner,
                )
            }
        }
        // wildcard, literal_pattern — no bindings
        Pattern::Wildcard | Pattern::Literal { .. } => Rc::clone(pattern),
    }
}

/// WI-794: does a binder's WRITTEN `: Type` annotation contradict the type the context
/// threads into its slot? `Some(error)` when the two are decisively incompatible, `None`
/// when they agree or when the pair cannot be judged.
///
/// DIRECTION. The binder is bound to `context_ty` — the context wins, which is WI-517's
/// soundness decision and is left untouched (see the `Pattern::Var` arm). So the
/// annotation is a CLAIM about a value that really has `context_ty`, and the claim is
/// truthful exactly when `context_ty` conforms to it: a WIDER annotation (`Int64` slot
/// annotated with a spec `Int64` provides) is imprecise but true and is accepted; a
/// NARROWER or disjoint one is false and is reported. The diagnostic then reads in the
/// user's direction — `expected` is what the slot really is, `actual` what they wrote.
///
/// GROUNDNESS GATE, the WI-385/WI-469 discipline: judge only when BOTH sides are ground.
/// A generic callback slot (`(acc: Acc, x: xs.T) -> Acc`) threads a type var or an
/// unresolved projection into the binder, and an annotation is a legitimate way to PIN
/// it — rejecting there would refuse correct programs. Deliberately conservative: this
/// closes the ground case WI-794 measured and leaves the polymorphic slot to unification,
/// alongside the same-family gap WI-791 pins as
/// `known_gap_generic_callback_arrow_is_not_conformance_checked`.
///
/// THE GATE IS WIDER THAN THAT RATIONALE, and the difference is worth knowing before
/// relying on this check. `resolved_type_is_ground` takes an immutable `&KnowledgeBase`
/// and answers STRUCTURALLY — it consults no `Substitution`, because this runs in the
/// visit phase, which has none (the same reason the comparison below needs a scratch
/// one). So a type var that the surrounding inference HAS already bound to a concrete
/// type still reads as non-ground here, and its contradiction is passed over exactly as
/// the original defect did. Not just the honestly-polymorphic slot: any slot whose
/// concreteness is known only through a substitution. Closing that needs the check to run
/// where `subst` is in hand, which is the argument-position alternative this ticket
/// rejected for a different reason (it would re-derive the binder↔slot alignment).
fn binder_annotation_conflict(
    kb: &mut KnowledgeBase,
    binder: Symbol,
    context_ty: &Value,
    annotation: &Value,
    span: Option<Span>,
) -> Option<TypeError> {
    if !resolved_type_is_ground(kb, context_ty) || !resolved_type_is_ground(kb, annotation) {
        return None;
    }
    // A scratch substitution: with both sides ground there is nothing to look up and
    // nothing to bind, so no inference is lost by discarding it. This check is a
    // VALIDATION — the binder's type is already decided above it.
    if types_compatible(kb, &mut Substitution::new(), context_ty, annotation) {
        return None;
    }
    Some(TypeError::TypeMismatch {
        site: TypeError::here(),
        span,
        context: TypeErrorContext::BinderAnnotation { binder },
        expected: context_ty.clone(),
        // The two sides are the binder's WRITTEN annotation and the type its context
        // threads in — both types, neither an expression.
        denoted: None,
        actual: annotation.clone(),
    })
}

/// WI-511 (WI-348): the optional type-annotation occurrence of a pattern
/// (`let p: T`, `lambda (x: T) -> …`).
///
/// WI-819: THE reader of THE annotation channel. It used to answer only for a
/// `Pattern::Var`, because that was the only variant with a slot — so a `let`
/// over any other pattern shape had to reach a second, `Expr::Let`-only field
/// instead. Both callers (the `Expr::Let` arm and the `Expr::Lambda` arm) now
/// come here, which is what makes `let x: Int64 = 1` and
/// `let (a, b): (Int64, String) = p` the same mechanism.
pub(super) fn extract_pattern_type_ann(
    pattern: &Rc<NodeOccurrence>,
) -> Option<&Rc<NodeOccurrence>> {
    pattern.pattern_type_ann()
}

/// WI-791: how many PARAMETERS a lambda writes — the arity its arrow type
/// records. A lambda holds ONE param occurrence, so the count lives in that
/// pattern's shape: `lambda (a, b) -> …` is a `Pattern::Tuple` of two, and
/// everything else (`lambda x -> …`, `lambda (u: (a: A, b: B)) -> …`) is one.
///
/// The written count is also the count the RUNTIME accepts: WI-784 taught
/// `gather_closure_arg` to gather an n-argument application into the tuple the
/// binder list destructures, so a multi-binder lambda handed to a genuinely
/// n-parameter callback now applies instead of trapping. (Before that, minting 1
/// here was the considered alternative; it was rejected because the defect was
/// the runtime's missing gather, not the program's — and reporting the written
/// count preserved every load verdict a multi-binder lambda already got.)
///
/// Both sides read the SAME rule, `Pattern::binder_arity` — see its doc for why
/// they must not drift.
///
/// Grouping is transparent (WI-620: `(p)` unwraps to `p` at conversion), so
/// `lambda ((a, b)) -> …` is the same two-binder lambda as `lambda (a, b) -> …`
/// — the surface has no spelling for "one tuple-shaped binder" other than naming
/// it (`lambda (u: (a: A, b: B)) -> …`), which lands on the arity-1 arm here.
pub(super) fn lambda_written_arity(lambda_occ: &Rc<NodeOccurrence>) -> usize {
    let param = match lambda_occ.as_expr() {
        Some(Expr::Lambda { param, .. }) | Some(Expr::LambdaWithin { param, .. }) => param,
        _ => return 1,
    };
    param.as_pattern().map(Pattern::binder_arity).unwrap_or(1)
}

// ── Operation info lookup ──────────────────────────────────────

pub(super) fn lookup_operation_return_type(kb: &KnowledgeBase, functor: Symbol) -> Option<TermId> {
    lookup_operation_field(kb, functor, "return_type")
}

fn lookup_operation_field(kb: &KnowledgeBase, functor: Symbol, field: &str) -> Option<TermId> {
    // WI-348: carrier-agnostic — the OperationInfo head may be a value fact
    // (Node-carrying) for ops with a `denoted` effect. Read fields through the
    // shared `op_info` helpers, which view either carrier. This path serves
    // `lookup_operation_return_type`, whose `field` is always ground.
    //
    // WI-20260912-1QVWA — the third keyed reader of these facts, and it had the same
    // miss shape as the two in `op_info`: asked about a functor that is not an
    // operation, it walked every `OperationInfo` fact to answer `None`. It shares their
    // rid source, so it shares the index.
    for rid in crate::kb::op_info::op_info_fact_rids(kb, functor) {
        let head = kb.rule_head_value(rid);
        if crate::kb::op_info::head_name_ref(kb, head) == Some(functor) {
            return crate::kb::op_info::head_field_term(kb, head, field);
        }
    }
    None
}

// ── Type unification ───────────────────────────────────────────

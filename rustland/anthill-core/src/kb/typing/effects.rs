//! Effect rows: WI-307 row unification and subtyping, and WI-067 guarded-effect
//! discharge at a call site (preconditions, guarded atoms).

use super::*;

// ── WI-307 v1a row unification ──────────────────────────────────────────

/// WI-493: THE single bare-vs-wrapped effect-row tolerance. An `effects_rows(<EE>)`
/// wrapper unwraps to its bare inner `EffectExpression` `<EE>`; anything else is
/// `None`. A row tail / row value can be bound to EITHER a bare EffectExpression
/// (the canonical [`bind_row_tail`] shape, and a `provides … E = {}` fact's bare
/// binding) OR a WRAPPED `effects_rows(…)` (a written `E = {…}` row, or a provided
/// `E` row bound whole onto the tail var across unify / subtype / provider
/// admissibility). The two row-binding sources disagree on shape, so every
/// row-tail walker routes its unwrap through THIS one helper — so a new row
/// consumer cannot drift into mis-decomposing a wrapped tail (WI-493 consolidates
/// what WI-278 first patched inline in `decompose_effect_row`). Matched on the
/// qualified `EffectsRows` functor symbol, never the short name.
pub(super) fn effects_rows_inner<V: TermView>(kb: &KnowledgeBase, v: &V) -> Option<Value> {
    let er = kb.try_resolve_symbol("anthill.prelude.TypeExtractor.EffectsRows")?;
    match v.head(kb) {
        ViewHead::Functor {
            functor: Some(f), ..
        } if f == er => view_child_value(kb, v, "effects_expr"),
        _ => None,
    }
}

/// Decompose an arrow.effects field (`effects_rows(EffectExpression)` Type)
/// into (present_labels, open_tail, absent_labels) by structurally walking
/// the EffectExpression algebra through the current substitution.
///
/// Walks substitution at every node — if a row-tail `open(?ρ)` has been
/// bound to a concrete EffectExpression (merge chain etc.) by a prior row
/// unification, the walk recurses into the bound value. So a row that was
/// just `open(?ρ)` becomes its full decomposed shape once ?ρ is resolved.
///
/// `absent_labels` (the `-e` lacks-constraint slot) is consumed by
/// [`unify_effect_rows`] / [`subtype_effect_rows`] (WI-328): each side's
/// absents are registered as `lacks` constraints on that side's tail var
/// (`Substitution::add_lacks`) before the tail-binding step. A within-row
/// `present`/`absent` clash on the same label is rejected here (see the
/// end of the function).
///
/// **WI-339 F13** — returns `None` on **malformed input**:
/// - a second row-tail `Var` encountered after one was already recorded
///   (e.g. `merge(open(?ρ_1), open(?ρ_2))` — semantically nonsensical;
///   pre-WI-339 we kept the first and dropped subsequent ones silently);
/// - an unexpected functor inside the EffectExpression algebra (not
///   `empty_row` / `present` / `absent` / `open` / `merge`);
/// - an unexpected term shape (not `Term::Var` or `Term::Fn`).
///
/// Per `CLAUDE.md` *avoid fallbacks, know about errors early* — callers
/// translate `None` into a sub/unify rejection rather than proceeding
/// on incomplete decomposition. The well-formed inputs the typer
/// produces today never trip this; the hard-reject closes the door on
/// external producers (loader bugs, hand-built test terms) leaking
/// silent miscompares.
///
/// The raw effect-row decomposition: present labels, row tails, absent labels —
/// WITHOUT the self-contradiction (`{e, -e}`) filter. Returns `None` only for a
/// genuinely malformed row (unknown functor). WI-705:
/// [`check_signature_self_contradiction`] needs the raw present/absent so it can
/// REJECT a signature row a row-param instantiation makes uninhabitable
/// (violates its own `-X` lacks-constraint — `{Outside, -Outside}`) with a targeted
/// diagnostic, instead of the silent `None` the filter turns it into. (WI-700 first
/// introduced this split for `validate_callback_effect_row`; WI-705 hoisted the
/// reject to signature altitude and that caller reverted to the filtered wrapper.)
/// The filtering [`decompose_effect_row`] wrapper preserves prior behavior for its
/// ~10 subtype/unify/merge callers.
pub(super) fn decompose_effect_row_raw(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    effects: &impl TermView,
) -> Option<(Vec<Value>, Vec<TermId>, Vec<Value>)> {
    // WI-342 P4-B (B2): carrier-agnostic walk over the `EffectExpression`
    // algebra via [`TermView`], so a `Value`-carried (denoted-bearing) row
    // decomposes by the same code as a hash-consed `TermId` row. Field-name
    // symbols are interned up front (idempotent; the view's `effect_expr_named`
    // resolves the same names via `lookup_symbol`) so the rest of the walk is
    // read-only. Labels surface as owned `Value`s; the tail materializes to a
    // hash-consed `TermId` Var (row tails are always plain logic vars).
    let label_key = kb.intern("label");
    let tail_key = kb.intern("tail");
    let left_key = kb.intern("left");
    let right_key = kb.intern("right");

    let walked = walk_view(kb, subst, effects);
    // WI-493: unwrap the `effects_rows(…)` wrapper via the single shared tolerance
    // (matched by qualified symbol, so a same-short-named functor elsewhere is not
    // mistaken for the prelude `Type.effects_rows`).
    let expr: Value = if let Some(e) = effects_rows_inner(kb, &walked) {
        e
    } else if value_is_bare_effect_expr(kb, &walked) {
        // WI-441: a BARE EffectExpression node (`open(?ρ)` — a row var's
        // BINDING shape from `bind_row_tail`; a `merge(…)` a bound row var
        // walked to) is the row's inner expression itself.
        walked.clone()
    } else {
        // Not an effects_rows wrapper — a bare row Var is itself an open-tail
        // row (mostly partial arrows in tests); anything else is empty.
        match row_tail_termid(kb, &walked) {
            Some(t) => return Some((Vec::new(), vec![t], Vec::new())),
            None => return Some((Vec::new(), Vec::new(), Vec::new())),
        }
    };

    let mut present: Vec<Value> = Vec::new();
    let mut absent: Vec<Value> = Vec::new();
    let mut tails: Vec<TermId> = Vec::new();
    let mut stack: Vec<Value> = vec![expr];
    while let Some(node_raw) = stack.pop() {
        let node = walk_value_to_resolved(kb, subst, node_raw);

        // Unbound Var directly inside the algebra — a row-tail (any flavor;
        // a `TermId`-carried Rigid/DeBruijn is preserved as before).
        if let Some(node_tail) = row_tail_termid(kb, &node) {
            // WI-441 (supersedes the WI-339 F13 two-tail reject): MULTIPLE
            // distinct row tails are a legitimate row UNION — the merge of
            // two row variables (`{E, EffP}`, the lazy combinators' result
            // row). Collected deduped; the unify/subtype arms decide what
            // they can soundly do with a multi-tail row.
            if !tails.contains(&node_tail) {
                tails.push(node_tail);
            }
            continue;
        }

        // WI-278/WI-493: a row-tail (or merge child) may have been bound to a
        // WRAPPED row — `effects_rows(…)` — rather than a bare EffectExpression
        // (the two row-binding sources disagree on shape: a `provides … E = {}`
        // fact binds bare, while a written / provided `E` row binds the wrapper
        // whole onto the tail var across unify / subtype / provider admissibility).
        // Unwrap it mid-walk via the SINGLE shared tolerance so a wrapped tail
        // decomposes identically to a bare one. A MALFORMED wrapper (no
        // `effects_expr` child, never produced by `make_effects_rows_*`) returns
        // `None` here, falls through, and the `_` arm below hard-rejects it as an
        // unknown functor (WI-339 F13) — loud, not a silent drop.
        if let Some(inner) = effects_rows_inner(kb, &node) {
            stack.push(inner);
            continue;
        }

        match resolved_functor_name(kb, &node) {
            Some("empty_row") => {}
            Some("present") => {
                if let Some(l) = named_child_value(kb, &node, label_key) {
                    present.push(l);
                }
            }
            // WI-478 (proposal 048): a `guarded(label, guard)` atom is
            // CONSERVATIVELY PRESENT here — discharge (refuting the guard to drop
            // the label) is WI-067, out of phase 1's scope. So it contributes its
            // label exactly like `present`, ignoring the `guard` child. This keeps
            // the row a sound over-approximation until discharge lands.
            Some("guarded") => {
                if let Some(l) = named_child_value(kb, &node, label_key) {
                    present.push(l);
                }
            }
            Some("absent") => {
                if let Some(l) = named_child_value(kb, &node, label_key) {
                    absent.push(l);
                }
            }
            Some("open") => {
                if let Some(t) = named_child_value(kb, &node, tail_key) {
                    // Re-walk through the open-tail: a bound row variable
                    // resolves to a concrete EffectExpression here.
                    stack.push(t);
                }
            }
            Some("merge") => {
                if let Some(r) = named_child_value(kb, &node, right_key) {
                    stack.push(r);
                }
                if let Some(l) = named_child_value(kb, &node, left_key) {
                    stack.push(l);
                }
            }
            // WI-339 F13: unknown functor / unexpected shape — hard reject.
            _ => return None,
        }
    }

    Some((present, tails, absent))
}

/// WI-700 / WI-328 (piece d / proposal §7.2): the first PRESENT label of a row that
/// is ALSO ABSENT (`{e, -e}`) — the self-contradictory, uninhabitable shape. Two
/// callers share this so the detection cannot drift: the filtering
/// [`decompose_effect_row`] tests `.is_some()` (drops the malformed row to `None`);
/// [`validate_callback_effect_row`] binds the returned label for its lacks-violation
/// diagnostic (an explicit instantiation that violates its own `-X` lacks-constraint).
///
/// The per-pair verdict is [`label_violates_absence`], which is DIRECTIONAL and wider
/// than equality — see there.
pub(super) fn row_self_contradiction<'a>(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    present: &'a [Value],
    absent: &[Value],
) -> Option<&'a Value> {
    present.iter().find(|p| {
        absent
            .iter()
            .any(|a| label_violates_absence(kb, subst, p, a))
    })
}

/// WI-20260825-CBRSW — render ONE effect-row atom the way it is WRITTEN.
///
/// THE RULE IS UNCHANGED AND THE OWNER MOVED. An absence is the term `absent(label: K)`
/// and a diagnostic must show the `-K` the author wrote, not internal row syntax;
/// presence renders bare, its default written form; a guarded atom shows its label,
/// since its guard is a rule body this has no reader for. That was implemented HERE
/// because [`type_display_name_value`] printed `absent[label = K]`. WI-20260904-B1KFS
/// merged the display onto one `TermView` walk and put these three renderings on the
/// ATOM (`effect_expression_display`), where every carrier and every position reads them
/// — so this function is now the display, and repeating the arms would print `--K`.
///
/// `label_key` is the caller's already-interned `"label"` — the same shape
/// [`peel_effect_atom`] takes, and for the same reason: interning needs `&mut`, and every
/// caller here holds a row it is about to walk element by element. Unused since the arms
/// moved; kept so the callers' shape does not churn.
pub(super) fn effect_atom_display(kb: &KnowledgeBase, v: &Value, _label_key: Symbol) -> String {
    // WI-20260904-B1KFS — THE WHOLE OF THIS IS NOW THE DISPLAY. The two arms it used to
    // carry — unwrap a `present` to its label, and prefix an `absent`'s label with `-` —
    // were a caller-side repair for a renderer that printed `present[label = External]`.
    // `effect_expression_display` renders both, so keeping them here would print `--X`
    // for an absence. The parameter stays for the callers that intern the key.
    type_display_name_value(kb, v)
}

/// WI-20260825-CBRSW (proposal 064) — does a PRESENT label violate an ABSENT one?
///
/// EQUALITY, PLUS ONE LABEL'S ENTAILMENT. Every caller had equality before this ticket
/// and every label but `Permission` still has exactly that; the extra arm is
/// [`permission_entails`], and it is deliberately not a general rule about lacks
/// constraints. Widening it to one was tried and is WRONG — see that function's
/// "WHY NOT GENERAL", which records the two programs that measured it.
///
/// Directional: `violates(present, absent)` is not `violates(absent, present)`.
pub(super) fn label_violates_absence(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    present: &Value,
    absent: &Value,
) -> bool {
    // Resolve ONCE and share. This is [`resolved_labels_equal`]'s body with the walk
    // hoisted, not a second opinion about what equality is — the verdict is still
    // `views_structurally_equal` — and the hoist is what keeps the NON-equal path (the
    // common one once a row carries a `-X` at all) from walking both sides twice.
    let p = walk_value_to_resolved(kb, subst, present.clone());
    let a = walk_value_to_resolved(kb, subst, absent.clone());
    // Carrier-aware equality first (WI-486): the common case, and — outside
    // `Permission` — the whole of the verdict, exactly as before this ticket.
    if views_structurally_equal(kb, &p, &a) {
        return true;
    }
    permission_entails(kb, subst, &p, &a)
}

/// WI-20260825-CBRSW — does performing `present` ENTAIL performing `absent`, for the one
/// label whose entailment proposal 064 defines?
///
/// `-Permission[Y]` forbids `Permission[X]` for every `X <: Y`, because an `X`
/// capability IS a `Y` capability. So the verdict compares the CAPABILITY ARGUMENTS,
/// `X <: Y`, and both labels must head at `anthill.prelude.Permission` for it to run at
/// all.
///
/// WHAT IT BUYS, and it is not hypothetical — MEASURED loading clean before this
/// function existed: a row carrying `-Permission[Model]` while acquiring
/// `Permission[GptModel]` (with `GptModel <: Model`). That is the privilege escalation
/// 064 names, and closing it is the whole reason `-Permission[Model]` is worth writing.
/// `permission_denial_is_not_evaded_by_a_sub_capability` is that program.
///
/// WHY NOT GENERAL, which is the part worth reading. The first cut asked
/// `types_compatible(absent, present)` for EVERY label — "the denied effect is subsumed
/// by the one actually present" — on the reasoning that 064's negative form should fall
/// out of the ordinary effect order. It does not, and TWO measured programs say so:
///
///   * `-Color` beside a supplied `Red` (with `Red provides Color`) LOADED CLEAN under
///     it. Performing `Red` plainly entails performing a `Color`, so the general rule
///     was not even catching the general case — its direction is the one `Permission`
///     needs, and `Permission` alone.
///   * `-Red` beside a supplied `Color` was newly REFUSED. That program loaded clean
///     before and should: performing some `Color` does not entail performing `Red`.
///
/// The reason is that ENTAILMENT and SUBSUMPTION run OPPOSITE ways for `Permission` and
/// the same way for an ordinary nominal label. `Permission` is declared CONTRAVARIANT
/// (a permission is a demand, and demands weaken as their subject widens), so
/// `Permission[Model] <: Permission[GptModel]` — while entailment runs COVARIANTLY in
/// the capability, since acquiring the sub-capability acquires the super. No single
/// reading of the subsumption order gives both families, which is why this compares the
/// ARGUMENTS directly rather than the labels. What a lacks constraint should mean for an
/// ordinary label under subtyping is a real question and is LEFT OPEN: it predates this
/// ticket (the `-Color`/`Red` program loads clean before and after), it is about every
/// label rather than this one, and no population in the tree exercises it.
///
/// THE ABSENT SIDE'S ARGUMENT DECIDES THE DEGENERATE CASES, and they are not symmetric:
///
///   * ABSENT with no argument — a bare `-Permission` — is the GENERAL DENIAL, *acquires
///     no authority whatsoever*, and forbids every capability at once. This is 064's
///     open question 1, and the answer is that the general denial needs no variable in a
///     lacks-constraint: it assumes neither a capability order nor a root.
///   * PRESENT with no argument names no capability, so nothing is decided and nothing
///     is refused — the conservative direction, and the one that cannot turn a loading
///     program into a refusal.
///   * Either side PARAMETRIC (`-Permission[?]`, a row parameter, an opened `Rho`) is
///     undecided for the same reason the override leg's effects-⊆ gate withholds there:
///     `types_compatible` would BIND the variable and report a contradiction the row
///     does not have. This is what leaves `-Permission[?]` inert — a trap, pinned and
///     documented as one by `a_variable_argument_in_a_lacks_constraint_constrains_
///     nothing`, with bare `-Permission` as the working spelling.
///
/// The probe substitution is a CLONE and is discarded: this is a test, not a commitment,
/// and both callers go on to make independent decisions.
fn permission_entails(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    present: &Value,
    absent: &Value,
) -> bool {
    // Head both labels FIRST — the cheap reject, and the common one, since most rows
    // carrying a `-X` at all carry no `Permission`.
    let head = |kb: &KnowledgeBase, v: &Value| match type_head(kb, v) {
        TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => {
            Some(kb.canonical_sort_sym(s))
        }
        _ => None,
    };
    let (Some(p_base), Some(a_base)) = (head(kb, present), head(kb, absent)) else {
        return false;
    };
    if p_base != a_base {
        return false;
    }
    let Some(perm) = kb.try_resolve_symbol("anthill.prelude.Permission") else {
        // No prelude `Permission` — nothing in this KB can name the label.
        return false;
    };
    if p_base != kb.canonical_sort_sym(perm) {
        return false;
    }
    // The capability slot, read from `Permission`'s DECLARATION rather than spelled `"T"`
    // here, so renaming it in permission.anthill moves both ends together — the same
    // discipline `check_effect_registration` keeps for `Effect`'s.
    let Some(param) = kb.type_params_of_sort(perm).first().cloned() else {
        return false;
    };
    let arg = |kb: &KnowledgeBase, v: &Value| extract_type_param(kb, v, &param);
    // A bare `-Permission` denies every capability; see the doc comment.
    let Some(a_arg) = arg(kb, absent) else {
        return true;
    };
    // A bare present `Permission` names none, so nothing is decided.
    let Some(p_arg) = arg(kb, present) else {
        return false;
    };
    if view_contains_type_param(kb, &p_arg) || view_contains_type_param(kb, &a_arg) {
        return false;
    }
    let mut probe = subst.clone();
    types_compatible(kb, &mut probe, &p_arg, &a_arg)
}

/// The self-contradiction-filtering decomposition used by the row subtype / unify
/// / merge callers: a row presenting AND absenting the same label (`{e, -e}`, the
/// WI-328 piece-d malformed shape) yields `None` — as does a genuinely malformed
/// row.
pub(super) fn decompose_effect_row(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    effects: &impl TermView,
) -> Option<(Vec<Value>, Vec<TermId>, Vec<Value>)> {
    let (present, tails, absent) = decompose_effect_row_raw(kb, subst, effects)?;
    if row_self_contradiction(kb, subst, &present, &absent).is_some() {
        return None;
    }
    Some((present, tails, absent))
}

// ── WI-067: guarded-effect discharge at a call site ────────────────
//
// The companion to `decompose_effect_row`: it collapses a `guarded` atom to a
// conservative `present` label (dropping the guard); discharge needs the guard
// back. Rather than widen `decompose_effect_row`'s return (and every one of its
// ~10 subtype/unify/merge callers, none of which discharge), the discharge path
// reads the guarded atoms separately here, refutes each, and removes the proven-
// dropped labels from the call's effect contribution. proposal 048 §"Typer
// delta"; 050 consumer 2 (effect discharge, Tier 1).

/// Collect the `(label, guard)` of every `guarded` atom in an effect row,
/// carrier-agnostically — the same `EffectExpression` algebra walk as
/// [`decompose_effect_row`], but gathering exactly the atoms that decompose
/// flattens to `present`. `guard` is the `List[reflect.Term]` value (read back
/// off the cons spine by [`guarded_atom_refuted`]).
pub(super) fn collect_guarded_atoms(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    effects: &impl TermView,
) -> Vec<(Value, Value)> {
    let label_key = kb.intern("label");
    let guard_key = kb.intern("guard");
    let tail_key = kb.intern("tail");
    let left_key = kb.intern("left");
    let right_key = kb.intern("right");

    let walked = walk_view(kb, subst, effects);
    let expr: Value = if let Some(e) = effects_rows_inner(kb, &walked) {
        e
    } else if value_is_bare_effect_expr(kb, &walked) {
        walked.clone()
    } else {
        return Vec::new();
    };

    let mut out: Vec<(Value, Value)> = Vec::new();
    let mut stack: Vec<Value> = vec![expr];
    while let Some(node_raw) = stack.pop() {
        let node = walk_value_to_resolved(kb, subst, node_raw);
        // Row tails / non-algebra leaves carry no guarded atom.
        if row_tail_termid(kb, &node).is_some() {
            continue;
        }
        if let Some(inner) = effects_rows_inner(kb, &node) {
            stack.push(inner);
            continue;
        }
        match resolved_functor_name(kb, &node) {
            Some("guarded") => {
                let label = named_child_value(kb, &node, label_key);
                let guard = named_child_value(kb, &node, guard_key);
                if let (Some(l), Some(g)) = (label, guard) {
                    out.push((l, g));
                }
            }
            Some("open") => {
                if let Some(t) = named_child_value(kb, &node, tail_key) {
                    stack.push(t);
                }
            }
            Some("merge") => {
                if let Some(r) = named_child_value(kb, &node, right_key) {
                    stack.push(r);
                }
                if let Some(l) = named_child_value(kb, &node, left_key) {
                    stack.push(l);
                }
            }
            // present / absent / empty_row / unknown: no guarded atom to collect
            // (an unknown shape is `decompose_effect_row`'s concern to reject).
            _ => {}
        }
    }
    out
}

/// The call substitution σ applied to a value precondition / guard / postcondition
/// GOAL, CARRIER-NEUTRALLY (WI-621): replace each callee parameter reference
/// `var_ref(s)` / bare `Ref(s)` / `Ident(s)` with the actual argument term `map[s]`
/// — a literal `5`, a threaded `Ref(b)` — so `div(a, 5)`'s guard `eq(b, 0)` becomes
/// the ground `eq(5, 0)` the resolver can refute by evaluation. Unlike
/// [`substitute_ref_syms`] (a param→param *rename* of effect labels), σ maps a param
/// to an arbitrary argument *term*, and the WHOLE `var_ref` node is replaced (WI-552
/// variable substitution), never recursed into.
///
/// A hash-consed `Value::Term` goal — the common case — substitutes in the term
/// world (hash-consed result, [`substitute_ref_terms_term`]): byte-identical to the
/// pre-WI-621 term path. A DENOTED `Value::Node` / value-carried `Value::Entity`
/// goal is walked through the View layer (the same traversal the discrimination tree
/// and [`views_structurally_equal`] run on) and rebuilt as a `Value::Entity`, with
/// the σ argument spliced as the `Value::term(map[s])` σ already holds. So a denoted
/// goal never reifies to a `TermId` (WI-348) and no term↔occurrence conversion is
/// introduced — a transient goal is legitimately a non-hash-consed carrier (the
/// Representation note: it indexes / matches identically). The resolver end
/// ([`prove_from_gamma`] / [`refute_guard`] / [`FlowEnv::assume`]) already takes
/// `&Value`, so the result feeds it directly.
pub(crate) fn substitute_ref_terms(
    kb: &mut KnowledgeBase,
    goal: &Value,
    map: &HashMap<Symbol, TermId>,
) -> Value {
    if map.is_empty() {
        return goal.clone();
    }
    let var_ref_sym = kb.resolve_symbol("anthill.reflect.Expr.var_ref");
    substitute_ref_terms_value_rec(kb, goal, map, var_ref_sym)
}

/// σ over a hash-consed goal TERM — the term-world core of [`substitute_ref_terms`],
/// kept as a direct `TermId → TermId` entry for the term-based contract proof pass
/// ([`crate::kb::proof_verify`], which skolemizes and symbolically executes a body in
/// term-land) and reused by the `Value::Term` fast path of the carrier-neutral entry.
pub(crate) fn substitute_ref_terms_term(
    kb: &mut KnowledgeBase,
    term: TermId,
    map: &HashMap<Symbol, TermId>,
) -> TermId {
    let var_ref_sym = kb.resolve_symbol("anthill.reflect.Expr.var_ref");
    substitute_ref_terms_rec(kb, term, map, var_ref_sym)
}

/// The carrier-neutral σ walk backing [`substitute_ref_terms`]. A `Value::Term`
/// subtree grounds in the term world (hash-consed); a `Value::Node` / `Value::Entity`
/// node is read through the View layer and rebuilt as a `Value::Entity` with each
/// child substituted — no reification of the goal, no term↔occurrence conversion.
fn substitute_ref_terms_value_rec(
    kb: &mut KnowledgeBase,
    v: &Value,
    map: &HashMap<Symbol, TermId>,
    var_ref_sym: Symbol,
) -> Value {
    // A hash-consed term subtree grounds in term-land (hash-consed result),
    // byte-identical to the pre-WI-621 term path — the common goal carrier.
    if let Value::Term { id, .. } = v {
        return Value::term(substitute_ref_terms_rec(kb, *id, map, var_ref_sym));
    }
    match v.head(kb) {
        // A binder / parameter `var_ref(name: Ref(s))`: replace the WHOLE node when
        // `s ∈ σ` (WI-552 variable substitution — never recurse into the `name`
        // child, which would corrupt the wrapper). An unmapped `var_ref` stays
        // intact: the open-world parameter the resolver flounders on.
        ViewHead::Functor {
            functor: Some(f), ..
        } if f == var_ref_sym => {
            match view_var_ref_name(kb, v) {
                Some(s) => map
                    .get(&s)
                    .map(|&t| Value::term(t))
                    .unwrap_or_else(|| v.clone()),
                // A `var_ref`'s `name` child is always `Ref(sym)` by construction
                // (`occ_head` exposes `Expr::Ref`); a `None` here means a malformed
                // binder reached σ — surface it loudly, mirroring the term-side
                // `substitute_ref_terms_rec` (repo principle: loud over silent).
                // Release keeps the conservative `v`.
                None => {
                    debug_assert!(
                        false,
                        "substitute_ref_terms: var_ref with a non-symbol `name` child"
                    );
                    v.clone()
                }
            }
        }
        // A bare global / parameter reference: substitute if mapped, else keep.
        //
        // WI-20260902-CZJ2N — THE ARITY PIN IS THE OLD `ViewHead::Ref`, and it must
        // stay AHEAD of the general `Functor` arm below: without it a bare `Ref(p)`
        // would fall through to the rebuild arm, which recurses over zero children and
        // hands back an un-substituted name.
        ViewHead::Ident(s) => map
            .get(&s)
            .map(|&t| Value::term(t))
            .unwrap_or_else(|| v.clone()),
        ViewHead::Functor {
            functor: Some(s),
            pos_arity: 0,
            named_arity: 0,
        } => map
            .get(&s)
            .map(|&t| Value::term(t))
            .unwrap_or_else(|| v.clone()),
        // A functor application on a non-Term carrier (a denoted `Value::Node` goal,
        // or a value-carried `Value::Entity`): rebuild carrier-neutrally as a
        // `Value::Entity`, substituting each child read through the View layer, so a
        // Node or Entity goal decomposes identically to its term twin. Named args are
        // re-canonicalized (`canonicalize_record_named_args`) — the invariant the order-
        // sensitive discrimination tree matches against, which a non-entity-functor
        // Node goal's source-order named children would otherwise violate.
        ViewHead::Functor {
            functor: Some(f),
            pos_arity,
            ..
        } => {
            let pos = subst_view_pos(kb, v, pos_arity, map, var_ref_sym);
            let mut named = subst_view_named(kb, v, map, var_ref_sym);
            kb.canonicalize_record_named_args(f, &mut named);
            Value::Entity {
                functor: f,
                pos: std::rc::Rc::from(pos),
                named: std::rc::Rc::from(named),
            }
        }
        // A functor-LESS aggregate with children — a native `Value::Tuple`: rebuild a
        // `Value::Tuple`, substituting each child, so a σ-parameter nested in a tuple
        // operand grounds exactly as the term-side walk recurses through a tuple
        // `Term::Fn`. A childless `Functor{None}` (`Value::Unit` / empty tuple) has no
        // parameter to ground and rides the verbatim `_` arm below.
        ViewHead::Functor {
            functor: None,
            pos_arity,
            named_arity,
        } if pos_arity + named_arity > 0 => {
            let pos = subst_view_pos(kb, v, pos_arity, map, var_ref_sym);
            let named = subst_view_named(kb, v, map, var_ref_sym);
            Value::Tuple {
                pos: std::rc::Rc::from(pos),
                named: std::rc::Rc::from(named),
            }
        }
        // A childless aggregate (Unit / empty tuple), literal, var, bottom, or opaque
        // head carries no σ-substitutable reference — keep it verbatim.
        _ => v.clone(),
    }
}

/// Substitute σ into each POSITIONAL child of a View, in one pass: `.to_value()`
/// materializes each child owned, ending the immutable View borrow of `v` / `kb`
/// before the `&mut kb` recursion (the borrow shape [`child_types_pos`] uses).
fn subst_view_pos(
    kb: &mut KnowledgeBase,
    v: &Value,
    pos_arity: usize,
    map: &HashMap<Symbol, TermId>,
    var_ref_sym: Symbol,
) -> Vec<Value> {
    let mut pos = Vec::with_capacity(pos_arity);
    for i in 0..pos_arity {
        let child = v.pos_arg(kb, i).expect("pos_arg within arity").to_value();
        pos.push(substitute_ref_terms_value_rec(kb, &child, map, var_ref_sym));
    }
    pos
}

/// Substitute σ into each NAMED child of a View, in one pass (keys in the View's
/// `named_keys` order; the `Value::Entity` caller re-canonicalizes before storing,
/// the `Value::Tuple` caller keeps positional-as-named order).
fn subst_view_named(
    kb: &mut KnowledgeBase,
    v: &Value,
    map: &HashMap<Symbol, TermId>,
    var_ref_sym: Symbol,
) -> Vec<(Symbol, Value)> {
    let keys = v.named_keys(kb);
    let mut named = Vec::with_capacity(keys.len());
    for k in keys {
        let child = v.named_arg(kb, k).expect("named key present").to_value();
        named.push((
            k,
            substitute_ref_terms_value_rec(kb, &child, map, var_ref_sym),
        ));
    }
    named
}

/// Read the binder symbol `s` from a `var_ref(name: Ref(s))` occurrence / term
/// through the View layer — the carrier-neutral peer of [`var_ref_name_symbol`]: the
/// `name` child heads as `Ref(s)`, whose [`ViewHead::functor_sym`] is `s`.
fn view_var_ref_name(kb: &KnowledgeBase, v: &Value) -> Option<Symbol> {
    let name_key = kb.lookup_symbol("name")?;
    v.named_arg(kb, name_key)?.head(kb).functor_sym()
}

/// WI-552: σ as a proper VARIABLE substitution. A binder/parameter occurrence is
/// `var_ref(name: Ref(s))`; when `s` is in the σ domain, the WHOLE `var_ref` node
/// is replaced by the bound argument term — never recursed into (recursing would
/// rewrite the `name` child and corrupt the wrapper, e.g. `var_ref(name: 0)`). A
/// `var_ref` over a symbol absent from σ is left intact — the surviving open-world
/// parameter the resolver flounders on. A bare `Ref` / `Ident` (a global) still
/// substitutes directly if mapped (e.g. a spec type-param binding), else stays.
fn substitute_ref_terms_rec(
    kb: &mut KnowledgeBase,
    term: TermId,
    map: &HashMap<Symbol, TermId>,
    var_ref_sym: Symbol,
) -> TermId {
    rewrite_term_leaves(kb, term, &|kb, t| match kb.get_term(t) {
        Term::Ref(s) | Term::Ident(s) => Some(map.get(s).copied().unwrap_or(t)),
        Term::Fn {
            functor,
            named_args,
            ..
        } if *functor == var_ref_sym => Some(match var_ref_name_symbol(kb, named_args) {
            Some(s) => map.get(&s).copied().unwrap_or(t),
            // A `var_ref`'s `name` child is always `Ref(sym)` by construction
            // ([`KnowledgeBase::make_var_ref_term`]). A `None` here means a
            // malformed binder reached σ — surface it loudly rather than
            // silently leaving an un-substitutable node (repo principle: loud
            // error over silent skip). Release keeps the conservative `term`.
            None => {
                debug_assert!(
                    false,
                    "substitute_ref_terms: var_ref with a non-symbol `name` child"
                );
                t
            }
        }),
        _ => None,
    })
}

/// Read the binder symbol `s` from a `var_ref(name: Ref(s))` term's `name` child.
/// Returns `None` for a malformed / absent `name` (the caller then leaves the
/// `var_ref` intact rather than substituting).
pub(super) fn var_ref_name_symbol(kb: &KnowledgeBase, named_args: &[(Symbol, TermId)]) -> Option<Symbol> {
    let name_key = kb.lookup_symbol("name")?;
    let child = named_args
        .iter()
        .find(|(k, _)| *k == name_key)
        .map(|(_, v)| *v)?;
    match kb.get_term(child) {
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        _ => None,
    }
}

/// Is a SINGLE conjunct (a guard / precondition goal) constructively REFUTED under
/// σ + Γ? The per-conjunct core shared by the guarded-effect drop
/// ([`guarded_atom_refuted`], where a refutation DROPS the effect) and the
/// value-precondition violation check ([`precondition_refuted`], where it RAISES) —
/// one computation, opposite actions — so the two can never diverge on σ-grounding
/// or on who decides equality.
///
/// σ grounds the goal over the actual arguments: a parameter `var_ref(b)` whose
/// argument is a concrete literal becomes that literal (refutes by evaluation); one
/// with no clean arg twin stays `var_ref(b)` — the open-world parameter the
/// resolver flounders on, so nothing is refuted. The goal already carries `var_ref`
/// for its binders from load (WI-552); σ substitutes the whole variable. Returns
/// `true` only on a DECIDED refutation — a symbolic float, or an `eq`/`neq` the
/// resolver leaves undecided, yields `false`.
///
/// WI-755/WI-1125 — THE OVERRIDE FLOOR IS THE RESOLVER'S, NOT A PRE-GATE HERE. WI-573 sat
/// a gate in front of [`refute_guard`] that suspended every `eq`/`neq` conjunct
/// whose operands could reach a carrier with its own equality, because `eq` was
/// then a purely STRUCTURAL builtin whose refutation would have ignored the
/// override. WI-616 retired that premise: `eq`/`neq` are `BuiltinTag::SemEq`/`SemNeq`
/// and decide SEMANTICALLY (`resolve.rs` `sem_eq_values`) — a head-carrier override
/// over deep-ground operands DISPATCHES `<carrier>.eq(a,b)` by bounded
/// sub-resolution, a BURIED override or a non-ground operand DELAYS, and only a
/// wholly structural operand takes the structural verdict. The gate therefore
/// shadowed the very dispatch it was written to wait for: it short-circuited before
/// `refute_guard` → [`prove_from_gamma`] → resolver, so a guard could never reach
/// `SemEq`. The floor survives the removal because [`prove_from_gamma`] runs
/// `definite_only`, under which a builtin `Delay` yields NO solution (`resolve.rs`
/// `step_init` / the `Delay` arm) — so every case the gate suspended still returns
/// `false` here, now decided by the resolver rather than assumed by the typer.
///
/// WI-755 left ONE case behind — a carrier supplying a `neq` and no `eq`, which the
/// dispatch index does not key — as a narrowed residual gate here
/// (`guard_conjunct_reaches_undispatchable_neq`, with its own value scan and depth
/// cap). **WI-1125 deleted all of it**, by removing the shape rather than the gate:
/// a carrier supplying its own `neq` is now a load error
/// ([`crate::kb::load::LoadError::CarrierSuppliesNeq`]), so no program reaching this
/// function can hold an equality override the resolver cannot see. The gate had
/// covered the refutation route ALONE; the three other [`prove_from_gamma`] consumers
/// and the interpreter never had one and answered such a carrier structurally, which
/// is what made a floor here the wrong shape of fix — it was one consumer's guard
/// against a program the loader should never have accepted.
///
/// WATCH — WI-648 (scoped / non-canonical instances). A refutation now depends on
/// WHICH `eq` is the carrier's, which today is a global fact: instance coherence
/// gives exactly one provider per (spec, carrier), so the eq-dispatch index has one
/// answer and a guarded effect's presence is a property of the program. Under
/// non-canonical instances it would become a property of the SCOPE the call sits
/// in, and an effect row inferred here is read by callers in other scopes — so
/// WI-648 must say which instance a discharge is entitled to consult before this
/// site can keep deciding.
fn conjunct_refuted(
    kb: &mut KnowledgeBase,
    flow: &FlowEnv,
    sigma: &HashMap<Symbol, TermId>,
    conj: &Value,
) -> bool {
    let conj = substitute_ref_terms(kb, conj, sigma);
    refute_guard(kb, flow, &conj)
}

/// Is a guarded atom's guard `G` REFUTED (so the effect drops)? `G` is a
/// conjunction `g1 ∧ … ∧ gn` (its `List[reflect.Term]` Horn body), and
/// `¬(g1 ∧ … ∧ gn)` follows from refuting ANY single conjunct — so the effect
/// drops as soon as one `gᵢ`, after σ-substitution, is constructively refuted
/// from Γ ([`conjunct_refuted`] → [`refute_guard`], never NAF). The empty guard
/// (`:- true`) has no conjunct to refute and is irrefutable — kept present (sound).
fn guarded_atom_refuted(
    kb: &mut KnowledgeBase,
    flow: &FlowEnv,
    sigma: &HashMap<Symbol, TermId>,
    guard_value: &Value,
) -> bool {
    // Read the guard's `List[reflect.Term]` conjunction CARRIER-AGNOSTICALLY: a
    // GROUND-label atom (`Error[D] :- eq(b,0)`) hash-conses its guard as a
    // `Value::Term` cons list; a DENOTED-label (Node-carried) atom
    // (`Modify[c] :- eq(b,0)`) stores it via `build_value_list` as a
    // `Value::Entity` value-cons spine — but its goal heads are still
    // `Value::Term`. An unexpected carrier keeps the effect (sound).
    let goals: Vec<Value> = match guard_value {
        Value::Term { id: t, .. } => list_to_vec(kb, *t).into_iter().map(Value::term).collect(),
        Value::Node(occ) => {
            let t = crate::kb::node_occurrence::occurrence_to_term(kb, occ);
            list_to_vec(kb, t).into_iter().map(Value::term).collect()
        }
        Value::Entity { .. } => crate::kb::op_info::value_list_to_vec(kb, guard_value),
        _ => return false,
    };
    // `¬(g1 ∧ … ∧ gn)` follows from refuting ANY single conjunct, so the effect
    // drops as soon as one gᵢ is constructively refuted from Γ (`conjunct_refuted`,
    // never NAF). The empty guard (`:- true`) has no conjunct — irrefutable, kept.
    // Each list element is a single conjunct goal `Value`; ground + refute it via
    // the shared per-conjunct core carrier-neutrally (WI-621 — no reification).
    goals.iter().any(|g| conjunct_refuted(kb, flow, sigma, g))
}

/// The `(eq, neq)` spec-op functor symbols (`anthill.prelude.PartialEq.{eq,neq}` —
/// WI-644 moved them off `Eq` onto its base); `neq` is `None` in a prelude-less KB.
/// The single source for the eq/neq family pair. WI-1125 left [`negate_goal`]'s
/// `eq ⇄ neq` swap as the only reader — the second one, WI-755's undispatchable-`neq`
/// floor, went with the shape it guarded (a carrier-supplied `neq` is now refused at
/// load, [`crate::kb::load::LoadError::CarrierSuppliesNeq`]).
pub(super) fn eq_neq_functors(kb: &mut KnowledgeBase) -> (Symbol, Option<Symbol>) {
    (
        kb.eq_functor(),
        kb.try_resolve_symbol("anthill.prelude.PartialEq.neq"),
    )
}

/// Build the call substitution σ: callee parameter ↦ the actual argument's
/// goal-term twin (`try_occurrence_to_term`). Used by guard discharge to ground
/// a guard over the actual arguments before refuting it. An argument without a
/// clean term twin (a computed, opaque expression) is absent from σ — its param
/// stays symbolic, so its guard flounders and the effect is conservatively kept.
pub(super) fn build_call_guard_sigma(
    kb: &mut KnowledgeBase,
    params: &[(Symbol, Value)],
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> HashMap<Symbol, TermId> {
    let mut sigma: HashMap<Symbol, TermId> = HashMap::new();
    for (i, arg_occ) in pos_args.iter().enumerate() {
        if let Some((param_sym, _)) = params.get(i) {
            if let Some(t) = crate::kb::node_occurrence::try_occurrence_to_term(kb, arg_occ) {
                sigma.insert(*param_sym, t);
            }
        }
    }
    for (arg_name, arg_occ) in named_args {
        if let Some((param_sym, _)) = match_named_arg_param(kb, params, *arg_name) {
            let param_sym = *param_sym;
            if let Some(t) = crate::kb::node_occurrence::try_occurrence_to_term(kb, arg_occ) {
                sigma.insert(param_sym, t);
            }
        }
    }
    sigma
}

/// Is a STANDALONE guarded atom's guard refuted under σ + Γ? Reads the atom's
/// `guard` child and refutes its conjunction via [`guarded_atom_refuted`].
pub(super) fn guarded_atom_value_refuted(
    kb: &mut KnowledgeBase,
    flow: &FlowEnv,
    subst: &Substitution,
    sigma: &HashMap<Symbol, TermId>,
    atom: &Value,
) -> bool {
    let guard_key = kb.intern("guard");
    let walked = walk_value_to_resolved(kb, subst, atom.clone());
    match named_child_value(kb, &walked, guard_key) {
        Some(guard) => guarded_atom_refuted(kb, flow, sigma, &guard),
        None => false,
    }
}

/// Drop, from a row's already-flattened `present` labels, the label of every
/// guarded atom inside that row whose σ(guard) is refuted from Γ. The flatten
/// ([`effect_row_present_values`]) left a guarded atom's label conservatively
/// present (WI-478); discharge removes only the proven-dropped ones, matching by
/// the carrier-aware [`resolved_labels_equal`].
pub(super) fn drop_refuted_guarded_labels(
    kb: &mut KnowledgeBase,
    flow: &FlowEnv,
    subst: &Substitution,
    sigma: &HashMap<Symbol, TermId>,
    row: &Value,
    present: &mut Vec<Value>,
) {
    let guarded = collect_guarded_atoms(kb, subst, row);
    let mut dropped: Vec<Value> = Vec::new();
    for (label, guard) in guarded {
        if guarded_atom_refuted(kb, flow, sigma, &guard) {
            dropped.push(label);
        }
    }
    // Remove ONE present entry per refuted guarded atom — NOT every entry with
    // that label. A row may carry the same label both unconditionally and
    // guarded (`{ Boom, Boom :- eq(b, 0) }`, or two guards on one label — the
    // unreduced disjunction the 048 merge keeps); the flatten collapsed each to a
    // `present(Boom)`, so a blanket `retain` would drop the UNCONDITIONAL twin too
    // and unsoundly lose a real effect. Removing one occurrence per proven-dropped
    // guard leaves exactly the still-present labels.
    for d in &dropped {
        if let Some(pos) = present
            .iter()
            .position(|e| resolved_labels_equal(kb, subst, e, d))
        {
            present.remove(pos);
        }
    }
}

/// WI-539: is a `requires` clause a VALUE precondition (a goal over the op's
/// parameters, e.g. `not(empty(s))` / `neq(b, 0)`) rather than a spec / typeclass
/// requirement (`Spec[C=T]`, the auto-inferred `EffectsRuntime[…]`)? Only value
/// preconditions are proved against Γ at a call site; a spec requirement's head
/// resolves to a `Sort` and is satisfied by dispatch / coverage (WI-343 / WI-325),
/// never by `prove_from_gamma`. A clause with no functor head is conservatively
/// NOT treated as a value precondition (left to the other checks).
pub(crate) fn is_value_precondition_clause(kb: &KnowledgeBase, clause: &Value) -> bool {
    match clause.head(kb) {
        ViewHead::Functor {
            functor: Some(f), ..
        } => kb.kind_of(f) != Some(crate::intern::SymbolKind::Sort),
        _ => false,
    }
}

/// WI-539: split a `requires`/`ensures` clause term into its conjuncts. The loader
/// lowers several comma-separated goals on ONE clause as a single
/// `conjunction(g1, …, gn)` term (`convert_clause_list`); a single goal is itself.
/// Mirrors [`push_op_requires_clause`] (which flattens the same shape) and
/// [`guarded_atom_refuted`]'s per-conjunct walk — without the split a multi-goal
/// clause would be proved / assumed as one opaque `conjunction(...)` goal that no
/// SLD rule resolves (a spurious failure for a `requires`, an inert fact for an
/// `ensures`).
pub(crate) fn clause_conjuncts(kb: &KnowledgeBase, clause: &Value) -> Vec<Value> {
    // Carrier-neutral (WI-621): read the head through the View layer, so a `Term`,
    // `Node`, or `Entity` `conjunction(g1, …, gn)` decomposes identically into its
    // goal `Value`s (each carrier-faithful — a `Node` conjunct stays an occurrence).
    if let ViewHead::Functor {
        functor: Some(f),
        pos_arity,
        ..
    } = clause.head(kb)
    {
        if kb.local_name_of(f) == "conjunction" {
            // Every slot `i < pos_arity` is present by the View's own arity report;
            // `.expect` (never `filter_map`) so a hole surfaces loudly rather than
            // silently dropping a conjunct — a dropped `requires`/guard conjunct would
            // weaken the obligation with no diagnostic (repo: loud over silent).
            return (0..pos_arity)
                .map(|i| {
                    clause
                        .pos_arg(kb, i)
                        .expect("pos_arg within arity")
                        .to_value()
                })
                .collect();
        }
    }
    vec![clause.clone()]
}

/// WI-539: does a goal `view` reference any of `syms` (the callee's parameter
/// symbols)? Used to keep an assumed `ensures` fact CALLER-CLOSED: after σ a conjunct
/// still naming a callee parameter (an argument with no clean term twin, so
/// `build_call_guard_sigma` omitted it) is DROPPED, not assumed. The parameter symbol
/// `<callee>.p` is SHARED across every call to that callee, so a fact over it would
/// let a SECOND same-callee call's guard / `requires` query — which builds the
/// identical `<callee>.p` reference — spuriously match (an unsound proof / effect
/// drop). Dropping it is a conservative miss, never a false proof.
///
/// Carrier-neutral (WI-621): reads through the View layer, so it finds a parameter
/// spelled as a bare `Ref` / `Ident`, or nested inside its `var_ref(name: Ref(p))`
/// wrapper (the named `name` child heads as `Ref(p)`), across a `Term`, `Node`, or
/// `Entity` conjunct alike. A functor SYMBOL is not a reference (a param can't be a
/// functor), matching the term-world predicate it replaces.
fn view_references_any<V: TermView>(kb: &KnowledgeBase, view: &V, syms: &[Symbol]) -> bool {
    match view.head(kb) {
        ViewHead::Ident(s) => syms.contains(&s),
        // WI-20260902-CZJ2N — the NULLARY arm is the retired `ViewHead::Ref`, and it
        // must precede the recursing arm below: a bare `Ref(p)` has no children, so
        // falling through would answer `false` for the very shape this looks for.
        // The doc's "a functor SYMBOL is not a reference" still holds — at arity > 0.
        ViewHead::Functor {
            functor: Some(s),
            pos_arity: 0,
            named_arity: 0,
        } => syms.contains(&s),
        ViewHead::Functor { pos_arity, .. } => {
            view_any_child(kb, view, pos_arity, |c| view_references_any(kb, c, syms))
        }
        _ => false,
    }
}

/// WI-9PGCM / WI-K88TN: is this `requires` goal UNDETERMINED after the call's type
/// substitution — i.e. does it still carry a logical variable NOBODY has decided and
/// nobody yet can? The obligation's third state: not proved, not refuted, nothing yet
/// to be right or wrong about (WI-067 / WI-292). Handing such a goal to
/// [`prove_from_gamma`] is what made the obligation vacuous: the resolver witnesses
/// a free variable EXISTENTIALLY and reports the clause proved off a fact about some
/// OTHER label.
///
/// A SKOLEM IS DECIDED, AND EVERY OTHER VAR KIND IS NOT (WI-K88TN, reversing what
/// WI-9PGCM first shipped here). The question this asks is WI-1059's DETERMINED
/// reading, not its CONCRETE one — "is anything left for a later pass to decide?",
/// not "does this mention a type parameter" — and the two answer oppositely on a
/// `Var::Rigid` (see [`type_value_is_ground_g`], where the same split is a
/// parameter). A rigid is the enclosing signature's own parameter, universally
/// quantified in this body by `rigidify_op_type_params` / `rigidify_unwritten_sort_
/// params`, whose doc states the rule this arm implements: "an unwritten parameter is
/// a NEW variable per instantiation, so the operation is universally quantified over
/// it and its body may only do what holds for EVERY value of it. Inside the body it
/// is therefore rigid; at a CALL it is flexible again and binds from the argument."
/// So `flows_to(?m, Public)` inside `relay(t: Text[L = ?m])` is `∀m. flows_to(m,
/// Public)` — a DECIDED proposition, and a false one — not an undetermined obligation
/// awaiting a caller.
///
/// THE VACUITY THIS GATE EXISTS TO STOP IS A FLEX HAZARD SPECIFICALLY, which is why
/// letting a rigid through to [`prove_from_gamma`] is sound rather than a reopening.
/// The resolver witnesses a FREE variable existentially — `flows_to(?l, Public)`
/// proves itself off `flows_to(Public, Public)` — but a skolem never binds
/// (`unify_concrete`: "a skolem must never bind ... unifies only with another Rigid
/// carrying the same id"), so `flows_to(Rigid(m), Public)` finds no such witness and
/// is unproved, exactly as `∀m` requires. What it CAN still prove is a genuinely
/// universal clause — a rule head's own flex var binds the skolem, which is ordinary
/// universal instantiation — so a wrapper whose obligation holds for every label needs
/// no `requires` line. That is why this falls through to the prover rather than to a
/// Γ-membership test, which would refuse such a wrapper for no reason (WI-K88TN
/// measured this departure from the ticket's prescribed "Γ ALONE, structural match").
///
/// REGIME (a), DECLARE-OR-REFUSE, is what that makes the pass do, and the alternative
/// was weighed and rejected on the corpus rather than on taste: inferring the floated
/// clause onto the enclosing signature (regime (b)) leaves the contract invisible at
/// the declaration §5.4 objects to, needs a call-graph fixpoint to stay modular, and
/// STILL needs this refusal for the residue — `f() = send(pick())` over a polymorphic
/// `pick() -> Text[L = ?k]` floats a clause naming a variable no signature binds, so
/// there is nowhere to infer it TO. The decisive precedent is that the other half of
/// the same clause list already runs (a): a body incurring an effect its signature
/// does not declare is refused `undeclared effect: …`, against `declared_canon` walked
/// through the same `op.rigidify`. `requires` and `effects` now agree.
///
/// A CARRIER THIS CANNOT FULLY READ WITHHOLDS, and that asymmetry is the whole
/// reason the entry is carrier-typed rather than generic over [`TermView`]. The View
/// surfaces an occurrence's children only for the `Expr` shapes `occ_pos_child` /
/// `occ_named_child` enumerate; a `NodeKind::Type` spine (an arrow's param / result /
/// effects, which `rewrite_type_occ_deep` walks on its own) is NOT among them, so for
/// a `Value::Node` "no children found" is not evidence of "no variable". The two
/// errors are not symmetric: a wrong TRUE floats an obligation (conservative), a
/// wrong FALSE hands a free-variable goal to the resolver and re-admits the exact
/// vacuity this gate exists to stop. So the Node arm answers `true` outright — the
/// same shape of argument [`type_contains_callable`] makes for its own unreadable
/// carrier. (Reachability: a post-σ_type clause is `Value::Term` or `Value::Node` and
/// nothing else — `op.requires` carries only those two, and `walk_type_deep_value`
/// preserves the carrier — so the wildcard is the Node case plus an impossible one.)
///
/// NOT [`view_references_any`]'s twin despite the shape: that one only DROPS an
/// assumed fact, so its under-collection is safe in the direction this one's is not.
pub(super) fn value_carries_undecided_var(kb: &KnowledgeBase, clause: &Value) -> bool {
    match clause {
        Value::Term { .. } => view_carries_undecided_var(kb, clause),
        _ => true,
    }
}

/// The structural scan behind [`value_carries_undecided_var`], on the one carrier whose
/// children the View reports in full. A functor SYMBOL is not a variable; only the
/// argument positions are walked.
///
/// A `Var::Rigid` is NOT undecided, and that one arm is WI-K88TN's whole regime choice —
/// see [`value_carries_undecided_var`]'s doc for why the skolem falls on this side. Every
/// other var kind is: a flex `Global` is an inference variable a later pass may still
/// solve, and a `DeBruijn` is a bound variable awaiting opening. Both keep the float.
fn view_carries_undecided_var<V: TermView>(kb: &KnowledgeBase, view: &V) -> bool {
    match view.head(kb) {
        ViewHead::Var(v) => !v.is_rigid(),
        ViewHead::Functor { pos_arity, .. } => {
            view_any_child(kb, view, pos_arity, |c| view_carries_undecided_var(kb, c))
        }
        _ => false,
    }
}

/// WI-K88TN — WHICH RIGIDS a judged clause carries, read as the repair the author is
/// owed. The complement of [`value_carries_undecided_var`] over the SAME structure, and
/// deliberately not its negation: a clause with no variables at all is `None` here and
/// `false` there, which is the ordinary ground call-site failure.
///
/// The three answers are [`PreconditionFailure`]'s three cases, and the split that
/// matters is inside the rigids: one that a signature in scope BINDS is declarable, one
/// that nothing binds is an existential witness and is not. See
/// [`PreconditionFailure::UndischargeableWitness`] for why a `Var::Rigid` alone cannot
/// answer this — two producers, opposite quantifiers.
///
/// A clause carrying BOTH kinds answers `Undischargeable`: a declaration could name the
/// parameter half and still could not name the witness, so the declarable answer would
/// prescribe a line that does not fix it.
///
/// An unreadable carrier answers `None` — the call-site message rather than a wrong
/// verdict — and a `Value::Node` never reaches it, since the gate above floats that
/// carrier whole.
pub(super) fn clause_rigid_kind(
    kb: &KnowledgeBase,
    env: &TypingEnv,
    clause: &Value,
) -> Option<ClauseRigids> {
    let Value::Term { .. } = clause else {
        return None;
    };
    let mut found = None;
    view_scan_rigids(kb, env, clause, &mut found);
    found
}

/// What [`clause_rigid_kind`] found, worst case winning.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) enum ClauseRigids {
    /// Every rigid is a parameter of a signature in scope — declarable.
    AllParams,
    /// At least one rigid is bound by nothing in scope.
    HasWitness,
}

/// The structural scan behind [`clause_rigid_kind`]; see [`view_carries_undecided_var`],
/// whose walk this mirrors at the rigid test. `HasWitness` is absorbing, so the scan
/// still visits every position rather than stopping at the first rigid.
fn view_scan_rigids<V: TermView>(
    kb: &KnowledgeBase,
    env: &TypingEnv,
    view: &V,
    found: &mut Option<ClauseRigids>,
) {
    match view.head(kb) {
        ViewHead::Var(v) => {
            let Some(vid) = v.as_rigid() else { return };
            let kind = if env.param_rigids().iter().any(|(g, rigid)| {
                *g == vid || matches!(kb.get_term(*rigid), Term::Var(Var::Rigid(rv)) if *rv == vid)
            }) {
                ClauseRigids::AllParams
            } else {
                ClauseRigids::HasWitness
            };
            if kind == ClauseRigids::HasWitness || found.is_none() {
                *found = Some(kind);
            }
        }
        ViewHead::Functor { pos_arity, .. } => {
            for i in 0..pos_arity {
                if let Some(c) = view.pos_arg(kb, i) {
                    view_scan_rigids(kb, env, &c, found);
                }
            }
            for &k in view.named_keys(kb).iter() {
                if let Some(c) = view.named_arg(kb, k) {
                    view_scan_rigids(kb, env, &c, found);
                }
            }
        }
        _ => {}
    }
}

/// WI-9PGCM — a goal in the spelling its SOURCE used, for a diagnostic: every
/// `var_ref(name: c)` binder wrapper unwrapped back to the bare `c`.
///
/// The wrapper is the WI-552 lowering of a parameter reference and is invisible in
/// source, so a message carrying it (`precondition \`neq(var_ref(name: c), Red)\``)
/// leaks the loader's internals at exactly the moment a reader is trying to match
/// the text against the line they wrote. Stripping it HERE, once, at the error's one
/// construction site, is what lets the report keep using [`TermPrinter`] — the
/// general `.anthill` term printer — for everything else rather than growing a
/// second renderer that would have to re-decide how every literal and carrier
/// prints.
///
/// A non-`Term` carrier passes through untouched: it has no `TermId` and
/// [`format_precondition_clause`] renders it through the View layer instead.
pub(super) fn goal_in_source_spelling(kb: &mut KnowledgeBase, clause: &Value) -> Value {
    let Value::Term { id, .. } = clause else {
        return clause.clone();
    };
    // BOTH lookups are the NON-ASSERTING readers, and a renderer is exactly where
    // that matters: this runs only while a diagnostic is being built, so a panic here
    // would replace a load error with a crash. Absent either way means the KB never
    // built a `var_ref`, so the goal is already in source spelling. The keys differ in
    // kind — `var_ref` is a qualified name (`try_resolve_symbol`), while the wrapper's
    // `name` is a bare named-arg label, which only the raw intern reader finds and
    // which the asserting one panicked on (MEASURED — six `wi756` cases died there).
    // `view_var_ref_name` reads the same pair on the checking side.
    let Some(var_ref_sym) = kb.try_resolve_symbol("anthill.reflect.Expr.var_ref") else {
        return clause.clone();
    };
    let Some(name_key) = kb.lookup_symbol("name") else {
        return clause.clone();
    };
    let stripped = strip_var_ref_terms(kb, *id, var_ref_sym, name_key);
    Value::term(unrigidify_for_display(kb, stripped))
}

/// WI-K88TN — a `Var::Rigid` back to the `?m` its author wrote, for a diagnostic ONLY.
///
/// The term printer spells a rigid `!m` (`persistence/print.rs`), which is the right
/// rendering wherever the skolem-vs-flex distinction is the subject — but here it is
/// not. The `UndeclaredInWrapper` message's whole job is to quote the `requires` line
/// the author must add, and `requires allowed(!m, n)` is not a line anthill parses: the
/// source spelling of that variable is `?m`, and the skolemization is a fact about how
/// this pass checks the body, not about the declaration being asked for. Same argument
/// as [`goal_in_source_spelling`]'s own — the reader is matching this text against the
/// line they wrote — which is why it is the same pass, at the same single construction
/// site, and never on a term that is stored or compared.
///
/// A rigid and a flex carrying one name render alike afterwards, and in this diagnostic
/// that is the point rather than a loss: the clause is being shown as SOURCE, where
/// there is only one spelling.
fn unrigidify_for_display(kb: &mut KnowledgeBase, t: TermId) -> TermId {
    if let Term::Var(Var::Rigid(vid)) = kb.get_term(t) {
        let vid = *vid;
        return kb.alloc(Term::Var(Var::Global(vid)));
    }
    kb.map_fn_children(t, |kb, child| unrigidify_for_display(kb, child))
}

/// The term-world recursion behind [`goal_in_source_spelling`]. Share-preserving via
/// `map_fn_children` (an unchanged subtree keeps its `TermId`), so a goal with no
/// wrapper — the WI-9PGCM type-level case, whose variables σ_type already replaced
/// with concrete labels — costs a traversal and allocates nothing.
fn strip_var_ref_terms(
    kb: &mut KnowledgeBase,
    t: TermId,
    var_ref_sym: Symbol,
    name_key: Symbol,
) -> TermId {
    let Term::Fn {
        functor,
        named_args,
        ..
    } = kb.get_term(t)
    else {
        return t;
    };
    if *functor == var_ref_sym {
        // The `name` child is `Ref(sym)` by construction (WI-552). A wrapper without
        // one is malformed; keep it whole rather than dropping the operand — this is
        // a renderer, and losing a term here would silently shorten the report.
        if let Some((_, name)) = named_args.iter().find(|(k, _)| *k == name_key) {
            return *name;
        }
        return t;
    }
    kb.map_fn_children(t, |kb, child| {
        strip_var_ref_terms(kb, child, var_ref_sym, name_key)
    })
}

/// WI-539: does a callee's value precondition `clause` PROVE from Γ at the call,
/// after σ (callee params ↦ actual args)? The dual of [`guarded_atom_refuted`]:
/// where a guard DROPS on a refutation of `¬G`, a precondition must be positively
/// PROVED — so this calls [`prove_from_gamma`] (not [`refute_guard`]) on σ(clause),
/// canonicalizing a binder/parameter reference to its `var_ref` twin first (so the
/// goal unifies with the flow-narrowed Γ fact AND is the open-world parameter the
/// resolver flounders on — `definite_only` keeps an unestablished precondition
/// UNPROVED, the obligation default, never NAF-"true"). A literal argument grounds
/// the goal and proves by evaluation; a symbolic one flounders ⇒ unproved ⇒ error.
/// A multi-goal clause (`conjunction(…)`) holds iff EVERY conjunct proves.
pub(super) fn precondition_proved(
    kb: &mut KnowledgeBase,
    flow: &FlowEnv,
    sigma: &HashMap<Symbol, TermId>,
    clause: &Value,
) -> bool {
    // A multi-goal clause is `conjunction(g1, …)`; ALL conjuncts must prove
    // (split carrier-neutrally, WI-621). The clause carries `var_ref` for its
    // parameters from load (WI-552); σ substitutes a parameter variable whose actual
    // argument is concrete, and a parameter with no clean arg twin stays `var_ref` —
    // floundering under `definite_only`, so the precondition is unproved (the
    // obligation default). `is_value_precondition_clause` already gated `clause` to a
    // functor-headed goal, so an unreadable carrier simply fails to prove (the same
    // conservative UNPROVED default as the dual `guarded_atom_refuted`'s `false`).
    for conj in clause_conjuncts(kb, clause) {
        let conj = substitute_ref_terms(kb, &conj, sigma);
        if !prove_from_gamma(kb, flow, &conj) {
            return false;
        }
    }
    true
}

/// WI-K88TN — Γ₀ for an operation body: the operation's OWN value preconditions,
/// assumed.
///
/// Proposal 050 reads a `requires` as a Hoare precondition, and a precondition is an
/// ASSUMPTION inside the body it guards — the caller was made to prove it, so the body
/// may use it. Before this the body's Γ₀ was [`FlowEnv::empty`] and an operation could
/// not use what its own signature demanded; with the WI-K88TN gate split that stopped
/// being merely incomplete and became load-bearing, since a rigid obligation now has to
/// be DISCHARGED and the declaration is the only place the discharge can come from.
///
/// WALKED THROUGH `rigidify`, WHICH IS THE WHOLE REASON THIS IS NOT A ONE-LINER. The
/// body's obligation reaches the gate having been σ_type-walked into the body's
/// vocabulary, where the enclosing signature's parameters are skolems; the stored
/// `op.requires` still carries them as the flex vars the loader parsed. Assuming the
/// clause un-walked would file `flows_to(?m_flex, Public)` against a query
/// `flows_to(Rigid(m), Public)` — the Γ overlay is consulted STRUCTURALLY and keys a
/// rigid as `DiscrimKey::RigidVar` (see [`prove_from_gamma`]: "A Γ fact `neq(b, 0)`
/// over a rigid parameter `b` proves the query `neq(b, 0)` over the same `b`"), so the
/// two would not meet and the declared wrapper would be refused for writing exactly the
/// line the error told it to write. The declared-effects check walks both sides through
/// this same substitution for the same reason.
///
/// VALUE PRECONDITIONS ONLY, split per CONJUNCT by [`clause_conjuncts`] before
/// classifying (WI-862): a spec requirement (`requires Ord[T]`) is dispatched, never
/// proved from Γ, and assuming one would put a type precondition in the value prover's
/// reach — the precise confusion §5.4 calls "what a type precondition must never be".
///
/// A SECOND IMPLEMENTATION OF THIS IDEA EXISTS and the two should not drift:
/// `proof_verify.rs`'s contract-proof seeding builds the same Γ from the same operation's
/// value preconditions behind the same `is_value_precondition_clause` filter. It differs
/// only in the substitution it walks through — σ_value skolemization there, `rigidify`
/// here — because it is proving the contract from OUTSIDE while this assumes it from
/// INSIDE. If either grows a rule about WHICH clauses are assumable, the other wants it.
pub(super) fn op_requires_gamma(
    kb: &mut KnowledgeBase,
    requires: &[Value],
    rigidify: &Substitution,
) -> FlowEnv {
    let conjuncts: Vec<Value> = requires
        .iter()
        .flat_map(|c| clause_conjuncts(kb, c))
        .collect();
    let values: Vec<Value> = conjuncts
        .into_iter()
        .filter(|c| is_value_precondition_clause(kb, c))
        .collect();
    let mut flow = FlowEnv::empty();
    for c in values {
        let c = walk_type_deep_value(kb, rigidify, &c);
        flow = flow.assume(kb, c);
    }
    flow
}

/// WI-602 — is this value precondition DEFINITELY VIOLATED (ground-refuted) under
/// σ + Γ? The refutation dual of [`precondition_proved`]: a precondition
/// `g1 ∧ … ∧ gn` is VIOLATED iff `¬(g1 ∧ … ∧ gn)`, which follows from
/// constructively refuting ANY single conjunct ([`conjunct_refuted`] — the same
/// core the guarded-effect drop uses). This is the polarity opposite of
/// `precondition_proved` on TWO counts: it refutes rather than proves, and it holds
/// on ANY refuted conjunct (`.any`) rather than requiring EVERY conjunct proved.
///
/// An all-FLOATING precondition (every conjunct symbolic — the legitimate rule-body
/// case, `rule_body_value_precondition_dot_dispatches`) returns `false`
/// (UNDETERMINED, not violated), so the WI-557 rule-body skip stays intact for it;
/// a literal `guarded(_, 0)` (`neq(0,0)` ground-false) returns `true`. Only a
/// DECIDED violation raises — never an undetermined one (the WI-067/WI-292
/// polarity). A clause unreadable as a goal returns `false` (undetermined; matches
/// `precondition_proved`'s conservative unreadable default).
pub(super) fn precondition_refuted(
    kb: &mut KnowledgeBase,
    flow: &FlowEnv,
    sigma: &HashMap<Symbol, TermId>,
    clause: &Value,
) -> bool {
    clause_conjuncts(kb, clause)
        .iter()
        .any(|conj| conjunct_refuted(kb, flow, sigma, conj))
}

/// WI-539 (proposal 050 "operation call" modification rule, `ensures` half): if
/// `value_node` is a direct call `callee(args)` bound to `binder` (a `let`), assume
/// the callee's postconditions into Γ for the code after the binding — with σ
/// mapping the callee's parameters ↦ the actual argument terms AND `result` ↦
/// `var_ref(binder)`. So `let y = op(); …` where `op ensures neq(result, 0)`
/// contributes `neq(y, 0)`, the fact a later `div(_, y)` guard discharge (or a
/// `requires`-check) reads straight from Γ — contract knowledge flowing through Γ,
/// the main populator beyond branch conditions and bindings.
///
/// Independent of the binding-fact purity gate (a postcondition holds after the
/// call regardless of its effects). Each clause is split into conjuncts; its
/// parameter / `result` occurrences carry `var_ref` from load (WI-552), and σ
/// substitutes them as variables (`result` ↦ `var_ref(binder)`), so producer and
/// consumer speak one form. A conjunct that, after σ, still references a callee
/// PARAMETER (an argument with no clean term twin) is DROPPED rather than
/// assumed: the `<callee>.param` symbol is shared across calls, so assuming a fact
/// over it would let a second same-callee call's query spuriously match it
/// ([`view_references_any`], which finds the param inside its `var_ref` wrapper).
/// Returns Γ unchanged for a non-call value or a callee with no `ensures`.
pub(super) fn assume_call_ensures(
    kb: &mut KnowledgeBase,
    flow: FlowEnv,
    value_node: &Rc<NodeOccurrence>,
    binder: Symbol,
) -> FlowEnv {
    let (functor, pos_args, named_args) = match &value_node.kind {
        NodeKind::Expr {
            expr:
                Expr::Apply {
                    functor,
                    pos_args,
                    named_args,
                    ..
                },
            ..
        } => (*functor, pos_args.clone(), named_args.clone()),
        _ => return flow,
    };
    let Some(rec) = crate::kb::op_info::lookup_operation_info(kb, functor) else {
        return flow;
    };
    if rec.ensures.is_empty() {
        return flow;
    }
    // σ: callee params ↦ actual arg terms, plus `result` ↦ var_ref(binder). The
    // reserved `result` resolves under the op scope as `<op>.result` (proposal 041).
    let mut sigma = build_call_guard_sigma(kb, &rec.params, &pos_args, &named_args);
    let op_qn = kb.qualified_name_of(functor).to_string();
    if let Some(result_sym) = kb.try_resolve_symbol(&format!("{}.result", op_qn)) {
        let binder_term = kb.make_var_ref_term(binder);
        sigma.insert(result_sym, binder_term);
    }
    // The callee parameter symbols — a conjunct still naming one after σ is not
    // caller-closed and is dropped (sound: never assume over a shared `<op>.param`).
    let param_syms: Vec<Symbol> = rec.params.iter().map(|(s, _)| *s).collect();
    let ensures = rec.ensures.clone();
    let mut flow = flow;
    for clause in &ensures {
        for conj in clause_conjuncts(kb, clause) {
            let conj = substitute_ref_terms(kb, &conj, &sigma);
            if view_references_any(kb, &conj, &param_syms) {
                continue;
            }
            flow = flow.assume(kb, conj);
        }
    }
    flow
}

/// WI-441: the multi-tail arm shared by [`unify_effect_rows`] and
/// [`subtype_effect_rows`] — at least one side decomposed to ≥ 2 row tails
/// (a row UNION like `{E, EffP}`). Two sound moves, else reject:
///
/// 1. **Equal tail sets** (walked): the rows agree on the open part; the
///    relation holds iff the label extras allow it (`only_a` empty; for the
///    symmetric unify also `only_b`).
/// 2. **Bare-flexible absorb**: a side that is a SINGLE flexible tail with
///    no labels/absents binds WHOLESALE to the other row's inner expression
///    (the receiver-binding shape: `collect`'s `Eff` := `{E, EffP}`).
///    Guarded by occurs (the other side's tails must not contain the var)
///    and the var's `lacks` (each absorbed present label is checked; lacks
///    are propagated onto the absorbed row's flexible tails).
fn multi_tail_rows_compat(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_inner: Option<Value>,
    b_inner: Option<Value>,
    a_parts: (&[Value], &[TermId], &[Value]),
    b_parts: (&[Value], &[TermId], &[Value]),
    only_a: &[Value],
    only_b: &[Value],
    directional: bool,
) -> bool {
    let (a_present, a_tails, a_absent) = a_parts;
    let (b_present, b_tails, b_absent) = b_parts;
    let mut a_set: Vec<TermId> = a_tails.iter().map(|t| walk_type(kb, subst, *t)).collect();
    let mut b_set: Vec<TermId> = b_tails.iter().map(|t| walk_type(kb, subst, *t)).collect();
    a_set.sort_unstable_by_key(|t| t.raw());
    a_set.dedup();
    b_set.sort_unstable_by_key(|t| t.raw());
    b_set.dedup();
    if a_set == b_set {
        return if directional {
            only_a.is_empty()
        } else {
            only_a.is_empty() && only_b.is_empty()
        };
    }
    let absorb = |kb: &mut KnowledgeBase,
                  subst: &mut Substitution,
                  bare_tail: TermId,
                  other_inner: &Option<Value>,
                  other_present: &[Value],
                  other_tails: &[TermId]|
     -> bool {
        let Term::Var(Var::Global(vid)) = kb.get_term(bare_tail) else {
            return false;
        };
        let vid = *vid;
        if other_tails
            .iter()
            .any(|t| walk_type(kb, subst, *t) == bare_tail)
        {
            return false; // occurs guard
        }
        let Some(inner) = other_inner else {
            return false;
        };
        let lacks = subst.lacks_of(vid);
        if !lacks.is_empty() {
            for l in other_present {
                if label_violates_lacks(kb, subst, l, &lacks) {
                    return false;
                }
            }
            for t in other_tails {
                if let Term::Var(Var::Global(tvid)) = kb.get_term(*t) {
                    let tvid = *tvid;
                    subst.add_lacks(tvid, lacks.iter().cloned());
                }
                // A rigid tail can't carry the lacks — enforced at its own
                // instantiation site (same conservatism as the rigid-alias
                // arm in the single-tail case).
            }
        }
        subst.bind_value(kb, vid, inner.clone());
        !subst.is_contradiction()
    };
    if a_present.is_empty() && a_absent.is_empty() && a_set.len() == 1 {
        return absorb(kb, subst, a_set[0], &b_inner, b_present, b_tails);
    }
    if b_present.is_empty() && b_absent.is_empty() && b_set.len() == 1 {
        return absorb(kb, subst, b_set[0], &a_inner, a_present, a_tails);
    }
    false
}

/// WI-441: is this value a BARE `EffectExpression` node (`merge` / `present` /
/// `absent` / `open` / `empty_row`, matched by QUALIFIED functor)? A row var's
/// binding (`open(?ρ)` from `bind_row_tail`) and a walked bound row are bare
/// expressions, not `effects_rows` wrappers.
fn value_is_bare_effect_expr(kb: &KnowledgeBase, v: &impl TermView) -> bool {
    // WI-436: `empty_row` is a 0-ary constructor → bare `Ref` head; read the
    // functor symbol off either spelling so a bare empty row is still classified
    // as a bare EffectExpression node.
    v.head(kb).functor_sym().is_some_and(|sym| {
        matches!(
            kb.qualified_name_of(sym)
                .strip_prefix("anthill.prelude.EffectExpression."),
            // WI-478: a bare `guarded(…)` atom is a complete EffectExpression node
            // (kept in step with the same list in `explode_incurred_effect_row`), so
            // a top-level bare guarded atom is row-shaped and decomposes via the row
            // algebra rather than falling through as an opaque value.
            Some("merge" | "present" | "guarded" | "absent" | "open" | "empty_row")
        )
    })
}

/// WI-329 — the strictly NARROWER sibling of [`value_is_bare_effect_expr`]: the bare
/// `EffectExpression` shapes a BOUND ROW TAIL can walk to, and only those. `bind_row_tail`
/// builds `merge` / `present` / `open` / `empty_row` chains and nothing else, so those four
/// are what a row variable resolves into at a call site.
///
/// `guarded` and `absent` are EXCLUDED, and that exclusion is the point. They are ELEMENT
/// forms a written row contributes, each already owned by its own arm of the call-site
/// effect loop, and flattening either one LOSES information rather than exposing it:
/// a standalone `guarded(label, guard)` — how a partial primitive declares its single
/// effect (`div … effects { Error[…] :- eq(b, 0) }`) — flattens to its LABEL with the
/// GUARD DROPPED, so the enclosing operation's row could no longer carry the condition for
/// a later call site to discharge (WI-067/WI-478); and a bare `absent` flattens to NOTHING
/// at all, silently deleting the element. Reusing the WI-478 predicate here captured 12 of
/// the 15 standalone `guarded` elements in the `wi067` + `wi478` fixtures, and no test
/// could see it because both routes keep the label.
pub(super) fn value_is_bare_row_expr(kb: &KnowledgeBase, v: &impl TermView) -> bool {
    v.head(kb).functor_sym().is_some_and(|sym| {
        matches!(
            kb.qualified_name_of(sym)
                .strip_prefix("anthill.prelude.EffectExpression."),
            Some("merge" | "present" | "open" | "empty_row")
        )
    })
}

/// WI-441: row-shaped = an `effects_rows` wrapper OR a bare `EffectExpression`
/// node. A pair with a row-shaped side must compare via the FULL row algebra
/// (`unify_effect_rows` / `subtype_effect_rows`) — the structural fallback is
/// order-sensitive over `merge` and cannot equate `?ρ` with `open(?ρ)`.
pub(super) fn value_is_row_shaped(kb: &KnowledgeBase, v: &impl TermView) -> bool {
    if value_is_bare_effect_expr(kb, v) {
        return true;
    }
    matches!(
        v.head(kb),
        ViewHead::Functor { functor: Some(sym), .. }
            if kb.qualified_name_of(sym) == "anthill.prelude.TypeExtractor.EffectsRows"
    )
}

/// WI-441: a row value's INNER `EffectExpression` (the `effects_expr` child of
/// the `effects_rows` wrapper; a bare row Var / bare expression is itself the
/// inner). Used by the multi-tail wholesale absorb to bind a bare row var to
/// the OTHER row as-is — reassembling from decomposed parts cannot represent
/// two tails canonically.
fn row_inner_value(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    row: &impl TermView,
) -> Option<Value> {
    let walked = walk_view(kb, subst, row);
    // WI-493: unwrap via the single shared tolerance; a bare row Var / expression
    // (not a wrapper) is its own inner.
    Some(effects_rows_inner(kb, &walked).unwrap_or(walked))
}

/// A row-tail [`TermId`] if `node` resolves to a logic var, else `None`. A
/// `TermId`-carried var (any flavor — Global/Rigid/DeBruijn) returns its own
/// hash-consed id (preserving the pre-P4 tail classification); a `Value::Var`
/// or an occurrence-carried `TypeNode::Var` materializes to a hash-consed
/// `Term::Var` (row tails are plain vars).
///
/// WI-20260923-N3W68 (#5) — THE OCCURRENCE ARM, the third spelling of a variable
/// WI-20260904-02ERR gave [`resolved_var`] and [`walk_value_to_resolved`] and not this
/// reader. Without it an unbound `TypeNode::Var` at the TOP of a row decomposed as the
/// EMPTY row — a closed `{}` where an open tail stood, silently. (Inside the algebra the
/// same variable is read through `named_child_value`, which hands it back as a plain
/// variable, so only the top-level read was affected.) A producer exists
/// (`value_to_type_child` mints this carrier for a `Value::Var` in a type slot, e.g. the
/// arrow rebuild in `rigidify_unwritten_sort_params`), but MEASURED, nothing brings one
/// here: a temporary probe fired zero times across the stdlib, both example corpora and
/// the 7410-test workspace suite. The arm is the twin's, not a response to a failing
/// program.
fn row_tail_termid(kb: &mut KnowledgeBase, node: &Value) -> Option<TermId> {
    match node {
        Value::Term { id: t, .. } => match kb.get_term(*t) {
            Term::Var(_) => Some(*t),
            _ => None,
        },
        Value::Var(v) => Some(kb.alloc(Term::Var(*v))),
        Value::Node(occ) => match occ.as_type() {
            Some(TypeNode::Var(v)) => Some(kb.alloc(Term::Var(*v))),
            _ => None,
        },
        _ => None,
    }
}

/// A view's named child as an owned [`Value`] (frees the `kb` borrow). `key`
/// must already be interned (the caller interns the well-known field names).
///
/// `pub(crate)` since WI-SPGBP: `eval::builtins`' strict `List[String]` read walks a
/// cons spine carrier-agnostically and needs exactly this projection. Duplicating the
/// `ViewItem` → `Value` conversion there would have made a second place that decides
/// what a named child IS.
pub(crate) fn named_child_value(
    kb: &KnowledgeBase,
    v: &impl TermView,
    key: Symbol,
) -> Option<Value> {
    v.named_arg(kb, key).map(|it| view_item_value(&it))
}

/// Resolve two effect-row labels through `subst` and compare structurally via
/// the carrier-aware [`views_structurally_equal`] (WI-486) — a ground
/// `Value::Term` label and a structurally-equal `Value::Node` occurrence label
/// compare equal ACROSS carriers (the prior hand-rolled match returned `false`
/// for any cross-carrier pair). Used for the present/absent same-label
/// malformed-row check (NOT a unification — it must not bind variables).
pub(super) fn resolved_labels_equal(
    kb: &KnowledgeBase,
    subst: &Substitution,
    a: &Value,
    b: &Value,
) -> bool {
    let ra = walk_value_to_resolved(kb, subst, a.clone());
    let rb = walk_value_to_resolved(kb, subst, b.clone());
    // WI-486: one carrier-aware compare for all carriers — Term-vs-Term,
    // Node-vs-Node, AND the cross-carrier Term-vs-Node case the old hand-rolled
    // match silently returned `false` for.
    views_structurally_equal(kb, &ra, &rb)
}

/// A LABEL'S ARGUMENT IS A TYPE, AND TYPES SUBSUME — for the label sorts that say so.
///
/// `Error[T]`'s argument is a payload TYPE, so a boundary declared to handle `Wide`
/// admits a body raising `Narrow` when `Narrow <: Wide`: the Java/Scala catch rule, and
/// what makes a hierarchy of error types worth declaring. `Modify[p]`'s argument is a
/// PLACE — `effects.anthill`'s header is emphatic that it is never a type — so
/// subsumption is meaningless there and identity is the whole rule.
///
/// ONE CHECK, THREE KINDS OF ARGUMENT, and the existing variance facts tell them apart
/// (proposal 035: variance is a FACT, not a keyword). This leg runs only where a
/// `Covariant`/`Contravariant` fact is declared; no fact means invariant, which is
/// `Modify`'s rule and is already decided by the legs around this one. So `Modify` is
/// protected by the DEFAULT rather than by anyone remembering to protect it.
///
/// THE COVARIANT ARM IS THE ONE THAT ADMITS, though what it expresses is the
/// contravariant relation, and the flip is already applied by WHAT THIS COMPARES. "A
/// handler for `Wide` handles `Narrow`" is contravariance of the handler; but `a` here
/// is the body's ACTUAL label and `e` the callback parameter's DECLARED one, and being
/// a parameter is what turned the relation round before this function is reached. So
/// the direction wanted is `actual refines declared`, which is `Variance::Covariant`.
/// MEASURED: declaring `Contravariant(Error, T)` applies the flip twice and refuses
/// exactly the programs this admits.
///
/// NOMINAL AND SHALLOW, DELIBERATELY — via [`sort_refines`], not `types_compatible`,
/// and this is the whole reason the leg is written by hand rather than delegating to
/// `check_binding_by_variance` like `parameterized_compatible_view` does. That
/// delegation was the first shipped shape and it KILLED THE `wi_tests` BINARY: an
/// overflowed thread stack past its guard page, reported as
/// `malloc: Heap corruption detected / *** Incorrect guard value`, taking 4400 tests
/// down as collateral. Not a cycle — the same run passed 4417/0 under
/// `RUST_MIN_STACK=32M` — but DEPTH, because this site is already far down the typer's
/// expression walk and structural equality used to bottom out here. Attaching a full
/// compatibility descent at a former leaf is what cost the remaining budget.
/// `sort_refines` walks the flat `requires` chain instead: no descent into arrows or
/// nested parameterizations, no substitution to clone, and an immutable KB.
///
/// THE LIMIT THAT BUYS: only a PLAIN SORT REFERENCE on both sides subsumes.
/// `Error[List[T = X]]` against `Error[List[T = Y]]` falls back to the exact-match leg
/// above, even where `X` refines `Y`. A payload type is a sort in every case this rule
/// is for, so the restriction costs nothing today — and the day it does, the fix is to
/// bound the typer's compatibility walk (which carries no depth cap and no visited set,
/// unlike eval's `step_cap` / `depth_cap` and the bridge's `BRIDGE_REENTRY_CAP`), not
/// to widen this leg back onto an unbounded one.
pub(super) fn labels_match_by_subsumption(kb: &KnowledgeBase, a: &Value, e: &Value) -> bool {
    let base = |v: &Value| match type_head(kb, v) {
        TypeHead::SortRef(s) | TypeHead::Parameterized { base: s } => {
            Some(kb.canonical_sort_sym(s))
        }
        _ => None,
    };
    let (Some(a_base), Some(e_base)) = (base(a), base(e)) else {
        return false;
    };
    if a_base != e_base {
        return false;
    }
    // A plain sort REFERENCE only — see "the limit that buys" above.
    let arg_sort = |v: &Value, name: &str| match extract_type_param(kb, v, name) {
        Some(av) => match type_head(kb, &av) {
            TypeHead::SortRef(s) => Some(kb.canonical_sort_sym(s)),
            _ => None,
        },
        None => None,
    };
    let params: Vec<Symbol> = kb.type_param_syms_of(e_base).to_vec();
    if params.is_empty() {
        return false;
    }
    let mut any_declared = false;
    for p in params {
        let variance = declared_variance(kb, e_base, p);
        let name = kb.local_name_of(p);
        // A label whose argument is UNWRITTEN on either side decides nothing here. Bare
        // `Error` is `Error[T = ?]`, an undecided payload, and letting it match through
        // this leg would answer a question 027.4 records as open — whether an undecided
        // argument satisfies a decided demand — in passing and in the loose direction.
        let (Some(av), Some(ev)) = (arg_sort(a, name), arg_sort(e, name)) else {
            return false;
        };
        let ok = match variance {
            Variance::Covariant => {
                any_declared = true;
                av == ev || sort_refines(kb, av, ev)
            }
            Variance::Contravariant => {
                any_declared = true;
                av == ev || sort_refines(kb, ev, av)
            }
            // No fact: identity, which the exact-match leg above already decided. This
            // arm exists so a MIXED sort (one declared parameter, one not) still holds
            // its undeclared parameters to equality rather than ignoring them.
            Variance::Invariant => av == ev,
            Variance::Bivariant => {
                any_declared = true;
                av == ev || sort_refines(kb, av, ev) || sort_refines(kb, ev, av)
            }
        };
        if !ok {
            return false;
        }
    }
    // Every parameter agreed, but if NONE of them declared a variance this is just the
    // equality the leg above already tried — say so rather than answering twice.
    any_declared
}

/// Pair present-labels from two rows by greedy structural unification.
///
/// Returns `(only_a, only_b)` — labels left over once every successful
/// pairing has been unified through `subst`. The canonical form
/// (`build_canonical_effects_rows`) sorts labels by `type_display_name`, so
/// parallel rows present labels in the same order and the greedy walk
/// produces the natural pairing for the common case (`{Modify[c], Error}`
/// vs `{Modify[c], Error}`).
///
/// **Limitation (v1a)** — no rollback. If a greedy pair unifies but a
/// downstream tail-binding step fails, the substitution is contaminated. In
/// practice the typer wraps unification calls in higher-level error
/// reporting, so the failed unification produces a top-level type error
/// rather than silent corruption. Backtracking is a v1b nicety.
fn pair_present_labels(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_present: &[Value],
    b_present: &[Value],
) -> (Vec<Value>, Vec<Value>) {
    match_present_labels(kb, subst, a_present, b_present, true)
}

/// WI-326 subtype variant of [`pair_present_labels`] — existential
/// covering instead of 1-to-1 pairing. A single expected label can cover
/// multiple actuals (set-with-subtyping semantics), so a covered `b` label is
/// recorded for the `only_b` computation but NEVER excludes a later
/// pairing attempt.
///
/// Rationale (code-review F1): the pre-WI-326 `arrow_compatible` did
/// `for ae in actual { expected.any(|ee| types_compatible(ae, ee)) }` —
/// exists-quantified. Replacing that with the unify-shaped 1-to-1
/// `pair_present_labels` introduced a regression: `{red, blue} <:
/// {Color}` (two actual entities of a single expected sort) was rejected
/// because `Color` got marked matched after pairing with `red`, leaving
/// `blue` un-paired. Set semantics with element subtyping needs
/// existential pairing; unify needs strict 1-to-1.
///
/// **Returns** `(only_a, only_b)` where:
/// - `only_a` are actual labels that no expected covered (genuine extras
///   on the actual side; under subtype these must be empty or absorbed
///   by expected's open tail).
/// - `only_b` are expected labels that NO actual matched (allowed under
///   subset semantics; they're effects expected may have that actual
///   doesn't use). The tail-binding step still wants these when
///   expected is open and the algorithm needs to bind actual's tail to
///   reach them — same shape as the unify case.
pub(super) fn cover_present_labels(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_present: &[Value],
    b_present: &[Value],
) -> (Vec<Value>, Vec<Value>) {
    match_present_labels(kb, subst, a_present, b_present, false)
}

/// The one greedy walk behind [`pair_present_labels`] and [`cover_present_labels`].
/// `one_to_one` decides exactly one thing: whether a `b` label that has already been
/// matched may be tried again — never, for unification's 1-to-1 pairing; always, for
/// WI-326's existential covering.
fn match_present_labels(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_present: &[Value],
    b_present: &[Value],
    one_to_one: bool,
) -> (Vec<Value>, Vec<Value>) {
    // WI-338 F11: each unify_types attempt may bind variables in `subst`
    // *before* it determines it can't complete the unification (partial
    // structural success that fails on a downstream sub-term). Snapshot
    // the substitution before each attempt and roll back on failure so
    // failed pairings don't leak bindings into the substitution. Required
    // for callers that share `subst` with downstream reasoning
    // (`unify_effect_rows` from inside `unify_arrow` does — its subst
    // propagates into the typer's main state).
    //
    // WI-338 F8: the pre-WI-338 implementation rejected pairings whose
    // functors differed (sort_ref vs parameterized) before calling
    // `unify_types`. That rejected legitimate cross-functor compatible
    // labels (a bare sort vs its instantiation). The pre-filter
    // existed to limit subst pollution from doomed attempts — now
    // unnecessary with the per-attempt snapshot/restore — and is
    // removed. `unify_types`' return value is authoritative.
    let mut b_matched = vec![false; b_present.len()];
    let mut only_a: Vec<Value> = Vec::new();
    for al in a_present {
        let mut paired = false;
        for (i, bl) in b_present.iter().enumerate() {
            if one_to_one && b_matched[i] {
                continue;
            }
            let snapshot = subst.clone();
            if unify_types(kb, subst, al, bl) {
                b_matched[i] = true;
                paired = true;
                break;
            }
            // Restore — discard partial bindings from the failed attempt.
            *subst = snapshot;
        }
        if !paired {
            only_a.push(al.clone());
        }
    }
    let only_b: Vec<Value> = b_present
        .iter()
        .enumerate()
        .filter(|(i, _)| !b_matched[*i])
        .map(|(_, t)| t.clone())
        .collect();
    (only_a, only_b)
}

/// Bind a row-tail variable to a synthesized EffectExpression representing
/// `extra_labels ++ (open(final_tail) | empty_row)`.
///
/// `tail` is the open()'s tail field (a `Term::Var(Var::Global(vid))` in
/// practice). The binding `vid := merge(present(l1), …, merge(present(ln),
/// <open(final_tail) or empty_row>))` plays the role of the row-rewrite
/// equation: subsequent `decompose_effect_row` calls that walk through the
/// substitution recover the labels and the new tail position.
///
/// When `final_tail` is `None`, the tail closes (`empty_row`); when
/// `Some(fresh)`, it stays open and `fresh` becomes the shared extension
/// point between two open rows.
///
/// **WI-336 — Var-variant gating**. Only `Var::Global` row tails are
/// bindable:
///
/// - `Var::Rigid` represents a forall-Skolem — the universally-quantified
///   row whose contents are unknown to this scope. We can't bind it (it's
///   a constant to the unifier) and we can't safely claim it equals
///   `empty_row` or any specific shape on the basis of a "no-op" binding;
///   either side could instantiate `Rigid` to a row that contradicts the
///   caller's claim. Reject.
/// - `Var::DeBruijn` shouldn't appear in a resolved (post-`with_fresh_vars`)
///   context; the typer opens binders before this is reached. Treat as a
///   schema error and reject.
/// - A non-`Var` tail is defensive only — `decompose_effect_row` returns
///   `Some(tail)` only for `Term::Var` nodes. If a malformed input
///   somehow reaches here, accept only the literal no-op (no extras, no
///   final_tail) so the algorithm degrades gracefully.
///
/// Currently latent for v1a (the typer never produces Rigid/DeBruijn
/// effect-row tails), but the v1b lacks-constraint + polymorphic-row work
/// will introduce universally-quantified row variables in arrow.effects
/// positions — at which point the pre-WI-336 fallback would silently
/// accept unsoundly.
pub(super) fn bind_row_tail(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    tail: TermId,
    extra_labels: &[Value],
    final_tail: Option<TermId>,
) -> bool {
    let vid = match kb.get_term(tail) {
        Term::Var(Var::Global(vid)) => *vid,
        // WI-336: forall-quantified (Rigid) or unopened DeBruijn tail —
        // not bindable, and the "would-be-no-op" assumption isn't safe.
        Term::Var(Var::Rigid(_)) | Term::Var(Var::DeBruijn(_)) => return false,
        // Non-Var tail: decompose_effect_row only returns Var for the
        // tail slot, so this is defensive against a malformed input.
        // Accept only a literal no-op.
        _ => return extra_labels.is_empty() && final_tail.is_none(),
    };

    // WI-328: lacks-constraint check. Any present label flowing INTO this
    // tail (via `extra_labels`) must not be one the tail is constrained to
    // lack (`ρ lacks e`). If `vid lacks e` and the binding would present
    // `e`, the row would carry a forbidden effect — reject the binding
    // (this is the "{Error | ρ} with ρ-lacks-Error fails" impossibility).
    let vid_lacks = subst.lacks_of(vid);
    if !vid_lacks.is_empty() {
        for l in extra_labels {
            if label_violates_lacks(kb, subst, l, &vid_lacks) {
                return false;
            }
        }
    }

    // WI-342 P4-B: a denoted-bearing extra label (`Value::Node`) would require
    // synthesizing a *Value-carried* row occurrence (`make_present_occ` …) and
    // binding the tail via `bind_value`. That path (open rows carrying a
    // denoted-bearing label, e.g. `{Modify[c] | ρ}`) is deferred — refuse
    // rather than mis-bind (sound). The ground extras below cover the closed-row
    // cross-carrier target this slice validates. In B1 `decompose_effect_row`
    // walks a `TermId` row, so every extra is already `Value::Term` here.
    let mut ground_extras: Vec<TermId> = Vec::with_capacity(extra_labels.len());
    for l in extra_labels {
        match l {
            Value::Term { id: t, .. } => ground_extras.push(*t),
            _ => return false,
        }
    }

    // WI-337: bootstrap-safety — `decompose_effect_row`'s bare-Var
    // path (line ~5535) returns a `Var::Global` tail without ever
    // resolving any `EffectExpression` symbol, so we can reach here
    // on a KB whose prelude isn't registered. The builders below all
    // call panic-on-miss `resolve_symbol`. Probe the symbols first;
    // if any are missing, reject the binding (sound — we can't
    // synthesize the inner term, so we can't claim the bind holds).
    if kb
        .try_resolve_symbol("anthill.prelude.EffectExpression.empty_row")
        .is_none()
        || kb
            .try_resolve_symbol("anthill.prelude.EffectExpression.open")
            .is_none()
        || kb
            .try_resolve_symbol("anthill.prelude.EffectExpression.present")
            .is_none()
        || kb
            .try_resolve_symbol("anthill.prelude.EffectExpression.merge")
            .is_none()
    {
        return false;
    }

    // Build the inner tail: open(fresh) if shared, empty_row if closed.
    let inner = match final_tail {
        Some(ft) => kb.make_effect_expression_open(ft),
        None => kb.make_effect_expression_empty_row(),
    };
    // Right-fold extras into the inner tail.
    let mut acc = inner;
    for &l in ground_extras.iter().rev() {
        let p = kb.make_effect_expression_present(l);
        acc = kb.make_effect_expression_merge(p, acc);
    }

    if occurs_in(kb, vid, acc) {
        return false;
    }
    subst.bind(kb, vid, acc);
    if subst.is_contradiction() {
        return false;
    }

    // WI-328: propagate this tail's lacks set onto the fresh continuation.
    // `ρ = extra_labels ∪ open(fresh)` and `ρ lacks L` (the extras were
    // already checked clean above) implies `fresh lacks L` — otherwise a
    // later binding of `fresh` could smuggle a forbidden effect back into
    // the row through the shared tail. Closed continuations (`final_tail =
    // None`) have no tail to carry the constraint, and that's sound: the
    // row is now fully determined and the extras passed the lacks check.
    if !vid_lacks.is_empty() {
        if let Some(ft) = final_tail {
            if let Term::Var(Var::Global(fresh_vid)) = kb.get_term(ft) {
                let fresh_vid = *fresh_vid;
                subst.add_lacks(fresh_vid, vid_lacks.iter().cloned());
            }
        }
    }
    true
}

/// WI-328 — does presenting `label` violate any `lacks` constraint in
/// `lacked`? A present label conflicts with a lacked label when the two
/// effect types unify (`Error` vs `Error`; `Modify[c]` vs `Modify[c]`; a
/// parameterized `Modify[?x]` lacked vs a concrete `Modify[c]` presented).
/// The probe unifies on a CLONE of `subst` so a match leaves no bindings
/// behind — the caller is deciding whether to reject the row, not
/// committing the label pairing.
///
/// **WI-341 coupling**: for a value-carrying label like `Modify[c]`, this
/// comparison (and v1a's `pair_present_labels`/`cover_present_labels`) works
/// only because the value occurrence `c` is currently flattened to a
/// hash-consed `denoted(value: Ref(c))`, so two `Modify[c]` share a TermId
/// and `unify_types` matches them. When `denoted` migrates to carry a real
/// `Rc<NodeOccurrence>` (per its `sort.anthill` schema), this must become
/// occurrence-aware — same change for the v1a label sites. See WI-341.
fn label_violates_lacks(
    kb: &mut KnowledgeBase,
    subst: &Substitution,
    label: &Value,
    lacked: &[Value],
) -> bool {
    for l in lacked {
        let mut probe = subst.clone();
        if unify_types(kb, &mut probe, label, l) {
            return true;
        }
    }
    false
}

/// WI-328 — register a row side's `absent` labels as `lacks` constraints on
/// that side's tail variable. Absents on a *closed* row (no tail) are
/// dropped: there is no tail to carry the constraint, and any cross-row
/// attempt to present a label the closed row forbids is already rejected by
/// the presence-pairing step (a forbidden label appears as an unabsorbable
/// extra). Only `Var::Global` tails carry lacks (Rigid/DeBruijn are
/// non-bindable per WI-336, so a lacks on them is unobservable).
fn register_row_lacks(
    kb: &KnowledgeBase,
    subst: &mut Substitution,
    tail: Option<TermId>,
    absent: &[Value],
) {
    if absent.is_empty() {
        return;
    }
    if let Some(t) = tail {
        if let Term::Var(Var::Global(vid)) = kb.get_term(t) {
            subst.add_lacks(*vid, absent.iter().cloned());
        }
    }
}

/// Allocate a fresh row-tail variable for the both-open arm of
/// [`unify_effect_rows`] / [`subtype_effect_rows`].
///
/// **WI-338 F9 known cost**: each call permanently increments
/// `kb.next_var` and inserts a new `Term::Var` into the hash-cons store.
/// The fresh var is bound in a local substitution that is typically
/// discarded after `arrow_compatible` returns — so the var ends up
/// orphaned but never observable. For long-running typer sessions
/// (language server, repeated batch checks) the VarId space grows
/// monotonically. Acceptable in practice today; if it ever becomes a
/// measured concern, possible mitigations:
///
/// - **memoize** `subtype_effect_rows` / `unify_effect_rows` results on
///   `(actual_effects, expected_effects)` so repeat queries don't
///   re-allocate;
/// - maintain a **free-list** of fresh row-tail vars on `KnowledgeBase`,
///   returning to the pool when a local substitution is dropped.
///
/// Both are out of scope for v1a hardening. This helper consolidates
/// the four pre-WI-338 inline allocation sites into one place so the
/// future fix has a single point of change.
fn fresh_row_tail_var(kb: &mut KnowledgeBase) -> TermId {
    let fresh_sym = kb.intern("?rho");
    let fresh_vid = kb.fresh_var(fresh_sym);
    kb.alloc(Term::Var(Var::Global(fresh_vid)))
}

/// WI-307 v1a row unification — the Rémy/Lindley-Cheney algorithm on
/// `effects_rows(EffectExpression)` payloads.
///
/// 1. Decompose each row into (present, tail, absent) through the current
///    substitution.
/// 2. Pair common labels by greedy unification (canonical sort makes the
///    parallel order natural).
/// 3. Resolve tails:
///    - both closed, no extras → trivially unify;
///    - both closed but extras present → reject (sets differ);
///    - one open, the other closed → other-side extras absorbed by the
///      open tail, closing it;
///    - both open → fresh shared tail `?ρ'`; each side's tail binds to its
///      own extras + `open(?ρ')`.
///
/// **Lacks-constraints (WI-328 / v1b)** — `absent` labels (`-e`) are
/// registered as `lacks` constraints on each side's tail
/// (`register_row_lacks`) before step 3; `bind_row_tail` then rejects any
/// present label flowing into a tail that lacks it, and propagates the
/// lacks set onto fresh shared tails so the constraint survives further
/// unification.
pub(super) fn unify_effect_rows<EA: TermView, EB: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_effects: &EA,
    b_effects: &EB,
) -> bool {
    relate_effect_rows(kb, subst, a_effects, b_effects, false)
}

/// WI-326 v1a row subtyping — the covariant directional analog of
/// [`unify_effect_rows`], mirroring its decompose/pair/tail-bind pipeline
/// ([`decompose_effect_row`], [`pair_present_labels`], [`bind_row_tail`])
/// but asymmetric: `actual <: expected` iff actual's effect *set* is a
/// subset of expected's. The body is [`relate_effect_rows`] with `a` the actual row and
/// `b` the expected one, so `only_a` / `only_b` below are its names. Specifically:
///
/// - `only_a` (labels actual has but expected doesn't) must be absorbed
///   by expected's open tail; with expected closed, that's a hard reject.
/// - `only_b` (labels expected has but actual doesn't) are always fine
///   under subset — expected can advertise effects the actual doesn't use.
///   If actual is open, expected's extras are absorbed by actual's tail
///   (the row-rewrite equation that makes actual reach expected's labels).
/// - Actual open + expected closed: actual's tail must close to
///   `empty_row` (actual can't carry unknown extras beyond expected's
///   finite set).
/// - Both open: the unify case applies as-is — a fresh shared tail
///   accommodates either side's extras; once both rows extend through it,
///   the sub relation holds.
///
/// The `subst` argument is the caller's THREADED substitution, not a scratch: since
/// WI-335 [`arrow_compatible_view`] and [`types_compatible`] pass their own, so a row
/// variable bound here is visible to the sibling param / result / effects checks of the
/// same comparison (a local scratch let each reason in isolation and accept arrows whose
/// shared row variable had no consistent binding). A caller whose question must not
/// commit bindings passes a σ of its own — the lattice checks allocate a fresh one per
/// direction. This doc said "a local scratch, allocated by `arrow_compatible_view`" until
/// WI-20260923-N3W68.
pub(super) fn subtype_effect_rows<EA: TermView, EB: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    actual_effects: &EA,
    expected_effects: &EB,
) -> bool {
    relate_effect_rows(kb, subst, actual_effects, expected_effects, true)
}

/// WI-20260923-32XFQ — the one body of [`unify_effect_rows`] (`directional = false`, `b` is
/// the other row) and [`subtype_effect_rows`] (`true`, `a` the actual and `b` the expected
/// row), which spelled it twice. The fast path, the decompose, the lacks registration, the
/// multi-tail arm and the both-open arm ([`bind_both_open_tails`]) are one code; the flag
/// decides EXACTLY five things, each marked `DIRECTIONAL` below — the label pairing, the
/// multi-tail flag (the one [`multi_tail_rows_compat`] already took), and three tail arms.
fn relate_effect_rows<EA: TermView, EB: TermView>(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_effects: &EA,
    b_effects: &EB,
    directional: bool,
) -> bool {
    // Fast path: identical hash-consed `TermId` carriers — covers the canonical
    // case where both arrows shared an effects field. (`Value::Node` carriers
    // have no O(1) identity → fall through to the structural decompose.)
    if let (BindValue::Term(x), BindValue::Term(y)) =
        (a_effects.as_bind_value(), b_effects.as_bind_value())
    {
        if x == y {
            return true;
        }
    }

    // WI-339 F13: decompose returns None on malformed input — propagate
    // as a rejection so the typer surfaces the row-shape error
    // instead of proceeding on incomplete decomposition.
    let (a_present, a_tails, a_absent) = match decompose_effect_row(kb, subst, a_effects) {
        Some(p) => p,
        None => return false,
    };
    let (b_present, b_tails, b_absent) = match decompose_effect_row(kb, subst, b_effects) {
        Some(p) => p,
        None => return false,
    };

    // WI-328: register each side's `- e` absents as `lacks` constraints on
    // that side's tail(s) BEFORE the tail-binding step, so `bind_row_tail`
    // sees them when it checks the labels flowing into each tail.
    //
    // Directional subtyping reuses the symmetric `bind_row_tail` lacks check: a label
    // absorbed into a tail that lacks it is rejected on either side. This is **sound
    // but conservative** on the open/open arm: when expected presents `e` and actual's
    // tail lacks `e` (`{-e | ρa} <: {e | ρe}`), the shared-tail step would bind `ρa` to
    // absorb `e`, which the lacks check rejects — so the pair is reported incompatible.
    // Rejecting is the safe direction (binding a lacked label into the tail would be
    // unsound); the rare genuinely-compatible directional case (route `e` only into the
    // expected side) is left for a later refinement.
    for &t in &a_tails {
        register_row_lacks(kb, subst, Some(t), &a_absent);
    }
    for &t in &b_tails {
        register_row_lacks(kb, subst, Some(t), &b_absent);
    }

    // DIRECTIONAL (1) — the pairing. Unification pairs 1-to-1. Subtyping COVERS
    // (WI-326 F1, code-review): set semantics with element subtyping lets one expected
    // label cover multiple actuals — `{red, blue} <: {Color}` where both `red`, `blue`
    // are entities of `Color` — and the 1-to-1 pairing would mark `Color` matched after
    // the first hit and reject the second.
    let (only_a, only_b) = if directional {
        cover_present_labels(kb, subst, &a_present, &b_present)
    } else {
        pair_present_labels(kb, subst, &a_present, &b_present)
    };

    // WI-441: a row UNION (≥ 2 tails, `{E, EffP}`) takes the dedicated
    // multi-tail arm — equal tail sets or the bare-flexible wholesale absorb.
    // DIRECTIONAL (2) — its own flag.
    if a_tails.len() > 1 || b_tails.len() > 1 {
        let a_inner = row_inner_value(kb, subst, a_effects);
        let b_inner = row_inner_value(kb, subst, b_effects);
        return multi_tail_rows_compat(
            kb,
            subst,
            a_inner,
            b_inner,
            (&a_present, &a_tails, &a_absent),
            (&b_present, &b_tails, &b_absent),
            &only_a,
            &only_b,
            directional,
        );
    }
    let a_tail = a_tails.first().copied();
    let b_tail = b_tails.first().copied();

    match (a_tail, b_tail) {
        // DIRECTIONAL (3) — both closed. Unification needs the two label sets equal;
        // subtyping needs only actual's extras empty (actual ⊆ expected labels), since
        // expected's extras are fine under subset semantics.
        (None, None) => only_a.is_empty() && (directional || only_b.is_empty()),
        // DIRECTIONAL (4) — `a` closed, `b` open. `b`'s tail absorbs `a`'s extras, closing
        // it. Under unification `a` has no tail to absorb `b`'s extras, so those must be
        // empty; under subtyping they are already in expected's known set and constrain
        // nothing.
        (None, Some(b_t)) => {
            // (Unification's reading — the only one with a failing path in this arm.)
            // WI-329 CONSIDERED BINDING HERE AND MEASURED THAT IT IS WRONG. A handler's
            // discharge wants `ρ := only_a` on exactly this arm's FAILING path (the body
            // does not perform the handled label), and binding before the `return` looks
            // free because it is the same `bind_row_tail` the success path performs. It
            // is not free: this relation runs once PER ARGUMENT with its boolean
            // DISCARDED, so a tail shared by two parameters gets closed by whichever
            // argument reaches it first. MEASURED — `two[Rho](a: () -> Int64 @
            // {Error[Int64], Rho}, b: () -> Int64 @ {Rho})` applied to a pure `a` and a
            // `{Clock}` `b` stops loading, because `a` closes `Rho` to `{}` before `b`
            // can contribute `Clock`. The discharge inference therefore belongs where
            // every argument's contribution is known: [`infer_discharged_row_tails`],
            // run once after the arg-unify loops. Leave this relation an EQUALITY that
            // does not leak bindings on refusal (the discipline `pair_present_labels`
            // states for the same reason).
            //
            // THE SUCCESS PATH BELOW HAS THE SAME PROBLEM AND IS NOT FIXED HERE —
            // WI-20260820-RDNS4. `bind_row_tail(…, None)` CLOSES the tail, so even when
            // this arm succeeds the first argument commits its least solution as if it
            // were the only constraint: the same `two[Rho]` at an ERRORING `a`, and a
            // `two_plain[Rho](a: @{Rho}, b: @{Rho})` with no handled label at all, are
            // both refused — before and after WI-329 alike, so it is pre-existing and not
            // about handlers. `infer_discharged_row_tails` cannot repair it either: it
            // fires only for tails still UNBOUND after both arg loops.
            if !directional && !only_b.is_empty() {
                return false;
            }
            bind_row_tail(kb, subst, b_t, &only_a, None)
        }
        // DIRECTIONAL (5) — `a` open, `b` closed. `b` can absorb nothing through a tail,
        // so `a`'s extras must be empty either way. `a`'s tail then closes to `b`'s extras
        // under unification, and to the EMPTY row under subtyping: actual can't carry
        // unknown extras beyond expected's finite set.
        (Some(a_t), None) => {
            if !only_a.is_empty() {
                return false;
            }
            let closing: &[Value] = if directional { &[] } else { &only_b };
            bind_row_tail(kb, subst, a_t, closing, None)
        }
        (Some(a_t), Some(b_t)) => bind_both_open_tails(kb, subst, a_t, b_t, &only_a, &only_b),
    }
}

/// The both-open arm of [`relate_effect_rows`], the same in both relations: once both tails
/// link through one shared continuation, the two rows agree on one set, which is what
/// unification asks and all that subtyping asks.
fn bind_both_open_tails(
    kb: &mut KnowledgeBase,
    subst: &mut Substitution,
    a_t: TermId,
    b_t: TermId,
    only_a: &[Value],
    only_b: &[Value],
) -> bool {
    let a_walked = walk_type(kb, subst, a_t);
    let b_walked = walk_type(kb, subst, b_t);
    // WI-334: a shared row var (a_walked == b_walked). Two distinct `bind_row_tail` calls
    // would each try to bind the same VarId to two structurally different terms
    // (`only_b ++ open(fresh)` vs `only_a ++ open(fresh)`) — contradicting subst.bind,
    // returning false even for valid pairs. Bind once with the union of both extras
    // instead: A's set = a_present ∪ K, B's set = b_present ∪ K, where K is the shared
    // tail. Binding K to {only_a ∪ only_b | fresh} makes both rows agree on the same set
    // (the labels already matched — paired under unification, covered under subtyping).
    if a_walked == b_walked {
        if only_a.is_empty() && only_b.is_empty() {
            return true;
        }
        let fresh_var = fresh_row_tail_var(kb);
        let mut all_extras: Vec<Value> = Vec::with_capacity(only_a.len() + only_b.len());
        all_extras.extend(only_a.iter().cloned());
        all_extras.extend(only_b.iter().cloned());
        return bind_row_tail(kb, subst, a_walked, &all_extras, Some(fresh_var));
    }
    // WI-441: tail-to-tail aliasing when ONE side's tail is a RIGID
    // (forall-Skolem) row var — the FORWARDING shape (`find(rest,
    // pred)` / `Stream.find(iterator(c), pred)` passes the enclosing
    // op's callback straight through, its row tail rigidified by the
    // body check). The rigid is un-bindable (WI-336), so the
    // symmetric fresh-tail step below would fail and leave the
    // callee's row param unconstrained. With no extras to push INTO
    // the rigid side, the flexible tail simply ALIASES the rigid
    // (a flexible var solves TO a rigid, the ordinary direction).
    // Under subtyping (actual ⊆ expected) that reads: a rigid ACTUAL tail can't absorb
    // expected's extras (require none) and the flexible expected tail aliases it;
    // symmetric for a rigid EXPECTED tail.
    // Note: the flexible side's lacks are not propagated onto the
    // rigid continuation (`bind_row_tail` propagates onto `Global`
    // continuations only) — the rigid's constraints are enforced at
    // its own instantiation site.
    let a_rigid = matches!(kb.get_term(a_walked), Term::Var(Var::Rigid(_)));
    let b_rigid = matches!(kb.get_term(b_walked), Term::Var(Var::Rigid(_)));
    match (a_rigid, b_rigid) {
        (true, false) if only_b.is_empty() => {
            return bind_row_tail(kb, subst, b_walked, only_a, Some(a_walked));
        }
        (false, true) if only_a.is_empty() => {
            return bind_row_tail(kb, subst, a_walked, only_b, Some(b_walked));
        }
        // Two DISTINCT rigids (the a_walked == b_walked case returned
        // above) never alias; a rigid that must absorb extras fails.
        (true, _) | (_, true) => return false,
        (false, false) => {}
    }
    // Distinct tails: fresh shared tail var ρ'. Both sides extend
    // their respective labels and end in `open(ρ')` — afterward a
    // future decompose_effect_row reveals (only_a + only_b) as
    // present labels with shared tail ρ'. The symmetric Rémy fresh-tail step.
    let fresh_var = fresh_row_tail_var(kb);
    bind_row_tail(kb, subst, a_t, only_b, Some(fresh_var))
        && bind_row_tail(kb, subst, b_t, only_a, Some(fresh_var))
}

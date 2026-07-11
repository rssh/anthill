//! WI-580 — the one-step operation-body specializer (SLD case-split engine).
//!
//! Design: `docs/design/abstract-interpreter-and-rules.md` §3.3. The body is the
//! single source of truth; its relational view is *derived on demand* by
//! abstractly interpreting the body one step at the actual call arguments,
//! rather than materialized as a duplicate `<=>`/`:-` rule. A derived rule IS
//! one step of abstract interpretation (§2): substitute the call's arguments
//! into the body, reduce the `match` whose scrutinee's head is statically known,
//! and leave every nested call — including the recursive one — as a residual.
//!
//! This module hosts the shared reduction primitives ([`reduce`],
//! [`match_pattern_occ`], [`ctor_field_occs`], [`same_ctor_sort`],
//! [`occ_head_ctor`]) and the SLD entry [`folded_call_match`]: it substitutes an
//! op-call's arguments into the body and, when the result is a `match` on a
//! still-unground (flex-var) scrutinee — exactly the shape the direct call
//! (`reduce_op_value` / the eval bridge) SUSPENDS on — returns that scrutinee
//! and the per-arm `(pattern, residual)` pairs for the resolver to case-split
//! (`KnowledgeBase::unfold_eq_operand` in `resolve.rs`). A known-head scrutinee
//! reduces deterministically instead (the caller's direct call handles that
//! ground case); an unknown scrutinee that is not a flex var is left opaque.
//!
//! (An earlier increment wired the reducer to the typer's `[simp]` hook (§3.2);
//! that proved type-unsound — rewriting a call before `check_apply_iter` bypasses
//! signature-level checks — and was the wrong consumer for the untagged `<=>`
//! twins, so WI-580 targets this SLD site. See `wi580-body-derived-rules` memo.)

use std::rc::Rc;

use crate::eval::pattern::functor_matches;
use crate::intern::{Symbol, SymbolKind};

use super::node_occurrence::{Expr, MatchBranch, NodeOccurrence, Pattern};
use super::occurrence::PassId;
use super::op_info::lookup_operation_info;
use super::term::{Literal, Term, Var};
use super::KnowledgeBase;

/// Local interpretation environment: a binder `Symbol` → the occurrence bound
/// to it (an operation parameter → its call argument, or a `match`-arm pattern
/// variable → the scrutinee sub-occurrence). A `Vec` searched most-recent-first
/// so an inner binder correctly shadows an outer name. Operation-body binders
/// are gensym'd per site (WI-550), so a pattern binder never actually collides
/// with a parameter name — the shadow discipline is defence in depth.
type Env = Vec<(Symbol, Rc<NodeOccurrence>)>;

fn env_lookup<'a>(env: &'a Env, name: Symbol) -> Option<&'a Rc<NodeOccurrence>> {
    env.iter().rev().find(|(s, _)| *s == name).map(|(_, o)| o)
}

fn short_of<'a>(kb: &'a KnowledgeBase, s: Symbol) -> &'a str {
    kb.resolve_sym(s).rsplit('.').next().unwrap_or("")
}

/// A `match`-arm exposed by unfolding a bodied op-call one step at its call
/// arguments — the SLD case-split unit (design §3.3). `pattern` is the arm's
/// constructor pattern (binders still their body-local symbols); `body` is the
/// arm's residual expression with the op's parameters already substituted (its
/// pattern binders still free — the caller opens them to fresh resolver vars).
pub(crate) struct UnfoldArm {
    pub pattern: Rc<NodeOccurrence>,
    pub body: Rc<NodeOccurrence>,
}

/// The SLD unfold entry (design §3.3): substitute a bodied op-call's arguments
/// into its body one step and, WHEN the result is a `match` on a still-unground
/// (flex-var) scrutinee, return that scrutinee occurrence and the per-arm
/// (pattern, residual). This is the case the direct call (`reduce_op_value` /
/// the eval bridge) SUSPENDS on — arguments too unground to decide — so the
/// resolver case-splits instead of floundering. Returns `None` when the op is
/// not a statically-known bodied op, the args don't bind, or the body does not
/// reduce to a match on a flex scrutinee (a known scrutinee already reduced via
/// the direct call; a non-match body has nothing to case-split) — the caller
/// then leaves the call to its normal delay handling.
///
/// The requires/effects gate is the CALLER's: at the SLD site a `requires`-op's
/// dictionary is owed-on-consumption (WI-562), unlike the typer rewrite site.
pub(crate) fn folded_call_match(
    kb: &mut KnowledgeBase,
    op: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Option<(Rc<NodeOccurrence>, Vec<UnfoldArm>)> {
    if !super::typing::op_has_runnable_body(kb, op) {
        return None;
    }
    let info = lookup_operation_info(kb, op)?;
    // Purity gate (design §9 + WI-562): an EFFECTFUL body is not a rewrite, and a
    // `requires`-carrying op owes its dictionary on consumption — the case-split
    // does not yet thread it. Decline both (the caller then delays / residualizes)
    // rather than enumerate arms whose effect or guard was never discharged.
    // (`member`'s `requires Eq[T]` is also excluded at the resolver's relational-
    // rules gate; this covers a `requires`/effect-only bodied op with no rules.)
    if !info.effects.is_empty() || !info.requires.is_empty() {
        return None;
    }
    let body = info.body_node.clone()?;
    let env = bind_params(kb, &info.params, pos_args, named_args)?;
    let pass = super::simp_rewrite::simp_pass(kb);
    let residual = reduce(kb, &body, &env, pass)?;
    // Case-split only a residual that is a `match` on a flex-var scrutinee — the
    // suspend shape. A `Var(Global)` here is an unbound resolver goal var (the
    // call arg the body branches on); any other scrutinee shape either reduced
    // already or isn't narrowable by unifying with a constructor pattern.
    let Some(Expr::Match { scrutinee, branches }) = residual.as_expr() else {
        return None;
    };
    if !matches!(scrutinee.as_expr(), Some(Expr::Var(Var::Global(_)))) {
        return None;
    }
    // Sound case-split requires DISJOINT arms: every arm a DISTINCT constructor
    // pattern. A catch-all (`_`/var/literal) or a repeated constructor arm
    // overlaps its predecessors, so enumerating it as an independent alternative
    // would over-generate — a real top-to-bottom `match` also requires "no
    // earlier arm matched", a negation guard that is undecidable on an unground
    // scrutinee (design §3.3 → WI-519 residual). Rather than emit those guards,
    // decline the whole unfold here; the caller then delays (residualizes),
    // never producing a wrong definite answer.
    let mut seen: Vec<Symbol> = Vec::with_capacity(branches.len());
    for b in branches {
        match b.pattern.as_pattern() {
            Some(Pattern::Constructor { name, .. }) if !seen.contains(name) => seen.push(*name),
            _ => return None,
        }
    }
    let arms = branches
        .iter()
        .map(|b| UnfoldArm { pattern: Rc::clone(&b.pattern), body: Rc::clone(&b.body) })
        .collect();
    Some((Rc::clone(scrutinee), arms))
}

/// A body-derived defining equation (design §3.4.1, WI-669): one arm of an
/// operation body specialized at a call's arguments. `result` is the reduced
/// arm expression (the op's parameters already substituted); `guards` are the
/// `if`-conditions on the path to it (empty for an unconditional body). The
/// arm set is exhaustive and mutually exclusive — equivalent to a single
/// `ite`-chain — so a consumer asserts `⋀ guardsᵢ ⇒ op(args) = resultᵢ`.
///
/// Carried as **occurrences, not hash-consed terms**: a defining equation is
/// transient, on-demand-derived structure (the CLAUDE.md Representation note —
/// do not intern transient derived structure), and smt-gen already consumes
/// rule bodies as occurrences (WI-246). Keeping the goal carrier neutral means
/// the consumer never forces the partial occurrence→`TermId` conversion (which
/// cannot represent control-flow); any lowering it needs happens at its own
/// atom boundary, where an unrepresentable shape is rejected loudly.
pub struct DefiningEquation {
    pub guards: Vec<DefiningGuard>,
    pub result: Rc<NodeOccurrence>,
}

/// One `if`-condition on the path to a [`DefiningEquation`]. `cond` is a
/// boolean-valued occurrence in the op's parameter frame; `negated` marks the
/// else-branch (the arm is reached only when `cond` is FALSE).
#[derive(Clone)]
pub struct DefiningGuard {
    pub cond: Rc<NodeOccurrence>,
    pub negated: bool,
}

/// The prover/SMT entry (design §3.4.1, WI-669): substitute a bodied op-call's
/// arguments into its body one step and return its defining equations — one
/// `DefiningEquation` per `if`-branch path, each carrying the branch conditions
/// (`guards`) and the reduced result. Unlike [`folded_call_match`] (which serves
/// the SLD relational case-split and admits only a flex-scrutinee disjoint
/// `match`), this serves proofs: the arms become guarded SMT clauses whose
/// conditions are asserted explicitly, so no flex/disjoint gate applies.
///
/// Returns `None` — a *loud* decline, never a silent partial — when the op is
/// not a statically-known pure bodied op, the args don't bind, or the reduced
/// body contains a form this increment does not admit: a `match` (ADT defining
/// equations need SMT datatype support — future), a `let` (needs `Expr::Let` in
/// [`reduce`] — the transponder follow-on, WI-679), or any higher-order /
/// post-elaboration shape.
fn defining_equations(
    kb: &mut KnowledgeBase,
    op: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Option<Vec<DefiningEquation>> {
    if !super::typing::op_has_runnable_body(kb, op) {
        return None;
    }
    let info = lookup_operation_info(kb, op)?;
    // Purity gate (design §9): an effectful body is not an equation. The
    // `requires` gate is kept for this increment (relaxing it to carry the
    // dictionary as an equation antecedent is future, §3.4.1); the arithmetic
    // consumers (`desired_position`, the ranking transition) are requires-free.
    if !info.effects.is_empty() || !info.requires.is_empty() {
        return None;
    }
    let body = info.body_node.clone()?;
    let env = bind_params(kb, &info.params, pos_args, named_args)?;
    let pass = super::simp_rewrite::simp_pass(kb);
    let residual = reduce(kb, &body, &env, pass)?;
    let mut arms = Vec::new();
    flatten_arms(&residual, Vec::new(), &mut arms)?;
    Some(arms)
}

/// Flatten a reduced body into guarded arms: split every residual `if` into its
/// two condition-guarded paths (then: `cond`; else: ¬`cond`), recursing so a
/// nested `if` accumulates its conditions; a non-`if`/non-`match` residual is
/// one arm under the guards collected so far. Declines (`None`) a residual
/// `match` — ADT defining equations are future (they need SMT datatype support)
/// — so the caller gets a loud decline rather than a silently-dropped branch.
fn flatten_arms(
    occ: &Rc<NodeOccurrence>,
    guards: Vec<DefiningGuard>,
    out: &mut Vec<DefiningEquation>,
) -> Option<()> {
    match occ.as_expr() {
        Some(Expr::If { condition, then_branch, else_branch }) => {
            let mut then_guards = guards.clone();
            then_guards.push(DefiningGuard { cond: Rc::clone(condition), negated: false });
            flatten_arms(then_branch, then_guards, out)?;
            let mut else_guards = guards;
            else_guards.push(DefiningGuard { cond: Rc::clone(condition), negated: true });
            flatten_arms(else_branch, else_guards, out)?;
            Some(())
        }
        // A residual `match` branches on an ADT scrutinee this increment can't
        // lower to SMT — decline loudly (future: SMT datatype support + WI-679).
        Some(Expr::Match { .. }) => None,
        // Any other residual (constructor, arithmetic apply, field access, var,
        // const) is a single arm under the accumulated guards.
        _ => {
            out.push(DefiningEquation { guards, result: Rc::clone(occ) });
            Some(())
        }
    }
}

/// Bind `params` (declaration order) to the call's positional-then-named
/// argument occurrences. Positional args fill the leading parameters; named
/// args match a parameter by short name. Returns `None` on any arity mismatch,
/// unknown named argument, or double binding (a partial / malformed application
/// — decline rather than specialize a wrong shape).
fn bind_params(
    kb: &KnowledgeBase,
    params: &[(Symbol, crate::eval::value::Value)],
    pos_args: &[Rc<NodeOccurrence>],
    named_args: &[(Symbol, Rc<NodeOccurrence>)],
) -> Option<Env> {
    if pos_args.len() + named_args.len() != params.len() {
        return None;
    }
    let mut env: Env = Vec::with_capacity(params.len());
    let mut bound = vec![false; params.len()];
    for (i, arg) in pos_args.iter().enumerate() {
        bound[i] = true;
        env.push((params[i].0, Rc::clone(arg)));
    }
    for (name, arg) in named_args {
        let short = short_of(kb, *name);
        let idx = params.iter().position(|(p, _)| short_of(kb, *p) == short)?;
        if bound[idx] {
            return None;
        }
        bound[idx] = true;
        env.push((params[idx].0, Rc::clone(arg)));
    }
    bound.iter().all(|b| *b).then_some(env)
}

/// One-step abstract interpretation of a body occurrence under `env`. Returns
/// the (parameter-substituted, statically-reduced) residual. Returns `None` to
/// decline the whole inline when the body contains a construct this increment
/// does not specialize — a *loud* decline: we never emit a residual that might
/// still carry an unsubstituted body-local variable or change meaning.
fn reduce(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    env: &Env,
    pass: PassId,
) -> Option<Rc<NodeOccurrence>> {
    let Some(expr) = occ.as_expr() else {
        // A non-Expr child (a Pattern/Type/EffectExpr occurrence reached only via
        // the generic arms below) carries no body variable to substitute.
        return Some(Rc::clone(occ));
    };
    match expr {
        // ── binder references: splice the bound occurrence in place ──
        Expr::Var(Var::Global(vid)) => Some(subst_leaf(env, vid.name(), occ)),
        Expr::Ref(s) | Expr::Ident(s) => Some(subst_leaf(env, *s, occ)),
        Expr::VarRef { name } => Some(subst_leaf(env, *name, occ)),
        // Non-Global vars never name a body parameter (bodies carry Global, WI-487).
        Expr::Var(_) | Expr::Const(_) | Expr::Bottom => Some(Rc::clone(occ)),

        // ── match: reduce when the scrutinee's shape is statically known ──
        Expr::Match { scrutinee, branches } => reduce_match(kb, occ, scrutinee, branches, env, pass),

        // ── if: reduce when the condition folds to a boolean literal ──
        Expr::If { condition, then_branch, else_branch } => {
            let cond = reduce(kb, condition, env, pass)?;
            if let Some(b) = static_bool(&cond) {
                let chosen = if b { then_branch } else { else_branch };
                return reduce(kb, chosen, env, pass);
            }
            let then_r = reduce(kb, then_branch, env, pass)?;
            let else_r = reduce(kb, else_branch, env, pass)?;
            Some(rebuild(
                occ,
                Expr::If { condition: cond, then_branch: then_r, else_branch: else_r },
                pass,
            ))
        }

        // ── residual-call boundary: substitute into args, do NOT unfold ──
        // The recursive/nested call stays a call; the WI-283 re-`Visit` loop
        // re-specializes it when it is reassembled at this same hook.
        Expr::Apply { functor, pos_args, named_args, type_args } => {
            let pos = reduce_vec(kb, pos_args, env, pass)?;
            let named = reduce_named(kb, named_args, env, pass)?;
            Some(rebuild(
                occ,
                Expr::Apply {
                    functor: *functor,
                    pos_args: pos,
                    named_args: named,
                    type_args: type_args.clone(),
                },
                pass,
            ))
        }
        Expr::Constructor { name, pos_args, named_args } => {
            let pos = reduce_vec(kb, pos_args, env, pass)?;
            let named = reduce_named(kb, named_args, env, pass)?;
            Some(rebuild(
                occ,
                Expr::Constructor { name: *name, pos_args: pos, named_args: named },
                pass,
            ))
        }

        // Any other form (let / lambda / higher-order / post-elaboration) is not
        // specialized in this increment — decline the inline rather than emit a
        // residual we cannot guarantee is body-variable-free.
        _ => None,
    }
}

/// Substitute a binder-reference leaf: return the bound occurrence when `name`
/// is in scope, else the leaf unchanged.
fn subst_leaf(env: &Env, name: Symbol, occ: &Rc<NodeOccurrence>) -> Rc<NodeOccurrence> {
    match env_lookup(env, name) {
        Some(bound) => Rc::clone(bound),
        None => Rc::clone(occ),
    }
}

fn reduce_match(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    scrutinee: &Rc<NodeOccurrence>,
    branches: &[MatchBranch],
    env: &Env,
    pass: PassId,
) -> Option<Rc<NodeOccurrence>> {
    let scr = reduce(kb, scrutinee, env, pass)?;
    // Select the surviving arm when the scrutinee's shape is statically known.
    match select_arm(kb, &scr, branches) {
        ArmSel::Matched { body, bindings } => {
            let mut env2 = env.clone();
            env2.extend(bindings);
            reduce(kb, &body, &env2, pass)
        }
        // Scrutinee shape unknown (or a sub-pattern we can't decide): keep the
        // match as a residual, substituting params into the scrutinee and each
        // arm body. Arm bodies reduce under `env` WITHOUT the arm's binders (the
        // scrutinee isn't known, so they stay free); binders are gensym'd so they
        // never collide with a parameter in `env` (shadowed defensively).
        ArmSel::Undecidable => {
            let mut new_branches = Vec::with_capacity(branches.len());
            for b in branches {
                let arm_env = shadow(env, &b.pattern);
                let body = reduce(kb, &b.body, &arm_env, pass)?;
                let guard = match &b.guard {
                    Some(g) => Some(reduce(kb, g, &arm_env, pass)?),
                    None => None,
                };
                new_branches.push(MatchBranch {
                    pattern: Rc::clone(&b.pattern),
                    guard,
                    body,
                    span: b.span,
                });
            }
            Some(rebuild(occ, Expr::Match { scrutinee: scr, branches: new_branches }, pass))
        }
    }
}

enum ArmSel {
    Matched { body: Rc<NodeOccurrence>, bindings: Vec<(Symbol, Rc<NodeOccurrence>)> },
    Undecidable,
}

/// Pick the arm a known-shape scrutinee selects. Iterates branches in order:
/// a definite match wins; a definite non-match skips to the next; anything
/// undecidable (unknown scrutinee shape, or a sub-pattern we can't resolve)
/// aborts arm selection so the match is kept as a residual — we never skip a
/// branch we couldn't rule out.
fn select_arm(kb: &KnowledgeBase, scr: &Rc<NodeOccurrence>, branches: &[MatchBranch]) -> ArmSel {
    for b in branches {
        // A guarded arm's guard is a value-level test we don't evaluate here —
        // treat the whole match as undecidable rather than pick past it.
        if b.guard.is_some() {
            return ArmSel::Undecidable;
        }
        match match_pattern_occ(kb, &b.pattern, scr) {
            PatOutcome::Yes(bindings) => {
                return ArmSel::Matched { body: Rc::clone(&b.body), bindings };
            }
            PatOutcome::No => continue,
            PatOutcome::Undecidable => return ArmSel::Undecidable,
        }
    }
    // Known scrutinee, no arm matched: a non-exhaustive source match. Don't
    // fabricate a reduction — keep it residual (typer exhaustiveness / eval
    // MatchFailed handle it).
    ArmSel::Undecidable
}

enum PatOutcome {
    Yes(Vec<(Symbol, Rc<NodeOccurrence>)>),
    No,
    Undecidable,
}

fn match_pattern_occ(
    kb: &KnowledgeBase,
    pattern: &Rc<NodeOccurrence>,
    scr: &Rc<NodeOccurrence>,
) -> PatOutcome {
    let Some(pat) = pattern.as_pattern() else {
        // A reflection meta-var pattern (an Expr-kind occurrence): not a runtime
        // matcher — don't guess.
        return PatOutcome::Undecidable;
    };
    match pat {
        Pattern::Var { name, .. } => PatOutcome::Yes(vec![(*name, Rc::clone(scr))]),
        Pattern::Wildcard => PatOutcome::Yes(vec![]),
        Pattern::Literal { value } => match scr_literal(scr) {
            Some(lit) if lit == value => PatOutcome::Yes(vec![]),
            Some(_) => PatOutcome::No,
            None => PatOutcome::Undecidable,
        },
        Pattern::Constructor { name, pos_args, named_args } => {
            let Some(head) = occ_head_ctor(kb, scr) else {
                return PatOutcome::Undecidable;
            };
            if functor_matches(kb, *name, head) {
                return match_ctor_fields(kb, scr, pos_args, named_args);
            }
            // Different head. This is a definite non-match ONLY when the
            // scrutinee's head is a genuine *sibling* constructor of the
            // pattern's sort (e.g. pattern `nil`, scrutinee `cons`). If the
            // scrutinee's head belongs to a different sort, it is not in this
            // sort's constructor form — a surface literal builder such as
            // `anthill.reflect.ListLiteral` (whose sort is not `List`) reaches
            // its `cons`/`nil` form only after lowering. Skipping the arm then
            // would fall through to a wildcard and pick the WRONG branch, so
            // report undecidable and leave the match a residual (WI-580: a
            // definite non-match must be a genuine same-sort mismatch).
            if same_ctor_sort(kb, *name, head) {
                PatOutcome::No
            } else {
                PatOutcome::Undecidable
            }
        }
        Pattern::Tuple { positional, named } => match scr.as_expr() {
            Some(Expr::TupleLit { positional: sp, named: sn }) => {
                match_tuple_fields(kb, positional, named, sp, sn)
            }
            // A known non-tuple scrutinee can't match a tuple pattern.
            _ if occ_head_ctor(kb, scr).is_some() || scr_literal(scr).is_some() => PatOutcome::No,
            _ => PatOutcome::Undecidable,
        },
    }
}

/// Match a constructor pattern's sub-patterns against a constructor scrutinee's
/// fields, aligning both sides by field symbol (declaration order for
/// positionals, name for named) so the result is independent of how either side
/// ordered its args.
fn match_ctor_fields(
    kb: &KnowledgeBase,
    scr: &Rc<NodeOccurrence>,
    pos_pats: &[Rc<NodeOccurrence>],
    named_pats: &[(Symbol, Rc<NodeOccurrence>)],
) -> PatOutcome {
    let Some(fields) = ctor_field_occs(kb, scr) else {
        return PatOutcome::Undecidable;
    };
    let n = fields.len();
    if pos_pats.len() + named_pats.len() != n {
        return PatOutcome::No;
    }
    let mut binds = Vec::new();
    let mut covered = vec![false; n];
    for (i, pat) in pos_pats.iter().enumerate() {
        covered[i] = true;
        match match_pattern_occ(kb, pat, &fields[i].1) {
            PatOutcome::Yes(mut b) => binds.append(&mut b),
            PatOutcome::No => return PatOutcome::No,
            PatOutcome::Undecidable => return PatOutcome::Undecidable,
        }
    }
    for (fsym, pat) in named_pats {
        let short = short_of(kb, *fsym);
        let Some(idx) = fields.iter().position(|(f, _)| short_of(kb, *f) == short) else {
            return PatOutcome::No;
        };
        if covered[idx] {
            return PatOutcome::No;
        }
        covered[idx] = true;
        match match_pattern_occ(kb, pat, &fields[idx].1) {
            PatOutcome::Yes(mut b) => binds.append(&mut b),
            PatOutcome::No => return PatOutcome::No,
            PatOutcome::Undecidable => return PatOutcome::Undecidable,
        }
    }
    PatOutcome::Yes(binds)
}

fn match_tuple_fields(
    kb: &KnowledgeBase,
    pos_pats: &[Rc<NodeOccurrence>],
    named_pats: &[(Symbol, Rc<NodeOccurrence>)],
    scr_pos: &[Rc<NodeOccurrence>],
    scr_named: &[(Symbol, Rc<NodeOccurrence>)],
) -> PatOutcome {
    if !named_pats.is_empty() || !scr_named.is_empty() || pos_pats.len() != scr_pos.len() {
        // Named-tuple patterns aren't exercised in this increment — don't guess.
        return if named_pats.is_empty() && scr_named.is_empty() {
            PatOutcome::No
        } else {
            PatOutcome::Undecidable
        };
    }
    let mut binds = Vec::new();
    for (pat, sub) in pos_pats.iter().zip(scr_pos.iter()) {
        match match_pattern_occ(kb, pat, sub) {
            PatOutcome::Yes(mut b) => binds.append(&mut b),
            PatOutcome::No => return PatOutcome::No,
            PatOutcome::Undecidable => return PatOutcome::Undecidable,
        }
    }
    PatOutcome::Yes(binds)
}

/// The (field-symbol, sub-occurrence) pairs of a constructor scrutinee, in the
/// entity's declaration order, or `None` when the scrutinee is not a statically
/// resolvable constructor application. Robust to the scrutinee mixing / reordering
/// positional and named args.
fn ctor_field_occs(
    kb: &KnowledgeBase,
    scr: &Rc<NodeOccurrence>,
) -> Option<Vec<(Symbol, Rc<NodeOccurrence>)>> {
    match scr.as_expr()? {
        Expr::Constructor { name, pos_args, named_args } => {
            let fields = kb.entity_field_names(*name)?;
            let mut slots: Vec<Option<Rc<NodeOccurrence>>> = vec![None; fields.len()];
            for (i, a) in pos_args.iter().enumerate() {
                *slots.get_mut(i)? = Some(Rc::clone(a));
            }
            for (fsym, a) in named_args {
                let short = short_of(kb, *fsym);
                let idx = fields.iter().position(|f| short_of(kb, *f) == short)?;
                if slots[idx].is_some() {
                    return None;
                }
                slots[idx] = Some(Rc::clone(a));
            }
            let mut out = Vec::with_capacity(fields.len());
            for (i, slot) in slots.into_iter().enumerate() {
                out.push((fields[i], slot?));
            }
            Some(out)
        }
        // A nullary constructor stored as a bare ref (WI-436/WI-511) — no fields.
        Expr::Ref(s) | Expr::Ident(s) if kb.kind_of(*s) == Some(SymbolKind::Entity) => {
            Some(Vec::new())
        }
        _ => None,
    }
}

/// The head constructor symbol of a statically-known constructor occurrence, or
/// `None` (a call, a variable, a literal — head not a known constructor).
fn occ_head_ctor(kb: &KnowledgeBase, occ: &Rc<NodeOccurrence>) -> Option<Symbol> {
    match occ.as_expr()? {
        Expr::Constructor { name, .. } => Some(*name),
        Expr::Ref(s) | Expr::Ident(s) if kb.kind_of(*s) == Some(SymbolKind::Entity) => Some(*s),
        _ => None,
    }
}

/// The symbol of the sort a constructor belongs to (`cons`/`nil` → `List`), or
/// `None` when the symbol is not a sort-owned constructor.
fn ctor_sort_sym(kb: &KnowledgeBase, ctor: Symbol) -> Option<Symbol> {
    let tid = kb.constructor_parent_sort(ctor)?;
    match kb.get_term(tid) {
        Term::Ref(s) | Term::Ident(s) => Some(*s),
        Term::Fn { functor, .. } => Some(*functor),
        _ => None,
    }
}

/// Whether two constructors are variants of the same sort — the condition under
/// which a head mismatch is a genuine non-match (rather than a not-yet-lowered
/// surface form). Requires both to resolve to a sort (a bare, sort-less symbol
/// is treated as not-same, i.e. undecidable, conservatively).
fn same_ctor_sort(kb: &KnowledgeBase, a: Symbol, b: Symbol) -> bool {
    match (ctor_sort_sym(kb, a), ctor_sort_sym(kb, b)) {
        (Some(sa), Some(sb)) => sa == sb,
        _ => false,
    }
}

fn scr_literal<'a>(occ: &'a Rc<NodeOccurrence>) -> Option<&'a Literal> {
    match occ.as_expr()? {
        Expr::Const(lit) => Some(lit),
        _ => None,
    }
}

fn static_bool(occ: &Rc<NodeOccurrence>) -> Option<bool> {
    match occ.as_expr()? {
        Expr::Const(Literal::Bool(b)) => Some(*b),
        _ => None,
    }
}

/// `env` with any name bound by `pattern` removed, so reducing an arm body does
/// not substitute a parameter into an occurrence of that arm's own binder.
fn shadow(env: &Env, pattern: &Rc<NodeOccurrence>) -> Env {
    let mut bound = Vec::new();
    collect_bound_names(pattern, &mut bound);
    if bound.is_empty() {
        return env.clone();
    }
    env.iter().filter(|(s, _)| !bound.contains(s)).cloned().collect()
}

fn collect_bound_names(pattern: &Rc<NodeOccurrence>, out: &mut Vec<Symbol>) {
    let Some(pat) = pattern.as_pattern() else { return };
    match pat {
        Pattern::Var { name, .. } => out.push(*name),
        Pattern::Wildcard | Pattern::Literal { .. } => {}
        Pattern::Constructor { pos_args, named_args, .. } => {
            for p in pos_args {
                collect_bound_names(p, out);
            }
            for (_, p) in named_args {
                collect_bound_names(p, out);
            }
        }
        Pattern::Tuple { positional, named } => {
            for p in positional {
                collect_bound_names(p, out);
            }
            for (_, p) in named {
                collect_bound_names(p, out);
            }
        }
    }
}

fn reduce_vec(
    kb: &KnowledgeBase,
    xs: &[Rc<NodeOccurrence>],
    env: &Env,
    pass: PassId,
) -> Option<Vec<Rc<NodeOccurrence>>> {
    let mut out = Vec::with_capacity(xs.len());
    for x in xs {
        out.push(reduce(kb, x, env, pass)?);
    }
    Some(out)
}

fn reduce_named(
    kb: &KnowledgeBase,
    xs: &[(Symbol, Rc<NodeOccurrence>)],
    env: &Env,
    pass: PassId,
) -> Option<Vec<(Symbol, Rc<NodeOccurrence>)>> {
    let mut out = Vec::with_capacity(xs.len());
    for (s, x) in xs {
        out.push((*s, reduce(kb, x, env, pass)?));
    }
    Some(out)
}

fn rebuild(from: &Rc<NodeOccurrence>, expr: Expr, pass: PassId) -> Rc<NodeOccurrence> {
    NodeOccurrence::synthesized_expr(expr, Rc::clone(from), pass, from.owner)
}

impl KnowledgeBase {
    /// Derive `op`'s defining equations from its body (design §3.4.1, WI-669):
    /// the op's parameters become DeBruijn vars (`?0`…), the body is specialized
    /// one step, and each `if`-branch path yields a guarded [`DefiningEquation`]
    /// over those vars — as occurrences (carrier-neutral; see the type doc).
    /// Returns `None` — a loud decline — when the body is not a pure,
    /// `match`/`let`-free bodied op (see [`defining_equations`]).
    ///
    /// The parameter frame is `Var::DeBruijn` (rule storage convention, see
    /// `rustland/CLAUDE.md` "De Bruijn Variables"), so a consumer can assert each
    /// equation as a transient rule whose body the SMT emitter inlines unchanged.
    pub fn op_defining_equations(&mut self, op: Symbol) -> Option<Vec<DefiningEquation>> {
        let info = lookup_operation_info(self, op)?;
        let span = info.body_node.as_ref()?.span;
        let pos_args: Vec<Rc<NodeOccurrence>> = (0..info.params.len())
            .map(|i| NodeOccurrence::new_expr(Expr::Var(Var::DeBruijn(i as u32)), span, None))
            .collect();
        defining_equations(self, op, &pos_args, &[])
    }
}

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

use smallvec::SmallVec;

use crate::eval::pattern::functor_matches;
use crate::intern::{Symbol, SymbolKind};
use crate::span::SourceSpan;

use super::node_occurrence::{Expr, MatchBranch, NodeOccurrence, Pattern};
use super::occurrence::PassId;
use super::op_info::lookup_operation_info;
use super::term::{Literal, Term, TermId, Var, VarId};
use super::{KnowledgeBase, RuleId};

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
/// equations need SMT datatype support — future) or any higher-order /
/// post-elaboration shape. A simple `let name = value` binding IS admitted
/// (WI-679): [`reduce`] inlines it; a destructuring / wildcard `let` still
/// declines.
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
    // Purity gate (design §9 + proposal 054 §"Consumers that must decline it —
    // loudly", WI-702). An EFFECTFUL body is not a function, so it has no defining
    // equations; a `requires` body owes a dictionary this increment cannot thread
    // as an equation antecedent (a future relaxation, §3.4.1). Decline BOTH — but
    // SILENTLY here: `defining_equations` is a shared reducer reached from the
    // tolerant proof-time goal-closure sweep (`synthesize_body_derived_defrules`),
    // so an unconditional diagnostic here would double-fire (generic +
    // per-call-site synth) and spam every effectful goal. The sweep is the one
    // consumer that treats an effectful op as a category error, and it emits the
    // LOUD, deduped diagnostic naming the op + row at that call site instead
    // ([`Self::effect_row_blocking_equations`]). The SLD/relational value-fold
    // paths (`folded_call_match`, `bare_bodied_bool_relation`) stay silent too.
    // (Any future memoization / CSE consumer joins the same decline.)
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
        Expr::Var(_) | Expr::Const(_) | Expr::Spliced(_) | Expr::Bottom => Some(Rc::clone(occ)),

        // ── match: reduce when the scrutinee's shape is statically known ──
        Expr::Match { scrutinee, branches } => reduce_match(kb, occ, scrutinee, branches, env, pass),

        // ── let: inline a simple `let name = value in body` binding ──
        // Reduce the value, bind the pattern var to it, and reduce the
        // continuation under the extended env — so a reference to `name` in
        // `body` splices the reduced value in place. This is the operational
        // face of proposal-050 Γ's binding component; it mirrors `reduce_match`'s
        // Env extension (value reduced under the OUTER env, so the binder cannot
        // capture into its own value). ONLY a top-level single binder
        // (`Pattern::Var` — including the `(x)` / `(x: T)` forms that lower to
        // it) is specialized: binding the whole value to that one name IS its
        // meaning. A destructuring pattern (`some(a)`, `(a, b)`) must PROJECT the
        // value, which this arm does not do, so anything but `Pattern::Var` is a
        // *loud* decline (the whole inline bails) rather than silently binding a
        // projection variable to the un-projected value — escalate destructuring
        // lets to their own ticket if a body needs them (WI-679 scope note).
        Expr::Let { pattern, value, body, .. } => {
            let Some(Pattern::Var { name, .. }) = pattern.as_pattern() else {
                return None;
            };
            let val = reduce(kb, value, env, pass)?;
            let mut env2 = env.clone();
            env2.push((*name, val));
            reduce(kb, body, &env2, pass)
        }

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
            // ── field projection (WI-687): a `field_access(recv, f)` whose
            // receiver reduces to a statically-known constructor projects to the
            // named field, so a body that `match`es (or otherwise reads) a field
            // of a concrete-constructor argument reduces at synth time. When the
            // receiver is NOT a known constructor — the abstract-parameter
            // generic synth (WI-681 `desired_position`), where `?0.position`
            // stays a residual read the SMT emitter later resolves via its
            // `entity_bindings` — fall through and keep the field access residual.
            if let Some((recv, fname)) = field_access_parts(kb, *functor, pos_args) {
                let recv_r = reduce(kb, &recv, env, pass)?;
                if let Some(fields) = ctor_field_occs(kb, &recv_r) {
                    let Some((_, val)) = fields.iter().find(|(f, _)| short_of(kb, *f) == fname)
                    else {
                        // Known constructor lacking the projected field — a
                        // malformed body; decline loudly, never emit a wrong read.
                        return None;
                    };
                    return Some(Rc::clone(val));
                }
                // Residual field access over a non-constructor receiver: rebuild
                // with the ALREADY-reduced receiver (reusing `recv_r` — don't reduce
                // it a second time) and the reduced remaining args (the selector).
                let mut pos = Vec::with_capacity(pos_args.len());
                pos.push(recv_r);
                for a in &pos_args[1..] {
                    pos.push(reduce(kb, a, env, pass)?);
                }
                let named = reduce_named(kb, named_args, env, pass)?;
                return Some(rebuild(
                    occ,
                    Expr::Apply {
                        functor: *functor,
                        pos_args: pos,
                        named_args: named,
                        type_args: type_args.clone(),
                    },
                    pass,
                ));
            }
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

        // Any other form (lambda / higher-order / post-elaboration) is not
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

/// Recognize an operation-body field projection `field_access(recv, field)` and
/// return `(receiver, field short-name)`. A reduced/loaded op body encodes
/// `x.f` as `Apply{field_access, [recv, Const::String(f)]}` (WI-681); the
/// reflect selector may also be a bare `Ident`/`Ref`. Returns `None` for any
/// non-field-access application.
///
/// NB: `anthill-smt-gen`'s `as_field_access` recognizes the SAME reflect form
/// (same QN check, same three selector shapes) for its own lowering — the two
/// are independent copies of one desugaring contract across the crate boundary;
/// a new selector form must be mirrored in both. `pub(crate)` so the WI-714
/// `where` row-lambda→query compiler (`eval::builtins::compile_operand`) reads a
/// column reference `c.x` through this SAME contract rather than a third copy —
/// and so `compile_condition` can refuse a projection in CONDITION position by the
/// same recognizer (WI-730).
pub(crate) fn field_access_parts(
    kb: &KnowledgeBase,
    functor: Symbol,
    pos_args: &[Rc<NodeOccurrence>],
) -> Option<(Rc<NodeOccurrence>, String)> {
    let qn = kb.qualified_name_of(functor);
    if qn != "anthill.reflect.field_access" && qn != "field_access" {
        return None;
    }
    let [obj, field] = pos_args else { return None };
    let name = match field.as_expr()? {
        Expr::Const(Literal::String(s)) => s.clone(),
        Expr::Ref(s) | Expr::Ident(s) => short_of(kb, *s).to_string(),
        _ => return None,
    };
    Some((Rc::clone(obj), name))
}

/// The data-constructor functor and child occurrences of a construction
/// application (an entity or ADT-variant build), or `None` for a
/// non-constructor occurrence. Recognizes `Constructor`/`Instantiation`, an
/// `Apply` whose functor is a data constructor, and a bare nullary constructor
/// `Ref`/`Ident`. Used by [`skeletonize`] to preserve a call argument's
/// constructor spine (WI-687).
#[allow(clippy::type_complexity)]
fn occ_as_ctor(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
) -> Option<(Symbol, Vec<Rc<NodeOccurrence>>, Vec<(Symbol, Rc<NodeOccurrence>)>)> {
    let is_data = |f: Symbol| kb.entity_field_types(f).is_some() || kb.is_constructor_symbol(f);
    match occ.as_expr()? {
        Expr::Constructor { name, pos_args, named_args }
        | Expr::Instantiation { name, pos_args, named_args }
            if is_data(*name) =>
        {
            Some((*name, pos_args.clone(), named_args.clone()))
        }
        Expr::Apply { functor, pos_args, named_args, .. } if is_data(*functor) => {
            Some((*functor, pos_args.clone(), named_args.clone()))
        }
        Expr::Ref(s) | Expr::Ident(s) if kb.kind_of(*s) == Some(SymbolKind::Entity) => {
            Some((*s, Vec::new(), Vec::new()))
        }
        _ => None,
    }
}

/// A per-call-site *shape skeleton* of an argument occurrence (WI-687): the
/// argument's data-constructor spine is preserved verbatim while every
/// non-constructor leaf is replaced by a FRESH `Var::Global`. Binding an
/// operation parameter to this skeleton lets [`reduce`] decide a `match` on the
/// parameter (or on one of its fields — the constructor heads are statically
/// known) while keeping the derived rule generic in the leaf values: the SMT
/// emitter binds each fresh leaf to the caller's actual sub-term when it inlines
/// the synthesized rule (`try_inline_rule_call`'s structural head binding).
fn skeletonize(kb: &mut KnowledgeBase, arg: &Rc<NodeOccurrence>) -> Rc<NodeOccurrence> {
    if let Some((name, pos, named)) = occ_as_ctor(kb, arg) {
        let pos2: Vec<_> = pos.iter().map(|p| skeletonize(kb, p)).collect();
        let named2: Vec<_> = named.iter().map(|(s, v)| (*s, skeletonize(kb, v))).collect();
        return NodeOccurrence::new_expr(
            Expr::Constructor { name, pos_args: pos2, named_args: named2 },
            arg.span,
            arg.owner,
        );
    }
    let name = kb.intern("defeq_arg");
    let g = kb.fresh_var(name);
    NodeOccurrence::new_expr(Expr::Var(Var::Global(g)), arg.span, arg.owner)
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

/// Refold the flattened guarded arms (design §3.4.1) back into ONE nested
/// `Expr::If` occurrence — `ite(conj(g₀), r₀, ite(conj(g₁), r₁, … r_last))` —
/// dropping the *last* arm's guard: the arm set is exhaustive and ordered, so
/// the final arm is the unconditional fallthrough. A single-arm body (no guards)
/// folds to its bare result (no `if`). This is the SMT-consumable form of the
/// equation set; `conj_of_guards` builds each non-last arm's guard.
///
/// Note the refold *hoists* each arm's guards out of their original control-flow
/// nesting into one flat conjunction (an inner `if`'s condition is `and`-ed with
/// the outer conditions rather than staying nested). That is sound only because
/// this increment's admitted guards — arithmetic/boolean comparisons — are
/// **total** in SMT-LIB (evaluating a guard outside the branch that originally
/// reached it can't fault). If the admitted guard fragment ever grows to include
/// a partial operation, the nesting would have to be preserved.
///
/// `None` — a loud decline — if a non-last arm carries no guard (a shape the
/// flattener should never produce) or `Bool.and`/`Bool.not` can't be resolved.
fn refold_defining_equations(
    kb: &mut KnowledgeBase,
    eqs: &[DefiningEquation],
    span: SourceSpan,
) -> Option<Rc<NodeOccurrence>> {
    let (last, rest) = eqs.split_last()?;
    let mut acc = Rc::clone(&last.result);
    for eq in rest.iter().rev() {
        let condition = conj_of_guards(kb, &eq.guards, span)?;
        acc = NodeOccurrence::new_expr(
            Expr::If { condition, then_branch: Rc::clone(&eq.result), else_branch: acc },
            span,
            None,
        );
    }
    Some(acc)
}

/// Conjoin an arm's guards into one boolean-valued occurrence: a negated guard
/// wraps its `cond` in `Bool.not`, several guards join pairwise under `Bool.and`.
/// A single non-negated guard (the top-level-`if` case — the demonstrator and the
/// lf1 GPS consumer) returns its `cond` unchanged, so those need neither builder.
/// `None` if the guard list is empty (a non-last arm always has ≥1 guard — a loud
/// decline if that invariant breaks) or `Bool.and`/`not` isn't resolvable.
fn conj_of_guards(
    kb: &mut KnowledgeBase,
    guards: &[DefiningGuard],
    span: SourceSpan,
) -> Option<Rc<NodeOccurrence>> {
    let mut terms: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(guards.len());
    for g in guards {
        let cond = Rc::clone(&g.cond);
        let term = if g.negated {
            let not_sym = kb.try_resolve_symbol("anthill.prelude.Bool.not")?;
            NodeOccurrence::new_expr(
                Expr::Apply {
                    functor: not_sym,
                    pos_args: vec![cond],
                    named_args: Vec::new(),
                    type_args: Vec::new(),
                },
                span,
                None,
            )
        } else {
            cond
        };
        terms.push(term);
    }
    let mut it = terms.into_iter();
    let mut acc = it.next()?;
    for term in it {
        let and_sym = kb.try_resolve_symbol("anthill.prelude.Bool.and")?;
        acc = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: and_sym,
                pos_args: vec![acc, term],
                named_args: Vec::new(),
                type_args: Vec::new(),
            },
            span,
            None,
        );
    }
    Some(acc)
}

/// The head functor of a rule-body goal occurrence (a relational atom), or
/// `None` for a non-`Apply` goal. Used by the WI-669 inc-1b seam to find bodied
/// op-calls in a proof obligation's body.
fn goal_functor(goal: &Rc<NodeOccurrence>) -> Option<Symbol> {
    match goal.as_expr()? {
        Expr::Apply { functor, .. } => Some(*functor),
        _ => None,
    }
}

/// The `n` leading positional argument occurrences of a relational op-call goal
/// `op(a₀…a_{n-1}, result)` — the value arguments the per-call-site synthesis
/// (WI-687) specializes at. The trailing result slot is dropped (the synth mints
/// its own fresh result var). `None` when the goal carries named args, or its op
/// has no known arity, or it supplies fewer than `n` positional args.
fn goal_value_args(
    kb: &KnowledgeBase,
    goal: &Rc<NodeOccurrence>,
    op: Symbol,
) -> Option<Vec<Rc<NodeOccurrence>>> {
    let Some(Expr::Apply { pos_args, named_args, .. }) = goal.as_expr() else {
        return None;
    };
    if !named_args.is_empty() {
        return None;
    }
    let n = lookup_operation_info(kb, op)?.params.len();
    Some(pos_args.get(..n)?.to_vec())
}

impl KnowledgeBase {
    /// Proposal 054 §"Consumers that must decline it — loudly" (WI-702): the
    /// rendered effect row of `op` when that row is NON-EMPTY, else `None`.
    ///
    /// An operation with any effect is NOT A FUNCTION, so it has no defining
    /// equations: for an `External` op `f(x) = f(x)` need not even hold across
    /// two calls, and a `Modify`/`Error` op is not an equation either — the gate's
    /// predicate is FUNCTION-HOOD, not the absence of one named effect (design
    /// §"Consumers"). Two consumers name this row in a LOUD decline rather than a
    /// silent absence: the proof-time goal-closure sweep
    /// ([`Self::synthesize_body_derived_defrules`], deduped once per op) and the
    /// load-time `[simp]`/`[unfold]` formation gate (`check_simp_effectful_ops`,
    /// as a `TypeError`). A test asserts this predicate directly so the mechanism
    /// is non-vacuous.
    ///
    /// A pure op → `None`. A `requires`-only op → `None` too: its equation decline
    /// is deliberately SILENT (carrying the dictionary as an equation antecedent is
    /// a future relaxation, §3.4.1, not a category error), so this predicate keys on
    /// the effect row alone.
    ///
    /// CONSERVATIVE on an effect-POLYMORPHIC op: an open row whose only member is a
    /// tail variable (`effects E`) has a non-empty `info.effects` (the var rides as
    /// a list element), so it is reported as blocking. That is deliberate and sound
    /// — the rewrite / equation would fire on EVERY instantiation, including an
    /// effectful one — even though it over-refuses the specific pure (`E = {}`)
    /// instantiation. No stdlib rule mentions such an op (the whole-stdlib load in
    /// `github_todo_test` is the standing control); weakening to present-labels-only
    /// would make the gate unsound for the effectful instantiation.
    pub fn effect_row_blocking_equations(&self, op: Symbol) -> Option<String> {
        let info = lookup_operation_info(self, op)?;
        if info.effects.is_empty() {
            return None;
        }
        let labels: Vec<String> = info
            .effects
            .iter()
            .map(|e| super::typing::type_display_name_value(self, e))
            .collect();
        Some(format!("{{{}}}", labels.join(", ")))
    }

    /// Derive `op`'s defining equations from its body (design §3.4.1, WI-669):
    /// the op's parameters become DeBruijn vars (`?0`…), the body is specialized
    /// one step, and each `if`-branch path yields a guarded [`DefiningEquation`]
    /// over those vars — as occurrences (carrier-neutral; see the type doc).
    /// Returns `None` — a loud decline — when the body is not a pure,
    /// `match`-free bodied op (a simple `let` IS inlined; see
    /// [`defining_equations`]).
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

    /// WI-669 inc-1b — synthesize a defining rule for a bodied `op` from its
    /// body-derived equations, so the SMT emitter can inline it at an
    /// `op(args, result)` call in a proof body (design §3.4.1). The rule is
    /// **run-scoped, not retracted**: it is registered under the op's functor and
    /// persists in the KB (see [`Self::synthesize_body_derived_defrules`] for why
    /// that is benign — the prove driver discards the KB on return). The rule is
    /// `op(?0…?n-1, ?result) :- ?result = <refolded-if>`, the arms refolded into
    /// one nested `Expr::If`. Returns the rule id, or `None` — a *loud* decline —
    /// when `op` has no admissible defining equations (effectful / `requires` /
    /// `match` body; see [`op_defining_equations`]). Idempotent: an
    /// existing defining rule (a prior synth, or a hand-written one) is returned
    /// as-is.
    ///
    /// The head **functor is `op` itself** (labeled `<op_qn>__defeq`) so the
    /// emitter's ordinary `rules_by_functor → try_inline_rule_call` path picks it
    /// up unchanged. Built over **fresh `Var::Global`s** — not the raw
    /// `Var::DeBruijn`s [`op_defining_equations`] emits — because
    /// [`Self::assert_rule_debruijn_with_nodes`] derives the rule's arity from the
    /// *Global* head/body vars it collects; feeding raw DeBruijn would leave the
    /// collector with zero head vars and mint a malformed arity-0 rule.
    pub fn synthesize_op_defining_rule(&mut self, op: Symbol) -> Option<RuleId> {
        // Idempotent — reuse any existing (synth or hand-written) defining rule.
        if let Some(rid) = self.rules_by_functor(op).into_iter().find(|r| !self.is_fact(*r)) {
            return Some(rid);
        }
        // Probe admissibility over the DeBruijn frame FIRST (no fresh vars): a
        // declined body (`match`/effectful) bails here, so a repeatedly
        // scanned non-synthesizable op never leaks the rule-frame `fresh_var`s
        // below across obligations (the idempotency short-circuit can't fire for
        // a declined op — no rule is ever created).
        self.op_defining_equations(op)?;
        let info = lookup_operation_info(self, op)?;
        let n = info.params.len();
        let span = info.body_node.as_ref()?.span;

        // Fresh Globals: one per parameter (named for readability). The result
        // Global is allocated by `assert_defining_rule`.
        let param_vars: Vec<VarId> =
            (0..n).map(|i| self.fresh_var(info.params[i].0)).collect();

        // Occurrence params → the arms carry these Globals; the head args are the
        // SAME Globals as `Term::Var`, so head/body share one De Bruijn frame.
        let pos_args: Vec<Rc<NodeOccurrence>> = param_vars
            .iter()
            .map(|g| NodeOccurrence::new_expr(Expr::Var(Var::Global(*g)), span, None))
            .collect();
        let eqs = defining_equations(self, op, &pos_args, &[])?;
        let head_args: SmallVec<[TermId; 4]> =
            param_vars.iter().map(|g| self.alloc(Term::Var(Var::Global(*g)))).collect();
        self.assert_defining_rule(op, &eqs, head_args, span)
    }

    /// Shared tail of the two defining-rule synthesizers (WI-669 generic /
    /// WI-687 per-call-site): from the derived `eqs` and the already-built head
    /// argument terms (fresh-Global params for the generic path, skeleton
    /// constructor terms for the per-call-site path), refold the arms into one
    /// nested `Expr::If`, build the rule `op(<args>, ?result) :- ?result = <if>`
    /// over a FRESH result Global, assert it under `op`'s own functor, and label
    /// it `<op_qn>__defeq` (idempotency + debuggability). The head args must carry
    /// `Var::Global` leaves (not raw De Bruijn) so
    /// [`Self::assert_rule_debruijn_with_nodes`]' collector derives the arity;
    /// the appended result Global becomes the trailing (highest-index) param.
    fn assert_defining_rule(
        &mut self,
        op: Symbol,
        eqs: &[DefiningEquation],
        mut head_args: SmallVec<[TermId; 4]>,
        span: SourceSpan,
    ) -> Option<RuleId> {
        let if_occ = refold_defining_equations(self, eqs, span)?;

        // Body node: `?result = <refolded-if>` over a fresh result Global.
        let result_name = self.intern("defeq_result");
        let result_var = self.fresh_var(result_name);
        let eq_sym = self.eq_functor();
        let result_occ =
            NodeOccurrence::new_expr(Expr::Var(Var::Global(result_var)), span, None);
        let body_node = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: eq_sym,
                pos_args: vec![result_occ, if_occ],
                named_args: Vec::new(),
                type_args: Vec::new(),
            },
            span,
            None,
        );

        // Head term `op(<args>, g_result)` — the result Global is the trailing arg.
        head_args.push(self.alloc(Term::Var(Var::Global(result_var))));
        let head = self.alloc(Term::Fn {
            functor: op,
            pos_args: head_args,
            named_args: SmallVec::new(),
        });

        let rule_sort = self.make_name_term("Rule");
        let global_scope = self.make_name_term("_global");
        let rid = self.assert_rule_debruijn_with_nodes(
            head,
            vec![body_node],
            rule_sort,
            global_scope,
            None,
        );

        // Stable QN `<op_qn>__defeq` (idempotency + debuggability).
        let op_qn = self.qualified_name_of(op).to_string();
        let defeq_qn = format!("{op_qn}__defeq");
        let short = defeq_qn.rsplit('.').next().unwrap_or(&defeq_qn).to_string();
        let label_sym =
            self.define_symbol(&short, &defeq_qn, SymbolKind::Rule, global_scope.raw());
        self.set_rule_label(rid, label_sym);
        Some(rid)
    }

    /// WI-687 — synthesize a defining rule for a **match-headed** bodied `op` by
    /// specializing its body at a proof call-site's concrete-constructor
    /// arguments. Where [`Self::synthesize_op_defining_rule`] builds ONE generic
    /// rule over fresh Globals — which cannot reduce a `match` whose scrutinee is
    /// an abstract parameter (or a field of one) — this reads the shape of the
    /// actual call arguments (`value_args`, a state constructor with
    /// `some(...)`/`none` Option fields, etc.), builds a fresh-Global *shape
    /// skeleton* per argument ([`skeletonize`]), and specializes at the skeleton.
    /// The known constructor heads let [`reduce`] decide the `match` (and project
    /// field reads) while the skeleton's fresh leaves keep the rule generic in
    /// the leaf values.
    ///
    /// The head is therefore **constructor-shaped** — `op(some(?0), ?1, ?result)`
    /// rather than `op(?0, ?1, ?result)` — so the SMT emitter's inline path binds
    /// the head structurally against the call (`try_inline_rule_call` recurses a
    /// constructor head arg against the caller's construction, WI-687). The head
    /// functor is `op` itself (label `<op_qn>__defeq`), so `rules_by_functor →
    /// try_inline_rule_call` finds it exactly as for the generic path.
    ///
    /// Returns `None` — a loud decline — when `op` is not a pure runnable bodied
    /// op, the arity doesn't fit, or the body still doesn't reduce at these
    /// argument shapes (e.g. a `match` on a field whose call argument was not a
    /// concrete constructor). A decline creates NO rule, so the idempotency check
    /// stays correct on a re-scan; the skeleton's fresh vars leak (a bounded
    /// handful per declined goal, benign — just a counter bump, no facts/index
    /// entries). Idempotent on success: an existing defining rule under `op`'s
    /// functor (a prior per-call-site or generic synth) is returned as-is, so a
    /// second obligation goal for the same op reuses it (one shape per op in this
    /// increment — a genuinely different-shape second call would inline the first
    /// rule and fail the emitter's structural head match loudly, never silently).
    pub fn synthesize_op_defining_rule_at(
        &mut self,
        op: Symbol,
        value_args: &[Rc<NodeOccurrence>],
    ) -> Option<RuleId> {
        // Idempotent — reuse any existing (per-call-site or generic) defining rule.
        if let Some(rid) = self.rules_by_functor(op).into_iter().find(|r| !self.is_fact(*r)) {
            return Some(rid);
        }
        if !super::typing::op_has_runnable_body(self, op) {
            return None;
        }
        let info = lookup_operation_info(self, op)?;
        let n = info.params.len();
        if value_args.len() != n {
            return None;
        }
        let span = info.body_node.as_ref()?.span;

        // Fresh-Global shape skeletons for each argument: the constructor spine is
        // preserved (so a `match` on it reduces) with fresh leaves (so the rule is
        // generic in the leaf values). Both the head term and the reduced body
        // reference the SAME skeleton Globals — `assert_rule_debruijn_with_nodes`
        // collects them head-first and closes to a consistent De Bruijn frame.
        let skeletons: Vec<Rc<NodeOccurrence>> =
            value_args.iter().map(|a| skeletonize(self, a)).collect();
        let eqs = defining_equations(self, op, &skeletons, &[])?;

        // Head args: each skeleton lowers to its constructor/var term twin (data
        // only — no control flow — so `occurrence_to_term` is total here). The
        // shared `assert_defining_rule` refolds the arms, appends the result var,
        // asserts, and labels — identical to the generic path.
        let head_args: SmallVec<[TermId; 4]> = skeletons
            .iter()
            .map(|s| super::node_occurrence::occurrence_to_term(self, s))
            .collect();
        self.assert_defining_rule(op, &eqs, head_args, span)
    }

    /// WI-669 inc-1b seam entry: scan `rule_qn`'s body for goals that call a
    /// **rule-less bodied op** and synthesize a defining rule for each, so the SMT
    /// emitter inlines the body-derived definition (no hand-written twin). A no-op
    /// for a rule that calls no such op, and idempotent (re-run over the same
    /// obligation adds nothing). Called by the prove driver before emitting an
    /// obligation to z3.
    ///
    /// Scope (all loud, never a silent wrong answer):
    /// - The scan is **transitive** over the rules the emitter will inline: the
    ///   obligation's own body goals, plus the bodies of every defined rule those
    ///   goals call *in goal position*, recursively (WI-681 — the lf1 GPS
    ///   obligation reaches `desired_position` a level below its direct body,
    ///   through `reachable_real_formation`). It does NOT follow `using`-cited
    ///   lemmas (their bodies are lifted, not inlined), nor bodied-op calls in
    ///   *value* position nested inside an expression (those are the resolver's
    ///   §3.3 value-fold, a different mechanism; the emitter rejects an
    ///   unhandled value-position op call loudly). Termination is by a
    ///   visited-rule set, so a recursive predicate (`real_pose_at`) is walked
    ///   once.
    /// - A bodied op whose GENERIC (abstract-parameter) synthesis declines — a
    ///   `match`-headed body, whose scrutinee is a parameter or a field of one —
    ///   is retried **per call-site** (WI-687): the goal's concrete-constructor
    ///   arguments are specialized (`synthesize_op_defining_rule_at`) so the
    ///   `match` reduces at the actual argument shapes. If that also declines
    ///   (the call did not supply a concrete constructor), the op is left
    ///   un-synthesized and the emitter rejects it loudly at its own goal
    ///   boundary (`unhandled body goal functor`).
    /// - Only a rule-less op with an actual `= body` is a synth candidate;
    ///   bodyless prelude ops (`add`/`cos`/…, no body_node) are never synthesized
    ///   — the emitter lowers them directly (arith / trig).
    /// - The synth rule is registered under the op's own functor and lives in the
    ///   KB for the rest of the prove run (the driver discards the KB on return).
    ///   It is semantically faithful (the op's true body), so this never yields a
    ///   wrong answer; but a later `by derivation` proof that calls the same op
    ///   *relationally* in the SAME run would see it — a benign order-dependency
    ///   the resolver's own §3.3 body-fold makes moot for value-position calls.
    pub fn synthesize_body_derived_defrules(&mut self, rule_qn: &str) {
        let Some(root) = self.rule_id_by_qn(rule_qn) else {
            return;
        };
        let mut visited: std::collections::HashSet<RuleId> = std::collections::HashSet::new();
        // Functors already synth-attempted — one attempt per op across the whole
        // scan (synthesis is idempotent, and the per-call-site path uses the FIRST
        // goal's shape; a repeat goal for the same op would only re-do work).
        let mut attempted: std::collections::HashSet<Symbol> = std::collections::HashSet::new();
        let mut worklist: Vec<RuleId> = vec![root];
        while let Some(rid) = worklist.pop() {
            if !visited.insert(rid) {
                continue;
            }
            // Clone the body goals (owned Rcs) so the &mut synth calls below don't
            // hold the immutable `rule_body_nodes` borrow. We iterate GOALS, not
            // just distinct functors, because the per-call-site path (WI-687)
            // needs each goal's actual argument occurrences.
            let goals: Vec<Rc<NodeOccurrence>> = self.rule_body_nodes(rid).to_vec();
            for goal in &goals {
                let Some(f) = goal_functor(goal) else { continue };
                // `f` must resolve to the operation itself — call the op qualified
                // enough to bind (a bare relation name that doesn't resolve to the
                // op is left to the emitter's loud "unhandled body goal functor").
                let clauses = self.rules_by_functor(f);
                let rule_less = clauses.iter().all(|r| self.is_fact(*r));
                if rule_less {
                    // A rule-less bodied op — synthesize its defining rule ONCE. Try
                    // the generic (abstract-parameter) path first; if it declines (a
                    // `match`-headed body won't reduce over abstract params), fall
                    // to per-call-site specialization at THIS goal's concrete args.
                    if attempted.insert(f) && super::typing::op_has_runnable_body(self, f) {
                        // Proposal 054 §"Consumers that must decline it — loudly"
                        // (WI-702): an EFFECTFUL bodied op is not a function, so it
                        // has no defining equations. This proof-time goal-closure
                        // sweep IS the "specifically requested" path the ticket
                        // names; its `attempted` set dedups per op, so emit the LOUD
                        // decline HERE (once), naming the op + row, and skip the
                        // synth attempts (they decline silently in
                        // `defining_equations`; the emitter then rejects the
                        // un-synthesized goal downstream). Emitting here — not inside
                        // the shared reducer — is what keeps it from double-firing.
                        if let Some(row) = self.effect_row_blocking_equations(f) {
                            eprintln!(
                                "[anthill] operation `{}` carries effect row {row} — \
                                 an effectful operation is not a function, so it has \
                                 no defining equations (proposal 054 §\"Consumers \
                                 that must decline it\")",
                                self.qualified_name_of(f),
                            );
                            continue;
                        }
                        if self.synthesize_op_defining_rule(f).is_none() {
                            if let Some(args) = goal_value_args(self, goal, f) {
                                let _ = self.synthesize_op_defining_rule_at(f, &args);
                            }
                        }
                    }
                } else {
                    // A defined rule the emitter would inline — recurse into its
                    // non-fact clauses so a bodied op called one level down
                    // (`desired_position` inside `reachable_real_formation`) is
                    // reached too.
                    for r in clauses {
                        if !self.is_fact(r) {
                            worklist.push(r);
                        }
                    }
                }
            }
        }
    }
}

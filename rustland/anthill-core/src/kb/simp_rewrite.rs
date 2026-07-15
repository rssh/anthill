//! WI-277 — typer-phase `[simp]` rewriting engine.
//!
//! The second firing site for `[simp]` equational rules (proposal 043 /
//! `docs/design/simp-rewrite-design.md`). As a separate pass over operation
//! bodies (before `type_check_sorts`/`req_insertion`), it fires matching
//! `[simp]` equations LHS→RHS bottom-up over the `NodeOccurrence` tree and
//! writes the rewritten, redex-free tree back via `set_op_body_node`. This
//! is the resolver's `apply_eq_rules` (`resolve.rs`) counterpart for the
//! occurrence representation — "one rewriter, two phases."
//!
//! Reuse: matching is the existing discrimination tree via `match_view`
//! (`Rc<NodeOccurrence>` is a `TermView`, WI-276/277); DeBruijn opening is
//! the KB's `term_from_debruijn`. The only occurrence-specific piece is the
//! build side, [`substitute_to_occurrence`], which constructs the RHS as a
//! `NodeOccurrence` (carrying span + `Synthesized` provenance) on top of the
//! shared `walk_view`.
//!
//! Firing (WI-283) matches an `is_equation` + `[simp]` rule's LHS via
//! `match_view`, then applies the type-directed guard
//! ([`super::typing::simp_fire_guard_holds`]): a rule scoped to a
//! parametric sort (its functor is a *spec op*, e.g. `Numeric.add`) fires
//! only where its carrier arguments' `min_sort` provides that sort; a
//! concrete functor (`add(?x, 0) = ?x` at top level) is guard-free. Loaded
//! equations are headed by the canonical `anthill.prelude.PartialEq.eq`
//! ([`KnowledgeBase::eq_functor`]), the symbol the firing index keys on.
//! Explicit value-level guards (`:- compare(?x, ?y) <= 0`) give the rule a
//! non-empty body, so it is not `is_equation` and not yet indexed for
//! firing — proposal 043 §4.1 / a follow-up.
//!
//! Recursion depth (WI-278): the walk is iterative. [`rewrite`] descends the
//! tree on an explicit `Visit`/`Build` work-stack, and
//! [`substitute_to_occurrence`] builds the RHS on a second work-stack — both
//! mirroring the sibling `NodeOccurrence::Drop`, `materialize_from_handle`,
//! and the typing pass, which were made iterative to survive deeply-nested
//! bodies (the 624-line typing_pass_spec.anthill). This was a prerequisite for
//! shipping `[simp]`/dot rules that fire on real (possibly deeply-nested)
//! operation bodies: the engine can no longer overflow the host stack on
//! source nesting depth.
//!
//! One driver, both carriers (WI-641 Phase 2 + WI-643): [`rewrite`] is
//! carrier-neutral — it descends a [`Value`] that is EITHER a `Value::Node`
//! occurrence (the typer phase; and the resolver's `anthill prove` Node goals)
//! OR a hash-consed term (the resolver's `apply_eq_rules`). The two carriers
//! share the one iterative loop; they differ only in [`children_of`] (descent)
//! and [`reassemble_value`] (reassembly), and in the firing STRATEGY behind the
//! [`SimpFirer`] trait. This retired the resolver's separate recursive term
//! walk, so a deeply-nested term redex no longer overflows the host stack nor
//! stops at a fuel-as-depth cutoff.

use std::rc::Rc;

use smallvec::SmallVec;

use crate::eval::value::Value;
use crate::intern::Symbol;

use super::load::meta_has_flag;
use super::node_occurrence::{self, Expr, MatchBranch, NodeOccurrence};
use super::occurrence::PassId;
use super::subst::Substitution;
use super::term::{Term, TermId, VarId};
use super::{KnowledgeBase, RuleId};

/// Per-node fixpoint bound — mirrors `apply_eq_rules`'s fuel (`resolve.rs`),
/// keeping the firing sites' termination policy aligned. `pub(super)` so the
/// typer's firing site (`typing::type_check_node`) bounds its fire→re-type
/// recursion by the same constant (WI-283).
pub(super) const SIMP_FUEL: usize = 100;

const PASS_NAME: &str = "anthill.kb.passes.simp_rewrite";

/// Whether any indexed `[simp]` equation exists — the gate the typer's firing
/// sites (`typing::type_check_node`'s `simp_enabled`, and [`run`]) use to skip
/// all firing work in the common no-rule case. Read once per typer walk (WI-283)
/// and once per [`run`]. Not cached (the typer runs at load, not the SLD hot
/// path — the resolver's O(1) `has_directional_rewrite` gate is the cached one).
///
/// WI-646: selects over BOTH the `eq` (`=`) AND `unify` (`<=>`) functor buckets
/// via the shared [`KnowledgeBase::simp_equation_rids`] — fixing the former
/// `eq`-only narrowness that left the typer UNDER-firing for a KB whose `[simp]`
/// laws are all `<=>`-headed (the stdlib case: 14/14) and which has no
/// dot-applies. The `[simp]`-only per-rule filter is kept deliberately: it
/// matches the typer's `try_fire`, which fires `[simp]` (never `[unfold]`), so
/// gating on `[simp]` OR `[unfold]` would enable a wasted (always-declining) walk
/// on an unfold-only KB. (The resolver's `has_directional_rewrite` gate, by
/// contrast, IS `[simp]` OR `[unfold]` — it fronts a firer that fires both.)
pub(super) fn has_simp_equations(kb: &mut KnowledgeBase) -> bool {
    kb.simp_equation_rids().into_iter().any(|rid| is_simp_equation(kb, rid))
}

/// WI-646: the typer's per-rule fire predicate — `rid` is a `[simp]`-tagged
/// EQUATION. Shared by `try_fire` AND the `has_simp_equations` gate so the two
/// can't drift (the typer's peer of the resolver's `is_directional_equation`).
/// `[simp]`-only, not `[simp]`/`[unfold]`: the typer fires only `[simp]` (never
/// `[unfold]`), so gating on both would enable an always-declining walk.
fn is_simp_equation(kb: &KnowledgeBase, rid: RuleId) -> bool {
    kb.is_equation(rid) && meta_has_flag(kb, kb.rule_meta(rid), "simp")
}

/// The `PassId` tagging `[simp]`-synthesized occurrences. Idempotent
/// (`register_pass` interns the name), so the typer firing site can fetch
/// it per fire without threading it through the work-stack.
pub(super) fn simp_pass(kb: &mut KnowledgeBase) -> PassId {
    kb.register_pass(PASS_NAME)
}

/// The firing strategy for the shared iterative driver [`rewrite`] (WI-641
/// Phase 2, generalized to both carriers in WI-643). Both simp phases descend
/// the SAME `Visit`/`Build` work-stack over the carrier-neutral [`Value`]; they
/// differ ONLY in what "fire a `[simp]` equation at this node" means — the typer
/// fires type-directed via [`try_fire`] ([`TyperFirer`]), the resolver fires
/// carrier-neutrally via `fire_simp_equation` (recording `EqChange`s;
/// `ResolverSimpFirer` in `resolve.rs`). Factored as a trait — not a closure —
/// so the firer can hold its own `&mut` state (the resolver's changes vec)
/// without a borrow conflict against the `&mut KnowledgeBase` the driver threads.
/// This replaced the resolver's former recursive `apply_eq_rules_occurrence`
/// walk (WI-641) AND its recursive TERM walk (WI-643), so a deeply-nested redex
/// — Node OR term — rewrites on the heap instead of overflowing the host stack.
pub(super) trait SimpFirer {
    /// Try to fire a `[simp]` equation at `redex` (a term or `Value::Node`
    /// occurrence); return the rewritten carrier-neutral `Value`, or `None`
    /// when nothing fires. `rids` are the candidate equation ids
    /// ([`KnowledgeBase::simp_equation_rids`]) gathered ONCE per [`rewrite`] walk
    /// and threaded in (WI-646) — so a per-node fire no longer re-scans the
    /// `eq`+`unify` functor buckets (2 `Vec` allocs) at every node.
    fn fire(&mut self, kb: &mut KnowledgeBase, redex: &Value, rids: &[RuleId]) -> Option<Value>;
}

/// The typer's firing strategy: type-directed [`try_fire`], carrying the
/// `[simp]`-synthesis `PassId` the RHS builder stamps onto new nodes.
pub(super) struct TyperFirer {
    pub(super) pass: PassId,
}

impl SimpFirer for TyperFirer {
    fn fire(&mut self, kb: &mut KnowledgeBase, redex: &Value, rids: &[RuleId]) -> Option<Value> {
        // The typer only ever walks operation bodies, which are occurrence
        // trees — every node the driver hands it is a `Value::Node` (the
        // occurrence carrier is closed under descent + rewrite). A non-Node
        // here is a carrier-routing bug, not a recoverable case.
        match redex {
            Value::Node(occ) => try_fire(kb, occ, self.pass, rids).map(Value::Node),
            other => unreachable!(
                "typer simp carrier is always an occurrence, got {}",
                other.type_name()
            ),
        }
    }
}

/// Entry point: rewrite every operation body by firing `[simp]` equations,
/// writing each rewritten (redex-free) tree back into `kb.op_bodies`.
///
/// Retired from the load pipeline in WI-283 — firing now runs *in the
/// typer* (`typing::build_type`), where it is type-directed. Kept as the
/// helper-level test harness exercising [`try_fire`] / [`reassemble`] /
/// [`substitute_to_occurrence`] over the bare occurrence representation.
pub fn run(kb: &mut KnowledgeBase) {
    if !has_simp_equations(kb) {
        return;
    }
    let pass = kb.register_pass(PASS_NAME);
    let mut firer = TyperFirer { pass };
    // Snapshot (op_sym, body) so we don't hold a borrow on `op_bodies` while
    // rewriting (which mutates `kb` — fresh vars, interning).
    let bodies: Vec<(Symbol, Rc<NodeOccurrence>)> =
        kb.op_bodies_iter().map(|(s, n)| (s, Rc::clone(n))).collect();
    for (op_sym, body) in bodies {
        // The driver is carrier-neutral (WI-643): wrap the occurrence body as a
        // `Value::Node` and unwrap the result. The occurrence carrier is closed
        // under rewrite, so a Node in always yields a Node out.
        let rewritten = match rewrite(kb, &Value::Node(Rc::clone(&body)), &mut firer, SIMP_FUEL) {
            Value::Node(n) => n,
            other => unreachable!(
                "typer simp run: an occurrence body must rewrite to a Node, got {}",
                other.type_name()
            ),
        };
        if !Rc::ptr_eq(&rewritten, &body) {
            kb.set_op_body_node(op_sym, rewritten);
        }
    }
}

/// Bottom-up rewrite: rewrite children first, then try firing a `[simp]`
/// equation at this node; on a firing, re-rewrite the result to fixpoint
/// (fuel-bounded). Leftmost-innermost, matching the typer's walk order and
/// `apply_eq_rules`.
///
/// Carrier-neutral (WI-643): the driver descends the SAME work-stack over a
/// carrier-neutral [`Value`] — a hash-consed term OR a `Value::Node` occurrence
/// — so BOTH simp carriers share ONE iterative loop. The only carrier-specific
/// pieces are [`children_of`] (child iteration + the descend test) and
/// [`reassemble_value`] (reassembly); firing is already carrier-neutral through
/// the [`SimpFirer`] (`fire_simp_equation` / `try_fire`). This replaced the
/// resolver's separate recursive TERM walk (`apply_eq_rules` steps 1–2), so a
/// deeply-nested TERM redex no longer stops at the fuel-as-depth cutoff nor risks
/// host-stack overflow — both carriers now spend `fuel` only on the fire→refire
/// chain.
///
/// Iterative (WI-278): an explicit `Visit`/`Build` work-stack flattens the tree
/// descent onto the heap — mirroring [`node_occurrence::materialize_from_handle`]
/// and [`node_occurrence::visit_classifications`], which were made iterative to
/// survive deeply-nested bodies (the 624-line `typing_pass_spec.anthill`).
/// `Visit` schedules a `Build` for every node (fuel permitting) and, for a
/// compound form with children, a `Visit` per child (reversed, so children pop in
/// source order); a fuel-exhausted node passes straight through. `Build` pops the
/// rewritten children, reassembles the node (preserving identity + provenance
/// when nothing changed), then fires a `[simp]` equation at it via the
/// [`SimpFirer`] — INCLUDING at a leaf (`child_count == 0`), so a functor-less
/// leaf redex still gets a fire attempt (WI-641). A firing re-enters the loop via
/// `Visit { fuel - 1 }` so the fixpoint is driven on the stack rather than the
/// host call stack. `fuel` bounds a single fire→refire chain (it descends to
/// children unchanged), exactly as the former recursion did.
pub(super) fn rewrite<F: SimpFirer>(
    kb: &mut KnowledgeBase,
    root: &Value,
    firer: &mut F,
    fuel: usize,
) -> Value {
    // WI-646: gather the eq+unify candidate ids ONCE per walk (rules don't
    // change mid-rewrite — firing synthesizes nodes, never asserts) and thread
    // them into every per-node fire, replacing `try_fire`/`fire_simp_equation`'s
    // former per-node `rules_by_functor` re-scan (amplified by WI-641/643
    // per-node firing).
    let rids = kb.simp_equation_rids();
    let mut work: Vec<RewriteOp> = vec![RewriteOp::Visit { node: root.clone(), fuel }];
    let mut results: Vec<Value> = Vec::new();

    while let Some(op) = work.pop() {
        match op {
            RewriteOp::Visit { node, fuel } => visit_node(kb, node, fuel, &mut work, &mut results),
            RewriteOp::Build { node, fuel, child_count } => {
                build_node(kb, node, fuel, child_count, firer, &rids, &mut work, &mut results)
            }
        }
    }

    debug_assert_eq!(
        results.len(),
        1,
        "rewrite: expected exactly one result on the stack, got {}",
        results.len(),
    );
    results.pop().expect("root produced no Value")
}

/// Work-stack item for the iterative [`rewrite`]. `fuel` rides on the op so
/// the fire→refire chain is bounded per-chain (descending to children
/// unchanged), as in the former recursion.
enum RewriteOp {
    Visit { node: Value, fuel: usize },
    /// `child_count` is the number of child `Visit`s scheduled alongside this
    /// frame — captured at `visit_node` time so `build_node` knows how many
    /// results to claim without re-walking the node.
    Build { node: Value, fuel: usize, child_count: usize },
}

/// Examine a node: schedule a `Build` (which ATTEMPTS a fire at this node) and,
/// for a compound form with children ([`children_of`]), a `Visit` per child so
/// the descent is bottom-up. Children are pushed in reverse source order so they
/// pop — and thus complete — in source order, each leaving exactly one entry on
/// `results`.
///
/// FIRING and DESCENT are gated separately (WI-641 Phase 2): a fire is attempted
/// at EVERY node — including a leaf redex, which the resolver's
/// `fire_simp_equation` still supports (a functor-less `Const`/`Ident`-LHS
/// rewrite like `[simp] unify(1, 2)`; the typer's `try_fire` cheaply declines a
/// non-`Apply`/`Constructor` node, so leaf-firing is a no-op there). DESCENT, by
/// contrast, is gated per carrier by [`children_of`]: a compound occurrence form
/// ([`is_rewritable`]) or a `Term::Fn` yields children; a leaf yields none, so
/// `build_node` reassembles it unchanged and then fires.
fn visit_node(
    kb: &KnowledgeBase,
    node: Value,
    fuel: usize,
    work: &mut Vec<RewriteOp>,
    results: &mut Vec<Value>,
) {
    // Fuel exhausted: stop the chain here (no descent, no firing), exactly as
    // the recursive `rewrite`'s `fuel == 0` early return did.
    if fuel == 0 {
        results.push(node);
        return;
    }
    let children = children_of(kb, &node);
    work.push(RewriteOp::Build { node, fuel, child_count: children.len() });
    for child in children.into_iter().rev() {
        work.push(RewriteOp::Visit { node: child, fuel });
    }
}

/// Whether [`rewrite`] DESCENDS into this expression form (a fire is attempted at
/// every node regardless — see [`visit_node`]). Mirrors the variants
/// `map_children` rebuilds (`Apply`/`Constructor`/… have children): leaves and
/// post-elaboration `*Within` / requirement projections — which don't occur
/// before `type_check_sorts` — have no children, so they are not descended
/// (`build_node` still fires at them).
fn is_rewritable(expr: Option<&Expr>) -> bool {
    matches!(
        expr,
        Some(
            Expr::Apply { .. }
                | Expr::Constructor { .. }
                | Expr::Instantiation { .. }
                | Expr::DotApply { .. }
                | Expr::HoApply { .. }
                | Expr::If { .. }
                | Expr::Let { .. }
                | Expr::Lambda { .. }
                | Expr::Proof { .. }
                | Expr::Match { .. }
                | Expr::ListLit(_)
                | Expr::SetLit(_)
                | Expr::TupleLit { .. }
        )
    )
}

/// Reassemble a node from its rewritten children (popped off `results`), then
/// fire a `[simp]` equation at it via the caller's [`SimpFirer`]. A firing
/// re-enters the loop via `Visit { fuel - 1 }` so the fixpoint runs on the
/// work-stack; otherwise the reassembled node is pushed to `results`.
fn build_node<F: SimpFirer>(
    kb: &mut KnowledgeBase,
    node: Value,
    fuel: usize,
    child_count: usize,
    firer: &mut F,
    rids: &[RuleId],
    work: &mut Vec<RewriteOp>,
    results: &mut Vec<Value>,
) {
    // The last `child_count` results are this node's children, pushed in
    // source order by `visit_node`.
    let start = results.len() - child_count;
    let new_children: Vec<Value> = results.split_off(start);
    let reassembled = reassemble_value(kb, &node, &new_children);
    match firer.fire(kb, &reassembled, rids) {
        // Re-normalize the firing result to fixpoint on the stack (fuel - 1).
        Some(fired) => work.push(RewriteOp::Visit { node: fired, fuel: fuel - 1 }),
        None => results.push(reassembled),
    }
}

/// The rewritable children of a carrier-neutral node, in source order — the
/// per-carrier DESCENT rule (WI-643). A `Value::Node` occurrence descends only
/// a compound [`is_rewritable`] form (via `for_each_child`, wrapping each child
/// back as `Value::Node`); a `Value::Term` descends any `Term::Fn` (its
/// positional then named args, wrapped as `Value::term`). A leaf (a Node leaf, a
/// non-`Fn` term, or a bare scalar) yields no children — `build_node` then
/// reassembles it unchanged and fires at it. Each carrier is closed under
/// descent, so a Node's children are Nodes and a term's children are terms.
fn children_of(kb: &KnowledgeBase, node: &Value) -> Vec<Value> {
    match node {
        Value::Node(occ) => {
            let mut children: Vec<Value> = Vec::new();
            if is_rewritable(occ.as_expr()) {
                if let Some(expr) = occ.as_expr() {
                    node_occurrence::for_each_child(expr, |c| children.push(Value::Node(Rc::clone(c))));
                }
            }
            children
        }
        Value::Term { id, .. } => match kb.get_term(*id) {
            Term::Fn { pos_args, named_args, .. } => {
                let mut children = Vec::with_capacity(pos_args.len() + named_args.len());
                children.extend(pos_args.iter().map(|&c| Value::term(c)));
                children.extend(named_args.iter().map(|&(_, c)| Value::term(c)));
                children
            }
            _ => Vec::new(),
        },
        // Any other carrier — a genuine scalar (Int/Bool/…) or a COMPOUND
        // `Value::Entity`/`Value::Tuple` (which does carry sub-`Value`s) — is a
        // fire-only leaf: the driver descends ONLY the two structural simp
        // carriers (a `Term::Fn` and a functor-headed occurrence), so a redex
        // nested inside an Entity/Tuple is not reached. This is not a silent drop
        // but a deliberate scope match: the retired recursive term walk likewise
        // descended only `Term::Fn`, and no `[simp]` rule matches inside an
        // entity/tuple carrier today. `build_node` still attempts a fire at the
        // leaf (a functor-less `[simp] unify(1, 2)` rewrites a `Const` redex);
        // descending Entity/Tuple would be a new behavior, out of WI-643's scope.
        _ => Vec::new(),
    }
}

/// Rebuild a carrier-neutral node from its already-rewritten children (in
/// [`children_of`] order), preserving identity when nothing changed (WI-643).
/// Dispatches on the carrier: a `Value::Node` occurrence delegates to
/// [`reassemble`] (which returns the same `Rc` — span, owner, provenance, and
/// `inferred_type` intact — when no child moved); a `Value::Term` rebuilds its
/// `Term::Fn` (hash-consing dedups an unchanged rebuild back to the same
/// `TermId`). A leaf carries no children and passes through unchanged.
fn reassemble_value(kb: &mut KnowledgeBase, node: &Value, new_children: &[Value]) -> Value {
    match node {
        Value::Node(occ) => {
            // Descent kept every occurrence child a `Value::Node` (the carrier is
            // closed), so unwrap each back to its `Rc<NodeOccurrence>`.
            let occs: Vec<Rc<NodeOccurrence>> = new_children
                .iter()
                .map(|c| match c {
                    Value::Node(n) => Rc::clone(n),
                    other => unreachable!(
                        "occurrence child must be a Node, got {}",
                        other.type_name()
                    ),
                })
                .collect();
            Value::Node(reassemble(occ, &occs))
        }
        Value::Term { id, .. } => match kb.get_term(*id).clone() {
            Term::Fn { functor, pos_args, named_args } => {
                let np = pos_args.len();
                // Unchanged-check (WI-646): if every rewritten child is the SAME
                // `TermId` as the original, return the node unchanged — skipping
                // `kb.alloc(Term::Fn)` + the two `SmallVec` builds. The Node arm's
                // `ChildCursor.changed`/`Rc::ptr_eq` analog for the term carrier.
                // Hash-consing would dedup an unchanged rebuild back to `id`
                // anyway, but this avoids the alloc + rebuild — now hit at EVERY
                // node since WI-643 removed the fuel-as-depth cutoff (the term
                // carrier rewrites bottom-up). Compare BEFORE building, returning
                // the original node unchanged when no child moved.
                let changed = new_children[..np]
                    .iter()
                    .zip(pos_args.iter())
                    .any(|(c, &orig)| c.expect_term() != orig)
                    || named_args
                        .iter()
                        .enumerate()
                        .any(|(i, &(_, orig))| new_children[np + i].expect_term() != orig);
                if !changed {
                    return node.clone();
                }
                let new_pos: SmallVec<[TermId; 4]> =
                    new_children[..np].iter().map(|c| c.expect_term()).collect();
                let new_named: SmallVec<[(Symbol, TermId); 2]> = named_args
                    .iter()
                    .enumerate()
                    .map(|(i, &(sym, _))| (sym, new_children[np + i].expect_term()))
                    .collect();
                Value::term(kb.alloc(Term::Fn { functor, pos_args: new_pos, named_args: new_named }))
            }
            _ => node.clone(),
        },
        _ => node.clone(),
    }
}

/// Try to fire a `[simp]` equation at this node. Returns the rewritten
/// occurrence, or `None` if no equation matches (or its type-directed
/// guard fails).
///
/// WI-283: matches the rule LHS structurally via `match_view`, then — for
/// a redex whose functor is a *spec op* (a rule scoped to a parametric
/// sort, e.g. `Numeric.add`) — fires only where the receiver's type
/// satisfies that sort ([`super::typing::simp_fire_guard_holds`]). A
/// concrete-functor redex (a top-level monomorphic identity like
/// `transpose(transpose(?m)) = ?m`) is guard-free: the functor symbol
/// already pins the sort, so structural match alone is sound.
pub(super) fn try_fire(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    pass: PassId,
    rids: &[RuleId],
) -> Option<Rc<NodeOccurrence>> {
    let node_functor = match occ.as_expr()? {
        Expr::Apply { functor, .. } => *functor,
        Expr::Constructor { name, .. } => *name,
        _ => return None,
    };
    // WI-655: the type-directed guard (`simp_fire_guard_holds`) is deferred to the
    // FIRST rid whose LHS functor matches this node (checked once, below, before any
    // `match_view`). A node whose functor matches no `[simp]` rule can never fire — the
    // `stored_lhs_functor` filter rejects every candidate — so it now skips the guard
    // entirely: the guard was ~78% of per-node simp cost (and fires 0 rewrites over the
    // whole stdlib), pure waste on a non-matching node. Sound: the guard verdict is
    // irrelevant when nothing matches the functor, and it is side-effect-free.
    let mut guard_ok = false;
    // WI-646: `rids` are the eq+unify candidates gathered ONCE by the caller
    // (`KnowledgeBase::simp_equation_rids` — `eq` for a legacy `=` equation,
    // `unify` for the `<=>` head, proposal 049; WI-139 keeps only
    // `[simp]`/`[unfold]`-tagged equations there). Scanning both functors makes
    // an `<=>`-spelled `[simp]` rule fire identically to an `=` one. (Moving
    // selection onto most-specific-first `query()` is proposal 043 §4.6, deferred
    // — type-independent recognition needs only that both functors are covered.)
    for &rid in rids {
        if !is_simp_equation(kb, rid) {
            continue;
        }
        // WI-582: a rule carrying EXPLICIT typed-pattern bounds (`?x: T`) is fired
        // only by the resolver's `apply_eq_rules`, which enforces the bounds via
        // `typed_pattern_bounds_hold`. The typer conservatively SKIPS such rules
        // here rather than firing them unguarded — sound but conservative (it
        // simply does not simplify with typed rules; never wrong-fires; WI-067).
        if !kb.rule_type_bounds(rid).is_empty() {
            continue;
        }
        // Cheap pre-filter on the stored (DeBruijn) head, before opening.
        if stored_lhs_functor(kb, rid) != Some(node_functor) {
            continue;
        }
        // WI-655: FIRST functor match — evaluate the type-directed guard once here.
        // A spec/sort rule's law holds only for carriers satisfying its sort; the
        // guard is keyed on the node functor, so it is shared by every candidate rule
        // under it (guard-free `true` for a concrete functor). `guard_ok` memoizes it
        // across sibling rids under the same functor.
        if !guard_ok {
            if !super::typing::simp_fire_guard_holds(kb, occ) {
                return None;
            }
            guard_ok = true;
        }
        // The typer skips typed-bound rules above, so it ignores the opened
        // `fresh` globals (they key only the resolver's typed-pattern bounds).
        let (lhs, rhs, _fresh) = match open_equation(kb, rid) {
            Some(opened) => opened,
            None => continue,
        };
        // `occ` is itself a `TermView` (WI-277), so we match the rule LHS
        // against it in place — no `Value::Node` wrapping.
        if let Some(subst) = kb.match_view(lhs, occ) {
            if subst.is_contradiction() {
                continue;
            }
            let template = substitute_to_occurrence(kb, rhs, &subst, occ, pass);
            // WI-722 (043.1): if the substituted RHS is headed by a compile-time
            // MACRO (a syntax→syntax op — every param + result an occurrence,
            // §3.1), evaluate it over its argument occurrences and splice the
            // occurrence it returns, instead of leaving the template call. The
            // typer's `push_visit` continuation re-types the spliced subtree.
            if let Some(expanded) = try_expand_macro(kb, &template) {
                return Some(expanded);
            }
            return Some(template);
        }
    }
    None
}

/// WI-722 (proposal 043.1) — if `template` (the just-substituted `[simp]` RHS) is
/// headed by a compile-time MACRO, evaluate it and return the occurrence it
/// produces; else `None` (the caller keeps the template unchanged).
///
/// A macro is an occurrence→occurrence op ([`super::typing::is_macro`]).
/// [`substitute_to_occurrence`] has already reused each matched pattern-var CHILD
/// OCCURRENCE in place, so the template `m(?a, ?b)` is `apply(m, [<occ a>, <occ
/// b>])` with the REAL argument occurrences. We bind the macro's params to those
/// occurrences as `Value::Node` — NOT materialized: the flatten in
/// `bridge_op_to_eval` is deliberately skipped (it would lower a lambda-body
/// argument to `Bottom`), so occurrence structure survives — and run the body
/// through the WI-625 scratch interpreter, which now also carries the occurrence
/// build builtins (`make_apply`, …). The body returns a `Value::Node`, spliced.
///
/// A macro that fails to produce an occurrence (a non-`Node` return, an eval
/// error, or the re-entry cap) yields `None`: the template call is kept, and its
/// downstream type-check surfaces the failure loudly at the redex — never a
/// silently-wrong rewrite.
fn try_expand_macro(
    kb: &mut KnowledgeBase,
    template: &Rc<NodeOccurrence>,
) -> Option<Rc<NodeOccurrence>> {
    // Read the head cheaply and gate on `is_macro` BEFORE building the argument
    // vector: `try_expand_macro` runs on EVERY fired `[simp]` rewrite, and the gate
    // is false for all but a macro head, so the common path allocates nothing. The
    // head must be a positional `apply` — a macro is called on the matched
    // pattern-var occurrences; named / type args are not part of the Inc-1 surface,
    // so a macro carrying those declines to expand and stays a template.
    let Some(Expr::Apply { functor, pos_args, named_args, type_args }) = template.as_expr() else {
        return None;
    };
    let functor = *functor;
    if !named_args.is_empty() || !type_args.is_empty() || !super::typing::is_macro(kb, functor) {
        return None;
    }
    // Bind the macro's params to the argument occurrences as `Value::Node` — NOT
    // materialized: the flatten in `bridge_op_to_eval` is deliberately skipped (it
    // would lower a lambda-body argument to `Bottom`), so occurrence structure
    // survives. Run the body through the WI-625 scratch interpreter, which now also
    // carries the occurrence build builtins (`make_apply`, …). `None` = re-entry
    // cap hit (`run_in_bridge_interp` mem::takes the KB and reclaims it).
    let node_args: Vec<Value> = pos_args.iter().map(|o| Value::Node(Rc::clone(o))).collect();
    let outcome = kb.run_in_bridge_interp(|interp| interp.call_op_bridged(functor, &node_args))?;
    match outcome {
        // The body returned a spliceable occurrence — the rewrite result.
        Ok(Value::Node(result)) => Some(result),
        // A macro's declared return is `NodeOccurrence`, so a non-`Node` value is a
        // type/evaluator invariant break — loud in debug, decline in release.
        Ok(other) => {
            debug_assert!(
                false,
                "WI-722: macro `{}` returned a non-occurrence value: {other:?}",
                kb.qualified_name_of(functor),
            );
            None
        }
        // A macro that fails to produce an occurrence declines: the template call is
        // kept, and its downstream type-check surfaces the failure loudly at the
        // redex. A `Suspended` flounder / runtime-domain error residualizes quietly;
        // an `Internal` evaluator bug is asserted loudly, mirroring `bridge_op_to_eval`.
        Err(e) => {
            debug_assert!(
                !matches!(e, crate::eval::EvalError::Internal(_)),
                "WI-722: internal evaluator error expanding macro `{}`: {e}",
                kb.qualified_name_of(functor),
            );
            None
        }
    }
}

/// The functor of an equation's LHS, read from the *stored* head (no
/// DeBruijn opening). Used to skip non-matching rules before the
/// allocate-heavy `open_equation`. `pub(super)`: the typer's dot-rule
/// firing (WI-279 INC2) pre-filters `[simp]` equations by LHS functor.
///
/// WI-663: reads the head carrier-agnostically via `fact_head_term` (not the
/// panicking term-only `rule_head`) — a value-fact head (`Value::Node`/`Entity`)
/// is never an equation, so it reads `None` and the caller skips it. Callers
/// already pre-gate with `is_equation`/`is_simp_equation` (carrier-agnostic), so
/// this is belt-and-suspenders that also makes the reader intrinsically safe.
pub(super) fn stored_lhs_functor(kb: &KnowledgeBase, rid: RuleId) -> Option<Symbol> {
    let head = kb.fact_head_term(rid)?;
    let lhs = match kb.get_term(head) {
        Term::Fn { pos_args, .. } if pos_args.len() == 2 => pos_args[0],
        _ => return None,
    };
    match kb.get_term(lhs) {
        Term::Fn { functor, .. } => Some(*functor),
        _ => None,
    }
}

/// Open an equation's DeBruijn vars to fresh globals and return its
/// `(lhs, rhs, fresh)` — the matchable/buildable LHS/RHS terms plus the fresh
/// globals the DeBruijn slots opened to (empty for a legacy arity-0 Global
/// head). Uses the KB's `term_from_debruijn` (the same opener `with_fresh_vars`
/// uses) — not a reimplementation of the resolver's rule-opening. The `fresh`
/// set lets the resolver's `fire_simp_equation` (WI-641 Phase 2) key typed-
/// pattern bounds by the opened globals and share this ONE opener rather than
/// re-inlining it. `pub(super)`: the typer's dot-rule firing (WI-279 INC2) opens
/// a matched `[simp]` dot rule (and ignores `fresh` — it skips typed rules).
pub(super) fn open_equation(
    kb: &mut KnowledgeBase,
    rid: RuleId,
) -> Option<(TermId, TermId, Vec<VarId>)> {
    let arity = kb.rule_arity(rid);
    // WI-663: `fact_head_term` (not the panicking term-only `rule_head`) — a
    // value-fact head has no term LHS to open, so it reads `None` and the caller
    // skips it. All callers pre-gate with `is_equation`/`is_simp_equation`.
    let head = kb.fact_head_term(rid)?;
    let (opened, fresh) = if arity > 0 {
        let name = kb.intern("_");
        let fresh: Vec<VarId> = (0..arity).map(|_| kb.fresh_var(name)).collect();
        (kb.term_from_debruijn(head, &fresh), fresh)
    } else {
        (head, Vec::new())
    };
    match kb.get_term(opened) {
        Term::Fn { pos_args, .. } if pos_args.len() == 2 => Some((pos_args[0], pos_args[1], fresh)),
        _ => None,
    }
}

/// Build the RHS as a fresh `NodeOccurrence`, resolving rule variables to
/// their matched bindings via the shared `walk_view`. A variable bound to a
/// matched child occurrence (`Value::Node`) is reused in place (identity
/// preserved); a functor builds a synthesized `Apply`; a literal builds a
/// `Const`. New nodes carry `origin: Synthesized { from, by }`.
pub(super) fn substitute_to_occurrence(
    kb: &KnowledgeBase,
    term: TermId,
    subst: &Substitution,
    from: &Rc<NodeOccurrence>,
    pass: PassId,
) -> Rc<NodeOccurrence> {
    let mut work: Vec<SubstOp> = vec![SubstOp::Visit(term)];
    let mut results: Vec<Rc<NodeOccurrence>> = Vec::new();
    while let Some(op) = work.pop() {
        match op {
            SubstOp::Visit(t) => subst_visit(kb, t, subst, from, pass, &mut work, &mut results),
            SubstOp::BuildApply { functor, pos_count, named_keys } => {
                // Children are on top of `results` in source order
                // (pos then named); peel them back off.
                let total = pos_count + named_keys.len();
                let start = results.len() - total;
                let mut children = results.split_off(start).into_iter();
                let pos_args: Vec<_> = (&mut children).take(pos_count).collect();
                let named_args: Vec<_> =
                    named_keys.into_iter().zip(children).collect();
                let expr = Expr::Apply { functor, pos_args, named_args, type_args: Vec::new() };
                results.push(NodeOccurrence::synthesized_expr(
                    expr,
                    Rc::clone(from),
                    pass,
                    from.owner,
                ));
            }
        }
    }
    debug_assert_eq!(results.len(), 1, "substitute_to_occurrence: expected one result");
    results.pop().expect("RHS produced no NodeOccurrence")
}

/// Work-stack item for the iterative [`substitute_to_occurrence`]. `Visit`
/// resolves a RHS term via `walk_view`; an `Apply` defers reconstruction to a
/// `BuildApply` once its children land on `results`.
enum SubstOp {
    Visit(TermId),
    BuildApply { functor: Symbol, pos_count: usize, named_keys: Vec<Symbol> },
}

/// Resolve one RHS term to a synthesized occurrence (leaf), or schedule a
/// `BuildApply` + child `Visit`s for a `Term::Fn`. Children push in reverse
/// source order so they pop — and complete — in source order.
fn subst_visit(
    kb: &KnowledgeBase,
    term: TermId,
    subst: &Substitution,
    from: &Rc<NodeOccurrence>,
    pass: PassId,
    work: &mut Vec<SubstOp>,
    results: &mut Vec<Rc<NodeOccurrence>>,
) {
    let synth = |expr: Expr| NodeOccurrence::synthesized_expr(expr, Rc::clone(from), pass, from.owner);
    match kb.walk_view(term, subst) {
        // Reused matched child — keep its identity (and provenance).
        Value::Node(occ) => results.push(occ),
        Value::Term { id: t, .. } => match kb.get_term(t) {
            Term::Fn { functor, pos_args, named_args } => {
                let named_keys: Vec<Symbol> = named_args.iter().map(|(s, _)| *s).collect();
                work.push(SubstOp::BuildApply {
                    functor: *functor,
                    pos_count: pos_args.len(),
                    named_keys,
                });
                // Push named (reversed) then pos (reversed) so pos pop first.
                for &(_, c) in named_args.iter().rev() {
                    work.push(SubstOp::Visit(c));
                }
                for &c in pos_args.iter().rev() {
                    work.push(SubstOp::Visit(c));
                }
            }
            Term::Const(lit) => results.push(synth(Expr::Const(lit.clone()))),
            Term::Ref(s) => results.push(synth(Expr::Ref(*s))),
            Term::Ident(s) => results.push(synth(Expr::Ident(*s))),
            // An unbound RHS var or `⊥` yields `⊥`; a well-formed `[simp]`
            // rule binds every RHS var, so the post-rewrite type-check
            // surfaces any genuinely unbound case as an error.
            _ => results.push(synth(Expr::Bottom)),
        },
        // Scalars → `Const` (shared with the resolver's occurrence walker).
        // Tuple/Entity/closures/etc. aren't expected as a structural RHS
        // binding in WI-277; `None` leaves a `⊥` for the type-check to flag.
        other => results.push(synth(
            node_occurrence::scalar_value_expr(&other).unwrap_or(Expr::Bottom),
        )),
    }
}

// ── child reassembly (bottom-up reconstruction) ────────────────────
//
// Non-destructive analog of `node_occurrence::drain_expr_children`: given the
// already-rewritten children (in `for_each_child` source order), rebuild the
// node only if some child changed (`Rc::ptr_eq`), preserving span/owner.
// Post-elaboration forms (`*Within`, requirement projections, `var_ref`)
// don't occur before `type_check_sorts`, so they (and the leaves) are never
// routed here — `is_rewritable` filters them out — and pass through unchanged.

/// Cursor over the rewritten children supplied to [`reassemble`], pairing each
/// with the corresponding original child so the caller can detect whether any
/// slot changed (`Rc::ptr_eq`) — the same change test the recursive
/// `map_children` made per child.
struct ChildCursor<'a> {
    new: &'a [Rc<NodeOccurrence>],
    idx: usize,
    changed: bool,
}

impl<'a> ChildCursor<'a> {
    fn new(new: &'a [Rc<NodeOccurrence>]) -> Self {
        ChildCursor { new, idx: 0, changed: false }
    }
    /// Take the next rewritten child, recording whether it differs from
    /// `original` (the slot it replaces).
    fn take(&mut self, original: &Rc<NodeOccurrence>) -> Rc<NodeOccurrence> {
        let r = Rc::clone(&self.new[self.idx]);
        self.idx += 1;
        self.changed |= !Rc::ptr_eq(&r, original);
        r
    }
    fn take_vec(&mut self, originals: &[Rc<NodeOccurrence>]) -> Vec<Rc<NodeOccurrence>> {
        originals.iter().map(|o| self.take(o)).collect()
    }
    fn take_named(
        &mut self,
        originals: &[(Symbol, Rc<NodeOccurrence>)],
    ) -> Vec<(Symbol, Rc<NodeOccurrence>)> {
        originals.iter().map(|(s, o)| (*s, self.take(o))).collect()
    }
}

/// Rebuild `occ` from its already-rewritten children (in `for_each_child`
/// source order), returning `occ` unchanged (same `Rc`) when no child
/// moved. `pub(super)` so the typer's `build_type` reassembles each node
/// from its children's `TypeResult.node` (WI-283).
pub(super) fn reassemble(
    occ: &Rc<NodeOccurrence>,
    new_children: &[Rc<NodeOccurrence>],
) -> Rc<NodeOccurrence> {
    let expr = match occ.as_expr() {
        Some(e) => e,
        None => return Rc::clone(occ),
    };
    let mut cur = ChildCursor::new(new_children);
    let new_expr: Expr = match expr {
        Expr::Apply { functor, pos_args, named_args, type_args } => Expr::Apply {
            functor: *functor,
            pos_args: cur.take_vec(pos_args),
            named_args: cur.take_named(named_args),
            type_args: type_args.clone(),
        },
        Expr::Constructor { name, pos_args, named_args } => Expr::Constructor {
            name: *name,
            pos_args: cur.take_vec(pos_args),
            named_args: cur.take_named(named_args),
        },
        Expr::Instantiation { name, pos_args, named_args } => Expr::Instantiation {
            name: *name,
            pos_args: cur.take_vec(pos_args),
            named_args: cur.take_named(named_args),
        },
        Expr::HoApply { predicate, args } => Expr::HoApply {
            predicate: cur.take(predicate),
            args: cur.take_vec(args),
        },
        Expr::DotApply { receiver, name, pos_args, named_args } => Expr::DotApply {
            receiver: cur.take(receiver),
            name: *name,
            pos_args: cur.take_vec(pos_args),
            named_args: cur.take_named(named_args),
        },
        Expr::If { condition, then_branch, else_branch } => Expr::If {
            condition: cur.take(condition),
            then_branch: cur.take(then_branch),
            else_branch: cur.take(else_branch),
        },
        Expr::Let { pattern, type_annotation, value, body } => Expr::Let {
            pattern: cur.take(pattern),
            type_annotation: type_annotation.clone(),
            value: cur.take(value),
            body: cur.take(body),
        },
        Expr::Lambda { param, body } => Expr::Lambda {
            param: cur.take(param),
            body: cur.take(body),
        },
        Expr::Match { scrutinee, branches } => {
            let scr = cur.take(scrutinee);
            // WI-318: `for_each_child` now visits each branch as
            // pattern, body, guard? — consume in that order.
            let new_branches: Vec<MatchBranch> = branches
                .iter()
                .map(|br| {
                    let pattern = cur.take(&br.pattern);
                    let body = cur.take(&br.body);
                    let guard = br.guard.as_ref().map(|g| cur.take(g));
                    MatchBranch { pattern, guard, body, span: br.span }
                })
                .collect();
            Expr::Match { scrutinee: scr, branches: new_branches }
        }
        Expr::ListLit(es) => Expr::ListLit(cur.take_vec(es)),
        Expr::SetLit(es) => Expr::SetLit(cur.take_vec(es)),
        Expr::TupleLit { positional, named } => Expr::TupleLit {
            positional: cur.take_vec(positional),
            named: cur.take_named(named),
        },
        // Post-elaboration forms. `is_rewritable` keeps these out of the
        // simp/typer `Build` path, but `open_debruijn_node` / `substitute_
        // occurrence` (WI-296) reassemble rule-body atoms that bypass
        // `is_rewritable` — a reflection rule matching `apply_within(...)`,
        // `requirement_at_sort(...)`, etc. as data reaches here. Rebuild them,
        // consuming children in `for_each_child` order (else their opened/
        // substituted children would be silently dropped).
        Expr::ApplyWithin { functor, args, named_args, requirements, type_args } => {
            Expr::ApplyWithin {
                functor: *functor,
                args: cur.take_vec(args),
                named_args: cur.take_named(named_args),
                requirements: cur.take_vec(requirements),
                type_args: type_args.clone(),
            }
        }
        Expr::HoApplyWithin { predicate, args, requirements } => Expr::HoApplyWithin {
            predicate: cur.take(predicate),
            args: cur.take_vec(args),
            requirements: cur.take_vec(requirements),
        },
        Expr::ConstructorWithin { name, pos_args, named_args, requirements } => {
            Expr::ConstructorWithin {
                name: *name,
                pos_args: cur.take_vec(pos_args),
                named_args: cur.take_named(named_args),
                requirements: cur.take_vec(requirements),
            }
        }
        Expr::LambdaWithin { param, body, requirements } => Expr::LambdaWithin {
            param: cur.take(param),
            body: cur.take(body),
            requirements: cur.take_vec(requirements),
        },
        Expr::RequirementAtSort { chain, slot } => Expr::RequirementAtSort {
            chain: cur.take(chain),
            slot: *slot,
        },
        Expr::ConstructRequirement { impl_functor, requirements } => Expr::ConstructRequirement {
            impl_functor: *impl_functor,
            requirements: cur.take_vec(requirements),
        },
        // WI-538: an in-body proof — consume children in `for_each_child`
        // order [conclude?, body] so a `[simp]` rewrite (or a WI-408
        // `some(…)` coercion) inside the goal or continuation propagates
        // up instead of being silently dropped.
        Expr::Proof { target, strategy, using, conclude, body } => Expr::Proof {
            target: *target,
            strategy: *strategy,
            using: using.clone(),
            conclude: conclude.as_ref().map(|c| cur.take(c)),
            body: cur.take(body),
        },
        // Genuine leaves (`Var`/`Const`/`Ref`/`Ident`/`Bottom`/`VarRef`) — no
        // children to reassemble.
        _ => return Rc::clone(occ),
    };
    if !cur.changed {
        return Rc::clone(occ);
    }
    // Preserve provenance (`Synthesized { from, by }`) AND the typer-stamped
    // `inferred_type` (WI-502 Step 3) when a child is rewritten under this node —
    // `rebuilt_expr` carries both, where a bare `new_expr` would drop the type.
    occ.rebuilt_expr(new_expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kb::node_occurrence::{NodeKind, OccurrenceOrigin};
    use crate::kb::term::{Literal, Var};
    use crate::span::{SourceId, SourceSpan};
    use smallvec::SmallVec;

    /// Build the `[simp]` equation `eq(add(?x, 0), ?x)` head + `[simp]` meta,
    /// returning `(eq_head, meta, add_sym)` without asserting.
    fn build_add_zero(kb: &mut KnowledgeBase) -> (TermId, TermId, Symbol) {
        let eq_sym = kb.intern("eq");
        let add = kb.intern("add");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let zero = kb.alloc(Term::Const(Literal::Int(0)));
        let lhs = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[var_x, zero]),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, var_x]),
            named_args: SmallVec::new(),
        });
        let simp_sym = kb.intern("simp");
        let meta_sym = kb.intern("meta");
        let tru = kb.alloc(Term::Const(Literal::Bool(true)));
        let meta = kb.alloc(Term::Fn {
            functor: meta_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(simp_sym, tru)]),
        });
        (eq_head, meta, add)
    }

    /// Assert `add_zero` as a ground-headed fact (Global vars, arity 0 — the
    /// minimal shape, like `simplify_variable_equation`).
    fn assert_add_zero(kb: &mut KnowledgeBase) -> Symbol {
        let (eq_head, meta, add) = build_add_zero(kb);
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        kb.assert_fact(eq_head, sort, domain, Some(meta));
        add
    }

    /// Assert `add_zero` via the DeBruijn path
    /// (`assert_rule_debruijn_with_nodes`, arity > 0) — the shape real `[simp]`
    /// rules take after loading. Exercises `open_equation`'s
    /// `term_from_debruijn` branch.
    fn assert_add_zero_db(kb: &mut KnowledgeBase) -> Symbol {
        let (eq_head, meta, add) = build_add_zero(kb);
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        kb.assert_rule_debruijn_with_nodes(eq_head, vec![], sort, domain, Some(meta));
        add
    }

    fn span() -> SourceSpan {
        SourceSpan::new(SourceId::from_raw(0), 0, 10)
    }

    /// WI-663: a value-fact head (`Value::Entity` — e.g. a reflect fact carrying
    /// a denoted value) must not abort the term-only `[simp]`-equation head
    /// readers. Before the migration `stored_lhs_functor` / `open_equation` read
    /// the head through the panicking term-only `rule_head`; now they read
    /// `fact_head_term`, so a value head — which is never an equation — reads
    /// `None` and the caller skips it. Feed a synthetic `eq`-shaped *value* head
    /// straight to both readers and assert they resolve to `None` instead of
    /// panicking the process.
    #[test]
    fn value_fact_head_skips_term_only_equation_readers() {
        use crate::eval::value::Value;
        let mut kb = KnowledgeBase::new();
        let eq = kb.eq_functor();
        let a = kb.intern("a");
        let b = kb.intern("b");
        // `eq(a, b)` shaped, but carried as a `Value::Entity` (a value fact, not a
        // hash-consed `Term`) — the adversarial case the `rule_head` panic guarded.
        let head = Value::Entity {
            functor: eq,
            pos: vec![
                Value::Entity { functor: a, pos: Vec::new().into(), named: Vec::new().into() },
                Value::Entity { functor: b, pos: Vec::new().into(), named: Vec::new().into() },
            ]
            .into(),
            named: Vec::new().into(),
        };
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let rid = kb.assert_fact_value(head, sort, domain, None);

        // The stored head is a value carrier (not a `Term`), so the term-only
        // `fact_head_term` skip reads `None`…
        assert!(matches!(kb.rule_head_value(rid), Value::Entity { .. }));
        assert_eq!(kb.fact_head_term(rid), None);
        // …and both migrated equation readers skip it gracefully (no panic).
        assert_eq!(stored_lhs_functor(&kb, rid), None);
        assert!(open_equation(&mut kb, rid).is_none());
    }

    #[test]
    fn has_simp_equations_counts_unify_headed_simp_rule() {
        // WI-646: `has_simp_equations` selects over BOTH `eq` and `unify` buckets
        // (via `simp_equation_rids`). A `[simp]` law spelled `<=>` (the `unify`
        // head — the stdlib's form, 14/14) must be counted, so the typer's
        // `simp_enabled` fires it even in a KB with no `eq`-headed simp law and no
        // dot-applies. The former `eq`-only spelling returned `false` here — the
        // under-firing this fixes.
        let mut kb = KnowledgeBase::new();
        let unify = kb.unify_functor(); // bare `unify` in a prelude-less KB
        let add = kb.intern("add");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let zero = kb.alloc(Term::Const(Literal::Int(0)));
        let lhs = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[var_x, zero]),
            named_args: SmallVec::new(),
        });
        // `<=>`-headed equation: unify(add(?x, 0), ?x).
        let unify_head = kb.alloc(Term::Fn {
            functor: unify,
            pos_args: SmallVec::from_slice(&[lhs, var_x]),
            named_args: SmallVec::new(),
        });
        let simp_sym = kb.intern("simp");
        let meta_sym = kb.intern("meta");
        let tru = kb.alloc(Term::Const(Literal::Bool(true)));
        let meta = kb.alloc(Term::Fn {
            functor: meta_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(simp_sym, tru)]),
        });
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        kb.assert_rule_debruijn_with_nodes(unify_head, vec![], sort, domain, Some(meta));

        assert!(
            has_simp_equations(&mut kb),
            "a <=>-headed [simp] rule must be counted (eq+unify selection)"
        );
    }

    #[test]
    fn guard_free_simp_rule_rewrites_op_body() {
        let mut kb = KnowledgeBase::new();
        let add = assert_add_zero(&mut kb);

        // op body: add(7, 0)
        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let body = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: add,
                pos_args: vec![Rc::clone(&seven), zero_occ],
                named_args: vec![],
                type_args: vec![],
            },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, Rc::clone(&body));

        run(&mut kb);

        let rewritten = kb.op_body_node(foo).expect("op body present");
        // add(7, 0) fired add_zero → ?x, i.e. the reused `7` child occurrence.
        assert!(
            matches!(rewritten.as_expr(), Some(Expr::Const(Literal::Int(7)))),
            "expected Const(7), got {:?}",
            rewritten.as_expr()
        );
        assert!(
            Rc::ptr_eq(rewritten, &seven),
            "rewritten body should reuse the matched `7` child occurrence (identity preserved)"
        );
    }

    #[test]
    fn nested_redex_rewrites_and_parent_rebuilds() {
        let mut kb = KnowledgeBase::new();
        let add = assert_add_zero(&mut kb);
        let wrap = kb.intern("wrap");

        // op body: wrap(add(7, 0)) — the redex is nested; the parent `wrap`
        // must be rebuilt with the rewritten child.
        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let inner = NodeOccurrence::new_expr(
            Expr::Apply { functor: add, pos_args: vec![Rc::clone(&seven), zero_occ], named_args: vec![], type_args: vec![] },
            span(),
            None,
        );
        let body = NodeOccurrence::new_expr(
            Expr::Apply { functor: wrap, pos_args: vec![inner], named_args: vec![], type_args: vec![] },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, body);

        run(&mut kb);

        let rewritten = kb.op_body_node(foo).expect("op body present");
        match rewritten.as_expr() {
            Some(Expr::Apply { functor, pos_args, .. }) => {
                assert_eq!(*functor, wrap);
                assert_eq!(pos_args.len(), 1);
                assert!(
                    matches!(pos_args[0].as_expr(), Some(Expr::Const(Literal::Int(7)))),
                    "inner add(7,0) should have rewritten to 7"
                );
                assert!(Rc::ptr_eq(&pos_args[0], &seven));
            }
            other => panic!("expected wrap(7), got {other:?}"),
        }
    }

    #[test]
    fn typer_and_resolver_phases_agree() {
        // The same `[simp]` rule reduces add(7, 0) → 7 in BOTH the resolver
        // (term, via simplify/apply_eq_rules) and the typer phase (occurrence,
        // via run) — the phase-agreement invariant (proposal 043 §4.7).
        let mut kb = KnowledgeBase::new();
        let add = assert_add_zero(&mut kb);

        // Resolver phase: simplify the term add(7, 0).
        let seven_t = kb.alloc(Term::Const(Literal::Int(7)));
        let zero_t = kb.alloc(Term::Const(Literal::Int(0)));
        let add_t = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[seven_t, zero_t]),
            named_args: SmallVec::new(),
        });
        assert_eq!(kb.simplify(add_t), seven_t, "resolver phase: add(7,0) → 7");

        // Typer phase: rewrite the occurrence add(7, 0).
        let seven_o = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_o = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let body = NodeOccurrence::new_expr(
            Expr::Apply { functor: add, pos_args: vec![Rc::clone(&seven_o), zero_o], named_args: vec![], type_args: vec![] },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, body);
        run(&mut kb);

        let rewritten = kb.op_body_node(foo).expect("op body present");
        assert!(
            matches!(rewritten.as_expr(), Some(Expr::Const(Literal::Int(7)))),
            "typer phase: add(7,0) → 7, got {:?}",
            rewritten.as_expr()
        );
    }

    #[test]
    fn debruijn_simp_rule_rewrites_op_body() {
        // Real-world shape: a `[simp]` rule stored with DeBruijn vars
        // (`assert_rule_debruijn_with_nodes`, as the loader produces) still
        // fires — `open_equation` opens it via `term_from_debruijn`.
        let mut kb = KnowledgeBase::new();
        let add = assert_add_zero_db(&mut kb);

        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let body = NodeOccurrence::new_expr(
            Expr::Apply { functor: add, pos_args: vec![Rc::clone(&seven), zero_occ], named_args: vec![], type_args: vec![] },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, body);

        run(&mut kb);

        let rewritten = kb.op_body_node(foo).expect("op body present");
        assert!(
            matches!(rewritten.as_expr(), Some(Expr::Const(Literal::Int(7)))),
            "DeBruijn [simp] rule: add(7,0) → 7, got {:?}",
            rewritten.as_expr()
        );
        assert!(Rc::ptr_eq(rewritten, &seven));
    }

    #[test]
    fn multi_step_rewrite_reaches_fixpoint_and_preserves_synthesized_origin() {
        // Two rules: f(?y) = g(add(?y, 0))  and  add(?x, 0) = ?x.
        // f(7) fires → synthesized g(add(7,0)); the engine re-rewrites that to
        // fixpoint → add(7,0) fires → g(7). The g node was synthesized, then
        // rebuilt when its child changed: it must keep its Synthesized origin.
        let mut kb = KnowledgeBase::new();
        let add = assert_add_zero(&mut kb);
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let f = kb.intern("f");
        let g = kb.intern("g");
        let y_sym = kb.intern("y");
        let vy = kb.fresh_var(y_sym);
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));
        let zero = kb.alloc(Term::Const(Literal::Int(0)));
        let add_y0 = kb.alloc(Term::Fn { functor: add, pos_args: SmallVec::from_slice(&[var_y, zero]), named_args: SmallVec::new() });
        let g_add = kb.alloc(Term::Fn { functor: g, pos_args: SmallVec::from_elem(add_y0, 1), named_args: SmallVec::new() });
        let f_y = kb.alloc(Term::Fn { functor: f, pos_args: SmallVec::from_elem(var_y, 1), named_args: SmallVec::new() });
        let eq_head = kb.alloc(Term::Fn { functor: eq_sym, pos_args: SmallVec::from_slice(&[f_y, g_add]), named_args: SmallVec::new() });
        let meta = {
            let simp_sym = kb.intern("simp");
            let meta_sym = kb.intern("meta");
            let tru = kb.alloc(Term::Const(Literal::Bool(true)));
            kb.alloc(Term::Fn { functor: meta_sym, pos_args: SmallVec::new(), named_args: SmallVec::from_slice(&[(simp_sym, tru)]) })
        };
        kb.assert_fact(eq_head, sort, domain, Some(meta));

        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let body = NodeOccurrence::new_expr(
            Expr::Apply { functor: f, pos_args: vec![seven], named_args: vec![], type_args: vec![] },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, body);

        run(&mut kb);

        let rewritten = kb.op_body_node(foo).expect("op body present");
        match rewritten.as_expr() {
            Some(Expr::Apply { functor, pos_args, .. }) => {
                assert_eq!(*functor, g, "f(7) should reduce to g(...)");
                assert!(
                    matches!(pos_args[0].as_expr(), Some(Expr::Const(Literal::Int(7)))),
                    "g's child add(7,0) should have reduced to 7 (fixpoint)"
                );
            }
            other => panic!("expected g(7), got {other:?}"),
        }
        assert!(
            matches!(&rewritten.kind, NodeKind::Expr { origin: OccurrenceOrigin::Synthesized { .. }, .. }),
            "the rebuilt g node should keep its Synthesized origin"
        );
    }

    #[test]
    fn deeply_nested_body_does_not_overflow_host_stack() {
        // WI-278: the walk is iterative, so a body nested far deeper than the
        // recursive version's host-stack budget (which overflowed on the
        // 624-line typing_pass_spec.anthill) rewrites without crashing. Build
        // wrap(wrap(…wrap(add(7, 0))…)) at a depth that the old recursive
        // `rewrite`/`map_children` could not survive, and confirm the
        // innermost redex still fires.
        let mut kb = KnowledgeBase::new();
        let add = assert_add_zero(&mut kb);
        let wrap = kb.intern("wrap");

        const DEPTH: usize = 200_000;
        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let mut node = NodeOccurrence::new_expr(
            Expr::Apply { functor: add, pos_args: vec![Rc::clone(&seven), zero_occ], named_args: vec![], type_args: vec![] },
            span(),
            None,
        );
        for _ in 0..DEPTH {
            node = NodeOccurrence::new_expr(
                Expr::Apply { functor: wrap, pos_args: vec![node], named_args: vec![], type_args: vec![] },
                span(),
                None,
            );
        }
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, node);

        run(&mut kb);

        // Walk down the wrap chain and confirm the innermost add(7, 0) → 7.
        let mut cur = Rc::clone(kb.op_body_node(foo).expect("op body present"));
        for _ in 0..DEPTH {
            cur = match cur.as_expr() {
                Some(Expr::Apply { functor, pos_args, .. }) if *functor == wrap => {
                    Rc::clone(&pos_args[0])
                }
                other => panic!("expected wrap(...), got {other:?}"),
            };
        }
        assert!(
            matches!(cur.as_expr(), Some(Expr::Const(Literal::Int(7)))),
            "innermost add(7, 0) should have rewritten to 7, got {:?}",
            cur.as_expr()
        );
        assert!(Rc::ptr_eq(&cur, &seven), "innermost redex should reuse the matched `7`");
    }
}

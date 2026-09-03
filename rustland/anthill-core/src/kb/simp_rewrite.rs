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
//! build side, [`build_rhs_template`], which produces the RHS as a
//! `NodeOccurrence` two ways. A rule that kept its written RHS
//! (`KnowledgeBase::rule_equation_rhs_node`, WI-20260903-FCZ3N) has it
//! re-parented onto the redex by [`reparent_spliced`] — every node keeping the
//! span and `dot_chain` the author wrote — and σ applied by the shared
//! `node_occurrence::substitute_occurrence`. A rule with no source text (a
//! host- or runtime-asserted equation) gets [`substitute_to_occurrence`],
//! which walks the head TERM and mints a `Synthesized` node per level on top
//! of the shared `walk_view`.
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
//! tree on an explicit `Visit`/`Build` work-stack, and both RHS builders
//! ([`substitute_to_occurrence`], [`reparent_spliced`]) build on a
//! second work-stack — all
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
use crate::parse::desugar_target as dt;

use super::load::meta_has_flag;
use super::node_occurrence::{self, Expr, MatchBranch, NodeKind, NodeOccurrence, OccurrenceOrigin};
use super::occurrence::PassId;
use super::subst::Substitution;
use super::term::{Term, TermId, Var, VarId};
use super::{KnowledgeBase, RuleId};

/// Per-node fixpoint bound — mirrors `apply_eq_rules`'s fuel (`resolve.rs`),
/// keeping the firing sites' termination policy aligned. `pub(super)` so the
/// typer's firing site (`typing::type_check_node`) bounds its fire→re-type
/// recursion by the same constant (WI-283).
pub(super) const SIMP_FUEL: usize = 100;

const PASS_NAME: &str = "anthill.kb.passes.simp_rewrite";

/// WI-757 — a compile-time MACRO's REJECTION of its input, carried out of
/// `try_expand_macro` to whoever drove the fire.
///
/// The macro seam has TWO negative outcomes and this type is the one that
/// distinguishes them. A **decline** (`Ok(None)`) says "not me / not yet": the
/// `[simp]` template call is kept and whatever downstream check the residual
/// fails is the diagnostic — the WI-722 contract, unchanged. A **rejection** says
/// the macro IS the right one and the input is definitively wrong; the reason is
/// known here and nowhere downstream, so it must be carried out rather than
/// dropped. The typer reports it as a load error at `span`; before WI-757 it was
/// mapped to a decline and the user read the residual `guarded_of` template's
/// type error instead.
///
/// No dedup key rides here on purpose. On the TYPER's path — the only one that
/// reports — a rejection is handed to the fire's CALLER, at the node it fired on,
/// and ABORTS that node's typing: one rejection produces one error, and an attempt
/// that instead succeeds leaves nothing behind to go stale. (Buffering rejections on
/// the KB for a later drain would need both, and would leak a rejection from a
/// speculative walk whose errors are discarded.) [`run`] — the unit-test harness,
/// which has no reporter — is the one place that does keep a rejection, and it keeps
/// only the FIRST and hands it straight back rather than accumulating.
#[derive(Debug)]
pub struct MacroRejection {
    /// The macro that rejected — the symbol at the head of the `[simp]` RHS.
    pub macro_name: Symbol,
    /// The macro's own words, already rendered, quoted verbatim into the load
    /// error. One string rather than a structured pair because the channel has TWO
    /// producers whose shapes differ: a HOST macro writes `expected …, got …`, an
    /// anthill macro RAISES a payload (proposal 043.1 §3.6).
    pub detail: String,
    /// The OFFENDING sub-expression's span when the macro named one — a host macro
    /// holds the argument occurrences, so it usually can. `None` leaves the location
    /// to the reporter, which falls back to the redex; that is what a RAISED
    /// rejection gets, `raise` carrying a payload and no occurrence.
    pub span: Option<crate::span::SourceSpan>,
}

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
    kb.simp_equation_rids()
        .into_iter()
        .any(|rid| is_simp_equation(kb, rid))
}

/// WI-646: the typer's per-rule fire predicate — `rid` is a `[simp]`-tagged
/// EQUATION. Shared by `try_fire` AND the `has_simp_equations` gate so the two
/// can't drift (the typer's peer of the resolver's `is_directional_equation`).
/// `[simp]`-only, not `[simp]`/`[unfold]`: the typer fires only `[simp]` (never
/// `[unfold]`), so gating on both would enable an always-declining walk.
///
/// WI-902 raised it to `pub(super)`: `typing::try_fire_dot_rule` had inlined a
/// third copy of the predicate, which is how it came to select on the `eq` bucket
/// alone and never fire a `<=>`-spelled dot rule. Both properties this test names —
/// equation-hood (connective-agnostic, `is_equation`) and the `[simp]` tag — are
/// exactly the ones a firing site must not re-derive.
pub(super) fn is_simp_equation(kb: &KnowledgeBase, rid: RuleId) -> bool {
    kb.is_equation(rid) && meta_has_flag(kb, kb.rule_meta(rid), "simp")
}

/// WI-898 — how many equations define `functor`, and how many of them can EVER
/// fire. The census a diagnostic needs when a call to an equation-introduced
/// functor ([`crate::intern::SymbolKind::EquationFunctor`]) reaches the typer
/// unreduced, because the two counts are two different bugs with two different
/// repairs: `simp == 0` means the equations are INERT and want the tag (`[simp]`
/// is the enablement, §5.3); `simp > 0` means they fire but none MATCHED these
/// arguments, and the author has to look at the patterns.
///
/// DELIBERATELY NOT SELECTED OVER [`KnowledgeBase::simp_equation_rids`], which is what
/// every FIRING site uses. That bucket cannot answer this question: WI-139
/// (`unindex_functor`) removes a non-directional — i.e. untagged — equation from
/// `rules_by_functor(eq)` precisely so it never drives automatic rewriting, so the
/// clauses whose absence of a tag IS the diagnosis are the ones the bucket hides.
/// MEASURED: an untagged `f(?x) = ?x` censused as ZERO defining equations and the
/// message blamed a retraction. The scan is over `live_rule_ids` instead, with the
/// firing sites' per-rule predicates ([`is_simp_equation`], [`stored_lhs_functor`])
/// applied unchanged so `simp_tagged` still means exactly "would fire".
///
/// An ERROR-PATH cost only (one pass over live rules), never on the firing path — and
/// `&KnowledgeBase`, though every other entry point in this module takes `&mut`: nothing
/// here mutates, and the census is consumed by a DIAGNOSTIC, which is exactly the place
/// a caller is apt to hold a shared borrow. A `&mut` here would push such a caller into
/// re-deriving the counts, the duplication this function exists to prevent.
pub(super) fn equation_clause_census(kb: &KnowledgeBase, functor: Symbol) -> ClauseCensus {
    let mut census = ClauseCensus {
        defining: 0,
        simp_tagged: 0,
    };
    // Streamed, not `live_rule_ids()`: that would materialize a Vec of EVERY
    // non-retracted rule (thousands, on a stdlib-sized KB) to then keep a handful.
    // `is_simp_equation` re-asks `is_equation` — left alone deliberately, because it is
    // the firing sites' own predicate and this module's doc is explicit that a reader
    // must not re-derive it to save a walk.
    for rid in kb.live_rule_ids_iter() {
        if !kb.is_equation(rid) || stored_lhs_functor(kb, rid) != Some(functor) {
            continue;
        }
        census.defining += 1;
        if is_simp_equation(kb, rid) {
            census.simp_tagged += 1;
        }
    }
    census
}

/// WI-1058 — the LHS SHAPE (positional arity + named-argument labels) of every live
/// equation defining `functor`, or `None` if any of them has a shape this cannot read.
///
/// The equation half of "could any clause of this name ever match this term". A `[simp]`
/// redex fires by MATCHING the stored LHS, so a call at an arity no LHS has can never
/// fire — the silent inertness [`ClauseCensus`] can only describe after the fact. The
/// `None` is the same honesty [`crate::kb::typing`]'s clause-head reader keeps: the
/// caller refuses only on a PROOF that nothing matches, and an unreadable head is not one.
///
/// Counts TAGGED AND UNTAGGED equations alike, for the census's own reason: an untagged
/// clause is inert, not absent, and its shape is still a shape this call could have been
/// written against. (`ClauseCensus` is what tells the two apart when the shape DOES
/// match.) Labels are returned unsorted-by-nothing — the caller canonicalises.
pub(super) fn equation_lhs_shapes(
    kb: &KnowledgeBase,
    functor: Symbol,
) -> Option<Vec<(usize, Vec<Symbol>)>> {
    let mut out: Vec<(usize, Vec<Symbol>)> = Vec::new();
    for rid in kb.live_rule_ids_iter() {
        if !kb.is_equation(rid) || stored_lhs_functor(kb, rid) != Some(functor) {
            continue;
        }
        let head = kb.fact_head_term(rid)?;
        let Term::Fn { pos_args, .. } = kb.get_term(head) else {
            return None;
        };
        let lhs = *pos_args.first()?;
        // WI-20260902-CZJ2N — a NULLARY LHS is stored bare, and its shape is
        // `(0, [])`. Bailing with `None` here is what the `Fn`-only destructure did,
        // and it became reachable the moment `stored_lhs_functor` learned to answer
        // for a `Ref` LHS (the sibling fix in this same file): the loop walked in and
        // then abandoned the whole census, which `data_functor_error` reads as "no
        // proof" and says NOTHING — so a call at an arity no clause has stopped being
        // refused, for every functor with a nullary defining equation.
        let shape = match kb.get_term(lhs) {
            Term::Fn {
                pos_args,
                named_args,
                ..
            } => (pos_args.len(), named_args.iter().map(|(k, _)| *k).collect()),
            Term::Ref(_) | Term::Ident(_) => (0usize, Vec::new()),
            _ => return None,
        };
        if !out.contains(&shape) {
            out.push(shape);
        }
    }
    Some(out)
}

/// [`equation_clause_census`]'s answer. `pub` because `TypeError` — public API —
/// carries one on its WI-898 variant; the *taking* of a census stays `pub(super)`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ClauseCensus {
    /// LIVE bodyless equations whose LHS functor is the subject — tagged or not,
    /// indexed or not (see the census's own note on why the tagless ones must count).
    pub defining: usize,
    /// …of which, those tagged `[simp]` — the ones the typer can fire.
    pub simp_tagged: usize,
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

/// The typer's firing strategy: type-directed [`try_fire`].
pub(super) struct TyperFirer {
    /// WI-757: the FIRST macro rejection this walk saw. The [`SimpFirer`] face is
    /// `Option`-valued (the resolver's firer has no diagnostic to report), so this
    /// harness keeps the rejection here instead of discarding it — [`run`] hands it
    /// back to its caller. The typer's own firing site does NOT go through this
    /// firer; it calls [`try_fire`] directly and reports at the redex.
    pub(super) rejected: Option<MacroRejection>,
}

impl SimpFirer for TyperFirer {
    fn fire(&mut self, kb: &mut KnowledgeBase, redex: &Value, rids: &[RuleId]) -> Option<Value> {
        // The typer only ever walks operation bodies, which are occurrence
        // trees — every node the driver hands it is a `Value::Node` (the
        // occurrence carrier is closed under descent + rewrite). A non-Node
        // here is a carrier-routing bug, not a recoverable case.
        match redex {
            Value::Node(occ) => match try_fire(kb, occ, rids) {
                Ok(fired) => fired.map(Value::Node),
                // Keep the first rejection and DECLINE at this node, so the walk
                // still completes and `run` reports one failure rather than the
                // last one. Not a silent skip: `run` returns it.
                Err(rejection) => {
                    self.rejected.get_or_insert(rejection);
                    None
                }
            },
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
///
/// WI-757: returns the FIRST macro rejection the walk saw, if any — this harness
/// has no error sink of its own, and a rejection is a definitive user-caused
/// failure that must not evaporate. `None` = every body rewrote (or declined)
/// cleanly.
#[must_use = "a macro rejection is a user-facing diagnostic; dropping it silences it"]
pub fn run(kb: &mut KnowledgeBase) -> Option<MacroRejection> {
    if !has_simp_equations(kb) {
        return None;
    }
    let mut firer = TyperFirer { rejected: None };
    // Snapshot (op_sym, body) so we don't hold a borrow on `op_bodies` while
    // rewriting (which mutates `kb` — fresh vars, interning).
    let bodies: Vec<(Symbol, Rc<NodeOccurrence>)> = kb
        .op_bodies_iter()
        .map(|(s, n)| (s, Rc::clone(n)))
        .collect();
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
    firer.rejected
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
    let mut work: Vec<RewriteOp> = vec![RewriteOp::Visit {
        node: root.clone(),
        fuel,
    }];
    let mut results: Vec<Value> = Vec::new();

    while let Some(op) = work.pop() {
        match op {
            RewriteOp::Visit { node, fuel } => visit_node(kb, node, fuel, &mut work, &mut results),
            RewriteOp::Build {
                node,
                fuel,
                child_count,
            } => build_node(
                kb,
                node,
                fuel,
                child_count,
                firer,
                &rids,
                &mut work,
                &mut results,
            ),
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
    Visit {
        node: Value,
        fuel: usize,
    },
    /// `child_count` is the number of child `Visit`s scheduled alongside this
    /// frame — captured at `visit_node` time so `build_node` knows how many
    /// results to claim without re-walking the node.
    Build {
        node: Value,
        fuel: usize,
        child_count: usize,
    },
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
    work.push(RewriteOp::Build {
        node,
        fuel,
        child_count: children.len(),
    });
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
        Some(fired) => work.push(RewriteOp::Visit {
            node: fired,
            fuel: fuel - 1,
        }),
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
                    node_occurrence::for_each_child(expr, |c| {
                        children.push(Value::Node(Rc::clone(c)))
                    });
                }
            }
            children
        }
        Value::Term { id, .. } => match kb.get_term(*id) {
            Term::Fn {
                pos_args,
                named_args,
                ..
            } => {
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
                    other => {
                        unreachable!("occurrence child must be a Node, got {}", other.type_name())
                    }
                })
                .collect();
            Value::Node(reassemble(occ, &occs))
        }
        Value::Term { id, .. } => match kb.get_term(*id).clone() {
            Term::Fn {
                functor,
                pos_args,
                named_args,
            } => {
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
                Value::term(kb.alloc(Term::Fn {
                    functor,
                    pos_args: new_pos,
                    named_args: new_named,
                }))
            }
            _ => node.clone(),
        },
        _ => node.clone(),
    }
}

/// Try to fire a `[simp]` equation at this node. Returns the rewritten
/// occurrence, or `Ok(None)` if no equation matches (or its type-directed
/// guard fails).
///
/// WI-283: matches the rule LHS structurally via `match_view`, then — for
/// a redex whose functor is a *spec op* (a rule scoped to a parametric
/// sort, e.g. `Numeric.add`) — fires only where the receiver's type
/// satisfies that sort ([`super::typing::simp_fire_guard_holds`]). A
/// concrete-functor redex (a top-level monomorphic identity like
/// `transpose(transpose(?m)) = ?m`) is guard-free: the functor symbol
/// already pins the sort, so structural match alone is sound.
///
/// WI-757: `Err` is a matched macro-RHS lowering whose MACRO rejected the
/// occurrences it was handed ([`MacroRejection`]) — a definitive, user-caused
/// failure the caller must report at this redex, as distinct from the `Ok(None)`
/// decline that keeps the template.
pub(super) fn try_fire(
    kb: &mut KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    rids: &[RuleId],
) -> Result<Option<Rc<NodeOccurrence>>, MacroRejection> {
    let node_functor = match occ.as_expr() {
        Some(Expr::Apply { functor, .. }) => *functor,
        Some(Expr::Constructor { name, .. }) => *name,
        _ => return Ok(None),
    };
    // WI-655: the type-directed guard (`simp_fire_guard_holds`) is deferred to the
    // FIRST rid whose LHS functor matches this node (checked once, below, before any
    // `match_view`). A node whose functor matches no `[simp]` rule can never fire — the
    // `stored_lhs_functor` filter rejects every candidate — so it now skips the guard
    // entirely: the guard was ~78% of per-node simp cost (and fires 0 rewrites over the
    // whole stdlib), pure waste on a non-matching node. Sound: the guard verdict is
    // irrelevant when nothing matches the functor, and it is side-effect-free.
    // The type-directed guard verdict for this node: `None` = not yet evaluated,
    // `Some(true)` = holds (value-RHS laws may fire), `Some(false)` = fails (only a
    // macro-RHS lowering may fire). Evaluated at most once per node (WI-655).
    let mut guard: Option<bool> = None;
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
        // WI-655: evaluate the type-directed guard ONCE per node (a spec/sort law holds
        // only for carriers satisfying its sort), memoized across sibling rids of the
        // same functor and kept BEFORE the allocate-heavy `open_equation`.
        let guard_holds =
            *guard.get_or_insert_with(|| super::typing::simp_fire_guard_holds(kb, occ));
        // WI-714: a MACRO-headed RHS (`where <=> guarded_of`) is a definitional
        // compile-time LOWERING, not a conditional typeclass law — it bypasses the
        // carrier guard (the macro is its own validity check; its carrier need not
        // `provides` its own abstract self-sort, `sort_provides(Relation, Relation)`
        // being false, else `where` would stay permanently dormant). So when the guard
        // did NOT hold, a value-RHS law is skipped but a macro-RHS lowering still fires.
        // Read from the STORED head (no DeBruijn open) and ONLY on guard failure, so the
        // common guard-passing path pays nothing. (WI-611 catch-22: firing a Map/Set
        // value-RHS reducing law on an abstract carrier yields an eval-broken body.)
        if !guard_holds
            && !stored_rhs_functor(kb, rid).is_some_and(|f| super::typing::is_macro(kb, f))
        {
            continue;
        }
        // WI-20260903-FCZ3N: the opened `fresh` globals are threaded into
        // `instantiate_rhs`, which opens this rule's WRITTEN RHS occurrence against the
        // same frame. (They key the resolver's typed-pattern bounds too; the typer skips
        // bound-carrying rules above and reads them for nothing else.)
        let (lhs, rhs, fresh) = match open_equation(kb, rid) {
            Some(opened) => opened,
            None => continue,
        };
        // WI-1129 (proposal 056 §2.3): a head written `fix(?r, ...?args)` matches a
        // redex whose named arguments it does not name, by FOLDING the leftovers into
        // one record occurrence first — see [`fold_capture_redex`]. The pattern is
        // untouched: the capture variable is an ordinary positional slot in it, so the
        // matcher that runs below is the same one, over a redex reshaped to the arity
        // the pattern already has. `None` = this redex cannot supply the capture
        // (wrong positional arity, a declared named argument missing); that is an
        // ordinary non-match, so the next candidate gets its turn.
        let folded = match kb.rule_head_capture(rid) {
            None => None,
            Some(capture_idx) => match fold_capture_redex(kb, lhs, occ, capture_idx) {
                Some(target) => Some(target),
                None => continue,
            },
        };
        // `occ` is itself a `TermView` (WI-277), so we match the rule LHS
        // against it in place — no `Value::Node` wrapping.
        let target = folded.as_ref().unwrap_or(occ);
        if let Some(subst) = kb.match_view(lhs, target) {
            if subst.is_contradiction() {
                continue;
            }
            // The RHS is instantiated `from` the FOLDED redex when there is one, so the
            // synthesized provenance chain reaches the record occurrence the macro was
            // handed rather than a node it never saw.
            return Ok(Some(instantiate_rhs(kb, rid, rhs, &fresh, &subst, target)?));
        }
    }
    Ok(None)
}

/// WI-1129 (proposal 056 §2.3) — reshape a redex so that a VARIADIC-CAPTURE rule head
/// can match it with the ordinary matcher: collect every named argument the head does
/// NOT name into one named-tuple record occurrence, and hand it back as the redex's
/// `capture_idx`-th positional argument.
///
/// `lhs` is the OPENED rule head (`fix(?r, ?args)` — the capture variable is a plain
/// positional slot in it, which is exactly why nothing about matching, DeBruijn
/// numbering or discrimination-tree keying had to change for this feature).
/// `capture_idx` is [`KnowledgeBase::rule_head_capture`]'s verdict, decided at parse.
///
/// `None` when this redex cannot supply the capture at all: a positional arity other
/// than the head's declared count, or a named argument the head DOES name that the
/// redex does not carry. Both are ordinary non-matches — the same answer `match_view`
/// would give — not diagnostics, because a functor may be lowered by several rules
/// and only one of them need match.
///
/// The record is an `Expr::Constructor` over `anthill.reflect.TupleLiteral` — the SAME
/// shape the operation face builds (`typing::synthesize_named_tuple_literal`), so a
/// macro reads its component labels through `occurrence_term` (whose named arguments
/// ARE the labels) and its children through `sub_occurrences`, with no form of its
/// own to learn. Its components keep the redex's OWN label symbols and source order.
/// It is deliberately left UNTYPED (no `set_inferred_type`): the operation face stamps
/// a type because a `Without[Drop = R]` return-type constructor consumes it, whereas
/// §2.3's reader is a macro that reads syntax — and a captured argument's own type is
/// still reachable, per component, through `occurrence_type`.
///
/// An EMPTY capture is a record with no components, not a failure — 056 §3 OQ #6, the
/// same verdict the operation face reaches for `r.fix()`.
fn fold_capture_redex(
    kb: &mut KnowledgeBase,
    lhs: TermId,
    occ: &Rc<NodeOccurrence>,
    capture_idx: usize,
) -> Option<Rc<NodeOccurrence>> {
    let Term::Fn {
        pos_args: pat_pos,
        named_args: pat_named,
        ..
    } = kb.get_term(lhs)
    else {
        return None;
    };
    debug_assert_eq!(
        capture_idx + 1,
        pat_pos.len(),
        "WI-1129: a rule-head capture is TRAILING by construction \
         (parse/convert.rs `claim_rule_head_captures`); a middle one would leave the \
         slots after it undefined",
    );
    // The head's declared positional count is its arity minus the capture slot.
    let declared_pos = capture_idx;
    let pat_labels: SmallVec<[Symbol; 2]> = pat_named.iter().map(|(s, _)| *s).collect();

    // WI-1130: `ctor_from_projection` rather than a bare `is_constructor` flag, so the
    // rebuild below CANNOT invent the mark — `Some(fp)` carries the redex's own value and
    // `None` says "this was an Apply, which has no such field". It used to destructure
    // with `..` and rebuild `from_projection: false`, which is exactly what that field's
    // doc (node_occurrence.rs, WI-762) says must never happen: the mark rides INSIDE the
    // `Expr` so that every rebuild site is a compile error until it decides, and missing
    // one is SILENT — a distributive projection re-read as a tuple of independent
    // single-column relations, the WI-732 mis-typing. Binding it by name restores that
    // compile-time obligation here. Found by a `/code-review` pass, which also probed the
    // arm and could not reach it today (a capture rule on a constructor head is refused at
    // load as a constructor-arity error), so this is a LATENT trap closed, not a live bug
    // fixed — and it is closed by construction rather than by remembering.
    let (functor, occ_pos, occ_named, ctor_from_projection) = match occ.as_expr()? {
        Expr::Apply {
            functor,
            pos_args,
            named_args,
            type_args,
            recv_type,
        } => {
            // A call-site type-argument bracket is not part of the Inc-1 macro surface
            // (`try_expand_macro` declines a template carrying one), so a capture rule
            // declines it here rather than dropping the bracket in the reshaped redex.
            // WI-20260829-W6JH0: a form-(3) COMPANION RECEIVER is declined on the same
            // grounds and in the same test — it is a type claim about the call's result,
            // and the reshaped redex has nowhere to put it.
            if !type_args.is_empty() || recv_type.is_some() {
                return None;
            }
            (*functor, pos_args, named_args, None)
        }
        Expr::Constructor {
            name,
            pos_args,
            named_args,
            from_projection,
        } => (*name, pos_args, named_args, Some(*from_projection)),
        _ => return None,
    };
    if occ_pos.len() != declared_pos {
        return None;
    }
    // Partition the redex's named arguments: one that the head NAMES stays in place
    // (keyed by the head's own symbol, so the matcher's identity comparison sees the
    // pattern's spelling); every other is a component of the captured record.
    let mut kept: Vec<(Symbol, Rc<NodeOccurrence>)> = Vec::new();
    let mut captured: Vec<(Symbol, Rc<NodeOccurrence>)> = Vec::new();
    for (label, child) in occ_named.iter() {
        match pat_labels
            .iter()
            .find(|p| super::typing::same_label(kb, **p, *label))
        {
            Some(&pat_label) => kept.push((pat_label, Rc::clone(child))),
            None => captured.push((*label, Rc::clone(child))),
        }
    }
    if kept.len() != pat_labels.len() {
        return None;
    }
    // Resolved outright, not `try_`-ed. This function's `None` means ONE thing — this
    // redex does not match — and an unresolvable constructor is not that; declining
    // would make the rule silently never fire, with nothing said anywhere. The
    // constructor is DEFINED by `register_prelude` (through `register_stdlib_scopes`,
    // beside `SetLiteral` / `ListLiteral`), which every load path runs before any rule
    // loads — so this is total with no stdlib at all; if that ever stops holding,
    // `resolve_symbol` says so by name. MEASURED both ways by
    // `wi1129_rule_head_capture_test::the_capture_record_constructor_is_bootstrapped`:
    // absent on a `KnowledgeBase::new()`, present after a bare `load_all`.
    //
    // `dt::qualified`, NOT the bare `dt::TUPLE_LITERAL` constant: the constant carries
    // the absolute-path marker, which is the address the converter WRITES and which
    // DEFINES nothing — `register_stdlib_scopes` defines the plain qualified name, so
    // resolving the marked spelling here would panic. (This warning outlived the
    // `load::CAPTURE_RECORD_CONSTRUCTOR` constant that used to carry it; S66VH retired
    // the constant as a second hand-written address and kept the reasoning.)
    let tuple_sym = kb.resolve_symbol(dt::qualified(dt::TUPLE_LITERAL));
    let pass = simp_pass(kb);
    let record = NodeOccurrence::synthesized_expr(
        Expr::Constructor {
            name: tuple_sym,
            pos_args: Vec::new(),
            named_args: captured,
            // CORRECTLY `false`, unlike the rebuild below (WI-1130): this node is MINTED
            // here, from the redex's leftover named arguments — there is no prior mark to
            // carry, and a capture record is not a distributive projection.
            from_projection: false,
        },
        Rc::clone(occ),
        pass,
        occ.owner,
    );
    let mut pos_args: Vec<Rc<NodeOccurrence>> = occ_pos.to_vec();
    pos_args.push(record);
    let expr = if let Some(from_projection) = ctor_from_projection {
        Expr::Constructor {
            name: functor,
            pos_args,
            named_args: kept,
            // The REDEX's own mark, carried — never re-decided here. Reshaping a node's
            // argument list is not a statement about where the node came from.
            from_projection,
        }
    } else {
        Expr::Apply {
            recv_type: None,
            functor,
            pos_args,
            named_args: kept,
            type_args: Vec::new(),
        }
    };
    Some(NodeOccurrence::synthesized_expr(
        expr,
        Rc::clone(occ),
        pass,
        occ.owner,
    ))
}

/// WI-902 — INSTANTIATE a fired `[simp]` rule's RHS: build the template from the
/// match substitution, then macro-expand it if it is headed by a macro. The whole
/// of "what a fire produces", owned once. The expansion itself is
/// [`try_expand_macro`]'s (WI-722); the typer's `push_visit` continuation re-types
/// the spliced subtree.
///
/// Both typer-side firing sites go through this — [`try_fire`] (the Apply /
/// Constructor redex) and `typing::try_fire_dot_rule` (the WI-279 INC2 sort-scoped
/// dot rule). They were split before WI-902: the dot site stopped at
/// [`substitute_to_occurrence`]. Keeping the two steps welded together is what
/// makes "a fired `[simp]` RHS is macro-expanded" a property of the ENGINE rather
/// than of each caller remembering. `Err` is the rejection, for the caller to
/// report at its redex.
///
/// The synthesis [`PassId`] is fetched HERE rather than threaded in: [`simp_pass`]
/// is idempotent for exactly this reason, and a fire that does not match should not
/// pay for one. That let both callers drop a parameter and `TyperFirer` drop a field.
pub(super) fn instantiate_rhs(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    rhs: TermId,
    fresh: &[VarId],
    subst: &Substitution,
    from: &Rc<NodeOccurrence>,
) -> Result<Rc<NodeOccurrence>, MacroRejection> {
    let pass = simp_pass(kb);
    let template = build_rhs_template(kb, rid, rhs, fresh, subst, from, pass);
    Ok(try_expand_macro(kb, &template)?.unwrap_or(template))
}

/// [`instantiate_rhs`]'s sibling for the RESOLVER's fire (`resolve.rs`
/// `fire_simp_equation`): build the RHS and stop — NO macro expansion, deliberately.
/// 043.1 §5: a macro is a compile-time syntax transform, so it runs occurrence-side
/// at the typer only; a runtime `Term` goal is not a syntax bracket.
///
/// The two intents are NAMED so that neither is the default: [`substitute_to_occurrence`]
/// is private, and a future firing site must pick `instantiate_rhs` (expands) or this
/// (does not) rather than reach the raw builder and silently get the WI-902 defect —
/// which is precisely how the dot site came to keep its templates. Illegal state
/// unrepresentable, over a doc comment asking callers to remember.
pub(super) fn instantiate_rhs_verbatim(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    rhs: TermId,
    fresh: &[VarId],
    subst: &Substitution,
    from: &Rc<NodeOccurrence>,
) -> Rc<NodeOccurrence> {
    let pass = simp_pass(kb);
    build_rhs_template(kb, rid, rhs, fresh, subst, from, pass)
}

/// WI-20260903-FCZ3N — THE SUBSTITUTED RHS, BUILT FROM THE OCCURRENCE THE AUTHOR WROTE
/// WHEN THE RULE KEPT ONE. The one place the two builders are chosen between, so neither
/// firing site decides it.
///
/// [`KnowledgeBase::rule_equation_rhs_node`] holds a source-written equation's RHS as an
/// occurrence, De Bruijn-closed beside the head. THREE STEPS, in this order, and the
/// order is what makes each one simple:
///
///  1. **OPEN** it against the SAME `fresh` globals [`open_equation`] opened the head
///     term with, so its variable leaves — everywhere, `Expr::Apply`'s `type_args` and
///     `recv_type` included — are the ones `subst` binds.
///  2. **RE-PARENT** every node onto the redex ([`reparent_spliced`]). Done BEFORE the
///     substitution, while the tree is still the template alone: after it, a matched
///     redex child is spliced in and must keep ITS identity, and a re-parent pass could
///     no longer tell the two apart.
///  3. **SUBSTITUTE** through [`node_occurrence::substitute_occurrence`] — the ONE owner
///     of "apply σ to an occurrence", shared with the resolver's per-goal walk. It
///     rebuilds with `rebuilt_expr`, which carries the span, the `dot_chain` and the
///     `Synthesized` origin step 2 just wrote.
///  4. **BOTTOM OUT** whatever rule variable σ did not bind ([`bottom_out_unbound`]),
///     because step 3's owner answers a DIFFERENT question about a free variable than
///     this one does — see below.
///
/// STEP 3 IS THAT FUNCTION AND NOT A LOCAL WALK, because σ reaches more places than an
/// `Expr::Var` leaf: `Expr::Apply`'s `type_args` and `recv_type`, a `Type`/`EffectExpr`
/// spine, a `Pattern`'s annotation. This ticket's first cut substituted only the leaves
/// `for_each_child` yields and copied the rest verbatim; `/code-review` found it.
///
/// ── A RULE VARIABLE IN A TYPE POSITION IS STILL NOT INSTANTIATED ────────────
///
/// AND ROUTING THROUGH `substitute_occurrence` DOES NOT FIX IT, which is measured rather
/// than assumed. With `import anthill.prelude.Map.{empty, put, size}`, driven by
/// `size(put(mk(…), "a", 1))` — the mismatch is `"a"` against the receiver's `K`:
///
/// | `[simp]` RHS                                 | before this ticket | now |
/// |---|---|---|
/// | `Map[K = Bool, V = Int64].empty()` (GROUND)  | 0 errors | **1** |
/// | `Map[K = ?k,   V = Int64].empty()` (VARIABLE)| 0 errors | 0 |
/// | the same call written directly in an operation body | 1 | 1 |
///
/// The GROUND row is this ticket's own gain: the term path dropped `recv_type`
/// altogether, so the receiver the author wrote was never checked at all, and it now
/// agrees with the direct spelling. The VARIABLE row is UNMOVED — 0 before, 0 after — and
/// the reason is a layer below this one: the typer's fire binds every rule variable to a
/// `Value::Node` (the redex's children are occurrences), and a type position is a
/// `Value::Term` whose σ is `KnowledgeBase::apply_subst`, which is term-world and
/// documents that "a var bound to a non-`Term` carrier stays the var". So `?k` stays the
/// throwaway `fresh` global, which unifies with anything.
///
/// NOT REFUSED AT LOAD EITHER, and that is the same measurement: whether the binding can
/// be represented depends on the REDEX, so a load-time refusal would also refuse the
/// resolver's term-bound case, which works. Censused: **0** of the 21 `[simp]`/`[unfold]`
/// equations in a stdlib load carry a type position at all, so nothing shipped depends on
/// either answer today. **OWNED BY WI-20260903-H054K**, which has to decide between
/// converting a type-shaped `Value::Node` binding into a type term and refusing at the
/// FIRE, where the carrier is known.
///
/// ── WHY STEP 4 EXISTS: ONE WALK, TWO QUESTIONS ABOUT A FREE VARIABLE ────────
///
/// [`node_occurrence::substitute_occurrence`] is the RESOLVER's σ, and there a surviving
/// `Expr::Var` is ORDINARY — a goal has free variables and `subst_var_leaf` keeps the
/// leaf by design. Instantiating a `[simp]` RHS is the opposite question: the LHS match
/// binds every variable the rule can bind, so one left over is a rule whose RHS names
/// something nothing supplies, and [`substitute_to_occurrence`] said so by writing `⊥`
/// ("a well-formed `[simp]` rule binds every RHS var", its own doc).
///
/// MEASURED — `rule f(?x) <=> g(?y) [simp]` with a consumer that fires it: the term path
/// answers **1** error, and routing σ through the shared owner alone answered **0**, i.e.
/// a malformed rule loading clean. So the reuse is kept (σ over an occurrence must have
/// ONE owner) and the verdict is restored beside it, rather than the walk being forked.
/// The `⊥` now carries the RHS VARIABLE's own span instead of the redex's, which is the
/// same relocation this whole ticket is about.
///
/// NOT A LOAD REFUSAL, for [`build_rhs_template`]'s neighbouring reason: an equation is
/// logically symmetric and citable both ways with `using` (§8.3), so `f(?x) <=> g(?y)` is
/// a strange but not meaningless LAW. What is broken is instantiating it left-to-right,
/// and that is exactly where this fires.
///
/// `rhs` (the opened head term's second operand) is what a rule with NO written RHS
/// falls back to, and that is not a hedge: a host-asserted or runtime-asserted equation
/// HAS no source text, so there is no occurrence to keep and re-deriving one from the
/// term is the honest answer for it. With step 4 in, the two paths agree on the unbound
/// case; they still differ on a STRUCTURED binding, which rides as `Expr::Spliced`
/// (WI-1040) here and had no arm at all in the term path.
fn build_rhs_template(
    kb: &mut KnowledgeBase,
    rid: RuleId,
    rhs: TermId,
    fresh: &[VarId],
    subst: &Substitution,
    from: &Rc<NodeOccurrence>,
    pass: PassId,
) -> Rc<NodeOccurrence> {
    match kb.rule_equation_rhs_node(rid) {
        Some(node) => {
            let opened = node_occurrence::open_debruijn_node(kb, &node, fresh);
            let spliced = reparent_spliced(&opened, from, pass);
            let applied = node_occurrence::substitute_occurrence(kb, &spliced, subst);
            bottom_out_unbound(&applied, fresh)
        }
        None => substitute_to_occurrence(kb, rhs, subst, from, pass),
    }
}

/// WI-20260903-FCZ3N — RE-PARENT A WRITTEN RHS ONTO THE REDEX IT IS BEING SPLICED INTO,
/// node by node, keeping everything else the author wrote.
///
/// The inverse of [`substitute_to_occurrence`]'s shape: that one walks a TERM and MINTS
/// an occurrence for each node (`synthesized_expr`, which hardcodes `dot_chain: false`
/// and takes the redex's span — correctly, for a node a pass decided to build); this one
/// walks the OCCURRENCE and mints nothing. Every node keeps its span and its `dot_chain`
/// ([`NodeOccurrence::reparented_from`]) and changes exactly two things — its provenance
/// and its `owner`.
///
/// WHAT THE SPAN AND THE BIT REPAIR, measured — `rule trig(?x) <=> sink(ns.inner.rel)
/// [simp]` with a consumer that fires it: THREE "expected resolved name, got unresolved"
/// errors at the REDEX became ONE, at the citation, naming the relation. The three were
/// WI-20260902-4NEKZ's per-leaf cascade, back because the spliced chain arrived with
/// `dot_chain` clear and `loader_chain_dotted_name`'s provenance gate could not read it.
///
/// TWO REASONS FOR THE RE-PARENT, and the second would have been a live bug:
///
///  * **PROVENANCE.** WI-20260820-5R2XT walks `Synthesized { from }` from a spliced node
///    to the surface call the author wrote, and a macro-headed RHS reaches the redex
///    through its TEMPLATE. Left `Source`, that chain would stop inside the rule and
///    `join(p, q, λ)` would report the macro's name instead of `join`. MEASURED: all four
///    arms of `wi_5r2xt_macro_spliced_call_name_test` fail without it.
///  * **NO SHARING WITH THE STORED RULE.** A `NodeKind::Expr` carries the typer's
///    `RefCell` stamps (`inferred_type`, the `CallClass`, `resolved_type_args`,
///    `lowered_receiver`). Splicing the rule's own `Rc` into an operation body would make
///    two call sites of one `[simp]` rule write those cells over each other.
///    `reparented_from` allocates, so every fire gets its own nodes.
///
/// ITERATIVE, for [`substitute_to_occurrence`]'s reason (WI-278): a `[simp]` RHS is
/// author-written and can nest as deeply as the source does.
///
/// A `Pattern` node (a `[simp]` RHS may write a lambda or a `match`) is descended and
/// rebuilt through the pattern pair `for_each_pattern_child` / `reassemble_pattern`, the
/// same one `open_debruijn_node` uses — the node itself holds no `RefCell` state, but its
/// `type_ann` is an `Expr` and would otherwise be the shared cell above. A `Type` /
/// `EffectExpr` spine is left as it is: it carries no stamps either, and it is
/// [`node_occurrence::substitute_occurrence`], one step later, that reaches inside one.
fn reparent_spliced(
    rhs_node: &Rc<NodeOccurrence>,
    from: &Rc<NodeOccurrence>,
    pass: PassId,
) -> Rc<NodeOccurrence> {
    let mut work: Vec<SpliceOp> = vec![SpliceOp::Visit(Rc::clone(rhs_node))];
    let mut results: Vec<Rc<NodeOccurrence>> = Vec::new();
    while let Some(op) = work.pop() {
        match op {
            SpliceOp::Visit(node) => {
                let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
                if let Some(expr) = node.as_expr() {
                    node_occurrence::for_each_child(expr, |c| children.push(Rc::clone(c)));
                } else if node.as_pattern().is_some() {
                    node_occurrence::for_each_pattern_child(&node, |c| children.push(Rc::clone(c)));
                }
                work.push(SpliceOp::Build {
                    child_count: children.len(),
                    node,
                });
                // Reversed, so children pop — and land on `results` — in the enumeration
                // order, which is the order the matching `reassemble*` consumes them.
                for c in children.into_iter().rev() {
                    work.push(SpliceOp::Visit(c));
                }
            }
            SpliceOp::Build { node, child_count } => {
                let start = results.len() - child_count;
                let new_children: Vec<Rc<NodeOccurrence>> = results.split_off(start);
                let rebuilt = if node.as_expr().is_some() {
                    reassemble(&node, &new_children).reparented_from(
                        Rc::clone(from),
                        pass,
                        from.owner,
                    )
                } else if node.as_pattern().is_some() {
                    node_occurrence::reassemble_pattern(&node, &new_children)
                } else {
                    Rc::clone(&node)
                };
                results.push(rebuilt);
            }
        }
    }
    debug_assert_eq!(results.len(), 1, "reparent_spliced: expected one result");
    results
        .pop()
        .expect("written RHS produced no NodeOccurrence")
}

/// WI-20260903-FCZ3N — REPLACE EVERY RULE VARIABLE σ DID NOT BIND WITH `⊥`.
///
/// `fresh` is the rule's OWN frame ([`open_equation`]'s opened globals), so a
/// `Expr::Var(Var::Global(v))` with `v ∈ fresh` surviving the substitution is a variable
/// the LHS match had no value for — a malformed `[simp]` rule, and the verdict
/// [`substitute_to_occurrence`] has always given it. See [`build_rhs_template`] for why
/// the shared σ owner cannot give it (there, a free variable is an ordinary goal
/// variable) and why this is not a load refusal.
///
/// KEYED ON `fresh`, NOT ON "any Global": a redex variable rides straight into the RHS
/// through a projecting rule (`pick(?q, 7) → ?q`, WI-634) and is legitimately unbound
/// there — bottoming that out would break a working rewrite. Only the RULE's own frame is
/// the rule's obligation.
///
/// Returns the input unchanged (same `Rc`) when nothing is left, which is every
/// well-formed rule — so a fire pays one walk over its own RHS and no allocation.
fn bottom_out_unbound(root: &Rc<NodeOccurrence>, fresh: &[VarId]) -> Rc<NodeOccurrence> {
    if fresh.is_empty() {
        return Rc::clone(root);
    }
    let mut work: Vec<SpliceOp> = vec![SpliceOp::Visit(Rc::clone(root))];
    let mut results: Vec<Rc<NodeOccurrence>> = Vec::new();
    while let Some(op) = work.pop() {
        match op {
            SpliceOp::Visit(node) => {
                if let Some(Expr::Var(Var::Global(v))) = node.as_expr() {
                    if fresh.contains(v) {
                        results.push(node.rebuilt_expr(Expr::Bottom));
                        continue;
                    }
                }
                let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
                if let Some(expr) = node.as_expr() {
                    node_occurrence::for_each_child(expr, |c| children.push(Rc::clone(c)));
                } else if node.as_pattern().is_some() {
                    node_occurrence::for_each_pattern_child(&node, |c| children.push(Rc::clone(c)));
                }
                work.push(SpliceOp::Build {
                    child_count: children.len(),
                    node,
                });
                for c in children.into_iter().rev() {
                    work.push(SpliceOp::Visit(c));
                }
            }
            SpliceOp::Build { node, child_count } => {
                let start = results.len() - child_count;
                let new_children: Vec<Rc<NodeOccurrence>> = results.split_off(start);
                let rebuilt = if node.as_expr().is_some() {
                    reassemble(&node, &new_children)
                } else if node.as_pattern().is_some() {
                    node_occurrence::reassemble_pattern(&node, &new_children)
                } else {
                    Rc::clone(&node)
                };
                results.push(rebuilt);
            }
        }
    }
    debug_assert_eq!(results.len(), 1, "bottom_out_unbound: expected one result");
    results
        .pop()
        .expect("written RHS produced no NodeOccurrence")
}

/// Work-stack item for the iterative [`reparent_spliced`] and [`bottom_out_unbound`], the
/// occurrence-carrier twin of [`SubstOp`].
enum SpliceOp {
    Visit(Rc<NodeOccurrence>),
    Build {
        node: Rc<NodeOccurrence>,
        child_count: usize,
    },
}

/// The functor of an equation's RHS (`Fn{eq/unify, [lhs, rhs]}` → rhs head), read
/// from the STORED head with NO DeBruijn opening — the sibling of [`stored_lhs_functor`]
/// (which reads the LHS at arg 0; this reads the RHS at arg 1). [`try_fire`] uses it to
/// detect a macro-RHS lowering (`where <=> guarded_of`) cheaply, before the
/// allocate-heavy `open_equation`, so a macro-RHS rule can bypass the spec-op carrier
/// guard while the common value-RHS path keeps guarding first (WI-655 cost model). A
/// non-`Fn` RHS (a bare const / nullary ref, e.g. `peek(?s) <=> true`) reads `None` —
/// never a macro, so it stays guard-gated.
///
fn stored_rhs_functor(kb: &KnowledgeBase, rid: RuleId) -> Option<Symbol> {
    stored_eq_operand_functor(kb, rid, 1)
}

/// WI-757 — the RHS-head MACRO that [`try_fire`] would EVALUATE AWAY for `rid`, or
/// `None` when this rule's RHS head is not macro-expanded at all.
///
/// The one owner of "would the expander actually run this macro?", so the WI-702
/// effectful-rewrite gate (`typing::check_simp_effectful_ops`) can exempt the macro
/// position — whose call is consumed by compilation and never reaches runtime —
/// WITHOUT the exemption drifting wider than the expansion it is justified by. Every
/// condition below is one [`try_fire`] itself applies; each one it does NOT is a
/// rule the typer leaves alone, where the RHS call really does survive the rewrite
/// into the program and must stay gated:
///
/// - `[simp]` ONLY. `[unfold]` is fired by the RESOLVER (`fire_simp_equation`),
///   which substitutes the RHS template verbatim and never macro-expands — so an
///   `[unfold]` rule's effectful RHS is exactly the hazard WI-702 exists for.
///   MEASURED: with the exemption keyed on `is_macro` alone, an effectful macro
///   under `[unfold]` loaded clean.
/// - NO typed-pattern bounds. WI-582: [`try_fire`] skips a rule carrying `?x: T`
///   bounds outright, leaving it to the resolver's `apply_eq_rules` — which, again,
///   does not expand macros. WI-903 made this condition EXACT rather than merely
///   sufficient: the loader now REFUSES a typed bound on the one rule shape the
///   typer expands without passing through [`try_fire`] — a `[simp]` DOT rule
///   ([`super::load::TypedPatternRefusal::DotRule`], keyed on
///   [`is_typer_fired_dot_rule`], since `try_fire_dot_rule` does not consult the
///   bounds either). So every bound-carrying rule that can exist is one the typer
///   does not fire, and reading `None` here is right for all of them.
/// - NO named arguments on the RHS head, mirroring [`try_expand_macro`]'s own
///   positional-only surface: a macro spelled `m(x: ?x)` declines and its template
///   is kept. (That residual is separately refused today — the pattern var arrives
///   as its VALUE type against an occurrence parameter — but the exemption should
///   not be leaning on a downstream check for its narrowness.)
pub(super) fn macro_expanded_rhs_head(kb: &KnowledgeBase, rid: RuleId) -> Option<Symbol> {
    if !is_simp_equation(kb, rid) || !kb.rule_type_bounds(rid).is_empty() {
        return None;
    }
    let head = kb.fact_head_term(rid)?;
    let rhs = match kb.get_term(head) {
        Term::Fn { pos_args, .. } if pos_args.len() == 2 => pos_args[1],
        _ => return None,
    };
    match kb.get_term(rhs) {
        Term::Fn {
            functor,
            named_args,
            ..
        } if named_args.is_empty() => Some(*functor).filter(|f| super::typing::is_macro(kb, *f)),
        // WI-20260902-CZJ2N: a NULLARY macro RHS (`rule f(?x) <=> m() [simp]`) is
        // stored bare. Without this arm the WI-757 exemption never fired and an
        // effectful nullary macro in a `[simp]` RHS was REFUSED at load with the wrong
        // error — while `subst_visit`'s sibling arm is what makes it expand at all.
        Term::Ref(s) | Term::Ident(s) => Some(*s).filter(|f| super::typing::is_macro(kb, *f)),
        _ => None,
    }
}

/// The functor of one operand of an equation's stored head (`Fn{eq/unify, [lhs, rhs]}`)
/// — `idx` 0 = LHS, 1 = RHS — read WITHOUT DeBruijn opening. The shared core of
/// [`stored_lhs_functor`] / [`stored_rhs_functor`], which differ only in the operand
/// index. Read carrier-agnostically via `fact_head_term` (WI-663): a value-fact head
/// (never an equation) reads `None` and the caller skips it. A non-binary head or a
/// non-`Fn` operand reads `None`.
fn stored_eq_operand_functor(kb: &KnowledgeBase, rid: RuleId, idx: usize) -> Option<Symbol> {
    let head = kb.fact_head_term(rid)?;
    let operand = match kb.get_term(head) {
        Term::Fn { pos_args, .. } if pos_args.len() == 2 => pos_args[idx],
        _ => return None,
    };
    match kb.get_term(operand) {
        Term::Fn { functor, .. } => Some(*functor),
        // WI-20260902-CZJ2N — A NULLARY LHS IS STORED BARE, so `rule tau() <=> 7 [simp]`
        // has a `Term::Ref` operand, not a `Term::Fn`. Without this arm the pre-filter
        // in `fire_simp_equation` compared `Some(tau)` against `None` and skipped every
        // nullary law: MEASURED, `operation drive(n) = tau()` under `rule tau() <=> 7
        // [simp]` went from 7 to an undischarged residual. It is also what makes the
        // BARE head `rule tau <=> 7 [simp]` fire, which is this ticket's D row — the two
        // spellings are one term, so one arm serves both.
        Term::Ref(s) => Some(*s),
        _ => None,
    }
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
/// error, or the re-entry cap) DECLINES — `Ok(None)`: the template call is kept,
/// and its downstream type-check surfaces the failure loudly at the redex — never
/// a silently-wrong rewrite.
///
/// WI-757: except when the macro used its DIAGNOSTIC channel
/// ([`crate::eval::EvalError::MacroRejected`]) to say the input is definitively
/// wrong AND why. That is `Err(MacroRejection)` — the reason is known here and
/// nowhere downstream, so it is carried out to be reported at the redex instead
/// of being flattened into a decline. Every other `Err` still declines: a
/// `Suspended` flounder is "not yet", and an unrelated evaluator error is not the
/// author's to read.
fn try_expand_macro(
    kb: &mut KnowledgeBase,
    template: &Rc<NodeOccurrence>,
) -> Result<Option<Rc<NodeOccurrence>>, MacroRejection> {
    // Read the head and gate on `is_macro` BEFORE building the argument vector:
    // `try_expand_macro` runs on EVERY fired `[simp]` rewrite, and the gate is false
    // for all but a macro head. The structural conjuncts here are free; `is_macro`
    // itself is NOT — it materializes an `OpInfoRecord` (WI-904 makes it zero-alloc,
    // which is what would make this ordering pay off fully). The
    // head must be a positional `apply` — a macro is called on the matched
    // pattern-var occurrences; named / type args are not part of the Inc-1 surface,
    // so a macro carrying those declines to expand and stays a template.
    let Some(Expr::Apply {
        functor,
        pos_args,
        named_args,
        type_args,
        recv_type,
    }) = template.as_expr()
    else {
        return Ok(None);
    };
    let functor = *functor;
    // WI-20260829-W6JH0: `recv_type` joins the decline set for the reason the comment
    // above gives about named and type args — a form-(3) call is not the Inc-1 surface.
    if !named_args.is_empty()
        || !type_args.is_empty()
        || recv_type.is_some()
        || !super::typing::is_macro(kb, functor)
    {
        return Ok(None);
    }
    // Bind the macro's params to the argument occurrences as `Value::Node` — NOT
    // materialized: the flatten in `bridge_op_to_eval` is deliberately skipped (it
    // would lower a lambda-body argument to `Bottom`), so occurrence structure
    // survives. Run the body through the WI-625 scratch interpreter, which now also
    // carries the occurrence build builtins (`make_apply`, …). `None` = re-entry
    // cap hit (`run_in_bridge_interp` mem::takes the KB and reclaims it).
    let node_args: Vec<Value> = pos_args.iter().map(|o| Value::Node(Rc::clone(o))).collect();
    let Some(outcome) =
        kb.run_in_bridge_interp(|interp| interp.call_op_bridged(functor, &node_args))
    else {
        return Ok(None);
    };
    match outcome {
        // The body returned a spliceable occurrence — the rewrite result.
        //
        // WI-20260820-5R2XT: RE-PARENTED onto the template, so the provenance chain
        // reaches the redex. A macro BUILDS its result and therefore chooses that
        // result's `from` itself — out of the occurrences it was handed, which are the
        // redex's ARGUMENTS. So the chain ended one level below the call: measured on
        // `p.join(q, λ)`, the spliced `join_run` chained to `VarRef(p)` while this
        // `template` chained `conjoin_of` → `join` → `.join`. Splicing them here is
        // macro-agnostic — no macro has to know it should do this, and none can forget.
        //
        // Only a node the macro BUILT is re-parented — one stamped `macro_expand_pass`,
        // which is what `make_apply` and `splice_query_runner` write. Its own `by` is then
        // kept, because only the `from` was ever wrong.
        //
        // The gate is NOT merely "is it `Synthesized`" (the first cut, corrected in
        // review). A macro that hands an argument straight back is returning an occurrence
        // it did not build — and that argument is very often ALREADY `Synthesized`, since
        // the `[simp]` engine rewrites children before parents. Re-parenting it would copy
        // it into a fresh `Rc` that claims to be an expansion of the template CONTAINING
        // it, and would drop `resolved_type_args` / `lowered_receiver` — and `None` there
        // is not "unknown" but "no dot was ever typed here", a distinction those writes are
        // unconditional in order to keep.
        Ok(Value::Node(result)) => {
            let macro_pass = crate::kb::occurrence::macro_expand_pass(kb);
            Ok(Some(match &result.kind {
                NodeKind::Expr {
                    origin: OccurrenceOrigin::Synthesized { by, .. },
                    ..
                } if *by == macro_pass => {
                    // WI-20260903-FCZ3N: the OWNER is the macro result's own — a macro
                    // built this node knowing the declaration it belongs to, and
                    // re-parenting only says what it is an expansion OF.
                    result.reparented_from(Rc::clone(template), macro_pass, result.owner)
                }
                _ => result,
            }))
        }
        // A macro's declared return is `NodeOccurrence`, so a non-`Node` value is a
        // type/evaluator invariant break — loud in debug, decline in release.
        Ok(other) => {
            debug_assert!(
                false,
                "WI-722: macro `{}` returned a non-occurrence value: {other:?}",
                kb.qualified_name_of(functor),
            );
            Ok(None)
        }
        // WI-757: the macro's DIAGNOSTIC channel — it read the occurrences, found
        // them definitively untranslatable, and said why. Carry it out, span and
        // all; a macro that named no span leaves the location to the reporter.
        Err(crate::eval::EvalError::MacroRejected { detail, span }) => Err(MacroRejection {
            macro_name: functor,
            detail,
            span,
        }),
        // WI-757 — the SAME channel, reached from anthill: a macro rejects by
        // RAISING (proposal 043.1 §3.6). A macro's declared row is capped at `Error`
        // (`check_macro_purity`) and its call is evaluated away at compile time, so
        // this `Error` is a compile-time DIAGNOSTIC and never a runtime effect —
        // which is why the WI-702 rewrite gate exempts a macro at the `[simp]` RHS
        // head. `raise` carries a payload and no occurrence, so the span is the
        // reporter's redex; a narrower one needs a `reject(…, at:)` op (043.1 §7).
        Err(crate::eval::EvalError::Raised { payload }) => Err(MacroRejection {
            macro_name: functor,
            detail: crate::eval::render_raised_payload(kb, &payload),
            span: None,
        }),
        // Any OTHER failure to produce an occurrence declines: the template call is
        // kept, and its downstream type-check surfaces the failure loudly at the
        // redex. A `Suspended` flounder / runtime-domain error residualizes quietly;
        // an `Internal` evaluator bug is asserted loudly, mirroring `bridge_op_to_eval`.
        Err(e) => {
            debug_assert!(
                !matches!(e, crate::eval::EvalError::Internal(_)),
                "WI-722: internal evaluator error expanding macro `{}`: {e}",
                kb.qualified_name_of(functor),
            );
            Ok(None)
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
    stored_eq_operand_functor(kb, rid, 0)
}

/// The reflect `Expr.dot_apply` ENTITY symbol — the LHS head a WI-279 INC2 DOT
/// rule (`rule dr: dot_apply(?e, m, ?x) <=> rhs [simp]`) loads as. The one owner of
/// the qualified name *for rule-shape tests*, so the site that FIRES dot rules
/// (`typing::try_fire_dot_rule`) and the site that REFUSES a typed pattern bound on
/// one (WI-903, `load::load_rule`) cannot drift apart on what a dot rule IS. S66VH
/// routes this and the declarative reflect tables (`ExprBuilderSyms`, `term_view`'s
/// field map, `eval`'s `ReflectSymbols`) through [`dt`], the address owner — so this
/// no longer owns a string anyone else spells. NOT EVERY consumer: the short-name
/// `match` ARMS in `node_occurrence` and `resolve::bounded_list_elements` cannot call
/// a function in a pattern and stay hand-written, guarded instead by
/// `node_occurrence::tests::the_hand_written_dispatch_arms_still_key_off_their_addresses`.
///
/// `None` only if the reflect vocabulary is absent. `register_prelude` →
/// `register_stdlib_scopes` DEFINES this symbol (it does not wait for
/// `reflect.anthill` to load), so every KB built the documented way resolves it
/// before any rule loads — the `Option` is the reader's honesty, not a live case.
pub(super) fn dot_apply_head_sym(kb: &KnowledgeBase) -> Option<Symbol> {
    kb.try_resolve_symbol(dt::qualified(dt::DOT_APPLY))
}

/// WI-903 — would the TYPER's dot-rule site FIRE `rid`? Exactly the two conditions
/// `typing::try_fire_dot_rule` applies before it matches: the rule is a `[simp]`
/// EQUATION ([`is_simp_equation`]) and its LHS is the reflect `Expr.dot_apply`
/// entity. That site never consults `rule_type_bounds`, so the loader refuses a
/// typed pattern bound (`?x: T`) on any rule this accepts — read it as "fired where
/// the bound is not enforced".
///
/// The firing site CALLS this rather than re-spelling the conjunction, so the
/// refusal cannot outrun the firing that justifies it (the discipline
/// [`macro_expanded_rhs_head`] follows for the WI-702 gate — and the failure this
/// very function had in WI-902, when an inlined third copy of [`is_simp_equation`]
/// scanned the `eq` bucket alone). `dot_apply` is [`dot_apply_head_sym`]'s result,
/// passed IN so the per-`DotApply` firing loop keeps hoisting that one string
/// lookup out; [`is_typer_fired_dot_rule`] is the self-contained form for the cold
/// loader path.
///
/// Deliberately shape-only — no `rule_type_bounds` test. Adding one would make the
/// loader's gate circular (a refused rule would read as "not typer-fired", hence
/// not refused).
pub(super) fn fires_as_dot_rule(kb: &KnowledgeBase, rid: RuleId, dot_apply: Symbol) -> bool {
    is_simp_equation(kb, rid) && stored_lhs_functor(kb, rid) == Some(dot_apply)
}

/// [`fires_as_dot_rule`] resolving the symbol itself — for a caller that tests one
/// rule rather than looping (the loader's WI-903 refusal).
///
/// `[simp]`-only, exactly as [`is_simp_equation`] is — but read the reason
/// precisely, because the obvious one is WRONG: the resolver fires `[simp]`
/// equations TOO (`fire_simp_equation` gates on `is_directional_equation`, which
/// accepts `[simp]` OR `[unfold]`) and enforces the bound there. What singles
/// `[simp]` out is that it ALSO has a firing site that IGNORES the bound, so the
/// bound cannot be relied on; nothing in the typer selects `[unfold]`, so refusing
/// that would refuse a shape this refusal has no evidence against.
///
/// Two residuals, both WI-906, both code-read rather than driven: whether a
/// `dot_apply` TERM redex ever reaches the resolver at all is UNMEASURED (if it
/// does not, the `[unfold]` carve-out is unjustified and both should be refused);
/// and this is NOT narrowed by the typer's per-receiver enclosing-SORT guard, which
/// a rule alone cannot decide — so a `dot_apply` `[simp]` rule whose `rule_domain`
/// no receiver can conform to is refused although only the resolver could fire it.
pub(super) fn is_typer_fired_dot_rule(kb: &KnowledgeBase, rid: RuleId) -> bool {
    dot_apply_head_sym(kb).is_some_and(|dot| fires_as_dot_rule(kb, rid, dot))
}

/// Open an equation's DeBruijn vars to fresh globals and return its
/// `(lhs, rhs, fresh)` — the matchable/buildable LHS/RHS terms plus THE RULE'S OWN
/// FRAME: the fresh globals the DeBruijn slots opened to, or (WI-20260903-2M5XR, for a
/// legacy arity-0 Global head, which has no slots to open) the Globals its head already
/// carries. One question, two representations — see the `else` arm for why answering
/// `Vec::new()` for the second let a malformed `fact` equation load clean.
///
/// Uses the KB's `term_from_debruijn` (the same opener `with_fresh_vars`
/// uses) — not a reimplementation of the resolver's rule-opening. The `fresh`
/// set lets the resolver's `fire_simp_equation` (WI-641 Phase 2) key typed-
/// pattern bounds by the opened globals and share this ONE opener rather than
/// re-inlining it. `pub(super)`: the typer's dot-rule firing (WI-279 INC2) opens a
/// matched `[simp]` dot rule and ignores `fresh` — soundly, since WI-903: a dot
/// rule THAT SITE fires can carry no typed-pattern bounds (the loader refuses
/// them, [`is_typer_fired_dot_rule`]), so there is nothing for the opened globals
/// to key.
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
        // WI-20260903-2M5XR — A LEGACY ARITY-0 GLOBAL HEAD HAS A FRAME TOO, and this
        // answered `Vec::new()` as though it did not. Such a head carries its clause's
        // variables as `Var::Global` rather than DeBruijn slots (`load_fact` asserts
        // through `assert_fact`, which leaves `arity`/`globals` at their ground-fact
        // defaults, where `load_rule` goes through `assert_rule_debruijn_with_nodes`),
        // so there is nothing to OPEN — but the set of variables the rule owns is
        // exactly the Globals its head carries, and that is what every reader of
        // `fresh` is asking for. `match_view_oneway` already binds precisely this set
        // ("the opened `fresh` globals for a DeBruijn rule, or the head's own `Global`
        // vars for a legacy arity-0 head" — `resolve.rs`); returning it here makes the
        // two agree by construction instead of by convention, which they did not:
        // `fact fu(?x) <=> sink(?y) [simp]` loaded clean while the `rule` spelling of
        // the same equation was refused.
        // NOT A SLOT VECTOR — and the two readers that INDEX `fresh` positionally must
        // therefore never see this one. `open_debruijn_node` does `fresh.get(idx)` for a
        // `Var::DeBruijn(idx)`, and `typed_pattern_bounds_hold` the same for a bound's
        // slot; `collect_vars` returns term-walk order, which is not slot order. Both are
        // unreachable here — an arity-0 rule's stored `rhs_node` is closed against an
        // EMPTY `globals`, so it holds no `DeBruijn` leaf for the first to find, and
        // `install_rule_type_bounds` runs only from `load_rule` (a typed pattern on a
        // `fact` head is refused at load, WI-582). But the FAILURE MODE changed when this
        // stopped being empty: an out-of-range `get` used to answer `None` and both
        // readers took their safe path, where an in-range one now answers an ARBITRARY
        // variable. The bounds half is asserted rather than argued; the node half has no
        // cheap assertion and is driven instead, by
        // `wi_2m5xr_fact_spelling_frame_test::a_well_formed_equation_still_fires`.
        debug_assert!(
            kb.rule_type_bounds(rid).is_empty(),
            "an arity-0 equation carries typed-pattern bounds, which would index this \
             frame by SLOT — but it is a term-walk-ordered SET (WI-20260903-2M5XR)"
        );
        (head, kb.collect_vars(head))
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
///
/// PRIVATE (WI-902): reach it through [`instantiate_rhs`] (expands a macro RHS) or
/// [`instantiate_rhs_verbatim`] (does not), so a firing site states which it means.
///
/// WI-20260903-FCZ3N — AND IT IS NO LONGER THE ONLY BUILDER. Every node it makes is a
/// SYNTHESIS: `dot_chain` clear, the redex's span. That is right for a node no author
/// wrote, and wrong for the RHS of a rule that HAS source text — so
/// [`build_rhs_template`] routes such a rule to [`reparent_spliced`] +
/// `node_occurrence::substitute_occurrence` instead, and leaves this one ONE job: a rule
/// with no written RHS at all.
fn substitute_to_occurrence(
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
            SubstOp::BuildApply {
                functor,
                pos_count,
                named_keys,
            } => {
                // Children are on top of `results` in source order
                // (pos then named); peel them back off.
                let total = pos_count + named_keys.len();
                let start = results.len() - total;
                let mut children = results.split_off(start).into_iter();
                let pos_args: Vec<_> = (&mut children).take(pos_count).collect();
                let named_args: Vec<_> = named_keys.into_iter().zip(children).collect();
                let expr = Expr::Apply {
                    recv_type: None,
                    functor,
                    pos_args,
                    named_args,
                    type_args: Vec::new(),
                };
                results.push(NodeOccurrence::synthesized_expr(
                    expr,
                    Rc::clone(from),
                    pass,
                    from.owner,
                ));
            }
        }
    }
    debug_assert_eq!(
        results.len(),
        1,
        "substitute_to_occurrence: expected one result"
    );
    results.pop().expect("RHS produced no NodeOccurrence")
}

/// Work-stack item for the iterative [`substitute_to_occurrence`]. `Visit`
/// resolves a RHS term via `walk_view`; an `Apply` defers reconstruction to a
/// `BuildApply` once its children land on `results`.
enum SubstOp {
    Visit(TermId),
    BuildApply {
        functor: Symbol,
        pos_count: usize,
        named_keys: Vec<Symbol>,
    },
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
    let synth =
        |expr: Expr| NodeOccurrence::synthesized_expr(expr, Rc::clone(from), pass, from.owner);
    match kb.walk_view(term, subst) {
        // Reused matched child — keep its identity (and provenance).
        Value::Node(occ) => results.push(occ),
        Value::Term { id: t, .. } => match kb.get_term(t) {
            Term::Fn {
                functor,
                pos_args,
                named_args,
            } => {
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
            // WI-20260902-CZJ2N — A NULLARY OPERATION'S BARE NAME IS ITS CALL, and
            // this arm has to say so because the shape no longer can: a nullary call
            // used to arrive as `Fn{f, [], []}` and take the `Apply` arm above, and it
            // is a `Term::Ref` now. Left as a plain `Expr::Ref`, a nullary macro in a
            // `[simp]` RHS stopped expanding (`try_expand_macro` matches `Expr::Apply`)
            // and a nullary op call in one stopped being a redex.
            //
            // A bare CONSTRUCTOR or SORT keeps `Expr::Ref` — `is_nullary_operation`
            // reads the DECLARATION, which is the only thing left that separates the
            // two readings.
            Term::Ref(s) if super::op_info::is_nullary_operation(kb, *s) => {
                work.push(SubstOp::BuildApply {
                    functor: *s,
                    pos_count: 0,
                    named_keys: Vec::new(),
                });
            }
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
        ChildCursor {
            new,
            idx: 0,
            changed: false,
        }
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
        Expr::Apply {
            functor,
            pos_args,
            named_args,
            type_args,
            recv_type,
        } => Expr::Apply {
            recv_type: recv_type.clone(),
            functor: *functor,
            pos_args: cur.take_vec(pos_args),
            named_args: cur.take_named(named_args),
            type_args: type_args.clone(),
        },
        Expr::Constructor {
            name,
            pos_args,
            named_args,
            from_projection,
        } => Expr::Constructor {
            name: *name,
            pos_args: cur.take_vec(pos_args),
            named_args: cur.take_named(named_args),
            // WI-762: a rewritten CHILD does not stop this node being the tuple a
            // projection desugared into — the receiver moved, the form did not.
            from_projection: *from_projection,
        },
        Expr::Instantiation {
            name,
            pos_args,
            named_args,
        } => Expr::Instantiation {
            name: *name,
            pos_args: cur.take_vec(pos_args),
            named_args: cur.take_named(named_args),
        },
        Expr::HoApply { predicate, args } => Expr::HoApply {
            predicate: cur.take(predicate),
            args: cur.take_vec(args),
        },
        Expr::DotApply {
            receiver,
            name,
            pos_args,
            named_args,
        } => Expr::DotApply {
            receiver: cur.take(receiver),
            name: *name,
            pos_args: cur.take_vec(pos_args),
            named_args: cur.take_named(named_args),
        },
        Expr::If {
            condition,
            then_branch,
            else_branch,
        } => Expr::If {
            condition: cur.take(condition),
            then_branch: cur.take(then_branch),
            else_branch: cur.take(else_branch),
        },
        // WI-819: three children, no annotation slot to carry across — the
        // `: T` rides the PATTERN occurrence, so `cur.take(pattern)` brings it.
        Expr::Let {
            pattern,
            value,
            body,
        } => Expr::Let {
            pattern: cur.take(pattern),
            value: cur.take(value),
            body: cur.take(body),
        },
        Expr::Lambda { param, body } => Expr::Lambda {
            param: cur.take(param),
            body: cur.take(body),
        },
        Expr::Match {
            scrutinee,
            branches,
        } => {
            let scr = cur.take(scrutinee);
            // WI-318: `for_each_child` now visits each branch as
            // pattern, body, guard? — consume in that order.
            let new_branches: Vec<MatchBranch> = branches
                .iter()
                .map(|br| {
                    let pattern = cur.take(&br.pattern);
                    let body = cur.take(&br.body);
                    let guard = br.guard.as_ref().map(|g| cur.take(g));
                    MatchBranch {
                        pattern,
                        guard,
                        body,
                        span: br.span,
                    }
                })
                .collect();
            Expr::Match {
                scrutinee: scr,
                branches: new_branches,
            }
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
        Expr::ApplyWithin {
            functor,
            args,
            named_args,
            requirements,
            type_args,
        } => Expr::ApplyWithin {
            functor: *functor,
            args: cur.take_vec(args),
            named_args: cur.take_named(named_args),
            requirements: cur.take_vec(requirements),
            type_args: type_args.clone(),
        },
        Expr::HoApplyWithin {
            predicate,
            args,
            requirements,
        } => Expr::HoApplyWithin {
            predicate: cur.take(predicate),
            args: cur.take_vec(args),
            requirements: cur.take_vec(requirements),
        },
        Expr::ConstructorWithin {
            name,
            pos_args,
            named_args,
            requirements,
        } => Expr::ConstructorWithin {
            name: *name,
            pos_args: cur.take_vec(pos_args),
            named_args: cur.take_named(named_args),
            requirements: cur.take_vec(requirements),
        },
        Expr::LambdaWithin {
            param,
            body,
            requirements,
        } => Expr::LambdaWithin {
            param: cur.take(param),
            body: cur.take(body),
            requirements: cur.take_vec(requirements),
        },
        Expr::RequirementAtSort { chain, slot } => Expr::RequirementAtSort {
            chain: cur.take(chain),
            slot: *slot,
        },
        Expr::Dictionary { impl_sort, subs } => Expr::Dictionary {
            impl_sort: *impl_sort,
            subs: cur.take_vec(subs),
        },
        // WI-538: an in-body proof — consume children in `for_each_child`
        // order [conclude?, body] so a `[simp]` rewrite (or a WI-408
        // `some(…)` coercion) inside the goal or continuation propagates
        // up instead of being silently dropped.
        Expr::Proof {
            target,
            strategy,
            using,
            conclude,
            body,
        } => Expr::Proof {
            target: *target,
            strategy: *strategy,
            using: using.clone(),
            conclude: conclude.as_ref().map(|c| cur.take(c)),
            body: cur.take(body),
        },
        // Proposal 055 — a type value's type ARGUMENTS are children (`for_each_child`
        // yields them), so it needs an arm of its own. Reaching the leaf catch-all below
        // instead would return the node unchanged and silently keep the OLD arguments
        // whenever a child moved.
        Expr::TypeValue {
            head,
            pos_args,
            named_args,
        } => Expr::TypeValue {
            head: *head,
            pos_args: cur.take_vec(pos_args),
            named_args: cur.take_named(named_args),
        },
        // Genuine leaves (`Var`/`Const`/`Ref`/`Ident`/`Bottom`/`VarRef`) — no
        // children to reassemble.
        _ => return Rc::clone(occ),
    };
    if !cur.changed {
        return Rc::clone(occ);
    }
    // Preserve provenance (`Synthesized { from, by }`) AND the typer's stamps when a
    // child is rewritten under this node — `rebuilt_expr` carries them (WI-502 Step 3
    // for `inferred_type`, WI-1026 for the `CallClass`; the list lives at
    // `NodeOccurrence::carry_typer_stamps_from`, not here, so it cannot be enumerated
    // stale a fourth time). A bare `new_expr` would drop them.
    occ.rebuilt_expr(new_expr)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kb::node_occurrence::{NodeKind, OccurrenceOrigin};
    use crate::kb::term::{Literal, Var};
    use crate::kb::ClauseKind;
    use crate::span::{SourceId, SourceSpan};
    use smallvec::SmallVec;

    /// A KB with the kernel vocabulary registered — the configuration in which
    /// `eq_functor()` / `unify_functor()` answer (WI-969). Tests that build
    /// equations need this; tests below that keep a bare `KnowledgeBase::new()`
    /// are deliberately exercising the prelude-less KB.
    fn kb_with_prelude() -> KnowledgeBase {
        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        kb
    }

    /// Build the `[simp]` equation `eq(add(?x, 0), ?x)` head + `[simp]` meta,
    /// returning `(eq_head, meta, add_sym)` without asserting.
    fn build_add_zero(kb: &mut KnowledgeBase) -> (TermId, TermId, Symbol) {
        let eq_sym = kb.eq_functor();
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
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");
        kb.assert_fact(eq_head, sort, domain, Some(meta));
        add
    }

    /// Assert `add_zero` via the DeBruijn path
    /// (`assert_rule_debruijn_with_nodes`, arity > 0) — the shape real `[simp]`
    /// rules take after loading. Exercises `open_equation`'s
    /// `term_from_debruijn` branch.
    fn assert_add_zero_db(kb: &mut KnowledgeBase) -> Symbol {
        let (eq_head, meta, add) = build_add_zero(kb);
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");
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
        let mut kb = kb_with_prelude();
        let eq = kb.eq_functor();
        let a = kb.intern("a");
        let b = kb.intern("b");
        // `eq(a, b)` shaped, but carried as a `Value::Entity` (a value fact, not a
        // hash-consed `Term`) — the adversarial case the `rule_head` panic guarded.
        let head = Value::Entity {
            functor: eq,
            pos: vec![
                Value::Entity {
                    functor: a,
                    pos: Vec::new().into(),
                    named: Vec::new().into(),
                },
                Value::Entity {
                    functor: b,
                    pos: Vec::new().into(),
                    named: Vec::new().into(),
                },
            ]
            .into(),
            named: Vec::new().into(),
        };
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");
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
        let mut kb = kb_with_prelude();
        let unify = kb.unify_functor(); // the canonical `anthill.kernel.unify` (WI-969)
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
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");
        kb.assert_rule_debruijn_with_nodes(unify_head, vec![], sort, domain, Some(meta));

        assert!(
            has_simp_equations(&mut kb),
            "a <=>-headed [simp] rule must be counted (eq+unify selection)"
        );
    }

    #[test]
    fn guard_free_simp_rule_rewrites_op_body() {
        let mut kb = kb_with_prelude();
        let add = assert_add_zero(&mut kb);

        // op body: add(7, 0)
        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let body = NodeOccurrence::new_expr(
            Expr::Apply {
                recv_type: None,
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

        assert!(run(&mut kb).is_none(), "no macro rejection expected here");

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
        let mut kb = kb_with_prelude();
        let add = assert_add_zero(&mut kb);
        let wrap = kb.intern("wrap");

        // op body: wrap(add(7, 0)) — the redex is nested; the parent `wrap`
        // must be rebuilt with the rewritten child.
        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let inner = NodeOccurrence::new_expr(
            Expr::Apply {
                recv_type: None,
                functor: add,
                pos_args: vec![Rc::clone(&seven), zero_occ],
                named_args: vec![],
                type_args: vec![],
            },
            span(),
            None,
        );
        let body = NodeOccurrence::new_expr(
            Expr::Apply {
                recv_type: None,
                functor: wrap,
                pos_args: vec![inner],
                named_args: vec![],
                type_args: vec![],
            },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, body);

        assert!(run(&mut kb).is_none(), "no macro rejection expected here");

        let rewritten = kb.op_body_node(foo).expect("op body present");
        match rewritten.as_expr() {
            Some(Expr::Apply {
                functor, pos_args, ..
            }) => {
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
        let mut kb = kb_with_prelude();
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
            Expr::Apply {
                recv_type: None,
                functor: add,
                pos_args: vec![Rc::clone(&seven_o), zero_o],
                named_args: vec![],
                type_args: vec![],
            },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, body);
        assert!(run(&mut kb).is_none(), "no macro rejection expected here");

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
        let mut kb = kb_with_prelude();
        let add = assert_add_zero_db(&mut kb);

        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let body = NodeOccurrence::new_expr(
            Expr::Apply {
                recv_type: None,
                functor: add,
                pos_args: vec![Rc::clone(&seven), zero_occ],
                named_args: vec![],
                type_args: vec![],
            },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, body);

        assert!(run(&mut kb).is_none(), "no macro rejection expected here");

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
        let mut kb = kb_with_prelude();
        let add = assert_add_zero(&mut kb);
        let sort = ClauseKind::Fact;
        let domain = kb.intern("test");
        let eq_sym = kb.eq_functor();
        let f = kb.intern("f");
        let g = kb.intern("g");
        let y_sym = kb.intern("y");
        let vy = kb.fresh_var(y_sym);
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));
        let zero = kb.alloc(Term::Const(Literal::Int(0)));
        let add_y0 = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[var_y, zero]),
            named_args: SmallVec::new(),
        });
        let g_add = kb.alloc(Term::Fn {
            functor: g,
            pos_args: SmallVec::from_elem(add_y0, 1),
            named_args: SmallVec::new(),
        });
        let f_y = kb.alloc(Term::Fn {
            functor: f,
            pos_args: SmallVec::from_elem(var_y, 1),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[f_y, g_add]),
            named_args: SmallVec::new(),
        });
        let meta = {
            let simp_sym = kb.intern("simp");
            let meta_sym = kb.intern("meta");
            let tru = kb.alloc(Term::Const(Literal::Bool(true)));
            kb.alloc(Term::Fn {
                functor: meta_sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::from_slice(&[(simp_sym, tru)]),
            })
        };
        kb.assert_fact(eq_head, sort, domain, Some(meta));

        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let body = NodeOccurrence::new_expr(
            Expr::Apply {
                recv_type: None,
                functor: f,
                pos_args: vec![seven],
                named_args: vec![],
                type_args: vec![],
            },
            span(),
            None,
        );
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, body);

        assert!(run(&mut kb).is_none(), "no macro rejection expected here");

        let rewritten = kb.op_body_node(foo).expect("op body present");
        match rewritten.as_expr() {
            Some(Expr::Apply {
                functor, pos_args, ..
            }) => {
                assert_eq!(*functor, g, "f(7) should reduce to g(...)");
                assert!(
                    matches!(pos_args[0].as_expr(), Some(Expr::Const(Literal::Int(7)))),
                    "g's child add(7,0) should have reduced to 7 (fixpoint)"
                );
            }
            other => panic!("expected g(7), got {other:?}"),
        }
        assert!(
            matches!(
                &rewritten.kind,
                NodeKind::Expr {
                    origin: OccurrenceOrigin::Synthesized { .. },
                    ..
                }
            ),
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
        let mut kb = kb_with_prelude();
        let add = assert_add_zero(&mut kb);
        let wrap = kb.intern("wrap");

        const DEPTH: usize = 200_000;
        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span(), None);
        let zero_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span(), None);
        let mut node = NodeOccurrence::new_expr(
            Expr::Apply {
                recv_type: None,
                functor: add,
                pos_args: vec![Rc::clone(&seven), zero_occ],
                named_args: vec![],
                type_args: vec![],
            },
            span(),
            None,
        );
        for _ in 0..DEPTH {
            node = NodeOccurrence::new_expr(
                Expr::Apply {
                    recv_type: None,
                    functor: wrap,
                    pos_args: vec![node],
                    named_args: vec![],
                    type_args: vec![],
                },
                span(),
                None,
            );
        }
        let foo = kb.intern("foo");
        kb.set_op_body_node(foo, node);

        assert!(run(&mut kb).is_none(), "no macro rejection expected here");

        // Walk down the wrap chain and confirm the innermost add(7, 0) → 7.
        let mut cur = Rc::clone(kb.op_body_node(foo).expect("op body present"));
        for _ in 0..DEPTH {
            cur = match cur.as_expr() {
                Some(Expr::Apply {
                    functor, pos_args, ..
                }) if *functor == wrap => Rc::clone(&pos_args[0]),
                other => panic!("expected wrap(...), got {other:?}"),
            };
        }
        assert!(
            matches!(cur.as_expr(), Some(Expr::Const(Literal::Int(7)))),
            "innermost add(7, 0) should have rewritten to 7, got {:?}",
            cur.as_expr()
        );
        assert!(
            Rc::ptr_eq(&cur, &seven),
            "innermost redex should reuse the matched `7`"
        );
    }
}

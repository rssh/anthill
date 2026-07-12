/// SLD resolution + equational simplification.
///
/// Two behavioral modes, both backed by the same KB:
/// - **Derivation rule** (body non-empty): backward-chaining SLD resolution
/// - **Equation** (head is `eq(lhs, rhs)`, body empty): rewrite `lhs` → `rhs`
///
/// Ground facts (head not `eq(...)`, body empty) are matched directly during
/// resolution as base cases.
///
/// Goals are always maximally concrete (no unresolved var chains). The answer
/// substitution is always flat (path-compressed on merge) — no `walk` needed.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use smallvec::SmallVec;

use super::subst::{Constraint, Substitution};
use super::node_occurrence::{
    self, EffectExprNode, Expr, NodeOccurrence, TypeChild, TypeNode,
};
use super::term::{Literal, Term, TermId, Var, VarId};
use super::term_view::{goal_fingerprint, GoalKey, ReflectedExpr, ReflectSyms, TermIdView, TermView, ViewHead, ViewItem};
use super::persist_subst::BindValue;
use super::discrim::SubstTree;
use crate::intern::Symbol;
use crate::eval::value::Value;
use crate::eval::{EvalConfig, EvalError, Interpreter};
use super::RuleId;
use super::KnowledgeBase;

/// WI-625 gap 1: max eval↔SLD bridge crossings before
/// [`KnowledgeBase::bridge_op_to_eval`] residualizes instead of recursing
/// further. Each crossing (bridge → eval → `prove_rule_predicate` → resolve →
/// bridge) nests ordinary Rust frames, so an unbounded non-decreasing mutual
/// recursion would overflow the native stack; this bounds it to a delay.
/// Legitimate cross-bridge nesting is shallow (a bridged compare whose element
/// compare bridges again), so this is generous headroom.
const BRIDGE_REENTRY_CAP: usize = 32;

thread_local! {
    /// Current eval↔SLD bridge nesting depth on this thread (resolution and its
    /// bridged evals run single-threaded). A thread-local — NOT a KB field — so
    /// it survives `bridge_op_to_eval`'s `mem::take` of the KB and is shared by
    /// every re-entrant bridge on the thread regardless of which KB instance runs.
    static BRIDGE_REENTRY_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// WI-500: how a constructor's POSITIONAL args map onto its declared field
/// NAMES — the loader's "rank-among-not-named" rule, factored out so the runtime
/// value→term lowering (`alloc_from_value`, `value_to_term`) canonicalizes to the
/// SAME named shape the loader produces for source terms (`convert_term_with_expected`).
/// That one shape is what the discrim tree / hash-cons store keys on; without it a
/// runtime-built positional entity persisted (`alloc_from_value` → `assert_fact`)
/// is stored positionally and never unifies with the canonical named pattern — the
/// WI-433 never-match bug class on the non-loader path. Computed by
/// [`KnowledgeBase::positional_to_named_plan`].
pub(crate) enum PositionalPlan {
    /// Keep the positional args as-is: there are none, the functor is a
    /// reflect-form meta-ctor (whose positional shape IS the encoding), or it has
    /// no registered fields to map onto (anonymous tuple / ad-hoc structure).
    Skip,
    /// Assign `fields[i]` to the i-th positional arg (`fields.len()` equals the
    /// requested positional count). The fields are the declared fields NOT
    /// already given by name, in declaration order.
    Assign(SmallVec<[Symbol; 4]>),
    /// More positional args than unfilled fields — the loud, never-a-silent-
    /// never-match case. `declared` is the full declared field list (for the
    /// error message); `unfilled` is how many fields were actually open.
    OverArity { declared: SmallVec<[Symbol; 4]>, unfilled: usize },
}

/// Capture a `TermView`'s top-level carrier as an owned `Value` goal (WI-349) —
/// `Value::Term` for a hash-consed pattern, the cloned `Value`/`Value::Node` for
/// a value/occurrence goal. The owned form the mutable search frame needs.
fn bind_value_to_value(bv: BindValue) -> Value {
    match bv {
        BindValue::Term(t) => Value::term(t),
        BindValue::Value(v) => v,
        // `Path` is the discrim tree's deferred fact-leaf extraction; a goal's
        // own `as_bind_value` (TermId / Value / occurrence carriers) never
        // yields it, so reaching it here is a broken invariant, not a fallback.
        BindValue::Path(_) => unreachable!(
            "bind_value_to_value: a goal view produced BindValue::Path (WI-349)",
        ),
    }
}

// ── Builtin tags ───────────────────────────────────────────────

/// Tag identifying a builtin operation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum BuiltinTag {
    /// `anthill.reflect.nonvar(?x)` — succeeds if `?x` is bound to a non-variable.
    NonVar,
    /// `anthill.reflect.ground(?x)` — succeeds if `?x` is fully ground (no variables).
    Ground,
    /// `anthill.reflect.qualified_name(?sym, ?result)` — Symbol → full qualified name string.
    QualifiedName,
    /// `anthill.reflect.short_name(?sym, ?result)` — Symbol → last segment string.
    ShortName,
    /// `anthill.reflect.lookup_symbol(?name_str, ?result)` — String → Symbol (fails if not found).
    LookupSymbol,
    /// `anthill.reflect.typing.is_entity_of(?sub, ?sup)` — succeeds if sub is entity of sup.
    IsEntityOf,
    /// `anthill.reflect.typing.extract_sort_ref(?inst, ?result)` — extract
    /// functor as a nullary Fn (canonical sort-name shape) from
    /// instantiation term.
    ExtractSort,
    /// `anthill.reflect.not(goal)` — negation-as-failure.
    Not,
    /// `anthill.reflect.resolve_sort_instantiation_param(?spec_inst, ?param_name, ?value)` —
    /// extract a named arg value from a ParameterizedType term by parameter name.
    ResolveSortInstParam,
    /// `anthill.reflect.scope(?sym, ?result)` — Symbol → enclosing scope symbol.
    Scope,
    /// `anthill.reflect.kind(?sym, ?result)` — Symbol → kind string.
    Kind,
    /// `anthill.reflect.feed.provenance(?place, ?result)` — place Symbol →
    /// `Provenance`, a function of the symbol's kind (WI-352): `Param`→`input`,
    /// `OpResult`→`op_result`, `CallbackResult`→`fresh_output`,
    /// `LocalLet`→`local`; anything else (incl. `CallbackParam`) fails.
    Provenance,
    /// `anthill.reflect.field_access(?object, ?field, ?result)` — dot projection.
    FieldAccess,
    /// `anthill.reflect.Expr.ho_apply(?P, args...)` — higher-order predicate application.
    HoApply,
    /// `anthill.kernel.push_choice(?a, ?b)` — binary choice point.
    /// Special-cased in `step_init`; see proposal 033 / WI-075.
    PushChoice,
    /// `anthill.kernel.cut` — cut control primitive (`!`). Surface form is the
    /// nullary `cut`; the resolver opens it to a barrier-tagged `cut(B)` when the
    /// enclosing rule body is entered. Special-cased in `step_init`: its effect
    /// is on the choice-point stack (it prunes back to the barrier), not on σ —
    /// like Not / HoApply / PushChoice. Proposal 033.1 / WI-568.
    Cut,
    // ── Arithmetic and comparison builtins ───────────────────
    /// `anthill.kernel.struct_eq(?a, ?b)` (`===`) — structural equality
    /// (succeeds/fails). Total, carrier-agnostic, never dispatches (WI-615 /
    /// proposal 051). Until WI-616 this tag also backed `PartialEq.eq`; structural
    /// inequality is `not(a === b)`.
    Eq,
    /// `anthill.prelude.PartialEq.eq(?a, ?b)` — SEMANTIC equality (WI-616 / proposal
    /// 051 Phase 2): the `PartialEq.eq` spec op, dispatched through the carrier's
    /// `Eq` instance. See [`KnowledgeBase::sem_eq_core`] for the full
    /// reflexivity / dispatch / buried-override / structural cascade.
    SemEq,
    /// `anthill.prelude.PartialEq.neq(?a, ?b)` — semantic inequality
    /// (`neq(a,b) <=> not(eq(a,b))`): [`KnowledgeBase::sem_eq_core`] with the
    /// verdict inverted.
    SemNeq,
    /// `anthill.kernel.unify(?a, ?b)` — structural unification (proposal 049).
    /// The bind-counterpart of `Eq`: same structural walk, but a flex var head
    /// **binds** to the other side (an occurs-checked frame effect →
    /// `SuccessWithBindings`) instead of merely comparing. The object-level face
    /// of `<=>` (and `let ?v = e`). Carrier-agnostic, never dispatches.
    Unify,
    /// `anthill.prelude.Ordered.gt(?a, ?b)` — greater-than on Int/Float constants.
    Gt,
    /// `anthill.prelude.Ordered.lt(?a, ?b)` — less-than on Int/Float constants.
    Lt,
    /// `anthill.prelude.Ordered.gte(?a, ?b)` — greater-or-equal on Int/Float constants.
    Gte,
    /// `anthill.prelude.Ordered.lte(?a, ?b)` — less-or-equal on Int/Float constants.
    Lte,
    /// `anthill.prelude.Numeric.add(?a, ?b)` — arithmetic addition (equation builtin).
    Add,
    /// `anthill.prelude.Numeric.sub(?a, ?b)` — arithmetic subtraction (equation builtin).
    Sub,
    /// `anthill.prelude.Numeric.mul(?a, ?b)` — arithmetic multiplication (equation builtin).
    Mul,
    // ── Conversion builtins ─────────────────────────────────
    /// `anthill.prelude.BigInt.to_bigint(?n, ?result)` — Int → BigInt.
    ToBigInt,
    /// `anthill.prelude.BigInt.to_int(?n, ?result)` — BigInt → Option[Int].
    ToInt,
    // ── Occurrence builtins (stubs) ──────────────────────────
    /// `anthill.reflect.occurrence_term(occ)` → Term
    OccurrenceTerm,
    /// `anthill.reflect.occurrence_span(occ)` → SourceSpan
    OccurrenceSpan,
    /// `anthill.reflect.occurrence_owner(occ)` → Symbol
    OccurrenceOwner,
    /// `anthill.reflect.sub_occurrences(occ)` → List[Occurrence]
    SubOccurrences,
    /// anthill.reflect.operation_body(op) -> Option[NodeOccurrence]
    OperationBody,
    /// WI-300 — `anthill.kernel.find_dictionary(spec_ref, grounding_var…)`: the
    /// rule-body requirement guard, the desugared form of a rule-body `requires(X)`
    /// (converter) after the typer sweep records which rule var grounds each of
    /// spec `X`'s type-parameters. Succeeds iff every grounding var's carried type
    /// makes `X` resolve (a `provides` provider exists) at the current binding;
    /// fails if a ground carrier has no provider; SUSPENDS as residual (Delay) when
    /// a carrier type is under-determined (never NAF-decide; WI-519 / WI-067).
    FindDictionary,
}

/// Result of executing a builtin.
enum BuiltinResult {
    /// Builtin succeeded; continue with current substitution unchanged.
    Success,
    /// Builtin succeeded and produced new variable bindings to merge.
    SuccessWithBindings(Substitution),
    /// Builtin cannot evaluate yet; delay this goal. WI-628 — `truncated` marks a
    /// delay whose undecidedness came from a depth-TRUNCATED sub-search (a carrier
    /// `eq`/`neq` closed sub-proof that hit `sem_eq_sub_depth`, or the eval
    /// bridge's re-entry cap), as opposed to an ordinary flex-var flounder
    /// (`truncated: false`, the common case — see [`BuiltinResult::delay`]). The
    /// step loop folds a truncated delay onto the outer [`SearchStream::truncated`]
    /// flag so an eager NAF/guard consumer (which reads an empty result as
    /// refutation) sees the incomplete search instead of silently deciding. A
    /// FIELD, not a separate variant: every `match` arm must bind it and every
    /// producer must choose it, so no consumer can forget the truncated case —
    /// the exact "forgot the check" bug class WI-628 fights.
    Delay { truncated: bool },
    /// Builtin definitively failed (e.g. lookup_symbol for non-existent name).
    Failure,
}

impl BuiltinResult {
    /// An ordinary flex-var flounder-delay (operand still unbound) — NOT from a
    /// truncated search. The common `Delay` producer; the ONLY truncated producer
    /// is the carrier-`eq` path ([`KnowledgeBase::sem_eq_dispatch`]).
    const fn delay() -> Self {
        BuiltinResult::Delay { truncated: false }
    }
}

/// WI-616 — map an "equal?" answer to the requested verdict: `positive` is
/// `true` for `eq` (equal ⇒ Success) and `false` for `neq` (equal ⇒ Failure).
fn sem_verdict(equal: bool, positive: bool) -> BuiltinResult {
    if equal == positive { BuiltinResult::Success } else { BuiltinResult::Failure }
}

/// WI-625 — the three-way outcome of proving a rule-backed predicate goal by a
/// bounded closed sub-resolution ([`KnowledgeBase::prove_rule_predicate`]).
/// Shared by the resolver's semantic-`eq` dispatch (`sem_eq_dispatch`) and the
/// eval→SLD bridge (`eval/builtins.rs`, `eval/eval.rs`), so both read a
/// carrier's own `eq`/`neq`/`subset`/… the identical way.
#[derive(Debug)]
pub(crate) enum PredicateProof {
    /// A definite proof was found (semi-deterministic: the first one settles it).
    Proved,
    /// The search ran to exhaustion, complete, with no proof.
    Refuted,
    /// No definite proof, and the search was incomplete — never decide from it.
    /// WI-628: `truncated` distinguishes the two incompleteness sources, because
    /// the resolver-side consumer ([`KnowledgeBase::sem_eq_dispatch`]) must
    /// PROPAGATE genuine truncation to the outer stream but NOT a mere flounder:
    /// * `truncated: true`  — a branch was abandoned at the depth cap
    ///   (`SEM_EQ_SUB_DEPTH`); the outer NAF/guard consumer must see it.
    /// * `truncated: false` — only residual (floundered) solutions over an
    ///   otherwise COMPLETE search (WI-519 "no definite solution"): undecided, but
    ///   there is no truncation to surface.
    Undecided { truncated: bool },
}

/// WI-628 — the outcome of the SLD→eval `eq`/`neq` bridge
/// ([`KnowledgeBase::bridge_eq_op_to_eval`]) for a BODIED instance-fact eq op: a
/// decided `Bool`, or UNDECIDED with whether the undecidedness came from a
/// RESOURCE CUT (the bridge re-entry cap — the eval analog of a depth-truncated
/// search, which an eager NAF/guard consumer must see) versus a clean bridge-mode
/// SUSPEND (a floundered nested compare — WI-519 undecided but complete).
pub(crate) enum BridgeEqOutcome {
    /// The op ran to a definite `Bool` verdict.
    Decided(bool),
    /// The op could not be decided; `truncated` mirrors [`PredicateProof`]'s.
    Undecided { truncated: bool },
}

/// A resolution candidate — either a regular KB rule/fact or a
/// scoped assumption. WI-251: the legacy `Occurrence(OccurrenceId, …)`
/// variant was removed when the legacy occurrence side-table went; reflection
/// queries now read `kb.op_bodies` (NodeOccurrence trees) directly.
#[derive(Clone)]
enum Candidate {
    /// Regular KB rule or fact.
    Rule(RuleId, Substitution),
    /// Frame-scoped assumed fact (introduced by `forall_impl` discharge —
    /// WI-108). Behaves as a zero-body rule.
    Assumption(Substitution),
    /// Inline goal-list continuation — body-only, no rule head, no
    /// fresh-var renaming. The synthesized goals are prepended before
    /// `frame.goals[1..]` and the parent frame's σ is inherited
    /// unchanged (no head match contributes bindings).
    ///
    /// Introduced by proposal 033 / WI-075 to back `push_choice(?a, ?b)`:
    /// the two branches of a binary choice are emitted as two
    /// `Continuation` candidates that share the frame's tail.
    ///
    /// The goals are carrier-neutral `Value`s (WI-668), not transit-interned
    /// `TermId`s: producers that start from terms (push_choice, branch-from-
    /// streams) wrap with `Value::term`, while the WI-580 body-unfold emits its
    /// op-call goals as `Value::Node` occurrences so the re-triggered operand is
    /// recognized without a `term_body_to_nodes` round-trip at re-entry
    /// (proposal 033 §"TermId / Value asymmetry").
    Continuation(Vec<Value>),
    /// Row from a registered external-source backend (proposal 007 §11 +
    /// 026.1 Q4 Stage B). The substitution unifies the goal pattern with
    /// the row's `Value::Entity`, with bindings entering σ as the row's
    /// raw `Value` shape (no `TermStore` allocation per row). Behaviorally
    /// identical to `Assumption`: zero body, just bindings to merge.
    ExternalRow(Substitution),
}

/// Result of a recursive groundness check.
enum GroundCheck {
    Ground,
    HasVar,
}

// ── Configuration ───────────────────────────────────────────────

/// Configuration for SLD resolution.
pub struct ResolveConfig {
    /// Maximum resolution depth (default 100).
    pub max_depth: usize,
    /// Maximum number of solutions to collect (0 = unlimited).
    pub max_solutions: usize,
    /// Whether to apply equational rewriting as fallback during resolution.
    pub simplify: bool,
    /// WI-519 (residual honesty): when `true`, a FLOUNDERED solution (one with
    /// a non-empty `residual` — an undischarged goal the search couldn't decide)
    /// is NOT yielded; the search skips it and continues. So such a result never
    /// counts toward `max_solutions` and never masquerades as a definite answer.
    /// Decision boundaries that ask "is there a (definite) solution?" — the
    /// prover, constraint guards — set this; the cap then counts only definite
    /// solutions. Default `false`: residual solutions ARE returned, for
    /// residual-honest consumers that inspect [`Solution::is_definite`] (and the
    /// resolver tests that pin the residual mechanism).
    pub definite_only: bool,
    /// Proposal 050 (WI-537) — the local-interpretation context Γ: a
    /// discrimination-tree overlay of facts the typer narrowed at a program
    /// point, consulted at the candidate step (`step_init`) exactly like the
    /// frame's `assumed_facts` so the SLD search resolves over **KB ∪ Γ** with
    /// no duplicated logic. `None` for every ordinary resolution (the typer's
    /// `prove_from_gamma` bridge is the only seeder). Global to one resolve
    /// call (every frame sees the same Γ), so it rides the config, not the
    /// per-frame `assumed_facts` stack. Only the in-crate `prove_from_gamma`
    /// bridge ever seeds it; external callers leave it `None` via
    /// `..ResolveConfig::default()`. `pub` (not `pub(crate)`) so `ResolveConfig`
    /// stays externally constructable; the carrier `SubstTree` is `pub(crate)`,
    /// hence the `allow` — the field is an internal channel, not public surface.
    #[allow(private_interfaces)]
    pub gamma: Option<Rc<SubstTree<Value>>>,
}

impl Default for ResolveConfig {
    fn default() -> Self {
        Self {
            max_depth: 100,
            max_solutions: 0,
            simplify: false,
            definite_only: false,
            gamma: None,
        }
    }
}

// ── Solution ────────────────────────────────────────────────────

/// A successful resolution result: variable bindings collected during proof.
///
/// The substitution is always flat (path-compressed) — read a binding via
/// `subst.resolve_as_value(vid)` directly, no `walk` needed.
///
/// `residual` holds the delayed goals that could not be resolved (e.g., a
/// `nonvar(?x)` where `?x` was never bound by any other goal), carried
/// carrier-agnostically as `Value` (WI-348): a delayed goal mentioning a
/// `Value::Node` keeps it, instead of materializing to a hash-consed `TermId`
/// via `reify_goal_value` (lossy for an occurrence's identity/span).
pub struct Solution {
    pub subst: Substitution,
    pub residual: Vec<Value>,
}

impl Solution {
    /// WI-519: a *definite* solution is one with no undischarged goals — an
    /// empty `residual`. A non-empty residual means the search FLOUNDERED (it
    /// delayed a goal whose variables never got bound and gave up), so the
    /// "answer" proves nothing. The codified form of the convention every
    /// honest consumer was hand-rolling as `sol.residual.is_empty()`; a
    /// floundered solution must never be counted as a definite answer.
    pub fn is_definite(&self) -> bool {
        self.residual.is_empty()
    }

    /// WI-502 Step 1 — the residual constraints `C` this answer carries in its
    /// substitution store (M2: an answer generalizes to `(σ, C)`). Delegates to
    /// [`Substitution::residual_constraints`]. Distinct from [`Self::residual`],
    /// which holds delayed *goals* (NAF/flounder); `C` is the var-keyed
    /// constraint store (`lacks` kind #1 / type kind #2). Write-mostly — no
    /// consumer reads it yet (`docs/design/constrained-term-substrate.md`).
    pub fn residual_constraints(&self) -> Vec<(VarId, Constraint)> {
        self.subst.residual_constraints()
    }
}

// ── EqChange ────────────────────────────────────────────────────

/// Record of an equational rewrite step, carrier-faithful (WI-348): `original`
/// is the redex as it arrived — a `Value::Term` or a `Value::Node` occurrence,
/// whichever carrier `apply_eq_rules` was walking — and `rewritten` is the RHS
/// built in that same carrier. (Consumed only by tests today; `#[allow(dead_code)]`.)
#[allow(dead_code)]
pub struct EqChange {
    pub rule_id: RuleId,
    pub original: Value,
    pub rewritten: Value,
}

// ── SearchStream (lazy resolution) ──────────────────────────────

/// How the current frame handles delayed goals.
#[derive(Clone, Debug)]
enum DelayMode {
    /// Normal resolution — no delayed goals seen yet.
    Normal,
    /// At least one goal has delayed; track consecutive delays.
    Delayed { consecutive_delays: usize },
}

impl DelayMode {
    /// Reset the consecutive delay counter (Normal stays Normal).
    fn reset(&self) -> DelayMode {
        match self {
            DelayMode::Normal => DelayMode::Normal,
            DelayMode::Delayed { .. } => DelayMode::Delayed { consecutive_delays: 0 },
        }
    }
}

/// What phase of processing a frame is in.
#[derive(Clone)]
enum FrameState {
    /// First visit: classify goals[0] (builtin? non-builtin? empty?).
    Init { delay_mode: DelayMode },

    /// Iterating over candidate rules/facts for a non-builtin goal.
    ChoicePoint {
        delay_mode: DelayMode,
        // WI-246: a `Value` so an occurrence goal can be re-pushed on the
        // delay-fallback path and reified for dedup.
        original_goal: Value,
        candidates: Vec<Candidate>,
        next: usize,
        any_delayed: bool,
        child_solutions: usize,
        /// Cut barrier (proposal 033.1 / WI-568). Set to `Some(B)` when this
        /// choice point selected a rule whose body contains a `!`: it is the
        /// frame the cut commits to. `cut(B)` (baked into that body) prunes this
        /// frame's remaining candidates and every choice point stacked above it.
        /// Allocated fresh per rule-body open and unique across the search, so
        /// the cut goal finds exactly its own call frame. `None` for choice
        /// points that opened no cut-bearing body (the overwhelming majority).
        cut_barrier: Option<i64>,
        /// Seen ground goals, keyed by carrier-agnostic structural fingerprint
        /// (WI-348): `goal_fingerprint` walks the goal's `TermView` through σ to
        /// a kb-free `GoalKey`, so a `Value::Node`-carrying answer keys by its
        /// structure (no `TermId` materialization, no drop).
        seen_goals: HashSet<GoalKey>,
    },
}

/// A choice point on the explicit stack.
#[derive(Clone)]
struct Frame {
    // WI-246: goals carry `Value` so rule-body occurrences flow into SLD as
    // `Value::Node` without lowering to hash-consed Term. During the
    // behavior-preserving carrier swap every goal is still `Value::Term`.
    goals: Vec<Value>,
    subst: Substitution,
    depth: usize,
    state: FrameState,
    /// Antecedents assumed under a `forall_impl` discharge that landed in
    /// this frame's goal stream. Consulted as zero-body facts during the
    /// proof of the consequent goals; popped when the frame pops. WI-108.
    /// WI-683: carried carrier-faithfully as `Value` (a `Value::Node` antecedent
    /// keeps its occurrence), matched via `match_view_value_pattern` — parity
    /// with the already-`Value` Γ overlay, no lowering to a hash-consed term.
    assumed_facts: Vec<Value>,
}

/// WI-246: reify a goal `Value` to a hash-consed `TermId` — a `Value::Term`
/// unwraps for free; a `Value::Node` occurrence goal is reified via
/// `occurrence_to_term`. Used only at genuine term/identity boundaries
/// (residual, dedup key, external-row handlers, assumed-fact matching), never
/// for the candidate match itself (which goes through `query_view`).
fn reify_goal_value(kb: &mut KnowledgeBase, g: &Value) -> TermId {
    match g {
        Value::Term { id: t, .. } => *t,
        Value::Node(occ) => node_occurrence::occurrence_to_term(kb, occ),
        // Goals are always term- or occurrence-shaped structures.
        other => panic!("reify_goal_value: non-goal Value {}", other.type_name()),
    }
}

/// Outcome of walking an `eq`/`neq` goal's two operands (WI-246): both
/// resolved, a flex operand forcing `Delay`, or a missing arg slot.
enum EqOperands {
    Ready(Value, Value),
    Delay,
    Absent,
}

/// Outcome of the structural unification walk (`builtin_unify`, proposal 049).
/// The recursion's three-valued signal, mapped to a [`BuiltinResult`] at the
/// top: `Ok` carries its bindings in the working substitution, `Fail` is no
/// unifier (functor/arity/scalar mismatch or occurs-check), `Delay` defers the
/// whole goal on an unreduced complex op-call operand (substitution
/// transparency, WI-483).
enum UnifyOutcome {
    Ok,
    Fail,
    Delay,
}

/// A comparable number extracted from a goal-arg `Value` for `cmp` (WI-246).
enum Num {
    Int(i64),
    Big(num_bigint::BigInt),
    Float(ordered_float::OrderedFloat<f64>),
}

/// Where a result-binding builtin should put its computed value (WI-246):
/// bind the unbound result var, or check equality against an already-bound
/// result. Resolved from the result arg through `TermView` *before* the
/// `&mut self` alloc, so no `ViewItem` borrow is held across it.
enum ResultTarget {
    Bind(VarId),
    /// An already-bound result to check the computed value against — held as a
    /// `Value` (a literal occurrence arg reads as `Value::Node`), reified in
    /// `finish_result`. `None` ⇒ the result arg slot is absent.
    Compare(Option<Value>),
}

/// Result of a single step in the search loop.
enum StepResult {
    /// Keep stepping.
    Continue,
    /// A solution has been found; yield it.
    YieldSolution(Solution),
}

/// Resolution telemetry. Counters are bumped during stepping; used to
/// gauge the asymptotic cost of a query.
#[derive(Clone, Debug, Default)]
pub struct ResolveStats {
    /// Number of `step()` invocations.
    pub steps: u64,
    /// Number of lazy-walks of `goals[0]` performed at goal-selection
    /// time in `step_init`. Should scale linearly with body size — i.e.
    /// roughly one walk per goal consumed (WI-030).
    pub lazy_walk_calls: u64,
    /// WI-628 — the search abandoned at least one branch at the `max_depth`
    /// limit, so it is INCOMPLETE: an empty / short result is UNDECIDED, not a
    /// refutation. Not a cost counter like the others — a completeness signal
    /// that rides with the telemetry so the EAGER `resolve` consumers (the
    /// constraint / quantifier guards, which read `is_empty()` / a count as a
    /// verdict) can read it off the drained stream ([`SearchStream::drain_all`])
    /// instead of silently deciding from a truncated search. Mirrors the
    /// stream-level [`SearchStream::truncated`] flag, snapshotted at drain time.
    pub truncated: bool,
}

/// Lazy search stream that yields one solution at a time via
/// `split_first`. Converts recursive DFS into an explicit choice-point
/// stack.
pub struct SearchStream {
    stack: Vec<Frame>,
    config: ResolveConfig,
    /// Per-query cache: a ground goal's carrier-agnostic [`GoalKey`] → its
    /// discrim-tree query results. Keyed by the structural fingerprint (not a
    /// hash-consed `TermId`), so a `Value::Node` occurrence goal caches on equal
    /// footing with a `Value::Term` — the typer phase / `anthill prove`, which
    /// feed occurrence goals, get query caching too. Safe because facts/rules
    /// don't change during a single resolve call.
    query_cache: HashMap<GoalKey, Vec<(RuleId, Substitution)>>,
    /// Telemetry (see `ResolveStats`).
    stats: ResolveStats,
    /// Monotonic cut-barrier allocator (proposal 033.1 / WI-568). Bumped each
    /// time a rule body containing a `!` is opened, yielding a fresh barrier
    /// unique within this stream — the cut goal baked into that body carries it,
    /// and the choice point that opened the body is tagged with it, so the cut
    /// commits to exactly its own invocation. Local to the stream, so a cut
    /// inside `not(P)` (a sub-stream — see `step_naf`) prunes only that
    /// sub-proof's choice points.
    next_barrier: i64,
    /// Per-query cache: rule → its cut functor (`Some` = the body has a top-level
    /// `!`, `None` = cut-free). Whether a rule body contains a cut is a static
    /// property, so this hoists the per-activation `cut_marker_functor` scan off
    /// the hot path — the overwhelming majority of rules are cut-free and resolve
    /// the body open with one `HashMap` probe instead of scanning every goal
    /// (WI-568). Safe because rules don't change during a single resolve call.
    cut_cache: HashMap<RuleId, Option<Symbol>>,
    /// WI-616/WI-628 — set when any branch was abandoned at the `max_depth`
    /// limit: the search is INCOMPLETE, so "no solutions" does not mean
    /// "refuted". Read (via [`SearchStream::drain_verdict`]) by the two
    /// closed-sub-proof consumers — the semantic-`eq` sub-resolution
    /// ([`KnowledgeBase::prove_rule_predicate`]) and ground NAF
    /// ([`SearchStream::step_naf`]) — to answer *undecided* instead of a definite
    /// verdict when the proof search was truncated. (The depth pop itself stays
    /// silent for ordinary resolution; surfacing truncation to the EAGER
    /// `resolve` consumers — the constraint / quantifier guards, which read
    /// `is_empty()` as refutation — is the filed WI-628 follow-up.)
    truncated: bool,
}

/// WI-628 — the three-way verdict of draining a CLOSED sub-resolution (see
/// [`SearchStream::drain_verdict`]). `truncated` rides ALONGSIDE the verdict so a
/// consumer cannot read an empty result as a refutation without first seeing that
/// the search was cut short at the depth limit — the discipline WI-628 restores
/// after ground NAF read a truncated empty search as "refuted".
struct DrainVerdict {
    /// A DEFINITE (residual-free) solution was found — the sub-goal holds.
    definite: bool,
    /// At least one FLOUNDERED (residual) solution was seen — undischarged goals.
    residual: bool,
    /// A branch was abandoned at the depth limit — an empty result is then
    /// UNDECIDED, never a refutation.
    truncated: bool,
}

impl SearchStream {
    /// Yield the next solution, consuming self and returning the
    /// continuation stream. Returns `None` when exhausted.
    pub fn split_first(mut self, kb: &mut KnowledgeBase) -> Option<(Solution, SearchStream)> {
        loop {
            if self.stack.is_empty() {
                return None;
            }
            match self.step(kb) {
                Some(StepResult::Continue) => continue,
                Some(StepResult::YieldSolution(sol)) => return Some((sol, self)),
                None => return None,
            }
        }
    }

    /// WI-628 — drive this stream with a manual `step` loop (NOT `split_first`,
    /// which consumes the stream on exhaustion) so `truncated` stays readable
    /// AFTER the search runs dry, then classify three ways. Consuming: the caller
    /// keeps only the [`DrainVerdict`]. Stops early on the first DEFINITE solution
    /// (a found proof wins regardless of later truncation). The shared drain of
    /// the two closed-sub-proof consumers ([`Self::step_naf`] ground NAF and
    /// [`KnowledgeBase::prove_rule_predicate`] semantic `eq`) — returning
    /// `truncated` beside the verdict so neither can forget to consult it.
    fn drain_verdict(mut self, kb: &mut KnowledgeBase) -> DrainVerdict {
        let mut definite = false;
        let mut residual = false;
        loop {
            if self.is_empty() {
                break;
            }
            match self.step(kb) {
                Some(StepResult::YieldSolution(sol)) => {
                    if sol.is_definite() {
                        definite = true;
                        break;
                    }
                    residual = true;
                }
                Some(StepResult::Continue) => {}
                None => break,
            }
        }
        DrainVerdict { definite, residual, truncated: self.truncated }
    }

    /// WI-628 — collect ALL solutions (up to `max_solutions`, 0 = unlimited)
    /// with a manual `step` loop, then return them and the final stats WITH
    /// `truncated` folded onto the stats. The eager front doors
    /// ([`KnowledgeBase::resolve_goals_with_truncation`] and
    /// [`KnowledgeBase::resolve_with_stats`]) route through this instead of a
    /// `split_first` loop because `split_first` consumes the stream on
    /// exhaustion and DROPS the stream-level `truncated` flag — so a constraint
    /// / quantifier guard reading `is_empty()` would decide a refutation from an
    /// incomplete search (the WI-628 hole, the eager-consumer analog of the
    /// ground-NAF one). Draining by hand keeps the stream alive so
    /// `self.truncated` is still readable after the search runs dry — this is
    /// the ONE place the live flag becomes an observable result.
    fn drain_all(mut self, kb: &mut KnowledgeBase, max_solutions: usize) -> (Vec<Solution>, ResolveStats) {
        let mut solutions = Vec::new();
        loop {
            if self.is_empty() {
                break;
            }
            match self.step(kb) {
                Some(StepResult::YieldSolution(sol)) => {
                    solutions.push(sol);
                    if max_solutions > 0 && solutions.len() >= max_solutions {
                        break;
                    }
                }
                Some(StepResult::Continue) => {}
                None => break,
            }
        }
        let mut stats = self.stats.clone();
        stats.truncated = self.truncated;
        (solutions, stats)
    }

    /// Check if the stream is obviously exhausted (empty stack).
    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    /// Execute one step of the search. Returns `None` when the stack is
    /// empty (no more work).
    fn step(&mut self, kb: &mut KnowledgeBase) -> Option<StepResult> {
        let frame = self.stack.last_mut()?;
        self.stats.steps += 1;
        match frame.state {
            FrameState::Init { .. } => self.step_init(kb),
            FrameState::ChoicePoint { .. } => self.step_choice_point(kb),
        }
    }

    /// Proposal 050 (WI-537) — the Γ-overlay candidates for a goal: each
    /// local-interpretation fact that unifies with the (already σ-reified)
    /// `goal_value`, as a zero-body [`Candidate::Assumption`]. The
    /// discrimination-tree query *is* the unifier; each candidate is confirmed
    /// `!is_contradiction()` exactly as `assumed_facts` / `query_view` are. A Γ
    /// fact `neq(b, 0)` over a rigid parameter keys `RigidVar(b)` (WI-537's
    /// `ViewHead` refactor) — it matches the same rigid, never a concrete goal.
    /// Empty unless the typer's `prove_from_gamma` bridge seeded `config.gamma`.
    fn gamma_candidates_for(&self, kb: &KnowledgeBase, goal_value: &Value) -> Vec<Candidate> {
        let Some(gamma) = self.config.gamma.clone() else {
            return Vec::new();
        };
        gamma
            .query_resolved_value(kb, goal_value, true, |f| f.clone())
            .into_iter()
            // Per-parameter soundness (WI-537): the discrim query unifies a goal
            // variable as a WILDCARD, so a fact `neq(b, 0)` would also match a
            // goal `neq(c, 0)` about a DIFFERENT parameter and unsoundly discharge
            // it. A Γ fact may discharge a goal only when it IS that goal up to
            // variable IDENTITY — `views_structurally_equal` compares vars by
            // identity, so `neq(b,0)` discharges `neq(b,0)` (same parameter) but
            // never `neq(c,0)`. (A KB-rule derivation still discharges: once the
            // rule head binds, the subgoal is the specific fact.) This is what
            // lets a parameter stay open-world for eq/neq floundering — the
            // generic flex-var representation — while keeping Γ membership exact.
            .filter(|(fact, s)| {
                !s.is_contradiction()
                    && crate::kb::term_view::views_structurally_equal(kb, goal_value, fact)
            })
            .map(|(_, s)| Candidate::Assumption(s))
            .collect()
    }

    /// Handle a frame in `Init` state — classify the current goal.
    fn step_init(&mut self, kb: &mut KnowledgeBase) -> Option<StepResult> {
        let frame = self.stack.last().unwrap();
        let depth = frame.depth;
        let delay_mode = match &frame.state {
            FrameState::Init { delay_mode } => delay_mode.clone(),
            _ => unreachable!(),
        };

        // 1. Depth limit exceeded → pop (recorded: the search is now incomplete,
        // so exhaustion no longer proves refutation — WI-616 `truncated`).
        if depth > self.config.max_depth {
            self.truncated = true;
            self.stack.pop();
            return Some(StepResult::Continue);
        }

        // 2. In delayed mode and consecutive_delays >= goals.len() → residualize
        if let DelayMode::Delayed { consecutive_delays } = &delay_mode {
            if *consecutive_delays >= frame.goals.len() {
                let subst = frame.subst.clone();
                // WI-348: residual carries the delayed goals as `Value` — no
                // materialize-to-`TermId`, so a goal mentioning a `Value::Node`
                // keeps its occurrence identity.
                let residual: Vec<Value> = frame.goals.clone();
                self.stack.pop();
                // WI-519: this is a FLOUNDERED branch (delay-and-rotate exhausted
                // with goals still undischarged). In definite-only mode it is not
                // a solution — skip it so it never counts toward `max_solutions`
                // or masquerades as success.
                if self.config.definite_only {
                    return Some(StepResult::Continue);
                }
                let sol = Solution { subst, residual };
                self.record_solution_in_ancestors();
                return Some(StepResult::YieldSolution(sol));
            }
        }

        // 3. Goals empty → yield solution (with head-var dedup)
        if frame.goals.is_empty() {
            let sol = Solution {
                subst: frame.subst.clone(),
                residual: vec![],
            };
            self.stack.pop();

            // Head-var dedup: project solution onto each ancestor ChoicePoint's
            // goal vars. If the projection was already seen, skip this solution.
            if self.is_duplicate_projection(kb, &sol) {
                return Some(StepResult::Continue);
            }

            self.record_solution_in_ancestors();
            return Some(StepResult::YieldSolution(sol));
        }

        // [WI-030] Lazy substitution. σ already carries every binding
        // accumulated up to this point (merged via `bind_compressed` in
        // `step_choice_point`). Walking goals[0] here — instead of eagerly
        // applying σ to every remaining goal after each match — turns the
        // inherent SLD work from O(n²) into O(n × goal_size). Memoize the
        // walked form back into goals[0] so choice-point retries don't
        // re-walk. Skip the structural walk when σ is empty (no bindings
        // could change anything anyway).
        self.stats.lazy_walk_calls += 1;
        // Walk goals[0] under σ to a `Value` goal (memoized back). A `Value::Node`
        // occurrence goal walks via `substitute_occurrence` (occurrence-native,
        // no lowering); a `Value::Term` goal via `apply_subst`. The goal rides
        // carrier-neutrally from here — the builtin handlers read it through
        // `TermView`, reifying to a `TermId` only at genuine term boundaries.
        let goal_val: Value = {
            let f = self.stack.last().unwrap();
            if f.subst.is_empty() {
                f.goals[0].clone()
            } else {
                let subst = f.subst.clone();
                let g0 = f.goals[0].clone();
                let walked = match g0 {
                    Value::Term { id: t, .. } => Value::term(kb.apply_subst(t, &subst)),
                    Value::Node(occ) => {
                        Value::Node(node_occurrence::substitute_occurrence(kb, &occ, &subst))
                    }
                    other => other,
                };
                self.stack.last_mut().unwrap().goals[0] = walked.clone();
                walked
            }
        };
        let frame = self.stack.last().unwrap();

        // Scoping / hereditary-Harrop markers (`__pop_assumption`,
        // `forall_impl`, WI-108). Detected by functor so they work for
        // occurrence goals too (a rule-body `forall …` is a `Value::Node`).
        // `__pop_assumption` classifies carrier-neutrally; the forall/quant
        // handlers are term-structured, so reify only when one of them matches.
        let is_marker = match goal_val.head(kb) {
            ViewHead::Functor { functor: Some(f), .. } => {
                let n = kb.resolve_sym(f);
                n == "__pop_assumption" || n == "forall_impl"
                    || n == "forall_in" || n == "some_in"
            }
            _ => false,
        };
        if is_marker {
            // 3.4 __pop_assumption(N) — pops N entries off assumed_facts.
            // Carrier-neutral: reads the count off the goal's TermView, so this
            // marker classifies without a `reify_goal_value` lowering.
            if let Some(n) = Self::pop_assumption_arg(kb, &goal_val) {
                let f = self.stack.last_mut().unwrap();
                let drop_from = f.assumed_facts.len().saturating_sub(n);
                f.assumed_facts.truncate(drop_from);
                f.goals.remove(0);
                f.depth += 1;
                f.state = FrameState::Init { delay_mode: delay_mode.reset() };
                return Some(StepResult::Continue);
            }
            // forall_impl / forall_in / some_in classify carrier-neutrally off
            // the goal's `TermView`, and their step_ handlers now read binders /
            // antecedents / consequents through `TermView` too and skolemise via
            // `reify_value` (WI-683) — so a rule-body `forall … ==>` arriving as a
            // `Value::Node` occurrence flows through without a whole-goal reify.
            //
            // 3.5 forall_impl(binders, antecedents, consequent) — skolemise,
            // push antecedents as scoped assumptions, prepend consequents.
            if Self::is_forall_impl(kb, &goal_val) {
                return self.step_forall_impl(kb, &goal_val, depth, delay_mode);
            }
            // 3.6 (WI-027) forall_in / some_in — bounded quantification over a
            // collection's elements; expand to a conjunction / disjunction.
            if let Some(is_forall) = Self::bounded_quant_kind(kb, &goal_val) {
                return self.step_bounded_quant(kb, &goal_val, is_forall, depth, delay_mode);
            }
        }

        // 4. Builtin goal — classify by functor read through TermView.
        if let Some(tag) = kb.get_builtin_view(&goal_val) {
            // NAF needs sub-resolution context — handle it specially
            if tag == BuiltinTag::Not {
                return self.step_naf(kb, &goal_val, depth, delay_mode);
            }
            // HO predicate application: replace goal with the applied term.
            // Carrier-neutral (WI-482 follow-up): `lower_ho_apply` reads the goal
            // through `TermView`, so a rule-body `ho_apply` occurrence lowers
            // without a whole-goal reify — only its args are reified as terms.
            if tag == BuiltinTag::HoApply {
                let subst = frame.subst.clone();
                if let Some(applied) = Self::lower_ho_apply(kb, &goal_val, &subst) {
                    let f = self.stack.last_mut().unwrap();
                    f.goals[0] = Value::term(applied);
                    f.state = FrameState::Init { delay_mode };
                    return Some(StepResult::Continue);
                } else {
                    // Predicate var still unbound — fail (can't apply unbound predicate)
                    self.stack.pop();
                    return Some(StepResult::Continue);
                }
            }
            // Bypasses execute_builtin: push_choice's effect is on the
            // choice-point stack, not on σ — like Not/HoApply. Carrier-neutral
            // (WI-348): the two branch goals are read off the goal's `TermView`
            // and walked to `Value`s, so a `Value::Node` push_choice goal needs no
            // whole-goal reify and its `Node` branch continuations ride through
            // as-is.
            if tag == BuiltinTag::PushChoice {
                let subst = frame.subst.clone();
                if let Some((goal_a, goal_b)) =
                    Self::resolve_push_choice_args(kb, &goal_val, &subst)
                {
                    let candidates = vec![
                        Candidate::Continuation(vec![goal_a]),
                        Candidate::Continuation(vec![goal_b]),
                    ];
                    let f = self.stack.last_mut().unwrap();
                    f.state = FrameState::ChoicePoint {
                        delay_mode,
                        original_goal: goal_val.clone(),
                        candidates,
                        next: 0,
                        any_delayed: false,
                        child_solutions: 0,
                        seen_goals: HashSet::new(),
                        cut_barrier: None,
                    };
                    return Some(StepResult::Continue);
                } else {
                    self.stack.pop();
                    return Some(StepResult::Continue);
                }
            }
            // Cut (`!`), proposal 033.1 / WI-568. Bypasses execute_builtin: its
            // effect is on the choice-point stack, not on σ. The barrier `B` is
            // baked into the goal (`cut(B)`) when the enclosing rule body was
            // opened (see `step_choice_point`); `apply_cut` prunes back to the
            // frame tagged with `B`. Then the cut goal is consumed and resolution
            // continues with the body's tail — the cut itself always succeeds.
            if tag == BuiltinTag::Cut {
                // Carrier-neutral (WI-348): the barrier is read off the goal's
                // `TermView`, so a `Value::Node` cut goal needs no whole-goal reify.
                let barrier = Self::resolve_cut_barrier(kb, &goal_val);
                self.apply_cut(barrier);
                let new_delay = delay_mode.reset();
                let f = self.stack.last_mut().unwrap();
                f.goals.remove(0);
                f.depth += 1;
                f.state = FrameState::Init { delay_mode: new_delay };
                return Some(StepResult::Continue);
            }
            // WI-537 (proposal 050): a Γ fact can discharge a builtin guard the
            // builtin would only DELAY on — `neq(b, 0)` over a symbolic
            // parameter `b`. Consult the Γ overlay before running the builtin;
            // if a local fact unifies with the goal, resolve via that assumption
            // (sound — Γ asserts it holds) and skip the builtin. A ground
            // builtin (`neq(5, 0)`) finds no Γ match and runs normally; `gamma`
            // is `None` for every resolution but the typer's bridge, so this is
            // inert otherwise.
            let mut force_delay = false;
            if self.config.gamma.is_some() {
                let frame_subst = self.stack.last().unwrap().subst.clone();
                let goal_value = kb.reify_value(&goal_val, &frame_subst);
                let gamma_cands = self.gamma_candidates_for(kb, &goal_value);
                if !gamma_cands.is_empty() {
                    let f = self.stack.last_mut().unwrap();
                    f.state = FrameState::ChoicePoint {
                        delay_mode,
                        original_goal: goal_val.clone(),
                        candidates: gamma_cands,
                        next: 0,
                        any_delayed: false,
                        child_solutions: 0,
                        seen_goals: HashSet::new(),
                        cut_barrier: None,
                    };
                    return Some(StepResult::Continue);
                }
                // WI-067 (proposal 050): no Γ fact unified, and the goal ranges over
                // an OPEN-WORLD parameter (a `var_ref` binder reference) — a scalar
                // builtin (`neq`/`eq`/…) would WRONGLY decide it, treating the
                // var_ref reflect-term as a ground constant (`neq(var_ref(b), 0)`
                // succeeds structurally). Force a DELAY so a symbolic guard
                // FLOUNDERS instead of being NAF-refuted: drop only on a positive
                // proof of ¬guard (048 §"constructive refutation"). The branch /
                // match cases that DO know `neq(b, 0)` discharged above via the Γ
                // fact; this is the symbolic fall-through.
                force_delay = kb.value_has_open_world_ref(&goal_value, &frame_subst);
            }
            // WI-580 (design §3.3): abstract-interpretation fallback. A `SemEq`
            // goal whose operand is an unground, rule-less bodied op-call is
            // expanded by case-splitting the callee's body — one `Continuation`
            // per `match` arm — instead of delaying. Mirrors the `push_choice` /
            // Γ special-cases above (set the frame's ChoicePoint, then continue).
            if !force_delay && tag == BuiltinTag::SemEq {
                let sub = self.stack.last().unwrap().subst.clone();
                if let Some(candidates) = kb.unfold_eq_operand(&goal_val, &sub) {
                    let f = self.stack.last_mut().unwrap();
                    f.state = FrameState::ChoicePoint {
                        delay_mode,
                        original_goal: goal_val.clone(),
                        candidates,
                        next: 0,
                        any_delayed: false,
                        child_solutions: 0,
                        seen_goals: HashSet::new(),
                        cut_barrier: None,
                    };
                    return Some(StepResult::Continue);
                }
            }
            let builtin_result = if force_delay {
                BuiltinResult::delay()
            } else {
                kb.execute_builtin(tag, &goal_val, &frame.subst)
            };
            match builtin_result {
                BuiltinResult::Success => {
                    // Remove goals[0], bump depth, reset delay counter if delayed
                    let new_goals = frame.goals[1..].to_vec();
                    let new_subst = frame.subst.clone();
                    let new_depth = depth + 1;
                    let new_delay = delay_mode.reset();
                    // Replace current frame
                    let f = self.stack.last_mut().unwrap();
                    f.goals = new_goals;
                    f.subst = new_subst;
                    f.depth = new_depth;
                    f.state = FrameState::Init { delay_mode: new_delay };
                    return Some(StepResult::Continue);
                }
                BuiltinResult::SuccessWithBindings(extra) => {
                    // Merge extra bindings into the current substitution.
                    // Iterate Value-typed bindings; use bind_waking so we
                    // don't force everything through Value::Term AND so any
                    // constraint carried on a bound var wakes (WI-502 Step 2).
                    let new_goals = frame.goals[1..].to_vec();
                    let mut new_subst = frame.subst.clone();
                    // WI-502 Step 2 (M7(b)) — carry `extra`'s TOP-LEVEL constraint
                    // store through the merge. This lift is the single funnel for
                    // every builtin `extra` plus `builtin_unify`'s `work`, and it
                    // previously threaded `extra.bindings` ONLY — silently dropping
                    // any constraint a builtin recorded. (No-op until a resolver-side
                    // producer exists in Step 3; mirrors ignoring `extra.parent`.)
                    new_subst.absorb_constraints(&extra);
                    // WI-649 NB: this non-`Term` `bind_waking` is NOT
                    // occurs-checked (unlike the external-row bind at the fact
                    // fast-path). It is safe today only by ABSENCE OF A PRODUCER:
                    // every builtin that writes a non-`Term` `extra` binding is
                    // either occurs-checked already (`builtin_unify` →
                    // `unify_bind`) or has no live anthill caller
                    // (`occurrence_term` / `sub_occurrences`, which could bind a
                    // pattern var to a non-`Term` occurrence). If a reflect op that
                    // quotes an open term over a shared var ever gains a caller,
                    // this becomes the same cyclic-σ route WI-649 closed at the
                    // fact fast-path — mirror the `occurs_in_value` guard here then.
                    for (var, val) in extra.bindings.iter() {
                        new_subst.bind_waking(kb, *var, val.clone());
                    }
                    let new_depth = depth + 1;
                    let new_delay = delay_mode.reset();
                    let f = self.stack.last_mut().unwrap();
                    f.goals = new_goals;
                    f.subst = new_subst;
                    f.depth = new_depth;
                    f.state = FrameState::Init { delay_mode: new_delay };
                    return Some(StepResult::Continue);
                }
                BuiltinResult::Failure => {
                    // Builtin definitively failed — no solutions from this branch
                    self.stack.pop();
                    return Some(StepResult::Continue);
                }
                BuiltinResult::Delay { truncated } => {
                    // WI-628: a carrier `eq`/`neq` whose closed sub-proof TRUNCATED
                    // folds its truncation onto THIS (outer) stream before the frame
                    // handling, so an eager NAF/guard consumer draining this stream
                    // sees the incomplete search rather than reading empty-as-refute.
                    self.truncated |= truncated;
                    match delay_mode {
                        DelayMode::Normal => {
                            if frame.goals.len() == 1 {
                                // Only goal — residualize (WI-519: or skip in
                                // definite-only mode — a floundered residual is
                                // not a definite solution).
                                let subst = frame.subst.clone();
                                let residual = vec![goal_val.clone()];
                                self.stack.pop();
                                if self.config.definite_only {
                                    return Some(StepResult::Continue);
                                }
                                self.record_solution_in_ancestors();
                                return Some(StepResult::YieldSolution(Solution { subst, residual }));
                            } else {
                                // Rotate to end, enter Delayed mode
                                let mut rotated: Vec<Value> = frame.goals[1..].to_vec();
                                rotated.push(goal_val.clone());
                                let new_depth = depth + 1;
                                let f = self.stack.last_mut().unwrap();
                                f.goals = rotated;
                                f.depth = new_depth;
                                f.state = FrameState::Init {
                                    delay_mode: DelayMode::Delayed { consecutive_delays: 1 },
                                };
                                return Some(StepResult::Continue);
                            }
                        }
                        DelayMode::Delayed { consecutive_delays } => {
                            // Rotate to end, increment consecutive_delays
                            let mut rotated: Vec<Value> = frame.goals[1..].to_vec();
                            rotated.push(goal_val.clone());
                            let new_depth = depth + 1;
                            let f = self.stack.last_mut().unwrap();
                            f.goals = rotated;
                            f.depth = new_depth;
                            f.state = FrameState::Init {
                                delay_mode: DelayMode::Delayed {
                                    consecutive_delays: consecutive_delays + 1,
                                },
                            };
                            return Some(StepResult::Continue);
                        }
                    }
                }
            }
        }

        // WI-580 (design §3.3/§5): a bare goal whose functor is a rule-LESS bodied
        // Bool operation is that operation's RELATIONAL VIEW — derived from the
        // body, not a hand-written `:-` twin whose unification diverges from the
        // body's declared `eq`. Route it to `eq(f(args), true)` so it resolves
        // through the body: a ground call decides via the eval bridge
        // (`reduce_op_value`) using the declared `Eq`, an unground one suspends to
        // a WI-519 residual (the "sound checker, not generator" of §5). Reached
        // only for a non-builtin goal (the builtin block above returns first);
        // fires only once a functor's unification twins are retired, and never for
        // a rule-backed relation (`Set.member`) — see `bare_bodied_bool_relation`.
        if let ViewHead::Functor { functor: Some(f), .. } = goal_val.head(kb) {
            if kb.bare_bodied_bool_relation(f) {
                let eq_sym = kb.eq_functor();
                let eq_goal = kb.make_goal_value(eq_sym, vec![goal_val.clone(), Value::Bool(true)]);
                let fr = self.stack.last_mut().unwrap();
                // Rewrite goal[0] in place, same goal count — `delay_mode` is
                // threaded through unchanged (like the `push_choice` / Γ / HoApply
                // goal-transform special-cases, NOT reset like a builtin discharge):
                // the rewrite is one step, so the goal still gets processed before
                // the delay-mode residualization check (`consecutive_delays >=
                // goals.len()`) can bite — a ground `member` reaches its `eq` and
                // decides; an unground one residualizes either way.
                fr.goals[0] = eq_goal;
                fr.state = FrameState::Init { delay_mode };
                return Some(StepResult::Continue);
            }
        }

        // 5. (WI-251) Expression-typed query path: the legacy
        // the legacy occurrence by-functor index lookup is gone. Reflection queries
        // that materialized expression occurrences now read from
        // `kb.op_bodies` (NodeOccurrence trees) at the reflection-op
        // layer, not via Resolve's candidate selection.
        let mut candidates: Vec<Candidate> = Vec::new();

        // 6. Non-builtin goal → query discrimination tree via `TermView`
        // (no lowering — a `Value::Node` goal matches Term-indexed heads).
        // Cache the discrim query only for a goal whose `GoalKey` faithfully and
        // completely identifies what `query_view` depends on, keyed by the
        // carrier-agnostic `GoalKey`. The fingerprint is taken over `goal_val`
        // exactly as `query_view` reads it — through `TermView` with NO σ
        // resolution (an empty subst). `query_view(&goal_val)` (below) applies no
        // σ, so the key must not either: a var kept in `goal_val` (a flex `Global`
        // that σ bound to a non-`Term`, or a child of an unwalked
        // `Value::Entity`/`Tuple` — the `other => other` walk arm) must stay a
        // `Var` token → not cacheable, NOT be resolved to a structure `query_view`
        // never saw. `is_cacheable` also excludes an `Opaque` leaf. Unlike the
        // former hash-consed `TermId` key, a ground `Value::Node` occurrence goal
        // caches too — no materialization.
        let cache_key: Option<GoalKey> = {
            let key = goal_fingerprint(kb, &goal_val, &Substitution::default());
            key.is_cacheable().then_some(key)
        };
        let rule_candidates = match cache_key.as_ref().and_then(|k| self.query_cache.get(k).cloned()) {
            Some(cached) => cached,
            None => {
                let mut rc = kb.query_view(&goal_val);
                // [simp] resolution-phase rewrite — carrier-neutral, so a
                // `Value::Node` occurrence goal (the typer phase and `anthill
                // prove` feed these) simplifies too, not only a hash-consed term
                // goal. Fires only when the goal has no non-equation candidate
                // (it doesn't already resolve).
                if self.config.simplify {
                    let has_non_eq = rc.iter().any(|(rid, _)| !kb.is_equation(*rid));
                    if !has_non_eq {
                        // WI-595: thread the frame's σ (its constraint store +
                        // bindings) so a constraint-typed carrier var in the redex
                        // is decidable by the type-directed `[simp]` guard, rather
                        // than reading headless under an empty subst (C1). O(1)
                        // imbl clone.
                        let eq_subst = self.stack.last().unwrap().subst.clone();
                        let (rewritten, changes) =
                            kb.apply_eq_rules(&goal_val, 100, &eq_subst);
                        // WI-634: when the WHOLE goal is a var-projecting simp
                        // redex (`pick(?q, 7)` under `[simp] eq(pick(?a,?b),?a)`),
                        // the rewrite is a bare caller var `?q`. Re-querying a bare
                        // var wildcard-matches EVERY head (a `Global` query head
                        // routes to all leaves) — spurious solutions against every
                        // fact. A bare-var goal is not resolvable, so leave the
                        // candidate set untouched (the goal fails) rather than
                        // matching everything. The intended use — a redex nested in
                        // a compound goal (`found(pick(?q,7))` → `found(?q)`) —
                        // keeps the goal a compound and re-queries normally.
                        if !changes.is_empty()
                            && !matches!(rewritten.head(kb), ViewHead::Var(_))
                        {
                            rc = kb.query_view(&rewritten);
                        }
                    }
                }
                rc.retain(|(rid, _)| !kb.is_equation(*rid));
                if let Some(k) = cache_key {
                    self.query_cache.insert(k, rc.clone());
                }
                rc
            }
        };

        candidates.extend(rule_candidates.into_iter().map(|(rid, s)| Candidate::Rule(rid, s)));

        // External-source rows (proposal 007 §11 + 026.1 Q4 Stage B). If the
        // goal head functor has a registered route handler, drain its stream and
        // add each matching row as an ExternalRow candidate. Carrier-neutral
        // (WI-696): the handler reads the goal `Value` through `TermView` and each
        // row matches via `match_view_value_pattern` — no whole-goal reify.
        let functor = match goal_val.head(kb) {
            ViewHead::Functor { functor: Some(f), .. } => Some(f),
            _ => None,
        };
        if let Some(functor) = functor {
            if kb.route_handler_for(functor).is_some() {
                let stream_opt =
                    kb.route_handler_for(functor).map(|h| h.retrieve(kb, &goal_val));
                if let Some(mut stream) = stream_opt {
                    while let Some(row) = stream.next() {
                        if let Some(subst) = kb.match_view_value_pattern(&goal_val, &row) {
                            if !subst.is_contradiction() {
                                candidates.push(Candidate::ExternalRow(subst));
                            }
                        }
                    }
                }
            }
        }

        // Local hypotheses, matched against the goal and added as zero-body
        // `Assumption` candidates — resolved *inside* the normal SLD search, so
        // they chain through KB rules and obey backtracking / floundering with
        // no duplicated logic. Two sources:
        //   • the frame's `assumed_facts` (WI-108) — `forall_impl` antecedents,
        //     a per-frame `Vec<TermId>` (push/pop with the discharge);
        //   • the Γ overlay (WI-537 / proposal 050) — the typer's
        //     local-interpretation context, a discrimination-tree index global
        //     to this resolve call (`config.gamma`).
        // Both reify the goal through the current σ carrier-faithfully (WI-348),
        // so a goal carrying a `Value::Node` matches by structure rather than
        // being lowered to a hash-consed term that drops the occurrence.
        let assumed = self.stack.last().unwrap().assumed_facts.clone();
        if !assumed.is_empty() || self.config.gamma.is_some() {
            let frame_subst = self.stack.last().unwrap().subst.clone();
            let goal_value = kb.reify_value(&goal_val, &frame_subst);
            for assumed_fact in &assumed {
                if let Some(subst) = kb.match_view_value_pattern(assumed_fact, &goal_value) {
                    if !subst.is_contradiction() {
                        candidates.push(Candidate::Assumption(subst));
                    }
                }
            }
            // The Γ overlay (WI-537) joins the candidates for a NON-builtin goal
            // here, alongside the KB rules — `gamma_candidates_for` matches each
            // local fact structurally (the discrim tree is the unifier). A
            // builtin goal is handled earlier (it never reaches here); a Γ fact
            // discharging it is the pre-`execute_builtin` check above.
            candidates.extend(self.gamma_candidates_for(kb, &goal_value));
        }

        // Transition to ChoicePoint
        let f = self.stack.last_mut().unwrap();
        f.state = FrameState::ChoicePoint {
            delay_mode,
            original_goal: goal_val,
            candidates,
            next: 0,
            any_delayed: false,
            child_solutions: 0,
            seen_goals: HashSet::new(),
            cut_barrier: None,
        };
        Some(StepResult::Continue)
    }

    /// Handle `not(Goal)` — negation-as-failure.
    ///
    /// - If the inner goal is not ground after applying the current substitution,
    ///   delay (floundering prevention).
    /// - Otherwise, run sub-resolution: if the inner goal has ANY solution,
    ///   `not(Goal)` fails; if it has NO solutions, `not(Goal)` succeeds.
    /// True if `goal` is a `forall_impl(...)` body goal. Reads the functor
    /// through [`TermView`] (carrier-neutral — a rule-body `forall … ==>` arrives
    /// as a `Value::Node` occurrence); the caller passes the already-σ-applied
    /// goal, so no walk is needed here.
    fn is_forall_impl(kb: &KnowledgeBase, goal: &Value) -> bool {
        matches!(
            goal.head(kb),
            ViewHead::Functor { functor: Some(f), .. } if kb.resolve_sym(f) == "forall_impl"
        )
    }

    /// Discharge a `forall_impl(binders, antecedents, consequent)` body
    /// goal: skolemise the binders into fresh `Var::Rigid` witnesses,
    /// substitute throughout antecedents and consequent, push antecedents
    /// as scoped assumptions on the next frame, and prepend consequents
    /// to the goal stream.
    fn step_forall_impl(
        &mut self,
        kb: &mut KnowledgeBase,
        goal: &Value,
        depth: usize,
        delay_mode: DelayMode,
    ) -> Option<StepResult> {
        // `goal` arrives already σ-applied (the caller substitutes `goal_val`
        // before dispatch), so read its structure directly through `TermView`
        // — carrier-neutral (WI-683), no whole-goal reify: a rule-body
        // `forall … ==>` flows through as its `Value::Node` occurrence.
        let pos_arity = match goal.head(kb) {
            ViewHead::Functor { pos_arity, .. } => pos_arity,
            _ => 0,
        };
        let (Some(binders_arg), Some(antes_arg), Some(cons_arg)) =
            (goal.pos_arg(kb, 0), goal.pos_arg(kb, 1), goal.pos_arg(kb, 2))
        else {
            // Malformed forall_impl — treat as failure.
            self.stack.pop();
            return Some(StepResult::Continue);
        };
        if pos_arity != 3 {
            self.stack.pop();
            return Some(StepResult::Continue);
        }
        let binders = Self::unwrap_tuple_args(kb, &binders_arg);
        let antecedents = Self::unwrap_tuple_args(kb, &antes_arg);
        let consequents = Self::unwrap_tuple_args(kb, &cons_arg);
        drop((binders_arg, antes_arg, cons_arg));

        // Skolemise the binders into fresh `Rigid` witnesses, as a `Substitution`
        // (Global → `Value::Var(Rigid)`) applied by `reify_value` — carrier-
        // faithful, so a `Value::Node` antecedent skolemises via
        // `substitute_occurrence` (reused, not re-derived) rather than a bespoke
        // rebuild. Each binder is already σ-applied (a child of the reified
        // goal); an open quantified binder is a flex `Global`.
        let mut skolem = Substitution::default();
        for b in &binders {
            if let Some(Var::Global(vid)) = b.index_var(kb) {
                // Skolemise each distinct binder once: duplicate binders
                // (`forall(?x, ?x)` — one opened Global) must map to ONE rigid,
                // and re-binding `bind_value` to a second fresh rigid would flag a
                // spurious contradiction on this throwaway subst (and leak a var).
                if skolem.resolve_as_value(vid).is_none() {
                    let fresh = kb.fresh_var(vid.name());
                    skolem.bind_value(kb, vid, Value::Var(Var::Rigid(fresh)));
                }
            }
        }

        let frame_subst = self.stack.last().unwrap().subst.clone();

        // Skolemise antecedents, then lower a top-level `ho_apply` so an assumed
        // antecedent shares a functor with whatever the consequent's resolution
        // looks up (the resolver's HoApply path lowers the goal-side; we lower
        // the assumption-side here for parity).
        let skolemized_antecedents: Vec<Value> = antecedents
            .iter()
            .map(|a| {
                let sk = kb.reify_value(a, &skolem);
                match Self::lower_ho_apply(kb, &sk, &frame_subst) {
                    Some(t) => Value::term(t),
                    None => sk,
                }
            })
            .collect();
        let skolemized_consequents: Vec<Value> =
            consequents.iter().map(|c| kb.reify_value(c, &skolem)).collect();

        // Append a pop_assumption marker after the consequents so the assumed
        // antecedents go out of scope before the surrounding rule's remaining
        // goals run (WI-108 scoping invariant).
        let n_assumed = skolemized_antecedents.len();
        let mut new_goals: Vec<Value> = skolemized_consequents;
        if n_assumed > 0 {
            let marker = Self::make_pop_assumption_marker(kb, n_assumed);
            new_goals.push(Value::term(marker));
        }
        let frame = self.stack.last().unwrap();
        new_goals.extend(frame.goals[1..].iter().cloned());
        let mut new_assumed = frame.assumed_facts.clone();
        new_assumed.extend(skolemized_antecedents);
        let new_subst = frame.subst.clone();
        let new_delay = delay_mode.reset();

        self.stack.pop();
        self.stack.push(Frame {
            goals: new_goals,
            subst: new_subst,
            depth: depth + 1,
            state: FrameState::Init { delay_mode: new_delay },
            assumed_facts: new_assumed,
        });
        Some(StepResult::Continue)
    }

    /// WI-027: classify a bounded-quantifier body goal. `Some(true)` for
    /// `forall_in(?x, xs, tuple(body))`, `Some(false)` for `some_in(...)`,
    /// `None` otherwise. Reads the functor through [`TermView`] (carrier-neutral);
    /// the caller passes the already-σ-applied goal, so no walk is needed.
    fn bounded_quant_kind(kb: &KnowledgeBase, goal: &Value) -> Option<bool> {
        match goal.head(kb) {
            ViewHead::Functor { functor: Some(f), .. } => match kb.resolve_sym(f) {
                "forall_in" => Some(true),
                "some_in" => Some(false),
                _ => None,
            },
            _ => None,
        }
    }

    /// WI-027: collect a list `Value`'s elements when it is a fully ground spine
    /// — a `cons`/`nil` chain (the runtime list shape) or a `ListLiteral(e…)`
    /// (the un-desugared surface literal, since a bounded-quant collection slot
    /// carries no List-typed context to trigger the WI-007 `ListLiteral →
    /// cons/nil` rewrite). A `ListLiteral` carries all its elements positionally
    /// and never a tail (the `[h | t]` surface was removed, WI-560). Elements
    /// themselves need not be ground — only the SPINE. Returns `None` when the
    /// spine is not ground (an unbound `cons` tail, or a non-list head): the
    /// caller then DELAYs rather than silently deciding the quantifier.
    /// Constructors match by SHORT NAME via `resolve_sym` (`functor_sym` reads
    /// the `Fn{c}` / `Ref(c)` spellings alike), since a value list and the
    /// resolver can carry distinct `Symbol`s sharing the name `cons` / `nil`.
    ///
    /// WI-683: carrier-neutral — reads the whole spine (including a
    /// `ListLiteral`, now a structural `TermView` case) through [`TermView`], so
    /// a list riding as a `Value::Entity` (a runtime list), a `Value::Node`
    /// occurrence, or a hash-consed term all walk natively, no lowering. Each
    /// spine node is chased through σ ([`walk_value_chain`]): `goal_val` is built
    /// by `apply_subst`/`substitute_occurrence`, which are SHALLOW at a var's
    /// binding (they inline `?xs ↦ cons(a, ?t)` but not the `?t` inside), so the
    /// collection can arrive as `cons(a, ?t)` with `?t` bound to the rest — a
    /// partial cons a relational goal left in σ. Chasing per node resolves it;
    /// the `seen` set guards a cyclic σ spine (`?t ↦ cons(_, ?t)`) → `None`
    /// (delay), replacing the former `HashSet<TermId>` guard carrier-neutrally.
    fn bounded_list_elements(
        kb: &KnowledgeBase,
        list: &Value,
        subst: &Substitution,
    ) -> Option<Vec<Value>> {
        let mut elems = Vec::new();
        let mut seen: HashSet<VarId> = HashSet::new();
        let mut cur = Self::walk_value_chain(kb, list.clone(), subst, &mut seen)?;
        loop {
            let name = cur.head(kb).functor_sym().map(|f| kb.resolve_sym(f));
            match name.as_deref() {
                // The nullary terminator (a bare `Ref(nil)` or an empty `Fn{nil}`
                // / `Entity{nil}` — `functor_sym` unifies the spellings).
                Some("nil") => return Some(elems),
                Some("cons") => {
                    // `cons(head:, tail:)` — named (canonical); tolerate a
                    // positional `cons(h, t)` too, like `list_to_vec`. The tail is
                    // chased through σ before the next iteration inspects it.
                    match (
                        Self::cons_child(kb, &cur, "head", 0),
                        Self::cons_child(kb, &cur, "tail", 1),
                    ) {
                        (Some(h), Some(t)) => {
                            elems.push(h);
                            cur = Self::walk_value_chain(kb, t, subst, &mut seen)?;
                        }
                        // A malformed `cons` — surface as not-ground (delay)
                        // rather than silently dropping the element.
                        _ => return None,
                    }
                }
                Some("ListLiteral") => {
                    // A `ListLiteral` carries all its elements as positional
                    // children and never a tail (the `[h | t]` surface was
                    // removed, WI-560), so the spine ends here.
                    let mut i = 0;
                    while let Some(e) = cur.pos_arg(kb, i) {
                        elems.push(e.to_value());
                        i += 1;
                    }
                    return Some(elems);
                }
                // Unbound var tail or any non-list head → spine not ground.
                _ => return None,
            }
        }
    }

    /// Chase a `Value`'s var chain under σ to its representative, carrier-neutrally
    /// (a `Value::Term` / `Value::Node` var leaf or a bare `Value::Var` all resolve
    /// via `index_var` → σ). `None` on a REVISITED var — a cyclic σ spine (`?t ↦
    /// cons(_, ?t)`); the [`bounded_list_elements`] caller treats that as a
    /// non-ground spine (delay), never an infinite loop. Only spine nodes are
    /// chased (elements ride as-is), so `seen` collects tail vars, never element
    /// vars — a legitimate list has distinct tail vars, so no false cycle.
    fn walk_value_chain(
        kb: &KnowledgeBase,
        mut v: Value,
        subst: &Substitution,
        seen: &mut HashSet<VarId>,
    ) -> Option<Value> {
        while let Some(Var::Global(vid)) = v.index_var(kb) {
            if !seen.insert(vid) {
                return None; // cyclic spine
            }
            match subst.resolve_as_value(vid) {
                Some(bound) => v = bound.clone(),
                None => return Some(v), // unbound var — a non-ground spine at the caller
            }
        }
        Some(v)
    }

    /// A `cons` cell's `head` / `tail` child as an owned [`Value`], read carrier-
    /// neutrally (WI-683): matched by field NAME (not `Symbol` identity — a value
    /// list can carry a `head`/`tail` symbol distinct from the resolver's),
    /// falling back to the positional slot for a `cons(h, t)`.
    fn cons_child(kb: &KnowledgeBase, cell: &Value, name: &str, pos: usize) -> Option<Value> {
        for key in cell.named_keys(kb) {
            if kb.resolve_sym(key) == name {
                return cell.named_arg(kb, key).map(|c| c.to_value());
            }
        }
        cell.pos_arg(kb, pos).map(|c| c.to_value())
    }

    /// WI-027: discharge a `forall_in(?x, xs, tuple(body))` / `some_in(…)` body
    /// goal. The collection `xs` is walked to a ground `cons`/`nil` (or
    /// `ListLiteral`) spine and each element substituted for the binder `?x` in
    /// `body` (structurally, via [`subst_globals`](Self::subst_globals) — other
    /// free vars pass through, preserving σ sharing with the enclosing rule).
    ///   * `forall`: every element's body must hold → prepend the FLATTENED
    ///     conjunction of all element bodies (`nil` ⇒ vacuously true ⇒ drop the
    ///     goal). Deterministic frame replacement, like `step_forall_impl`.
    ///   * `some`: at least one element's body must hold → a CHOICE POINT with
    ///     one `Continuation` per element (`nil` ⇒ no witness ⇒ fail).
    /// A collection whose spine is NOT ground is DELAYed (WI-519 floundering),
    /// never silently decided.
    fn step_bounded_quant(
        &mut self,
        kb: &mut KnowledgeBase,
        goal: &Value,
        is_forall: bool,
        depth: usize,
        delay_mode: DelayMode,
    ) -> Option<StepResult> {
        // `goal` arrives already σ-applied (the caller substitutes `goal_val`
        // before dispatch), so read its structure directly through `TermView`
        // — carrier-neutral (WI-683). The binder / body ride as `Value`; only
        // the COLLECTION structural-arg is reified (below), for the term-spine
        // walk, mirroring `forall_impl`'s antecedent path.
        let pos_arity = match goal.head(kb) {
            ViewHead::Functor { pos_arity, .. } => pos_arity,
            _ => 0,
        };
        let (Some(binder_arg), Some(coll_arg), Some(body_arg)) =
            (goal.pos_arg(kb, 0), goal.pos_arg(kb, 1), goal.pos_arg(kb, 2))
        else {
            // Malformed bounded quantifier — treat as failure.
            self.stack.pop();
            return Some(StepResult::Continue);
        };
        if pos_arity != 3 {
            self.stack.pop();
            return Some(StepResult::Continue);
        }
        let binder = binder_arg.to_value();
        let collection = coll_arg.to_value();
        let body: Vec<Value> = Self::unwrap_tuple_args(kb, &body_arg);
        drop((binder_arg, coll_arg, body_arg));

        let subst = self.stack.last().unwrap().subst.clone();

        // The binder's Global var id (after rule opening it is a fresh Global,
        // never bound in σ). `None` if the slot is not an open Global — then no
        // element substitution applies (a degenerate but defensible case). Read
        // off the σ-applied binder directly (no re-walk): it and the body's
        // binder occurrence share the SAME shallow substitution, so binding this
        // vid substitutes the body's occurrences consistently.
        let binder_vid = match binder.index_var(kb) {
            Some(Var::Global(vid)) => Some(vid),
            _ => None,
        };

        // The collection's ground `cons`/`nil`/`ListLiteral` spine, read carrier-
        // neutrally (WI-683): a list riding as a `Value::Entity` runtime
        // list, a `Value::Node` occurrence, or a hash-consed term all walk
        // natively — no lowering. σ is chased per spine node (the collection can
        // arrive as a partial `cons(a, ?t)` with `?t` bound elsewhere). `None` ⇒
        // spine not ground ⇒ delay (floundering residual), never silently decided.
        let Some(elements) = Self::bounded_list_elements(kb, &collection, &subst) else {
            return self.delay_goal(depth, delay_mode);
        };

        // body[?x := element_i] for each element, binding only the binder — as a
        // `Substitution` applied by `reify_value` (carrier-faithful, retiring
        // `subst_globals`; the body and elements stay `Value`).
        let per_element: Vec<Vec<Value>> = elements
            .iter()
            .map(|e| {
                let mut map = Substitution::default();
                if let Some(vid) = binder_vid {
                    map.bind_value(kb, vid, e.clone());
                }
                body.iter().map(|g| kb.reify_value(g, &map)).collect()
            })
            .collect();

        if is_forall {
            // Conjunction: flatten all element bodies, prepend, replace frame.
            let frame = self.stack.last().unwrap();
            let mut new_goals: Vec<Value> = per_element.into_iter().flatten().collect();
            new_goals.extend(frame.goals[1..].iter().cloned());
            let new_subst = frame.subst.clone();
            let new_assumed = frame.assumed_facts.clone();
            self.stack.pop();
            self.stack.push(Frame {
                goals: new_goals,
                subst: new_subst,
                depth: depth + 1,
                state: FrameState::Init { delay_mode: delay_mode.reset() },
                assumed_facts: new_assumed,
            });
            Some(StepResult::Continue)
        } else {
            // Disjunction: one Continuation candidate per element; `nil` ⇒ fail.
            if per_element.is_empty() {
                self.stack.pop();
                return Some(StepResult::Continue);
            }
            let candidates: Vec<Candidate> = per_element
                .into_iter()
                .map(Candidate::Continuation)
                .collect();
            let original_goal = self.stack.last().unwrap().goals[0].clone();
            let f = self.stack.last_mut().unwrap();
            f.state = FrameState::ChoicePoint {
                delay_mode,
                original_goal,
                candidates,
                next: 0,
                any_delayed: false,
                child_solutions: 0,
                seen_goals: HashSet::new(),
                cut_barrier: None,
            };
            Some(StepResult::Continue)
        }
    }

    /// Delay the current frame's `goals[0]` — rotate it to the back, entering or
    /// continuing `Delayed` mode so a not-yet-ground goal gets another chance
    /// after its variables may bind. If it is the ONLY goal, residualize it
    /// (WI-519: a floundered residual, skipped under `definite_only`). Mirrors
    /// the builtin delay/rotate path so bounded quantifiers flounder the same way.
    fn delay_goal(&mut self, depth: usize, delay_mode: DelayMode) -> Option<StepResult> {
        let frame = self.stack.last().unwrap();
        let goal_val = frame.goals[0].clone();
        let consecutive = match delay_mode {
            DelayMode::Normal => {
                if frame.goals.len() == 1 {
                    let subst = frame.subst.clone();
                    let residual = vec![goal_val];
                    self.stack.pop();
                    if self.config.definite_only {
                        return Some(StepResult::Continue);
                    }
                    self.record_solution_in_ancestors();
                    return Some(StepResult::YieldSolution(Solution { subst, residual }));
                }
                1
            }
            DelayMode::Delayed { consecutive_delays } => consecutive_delays + 1,
        };
        let mut rotated: Vec<Value> = frame.goals[1..].to_vec();
        rotated.push(goal_val);
        let new_depth = depth + 1;
        let f = self.stack.last_mut().unwrap();
        f.goals = rotated;
        f.depth = new_depth;
        f.state = FrameState::Init {
            delay_mode: DelayMode::Delayed { consecutive_delays: consecutive },
        };
        Some(StepResult::Continue)
    }

    /// If `goal` is a top-level `ho_apply(?P, args…)` whose predicate `?P` walks
    /// to a concrete symbol under σ, return the lowered form `pred_sym(args…)`;
    /// otherwise `None`. Reads `goal` through [`TermView`] (carrier-neutral — a
    /// rule-body `ho_apply` occurrence lowers without a whole-goal reify), and
    /// **creates a term for each argument** via `value_to_term` to build the
    /// lowered `Term::Fn` (rather than splicing pre-interned arg handles). The
    /// single lowering path for both the HoApply-builtin dispatch (a `Value`
    /// goal) and `forall_impl` antecedent lowering (a `TermId`, which is itself a
    /// `TermView`).
    fn lower_ho_apply<V: TermView>(
        kb: &mut KnowledgeBase,
        goal: &V,
        subst: &Substitution,
    ) -> Option<TermId> {
        let pos_arity = match goal.head(kb) {
            ViewHead::Functor { functor: Some(f), pos_arity, .. }
                if kb.resolve_sym(f) == "ho_apply" => pos_arity,
            _ => return None,
        };
        if pos_arity == 0 { return None; }
        // Collect the predicate (arg 0) and args (arg 1…) as raw owned values
        // first — each `pos_arg` borrows `kb`, so this must finish before the
        // `&mut kb` reify/alloc. The args are copied as-is (unwalked), mirroring
        // the original splice.
        let mut raw: SmallVec<[Value; 4]> = SmallVec::new();
        for i in 0..pos_arity {
            raw.push(match goal.pos_arg(kb, i)? {
                ViewItem::Term(t) => Value::term(t),
                ViewItem::Value(v) => v.clone(),
                ViewItem::Node(occ) => Value::Node(occ),
            });
        }
        // The predicate (arg 0) must reduce to a concrete symbol under σ: reify
        // its carrier, then chase the var chain multi-hop through σ via
        // `walk_view` (the carrier-faithful walk the old `walk_arg_term` used, so
        // an ≥2-hop chain resolves the same). A still-unbound var / non-symbol
        // term can't be applied.
        let pred_term = kb.carrier_term(&raw[0])?;
        let pred_sym = match kb.walk_view(pred_term, subst) {
            Value::Term { id, .. } => match kb.terms.get(id) {
                Term::Ref(s) => *s,
                Term::Fn { functor, pos_args: pa, named_args: na, .. }
                    if pa.is_empty() && na.is_empty() => *functor,
                _ => return None,
            },
            _ => return None,
        };
        // Create a term for each argument (a `Value::Node` arg lowers via
        // `occurrence_to_term`, a `Value::Term` unwraps, a scalar allocs a const).
        let mut remaining: SmallVec<[TermId; 4]> = SmallVec::new();
        for a in &raw[1..] {
            remaining.push(node_occurrence::value_to_term(kb, a).ok()?);
        }
        Some(kb.alloc(Term::Fn {
            functor: pred_sym,
            pos_args: remaining,
            named_args: SmallVec::new(),
        }))
    }

    /// Build `__pop_assumption(N)` — a synthetic goal that, when reached
    /// in step_init, drops N entries from the frame's assumed_facts.
    fn make_pop_assumption_marker(kb: &mut KnowledgeBase, n: usize) -> TermId {
        let functor = kb.intern("__pop_assumption");
        let count = kb.alloc(Term::Const(crate::kb::term::Literal::Int(n as i64)));
        kb.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::from_slice(&[count]),
            named_args: SmallVec::new(),
        })
    }

    /// Read both args of a `push_choice(?a, ?b)` goal, walked through σ, as
    /// `(goal_a, goal_b)`. Carrier-neutral (WI-348): the goal is read through
    /// [`TermView`] and each arg is [`Self::walk_arg`]'d to a `Value`, so a
    /// `Value::Node` push_choice goal needs no whole-goal reify and a `Node`
    /// continuation rides through as-is (rather than being lowered to a `TermId`
    /// and re-wrapped) — the [`Self::eq_operands`] idiom. `None` if the goal is
    /// malformed (not a 2-ary, unnamed application). Proposal 033 / WI-075.
    fn resolve_push_choice_args(
        kb: &KnowledgeBase,
        goal: &Value,
        subst: &Substitution,
    ) -> Option<(Value, Value)> {
        match goal.head(kb) {
            ViewHead::Functor { pos_arity: 2, named_arity: 0, .. } => {
                let goal_a = kb.walk_arg(goal.pos_arg(kb, 0), subst)?;
                let goal_b = kb.walk_arg(goal.pos_arg(kb, 1), subst)?;
                Some((goal_a, goal_b))
            }
            _ => None,
        }
    }

    /// If `node` is a cut marker (`anthill.kernel.cut`), return its functor
    /// symbol (proposal 033.1 / WI-568). Detection reuses `get_builtin_view`'s
    /// resolution so it matches exactly how the cut goal is classified when it
    /// later fires; the functor is reused to build the baked `cut(B)` term.
    fn cut_marker_functor(kb: &KnowledgeBase, node: &Rc<NodeOccurrence>) -> Option<Symbol> {
        let v = Value::Node(node.clone());
        if kb.get_builtin_view(&v) == Some(BuiltinTag::Cut) {
            v.head(kb).functor_sym()
        } else {
            None
        }
    }

    /// Build the barrier-carrying cut goal `cut(IntLit(barrier))` — the opened
    /// form of the surface `!` (proposal 033.1 / WI-568). Reuses the marker's own
    /// functor so the baked goal resolves to the same `BuiltinTag::Cut`.
    fn bake_cut_term(kb: &mut KnowledgeBase, cut_sym: Symbol, barrier: i64) -> TermId {
        let lit = kb.alloc(Term::Const(crate::kb::term::Literal::Int(barrier)));
        kb.alloc(Term::Fn {
            functor: cut_sym,
            pos_args: SmallVec::from_elem(lit, 1),
            named_args: SmallVec::new(),
        })
    }

    /// Read the barrier `B` baked into a `cut(B)` goal (proposal 033.1 / WI-568).
    /// The surface `!` is opened to `cut(IntLit(B))` when the enclosing rule body
    /// is entered (`bake_cut_barrier`). Returns `None` for the unbaked nullary
    /// `cut` — a `!` written at query top level with no enclosing rule —
    /// whereupon [`Self::apply_cut`] commits the whole query.
    ///
    /// Carrier-neutral (WI-348): the goal is read through [`TermView`]
    /// (`head` arity gate + `pos_arg`), so a rule-body `!` arriving as a
    /// `Value::Node` occurrence is classified without a whole-goal reify. The
    /// baked barrier is a concrete `IntLit` (never a σ-bound variable), so the arg
    /// head is read directly — no walk — exactly as the former term reader did.
    fn resolve_cut_barrier(kb: &KnowledgeBase, goal: &Value) -> Option<i64> {
        match goal.head(kb) {
            // Unbaked nullary `cut` — a top-level-query `!` with no enclosing rule
            // body to open it. Intentional: `apply_cut(None)` commits the query.
            // (`cut` is a builtin, not a constructor, so it never canonicalizes to
            // the bare `Ref` spelling — the 0-ary `Functor` head is exact.)
            ViewHead::Functor { pos_arity: 0, named_arity: 0, .. } => None,
            // The baked form `cut(IntLit(B))`.
            ViewHead::Functor { pos_arity: 1, named_arity: 0, .. } => {
                match goal.pos_arg(kb, 0) {
                    Some(arg) => match arg.head(kb) {
                        ViewHead::Const(Literal::Int(n)) => Some(n),
                        // A baked cut always carries an Int barrier; any other arg
                        // means a broken lowering, not a recoverable case.
                        _ => {
                            debug_assert!(false, "cut goal argument is not an Int barrier");
                            None
                        }
                    },
                    // Head reports arity 1 but the view can't resolve arg 0 — a
                    // carrier/view desync; surface it loudly rather than skip.
                    None => {
                        debug_assert!(false, "cut goal reports arity 1 but no arg 0");
                        None
                    }
                }
            }
            // Neither nullary nor `cut(IntLit)`: a malformed cut goal.
            _ => {
                debug_assert!(false, "cut goal has an unexpected shape");
                None
            }
        }
    }

    /// Prune the choice-point stack back to the cut barrier (proposal 033.1 /
    /// WI-568). The cut commits to the rule invocation whose choice point is
    /// tagged with `barrier`: that frame's remaining clauses **and** every choice
    /// point stacked above it (created while resolving the goals before the `!`)
    /// are neutralized — `next` advanced past all candidates and the delay-
    /// fallback cleared — so backtracking pops straight through them. The current
    /// (top) frame, where the cut fired, is left intact to continue with the
    /// body's tail. `None` (an unbaked top-level cut) commits to the stack floor.
    ///
    /// Finding the barrier frame by scan, then neutralizing the contiguous
    /// suffix above it, is the WAM "reset B to the cut barrier" reset: the stack
    /// *is* the call-tree spine, so "stacked above the barrier frame" is exactly
    /// "created during this invocation's body". Disjunction transparency falls
    /// out — an `or(...)`'s `push_choice` continuations sit above the frame and
    /// are pruned; a cut inside an inner rule carries that rule's own (higher)
    /// barrier and so never reaches down past it.
    fn apply_cut(&mut self, barrier: Option<i64>) {
        let top = self.stack.len().saturating_sub(1);
        let floor = match barrier {
            Some(b) => self.stack.iter().position(|f| {
                matches!(&f.state, FrameState::ChoicePoint { cut_barrier: Some(cb), .. } if *cb == b)
            }),
            None => Some(0),
        };
        // The barrier frame is always below the cut frame: the `cut(B)` goal
        // flows down the spine from the frame (`F0`) that opened its rule body,
        // and `F0` can't pop while a descendant holding the cut is live. Its
        // absence is a broken invariant, not a recoverable case — assert loudly
        // (caught in tests) rather than silently prune nothing.
        let floor_idx = match floor {
            Some(idx) => idx,
            None => {
                debug_assert!(
                    false,
                    "apply_cut: barrier {barrier:?} has no owning ChoicePoint on the stack"
                );
                return;
            }
        };
        for frame in self.stack[floor_idx..top].iter_mut() {
            if let FrameState::ChoicePoint { next, candidates, any_delayed, .. } = &mut frame.state {
                *next = candidates.len();
                *any_delayed = false;
            }
        }
    }

    /// Recognise `__pop_assumption(N)` and return N, reading through
    /// [`TermView`] so the classification is carrier-neutral — no lowering to a
    /// hash-consed `TermId`. The marker is synthesised as a `Value::Term` (see
    /// `make_pop_assumption_marker`), so it never actually carries a `Value::Node`;
    /// reading it via the view is what lets the marker branch dispatch on `&Value`
    /// directly, before the `reify_goal_value` the term-structured forall/quant
    /// handlers beside it still need. Returns None for anything else.
    fn pop_assumption_arg(kb: &KnowledgeBase, goal: &impl TermView) -> Option<usize> {
        match goal.head(kb) {
            ViewHead::Functor { functor: Some(f), pos_arity: 1, named_arity: 0 }
                if kb.resolve_sym(f) == "__pop_assumption" =>
            {
                match goal.pos_arg(kb, 0)?.head(kb) {
                    ViewHead::Const(Literal::Int(n)) if n >= 0 => Some(n as usize),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// The positional args of a `tuple(...)` application, each as a carrier-
    /// faithful [`Value`] (WI-683). Reads through [`TermView`], so a `Value::Node`
    /// `forall_impl` binder / antecedent / consequent tuple — or a bounded-quant
    /// body tuple — unwraps to its child occurrences without lowering to a term.
    /// Empty vec if the head isn't a `tuple` (`functor_sym` reads the functor off
    /// either the `Fn{tuple}` or the 0-ary `Ref(tuple)` spelling).
    fn unwrap_tuple_args(kb: &KnowledgeBase, goal: &impl TermView) -> Vec<Value> {
        let is_tuple = matches!(
            goal.head(kb).functor_sym(),
            Some(f) if kb.resolve_sym(f) == "tuple"
        );
        if !is_tuple {
            return Vec::new();
        }
        let mut out = Vec::new();
        let mut i = 0;
        while let Some(child) = goal.pos_arg(kb, i) {
            out.push(child.to_value());
            i += 1;
        }
        out
    }

    /// Rotate the current frame's `goals[0]` (a delayed / undecided NAF goal)
    /// behind the rest of the goal list, re-entering `Init` in `Delayed` mode with
    /// the given consecutive-delay count. The single rotate primitive shared by
    /// `step_naf`'s groundness-gate Delay branch (non-ground inner) and its
    /// ground/inner-floundered branch (WI-629). Callers own the counter policy —
    /// `Normal → 1`, `Delayed{n} → n + 1` — so the `consecutive_delays >=
    /// goals.len()` residual gate in [`step_init`] advances and the rotation
    /// terminates; a hard-coded `1` would pin it and spin (WI-629 regression).
    fn rotate_naf_goal_behind_tail(&mut self, goal: &Value, depth: usize, new_consecutive: usize) {
        let f = self.stack.last_mut().unwrap();
        let mut rotated: Vec<Value> = f.goals[1..].to_vec();
        rotated.push(goal.clone());
        f.goals = rotated;
        f.depth = depth + 1;
        f.state = FrameState::Init {
            delay_mode: DelayMode::Delayed { consecutive_delays: new_consecutive },
        };
    }

    fn step_naf(
        &mut self,
        kb: &mut KnowledgeBase,
        goal: &Value,
        depth: usize,
        delay_mode: DelayMode,
    ) -> Option<StepResult> {
        let subst = self.stack.last().unwrap().subst.clone();
        let goals_len = self.stack.last().unwrap().goals.len();

        // Inner goal P of `not(P)`, read through TermView and σ-walked. The
        // groundness gate and sub-resolution read it carrier-faithfully as a
        // `Value` — no lowering to a hash-consed term (WI-348).
        let inner = match goal.pos_arg(kb, 0).and_then(|item| kb.walk_arg(Some(item), &subst)) {
            Some(v) => v,
            None => {
                self.stack.pop();
                return Some(StepResult::Continue);
            }
        };

        // Groundness check: NAF on non-ground goals would be unsound. In the
        // LOCAL-INTERPRETATION query context (proposal 050: the `gamma` overlay is
        // set — only `prove_from_gamma` sets it), a `var_ref(name)` is ALSO treated
        // as non-ground: it is an OPEN-WORLD reference to a runtime binder /
        // parameter whose value is unknown, so `not(eq(b, 0))` over a symbolic
        // parameter must FLOUNDER (delay) rather than succeed by NAF — the
        // soundness contract effect discharge (048 §"constructive refutation") and
        // the in-body proof bridge rely on. Outside a Γ query, `var_ref` is a
        // closed reflect datum and keeps its ordinary ground reading.
        let open_world_param = self.config.gamma.is_some() && kb.value_has_open_world_ref(&inner, &subst);
        if open_world_param || !kb.value_is_ground(&inner, &subst) {
            // Delay — same mechanism as other builtins
            match delay_mode {
                DelayMode::Normal => {
                    if goals_len == 1 {
                        self.stack.pop();
                        // WI-519: a floundered `not(P)` (non-ground inner) is not
                        // a definite solution — skip in definite-only mode.
                        if self.config.definite_only {
                            return Some(StepResult::Continue);
                        }
                        let residual = vec![goal.clone()];
                        self.record_solution_in_ancestors();
                        return Some(StepResult::YieldSolution(Solution { subst, residual }));
                    } else {
                        // First delay of this goal — start the rotation counter at 1.
                        self.rotate_naf_goal_behind_tail(goal, depth, 1);
                        return Some(StepResult::Continue);
                    }
                }
                DelayMode::Delayed { consecutive_delays } => {
                    self.rotate_naf_goal_behind_tail(goal, depth, consecutive_delays + 1);
                    return Some(StepResult::Continue);
                }
            }
        } else {
            // Ground: classify the inner goal P — DEFINITE (P holds → not(P)
            // fails), FLOUNDERED or TRUNCATED (undecided → not(P) undecided), or
            // COMPLETE-empty (P false → not(P) succeeds). `definite_only` is OFF
            // for this sub-search so residuals stay observable for the flounder
            // check (WI-519 three-way + WI-628 truncation).
            let goal_v = kb.reify_value(&inner, &subst);
            let remaining_depth = self.config.max_depth.saturating_sub(depth);
            let sub_config = ResolveConfig {
                max_depth: remaining_depth,
                max_solutions: 0,
                simplify: self.config.simplify,
                definite_only: false,
                // WI-537: the inner `P` of `not(P)` must see Γ too, so a Γ fact
                // proving `P` correctly fails `not(P)` (sound negation under Γ).
                gamma: self.config.gamma.clone(),
            };
            // WI-628: drain the inner search to a three-way verdict that carries
            // `truncated`. A sub-search abandoned at `remaining_depth` proves
            // nothing, so its empty result is UNDECIDED, not a refutation of `P`;
            // folding `truncated` into the floundered branch below is what keeps
            // `not(P)` from silently succeeding on an incomplete search.
            let sub_stream = kb.resolve_lazy_goals(vec![goal_v], &sub_config);
            let v = sub_stream.drain_verdict(kb);

            if v.definite {
                // P has a definite solution → P holds → not(P) FAILS — backtrack.
                self.stack.pop();
                return Some(StepResult::Continue);
            } else if v.residual || v.truncated {
                // P FLOUNDERED (a residual, no definite solution) OR its search
                // TRUNCATED at the depth limit (WI-628) → P is undecided, so
                // `not(P)` is undecided too: it must NOT silently succeed (the old
                // `is_some()` treated a residual as "P holds" and made `not`
                // wrongly FAIL; reading a TRUNCATED empty search as refutation
                // makes `not` wrongly SUCCEED — the WI-628 hole). Propagate the
                // undecidedness as a residual `not(P)` — or skip it in
                // definite-only mode (a floundered goal is not a definite
                // solution). WI-519.
                //
                // WI-628(b): if the inner search TRUNCATED, taint the OUTER stream
                // so the eager consumers see it. This is load-bearing under
                // `definite_only`: the frame below is skipped WITHOUT yielding a
                // residual, so the sub-stream's local `truncated` (dropped with
                // `v`) would otherwise vanish — a nested `not(Q)` truncation would
                // be invisible and a forall/negation/count guard would read the
                // outer `is_empty()` as a refutation. `drain_all` snapshots this
                // onto the returned stats. (Fold only `truncated`, not `residual`:
                // a flounder is surfaced as its own residual `not(P)`, below.)
                self.truncated |= v.truncated;
                //
                // WI-629: but the frame may still hold TAIL goals. Yielding a bare
                // `residual:[not(P)]` here DROPS `goals[1..]` — the conjunction
                // reads satisfied-modulo-residual while a conjunct was never
                // attempted. Mirror the groundness-gate Delay branch above: when a
                // tail exists, ROTATE the undecided `not(P)` behind it so the
                // resolvable conjuncts still run (the eventual residual then
                // honestly carries every undischarged goal via the delay-exhaustion
                // yield in `step_init`, and the rotation terminates because a
                // still-floundering `not(P)` re-enters here as the sole goal, or
                // `consecutive_delays` reaches `goals.len()`).
                if self.config.definite_only {
                    // A floundered/truncated `not(P)` can never be discharged
                    // DEFINITELY, and `P` is GROUND here (the `else`/ground branch)
                    // so re-resolving after the tail binds nothing stays undecided
                    // (a truncated search only loses budget as depth grows) — the
                    // whole conjunction is non-definite regardless of the tail.
                    // Skip the frame outright (no rotation, no residual yield).
                    // WI-519 / WI-628.
                    self.stack.pop();
                    return Some(StepResult::Continue);
                }
                if goals_len == 1 {
                    // `not(P)` is the sole goal — the residual `[not(P)]` is the
                    // honest whole-query answer.
                    self.stack.pop();
                    let residual = vec![goal.clone()];
                    self.record_solution_in_ancestors();
                    return Some(StepResult::YieldSolution(Solution { subst, residual }));
                } else {
                    // Rotate the undecided `not(P)` behind the tail — but THREAD the
                    // incoming `delay_mode` into the counter (like the groundness-gate
                    // Delayed branch above), NOT a hard `1`. A ground-floundering
                    // `not()` routes ONLY through here, never the generic incrementing
                    // delay path, so a hard `1` would pin the counter and a conjunction
                    // of ≥2 ground-floundering `not()`s would rotate forever without
                    // ever reaching the `consecutive_delays >= goals.len()` residual
                    // gate in `step_init` (it would burn to the depth limit and return
                    // NO solution — the exact verdict dishonesty WI-629 fixes).
                    let new_consecutive = match delay_mode {
                        DelayMode::Normal => 1,
                        DelayMode::Delayed { consecutive_delays } => consecutive_delays + 1,
                    };
                    self.rotate_naf_goal_behind_tail(goal, depth, new_consecutive);
                    return Some(StepResult::Continue);
                }
            } else {
                // P has no solution and the search was COMPLETE (not truncated,
                // not floundered) → P is genuinely false → not(P) SUCCEEDS.
                let new_delay = delay_mode.reset();
                let f = self.stack.last_mut().unwrap();
                let new_goals = f.goals[1..].to_vec();
                f.goals = new_goals;
                f.subst = subst;
                f.depth = depth + 1;
                f.state = FrameState::Init { delay_mode: new_delay };
                return Some(StepResult::Continue);
            }
        }
    }

    /// Handle a frame in `ChoicePoint` state — try the next candidate.
    fn step_choice_point(&mut self, kb: &mut KnowledgeBase) -> Option<StepResult> {
        let frame = self.stack.last().unwrap();
        let (delay_mode, original_goal, next, candidates_len, any_delayed, child_solutions) =
            match &frame.state {
                FrameState::ChoicePoint {
                    delay_mode,
                    original_goal,
                    next,
                    candidates,
                    any_delayed,
                    child_solutions,
                    ..
                } => (
                    delay_mode.clone(),
                    original_goal.clone(),
                    *next,
                    candidates.len(),
                    *any_delayed,
                    *child_solutions,
                ),
                _ => unreachable!(),
            };

        // All candidates exhausted
        if next >= candidates_len {
            if child_solutions == 0 && any_delayed {
                // Delay fallback: rotate goal to end, push new Init frame
                let goals = &frame.goals;
                let mut rotated: Vec<Value> = goals[1..].to_vec();
                rotated.push(original_goal.clone());
                let new_depth = frame.depth + 1;
                let new_subst = frame.subst.clone();
                let new_consecutive = match &delay_mode {
                    DelayMode::Normal => 1,
                    DelayMode::Delayed { consecutive_delays } => consecutive_delays + 1,
                };
                let inherited = frame.assumed_facts.clone();
                self.stack.pop();
                self.stack.push(Frame {
                    goals: rotated,
                    subst: new_subst,
                    depth: new_depth,
                    state: FrameState::Init {
                        delay_mode: DelayMode::Delayed {
                            consecutive_delays: new_consecutive,
                        },
                    },
                    assumed_facts: inherited,
                });
                return Some(StepResult::Continue);
            }
            // Backtrack — pop this frame
            self.stack.pop();
            return Some(StepResult::Continue);
        }

        // Extract candidate data
        let candidate = {
            let frame = self.stack.last().unwrap();
            match &frame.state {
                FrameState::ChoicePoint { candidates, next, .. } => {
                    candidates[*next].clone()
                }
                _ => unreachable!(),
            }
        };

        // Advance `next` in the current frame
        {
            let frame = self.stack.last_mut().unwrap();
            match &mut frame.state {
                FrameState::ChoicePoint { next, .. } => *next += 1,
                _ => unreachable!(),
            }
        }

        // Continuation inherits parent σ unchanged — no head match, so no
        // new bindings to merge and no walk of the tail to perform. See
        // proposal 033 §"TermId / Value asymmetry" for why σ is omitted
        // from the variant.
        if let Candidate::Continuation(body) = candidate {
            let frame = self.stack.last().unwrap();
            let tail = &frame.goals[1..];
            let mut new_goals: Vec<Value> = Vec::with_capacity(body.len() + tail.len());
            new_goals.extend(body);
            new_goals.extend(tail.iter().cloned());
            self.stack.push(Frame {
                goals: new_goals,
                subst: frame.subst.clone(),
                depth: frame.depth + 1,
                state: FrameState::Init { delay_mode: delay_mode.reset() },
                assumed_facts: frame.assumed_facts.clone(),
            });
            return Some(StepResult::Continue);
        }

        // Extract components from candidate
        let (opt_rid, tree_subst) = match candidate {
            Candidate::Rule(rid, subst) => (Some(rid), subst),
            Candidate::Assumption(subst) => (None, subst),
            Candidate::ExternalRow(subst) => (None, subst),
            Candidate::Continuation(_) => unreachable!("handled above"),
        };

        // WI-512: a NON-LINEAR goal atom (a query var repeated within one atom,
        // e.g. `edge(from: ?n, to: ?n)`) binds that var to two different fact
        // subterms during the discrim match — the tree indexes each var position
        // independently (it is a linear index), so it cannot enforce the repeat.
        // `resolve_leaf` UNIFIES the two values (WI-633; ground-vs-ground this
        // is the old structural-identity check) and records a genuine mismatch
        // as `is_contradiction()`; a contradictory candidate is a FALSE match,
        // so drop it rather than count it as a solution.
        if tree_subst.is_contradiction() {
            return Some(StepResult::Continue);
        }

        // A GROUND arity-0 fact (empty body, no De Bruijn vars, no Global head
        // vars) or a non-rule candidate (external row / no rid). Two kinds of
        // bodyless-but-non-ground head must NOT take the fact fast-path, because
        // the raw bind below would leak an unfreshened head var into σ:
        //  - arity > 0: its `tree_subst` carries raw `Var(DeBruijn)` head subterms
        //    and synthetic `u32::MAX - n` entries (WI-624 — the nonlinear head
        //    `unbox(box(v: ?v), ?v)` answered `Var(DeBruijn(0))`).
        //  - arity == 0 with a non-ground head carrying live `Var::Global`s (the
        //    loader's omitted-field fresh fills, or a value fact whose children
        //    carry Globals): raw-binding leaks the fact's PERSISTENT VarId, so two
        //    goals matching the same fact alias one vid and constraining them
        //    differently spuriously fails (WI-635).
        // Both route through `with_fresh_vars` like any rule (the arity-0 legacy
        // path freshens Global head vars, carrier-neutrally); a fact's body is
        // just empty. `rule_head_has_vars` reads the head's `Var::Global`s cached
        // at assert, so this stays an O(1) gate — no per-match head walk (the
        // workitem fact set is large).
        let is_fact = opt_rid.map_or(true, |rid| {
            kb.is_fact(rid) && kb.rule_arity(rid) == 0 && !kb.rule_head_has_vars(rid)
        });

        let frame = self.stack.last().unwrap();

        if is_fact {
            // Ground fact (occurrence or rule with empty body, or
            // ExternalRow from a routed-store backend).
            //
            // [WI-030] No eager apply_subst_each here — bindings from this
            // match enter `frame.subst` via `bind_compressed` below, and
            // remaining goals are lazily walked at selection time in
            // `step_init`.
            let remaining = frame.goals[1..].to_vec();
            let mut merged = frame.subst.clone();
            // bind_compressed wants (VarId, TermId) pairs; filter to the
            // Value::Term subset — path compression is TermId-only.
            // WI-502 Step 2/5: this is the `Value::Term` fact-bind path; it goes
            // through `bind_compressed` (loud-asserts on a constrained var), NOT
            // `bind_waking`. Harmless today (no resolver-side constraint producer
            // until Step 3), but when Step 5 makes Type constraints live, a
            // constrained query var binding to a concrete fact term here will trip
            // the loud guard — Step 5 must route this path through `bind_waking`
            // (or add the per-kind check) so it wakes/suspends instead of panics.
            // Same applies to the rule branch's `answer_links` bind_compressed
            // below (post-WI-624 that branch also serves bodyless rules).
            let term_pairs: Vec<(VarId, TermId)> = tree_subst.iter_terms().collect();
            merged.bind_compressed(term_pairs.into_iter(), &kb.terms);
            // Non-Term bindings (`Value::Entity` from external rows, etc.)
            // bypass path compression and bind directly. This is the
            // proposal 026.1 §"Lineage-preserving bindings" guarantee:
            // an external row enters σ as its raw `Value` shape.
            for (vid, val) in tree_subst.iter() {
                if !matches!(val, Value::Term { .. }) {
                    // WI-649: occurs-check this external-row / value-fact carrier
                    // before it enters σ. The hot term fast-path
                    // (`bind_compressed` above) stays unchecked; this rare
                    // non-`Term` bind is the one route by which a cyclic entity
                    // sigma (`?v ↦ Entity{…?v…}` — a routed-store row that
                    // references the goal's own query var) could form and later
                    // overflow `reify_value`'s now-deep (WI-629) child recursion.
                    //
                    // Mirror `unify_bind` (the reference occurs-check) exactly:
                    // chase `val`'s head through `merged` first, THEN distinguish
                    // two var-headed outcomes the raw `occurs_in_value` conflates.
                    // If the chased head IS `vid`, the bind is a vacuous variable
                    // equivalence — `?v = ?v`, or `?v ↦ ?w` when σ already aliases
                    // `?w → …→ ?v` — already encoded in σ, NOT a structural cycle;
                    // binding the raw carrier would only add a degenerate alias
                    // loop that reify_value's var-chase would spin on, so skip it
                    // (like `unify_bind`'s `?v <=> ?v → Ok`) and keep the
                    // candidate. Otherwise a positive `occurs_in_value` (which
                    // chases `merged`, so it also catches mutual cycles across
                    // bindings) means `vid` occurs inside `val`'s STRUCTURE: a real
                    // occurs-failure (no finite term satisfies `?v = f(?v)`). Drop
                    // the candidate as contradictory — the WI-624 answer_link move
                    // (a false match, not a solution). σ stays acyclic inductively,
                    // so neither `chase_value` nor `occurs_in_value` diverges.
                    let head = kb.chase_value(val.clone(), &merged);
                    if kb.unify_flex_var(&head) == Some(*vid) {
                        continue;
                    }
                    if kb.occurs_in_value(*vid, &head, &merged) {
                        return Some(StepResult::Continue);
                    }
                    // WI-502 Step 2 — route through the waking choke-point so a
                    // constraint on `vid` (in the accumulating σ) wakes rather
                    // than being silently bound over. (No-op until Step 3's
                    // producer; `tree_subst` itself is freshly built per match,
                    // so it carries no constraints — only `merged`/σ might.)
                    merged.bind_waking(kb, *vid, val.clone());
                }
            }
            let new_delay = delay_mode.reset();
            let inherited = frame.assumed_facts.clone();
            self.stack.push(Frame {
                goals: remaining,
                subst: merged,
                depth: frame.depth + 1,
                state: FrameState::Init { delay_mode: new_delay },
                assumed_facts: inherited,
            });
        } else {
            // Rule with body
            let rid = opt_rid.unwrap();
            // `fresh_nodes` is the occurrence body pushed as `Value::Node`
            // goals; it also drives the caller-var delay pre-check below
            // (WI-246 — the term body is no longer built or consulted here).
            let (fresh_nodes, answer_links) = kb.with_fresh_vars(rid, &tree_subst);
            // WI-624: `with_fresh_vars` flags an occurs violation (a query
            // var whose head-match link would contain itself) as a
            // contradiction — a FALSE match, exactly like a contradictory
            // `tree_subst` above. Drop the candidate.
            if answer_links.is_contradiction() {
                return Some(StepResult::Continue);
            }
            // [WI-030] No eager apply_subst_each here. The body itself is
            // already concretised through `body_rename` inside
            // `with_fresh_vars`, and caller-side bindings flow into
            // `frame.subst` via the `bind_compressed` call below; remaining
            // goals are walked lazily in `step_init`.
            let remaining = frame.goals[1..].to_vec();

            // Sole consumer is the delay pre-check over the body — statically
            // moot for the empty body of a rerouted bodyless rule (WI-624),
            // so skip the collection walk there.
            let caller_fresh_vars: Vec<VarId> = if fresh_nodes.is_empty() {
                Vec::new()
            } else {
                answer_links
                    .iter_terms()
                    .filter_map(|(_, tid)| match kb.terms.get(tid) {
                        Term::Var(Var::Global(vid)) => Some(*vid),
                        _ => None,
                    })
                    .collect()
            };

            let mut merged = frame.subst.clone();
            // Path compression over the answer links. `answer_links` is Term-only
            // *by construction* — with_fresh_vars writes every entry via `.bind`
            // (→ `Value::Term`), never `bind_value`/`bind_waking` — so `iter_terms`
            // captures all of it. (Contrast the fact fast-path above, whose
            // external-row `tree_subst` carries raw non-Term values and so needs a
            // `bind_waking` loop. WI-636's completeness fix — reify a non-Term
            // head-match carrier into the links, or drop the whole candidate when
            // un-reifiable — lives at the source in `with_fresh_vars`, not here.)
            // Assert the construction invariant so a future edit that writes a
            // non-Term into this row (which `iter_terms` would then silently drop)
            // trips loudly in test/dev.
            debug_assert!(
                answer_links.iter().all(|(_, v)| matches!(v, Value::Term { .. })),
                "answer_links must be Term-only by construction; a non-Term entry \
                 would be silently dropped by iter_terms (WI-636)",
            );
            let link_pairs: Vec<(VarId, TermId)> = answer_links.iter_terms().collect();
            merged.bind_compressed(link_pairs.into_iter(), &kb.terms);

            // Pre-check: delay propagation on caller vars (over the occurrence body)
            if !caller_fresh_vars.is_empty()
                && kb.body_builtins_delay_on_caller_vars_nodes(&fresh_nodes, &caller_fresh_vars, &merged)
            {
                let f = self.stack.last_mut().unwrap();
                match &mut f.state {
                    FrameState::ChoicePoint { any_delayed, .. } => *any_delayed = true,
                    _ => unreachable!(),
                }
                return Some(StepResult::Continue);
            }

            // Capture what the push still needs from `frame` before the
            // `self`-mut barrier-tagging below ends its borrow.
            let parent_depth = frame.depth;
            let inherited = frame.assumed_facts.clone();
            let new_delay = delay_mode.reset();

            // Cut baking (proposal 033.1 / WI-568). A body conjunct is a separate
            // `fresh_nodes` entry, so a top-level `!` is detected here directly.
            // (A cut nested inside an argument term — e.g. a hand-written
            // `or((g, !), h)` — is not baked here; the supported surface form is
            // the conjunct `!` that `once` / if-then-else and priority rules
            // expand to.) Cut-ness is a static property of the rule, so the scan
            // runs once per rule and is cached (cut-free rules — the vast
            // majority — then skip it).
            // An empty body (rerouted bodyless rule, WI-624) can't carry a cut
            // marker — skip the cache probe entirely.
            let cut_functor = if fresh_nodes.is_empty() {
                None
            } else {
                match self.cut_cache.get(&rid) {
                    Some(&cached) => cached,
                    None => {
                        let detected =
                            fresh_nodes.iter().find_map(|n| Self::cut_marker_functor(kb, n));
                        self.cut_cache.insert(rid, detected);
                        detected
                    }
                }
            };

            // WI-246: opened rule-body atoms enter the goal stream as
            // `Value::Node` occurrences (carrying any typer dot-rewrites),
            // matched/resolved through `TermView` — no lowering to terms. A cut
            // marker is the exception: it is baked to a `Value::Term(cut(B))` so
            // it carries the barrier down the spine wherever the goal flows.
            let mut new_goals: Vec<Value> = Vec::with_capacity(fresh_nodes.len() + remaining.len());
            match cut_functor {
                Some(cut_sym) => {
                    // Allocate a fresh barrier, tag the opening choice point (the
                    // current frame `F0`) with it, then bake it into every cut
                    // marker. All cuts in one body share `B` — they commit to the
                    // same invocation.
                    let barrier = self.next_barrier;
                    self.next_barrier += 1;
                    if let FrameState::ChoicePoint { cut_barrier, .. } =
                        &mut self.stack.last_mut().unwrap().state
                    {
                        *cut_barrier = Some(barrier);
                    }
                    let baked = Self::bake_cut_term(kb, cut_sym, barrier);
                    for n in fresh_nodes {
                        if Self::cut_marker_functor(kb, &n).is_some() {
                            new_goals.push(Value::term(baked));
                        } else {
                            new_goals.push(Value::Node(n));
                        }
                    }
                }
                None => new_goals.extend(fresh_nodes.into_iter().map(Value::Node)),
            }
            new_goals.extend(remaining);
            self.stack.push(Frame {
                goals: new_goals,
                subst: merged,
                depth: parent_depth + 1,
                state: FrameState::Init { delay_mode: new_delay },
                assumed_facts: inherited,
            });
        }

        Some(StepResult::Continue)
    }

    /// Check if a solution is a duplicate by **structurally fingerprinting** the
    /// nearest ancestor ChoicePoint's goal through the solution σ (WI-348). The
    /// fingerprint (`goal_fingerprint`) reads the goal through `TermView`, so it
    /// is carrier-agnostic: a `Value::Node` answer keys by its structure, with
    /// no `TermId` materialization and no `TermStore` growth.
    ///
    /// Skipped when σ carries a binding with no structural fingerprint — a
    /// genuinely external-row / opaque value (`Value::Str`/`Value::Entity` from
    /// a stream, a closure). A `Value::Node` does NOT disable dedup (it
    /// fingerprints structurally); only those opaque rows do, which would
    /// otherwise collapse genuinely distinct rows to one key.
    fn is_duplicate_projection(&mut self, kb: &mut KnowledgeBase, sol: &Solution) -> bool {
        let has_value_binding = sol.subst.iter()
            .any(|(_, v)| !matches!(v, Value::Term { .. } | Value::Node(_)));
        if has_value_binding {
            return false;
        }
        for frame in self.stack.iter_mut().rev() {
            if let FrameState::ChoicePoint { original_goal, seen_goals, .. } = &mut frame.state {
                // Carrier-agnostic structural fingerprint of the goal reified
                // through σ — keys a `Value::Node` answer by its structure, with
                // no `TermId` materialization and no `TermStore` growth (WI-348).
                let key = goal_fingerprint(kb, &*original_goal, &sol.subst);
                return !seen_goals.insert(key);
            }
        }
        false // no ChoicePoint ancestor — no dedup
    }

    /// When yielding a solution, walk the stack to find the nearest
    /// `ChoicePoint` ancestor and increment its `child_solutions` counter.
    fn record_solution_in_ancestors(&mut self) {
        for frame in self.stack.iter_mut().rev() {
            if let FrameState::ChoicePoint { child_solutions, .. } = &mut frame.state {
                *child_solutions += 1;
                return;
            }
        }
    }
}

/// WI-483: walk an op-body occurrence and bind every param-named var to its
/// call arg in `fold`. WI-487 mints a fresh `VarId` per param occurrence (all
/// sharing the param Symbol), so this collects them ALL — matching by the
/// interned param Symbol (`vid.name()`), the by-symbol fold. Vars not naming a
/// param are left unbound (`substitute_occurrence` keeps them as var leaves).
///
/// This is NOT scope-aware: a `let`/`lambda`/`match` binder that SHADOWS a param
/// name would be wrongly bound here. That is currently harmless because any body
/// introducing such a binder is an `Expr::Let`/`Lambda`/`Match` node, which does
/// not reduce to a value (COMPLEX) and so the folded result is discarded — no
/// wrong value escapes. If foldability is ever extended to bodies with binders,
/// this walk must become scope-aware (stop descending past a shadowing binder).
fn collect_param_var_bindings(
    kb: &KnowledgeBase,
    occ: &Rc<NodeOccurrence>,
    param_args: &HashMap<Symbol, Value>,
    fold: &mut Substitution,
) {
    let Some(expr) = occ.as_expr() else { return };
    if let Expr::Var(Var::Global(vid)) = expr {
        if let Some(arg) = param_args.get(&vid.name()) {
            fold.bind_value(kb, *vid, arg.clone());
        }
    }
    node_occurrence::for_each_child(expr, |c| collect_param_var_bindings(kb, c, param_args, fold));
}

// ── SLD Resolution ──────────────────────────────────────────────

/// The resolver's firing strategy for the shared iterative simp driver
/// ([`super::simp_rewrite::rewrite`], WI-641 Phase 2 / WI-643): fire carrier-
/// neutrally via [`KnowledgeBase::fire_simp_equation`] under the frame subst,
/// recording each firing as an `EqChange`. Replaces the former recursive
/// `apply_eq_rules_occurrence` walk (WI-641) AND the recursive TERM walk
/// (WI-643) — the driver descends BOTH carriers iteratively, so a deeply-nested
/// redex (Node or term) can't overflow. `fire_simp_equation` already fires
/// carrier-neutrally over a `&Value`, so this firer is identical for both.
struct ResolverSimpFirer<'a> {
    subst: &'a Substitution,
    changes: &'a mut Vec<EqChange>,
}

impl super::simp_rewrite::SimpFirer for ResolverSimpFirer<'_> {
    fn fire(&mut self, kb: &mut KnowledgeBase, redex: &Value, rids: &[RuleId]) -> Option<Value> {
        let (rid, rewritten) = kb.fire_simp_equation(redex, self.subst, rids)?;
        self.changes.push(EqChange {
            rule_id: rid,
            original: redex.clone(),
            rewritten: rewritten.clone(),
        });
        Some(rewritten)
    }
}

/// WI-682: the σ-applied arg1 pattern of an occurrence reflect builtin, kept
/// carrier-faithful. A genuine hash-consed pattern (arg1 was a `Term` /
/// `Value::Term`) routes through the fast [`KnowledgeBase::match_view`]; a
/// `Value::Node` occurrence pattern STAYS a Node and routes through the
/// carrier-neutral [`KnowledgeBase::match_view_value_pattern`] (WI-683) — no
/// reification, so the occurrence keeps its identity/span. Built by
/// [`KnowledgeBase::occurrence_arg_and_pattern`], consumed via
/// [`KnowledgeBase::match_occ_pattern`].
enum OccPattern {
    Term(TermId),
    Node(Value),
}

/// WI-689 — the ONE generic structural fold that the sem-eq / groundness "gates"
/// reduce to, retiring the former per-carrier + per-gate twin split (8 helpers
/// that hand-rolled the SAME `TermView` recursion skeleton, differing only in a
/// few axes). It is the ONE-view analog of the two-view
/// [`views_structurally_equal`](super::term_view::views_structurally_equal): a
/// single walk over any [`TermView`] carrier (`Term` / `Value` / `Node` /
/// `Entity` / `Tuple`), so a hypothetical NEW value carrier needs NO new per-gate
/// arm — it rides the view like every other. Each gate is a thin predicate over a
/// [`KnowledgeBase::fold_gate`] call parameterized by this spec.
///
/// The axes the gates differ on:
/// * `combine` — how child verdicts fold (`All` for groundness, `Any` for the
///   "reaches …" scans), which also fixes the empty-children (pure-leaf) verdict.
/// * `chase_sigma` — whether a `Var(Global)` head is resolved through σ (the
///   dispatch-time gates chase; the structural gates read already-reduced values).
/// * `head_check` — an optional head-level short-circuit ([`HeadCheck`]).
/// * `opaque` — the verdict for an [`ViewHead::Opaque`] carrier (normally the
///   combine identity; `has_bodied_op_call` conservatively declines with `true`).
/// * `depth_cap` — an optional `(cap, verdict-at-cap)` bound (only the
///   `reaches_eq_override` scan caps, conservatively `true` at 256).
#[derive(Clone, Copy)]
pub(crate) struct GateSpec {
    combine: Combine,
    chase_sigma: bool,
    head_check: HeadCheck,
    opaque: bool,
    depth_cap: Option<(usize, bool)>,
}

/// How a [`GateSpec`] folds child verdicts — and, for a pure leaf with no child,
/// its identity element (`All` ⇒ `true`, `Any` ⇒ `false`).
#[derive(Clone, Copy)]
enum Combine {
    /// Every child must hold (groundness) — short-circuits `false`.
    All,
    /// Some child must hold (the "reaches …" scans) — short-circuits `true`.
    Any,
}

/// The head-level short-circuit a gate applies before recursing into children.
/// Each reads only the head's `ViewHead` plus the KB's classification tables, so a
/// gate is a fixed, `&self`-free predicate (the whole point of the unification —
/// adding a value carrier can no longer silently omit an arm).
#[derive(Clone, Copy)]
enum HeadCheck {
    /// No head short-circuit — always recurse (deep groundness).
    AlwaysRecurse,
    /// WI-616: the head functor is an eq-dispatch-index carrier (overrides `eq`),
    /// read off either the `Functor` or the canonical bare-`Ref` spelling.
    EqOverride,
    /// WI-580/690: the head is a bodied (non-builtin) operation call — read off the
    /// raw `Functor` functor ONLY (a bare `Ref` is a 0-ary constructor, never a
    /// bodied op, so it takes the recurse-over-no-children path to the identity).
    BodiedOpCall,
    /// WI-664: the head is a `Float` leaf (an unshielded partial carrier) or a
    /// sort/constructor whose precomputed per-constructor NonEq classification
    /// decides in O(1) and STOPS (it already stopped at lawful-Eq boundaries, so
    /// its fields are not re-walked); a functor-less aggregate walks its fields.
    PartialCarrier,
}

/// The outcome of a [`HeadCheck`] at a node: a definite short-circuit verdict, or
/// "descend into the children".
enum HeadVerdict {
    Stop(bool),
    Recurse,
}

/// Reach-scan depth cap (WI-616): a buried-override scan on a pathologically deep
/// value conservatively reports "reaches" at this depth rather than recursing
/// unboundedly. Only [`REACHES_EQ_OVERRIDE`] caps.
const REACH_DEPTH_CAP: usize = 256;

/// WI-616 — deep groundness: no unbound variable anywhere inside a σ-walked value.
pub(crate) const DEEP_GROUND: GateSpec = GateSpec {
    combine: Combine::All,
    chase_sigma: true,
    head_check: HeadCheck::AlwaysRecurse,
    // A runtime handle (`Map`/`Closure`/…) has no unbound var leaf — ground.
    opaque: true,
    depth_cap: None,
};

/// WI-616 — does the value structurally CONTAIN an eq-dispatch-override carrier?
pub(crate) const REACHES_EQ_OVERRIDE: GateSpec = GateSpec {
    combine: Combine::Any,
    chase_sigma: true,
    head_check: HeadCheck::EqOverride,
    // An opaque carrier overrides nothing reachable here.
    opaque: false,
    depth_cap: Some((REACH_DEPTH_CAP, true)),
};

/// WI-580/690 — does the value structurally CONTAIN a bodied (non-builtin) op-call?
pub(crate) const HAS_BODIED_OP_CALL: GateSpec = GateSpec {
    combine: Combine::Any,
    chase_sigma: false,
    head_check: HeadCheck::BodiedOpCall,
    // An opaque carrier we cannot decompose MIGHT hide a bodied op-call — decline
    // (conservatively `true`) rather than structurally unify a form we can't inspect.
    opaque: true,
    depth_cap: None,
};

/// WI-664 — does the value reach an UNSHIELDED partial (Float) carrier?
pub(crate) const REACHES_PARTIAL_CARRIER: GateSpec = GateSpec {
    combine: Combine::Any,
    chase_sigma: false,
    head_check: HeadCheck::PartialCarrier,
    opaque: false,
    depth_cap: None,
};

impl HeadCheck {
    /// The head-level short-circuit for this gate — reads the head and the KB's
    /// classification tables only.
    fn classify(self, kb: &KnowledgeBase, head: &ViewHead) -> HeadVerdict {
        match self {
            HeadCheck::AlwaysRecurse => HeadVerdict::Recurse,
            HeadCheck::EqOverride => match head.functor_sym() {
                Some(s) if kb.eq_dispatch_target(s).is_some() => HeadVerdict::Stop(true),
                _ => HeadVerdict::Recurse,
            },
            HeadCheck::BodiedOpCall => match head {
                ViewHead::Functor { functor: Some(f), .. }
                    if kb.builtins.get(f).is_none() && kb.op_body_node(*f).is_some() =>
                {
                    HeadVerdict::Stop(true)
                }
                _ => HeadVerdict::Recurse,
            },
            HeadCheck::PartialCarrier => {
                // A `Float` literal read carrier-neutrally through the view (a bare
                // `Value::Float`, a `Value::Term(Const)`, a Node float-literal).
                if matches!(head, ViewHead::Const(Literal::Float(_))) {
                    return HeadVerdict::Stop(true);
                }
                match head.functor_sym() {
                    // A sort/constructor head reads the O(1) per-constructor NonEq
                    // classification and STOPS (no descent into a shielded field).
                    Some(f) => HeadVerdict::Stop(kb.field_wise_noneq_carriers.contains(&f)),
                    // A functor-less aggregate (tuple/unit) has no sort to key on.
                    None => HeadVerdict::Recurse,
                }
            }
        }
    }
}

impl KnowledgeBase {
    /// Create a lazy search stream for the given goals. Representation-neutral
    /// (WI-349): a goal is anything that implements [`TermView`] — the same
    /// read-through-any-carrier abstraction the matcher and discrimination tree
    /// already speak — so a `TermId` ground pattern, a `Value`, or a
    /// `Value::Node` occurrence goal all go through one door, with no term-only
    /// entry point. Each goal is captured into the owned `Vec<Value>` goal list
    /// (the mutable search frame needs ownership) via its `as_bind_value`.
    /// [`Self::resolve_lazy_goals`] is the canonical `Vec<Value>` core.
    pub fn resolve_lazy<V: TermView>(&self, goals: &[V], config: &ResolveConfig) -> SearchStream {
        let value_goals = goals.iter().map(|g| bind_value_to_value(g.as_bind_value())).collect();
        self.resolve_lazy_goals(value_goals, config)
    }

    /// Like [`Self::resolve_lazy`] but takes pre-built `Value` goals — e.g. the
    /// `Value::Node` occurrence goals from [`Self::with_fresh_vars`], so a
    /// caller resolving an occurrence body need not lower it to terms first.
    /// `resolve_lazy` is the thin `&[TermId]` → `Value::Term` wrapper over this.
    pub fn resolve_lazy_goals(&self, goals: Vec<Value>, config: &ResolveConfig) -> SearchStream {
        let initial_frame = Frame {
            goals,
            subst: Substitution::new(),
            depth: 0,
            state: FrameState::Init { delay_mode: DelayMode::Normal },
            assumed_facts: Vec::new(),
        };
        SearchStream {
            stack: vec![initial_frame],
            config: ResolveConfig {
                max_depth: config.max_depth,
                max_solutions: config.max_solutions,
                simplify: config.simplify,
                // WI-519: thread the residual-honesty mode into the stream's
                // config so the step functions skip floundered yields.
                definite_only: config.definite_only,
                // WI-537: the Γ overlay rides into the stream so `step_init`'s
                // candidate step can consult it (an `Rc` clone — a refcount bump).
                gamma: config.gamma.clone(),
            },
            query_cache: HashMap::new(),
            stats: ResolveStats::default(),
            next_barrier: 0,
            cut_cache: HashMap::new(),
            truncated: false,
        }
    }

    /// Resolve a list of goals using SLD resolution. Representation-neutral
    /// (WI-349): a goal is anything that implements [`TermView`] — a `TermId`
    /// ground pattern, a `Value`, or a `Value::Node` occurrence goal — so an
    /// occurrence query (carrying source spans) and a term query go through the
    /// same door.
    ///
    /// Returns all solutions (up to `config.max_solutions`) that satisfy all
    /// goals simultaneously. Each solution contains variable bindings from
    /// the original query variables.
    pub fn resolve<V: TermView>(&mut self, goals: &[V], config: &ResolveConfig) -> Vec<Solution> {
        self.resolve_with_stats(goals, config).0
    }

    /// Resolve pre-built `Value` goals by value — the canonical `Vec<Value>`
    /// core that the slice front doors ([`Self::resolve`]) coerce into. Handy
    /// when a caller already owns a `Vec<Value>` (e.g. the `Value::Node`
    /// occurrence goals from [`Self::with_fresh_vars`]). Named `_goals` (not
    /// `_value`) to avoid colliding with the subst-layer `resolve_as_value` (a
    /// variable→binding lookup, an unrelated operation).
    pub fn resolve_goals(&mut self, goals: Vec<Value>, config: &ResolveConfig) -> Vec<Solution> {
        self.resolve_goals_with_truncation(goals, config).0
    }

    /// WI-628 — like [`Self::resolve_goals`] but also reports whether the search
    /// TRUNCATED at the depth limit. An empty (or, for a count, short) result
    /// from a truncated search is UNDECIDED, never a refutation, so the eager
    /// constraint / quantifier guards (`eval_negation_guard` / `eval_forall_guard`
    /// / `eval_count_guard`) consult this before reading `is_empty()` / a count as
    /// a verdict — raising a loud "undecidable within depth budget" rather than
    /// silently deciding from an incomplete search. Drains via
    /// [`SearchStream::drain_all`], which keeps the stream alive past exhaustion
    /// so the flag survives (the plain `split_first` loop dropped it).
    pub fn resolve_goals_with_truncation(
        &mut self,
        goals: Vec<Value>,
        config: &ResolveConfig,
    ) -> (Vec<Solution>, bool) {
        let stream = self.resolve_lazy_goals(goals, config);
        let (solutions, stats) = stream.drain_all(self, config.max_solutions);
        (solutions, stats.truncated)
    }

    /// Like `resolve`, but also returns telemetry from the underlying
    /// search stream (see `ResolveStats`). Used by performance-oriented
    /// tests; production callers can stick with `resolve`.
    pub fn resolve_with_stats<V: TermView>(
        &mut self,
        goals: &[V],
        config: &ResolveConfig,
    ) -> (Vec<Solution>, ResolveStats) {
        // WI-628: drain via `drain_all` (not a `split_first` loop) so the final
        // stats reflect the WHOLE search — including the empty / post-last-solution
        // path the old loop never sampled (it refreshed `stats` only on a yielded
        // solution) — and so `stats.truncated` is populated.
        let stream = self.resolve_lazy(goals, config);
        stream.drain_all(self, config.max_solutions)
    }


    // ── Equational Rewriting ────────────────────────────────────

    /// Simplify a term using equational rules in the KB.
    ///
    /// Strategy: innermost (simplify subterms first, then try rewriting
    /// at the top level). Uses fuel to prevent non-termination from
    /// divergent rewrite systems.
    pub fn simplify(&mut self, term: TermId) -> TermId {
        // The standalone simplifier has no resolver frame, so no constraint-store
        // bindings to read — an empty subst (WI-595: the type-directed guard then
        // reads the redex's own structural type only).
        let (result, _) = self.apply_eq_rules(&Value::term(term), 100, &Substitution::new());
        result.expect_term()
    }

    /// Try firing a directional `[simp]`/`[unfold]` equation at `redex` (a term
    /// OR a `Value::Node` occurrence) via the one-directional `match_view`
    /// matcher — the convergence of the resolver and typer rewriters (see the
    /// simp-rewriter-convergence note). `match_view` binds the rule's opened head
    /// vars directly to the redex's subterms, and a redex/query var is INERT (one-
    /// way match), so a projected redex var rides into the RHS with no threading
    /// (`pick(?q, 7) → ?q`) and a nonlinear LHS over a half-ground redex
    /// (`sub(?a,?a)` over `sub(f(?x),f(42))`) simply FAILS TO MATCH. The RHS is
    /// built in the redex's carrier. This retired the `query(eq(current,?r))` +
    /// WI-624/633/634 apparatus (synthetic-DeBruijn `tree_subst`, query-link
    /// classification, `instantiate_eq_rhs`, linearity gate — all deleted).
    /// Returns `(rule, rewritten)`.
    fn fire_simp_equation(
        &mut self,
        redex: &Value,
        subst: &Substitution,
        rids: &[RuleId],
    ) -> Option<(RuleId, Value)> {
        // The redex's head functor, if it has one — read carrier-neutrally via
        // `head` (not `get_term`). A functor-less redex (a bare `Const`/`Ref`/
        // `Ident`, e.g. `1` under `[simp] unify(1, 2)`) still fires — the functor
        // pre-filter below is skipped and `match_view` decides.
        let current_functor = redex.head(self).functor_sym();
        // WI-595: the requires-guard decision reads ONLY the redex + `subst` (not
        // `rid`), so it is the SAME for every requires-guarded candidate — compute
        // it at most ONCE, lazily (WI-641: carrier-neutrally, so a `Value::Node`
        // redex's WI-578 carried types are read rather than reified away), only
        // when a requires-guarded candidate is actually reached.
        let mut redex_guard: Option<bool> = None;
        // WI-646: `rids` are the eq+unify candidates gathered ONCE per
        // `simp_rewrite::rewrite` walk by `ResolverSimpFirer` (from
        // `KnowledgeBase::simp_equation_rids`) — `eq` for a legacy `=` equation,
        // `unify` for the `<=>` head; WI-139 keeps only `[simp]`/`[unfold]`-tagged
        // equations there. Mirrors the typer's `simp_rewrite::try_fire` selection.
        for &rid in rids {
            if !self.is_directional_equation(rid) {
                continue;
            }
            // A value-headed equation (a `Value::Node`/`Entity` head, WI-348) has
            // no term LHS the term-rewrite path can open — skip it (the retired
            // legacy branch did too). Early-out: the head reads below
            // (`stored_lhs_functor` / `open_equation`) are now carrier-agnostic
            // (WI-663 — they read `fact_head_term` and return `None` on a value
            // head rather than panicking), so this guard is a cheap early skip,
            // no longer a panic-prevention necessity.
            if !matches!(&self.rules[rid.index()].head, Value::Term { .. }) {
                continue;
            }
            // Pre-filter on the stored LHS functor: the redex's head functor must
            // equal the LHS's. Both `None` = both functor-less (a `Const`-LHS eq
            // like `unify(1,2)` over a `Const` redex — kept); any mismatch (incl. a
            // functor redex vs a functor-less LHS, or a functor-less redex vs a
            // functor LHS) skips without the allocate-heavy open + `match_view`.
            if current_functor != super::simp_rewrite::stored_lhs_functor(self, rid) {
                continue;
            }
            // Type-directed requires-guard (WI-283): a requires-bearing sort's
            // rule fires only where the redex's carrier args provide the spec.
            if self.equation_is_requires_guarded(rid) {
                let holds = *redex_guard.get_or_insert_with(|| {
                    super::typing::simp_requires_guard_holds(self, redex, subst)
                });
                if !holds {
                    continue;
                }
            }
            // Open the equation's DeBruijn head to fresh globals through the ONE
            // shared opener (`simp_rewrite::open_equation`, WI-641 Phase 2); it
            // returns the fresh set so a rule-var binding is told apart from a
            // constrained redex var below (typed-pattern bounds are keyed by it).
            let (lhs, rhs, fresh) = match super::simp_rewrite::open_equation(self, rid) {
                Some(opened) => opened,
                None => continue,
            };
            // `match_view` runs in one-directional MATCH mode: it binds only the
            // rule's head vars (the opened `fresh` globals for a DeBruijn rule, or
            // the head's own `Global` vars for a legacy arity-0 head) to the
            // redex's subterms; a redex/query var is INERT and never bound. So a
            // projected redex var rides straight into the RHS (`pick(?q,7) → ?q`,
            // WI-634, threading-free), and a nonlinear LHS over a half-ground
            // redex (`sub(?a,?a)` over `sub(f(?x),f(42))`) simply FAILS TO MATCH
            // (the repeated head var can't match two distinct subterms) rather
            // than binding a redex var — so the old "inexpressible"/linearity gate
            // is unnecessary here.
            let Some(msubst) = self.match_view_oneway(lhs, redex) else {
                continue;
            };
            if msubst.is_contradiction() {
                continue;
            }
            // WI-582 typed-pattern bounds, keyed by the opened globals.
            if !super::typing::typed_pattern_bounds_hold(self, rid, &msubst, &fresh) {
                continue;
            }
            // Build the RHS in the redex's carrier: a `Value::Node` redex keeps
            // occurrence identity (`substitute_to_occurrence`, the typer's RHS
            // builder); a term redex rebuilds its hash-consed term.
            let rewritten = match redex {
                Value::Node(occ) => {
                    let pass = super::simp_rewrite::simp_pass(self);
                    Value::Node(super::simp_rewrite::substitute_to_occurrence(
                        self, rhs, &msubst, occ, pass,
                    ))
                }
                _ => Value::term(self.apply_subst(rhs, &msubst)),
            };
            return Some((rid, rewritten));
        }
        None
    }

    /// Apply equational `[simp]`/`[unfold]` rules to rewrite a redex, carrier-
    /// neutrally: the redex arrives as a `Value` (a hash-consed term or a
    /// `Value::Node` occurrence) and the rewrite is rebuilt in the SAME carrier,
    /// so a resolution goal keeps its occurrence identity. Strategy: innermost —
    /// rewrite subterms first (each carrier stays closed under rewrite), then try
    /// firing at the top level via [`Self::fire_simp_equation`]. Returns
    /// `(rewritten, changes)`.
    ///
    /// WI-643: BOTH carriers now route through the ONE shared iterative driver
    /// ([`super::simp_rewrite::rewrite`]) — a `Value::Node` occurrence and a
    /// hash-consed term drive the SAME work-stack (bottom-up descent + top-fire +
    /// fixpoint on the heap), firing carrier-neutrally via `ResolverSimpFirer`.
    /// This retired the resolver's separate recursive TERM walk (former steps
    /// 1–2), so a deeply-nested TERM redex no longer overflows the host stack nor
    /// stops at a fuel-as-depth cutoff. Both carriers now spend `fuel` ONLY on the
    /// fire→refire chain (descent carries `fuel` unchanged), so they reach the
    /// same firing DECISIONS at the same depth — the former term/Node fuel
    /// divergence (depth-bounded vs chain-bounded) is gone.
    ///
    /// O(1) gate (WI-646): short-circuit a KB with NO directional
    /// (`[simp]`/`[unfold]`) equation via [`Self::has_directional_rewrite`] — a
    /// KB-cached bit, NOT a per-call bucket scan. This is the CORRECT gate the
    /// WI-643 note deferred: it mirrors `equation_is_directional_rewrite`
    /// (`[simp]` OR `[unfold]`) over BOTH `eq` AND `unify`, so — unlike the
    /// `[simp]`-only/`eq`-only `has_simp_equations` that WI-643 refused to ship as
    /// a gate — it never skips an unfold-only or `<=>`-only KB's rewrites. When it
    /// returns `false` nothing could fire anyway, so returning the redex unchanged
    /// is exactly what the driver would produce, at a bool-read's cost.
    pub fn apply_eq_rules(
        &mut self,
        redex: &Value,
        fuel: usize,
        subst: &Substitution,
    ) -> (Value, Vec<EqChange>) {
        if fuel == 0 || !self.has_directional_rewrite() {
            return (redex.clone(), vec![]);
        }
        let mut changes = Vec::new();
        let mut firer = ResolverSimpFirer { subst, changes: &mut changes };
        let rewritten = super::simp_rewrite::rewrite(self, redex, &mut firer, fuel);
        (rewritten, changes)
    }

    /// WI-292: whether `rid` is a DIRECTIONAL `[simp]`/`[unfold]` rewrite — the
    /// firing gate the typer's `simp_rewrite` already applies via
    /// [`super::load::meta_has_flag`]. An equational head that carries neither tag
    /// is a logical LAW, not a rewrite, and is `unindex_functor`'d at load
    /// (load.rs WI-139); the discrim tree [`apply_eq_rules`] queries still returns
    /// it, so the rewriter re-checks the tag here so it doesn't fire a
    /// non-reducing law (commutativity / a recursive definition) into a
    /// fuel-bounded loop.
    fn equation_is_directional_rewrite(&self, rid: RuleId) -> bool {
        let meta = self.rule_meta(rid);
        super::load::meta_has_flag(self, meta, "simp")
            || super::load::meta_has_flag(self, meta, "unfold")
    }

    /// WI-646: the resolver's per-rule fire predicate — `rid` is a directional
    /// (`[simp]`/`[unfold]`) EQUATION. Shared by the `has_directional_rewrite`
    /// gate AND the `fire_simp_equation` loop so the two can't drift apart: a gate
    /// that under-counts relative to the fire site would silently skip a KB that
    /// would fire (the WI-643 regression class). The additional fire-time filters
    /// (`Value::Term` head, functor match, guards) only NARROW this, so the gate
    /// stays a sound necessary condition.
    fn is_directional_equation(&self, rid: RuleId) -> bool {
        self.is_equation(rid) && self.equation_is_directional_rewrite(rid)
    }

    /// WI-646: whether the KB holds ANY directional (`[simp]`/`[unfold]`) equation
    /// under `eq` or `unify` — the O(1) gate [`Self::apply_eq_rules`] short-
    /// circuits on. Reads a KB-cached bit ([`KnowledgeBase::simp_gate_cache`]),
    /// computing it once on a miss by mirroring the per-rule fire filter
    /// (`is_equation` + [`Self::equation_is_directional_rewrite`]) over the shared
    /// [`Self::simp_equation_rids`] selection — the SAME two predicates
    /// `fire_simp_equation` applies, so the gate is exact (a `true` may still not
    /// fire at a given redex — functor/guard mismatch — but a `false` guarantees
    /// nothing fires anywhere). The cache is dropped whenever those buckets change
    /// (`push_value_head_entry` / `retract` / `unindex_functor`), so it can't go
    /// stale; during a query no rule mutates, so this is O(1) amortized on the hot
    /// path.
    fn has_directional_rewrite(&mut self) -> bool {
        if let Some(cached) = self.simp_gate_cache {
            return cached;
        }
        let computed = self
            .simp_equation_rids()
            .into_iter()
            .any(|rid| self.is_directional_equation(rid));
        self.simp_gate_cache = Some(computed);
        computed
    }

    /// WI-283: whether `rid`'s enclosing sort (its `rule_domain`) declares
    /// `requires` — i.e. the equation carries an implicit type-directed
    /// guard. Top-level rules (domain = a namespace, not a sort) and rules
    /// on requires-free sorts return `false`: they are type-independent
    /// identities the resolver can fire soundly. A requires-bearing sort's
    /// rule returns `true`, so [`apply_eq_rules`] skips it (the typer fires
    /// it, where `min_sort` is available to check the guard).
    fn equation_is_requires_guarded(&mut self, rid: RuleId) -> bool {
        let domain = self.rule_domain(rid);
        let sort_sym = match self.get_term(domain) {
            Term::Fn { functor, .. } => Some(*functor),
            Term::Ref(s) | Term::Ident(s) => Some(*s),
            _ => None,
        };
        match sort_sym {
            Some(s) => !super::typing::requires_chain(self, s).is_empty(),
            None => false,
        }
    }

    // ── Builtin execution ──────────────────────────────────────

    /// Dispatch a builtin by tag. The goal has already been identified as a
    /// builtin; this evaluates it against the current substitution.
    fn execute_builtin(
        &mut self,
        tag: BuiltinTag,
        goal: &Value,
        answer_subst: &Substitution,
    ) -> BuiltinResult {
        // Every builtin reads its goal carrier-agnostically through `TermView`
        // (WI-482): a rule-body `Value::Node` occurrence resolves without
        // lowering the whole goal to a hash-consed `TermId`. The
        // symbol-reflection builtins (`qualified_name`, `short_name`,
        // `lookup_symbol`, `resolve_sort_instantiation_param`) still reify their
        // *structural* argument carrier (a symbol ref, a `SortView`) internally
        // via `carrier_term` — the KB's symbol/field lookups are keyed over
        // `Term` — but that is a narrow, per-arg reify, not a per-goal one.
        match tag {
            BuiltinTag::NonVar => self.builtin_nonvar(goal, answer_subst),
            BuiltinTag::Ground => self.builtin_ground(goal, answer_subst),
            BuiltinTag::QualifiedName => self.builtin_qualified_name(goal, answer_subst),
            BuiltinTag::ShortName => self.builtin_short_name(goal, answer_subst),
            BuiltinTag::LookupSymbol => self.builtin_lookup_symbol(goal, answer_subst),
            BuiltinTag::IsEntityOf => self.builtin_is_entity_of(goal, answer_subst),
            BuiltinTag::ExtractSort => self.builtin_extract_sort(goal, answer_subst),
            BuiltinTag::Not => unreachable!("Not is handled in step_init, not execute_builtin"),
            BuiltinTag::HoApply => unreachable!("HoApply is handled in step_init, not execute_builtin"),
            BuiltinTag::PushChoice => unreachable!("PushChoice is handled in step_init, not execute_builtin"),
            BuiltinTag::Cut => unreachable!("Cut is handled in step_init, not execute_builtin"),
            BuiltinTag::ResolveSortInstParam => self.builtin_resolve_sort_inst_param(goal, answer_subst),
            BuiltinTag::Scope => self.builtin_scope(goal, answer_subst),
            BuiltinTag::Kind => self.builtin_kind(goal, answer_subst),
            BuiltinTag::Provenance => self.builtin_provenance(goal, answer_subst),
            BuiltinTag::FieldAccess => self.builtin_field_access(goal, answer_subst),
            BuiltinTag::Eq => self.builtin_eq(goal, answer_subst),
            BuiltinTag::SemEq => self.builtin_sem_eq(goal, answer_subst),
            BuiltinTag::SemNeq => self.builtin_sem_neq(goal, answer_subst),
            BuiltinTag::Unify => self.builtin_unify(goal, answer_subst),
            BuiltinTag::Gt => self.builtin_cmp(goal, answer_subst, |ord| ord == std::cmp::Ordering::Greater),
            BuiltinTag::Lt => self.builtin_cmp(goal, answer_subst, |ord| ord == std::cmp::Ordering::Less),
            BuiltinTag::Gte => self.builtin_cmp(goal, answer_subst, |ord| ord != std::cmp::Ordering::Less),
            BuiltinTag::Lte => self.builtin_cmp(goal, answer_subst, |ord| ord != std::cmp::Ordering::Greater),
            BuiltinTag::Add => self.builtin_arith(goal, answer_subst, |a, b| a + b, |a, b| a + b, |a, b| a + b),
            BuiltinTag::Sub => self.builtin_arith(goal, answer_subst, |a, b| a - b, |a, b| a - b, |a, b| a - b),
            BuiltinTag::Mul => self.builtin_arith(goal, answer_subst, |a, b| a * b, |a, b| a * b, |a, b| a * b),
            BuiltinTag::ToBigInt => self.builtin_to_bigint(goal, answer_subst),
            BuiltinTag::ToInt => self.builtin_to_int(goal, answer_subst),
            // Occurrence reflection builtins (WI-297).
            BuiltinTag::OccurrenceTerm => self.builtin_occurrence_term(goal, answer_subst),
            BuiltinTag::OccurrenceSpan => self.builtin_occurrence_span(goal, answer_subst),
            BuiltinTag::OccurrenceOwner => self.builtin_occurrence_owner(goal, answer_subst),
            BuiltinTag::SubOccurrences => self.builtin_sub_occurrences(goal, answer_subst),
            BuiltinTag::OperationBody => self.builtin_operation_body(goal, answer_subst),
            BuiltinTag::FindDictionary => self.builtin_find_dictionary(goal, answer_subst),
        }
    }

    /// Resolve a builtin goal argument (read through [`TermView`]) to a
    /// `Value` under σ — the representation-agnostic analog of
    /// `walk(goal's positional arg, σ)`. A term child is `walk_view`d; an
    /// occurrence child that is a bound `Global` var leaf is resolved via σ,
    /// otherwise kept as-is (WI-246). `None` ⇒ the arg slot is absent.
    fn walk_arg(&self, item: Option<ViewItem>, subst: &Substitution) -> Option<Value> {
        Some(match item? {
            ViewItem::Term(t) => self.walk_view(t, subst),
            ViewItem::Value(Value::Term { id: t, .. }) => self.walk_view(*t, subst),
            ViewItem::Value(v) => v.clone(),
            ViewItem::Node(occ) => match occ.as_expr() {
                Some(Expr::Var(Var::Global(vid))) => {
                    subst.resolve_as_value(*vid).cloned().unwrap_or(Value::Node(occ))
                }
                _ => Value::Node(occ),
            },
        })
    }

    /// Whether a σ-walked `Value` is still *any* unbound logic variable —
    /// `Term::Var(_)` (flex/rigid/DeBruijn) or an `Expr::Var(_)` occurrence
    /// leaf. The delay test for `nonvar`/`cmp`/`arith`.
    fn value_is_unbound_var(&self, v: &Value) -> bool {
        match v {
            Value::Term { id: t, .. } => matches!(self.terms.get(*t), Term::Var(_)),
            Value::Node(occ) => matches!(occ.as_expr(), Some(Expr::Var(_))),
            // WI-109: a value-level logic variable is, itself, a variable.
            Value::Var(_) => true,
            _ => false,
        }
    }

    /// Whether a σ-walked `Value` is a *flex* variable (`Var::Global` only) —
    /// the narrower delay test for `eq`/`neq`, which compare rigid vars by
    /// identity rather than delaying on them.
    fn value_is_flex(&self, v: &Value) -> bool {
        self.value_global_var(v).is_some()
    }

    /// `nonvar(?x)`: succeeds if `?x` is bound to a non-variable after walking.
    fn builtin_nonvar<V: TermView>(&self, goal: &V, subst: &Substitution) -> BuiltinResult {
        match self.walk_arg(goal.pos_arg(self, 0), subst) {
            None => BuiltinResult::Failure,
            Some(v) if self.value_is_unbound_var(&v) => BuiltinResult::delay(),
            Some(_) => BuiltinResult::Success,
        }
    }

    /// `ground(?x)`: succeeds if `?x` is fully ground (no unbound variables anywhere).
    fn builtin_ground<V: TermView>(&self, goal: &V, subst: &Substitution) -> BuiltinResult {
        match self.walk_arg(goal.pos_arg(self, 0), subst) {
            None => BuiltinResult::Failure,
            Some(v) if self.value_is_ground(&v, subst) => BuiltinResult::Success,
            Some(_) => BuiltinResult::delay(),
        }
    }

    /// Carrier-agnostic groundness of a σ-walked goal [`Value`] (WI-348): a
    /// `Value::Term` re-uses the recursive term check [`Self::is_ground`]
    /// (chasing `σ` into subterms); a `Value::Node` occurrence (post-flip) is
    /// ground iff it has no remaining unbound `Expr::Var(Global)` leaf
    /// (`occurrence_has_unbound_var`); a value-level logic var (WI-109) is never
    /// ground; any other scalar is. The shared core of the `ground(?x)` builtin
    /// and the NAF groundness gate, so neither materializes the goal to a
    /// `TermId` just to ask "is it ground".
    fn value_is_ground(&self, v: &Value, subst: &Substitution) -> bool {
        match v {
            Value::Term { id: t, .. } => matches!(self.is_ground(*t, subst), GroundCheck::Ground),
            Value::Node(occ) => !node_occurrence::occurrence_has_unbound_var(occ),
            // WI-629: a COMPOUND value carrier — a `Value::Entity` (the `not`/`or`
            // wrapper `make_goal_value` synthesizes; a `not(not(P))` inner lands
            // here) or a `Value::Tuple` (only ever a nested child value) — is ground
            // iff every child is. Without this arm it fell to `_ => true`, so the NAF
            // groundness gate ([`SearchStream::step_naf`]) read a `not(Entity{…})`
            // with unbound vars inside as GROUND and ran NAF where it should
            // delay-and-rotate. Mirrors the Entity recursion in
            // [`Self::value_has_open_world_ref_inner`] / [`Self::value_deep_ground`]
            // (recursing via `value_is_ground` keeps the precise `Term`/`Node`/`Var`
            // leaf readings this shares with the `ground(?x)` builtin).
            Value::Entity { pos, named, .. } | Value::Tuple { pos, named, .. } => {
                pos.iter().all(|c| self.value_is_ground(c, subst))
                    && named.iter().all(|(_, c)| self.value_is_ground(c, subst))
            }
            Value::Var(_) => false,
            _ => true,
        }
    }

    /// WI-067 / proposal 050: does a goal value reference an OPEN-WORLD binder /
    /// parameter — a value unknown at static time, so a `not(…)` / scalar builtin
    /// over it must FLOUNDER rather than NAF-succeed (the soundness contract effect
    /// discharge relies on; see the gates in [`SearchStream::step_naf`] /
    /// `step_builtin`)? The reference is the canonical `var_ref(name)` reflect-term
    /// twin (`Functor{anthill.reflect.Expr.var_ref}`) — the ONLY binder-reference
    /// shape `Γ` is built with ([`binder_ref_value`]) and the one a clause / guard
    /// binder carries NATIVELY from load (`wrap_places_as_var_ref`, WI-552). The
    /// recognition is therefore principled — `var_ref` ⇒ open-world, with no
    /// pre-discharge normalize step to depend on. A bare `Ref`/`Ident` is
    /// deliberately NOT matched: a binder is already wrapped, while a *bare* `Ref`
    /// here is a closed datum — a sort,
    /// operation, const, or constructor — that a reflective builtin a proof goal
    /// chases (`scope`/`is_entity_of`/…) must still be able to DECIDE, not
    /// flounder. Carrier-agnostic: walks `Term`, `Node` occurrences, AND
    /// value-carrier `Entity` arguments (a reified goal lands as a
    /// `Value::Entity` of `Value`s). Only consulted under the `gamma` overlay (the
    /// local-interpretation context); inert otherwise.
    pub(crate) fn value_has_open_world_ref(&self, v: &Value, subst: &Substitution) -> bool {
        // No `var_ref` symbol interned (a prelude-less KB) ⇒ no binder references
        // can exist ⇒ nothing is open-world.
        match self.symbols.by_qualified_name.get("anthill.reflect.Expr.var_ref").copied() {
            Some(var_ref) => self.value_has_open_world_ref_inner(v, var_ref, subst),
            None => false,
        }
    }

    fn value_has_open_world_ref_inner(&self, v: &Value, var_ref: crate::intern::Symbol, subst: &Substitution) -> bool {
        match v {
            Value::Term { id: t, .. } => self.term_has_var_ref(*t, var_ref, subst),
            Value::Node(occ) => node_occurrence::occurrence_has_var_ref(occ),
            // WI-629: recurse BOTH compound carriers. A `var_ref` buried in a
            // `Value::Tuple` child of a `not(…)` goal (a tuple nested inside the
            // `make_goal_value` Entity wrapper) would otherwise be missed here → the
            // NAF gate reads the inner as closed and can NAF-succeed where it must
            // FLOUNDER over the symbolic binder (unsound negation under Γ). Same
            // recursion as `value_is_ground` / `value_deep_ground`.
            Value::Entity { pos, named, .. } | Value::Tuple { pos, named, .. } => {
                pos.iter().any(|a| self.value_has_open_world_ref_inner(a, var_ref, subst))
                    || named.iter().any(|(_, a)| self.value_has_open_world_ref_inner(a, var_ref, subst))
            }
            _ => false,
        }
    }

    /// Recursive `var_ref`-functor search over a hash-consed goal term — a binder
    /// reference (`var_ref(name: …)`) anywhere in the term. A bare `Ref`/`Ident`
    /// is closed (see [`value_has_open_world_ref`]).
    fn term_has_var_ref(&self, term: TermId, var_ref: crate::intern::Symbol, subst: &Substitution) -> bool {
        let walked = self.walk(term, subst);
        match self.terms.get(walked) {
            Term::Fn { functor, pos_args, named_args } => {
                if *functor == var_ref {
                    return true;
                }
                let pos_args = pos_args.clone();
                let named_args = named_args.clone();
                pos_args.iter().any(|&a| self.term_has_var_ref(a, var_ref, subst))
                    || named_args.iter().any(|&(_, a)| self.term_has_var_ref(a, var_ref, subst))
            }
            _ => false,
        }
    }

    /// Recursive groundness check: walk the term, then check all subterms.
    fn is_ground(&self, term: TermId, subst: &Substitution) -> GroundCheck {
        let walked = self.walk(term, subst);
        match self.terms.get(walked) {
            Term::Var(_) => GroundCheck::HasVar,
            Term::Const(_) | Term::Ref(_) | Term::Bottom | Term::Ident(_) => GroundCheck::Ground,
            Term::ParseAux(_) => unreachable!(
                "parse-only Term::ParseAux variant reached the KB resolver",
            ),
            Term::Fn { pos_args, named_args, .. } => {
                let pos_args = pos_args.clone();
                let named_args = named_args.clone();
                for &arg in pos_args.iter() {
                    if matches!(self.is_ground(arg, subst), GroundCheck::HasVar) {
                        return GroundCheck::HasVar;
                    }
                }
                for &(_, arg) in named_args.iter() {
                    if matches!(self.is_ground(arg, subst), GroundCheck::HasVar) {
                        return GroundCheck::HasVar;
                    }
                }
                GroundCheck::Ground
            }
        }
    }

    /// The fully-qualified name for a symbol. Resolved symbols use their
    /// `qualified_name`; unresolved ones get `_unresolved.<name>`.
    fn symbol_qualified_name(&self, sym: crate::intern::Symbol) -> String {
        match self.symbols.get(sym) {
            crate::intern::SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            crate::intern::SymbolDef::Unresolved { name } => format!("_unresolved.{}", name),
        }
    }

    /// `qualified_name(?sym, ?result)` — if `?sym` is bound to a `Ref`/`Ident`
    /// symbol, bind `?result` to its full qualified-name string. Delay if `?sym`
    /// is unbound. Reads its goal through [`TermView`] (WI-482) so a rule-body
    /// `Value::Node` occurrence resolves; the symbol carrier itself is reified
    /// via `carrier_term`.
    fn builtin_qualified_name<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        if !matches!(goal.head(self), ViewHead::Functor { pos_arity, .. } if pos_arity >= 2) {
            return BuiltinResult::Failure;
        }
        let sym_val = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            Some(v) => v,
            None => return BuiltinResult::Failure,
        };
        if self.value_is_unbound_var(&sym_val) {
            return BuiltinResult::delay();
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        let Some(sym_term) = self.carrier_term(&sym_val) else {
            return BuiltinResult::Failure;
        };
        let sym = match self.terms.get(sym_term) {
            Term::Ref(s) | Term::Ident(s) => *s,
            _ => return BuiltinResult::Failure,
        };
        let name = self.symbol_qualified_name(sym);
        let str_term = self.alloc(Term::Const(super::term::Literal::String(name)));
        self.finish_result(target, str_term)
    }

    /// `short_name(?sym, ?result)` — if `?sym` is bound to a `Ref`/`Ident`
    /// symbol, bind `?result` to the last dot-separated segment of its name.
    /// Delay if `?sym` is unbound. `TermView` goal (WI-482); symbol carrier
    /// reified via `carrier_term`.
    fn builtin_short_name<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        if !matches!(goal.head(self), ViewHead::Functor { pos_arity, .. } if pos_arity >= 2) {
            return BuiltinResult::Failure;
        }
        let sym_val = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            Some(v) => v,
            None => return BuiltinResult::Failure,
        };
        if self.value_is_unbound_var(&sym_val) {
            return BuiltinResult::delay();
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        let Some(sym_term) = self.carrier_term(&sym_val) else {
            return BuiltinResult::Failure;
        };
        let sym = match self.terms.get(sym_term) {
            Term::Ref(s) | Term::Ident(s) => *s,
            _ => return BuiltinResult::Failure,
        };
        let full = self.symbols.resolve(sym);
        let short = full.rsplit('.').next().unwrap_or(full).to_string();
        let str_term = self.alloc(Term::Const(super::term::Literal::String(short)));
        self.finish_result(target, str_term)
    }

    /// `lookup_symbol(?name_str, ?result)` — if `?name_str` is a bound String,
    /// search the symbol table for that qualified name and bind `?result` to
    /// `Ref(symbol)` if found, fail if not. Delay if `?name_str` is unbound.
    /// `TermView` goal (WI-482); the name carrier is reified via `carrier_term`.
    fn builtin_lookup_symbol<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        if !matches!(goal.head(self), ViewHead::Functor { pos_arity, .. } if pos_arity >= 2) {
            return BuiltinResult::Failure;
        }
        let name_val = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            Some(v) => v,
            None => return BuiltinResult::Failure,
        };
        if self.value_is_unbound_var(&name_val) {
            return BuiltinResult::delay();
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        let Some(name_term) = self.carrier_term(&name_val) else {
            return BuiltinResult::Failure;
        };
        let name = match self.terms.get(name_term) {
            Term::Const(super::term::Literal::String(s)) => s.clone(),
            _ => return BuiltinResult::Failure,
        };
        // Look up the symbol by qualified name (read-only).
        match self.symbols.by_qualified_name.get(&name).copied() {
            Some(sym) => {
                let ref_term = self.alloc(Term::Ref(sym));
                self.finish_result(target, ref_term)
            }
            None => BuiltinResult::Failure,
        }
    }

    /// `is_entity_of(?sub, ?sup)`: succeeds if sub is an entity of sup (via KB indexes).
    /// Both args must be non-var (delay otherwise).
    fn builtin_is_entity_of<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let (sub, sup) = match (
            self.walk_arg(goal.pos_arg(self, 0), subst),
            self.walk_arg(goal.pos_arg(self, 1), subst),
        ) {
            (Some(sub), Some(sup)) => (sub, sup),
            _ => return BuiltinResult::Failure,
        };
        if self.value_is_unbound_var(&sub) || self.value_is_unbound_var(&sup) {
            return BuiltinResult::delay();
        }
        // The subtype check is a KB lookup over hash-consed terms; reify each
        // operand (a literal goal arg reads as `Value::Node`, a σ-bound one as
        // `Value::Term`) to a term first.
        let sub_t = reify_goal_value(self, &sub);
        let sup_t = reify_goal_value(self, &sup);
        if self.is_entity_of(sub_t, sup_t) {
            BuiltinResult::Success
        } else {
            BuiltinResult::Failure
        }
    }

    /// `extract_sort_ref(?inst, ?result)`: given a term like `Eq[T = Int]` (represented as
    /// `ParameterizedType(Eq(), T=Int())`) or a simple `Ref(Eq)`, extract the sort symbol
    /// and bind `?result` to `Ref(sort_sym)`. Delays if `?inst` is unbound.
    fn builtin_extract_sort<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let inst = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            Some(v) => v,
            None => return BuiltinResult::Failure,
        };
        if self.value_is_unbound_var(&inst) {
            return BuiltinResult::delay();
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        // WI-694: read the sort symbol off the arg's head carrier-neutrally (no
        // reify) — `functor_sym` unifies the `Ref` / `Fn` spellings across carriers.
        let sort_sym = match inst.head(self) {
            // Simple Ref: the sort itself.
            ViewHead::Ref(sym) => Some(sym),
            // `SortView(sort_name, bindings…)` — the first positional child is the
            // sort name; read ITS head symbol. Any other functor is the sort itself
            // (e.g. `Eq()` / `SortInfo(...)`).
            ViewHead::Functor { functor: Some(functor), pos_arity, .. } => {
                if self.symbols.name(functor) == "SortView" && pos_arity > 0 {
                    inst.pos_arg(self, 0)
                        .and_then(|name| name.head(self).functor_sym())
                } else {
                    Some(functor)
                }
            }
            _ => None,
        };

        match sort_sym {
            Some(sym) => {
                // Canonical nullary-Fn shape — matches the form used by
                // load.rs for sort references.
                let ref_term = self.make_name_term_from_sym(sym);
                self.finish_result(target, ref_term)
            }
            None => BuiltinResult::Failure,
        }
    }

    /// WI-352 — `anthill.reflect.feed.provenance(?place, ?result)`: the place
    /// symbol's `Provenance`, a pure function of its `SymbolKind` (so there are
    /// no materialized provenance facts; the symbol's kind is the source of
    /// truth). `Param`→`input`, `OpResult`→`op_result`,
    /// `CallbackResult`→`fresh_output`, `LocalLet`→`local`; anything else
    /// (notably `CallbackParam`, a flow *target*, and non-place symbols) has no
    /// provenance and the goal fails. Used by `feed`'s `keep_modify` rules.
    fn builtin_provenance<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let place_val = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            Some(v) => v,
            None => return BuiltinResult::Failure,
        };
        if self.value_is_unbound_var(&place_val) {
            return BuiltinResult::delay();
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        // WI-694: the place symbol read off the arg's head, carrier-neutrally. A
        // `Symbol` value is a `Ref`, a canonical sort/place reference a nullary `Fn`;
        // `functor_sym` yields the symbol from either spelling for any carrier
        // (Term/Node/Entity) with no reify. A non-symbol arg (scalar/…) reads `None`
        // → clean `Failure` (the former `reify_goal_value` would have panicked).
        let Some(sym) = place_val.head(self).functor_sym() else {
            return BuiltinResult::Failure;
        };
        let prov_qn = match self.kind_of(sym) {
            Some(crate::intern::SymbolKind::Param) => "anthill.reflect.feed.Provenance.input",
            Some(crate::intern::SymbolKind::OpResult) => "anthill.reflect.feed.Provenance.op_result",
            Some(crate::intern::SymbolKind::CallbackResult) => {
                "anthill.reflect.feed.Provenance.fresh_output"
            }
            Some(crate::intern::SymbolKind::LocalLet) => "anthill.reflect.feed.Provenance.local",
            // CallbackParam (a flow target) and non-place symbols: no provenance.
            _ => return BuiltinResult::Failure,
        };
        let prov_sym = match self.try_resolve_symbol(prov_qn) {
            Some(s) => s,
            None => return BuiltinResult::Failure,
        };
        // A bare nullary enum variant (`input`, …) appears in rule bodies as a
        // `Term::Ref` (not a nullary `Fn` — that is the sort-ref shape), so emit
        // a `Ref` to unify with the `keep_modify` rule's `provenance(?r, input)`.
        let prov_term = self.alloc(Term::Ref(prov_sym));
        self.finish_result(target, prov_term)
    }

    /// Shared front-half for the four occurrence reflect builtins (WI-297): walk
    /// arg0 to the subject occurrence and read arg1 as a carrier-faithful
    /// [`OccPattern`] via [`occ_arg1_pattern`](Self::occ_arg1_pattern). `Err(_)`
    /// carries the early `BuiltinResult` (Delay on an unbound subject, Failure on
    /// a missing / non-occurrence subject or a bad arg1). On `Ok`, the caller
    /// builds its target term/view and unifies the pattern against it via
    /// [`match_occ_pattern`](Self::match_occ_pattern).
    fn occurrence_arg_and_pattern<V: TermView>(
        &mut self,
        goal: &V,
        subst: &Substitution,
    ) -> Result<(Rc<NodeOccurrence>, OccPattern), BuiltinResult> {
        // arg0 — the subject occurrence.
        let occ = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            None => return Err(BuiltinResult::Failure),
            Some(v) if self.value_is_unbound_var(&v) => return Err(BuiltinResult::delay()),
            Some(Value::Node(rc)) => rc,
            // Not an occurrence — nothing to reflect.
            Some(_) => return Err(BuiltinResult::Failure),
        };
        let pattern = self.occ_arg1_pattern(goal, subst)?;
        Ok((occ, pattern))
    }

    /// WI-682: read arg1 of an occurrence reflect builtin as a σ-applied,
    /// carrier-faithful [`OccPattern`] — shared by
    /// [`occurrence_arg_and_pattern`](Self::occurrence_arg_and_pattern) (the four
    /// occurrence builtins) and [`builtin_operation_body`](Self::builtin_operation_body).
    /// A `Value::Term` arg rides as a hash-consed term (matched via the fast
    /// [`match_view`](Self::match_view)); a `Value::Node` occurrence arg STAYS a
    /// Node — σ-applied carrier-faithfully (`substitute_occurrence` via
    /// [`reify_value`](Self::reify_value), identity/span preserved) and matched via
    /// the carrier-neutral [`match_view_value_pattern`](Self::match_view_value_pattern)
    /// (WI-683), no reification.
    ///
    /// The `view_is_indexable` guard rejects a child-bearing / post-elaboration
    /// reflect form (`if`/`let`/`lambda`/`match`, …) that reads `Opaque` and has no
    /// goal-term shape: it fails clean (such a pattern could never unify with a
    /// goal-shaped target) rather than trip `insert_pattern`'s `Opaque` panic. This
    /// is the carrier-neutral peer of the former `try_occurrence_to_term`
    /// `None => Failure` arm (WI-297) and — reading the WHOLE structure — also fails
    /// clean on a *nested* such form (which that top-level-only reify silently
    /// lowered to ⊥). `Err(BuiltinResult::Failure)` on a missing arg1 or a
    /// non-term / non-occurrence carrier.
    fn occ_arg1_pattern<V: TermView>(
        &mut self,
        goal: &V,
        subst: &Substitution,
    ) -> Result<OccPattern, BuiltinResult> {
        // Extract an owned pattern source so the immutable borrow from `pos_arg`
        // ends before the `&mut self` σ-apply below.
        let mut pat_term: Option<TermId> = None;
        let mut pat_node = None;
        match goal.pos_arg(self, 1) {
            Some(ViewItem::Term(t)) => pat_term = Some(t),
            Some(ViewItem::Value(Value::Term { id: t, .. })) => pat_term = Some(*t),
            Some(ViewItem::Node(o)) => pat_node = Some(o),
            Some(ViewItem::Value(_)) | None => return Err(BuiltinResult::Failure),
        }
        match (pat_term, pat_node) {
            (Some(t), _) => Ok(OccPattern::Term(self.apply_subst(t, subst))),
            (None, Some(o)) => {
                let v = self.reify_value(&Value::Node(o), subst);
                if !super::discrim::view_is_indexable(self, &v) {
                    return Err(BuiltinResult::Failure);
                }
                Ok(OccPattern::Node(v))
            }
            (None, None) => Err(BuiltinResult::Failure),
        }
    }

    /// WI-682: unify a carrier-faithful [`OccPattern`] against `target`. A term
    /// pattern takes the established fast [`match_view`](Self::match_view); a
    /// `Value::Node` occurrence pattern takes the carrier-neutral
    /// [`match_view_value_pattern`](Self::match_view_value_pattern) (WI-683) — the
    /// occurrence is never lowered to a hash-consed term to be matched.
    fn match_occ_pattern<V: TermView>(
        &self,
        pattern: &OccPattern,
        target: &V,
    ) -> Option<Substitution> {
        match pattern {
            OccPattern::Term(t) => self.match_view(*t, target),
            OccPattern::Node(v) => self.match_view_value_pattern(v, target),
        }
    }

    /// `occurrence_term(occ, term)` — WI-297. "Show" the occurrence: unify the
    /// second argument against `occ` read through the reflect lens
    /// ([`ReflectedExpr`]). No hash-consed term is built and `occ` keeps its
    /// identity — an unbound result var binds to the `Value::Node` itself, a
    /// reflect pattern (`int_lit(value: ?)`, …) matches structurally against
    /// the lens.
    fn builtin_occurrence_term<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let (occ, pattern) = match self.occurrence_arg_and_pattern(goal, subst) {
            Ok(pair) => pair,
            Err(r) => return r,
        };
        let syms = ReflectSyms::resolve(self);
        match self.match_occ_pattern(&pattern, &ReflectedExpr::new(occ, syms)) {
            Some(extra) => BuiltinResult::SuccessWithBindings(extra),
            None => BuiltinResult::Failure,
        }
    }

    /// `occurrence_span(occ, span)` — WI-297. The span lives on the occurrence
    /// as a Rust struct, with no occurrence/term form to *show*, so this
    /// constructs the anthill `source_span(file:, start_byte:, end_byte:)`
    /// entity (plain `Int` fields, the raw `SourceId` for `file`) and unifies
    /// the second arg against it.
    fn builtin_occurrence_span<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let (occ, pattern) = match self.occurrence_arg_and_pattern(goal, subst) {
            Ok(pair) => pair,
            Err(r) => return r,
        };
        let span_term = match self.make_source_span_term(occ.span) {
            Some(t) => t,
            None => return BuiltinResult::Failure,
        };
        match self.match_occ_pattern(&pattern, &TermIdView(span_term)) {
            Some(extra) => BuiltinResult::SuccessWithBindings(extra),
            None => BuiltinResult::Failure,
        }
    }

    /// `occurrence_owner(occ, sym)` — WI-297. The owner is a `Symbol` (interned
    /// name), whose term form is `Term::Ref` (per `anthill.reflect.Symbol`).
    /// Fails when the occurrence has no owner (top-level / unknown context).
    fn builtin_occurrence_owner<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let (occ, pattern) = match self.occurrence_arg_and_pattern(goal, subst) {
            Ok(pair) => pair,
            Err(r) => return r,
        };
        let owner = match occ.owner {
            Some(sym) => self.alloc(Term::Ref(sym)),
            None => return BuiltinResult::Failure,
        };
        match self.match_occ_pattern(&pattern, &TermIdView(owner)) {
            Some(extra) => BuiltinResult::SuccessWithBindings(extra),
            None => BuiltinResult::Failure,
        }
    }

    /// `sub_occurrences(occ, list)` — WI-297. Shows the occurrence's direct
    /// child occurrences as a `List[Occurrence]`: the children keep their
    /// identity (the existing `Rc`s), only the cons-list spine is built.
    fn builtin_sub_occurrences<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let (occ, pattern) = match self.occurrence_arg_and_pattern(goal, subst) {
            Ok(pair) => pair,
            Err(r) => return r,
        };
        let mut children: Vec<Rc<NodeOccurrence>> = Vec::new();
        if let Some(expr) = occ.as_expr() {
            node_occurrence::for_each_child(expr, |c| children.push(Rc::clone(c)));
        }
        let nil_sym = self.resolve_symbol("anthill.prelude.List.nil");
        let cons_sym = self.resolve_symbol("anthill.prelude.List.cons");
        let head_sym = self.intern("head");
        let tail_sym = self.intern("tail");
        let list = node_occurrence::build_occurrence_cons_list(
            self, children, occ.span, nil_sym, cons_sym, head_sym, tail_sym,
        );
        match self.match_occ_pattern(&pattern, &Value::Node(list)) {
            Some(extra) => BuiltinResult::SuccessWithBindings(extra),
            None => BuiltinResult::Failure,
        }
    }

    /// `operation_body(op, result)` — WI-305. Bind `result` to the operation's
    /// body occurrence wrapped in `some(value: <NodeOccurrence>)`, or `none()` when
    /// the op has no body (declaration-only). The body lives in the `op_body_node`
    /// side-table (not a fact field), so this builtin is how anthill code reaches
    /// it. arg0 is the operation Symbol (Ref/Ident/Fn-functor).
    fn builtin_operation_body<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let op_val = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            None => return BuiltinResult::Failure,
            Some(v) if self.value_is_unbound_var(&v) => return BuiltinResult::delay(),
            Some(v) => v,
        };
        // arg0 must be a term-shaped Symbol (Ref/Ident/Fn-functor). A non-term
        // Value (Node / scalar / tuple) is simply not an operation symbol — fail
        // cleanly rather than panic (don't route through `reify_goal_value`).
        let op_sym = match &op_val {
            Value::Term { id: t, .. } => match self.terms.get(*t) {
                Term::Ref(s) | Term::Ident(s) => *s,
                Term::Fn { functor, .. } => *functor,
                _ => return BuiltinResult::Failure,
            },
            _ => return BuiltinResult::Failure,
        };
        // arg1 — the result pattern, read carrier-faithfully (WI-682): a
        // `Value::Node` some(value: …) / none() pattern STAYS a Node, matched via
        // the carrier-neutral `match_occ_pattern` below (shared with the four
        // occurrence builtins — same `occ_arg1_pattern` reader).
        let pattern = match self.occ_arg1_pattern(goal, subst) {
            Ok(p) => p,
            Err(r) => return r,
        };
        // Build the Option result as a Value::Node occurrence (like sub_occurrences
        // builds its list-node): some(value: <body>) or none().
        let result_node = match self.op_body_node(op_sym).cloned() {
            Some(node) => {
                let some_sym = self.resolve_symbol("anthill.prelude.Option.some");
                let value_sym = self.intern("value");
                let mut named = vec![(value_sym, node.clone())];
                self.canonicalize_record_named_args(some_sym, &mut named);
                NodeOccurrence::new_expr(
                    Expr::Constructor { name: some_sym, pos_args: Vec::new(), named_args: named },
                    node.span,
                    None,
                )
            }
            None => {
                let none_sym = self.resolve_symbol("anthill.prelude.Option.none");
                // nullary none follows the Ref convention (see build_occurrence_cons_list);
                // synthetic span (0,0) matches node_occurrence::empty_span.
                NodeOccurrence::new_expr(
                    Expr::Ref(none_sym),
                    crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0),
                    None,
                )
            }
        };
        match self.match_occ_pattern(&pattern, &Value::Node(result_node)) {
            Some(extra) => BuiltinResult::SuccessWithBindings(extra),
            None => BuiltinResult::Failure,
        }
    }

    /// Build the anthill `source_span(file:, start_byte:, end_byte:)` entity
    /// term from a Rust [`SourceSpan`](crate::span::SourceSpan) — `Int` fields,
    /// raw `SourceId` for `file`. `None` when reflect isn't loaded.
    fn make_source_span_term(&mut self, span: crate::span::SourceSpan) -> Option<TermId> {
        let functor = self.try_resolve_symbol("anthill.reflect.SourceSpan.source_span")?;
        let file_k = self.intern("file");
        let start_k = self.intern("start_byte");
        let end_k = self.intern("end_byte");
        let file_v = self.alloc(Term::Const(Literal::Int(span.source.raw() as i64)));
        let start_v = self.alloc(Term::Const(Literal::Int(span.start() as i64)));
        let end_v = self.alloc(Term::Const(Literal::Int(span.end() as i64)));
        let mut named: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        named.push((file_k, file_v));
        named.push((start_k, start_v));
        named.push((end_k, end_v));
        Some(self.make_entity_term(functor, SmallVec::new(), named))
    }

    /// Reorder a RECORD's named args into a canonical order so the payload
    /// hash-conses / discrim-matches regardless of source order. The discrim
    /// tree matches named args positionally (`discrim.rs`: it descends
    /// `NamedKey(query_keys[i])` against the tree's i-th pattern key), so a built
    /// term must use the same order as the loaded pattern or it silently fails to
    /// match. A registered field schema orders by DECLARED field order; a
    /// schema-less functor falls back to interning order. Generic over the value
    /// type so it serves both `Term::Fn` (`TermId`) and occurrence
    /// (`Rc<NodeOccurrence>`) builders.
    ///
    /// This is NOT universal — it is deliberately a no-op for an ORDERED PRODUCT
    /// ([`Self::is_ordered_product_functor`], a named tuple). A tuple's component
    /// order is SEMANTIC (source order IS its identity); reordering it would
    /// collapse `(x: 1, y: 2)` and `(y: 2, x: 1)` into one value — the
    /// record-collapse `tuple_order_test` guards. The old name
    /// (`sort_named_canonical`) implied it applied to every named-arg structure;
    /// the ordered-product exemption below makes the "records only" contract
    /// explicit rather than resting on a tuple's empty schema + a stable sort.
    pub(crate) fn canonicalize_record_named_args<T>(
        &self,
        functor: Symbol,
        named: &mut [(Symbol, T)],
    ) {
        // Ordered product (named tuple): source order IS canonical — leave it.
        if self.is_ordered_product_functor(functor) {
            return;
        }
        match self.entity_field_names(functor) {
            Some(fields) => {
                let order: HashMap<Symbol, usize> =
                    fields.iter().enumerate().map(|(i, &s)| (s, i)).collect();
                named.sort_by_key(|(s, _)| order.get(s).copied().unwrap_or(usize::MAX));
            }
            None => named.sort_by_key(|(s, _)| s.index()),
        }
    }

    /// Is `functor` an ORDERED PRODUCT — a named tuple
    /// (`anthill.reflect.TupleLiteral`)? Its labelled components carry SEMANTIC
    /// source order (the order IS the value's identity), so it is exempt from
    /// [`Self::canonicalize_record_named_args`]. Records, entities, and the
    /// reflect meta-constructors are NOT ordered products: their named args carry
    /// no source-order meaning and must be canonicalized for discrim matching.
    pub(crate) fn is_ordered_product_functor(&self, functor: Symbol) -> bool {
        self.qualified_name_of(functor) == "anthill.reflect.TupleLiteral"
    }

    /// WI-500: plan the positional→named desugar for a constructor — the loader's
    /// "rank-among-not-named" rule ([`crate::kb::load`]'s `convert_term_with_expected`),
    /// shared so runtime value→term lowering canonicalizes to the SAME named shape
    /// (see [`PositionalPlan`]). `named_fields` are the field symbols already given
    /// by name; `pos_count` is the number of positional args. Positional args fill
    /// the declared fields NOT already named, in declaration order. Reflect-form
    /// meta-ctors and field-less functors keep their positional shape ([`PositionalPlan::Skip`]).
    pub(crate) fn positional_to_named_plan(
        &self,
        functor: Symbol,
        named_fields: &[Symbol],
        pos_count: usize,
    ) -> PositionalPlan {
        if pos_count == 0 {
            return PositionalPlan::Skip;
        }
        // The reflect `Expr` / `Pattern` meta-ctors (`ho_apply`, `match_expr`, …)
        // carry a positional shape that IS the reflect encoding, not user
        // named-field application — mirrors the loader's exclusion.
        if node_occurrence::is_reflect_form_functor(self, functor)
            || self.qualified_name_of(functor).starts_with("anthill.reflect.")
        {
            return PositionalPlan::Skip;
        }
        let Some(all_fields) = self.entity_field_names(functor) else {
            // No declared fields (anonymous tuple / ad-hoc structure): nothing to
            // map onto, leave positional.
            return PositionalPlan::Skip;
        };
        let unfilled: SmallVec<[Symbol; 4]> = all_fields
            .iter()
            .copied()
            .filter(|f| !named_fields.contains(f))
            .collect();
        if pos_count > unfilled.len() {
            return PositionalPlan::OverArity {
                declared: all_fields.iter().copied().collect(),
                unfilled: unfilled.len(),
            };
        }
        let mut assign = unfilled;
        assign.truncate(pos_count);
        PositionalPlan::Assign(assign)
    }

    /// `resolve_sort_instantiation_param(?spec, ?param_name, ?value)` — given a
    /// `SortView(sort, named…)` instance and a `Ref`/`Fn` param symbol, bind
    /// `?value` to the instance's binding for that param (fail if none). Delays
    /// if `?spec` or `?param_name` is unbound. `TermView` goal (WI-482); the
    /// `SortView`/param carriers are reified via `carrier_term`.
    fn builtin_resolve_sort_inst_param<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        if !matches!(goal.head(self), ViewHead::Functor { pos_arity, .. } if pos_arity >= 3) {
            return BuiltinResult::Failure;
        }
        let inst_val = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            Some(v) => v,
            None => return BuiltinResult::Failure,
        };
        let param_val = match self.walk_arg(goal.pos_arg(self, 1), subst) {
            Some(v) => v,
            None => return BuiltinResult::Failure,
        };
        if self.value_is_unbound_var(&inst_val) || self.value_is_unbound_var(&param_val) {
            return BuiltinResult::delay();
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 2), subst);
        // The param arg names a `Ref`, or a nullary-`Fn` name term.
        let Some(param_term) = self.carrier_term(&param_val) else {
            return BuiltinResult::Failure;
        };
        let param_sym = match self.terms.get(param_term) {
            Term::Ref(sym) => *sym,
            Term::Fn { functor, .. } => *functor,
            _ => return BuiltinResult::Failure,
        };
        // The instance must be `SortView(sort_name, named_args…)`; find the
        // named binding for `param_sym`.
        let Some(inst_term) = self.carrier_term(&inst_val) else {
            return BuiltinResult::Failure;
        };
        let value_tid = match self.terms.get(inst_term).clone() {
            Term::Fn { ref functor, ref named_args, .. } if self.symbols.name(*functor) == "SortView" => {
                named_args.iter().find(|(sym, _)| *sym == param_sym).map(|(_, tid)| *tid)
            }
            _ => None,
        };
        match value_tid {
            Some(val) => self.finish_result(target, val),
            None => BuiltinResult::Failure,
        }
    }

    // ── Equality and comparison builtins ─────────────────────

    /// `eq(?a, ?b)` — structural equality after walking. Succeeds if both
    /// args resolve to the same TermId (hash-consed identity = structural equality).
    /// Delays only on flex (`Var::Global`); rigid vars compare by TermId
    /// identity (hash-consing ensures `Rigid(a) == Rigid(a)`).
    fn builtin_eq<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        match self.eq_operands(goal, subst) {
            EqOperands::Delay => BuiltinResult::delay(),
            EqOperands::Ready(a, b) => {
                if self.values_equal(&a, &b) { BuiltinResult::Success } else { BuiltinResult::Failure }
            }
            EqOperands::Absent => BuiltinResult::Failure,
        }
    }

    /// WI-616 (proposal 051 Phase 2) — `eq(?a, ?b)`, the SEMANTIC `PartialEq.eq` spec
    /// op. See [`Self::sem_eq_core`].
    fn builtin_sem_eq<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        self.sem_eq_core(goal, subst, true)
    }

    /// WI-616 — `neq(?a, ?b)`, semantic inequality (`neq(a,b) <=> not(eq(a,b))`,
    /// the `Eq` law): [`Self::sem_eq_core`] with the verdict inverted.
    fn builtin_sem_neq<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        self.sem_eq_core(goal, subst, false)
    }

    /// WI-616 (proposal 051 Phase 2) — the shared core of semantic `eq`/`neq`
    /// (`positive` = which verdict "equal" maps to). Outcomes, in order:
    ///
    /// 1. **Reflexivity** — structurally identical operands are equal under any
    ///    lawful `Eq` instance: verdict with no lookups (the hot path, and
    ///    exactly the pre-WI-616 answer).
    /// 2. **Dispatch** — an operand whose head functor keys the load-time
    ///    eq-dispatch index ([`KnowledgeBase::eq_dispatch_target`]: the carrier
    ///    sort declares its OWN `eq` override — `Set.eq`/`Map.eq`, the
    ///    WI-350/WI-444 short-name convention): prove `<carrier>.eq(a, b)` by a
    ///    bounded SUB-RESOLUTION ([`Self::sem_eq_dispatch`]). Only GROUND
    ///    operand pairs dispatch — `=` is a TEST and must never bind
    ///    (kernel-language.md §8.3), and a sub-proof over non-ground operands
    ///    would enumerate bindings; a non-ground operand suspends (Delay) until
    ///    other goals ground it, else residualizes. The abstract-argument tier
    ///    (requirement dictionaries, WI-300 Tier B) stays gated on the
    ///    SLD→eval bridge (WI-625).
    /// 3. **Buried override** — no override at either head, but an overriding
    ///    carrier is REACHABLE inside an operand (`some({1,2})` vs
    ///    `some({2,1})`): the structural verdict would be unsound (the WI-573
    ///    reasoning — structural recursion ignores the inner carrier's `eq`),
    ///    so suspend as undecided rather than decide either way.
    /// 4. **Structural** — purely structural operands get the structural
    ///    verdict: structural equality IS their instance (`Int` stays an i64
    ///    compare).
    fn sem_eq_core<V: TermView>(
        &mut self,
        goal: &V,
        subst: &Substitution,
        positive: bool,
    ) -> BuiltinResult {
        match self.eq_operands(goal, subst) {
            EqOperands::Delay => BuiltinResult::delay(),
            EqOperands::Absent => BuiltinResult::Failure,
            EqOperands::Ready(a, b) => self.sem_eq_values(a, b, subst, positive),
        }
    }

    /// WI-616/WI-625/WI-664 — the VALUE-level core of semantic `eq`/`neq`, shared
    /// by [`Self::sem_eq_core`] (the SLD goal, after [`Self::eq_operands`] walks the
    /// operands) and the WI-664 field-wise recursion (each field pair). `positive`
    /// requests the EQUAL verdict (`eq`) or its negation (`neq`). Outcome order is
    /// [`Self::sem_eq_core`]'s doc, with the WI-664 field-wise step inserted between
    /// the Float-pair (1) and reflexivity (2) outcomes.
    fn sem_eq_values(
        &mut self,
        a: Value,
        b: Value,
        subst: &Substitution,
        positive: bool,
    ) -> BuiltinResult {
        // (1) Float operand pair — IEEE `==` (nan != nan, -0.0 == +0.0), NOT the
        // structural reflexivity shortcut below (which reads nan == nan through
        // `OrderedFloat`). Mirrors eval's `float_ieee_eq` so resolver, interpreter,
        // and C++ codegen agree (the WI-645 acceptance).
        if let (Some(x), Some(y)) = (self.value_f64(&a), self.value_f64(&b)) {
            return sem_verdict(x == y, positive);
        }
        // WI-664: a composite reaching an UNSHIELDED partial (Float) carrier
        // compares FIELD-WISE, not by the structural reflexivity shortcut below
        // (which would launder a nested NaN). Mirrors eval's `semantic_equal`; a
        // lawful-Eq boundary (`TotalFloat`/`Set`/`Map`, own eq) is not a partial
        // carrier and is untouched.
        if self.value_reaches_partial_carrier(&a) || self.value_reaches_partial_carrier(&b) {
            if let Some(result) = self.composite_field_wise_sem_eq(&a, &b, subst, positive) {
                return result;
            }
            // Not both same-shape composites: fall through to the structural verdict.
        }
        // (2) Reflexivity — structurally-identical operands (sound here: no
        // unshielded partial carrier reaches this point).
        if self.values_equal(&a, &b) {
            return sem_verdict(true, positive);
        }
        // (3) No carrier overrides eq at all (the common KB): straight to
        // the structural verdict — no per-operand probes or scans.
        if !self.has_eq_dispatch_entries() {
            return sem_verdict(false, positive);
        }
        // (4) Head-carrier override over GROUND operands ⇒ dispatch.
        let target = self
            .sem_eq_dispatch_target(&a)
            .or_else(|| self.sem_eq_dispatch_target(&b));
        if let Some(target) = target {
            if !self.value_deep_ground(&a, subst) || !self.value_deep_ground(&b, subst) {
                return BuiltinResult::delay();
            }
            return self.sem_eq_dispatch(target, a, b, subst, positive);
        }
        // (5) Buried override → suspend rather than mis-decide structurally.
        if self.value_reaches_eq_override(&a, subst)
            || self.value_reaches_eq_override(&b, subst)
        {
            return BuiltinResult::delay();
        }
        // (6) Structural verdict.
        sem_verdict(false, positive)
    }

    /// WI-664 — field-wise SEMANTIC equality for two composites whose carrier is a
    /// derived `NonEq` (field-wise) carrier: decompose to identical shape and AND
    /// [`Self::sem_eq_values`] over the matching fields, so a nested `Float` follows
    /// IEEE. `Some(sem_verdict(false, …))` on a shape mismatch; `None` when the
    /// operands are not both functor-headed composites (caller keeps the structural
    /// verdict). Requires GROUND operands — a var field can't be IEEE-compared, so
    /// a non-ground operand suspends (Delay), consistent with the dispatch path.
    fn composite_field_wise_sem_eq(
        &mut self,
        a: &Value,
        b: &Value,
        subst: &Substitution,
        positive: bool,
    ) -> Option<BuiltinResult> {
        // Shared shape-decomposition (mirrors eval's `composite_field_wise_eq`).
        let pairs = match self.same_shape_child_pairs(a, b) {
            super::eq_derive::FieldPairs::NotComposite => return None, // keep structural verdict
            super::eq_derive::FieldPairs::Mismatch => return Some(sem_verdict(false, positive)),
            super::eq_derive::FieldPairs::Pairs(pairs) => {
                // A var field can't be IEEE-compared: suspend like the dispatch path.
                if !self.value_deep_ground(a, subst) || !self.value_deep_ground(b, subst) {
                    return Some(BuiltinResult::delay());
                }
                pairs
            }
        };
        // Recurse per field; the composite is EQUAL iff every field is. `positive =
        // true` per field, so a `Failure` means "this field is unequal" — a DEFINITE
        // unequal verdict that short-circuits regardless of other fields (sound: one
        // unequal field makes the composite unequal). An UNDECIDED field must NOT
        // short-circuit: WI-628 — a LATER field may TRUNCATE, and returning on the
        // first flounder would DROP that truncation, making soundness depend on
        // field order (a truncated field would read as a mere flounder → the outer
        // guard decides from an incomplete search). So scan ALL fields, accumulating
        // the strongest undecidedness: a truncation ANYWHERE ⇒ the composite is
        // truncated. `eq` never binds, so evaluating a later field after an earlier
        // flounder has no side effect.
        let mut saw_delay = false;
        let mut saw_truncated = false;
        for (ca, cb) in pairs {
            match self.sem_eq_values(ca, cb, subst, true) {
                BuiltinResult::Success => {}
                BuiltinResult::Failure => return Some(sem_verdict(false, positive)),
                BuiltinResult::Delay { truncated } => {
                    saw_delay = true;
                    saw_truncated |= truncated;
                }
                // `eq` never binds; a surprise binding can't be trusted as a verdict.
                BuiltinResult::SuccessWithBindings(_) => saw_delay = true,
            }
        }
        if saw_delay {
            return Some(BuiltinResult::Delay { truncated: saw_truncated });
        }
        Some(sem_verdict(true, positive))
    }

    /// WI-616 — the eq-dispatch index probe for one operand: its head functor's
    /// entry (an entity constructor or self-returning op of an eq-overriding
    /// carrier sort — see `load::build_sort_ops_table` pass 3). One O(1) hash
    /// lookup; scalars and headless values read `None` (structural).
    pub(crate) fn sem_eq_dispatch_target(&self, v: &Value) -> Option<Symbol> {
        let functor = match v.head(self) {
            ViewHead::Ref(s) | ViewHead::Functor { functor: Some(s), .. } => s,
            _ => return None,
        };
        self.eq_dispatch_target(functor)
    }

    /// WI-616 — prove the dispatched carrier equality `target(a, b)` by a
    /// bounded SUB-RESOLUTION (a fresh [`SearchStream`], fresh depth budget —
    /// rules-backed instances need no SLD→eval bridge; ordinary SLD is the
    /// evaluator). The sub-proof is a closed TEST: its bindings never reach the
    /// caller's frame (`=` never binds), and the first DEFINITE proof settles
    /// the verdict (no solution multiplicity leaks — `eq` stays
    /// semi-deterministic). Three-way, never wrong-by-truncation:
    /// * a definite proof            → equal (`Success`/`Failure` per `positive`);
    /// * exhausted, complete search  → not equal;
    /// * undecided → `Delay { truncated }` (never decide from an incomplete
    ///   search). WI-628: the truncated bit is CARRIED, not collapsed — a TRUNCATED
    ///   sub-proof (depth cap / bridge re-entry cap) yields `truncated: true`, which
    ///   the step loop folds onto the outer stream so an eager NAF/guard consumer
    ///   sees the incomplete search; only-residual (floundered) but COMPLETE
    ///   solutions yield `truncated: false`.
    fn sem_eq_dispatch(
        &mut self,
        target: Symbol,
        a: Value,
        b: Value,
        subst: &Substitution,
        positive: bool,
    ) -> BuiltinResult {
        // Close the operands under the caller's σ: groundness was checked
        // AGAINST σ, but the sub-resolution starts from an empty substitution —
        // a σ-bound variable inside an entity-carried operand would enter the
        // sub-proof locally flex (flounder at best). The sub-proof runs
        // KB-only (no Γ overlay — a Γ-relevant operand is symbolic and already
        // delayed before the builtin ran; see the WI-537/WI-067 pre-checks).
        let a = self.reify_value(&a, subst);
        let b = self.reify_value(&b, subst);
        // WI-625 gap 2: a BODIED instance-fact eq op (`fact PartialEq[T = X,
        // eq = myEq]` with `myEq` a match/if/recursive function) is NOT a
        // rule-backed predicate — SLD finds no clause for it, so `prove_rule_
        // predicate` would spuriously Refute. Run it through the eval bridge and
        // read the Bool verdict; a body-less rule-backed carrier op (`Set.eq`,
        // proved via its discrim-indexed `rule eq` clauses) still proves
        // relationally. The discriminator is the operation's own body: `Set.eq`
        // is a body-less `operation eq(...) -> Bool` backed by separate rules.
        if super::typing::op_has_runnable_body(self, target) {
            return match self.bridge_eq_op_to_eval(target, a, b) {
                Ok(BridgeEqOutcome::Decided(v)) => sem_verdict(v, positive),
                // WI-628: carry the incompleteness bit straight through — a re-entry
                // cap OR a nested truncation surfaced via the eval bridge is
                // `truncated: true`, propagated so an eager NAF/guard consumer does
                // not decide from an incomplete run; a clean bridge-mode suspend is
                // `truncated: false` (a complete flounder).
                Ok(BridgeEqOutcome::Undecided { truncated }) => BuiltinResult::Delay { truncated },
                // The op's own runtime error also residualizes (WI-483
                // substitution-transparency) — a plain, non-truncated delay.
                Err(_) => BuiltinResult::delay(),
            };
        }
        match self.prove_rule_predicate(target, vec![a, b]) {
            PredicateProof::Proved => sem_verdict(true, positive),
            PredicateProof::Refuted => sem_verdict(false, positive),
            // Never decide from an incomplete search: suspend as undecided, carrying
            // the truncated bit. WI-628 — a TRUNCATED sub-proof taints the outer
            // stream (the step loop folds `Delay { truncated: true }` onto it), so a
            // guard reading empty-as-refute sees it; a flounder over a complete
            // search stays a non-truncated delay.
            PredicateProof::Undecided { truncated } => BuiltinResult::Delay { truncated },
        }
    }

    /// WI-616/WI-625 — prove a rule-backed predicate goal `pred(args)` (a
    /// carrier's own `eq`/`neq`/`subset`/`member`, …) by a CLOSED, BOUNDED
    /// sub-resolution: a fresh [`SearchStream`] on its own generous depth budget.
    /// Rules-backed instances need no SLD→eval bridge — ordinary SLD is the
    /// evaluator. Operands must be CLOSED (ground): the resolver reifies under σ
    /// before calling ([`Self::sem_eq_dispatch`]); the eval→SLD bridge (WI-625)
    /// passes already-ground interpreter values. The sub-proof is a closed TEST —
    /// its bindings never reach the caller's frame — and three-way, never
    /// wrong-by-truncation (see [`PredicateProof`]).
    pub(crate) fn prove_rule_predicate(&mut self, pred: Symbol, args: Vec<Value>) -> PredicateProof {
        // Generous but bounded: the relational instances consume one depth unit
        // per goal along a branch (Set: O(n²) for n elements), so the outer
        // default of 100 would truncate at ~10 elements. Truncation degrades to
        // UNDECIDED, never a wrong verdict. WI-628: production uses the fixed
        // `DEFAULT_SEM_EQ_SUB_DEPTH`; a `cfg(test)` field lowers it so a unit test
        // can force truncation cheaply (no production mutable knob).
        #[cfg(not(test))]
        let max_depth = Self::DEFAULT_SEM_EQ_SUB_DEPTH;
        #[cfg(test)]
        let max_depth = self.sem_eq_sub_depth;
        let goal = self.make_goal_value(pred, args);
        let config = ResolveConfig { max_depth, ..ResolveConfig::default() };
        let stream = self.resolve_lazy_goals(vec![goal], &config);
        // WI-628: shared drain — `truncated` rides with the verdict so a depth-cut
        // search degrades to UNDECIDED, never a wrong Refuted. Truncation is kept
        // DISTINCT from a mere flounder (checked FIRST — a search that both
        // floundered and truncated is still incomplete): only genuine truncation
        // must propagate to the outer stream (see `PredicateProof::Undecided`).
        let v = stream.drain_verdict(self);
        if v.definite {
            PredicateProof::Proved
        } else if v.truncated {
            PredicateProof::Undecided { truncated: true }
        } else if v.residual {
            PredicateProof::Undecided { truncated: false }
        } else {
            PredicateProof::Refuted
        }
    }

    /// WI-689 — the ONE generic structural fold the sem-eq / groundness gates
    /// reduce to (see [`GateSpec`]). Reads any [`TermView`] carrier through the
    /// view, so a new value carrier rides it with no per-gate arm to add.
    ///
    /// Per-carrier σ-read distinction (the WI-685 invariant this preserves): a
    /// `Term` carrier path-compresses through σ via [`Self::walk`] (term→term
    /// chase) BEFORE its head is read — matching the former `term_*` twins that led
    /// with `walk`; a value / occurrence carrier reads its head directly and chases
    /// a `Var(Global)` head through `resolve_as_value` below. Only the σ-chasing
    /// gates walk/chase; the structural gates read already-reduced values verbatim.
    /// `depth` increments on each child and each σ-chase (never on the term-walk),
    /// so a capped gate ([`REACHES_EQ_OVERRIDE`]) counts exactly as its twins did.
    pub(crate) fn fold_gate(
        &self,
        v: &Value,
        subst: Option<&Substitution>,
        depth: usize,
        spec: GateSpec,
    ) -> bool {
        if let Some((cap, at_cap)) = spec.depth_cap {
            if depth >= cap {
                return at_cap;
            }
        }
        // A Term carrier leads with `walk` (term→term path compression) when a σ is
        // present; the structural gates pass `subst: None` — no bindings to follow —
        // and read the head as-is (an inert empty σ, without minting one per call).
        // Other carriers read the head directly too (a `Var(Global)` head is chased
        // below).
        let walked;
        let v = match (v, subst) {
            (Value::Term { id, .. }, Some(s)) if spec.chase_sigma => {
                walked = Value::term(self.walk(*id, s));
                &walked
            }
            _ => v,
        };
        match v.head(self) {
            // A flex `Global` head under a σ-chasing gate: resolve and recurse; an
            // unbound flex var (or an absent σ) is never itself ground / an override /
            // a partial carrier / a bodied op-call.
            ViewHead::Var(Var::Global(vid)) if spec.chase_sigma => {
                match subst.and_then(|s| s.resolve_as_value(vid)) {
                    Some(bound) => {
                        let bound = bound.clone();
                        self.fold_gate(&bound, subst, depth + 1, spec)
                    }
                    None => false,
                }
            }
            // A rigid / DeBruijn skolem (or a flex `Global` in a structural gate):
            // a bare variable satisfies no gate.
            ViewHead::Var(_) => false,
            ViewHead::Opaque => spec.opaque,
            head => match spec.head_check.classify(self, &head) {
                HeadVerdict::Stop(verdict) => verdict,
                HeadVerdict::Recurse => {
                    let pos_arity = match head {
                        ViewHead::Functor { pos_arity, .. } => pos_arity,
                        _ => 0,
                    };
                    self.fold_gate_children(v, subst, depth, pos_arity, spec)
                }
            },
        }
    }

    /// Combine the child verdicts of a functor-headed node per [`Combine`] —
    /// short-circuiting `true` for `Any` and `false` for `All`, else returning the
    /// combine's identity (`All` ⇒ `true`, `Any` ⇒ `false`) for a childless node.
    fn fold_gate_children(
        &self,
        v: &Value,
        subst: Option<&Substitution>,
        depth: usize,
        pos_arity: usize,
        spec: GateSpec,
    ) -> bool {
        for i in 0..pos_arity {
            match v.pos_arg(self, i) {
                Some(child) => {
                    let r = self.fold_gate(&child.to_value(), subst, depth + 1, spec);
                    match spec.combine {
                        Combine::Any if r => return true,
                        Combine::All if !r => return false,
                        _ => {}
                    }
                }
                // WI-685 hardening: a child the head reports but the view cannot
                // resolve is a carrier/view desync — surface it loudly, never a
                // silent skip. Unreachable for the stored-child carriers
                // (Entity/Tuple/Term, whose `pos_arity` equals the stored vec len);
                // a guard for synthetic occurrence children.
                None => debug_assert!(
                    false,
                    "fold_gate_children: head reports positional child {i} the view cannot resolve"
                ),
            }
        }
        for key in v.named_keys(self) {
            match v.named_arg(self, key) {
                Some(child) => {
                    let r = self.fold_gate(&child.to_value(), subst, depth + 1, spec);
                    match spec.combine {
                        Combine::Any if r => return true,
                        Combine::All if !r => return false,
                        _ => {}
                    }
                }
                None => debug_assert!(
                    false,
                    "fold_gate_children: named_keys reports a key named_arg cannot resolve"
                ),
            }
        }
        matches!(spec.combine, Combine::All)
    }

    /// WI-616 — deep groundness of a σ-walked operand `Value`: no unbound variable
    /// anywhere inside. The dispatch gate. Now a thin [`Self::fold_gate`] over
    /// [`DEEP_GROUND`] — every carrier (term / entity / tuple / occurrence, WI-685)
    /// walks through the ONE view-generic fold; scalars and runtime handles are
    /// ground.
    pub(crate) fn value_deep_ground(&self, v: &Value, subst: &Substitution) -> bool {
        self.fold_gate(v, Some(subst), 0, DEEP_GROUND)
    }

    /// WI-616 — does `v` STRUCTURALLY CONTAIN (at any depth) a value headed by an
    /// eq-dispatch-index functor? Outcome 3's scan: an overriding carrier buried
    /// under non-overriding structure makes the structural verdict unsound, so the
    /// compare suspends instead of deciding. Present structure only — an unbound
    /// variable is not (yet) an overriding value, matching the structural test's
    /// instantiation-time semantics. Conservative `true` at the depth cap
    /// ([`REACH_DEPTH_CAP`]).
    ///
    /// WI-625 gap 1: an eval-side entry with a fresh, empty σ — a bridged
    /// interpreter's operand `Value`s are already reified, carrying no resolution
    /// bindings — so the interpreter's `semantic_equal` suspends on a buried
    /// override exactly where the resolver delays, and the bridge never imports a
    /// membership-wrong structural verdict.
    pub(crate) fn value_has_buried_eq_override(&self, v: &Value) -> bool {
        // No σ — the operands are already reified; `None` is the inert empty σ the
        // reach scan would otherwise never consult, without minting one per call.
        self.fold_gate(v, None, 0, REACHES_EQ_OVERRIDE)
    }

    /// WI-616 — the σ-threaded reach scan ([`REACHES_EQ_OVERRIDE`]) whose every
    /// carrier (term / entity / tuple / occurrence, WI-685) reads through the ONE
    /// view-generic fold.
    fn value_reaches_eq_override(&self, v: &Value, subst: &Substitution) -> bool {
        self.fold_gate(v, Some(subst), 0, REACHES_EQ_OVERRIDE)
    }

    /// WI-511: structural value equality that is CARRIER-AWARE — routes through
    /// [`views_structurally_equal`] so a 0-ary constructor compares equal across
    /// carriers (`Value::Entity{c}` vs `Value::Term(Ref(c))`), the cross-carrier
    /// case the now-removed carrier-blind `Value::structural_eq` (WI-486) left to
    /// `TermView`. The `eq`/`neq` operands are already walked (flex vars `Delay`,
    /// so none reach here) and a rigid var compares by `Var` identity in both — so
    /// this only ADDS the cross-carrier bridge, with no same-carrier regression.
    fn values_equal(&self, a: &Value, b: &Value) -> bool {
        crate::kb::term_view::views_structurally_equal(self, a, b)
    }

    /// Walk the two operands of an `eq`/`neq` goal: `Delay` if either is flex
    /// (`Var::Global`), else the two `Value`s. Two term values compare by
    /// hash-consed-`TermId` identity (= the original `a == b` test); occurrence
    /// values compare structurally (WI-246) — both via `views_structurally_equal`.
    fn eq_operands<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> EqOperands {
        let (a, b) = match (
            self.walk_arg(goal.pos_arg(self, 0), subst),
            self.walk_arg(goal.pos_arg(self, 1), subst),
        ) {
            (Some(a), Some(b)) => (a, b),
            _ => return EqOperands::Absent,
        };
        // WI-482: project a dispatched dot operand (`eq(?v, ?p.x)`); WI-483: fold a
        // dispatched method-op operand (`eq(?v, ?b.peek())`) to its value.
        let a = self.reduce_operand(a, subst);
        let b = self.reduce_operand(b, subst);
        // WI-483: a residual (complex, unfolded) op-call operand is treated as
        // un-ground — delay rather than fail, so a complex callee residualizes
        // (substitution transparency), not silently mismatches. A `Value::Node`
        // op-call carrier reads directly in its native carrier (WI-685).
        if self.is_unreduced_op_call(&a) || self.is_unreduced_op_call(&b) {
            return EqOperands::Delay;
        }
        // WI-685: operands ride in their native carrier — a `Value::Node`
        // occurrence is compared structurally by [`Self::values_equal`] and gated
        // by the carrier-neutral `value_deep_ground` / `value_reaches_eq_override`,
        // so no collapse to a hash-consed `Term` is needed.
        if self.value_is_flex(&a) || self.value_is_flex(&b) {
            return EqOperands::Delay;
        }
        EqOperands::Ready(a, b)
    }

    // ── Unification builtin (proposal 049) ───────────────────────

    /// `unify(?a, ?b)` — structural unification, the object-level face of `<=>`
    /// (and `let ?v = e`). The bind-counterpart of [`Self::builtin_eq`]: the
    /// same structural walk, but a flex var head **binds** to the other side (an
    /// occurs-checked substitution effect) instead of being compared, and a
    /// functor match recurses binding sub-vars on EITHER side (`some(?x) <=>
    /// some(3)` binds `?x ↦ 3`, which `eq` instead fails). Returns
    /// `SuccessWithBindings` carrying the new bindings as a frame effect, plain
    /// `Success` when the two sides are already equal with nothing to bind,
    /// `Delay` on a complex op-call operand (substitution transparency), and
    /// `Failure` on a mismatch or occurs-check violation. Carrier-agnostic and
    /// structural-only — it never dispatches (the proposal Invariant).
    fn builtin_unify<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let (a, b) = match (
            self.walk_arg(goal.pos_arg(self, 0), subst),
            self.walk_arg(goal.pos_arg(self, 1), subst),
        ) {
            (Some(a), Some(b)) => (a, b),
            _ => return BuiltinResult::Failure,
        };
        // Accumulate new bindings in a working substitution chained over the
        // caller's σ: the parent gives read-through so a var bound earlier in
        // THIS unify is chased on its next occurrence, while only `work`'s own
        // top-level bindings travel back via `SuccessWithBindings` (the resolver
        // lifts `extra.bindings`, never the parent).
        let mut work = Substitution::with_parent(subst.clone());
        match self.unify_values(a, b, &mut work) {
            UnifyOutcome::Delay => BuiltinResult::delay(),
            UnifyOutcome::Fail => BuiltinResult::Failure,
            // A binding to two structurally-distinct values surfaces as a
            // `work` contradiction (the chase prevents it on the linear-var
            // path; this is the carrier-edge backstop) — no unifier.
            UnifyOutcome::Ok if work.is_contradiction() => BuiltinResult::Failure,
            UnifyOutcome::Ok if work.bindings.is_empty() => BuiltinResult::Success,
            UnifyOutcome::Ok => BuiltinResult::SuccessWithBindings(work),
        }
    }

    /// WI-300 — the rule-body requirement guard. The converter desugars a
    /// rule-body `requires(X)` to `find_dictionary(X)`; the typer sweep
    /// ([`super::typing::record_find_dictionary_grounding`]) then rewrites it into
    /// `find_dictionary(spec_base, op_functor, op_arg…)` — `spec_base` is spec X's
    /// nominal sort, `op_functor` a body call to one of X's operations, and
    /// `op_arg…` that call's carrier arguments (the witness redex whose types
    /// decide the instance). At the current binding this reads each argument's
    /// carried type and shares the WI-596 `provides` decision with the `[simp]`
    /// guard: `Success` iff every carrier provides X, `Failure` if a ground carrier
    /// has no provider, `Delay` (suspend-as-residual, never NAF-decide; WI-519 /
    /// WI-067) when a carrier type is under-determined. A goal with fewer than two
    /// positional args — an un-rewritten `find_dictionary(X)`, which the typer sweep
    /// turns into either the ≥2-arg form or a hard load error, so it is unreachable
    /// from a clean load; only a direct hand-written call reaches it — declines to
    /// fire (returns `Failure`) rather than wrongly succeeding.
    fn builtin_find_dictionary<V: TermView>(
        &mut self,
        goal: &V,
        subst: &Substitution,
    ) -> BuiltinResult {
        let pos_arity = match goal.head(self) {
            ViewHead::Functor { pos_arity, .. } => pos_arity,
            _ => return BuiltinResult::Failure,
        };
        if pos_arity < 2 {
            return BuiltinResult::Failure;
        }
        // A nominal-symbol argument (spec base / op functor) rides as a `Ref`, an
        // as-yet-unresolved `Ident`, or a nullary `Fn` (`make_name_term` shape).
        fn head_symbol(kb: &KnowledgeBase, v: &Value) -> Option<Symbol> {
            match v.head(kb) {
                ViewHead::Ref(s) | ViewHead::Ident(s) => Some(s),
                ViewHead::Functor { functor: Some(s), .. } => Some(s),
                _ => None,
            }
        }
        let spec_sort = match self
            .walk_arg(goal.pos_arg(self, 0), subst)
            .and_then(|v| head_symbol(self, &v))
        {
            Some(s) => s,
            None => return BuiltinResult::Failure,
        };
        let op_functor = match self
            .walk_arg(goal.pos_arg(self, 1), subst)
            .and_then(|v| head_symbol(self, &v))
        {
            Some(s) => s,
            None => return BuiltinResult::Failure,
        };
        let mut arg_vals: Vec<Value> = Vec::with_capacity(pos_arity - 2);
        for i in 2..pos_arity {
            match self.walk_arg(goal.pos_arg(self, i), subst) {
                Some(v) => arg_vals.push(v),
                None => return BuiltinResult::Failure,
            }
        }
        match super::typing::find_dictionary_guard(self, subst, spec_sort, op_functor, &arg_vals) {
            super::typing::FindDictOutcome::Fire => BuiltinResult::Success,
            super::typing::FindDictOutcome::DontFire => BuiltinResult::Failure,
            super::typing::FindDictOutcome::Suspend => BuiltinResult::delay(),
        }
    }

    /// Term-level structural unification (proposal 049's "honest signature"):
    /// the most general unifier of `a` and `b` as a substitution, or `None`
    /// when they do not unify. The DATA face shared with the object-level
    /// `<=>` builtin — `<=>` installs this σ as a frame effect, the term-level
    /// `reflect.unify` returns it as data (for reflection and the WI-010
    /// self-hosted resolver). Occurs-checked; a delaying op-call operand (only
    /// reachable from occurrence-carried inputs) reads as non-unifiable here.
    pub fn unify_terms(&mut self, a: TermId, b: TermId) -> Option<Substitution> {
        let mut work = Substitution::new();
        match self.unify_values(Value::term(a), Value::term(b), &mut work) {
            UnifyOutcome::Ok if !work.is_contradiction() => Some(work),
            _ => None,
        }
    }

    /// The recursive core (proposal 049 steps 1–6). Chases each side's head var
    /// through `work`, head-normalizes it on reach (project `?p.x` / fold a
    /// foldable `peek(?b)` — head-only, no descent into constructor args), then:
    /// a complex op-call head delays; a flex var head binds (occurs-checked) to
    /// the other side; two concrete heads compare structurally and recurse on a
    /// functor match. Children are head-normalized on their own reach (the
    /// laziness — a bound cell keeps its interior unreduced).
    fn unify_values(&mut self, a: Value, b: Value, work: &mut Substitution) -> UnifyOutcome {
        // Step 1: chase head vars through σ (including bindings made earlier in
        // THIS unify), then head-normalize on reach.
        let a = self.chase_value(a, work);
        let b = self.chase_value(b, work);
        let a = self.reduce_operand(a, work);
        let b = self.reduce_operand(b, work);
        // Step 2: an unreduced complex op-call head ⇒ delay the whole goal
        // (never commit to a structural verdict over an uninterpreted callee).
        if self.is_unreduced_op_call(&a) || self.is_unreduced_op_call(&b) {
            return UnifyOutcome::Delay;
        }
        // Step 3: a flex var on either side ⇒ occurs-checked bind-and-stop.
        if let Some(vid) = self.unify_flex_var(&a) {
            return self.unify_bind(vid, b, work);
        }
        if let Some(vid) = self.unify_flex_var(&b) {
            return self.unify_bind(vid, a, work);
        }
        // Steps 4–6: both heads concrete — structural compare + recurse.
        self.unify_concrete(&a, &b, work)
    }

    /// Step 3: bind flex `vid` to the head-normalized `other` side, occurs-checked.
    /// `?v <=> f(?v)` fails (no cyclic term — "know errors early"); `?v <=> ?v`
    /// binds nothing. The bound value's interior stays unreduced.
    fn unify_bind(&mut self, vid: VarId, other: Value, work: &mut Substitution) -> UnifyOutcome {
        if self.unify_flex_var(&other) == Some(vid) {
            return UnifyOutcome::Ok; // ?v <=> ?v
        }
        if self.occurs_in_value(vid, &other, work) {
            return UnifyOutcome::Fail; // occurs-check
        }
        work.bind_value(self, vid, other);
        UnifyOutcome::Ok
    }

    /// Steps 4–6: unify two concrete-headed values structurally, recursing on a
    /// functor match (positional then named children, head-normalized on reach)
    /// and binding sub-vars on either side; fail-fast on any
    /// functor/arity/scalar/head-kind mismatch BEFORE reducing children — the
    /// work a bottom-first derive pass would forfeit. The bind-enabled twin of
    /// [`views_structurally_equal`] (which only tests).
    fn unify_concrete(&mut self, a: &Value, b: &Value, work: &mut Substitution) -> UnifyOutcome {
        let eq_or = |same: bool| if same { UnifyOutcome::Ok } else { UnifyOutcome::Fail };
        // Rigid (skolem) / DeBruijn vars now head as `ViewHead::Var`, but the
        // concrete-head match below has no `Var` arm — mirror
        // [`views_structurally_equal`] (WI-108): two occurrences of the SAME such
        // var unify (reflexivity, no binding); a rigid var vs a different var or a
        // concrete term does NOT (a skolem must never bind, per `Var::Rigid`'s
        // "unifies only with another Rigid carrying the same id"). Flex `Global`
        // vars were already bound by `unify_values` before reaching here; without
        // this arm `!k <=> !k` would wrongly hit the `_ => Fail` catch-all below,
        // diverging from `eq`.
        if let (Some(va), Some(vb)) = (a.index_var(self), b.index_var(self)) {
            if va.is_rigid() || va.is_debruijn() || vb.is_rigid() || vb.is_debruijn() {
                return eq_or(va == vb);
            }
        }
        match (a.head(self), b.head(self)) {
            (ViewHead::Const(la), ViewHead::Const(lb)) => eq_or(la == lb),
            (ViewHead::Ref(sa), ViewHead::Ref(sb)) => eq_or(sa == sb),
            (ViewHead::Ident(sa), ViewHead::Ident(sb)) => eq_or(sa == sb),
            (ViewHead::Bottom, ViewHead::Bottom) => UnifyOutcome::Ok,
            (
                ViewHead::Functor { functor: fa, pos_arity: pa, named_arity: na },
                ViewHead::Functor { functor: fb, pos_arity: pb, named_arity: nb },
            ) => {
                if fa != fb || pa != pb || na != nb {
                    return UnifyOutcome::Fail; // step 4: fail-fast, no child reduction
                }
                for i in 0..pa {
                    let (ca, cb) = match (a.pos_arg(self, i), b.pos_arg(self, i)) {
                        (Some(ca), Some(cb)) => (ca.to_value(), cb.to_value()),
                        _ => return UnifyOutcome::Fail,
                    };
                    match self.unify_values(ca, cb, work) {
                        UnifyOutcome::Ok => {}
                        other => return other,
                    }
                }
                // Equal `named_arity` + every `a` key found-and-unified in `b`
                // ⇒ identical key sets (named args are duplicate-free, canonical
                // order), mirroring `views_structurally_equal`.
                for key in a.named_keys(self) {
                    let (ca, cb) = match (a.named_arg(self, key), b.named_arg(self, key)) {
                        (Some(ca), Some(cb)) => (ca.to_value(), cb.to_value()),
                        _ => return UnifyOutcome::Fail,
                    };
                    match self.unify_values(ca, cb, work) {
                        UnifyOutcome::Ok => {}
                        other => return other,
                    }
                }
                UnifyOutcome::Ok
            }
            // Var heads are handled before reaching here; rigid / DeBruijn /
            // opaque heads and any head-kind mismatch have no shared structure.
            _ => UnifyOutcome::Fail,
        }
    }

    /// The flex (`Global`) var id at a σ-walked value head across all carriers —
    /// `Value::Term(Var::Global)`, `Value::Node(Expr::Var(Global))`, and the
    /// value-level `Value::Var(Global)` (WI-109). The unify-side companion of
    /// [`Self::value_global_var`], which omits the `Value::Var` arm (eq/neq
    /// never meet one); unify must, since a bound child can ride as `Value::Var`.
    fn unify_flex_var(&self, v: &Value) -> Option<VarId> {
        match v {
            Value::Var(Var::Global(vid)) => Some(*vid),
            _ => self.value_global_var(v),
        }
    }

    /// WI-633 — the STRUCTURAL unifier behind the discrimination-tree match
    /// ([`Substitution::bind_value_unifying`], the `resolve_leaf` re-bind
    /// path). Rule-head matching is unification: a repeated head var imposes
    /// equality-up-to-unification on the query subterms it matched, not
    /// structural identity — `p(box(v: ?v), ?v)` queried
    /// `p(box(v: some(?x)), some(42))` binds `?x = 42`, where the
    /// structural-identity re-bind check false-dropped the candidate as a
    /// contradiction (silent 0 solutions).
    ///
    /// The `&self` sibling of [`Self::unify_values`]: the same flex-`Global`
    /// bind (occurs-checked, chased through `work`) and functor recursion,
    /// but NO operand reduction and NO delay — the tree match is structural
    /// (an unreduced op-call is concrete structure here, exactly as the tree
    /// indexed it; today's structural-identity check treats it the same way),
    /// and evaluation cannot run under the `&KnowledgeBase` the tree walk
    /// holds. `Rigid` and `DeBruijn` heads stay reflexive-only
    /// ([`Self::unify_concrete`] parity): a DeBruijn met here is either a
    /// rule-head var whose caller linkage `with_fresh_vars` threads (WI-624)
    /// or a binder-bound var inside a lambda where a bind would be
    /// capture-unsound — so the query-nonlinear-vs-head-var corner
    /// (`p(?x, ?x)` against head `p(?u, 42)`) still drops, as before.
    ///
    /// Returns `false` on mismatch or occurs violation; `work` may then hold
    /// partial bindings (the caller flags the whole substitution contradictory
    /// and every consumer drops it — the same discipline as `unify_values`).
    pub(crate) fn unify_match_values(&self, a: &Value, b: &Value, work: &mut Substitution) -> bool {
        let a = self.chase_value(a.clone(), work);
        let b = self.chase_value(b.clone(), work);
        // Flex `Global` on either side: occurs-checked bind-and-stop.
        let (fa, fb) = (self.unify_flex_var(&a), self.unify_flex_var(&b));
        if let (Some(x), Some(y)) = (fa, fb) {
            if x == y {
                return true; // ?v against ?v — nothing to bind
            }
        }
        if let Some(vid) = fa {
            if self.occurs_in_value(vid, &b, work) {
                return false;
            }
            work.bind_value(self, vid, b);
            return true;
        }
        if let Some(vid) = fb {
            if self.occurs_in_value(vid, &a, work) {
                return false;
            }
            work.bind_value(self, vid, a);
            return true;
        }
        // Rigid / DeBruijn heads: reflexive-only, mirroring `unify_concrete`.
        if let (Some(va), Some(vb)) = (a.index_var(self), b.index_var(self)) {
            if va.is_rigid() || va.is_debruijn() || vb.is_rigid() || vb.is_debruijn() {
                return va == vb;
            }
        }
        match (a.head(self), b.head(self)) {
            (ViewHead::Const(la), ViewHead::Const(lb)) => la == lb,
            (ViewHead::Ref(sa), ViewHead::Ref(sb)) => sa == sb,
            (ViewHead::Ident(sa), ViewHead::Ident(sb)) => sa == sb,
            (ViewHead::Bottom, ViewHead::Bottom) => true,
            (
                ViewHead::Functor { functor: ffa, pos_arity: pa, named_arity: na },
                ViewHead::Functor { functor: ffb, pos_arity: pb, named_arity: nb },
            ) => {
                if ffa != ffb || pa != pb || na != nb {
                    return false;
                }
                for i in 0..pa {
                    match (a.pos_arg(self, i), b.pos_arg(self, i)) {
                        (Some(ca), Some(cb)) => {
                            let (ca, cb) = (ca.to_value(), cb.to_value());
                            if !self.unify_match_values(&ca, &cb, work) {
                                return false;
                            }
                        }
                        _ => return false,
                    }
                }
                // Equal `named_arity` + every `a` key found-and-unified in `b`
                // ⇒ identical key sets (named args are duplicate-free,
                // canonical order), mirroring `unify_concrete`.
                for key in a.named_keys(self) {
                    match (a.named_arg(self, key), b.named_arg(self, key)) {
                        (Some(ca), Some(cb)) => {
                            let (ca, cb) = (ca.to_value(), cb.to_value());
                            if !self.unify_match_values(&ca, &cb, work) {
                                return false;
                            }
                        }
                        _ => return false,
                    }
                }
                true
            }
            // Opaque heads and any head-kind mismatch have no shared structure.
            _ => false,
        }
    }

    /// Resolve a value's head var through σ (no structural descent) — the
    /// value-level analogue of [`Self::walk`]. A flex var bound in `work` is
    /// replaced by its binding, chased transitively; a self-referential binding
    /// or an unbound var stops the chase. Everything else is returned unchanged.
    fn chase_value(&self, v: Value, work: &Substitution) -> Value {
        let mut cur = v;
        loop {
            let Some(vid) = self.unify_flex_var(&cur) else { return cur };
            match work.resolve_as_value(vid) {
                Some(bound) => {
                    let bound = bound.clone();
                    if self.unify_flex_var(&bound) == Some(vid) {
                        return bound; // ?v ↦ ?v
                    }
                    cur = bound;
                }
                None => return cur, // unbound flex var
            }
        }
    }

    /// Occurs-check: does flex `vid` appear anywhere in `value` after resolving
    /// through `work`? Walks every carrier structurally via [`TermView`].
    /// Rejects `?v <=> f(?v)` (proposal 049 step 3) before a cyclic term forms.
    /// `pub(crate)` for `with_fresh_vars` (WI-624): a nonlinear head match can
    /// thread a query var's own term back into its answer link; the link is
    /// occurs-checked against the links built so far before it enters σ.
    pub(crate) fn occurs_in_value(&self, vid: VarId, value: &Value, work: &Substitution) -> bool {
        // A var head: identity hit, or chase its binding (so `?w ↦ f(?v)` is
        // caught through `?v <=> ?w`).
        if let Some(w) = self.unify_flex_var(value) {
            if w == vid {
                return true;
            }
            return match work.resolve_as_value(w) {
                Some(bound) => {
                    let bound = bound.clone();
                    // Self-referential binding — no further structure to chase.
                    if self.unify_flex_var(&bound) == Some(w) {
                        false
                    } else {
                        self.occurs_in_value(vid, &bound, work)
                    }
                }
                None => false, // distinct unbound var
            };
        }
        match value.head(self) {
            ViewHead::Functor { pos_arity, .. } => {
                for i in 0..pos_arity {
                    if let Some(child) = value.pos_arg(self, i) {
                        if self.occurs_in_value(vid, &child.to_value(), work) {
                            return true;
                        }
                    }
                }
                for key in value.named_keys(self) {
                    if let Some(child) = value.named_arg(self, key) {
                        if self.occurs_in_value(vid, &child.to_value(), work) {
                            return true;
                        }
                    }
                }
                false
            }
            // Const / Ref / Ident / Bottom / Opaque carry no flex vars.
            _ => false,
        }
    }

    /// Generic comparison builtin for gt/lt/gte/lte.
    /// Compares Int/BigInt/Float values; delays if unbound, fails on type mismatch.
    fn builtin_cmp<V: TermView>(
        &mut self,
        goal: &V,
        subst: &Substitution,
        pred: impl Fn(std::cmp::Ordering) -> bool,
    ) -> BuiltinResult {
        let (a, b) = match (
            self.walk_arg(goal.pos_arg(self, 0), subst),
            self.walk_arg(goal.pos_arg(self, 1), subst),
        ) {
            (Some(a), Some(b)) => (a, b),
            _ => return BuiltinResult::Failure,
        };
        // WI-482: project a dispatched dot operand (`lt(?p.x, ?limit)`); WI-483:
        // fold a method-op operand (`lt(?b.peek(), ?limit)`).
        let a = self.reduce_operand(a, subst);
        let b = self.reduce_operand(b, subst);
        // WI-483: a residual complex op-call operand is un-ground → delay.
        if self.value_is_unbound_var(&a) || self.value_is_unbound_var(&b)
            || self.is_unreduced_op_call(&a) || self.is_unreduced_op_call(&b)
        {
            return BuiltinResult::delay();
        }
        // WI-685: `value_num` reads a numeric literal carrier-neutrally through
        // the view (Term or Node), so no collapse-to-Term step is needed.
        let ord = match (self.value_num(&a), self.value_num(&b)) {
            (Some(Num::Int(x)), Some(Num::Int(y))) => x.cmp(&y),
            (Some(Num::Big(x)), Some(Num::Big(y))) => x.cmp(&y),
            (Some(Num::Float(x)), Some(Num::Float(y))) => {
                // WI-644 / proposal 004: the resolver's `PartialOrd.gt`/`lt`/`gte`/`lte`
                // are IEEE — a NaN operand is UNORDERED, so the comparison is FALSE
                // (`partial_cmp` = `None`), NOT `OrderedFloat`'s total_cmp where NaN
                // ranks largest. This keeps rule-body comparisons agreeing with eval's
                // `ordered_*` (float_pair) and the C++ codegen (the WI-645 acceptance:
                // resolver == interpreter == codegen on Float).
                match x.into_inner().partial_cmp(&y.into_inner()) {
                    Some(o) => o,
                    None => return BuiltinResult::Failure,
                }
            }
            // unbound handled above; cross-type / non-numeric → fail
            _ => return BuiltinResult::Failure,
        };
        if pred(ord) { BuiltinResult::Success } else { BuiltinResult::Failure }
    }

    /// Extract a comparable number from a σ-walked `Value` — an unboxed
    /// scalar, or a numeric `Const` read through the view from EITHER carrier.
    /// `None` for non-numeric values (cmp then fails, matching the original).
    fn value_num(&self, v: &Value) -> Option<Num> {
        match v {
            Value::Int(n) => Some(Num::Int(*n)),
            Value::BigInt(n) => Some(Num::Big(n.clone())),
            Value::Float(f) => Some(Num::Float(ordered_float::OrderedFloat(*f))),
            // WI-685: read a numeric `Const` carrier-neutrally through the view —
            // a `Value::Term(Const)` OR a `Value::Node` literal occurrence (a
            // numeric literal written in a rule body reads as `Value::Node`), so
            // cmp/arith read it directly with no collapse-to-Term step first.
            _ => match v.head(self) {
                ViewHead::Const(Literal::Int(n)) => Some(Num::Int(n)),
                ViewHead::Const(Literal::BigInt(n)) => Some(Num::Big(n)),
                ViewHead::Const(Literal::Float(f)) => Some(Num::Float(f)),
                _ => None,
            },
        }
    }

    /// WI-644 / proposal 004: the RAW `f64` of a σ-walked Float `Value` (unboxed or a
    /// `Literal::Float` inside a `Value::Term`) — `None` for non-Float. Unlike
    /// `value_num`'s `OrderedFloat` (which equates NaNs, for hash-consing), this keeps
    /// IEEE semantics (`NaN != NaN`, `-0.0 == +0.0`) so the SEMANTIC `PartialEq.eq` on
    /// the partial Float carrier agrees with eval's `float_ieee_eq` and the C++ codegen.
    fn value_f64(&self, v: &Value) -> Option<f64> {
        match v {
            Value::Float(f) => Some(*f),
            // WI-685: a `Literal::Float` read carrier-neutrally through the view —
            // a `Value::Term(Const)` OR a `Value::Node` float literal occurrence.
            _ => match v.head(self) {
                ViewHead::Const(Literal::Float(f)) => Some(f.into_inner()),
                _ => None,
            },
        }
    }

    /// The `Var::Global` id of a σ-walked `Value`, if it is one — `Term::Var`
    /// or `Expr::Var` occurrence leaf. Used to decide whether a result arg is
    /// an unbound var to bind.
    fn value_global_var(&self, v: &Value) -> Option<VarId> {
        match v {
            Value::Term { id: t, .. } => match self.terms.get(*t) {
                Term::Var(Var::Global(vid)) => Some(*vid),
                _ => None,
            },
            Value::Node(occ) => match occ.as_expr() {
                Some(Expr::Var(Var::Global(vid))) => Some(*vid),
                _ => None,
            },
            _ => None,
        }
    }

    /// Resolve a builtin's *result* arg (read through `TermView`) under σ to a
    /// [`ResultTarget`] — the view-based front half of the old
    /// `try_bind_result`. Consumes the `ViewItem` so no borrow is held across
    /// the caller's subsequent `&mut self` value computation.
    fn resolve_result_target(&self, result: Option<ViewItem>, subst: &Substitution) -> ResultTarget {
        match self.walk_arg(result, subst) {
            None => ResultTarget::Compare(None),
            Some(v) => match self.value_global_var(&v) {
                Some(vid) => ResultTarget::Bind(vid),
                None => ResultTarget::Compare(Some(v)),
            },
        }
    }

    /// Back half of result binding: bind the computed `value` to the result
    /// var, or check equality against an already-bound result.
    fn finish_result(&mut self, target: ResultTarget, value: TermId) -> BuiltinResult {
        match target {
            ResultTarget::Bind(vid) => {
                let mut extra = Substitution::new();
                extra.bind(self, vid, value);
                BuiltinResult::SuccessWithBindings(extra)
            }
            ResultTarget::Compare(Some(v)) => {
                // WI-685: structural cross-carrier compare of the σ-walked result
                // arg (a `Value::Node` literal, a `Value::Term`, or an unboxed
                // scalar) against the computed term — no materialization of `v` to
                // a `TermId` first.
                if self.values_equal(&v, &Value::term(value)) {
                    BuiltinResult::Success
                } else {
                    BuiltinResult::Failure
                }
            }
            ResultTarget::Compare(None) => BuiltinResult::Failure,
        }
    }

    // ── Arithmetic builtins ──────────────────────────────────

    /// Generic arithmetic builtin for add/sub/mul.
    /// If 2 positional args: used as an equation builtin (reduces term to result).
    /// If 3 positional args: binds the 3rd arg to the computed result.
    /// Operates on Int, BigInt, or Float constants.
    fn builtin_arith<V: TermView>(
        &mut self,
        goal: &V,
        subst: &Substitution,
        int_op: impl Fn(i64, i64) -> i64,
        bigint_op: impl Fn(&num_bigint::BigInt, &num_bigint::BigInt) -> num_bigint::BigInt,
        float_op: impl Fn(f64, f64) -> f64,
    ) -> BuiltinResult {
        let pos_arity = match goal.head(self) {
            ViewHead::Functor { pos_arity, .. } if pos_arity >= 2 => pos_arity,
            _ => return BuiltinResult::Failure,
        };
        // Resolve operands (and, for the 3-arg form, the result target) to
        // owned values up front — `ViewItem` borrows the KB, so this must
        // finish before the `&mut self` alloc below.
        let a = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            Some(a) => a,
            None => return BuiltinResult::Failure,
        };
        let b = match self.walk_arg(goal.pos_arg(self, 1), subst) {
            Some(b) => b,
            None => return BuiltinResult::Failure,
        };
        // WI-482: project a dispatched dot operand (`mul(?p.x, ?dt)`); WI-483:
        // fold a method-op operand (`mul(?b.peek(), ?dt)`).
        let a = self.reduce_operand(a, subst);
        let b = self.reduce_operand(b, subst);
        // WI-483: a residual complex op-call operand is un-ground → delay.
        if self.value_is_unbound_var(&a) || self.value_is_unbound_var(&b)
            || self.is_unreduced_op_call(&a) || self.is_unreduced_op_call(&b)
        {
            return BuiltinResult::delay();
        }
        let target = (pos_arity >= 3).then(|| self.resolve_result_target(goal.pos_arg(self, 2), subst));

        // WI-685: `value_num` reads a numeric literal carrier-neutrally through
        // the view (Term or Node), so no collapse-to-Term step is needed.
        let result_term = match (self.value_num(&a), self.value_num(&b)) {
            (Some(Num::Int(x)), Some(Num::Int(y))) => {
                self.alloc(Term::Const(Literal::Int(int_op(x, y))))
            }
            (Some(Num::Big(x)), Some(Num::Big(y))) => {
                self.alloc(Term::Const(Literal::BigInt(bigint_op(&x, &y))))
            }
            (Some(Num::Float(x)), Some(Num::Float(y))) => {
                self.alloc(Term::Const(Literal::Float(ordered_float::OrderedFloat(float_op(x.0, y.0)))))
            }
            // unbound handled above; cross-type / non-numeric → fail
            _ => return BuiltinResult::Failure,
        };

        match target {
            Some(t) => self.finish_result(t, result_term),
            // 2-arg form: succeeds as a ground test (both args are concrete constants)
            None => BuiltinResult::Success,
        }
    }

    // ── Conversion builtins ────────────────────────────────────

    /// `to_bigint(?n, ?result)` — convert Int to BigInt.
    fn builtin_to_bigint<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let arg = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            Some(a) => a,
            None => return BuiltinResult::Failure,
        };
        if self.value_is_unbound_var(&arg) {
            return BuiltinResult::delay();
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        let value = match self.value_num(&arg) {
            Some(Num::Int(n)) => self.alloc(Term::Const(Literal::BigInt(num_bigint::BigInt::from(n)))),
            // Already a BigInt — pass the term through, or promote a scalar.
            Some(Num::Big(n)) => match &arg {
                Value::Term { id: t, .. } => *t,
                _ => self.alloc(Term::Const(Literal::BigInt(n))),
            },
            _ => return BuiltinResult::Failure,
        };
        self.finish_result(target, value)
    }

    /// `to_int(?n, ?result)` — convert BigInt to Int. Wraps in some/none.
    fn builtin_to_int<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let arg = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            Some(a) => a,
            None => return BuiltinResult::Failure,
        };
        if self.value_is_unbound_var(&arg) {
            return BuiltinResult::delay();
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        let result = match self.value_num(&arg) {
            Some(Num::Big(n)) => {
                use std::convert::TryFrom;
                if let Ok(small) = i64::try_from(&n) {
                    let int_term = self.alloc(Term::Const(Literal::Int(small)));
                    super::load::build_some(self, int_term)
                } else {
                    super::load::build_none(self)
                }
            }
            // Already an Int — wrap in some.
            Some(Num::Int(n)) => {
                let int_term = self.alloc(Term::Const(Literal::Int(n)));
                super::load::build_some(self, int_term)
            }
            _ => return BuiltinResult::Failure,
        };
        self.finish_result(target, result)
    }

    /// `scope(?sym, ?result)` — if `?sym` is bound to a Ref or Fn, bind `?result`
    /// to the enclosing scope term (Fn). Fails if scope is _global (top-level).
    fn builtin_scope<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let sym_val = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            Some(v) => v,
            None => return BuiltinResult::Failure,
        };
        if self.value_is_unbound_var(&sym_val) {
            return BuiltinResult::delay();
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        // WI-694: the symbol read off the arg's head, carrier-neutrally —
        // `functor_sym` yields it from a `Ref` or `Fn` of any carrier without
        // reifying; a non-symbol arg reads `None` → `Failure`.
        let Some(sym) = sym_val.head(self).functor_sym() else {
            return BuiltinResult::Failure;
        };

        let scope_raw = match self.symbols.get(sym) {
            crate::intern::SymbolDef::Resolved { scope_raw, .. } => *scope_raw,
            _ => return BuiltinResult::Failure,
        };

        let scope_tid = super::term::TermId::from_raw(scope_raw);
        // The scope term is a Fn term — return it directly
        match self.terms.get(scope_tid) {
            Term::Fn { functor, .. } => {
                let f = *functor;
                // Check if scope is _global (top-level, no meaningful parent)
                if self.symbols.name(f) == "_global" {
                    return BuiltinResult::Failure;
                }
                self.finish_result(target, scope_tid)
            }
            _ => BuiltinResult::Failure,
        }
    }

    /// `kind(?sym, ?result)` — if `?sym` is bound to a Ref, bind `?result`
    /// to a string describing the symbol's kind ("Sort", "Entity", etc.).
    fn builtin_kind<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let sym_val = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            Some(v) => v,
            None => return BuiltinResult::Failure,
        };
        if self.value_is_unbound_var(&sym_val) {
            return BuiltinResult::delay();
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        // WI-694: the symbol read off the arg's head, carrier-neutrally (no reify);
        // a non-symbol arg reads `None` → `Failure`.
        let Some(sym) = sym_val.head(self).functor_sym() else {
            return BuiltinResult::Failure;
        };

        let kind_str = match self.symbols.get(sym) {
            crate::intern::SymbolDef::Resolved { kind, .. } => {
                match kind {
                    crate::intern::SymbolKind::Sort => "Sort",
                    crate::intern::SymbolKind::Entity => "Entity",
                    crate::intern::SymbolKind::Operation => "Operation",
                    crate::intern::SymbolKind::Const => "Const",
                    crate::intern::SymbolKind::Namespace => "Namespace",
                    crate::intern::SymbolKind::Fact => "Fact",
                    crate::intern::SymbolKind::Rule => "Rule",
                    crate::intern::SymbolKind::Constraint => "Constraint",
                    crate::intern::SymbolKind::Param => "Param",
                    crate::intern::SymbolKind::Field => "Field",
                    crate::intern::SymbolKind::Goal => "Goal",
                    crate::intern::SymbolKind::OpResult => "OpResult",
                    crate::intern::SymbolKind::CallbackParam => "CallbackParam",
                    crate::intern::SymbolKind::CallbackResult => "CallbackResult",
                    crate::intern::SymbolKind::LocalLet => "LocalLet",
                }
            }
            _ => return BuiltinResult::Failure,
        };

        let kind_term = self.alloc(Term::Const(super::term::Literal::String(kind_str.to_owned())));
        self.finish_result(target, kind_term)
    }

    /// `field_access(?object, ?field, ?result)` — dot projection builtin
    /// (WI-279/WI-282), `TermView`-generic so a rule-body `Value::Node` goal
    /// (a dispatched `?p.x`) resolves without lowering (WI-482).
    ///
    /// Two dispatch modes (see [`Self::project_field`]):
    /// 1. Entity instance: `object` is `Fn { functor, named_args, .. }` with the
    ///    functor in `entity_fields` → return the named field's value.
    /// 2. Sort component: `object` is `Fn { functor, .. }` with `functor` a sort →
    ///    look up the field in the sort's scope via qualified name.
    ///
    /// The 3-arg form binds/compares a `?result`; the 2-arg form (a desugared
    /// bare `?x.y`) is a projection test — success iff the field exists.
    fn builtin_field_access<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        let pos_arity = match goal.head(self) {
            ViewHead::Functor { pos_arity, .. } if pos_arity >= 2 => pos_arity,
            _ => return BuiltinResult::Failure,
        };
        // Resolve operands (and the 3-arg result target) to owned values up
        // front — a `ViewItem` borrows the KB, so this must finish before the
        // `&mut self` reify/alloc below.
        let obj = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            Some(v) => v,
            None => return BuiltinResult::Failure,
        };
        let field = match self.walk_arg(goal.pos_arg(self, 1), subst) {
            Some(v) => v,
            None => return BuiltinResult::Failure,
        };
        if self.value_is_unbound_var(&obj) || self.value_is_unbound_var(&field) {
            return BuiltinResult::delay();
        }
        let target = (pos_arity >= 3).then(|| self.resolve_result_target(goal.pos_arg(self, 2), subst));

        // The receiver must be a structural carrier (entity/sort term, or a
        // denoted-occurrence twin); a scalar receiver has no fields.
        let Some(obj_term) = self.carrier_term(&obj) else {
            return BuiltinResult::Failure;
        };
        let Some(field_name) = self.field_name_from_value(&field) else {
            return BuiltinResult::Failure;
        };
        match self.project_field(obj_term, &field_name) {
            Some(val) => match target {
                Some(t) => self.finish_result(t, val),
                None => BuiltinResult::Success,
            },
            None => BuiltinResult::Failure,
        }
    }

    /// The field's short name from a `field_access` field operand `Value`: a
    /// `String` scalar / `Const`-string (the dispatched-dot form, whose eval
    /// twin also takes a string — `eval::builtins::reflect_field_access`), or a
    /// `Ref`/`Ident`/`Fn` symbol (the reflection-rule form). `None` otherwise.
    fn field_name_from_value(&mut self, v: &Value) -> Option<String> {
        if let Value::Str(s) = v {
            return Some(s.clone());
        }
        let t = self.carrier_term(v)?;
        self.field_operand_name(t)
    }

    /// The hash-consed term carrier of a structural value — a `Value::Term`
    /// unwrapped, a `Value::Node` occurrence reified via `occurrence_to_term`.
    /// `None` for a scalar / value-level var carrier, which has no fields (the
    /// caller fails or leaves the operand unreduced). Shared by the
    /// `field_access` builtin, `field_name_from_value`, and `reduce_dot_value`
    /// (WI-482).
    fn carrier_term(&mut self, v: &Value) -> Option<TermId> {
        match v {
            Value::Term { .. } | Value::Node(_) => Some(reify_goal_value(self, v)),
            _ => None,
        }
    }

    /// The field's short name from a reified field operand term — a `Ref`/`Ident`
    /// symbol or `Fn` functor → its short name, a `String` const → the string.
    fn field_operand_name(&self, field_term: TermId) -> Option<String> {
        match self.terms.get(field_term) {
            Term::Ref(s) | Term::Ident(s) => Some(self.symbols.name(*s).to_owned()),
            Term::Fn { functor, .. } => Some(self.symbols.name(*functor).to_owned()),
            Term::Const(Literal::String(s)) => Some(s.clone()),
            _ => None,
        }
    }

    /// WI-482: the field-projection core shared by the `field_access` builtin (a
    /// dot goal) and [`Self::reduce_dot_value`] (a dot in operand position).
    /// Returns the projected value term for an entity instance's named field or
    /// a sort-scope component, or `None` if the object carries no such field.
    /// Pure lookup — no result binding, no delay.
    fn project_field(&mut self, obj_term: TermId, field_name: &str) -> Option<TermId> {
        let (functor, named_args) = match self.terms.get(obj_term) {
            Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
            _ => return None,
        };
        // Dispatch 1: entity field access — match the named arg by short name.
        if self.entity_fields.contains_key(&functor) {
            return named_args
                .iter()
                .find(|(arg_sym, _)| self.symbols.name(*arg_sym) == field_name)
                .map(|(_, v)| *v);
        }
        // Dispatch 2: sort component access — resolve `functor_qname.field`.
        let functor_qname = match self.symbols.get(functor) {
            crate::intern::SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            _ => return None,
        };
        let target_qname = format!("{}.{}", functor_qname, field_name);
        let resolved_sym = *self.symbols.by_qualified_name.get(&target_qname)?;
        // A sort/entity component is a nullary name term; anything else a Ref.
        Some(match self.symbols.get(resolved_sym) {
            crate::intern::SymbolDef::Resolved { kind, .. }
                if matches!(kind, crate::intern::SymbolKind::Sort | crate::intern::SymbolKind::Entity) =>
            {
                self.make_name_term_from_sym(resolved_sym)
            }
            _ => self.alloc(Term::Ref(resolved_sym)),
        })
    }

    /// WI-482: reduce a σ-walked operand `Value` that is a dispatched dot
    /// (`field_access(receiver, "field")` — the form a rule-body `?p.x` rewrites
    /// to) to the projected field value, so a dot in OPERAND position
    /// (`eq(?v, ?p.x)`, `mul(?p.x, ?dt)`) computes — not only a top-level dot
    /// goal. The receiver is reduced first so a chain `?p.a.b` collapses
    /// inside-out. A non-dot value, or a dot whose receiver/field is unbound or
    /// names no such field, is returned UNCHANGED — the caller's comparison then
    /// sees the residual node and fails/delays (no silent success).
    fn reduce_dot_value(&mut self, v: Value, subst: &Substitution) -> Value {
        let occ = match &v {
            Value::Node(o) => Rc::clone(o),
            _ => return v,
        };
        let is_field_access = matches!(
            occ.as_expr(),
            Some(Expr::Apply { functor, .. })
                if self.builtins.get(functor).copied() == Some(BuiltinTag::FieldAccess)
        );
        if !is_field_access {
            return v;
        }
        // Receiver (arg 0) and field name (arg 1), σ-walked. The receiver may
        // itself be a dot — reduce it first.
        let recv = match self.walk_arg(occ.pos_arg(self, 0), subst) {
            Some(r) => r,
            None => return v,
        };
        let recv = self.reduce_dot_value(recv, subst);
        let field = match self.walk_arg(occ.pos_arg(self, 1), subst) {
            Some(f) => f,
            None => return v,
        };
        if self.value_is_unbound_var(&recv) || self.value_is_unbound_var(&field) {
            return v;
        }
        // Scalar receiver: no fields — leave the operand unreduced.
        let Some(obj_term) = self.carrier_term(&recv) else {
            return v;
        };
        let Some(field_name) = self.field_name_from_value(&field) else {
            return v;
        };
        match self.project_field(obj_term, &field_name) {
            Some(val) => Value::term(val),
            None => v,
        }
    }

    /// WI-483: reduce a dispatched rule-body method-op call operand
    /// (`Expr::Apply{op, args}` where `op` is a CONCRETE operation) by inlining
    /// the operation body with the call args substituted into its param vars BY
    /// SYMBOL — the param Symbol WI-487 stamps on op-body param vars — then
    /// reducing the folded body through the existing field-access reduction. The
    /// substitution-transparent peer of [`Self::reduce_dot_value`] for op-calls:
    /// `peek(?b)` ≡ its body `?b.value`, so inlining the definition is sound.
    ///
    /// FOLDABLE (the folded body collapses to a value — a `field_access` chain):
    /// returns that value. COMPLEX (arithmetic / `match` / `if` / `let` /
    /// recursion — the folded body does not collapse): returns the call
    /// UNCHANGED. The operand sites then treat a residual op-call as un-ground
    /// (delay) via [`Self::is_unreduced_op_call`], per the WI-483 decision —
    /// leave a complex callee uninterpreted, NEVER loud, so a rule's validity
    /// never depends on its callee's body complexity (substitution transparency).
    /// The interpreter bridge for complex bodies is a deferred follow-up.
    fn reduce_op_value(&mut self, v: Value, subst: &Substitution, depth: usize) -> Value {
        const FOLD_DEPTH_CAP: usize = 64;
        let occ = match &v {
            Value::Node(o) => Rc::clone(o),
            _ => return v,
        };
        let op = match occ.as_expr() {
            Some(Expr::Apply { functor, .. }) => *functor,
            _ => return v,
        };
        // A builtin (field_access, arith, eq, …) is reduced by its own path, not
        // folded. Only a CONCRETE operation (one with a stored body) folds; an
        // abstract / spec op has no body (its requires are abstract) — leave it.
        if self.builtins.get(&op).is_some() {
            return v;
        }
        let body = match self.op_body_node(op) {
            Some(b) => Rc::clone(b),
            None => return v, // abstract op (no concrete body) → leave un-ground
        };
        // Recursion guard: a self-recursive op never folds to a value — treat it
        // as complex and leave it un-ground rather than looping.
        if depth >= FOLD_DEPTH_CAP {
            return v;
        }
        // Param symbols in declaration order — the WI-352 arg-place list (the same
        // symbols WI-487 stamps on the body's param vars), read O(1) off the op
        // symbol rather than rescanning every `OperationInfo` fact per fold.
        let params: Vec<Symbol> = self.symbols.arg_places(op).to_vec();
        if params.is_empty() {
            return v; // nullary / unscanned op — nothing to fold
        }
        // σ-walk each call arg to a Value, keyed by param place. WI-279/WI-282
        // method dispatch puts the receiver + positional args positionally, but
        // the loader canonicalizes a plain op-call's args to NAMED form by field
        // name (`code(?c)` → `code(c: ?c)`) — so read positional `i` first, then
        // fall back to the named arg `p`. A param with neither leaves the call
        // un-ground (residualizes), safe per the WI-483 leave-uninterpreted rule.
        let mut param_args: HashMap<Symbol, Value> = HashMap::new();
        for (i, &p) in params.iter().enumerate() {
            let item = occ.pos_arg(self, i).or_else(|| occ.named_arg(self, p));
            match self.walk_arg(item, subst) {
                Some(a) => { param_args.insert(p, a); }
                None => return v,
            }
        }
        // Build the fold substitution: every op-body var named after a param maps
        // to its call arg. WI-487 mints a FRESH VarId per param occurrence (all
        // sharing the param Symbol), so bind every such VarId by Symbol — the
        // by-symbol fold (no string name-matching, no occurrence→term lowering).
        let mut fold = Substitution::new();
        collect_param_var_bindings(self, &body, &param_args, &mut fold);
        let folded = node_occurrence::substitute_occurrence(self, &body, &fold);
        // Reduce the folded body via field-access reduction; recurse for a nested
        // op-call. A value (Term/scalar) ⇒ FOLDABLE; a residual `Node` (arith /
        // match / unfoldable op-call) ⇒ COMPLEX → return the ORIGINAL call.
        let reduced = self.reduce_dot_value(Value::Node(folded), subst);
        let reduced = self.reduce_op_value(reduced, subst, depth + 1);
        match reduced {
            // A COMPLEX body (`match`/`if`/`let`/recursion) the structural fold
            // can't collapse. WI-625 gap 1 — the SLD→eval dual of the eval→SLD eq
            // bridge: run the op through a live, bounded interpreter instead of
            // residualizing. Ground-gated (`=`/`cmp` are tests — never bind); a
            // suspended or errored eval falls back to the ORIGINAL call `v`, so a
            // callee's body complexity never forces an unsound verdict — the
            // operand stays un-reduced and the `eq`/`cmp` goal delays.
            // Bridge only at the TOP operand reduction (`depth == 0`):
            // `call_op_bridged` evaluates the WHOLE body including nested op-calls,
            // so a depth-0 bridge already covers every nesting level. Attempting
            // it inside the fold-recursion would rebuild the interpreter at each
            // depth and, on a failing inner bridge, re-bridge the same operand
            // once per level. A complex body nested inside another op therefore
            // rides its enclosing op's single top-level bridge.
            Value::Node(_) if depth == 0 => self
                .bridge_op_to_eval(op, &params, &param_args, subst)
                .unwrap_or(v),
            other => other,
        }
    }

    /// WI-625 gap 1 (SLD→eval op-body dispatch bridge): run a CONCRETE op whose
    /// body the structural fold left un-reduced (`match`/`if`/`let`/recursion)
    /// through a live [`Interpreter`], returning its value so the resolver can
    /// continue as if the op-call were a scalar. The resolver→eval dual of the
    /// eval→SLD [`Self::prove_rule_predicate`] bridge (WI-625 gaps 4/5/6).
    ///
    /// Ownership: the interpreter OWNS a `KnowledgeBase`, so the resolver LENDS
    /// its own KB (`mem::take` — KB is `Default`), runs, and reclaims it via
    /// [`Interpreter::into_kb`]. `run()` is trampolined (heap stack), so eval
    /// depth costs no Rust stack. The eval↔SLD ping-pong (a bridged body whose
    /// `eq` dispatches back through [`Self::prove_rule_predicate`], which may
    /// re-enter this bridge) DOES nest ordinary Rust frames per crossing, so a
    /// thread-local `BRIDGE_REENTRY_DEPTH` caps it at [`BRIDGE_REENTRY_CAP`]
    /// crossings — a non-decreasing mutual recursion degrades to a residualize
    /// (delay) instead of a native stack overflow.
    ///
    /// Soundness gates:
    /// - **ground** — each arg is reified under σ (the interpreter has no σ) and
    ///   must be deeply ground; `=`/`cmp` are tests that must not bind, so a
    ///   non-ground operand returns `None` (the resolver delays), never runs.
    ///   (WI-685: `value_deep_ground` walks a `Value::Node` operand carrier-
    ///   neutrally — including nested Node children — so a genuinely ground
    ///   occurrence reads as ground and `materialize_value` lowers it, rather than
    ///   collapsing the occurrence to a `Term` before the check.)
    /// - **no requirement dicts** — invoked via [`Interpreter::call_op_bridged`],
    ///   NOT the placeholder-seeding entry: a body that dispatches through a
    ///   `requires` slot errors → residualize, so only requirement-FREE ops
    ///   decide and a placeholder can never misdispatch to a wrong value (gap 3).
    /// - **pure** — effects are contained by construction: the scratch
    ///   interpreter's effect registry is EMPTY (an effect → unhandled → error →
    ///   residualize) and its arenas (`Cell`/`Map`/…) are fresh and DROPPED with
    ///   it, so a bridged body cannot mutate resolver-visible state; the only
    ///   shared store is the KB's monotonic term interner. So re-running the
    ///   bridge on a resolver backtrack is idempotent.
    /// - **suspend** — the scratch interpreter runs in `bridge_mode`, so a
    ///   semantic comparison that reaches an undecided point (truncation, or a
    ///   buried override) raises [`EvalError::Suspended`] → residualize, so an
    ///   undecided body delays rather than injecting a wrong definite answer.
    ///
    /// Returns `Some(value)` only when the interpreter DECIDED a concrete value.
    /// Note the reflect builtins (`anthill.reflect.*`) live in the downstream
    /// `anthill-stl` crate and are NOT registered here, so a body dispatching to
    /// one hits `UnknownOperation` → residualize (a benign capability gap).
    fn bridge_op_to_eval(
        &mut self,
        op: Symbol,
        params: &[Symbol],
        param_args: &HashMap<Symbol, Value>,
        subst: &Substitution,
    ) -> Option<Value> {
        // Reify + ground-gate each arg under σ, in declaration order (before
        // taking the KB — this needs σ, which the interpreter has not). `reify_value`
        // applies σ; the arg then rides in its native carrier — a ground occurrence
        // (`Value::Node(Ref(green))`) reads as ground through the carrier-neutral
        // `value_deep_ground` (WI-685), so no collapse to a `Term` is needed and
        // `materialize_value` below lowers any Node to the interpreter's form.
        let mut args: Vec<Value> = Vec::with_capacity(params.len());
        for p in params {
            let a = self.reify_value(param_args.get(p)?, subst);
            if !self.value_deep_ground(&a, subst) {
                return None;
            }
            args.push(a);
        }
        // Run the op in a bridge-mode scratch interpreter, materializing each
        // term/occurrence operand into the interpreter's native form
        // (`Value::Term(box(…))` / `Value::Node` → `Value::Entity`), else a body
        // that reads a field errors with "receiver is not an entity".
        let outcome = self.run_in_bridge_interp(|interp| {
            let native: Vec<Value> =
                args.into_iter().map(|a| interp.materialize_value(a)).collect();
            interp.call_op_bridged(op, &native)
        })?;
        match outcome {
            Ok(value) => Some(value),
            // The bridge-mode suspend signal (an undecided semantic compare):
            // delay, exactly like the resolver's own SUSPEND. By design.
            Err(EvalError::Suspended { .. }) => None,
            // Any other eval error residualizes per WI-483 substitution-
            // transparency: a callee's runtime-domain error (`Overflow`,
            // `Raised`), an unhandled effect (resolution must not perform
            // effects), or a body needing a real requirement dict (gap 3) must
            // not break the enclosing rule. The one class worth surfacing is an
            // evaluator-INVARIANT `Internal` bug — assert it loudly in debug/test
            // builds (the loud-over-silent rule) while still residualizing in
            // release rather than aborting resolution.
            Err(e) => {
                debug_assert!(
                    !matches!(e, EvalError::Internal(_)),
                    "bridge_op_to_eval: internal evaluator error bridging `{}`: {e}",
                    self.qualified_name_of(op),
                );
                None
            }
        }
    }

    /// Shared core of the SLD→eval bridge (WI-625): lend the KB to a fresh
    /// bridge-mode [`Interpreter`], register the standard eval builtins, run `f`,
    /// and reclaim the KB. Caps eval↔SLD re-entry at [`BRIDGE_REENTRY_CAP`] —
    /// returns `None` (⇒ the caller residualizes/delays) when the cap is hit, so a
    /// non-terminating mutual recursion across the bridge degrades to a delay
    /// rather than a native stack overflow. The counter is a thread-local
    /// (resolution + its bridged evals run on one thread), so it survives the
    /// `mem::take` of `self`.
    ///
    /// The scratch interpreter's effect registry is EMPTY and its arenas
    /// (`Cell`/`Map`/…) are fresh and dropped with it, so a bridged run cannot
    /// mutate resolver-visible state — re-running on a resolver backtrack is
    /// idempotent; the only shared store is the KB's monotonic term interner.
    /// Re-registering the builtins per call is the simple-correct choice (the
    /// interpreter owns the lent KB, so they can't persist across calls); a
    /// registration failure surfaces as `Some(Err(_))`, which callers residualize.
    fn run_in_bridge_interp<F>(&mut self, f: F) -> Option<Result<Value, EvalError>>
    where
        F: FnOnce(&mut Interpreter) -> Result<Value, EvalError>,
    {
        if BRIDGE_REENTRY_DEPTH.with(|d| d.get()) >= BRIDGE_REENTRY_CAP {
            return None;
        }
        BRIDGE_REENTRY_DEPTH.with(|d| d.set(d.get() + 1));
        let kb = std::mem::take(self);
        let config = EvalConfig { bridge_mode: true, ..EvalConfig::default() };
        let mut interp = Interpreter::with_config(kb, config);
        let outcome = match crate::eval::builtins::register_standard_builtins(&mut interp) {
            Ok(()) => f(&mut interp),
            Err(e) => Err(e),
        };
        *self = interp.into_kb();
        BRIDGE_REENTRY_DEPTH.with(|d| d.set(d.get() - 1));
        Some(outcome)
    }

    /// WI-625 gap 2 — decide `eq`/`neq` for a RETROACTIVE instance-fact carrier
    /// whose bound op is a BODIED function (`fact PartialEq[T = X, eq = myEq]` with
    /// `myEq` a `match`/`if`/recursive operation, NOT a body-less rule-backed
    /// predicate like `Set.eq` — that is [`Self::prove_rule_predicate`]'s job).
    /// Runs `target(a, b) -> Bool` through the SLD→eval bridge and reads the
    /// verdict. Operands must already be reified + deeply ground (the caller
    /// [`Self::sem_eq_dispatch`] gates before dispatching). Three-way, so an
    /// APPLICABLE override that cannot be decided never masquerades as a structural
    /// answer (the Finding-1 soundness point). Returns [`BridgeEqOutcome`]:
    ///   * `Ok(Decided(v))`             — the op ran and returned `v`;
    ///   * `Ok(Undecided { truncated })` — UNDECIDED: the re-entry cap was hit
    ///                      (`truncated: true`, the eval analog of a depth-cut), or
    ///                      a bridge-mode suspend fired inside the op — itself either
    ///                      a clean nested-compare flounder (`false`) or a NESTED
    ///                      carrier-eq truncation surfaced through eval (`true`,
    ///                      WI-628). The resolver Delays, carrying the bit; eval
    ///                      suspends/errors — it must NOT read this as "unequal";
    ///   * `Err(e)`       — the bodied op itself FAILED (raise/overflow, a non-Bool
    ///                      return, a missing dict). The resolver residualizes
    ///                      (WI-483); eval propagates — never a silent `false`.
    ///
    /// Also the EVAL entry (`eval::builtins::semantic_equal`): it runs an ISOLATED
    /// scratch interpreter (via [`Self::run_in_bridge_interp`]'s `mem::take` of the
    /// KB), so it is safe to call from a builtin executing mid-trampoline — unlike
    /// [`Interpreter::call_op_bridged`], whose nested `run()` would corrupt the live
    /// activation stack. Eval and SLD thus decide instance-fact eq through one path.
    pub(crate) fn bridge_eq_op_to_eval(
        &mut self,
        target: Symbol,
        a: Value,
        b: Value,
    ) -> Result<BridgeEqOutcome, EvalError> {
        // `None` from the bridge core = the re-entry cap was hit ⇒ undecided. WI-628:
        // the cap is a RESOURCE CUT (the eval analog of a depth-truncated search),
        // so mark it `truncated` — an eager NAF/guard consumer must see it, unlike a
        // clean bridge-mode suspend below.
        let Some(outcome) = self.run_in_bridge_interp(|interp| {
            let na = interp.materialize_value(a);
            let nb = interp.materialize_value(b);
            interp.call_op_bridged(target, &[na, nb])
        }) else {
            return Ok(BridgeEqOutcome::Undecided { truncated: true });
        };
        match outcome {
            Ok(Value::Bool(v)) => Ok(BridgeEqOutcome::Decided(v)),
            // A bridge-mode suspend (an undecided nested compare) is "cannot decide
            // yet", NOT a failure — undecided. WI-628: it carries its OWN `truncated`
            // bit — a clean flounder is `false`, but a NESTED carrier-eq truncation
            // (surfaced as a Suspend by `eval::builtins::semantic_equal`) is `true`
            // and must propagate, so read it through rather than assuming complete.
            Err(EvalError::Suspended { truncated, .. }) => {
                Ok(BridgeEqOutcome::Undecided { truncated })
            }
            // A non-Bool return breaks the invariant that an eq op is declared
            // `-> Bool` (a load-time type error otherwise) — loud in debug, an
            // honest `Internal` in release (NOT a silent structural verdict).
            Ok(other) => {
                let detail = format!(
                    "instance-fact eq op `{}` returned a non-Bool `{other:?}`",
                    self.qualified_name_of(target),
                );
                debug_assert!(false, "{detail}");
                Err(EvalError::Internal(detail))
            }
            // The op's OWN failure (raise/overflow/missing dict). Surface it: the
            // resolver residualizes, eval propagates. An evaluator-INVARIANT
            // `Internal` bug is asserted loudly (loud-over-silent) but still
            // surfaced rather than swallowed.
            Err(e) => {
                debug_assert!(
                    !matches!(e, EvalError::Internal(_)),
                    "bridge_eq_op_to_eval: internal evaluator error bridging `{}`: {e}",
                    self.qualified_name_of(target),
                );
                Err(e)
            }
        }
    }

    /// WI-482 + WI-483: reduce a builtin operand to its value — project a
    /// dispatched `field_access` dot (`?p.x`), then fold a dispatched method-op
    /// call (`?b.peek()`). The single operand-reduction pipeline shared by
    /// `eq`/`cmp`/`arith`. A residual (complex) op-call is left as-is here; the
    /// caller delays on it via [`Self::is_unreduced_op_call`].
    fn reduce_operand(&mut self, v: Value, subst: &Substitution) -> Value {
        let v = self.reduce_dot_value(v, subst);
        self.reduce_op_value(v, subst, 0)
    }

    /// WI-483: is `v` a residual (unfolded) method-op call operand — a
    /// `Value::Node` applying a CONCRETE operation that [`Self::reduce_op_value`]
    /// left un-reduced (a complex body)? Such an operand is treated as un-ground
    /// (delay) by `eq`/`cmp`/`arith`, so a complex callee residualizes rather
    /// than failing — the substitution-transparency rule.
    fn is_unreduced_op_call(&self, v: &Value) -> bool {
        let Value::Node(occ) = v else { return false };
        match occ.as_expr() {
            Some(Expr::Apply { functor, .. }) => {
                self.builtins.get(functor).is_none() && self.op_body_node(*functor).is_some()
            }
            _ => false,
        }
    }

    /// The occurrence of a bodied (non-builtin) op-call operand, from EITHER
    /// carrier. A `Value::Node` occurrence — a rule-body atom (WI-246) or the
    /// WI-580 unfold's own hoisted goals (WI-668) — is returned directly. A
    /// `Value::Term(Fn{op,…})` is materialized to an occurrence: that is the
    /// carrier a *term-lowered* goal presents (a direct `resolve(&[term])`
    /// equation query, or an `or`/`push_choice` branch body), since `walk_view`
    /// yields a `Value::term` for any `Term::Fn`. The Term arm is load-bearing
    /// for carrier-neutrality — WI-668 routed the WI-580 *recursion* onto the
    /// Node arm, but a Term-carried op-call operand still reaches here and must
    /// case-split (regression guard: `wi668_term_carried_opcall_eq_case_splits`).
    /// `None` when `v` is not such an op-call.
    fn op_call_as_occ(&self, v: &Value) -> Option<Rc<NodeOccurrence>> {
        match v {
            Value::Node(o) if self.is_unreduced_op_call(v) => Some(Rc::clone(o)),
            Value::Node(_) => None,
            Value::Term { id, .. } => {
                let functor = match self.get_term(*id) {
                    Term::Fn { functor, .. } => *functor,
                    _ => return None,
                };
                if self.builtins.get(&functor).is_none() && self.op_body_node(functor).is_some() {
                    Some(super::node_occurrence::materialize_from_handle(self, *id))
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    /// WI-690 — carrier-neutral peer of the former `term_has_bodied_op_call`:
    /// does the value STRUCTURALLY CONTAIN (at any depth) a bodied (non-builtin)
    /// operation call — an unevaluated op-call that structural `unify` would
    /// compare wrongly? WI-580 declines to case-split against such an OTHER
    /// operand (leaving it to the builtin, which delays), preserving soundness
    /// for a query like `eq(append(?a, x), reverse(?b))`.
    ///
    /// A thin [`Self::fold_gate`] over [`HAS_BODIED_OP_CALL`]: structural (no σ
    /// chase — the empty σ is inert), reading the shallow-walked OTHER value
    /// directly through `TermView` so a Node/Entity operand is not lowered to a
    /// term. An [`ViewHead::Opaque`] carrier we cannot decompose conservatively
    /// declines (`opaque: true`) — the builtin still handles the eq; a "loud over
    /// silent" decline rather than a latent unsound miss.
    fn value_has_bodied_op_call(&self, v: &Value) -> bool {
        // Structural gate (no σ chase) — `None` is the inert empty σ.
        self.fold_gate(v, None, 0, HAS_BODIED_OP_CALL)
    }

    /// WI-580 (design §3.3/§5): is `f` a functor whose *bare* goal is the
    /// RELATIONAL VIEW of a bodied operation — a Bool-returning operation with a
    /// runnable body and NO hand-written rules? Such a goal (`member(?x, ?l)`) is
    /// the operation's relation, and WI-580 derives it from the body rather than
    /// from a hand-written `:-` twin whose UNIFICATION diverges from the body's
    /// declared `eq` (the member soundness gap). [`SearchStream::step_init`] routes
    /// a matching goal to `eq(f(args), true)`, so a ground call decides via the
    /// eval bridge ([`Self::reduce_op_value`]) using the declared `Eq`, and an
    /// unground one suspends to a WI-519 residual (the "sound checker, not
    /// generator" of §5).
    ///
    /// Rule-LESS is load-bearing: precedence (design §3.3) keeps hand-written
    /// rules winning while both a body and rules coexist, so a rule-backed
    /// relation (`Set.member`) is untouched and this fires ONLY once a functor's
    /// unification twins are retired. Cheap-gated for the per-goal hot path — a
    /// builtin or a body-less predicate (the common case) bails before the
    /// `rules_by_functor` allocation, which is reached only for a bodied Bool op.
    pub(crate) fn bare_bodied_bool_relation(&self, f: Symbol) -> bool {
        if self.builtins.get(&f).is_some() || self.op_body_node(f).is_none() {
            return false;
        }
        // Read the cached signature by ref (no record clone).
        let Some(sig) = self.op_record(f).and_then(|r| r.signature.as_ref()) else {
            return false;
        };
        // Effect-free: an effectful body is not a logical relation — effects don't
        // belong in a relation, and the eval bridge (empty effect registry) would
        // suspend on one anyway — so an effectful Bool op (`Stream.isEmpty`) is NOT
        // granted a relational view. `requires` is deliberately NOT excluded here
        // (unlike the unfold's `folded_call_match` gate): `member`'s `requires
        // Eq[T]` is discharged at the body's own `eq(head, x)` call by
        // value-directed dispatch, which the bridge honours (the unfold would drop
        // the dict; the bridge does not).
        if !sig.effects.is_empty() {
            return false;
        }
        // Bool-returning? `sort_sym_is_bool` compares by short name — robust to
        // how `Bool` is qualified; a hypothetical user `Bool` merely routes a
        // meaningless bare goal to `= true` (harmless), never a wrong answer.
        // Shared with the typer's `check_rule_body_goal_ops` so the goal-routing
        // gate and its static check cannot drift.
        let returns_bool = super::typing::sort_functor_of_view(self, &sig.return_type)
            .is_some_and(|s| self.sort_sym_is_bool(s));
        // Rule-less last: the borrowing `rules_by_functor_iter` short-circuits at
        // the first rule with no `Vec` alloc — this leg is reached only for a pure
        // bodied Bool op, which is rare.
        returns_bool && self.rules_by_functor_iter(f).next().is_none()
    }

    /// WI-580 (design §3.3): abstract-interpretation fallback for a suspended
    /// op-call operand in a `SemEq` goal. When `eq(A, B)` has an operand that is
    /// an unground, rule-less bodied op-call whose body case-splits on a flex
    /// scrutinee — exactly the shape [`Self::reduce_op_value`] / the eval bridge
    /// SUSPEND on (arguments too unground to decide) — expand the `eq` into one
    /// [`Candidate::Continuation`] per `match` arm instead of delaying. Each
    /// alternative
    ///   `[unify(scrutinee_arg, patternᵢ), eq(resultᵢ, OTHER), <hoisted op-calls>]`
    /// narrows the scrutinee argument to the arm's constructor (fresh vars) and
    /// asserts the arm's residual equals the other operand; a nested op-call in
    /// the residual is ANF-hoisted to a fresh var + its own `eq` goal so it
    /// re-becomes a top-level operand that re-triggers this fallback (the
    /// recursion terminates against the finite OTHER operand — e.g. relational
    /// `append(?a, [3]) = [1,3]` solves `?a = [1]`). Returns `None` when neither
    /// operand is a case-splittable unground op-call — the caller then runs the
    /// builtin, which delays (WI-519 residual) as before.
    ///
    /// Precedence (design §3.3): only a functor whose rules are ALL equations
    /// (or none) unfolds — a functor with genuine relational (`:-`) rules
    /// resolves via those ("rules win while both exist" during migration).
    fn unfold_eq_operand(&mut self, goal: &Value, subst: &Substitution) -> Option<Vec<Candidate>> {
        // Detect an op-call operand on the WALKED value directly — no
        // `reduce_operand` here (it would double the operand-reduction every
        // plain `SemEq` goal pays, and the builtin recomputes it on the decline
        // path anyway). A ground op-call is still recognized syntactically but
        // declines below at `folded_call_match`'s flex-scrutinee check, so only a
        // genuinely unground op-call case-splits.
        let a = self.walk_arg(goal.pos_arg(self, 0), subst)?;
        let b = self.walk_arg(goal.pos_arg(self, 1), subst)?;
        let (occ, other) = if let Some(o) = self.op_call_as_occ(&a) {
            (o, b)
        } else if let Some(o) = self.op_call_as_occ(&b) {
            (o, a)
        } else {
            return None;
        };
        let (op, pos_args, named_args) = match occ.as_expr() {
            Some(Expr::Apply { functor, pos_args, named_args, .. }) => {
                (*functor, pos_args.clone(), named_args.clone())
            }
            _ => return None,
        };
        if self.rules_by_functor_iter(op).any(|rid| !self.is_equation(rid)) {
            return None;
        }
        let (scrutinee_occ, arms) =
            super::body_specialize::folded_call_match(self, op, &pos_args, &named_args)?;
        // OTHER must be finite DATA: the per-arm `unify(result, OTHER)` compares
        // structurally, so an unevaluated bodied op-call inside OTHER would
        // wrongly FAIL (dropping real solutions — unsound under NAF). DECLINE if
        // OTHER carries a bodied op-call (read on the value carrier, WI-690).
        if self.value_has_bodied_op_call(&other) {
            return None;
        }
        // OTHER as a goal occurrence for the Node `unify(result, OTHER)` goal: a
        // `Node` rides directly (no `occurrence_to_term`); any other carrier is
        // the external finite-DATA operand we did not build, so materialize its
        // occurrence at this boundary (via its faithful term twin).
        let other_occ = match &other {
            Value::Node(occ) => Rc::clone(occ),
            _ => {
                let t = self.alloc_from_value(&other).ok()?;
                super::node_occurrence::materialize_from_handle(self, t)
            }
        };
        let unify_sym = self.unify_functor();
        // Build a `Value::Node` `unify(a, b)` goal — the shape shared by the
        // scrutinee-shape and result/OTHER decompositions in each arm.
        let mk_unify = |pos: Vec<Rc<NodeOccurrence>>, span| {
            Value::Node(NodeOccurrence::new_expr(
                Expr::Apply {
                    functor: unify_sym,
                    pos_args: pos,
                    named_args: Vec::new(),
                    type_args: Vec::new(),
                },
                span,
                None,
            ))
        };
        let mut cands = Vec::with_capacity(arms.len());
        for arm in arms {
            let mut rename: Vec<(Symbol, VarId)> = Vec::new();
            let pattern_occ = self.fresh_pattern_occ(&arm.pattern, &mut rename)?;
            let mut hoists: Vec<Value> = Vec::new();
            // WI-690: `anf_flatten` builds the arm body (and its hoisted op-call
            // `eq` goals) as `Value::Node` occurrences directly — no Term::Fn build
            // re-walked back to a Node (the retired `materialize_from_handle`
            // round-trip).
            let result_occ = self.anf_flatten(&arm.body, &rename, &mut hoists)?;
            // WI-690 inc2: both `unify` goals ride as `Value::Node` occurrences —
            // the scrutinee / result / OTHER operands are used directly, with no
            // `occurrence_to_term` lowering. The residual/OTHER decomposition is
            // UNIFY, not `SemEq`: needed narrowing must BIND the fresh spine vars
            // (`SemEq` only compares and would delay on a flex operand). This is
            // structural on the data spine (sound; for a custom-`Eq` ELEMENT type
            // it is sound but may be incomplete — eq-variant solutions need element
            // narrowing and stay WI-519 residual, per design §5). Element `eq`
            // semantics live in the body's own `eq` calls (hoisted below as `SemEq`).
            let unify_g = mk_unify(vec![Rc::clone(&scrutinee_occ), pattern_occ], scrutinee_occ.span);
            let result_g = mk_unify(vec![result_occ, Rc::clone(&other_occ)], arm.body.span);
            // Order: unify scrutinee shape → unify(result, OTHER) (binds the
            // hoist vars against the finite OTHER, bounding the recursion) → the
            // hoisted op-call `SemEq` goals (which re-trigger this fallback on
            // their now-smaller arguments).
            // WI-668/WI-690: each hoisted op-call goal is ALREADY a `Value::Node`
            // occurrence (built directly by `anf_flatten`), so its re-triggered
            // operand is recognized directly by `op_call_as_occ`'s Node arm — the
            // recursion stays on the Node carrier and never round-trips through the
            // Term arm at re-entry.
            let mut goals = vec![unify_g, result_g];
            goals.extend(hoists);
            cands.push(Candidate::Continuation(goals));
        }
        Some(cands)
    }

    /// Build a constructor pattern OCCURRENCE with FRESH resolver vars for each
    /// binder (rule-head-style opening), recording each binder `Symbol` → its
    /// fresh-var `Term` in `rename` so the arm body ([`Self::anf_flatten`]) can be
    /// renamed to match. `None` for a pattern shape this unfold doesn't handle (a
    /// tuple pattern).
    ///
    /// WI-690 inc2: occurrence-native, so the `unify(scrutinee, pattern)` goal
    /// rides as a `Value::Node` (the scrutinee is used directly, no
    /// `occurrence_to_term` lowering). `rename` records each binder's fresh
    /// `VarId`; the pattern occurrence and the arm body ([`Self::anf_flatten`])
    /// both emit `Expr::Var(Global(vid))` from it, so they share one binder
    /// identity.
    fn fresh_pattern_occ(
        &mut self,
        pattern: &Rc<NodeOccurrence>,
        rename: &mut Vec<(Symbol, VarId)>,
    ) -> Option<Rc<NodeOccurrence>> {
        use super::node_occurrence::Pattern;
        let span = pattern.span;
        match pattern.as_pattern()? {
            Pattern::Var { name, .. } => {
                let name = *name;
                let v = self.fresh_var(name);
                // Record the fresh `VarId` and emit the same `VarId` as the
                // pattern's occurrence leaf, so the pattern and the arm body share
                // one binder identity.
                rename.push((name, v));
                Some(NodeOccurrence::new_expr(Expr::Var(Var::Global(v)), span, None))
            }
            Pattern::Wildcard => {
                let anon = self.intern("_");
                let v = self.fresh_var(anon);
                Some(NodeOccurrence::new_expr(Expr::Var(Var::Global(v)), span, None))
            }
            Pattern::Literal { value } => {
                let lit = value.clone();
                Some(NodeOccurrence::new_expr(Expr::Const(lit), span, None))
            }
            Pattern::Constructor { name, pos_args, named_args } => {
                let name = *name;
                let pos_p = pos_args.clone();
                let named_p = named_args.clone();
                // Build a CANONICAL entity occurrence: positional sub-patterns map
                // to the constructor's declaration field names, all args carried
                // named + sorted (the system's canonical entity form), so the
                // bound value matches how entities are represented everywhere. A
                // NULLARY constructor is the canonical `Ref(name)` (WI-436/WI-511),
                // not an empty-args `Constructor`.
                let fields = self.entity_field_names(name).map(|f| f.to_vec());
                let mut named: Vec<(Symbol, Rc<NodeOccurrence>)> = Vec::new();
                for (i, p) in pos_p.iter().enumerate() {
                    let field = fields.as_ref().and_then(|f| f.get(i).copied())?;
                    let occ = self.fresh_pattern_occ(p, rename)?;
                    named.push((field, occ));
                }
                for (fs, p) in &named_p {
                    named.push((*fs, self.fresh_pattern_occ(p, rename)?));
                }
                if named.is_empty() {
                    Some(NodeOccurrence::new_expr(Expr::Ref(name), span, None))
                } else {
                    named.sort_by_key(|(s, _)| s.index());
                    Some(NodeOccurrence::new_expr(
                        Expr::Constructor { name, pos_args: Vec::new(), named_args: named },
                        span,
                        None,
                    ))
                }
            }
            Pattern::Tuple { .. } => None,
        }
    }

    /// Flatten an arm-body occurrence into a goal OCCURRENCE (ANF), renaming
    /// pattern binders per `rename` and HOISTING each nested op-call to a fresh
    /// var + a `Value::Node` `eq` goal appended to `hoists` (so it re-becomes a
    /// top-level operand that re-triggers [`Self::unfold_eq_operand`]). `None`
    /// for a body form this unfold does not handle yet (`if`/`let`/`lambda`/…) —
    /// the caller then declines the whole unfold, leaving the call to its normal
    /// delay.
    ///
    /// WI-690: occurrence-native. The former `Term`-building variant round-tripped
    /// every hoisted op-call goal back to a `Value::Node` through
    /// `materialize_from_handle` (WI-668) — a build-then-re-walk. Building the
    /// arm body (and its hoisted goals) as occurrences directly retires that
    /// round-trip; the op-call-free result spine is what the caller lowers for
    /// the `result_g` operand.
    fn anf_flatten(
        &mut self,
        occ: &Rc<NodeOccurrence>,
        rename: &[(Symbol, VarId)],
        hoists: &mut Vec<Value>,
    ) -> Option<Rc<NodeOccurrence>> {
        let span = occ.span;
        let Some(expr) = occ.as_expr() else {
            // A non-`Expr` occurrence (a ground arg substituted from the call) is
            // ALREADY an occurrence carrier — return it verbatim (no
            // `occurrence_to_term` reification; it carries no op-call to hoist).
            return Some(Rc::clone(occ));
        };
        match expr {
            Expr::Var(Var::Global(vid)) => {
                let name = vid.name();
                let vid = *vid;
                Some(match rename.iter().rev().find(|(s, _)| *s == name) {
                    // A pattern binder resolves to its fresh `VarId` (recorded by
                    // `fresh_pattern_occ`); emit its occurrence leaf so the same
                    // `VarId` is shared between the pattern occurrence and this
                    // body — the var identity the unfold relies on.
                    Some((_, vid)) => NodeOccurrence::new_expr(Expr::Var(Var::Global(*vid)), span, None),
                    None => NodeOccurrence::new_expr(Expr::Var(Var::Global(vid)), span, None),
                })
            }
            Expr::Ref(s) | Expr::Ident(s) => {
                let s = *s;
                Some(match rename.iter().rev().find(|(sy, _)| *sy == s) {
                    Some((_, vid)) => NodeOccurrence::new_expr(Expr::Var(Var::Global(*vid)), span, None),
                    None => NodeOccurrence::new_expr(Expr::Ref(s), span, None),
                })
            }
            Expr::Const(lit) => {
                let lit = lit.clone();
                Some(NodeOccurrence::new_expr(Expr::Const(lit), span, None))
            }
            Expr::Constructor { name, pos_args, named_args } => {
                let name = *name;
                let pos_c = pos_args.clone();
                let named_c = named_args.clone();
                let mut pos = Vec::with_capacity(pos_c.len());
                for a in &pos_c {
                    pos.push(self.anf_flatten(a, rename, hoists)?);
                }
                let mut named = Vec::with_capacity(named_c.len());
                for (fs, a) in &named_c {
                    named.push((*fs, self.anf_flatten(a, rename, hoists)?));
                }
                // Match the former Term build's canonicalization: an arg-LESS
                // constructor lowered to `Term::Ref(name)`, but `occ_build_fn`
                // (occurrence_to_term's Constructor path) emits `Term::Fn{name,[],[]}`
                // — a different term. Emit `Expr::Ref` for the nullary case so the
                // caller's `occurrence_to_term(result_occ)` stays byte-identical.
                if pos.is_empty() && named.is_empty() {
                    Some(NodeOccurrence::new_expr(Expr::Ref(name), span, None))
                } else {
                    Some(NodeOccurrence::new_expr(
                        Expr::Constructor { name, pos_args: pos, named_args: named },
                        span,
                        None,
                    ))
                }
            }
            Expr::Apply { functor, pos_args, named_args, .. } => {
                let functor = *functor;
                let pos_c = pos_args.clone();
                let named_c = named_args.clone();
                let mut pos = Vec::with_capacity(pos_c.len());
                for a in &pos_c {
                    pos.push(self.anf_flatten(a, rename, hoists)?);
                }
                let mut named = Vec::with_capacity(named_c.len());
                for (fs, a) in &named_c {
                    named.push((*fs, self.anf_flatten(a, rename, hoists)?));
                }
                // Build the op-call as a Node occurrence directly (the shape
                // `materialize_from_handle` produced for a `Term::Fn` op-call:
                // `Expr::Apply` with empty `type_args`), then ANF-hoist it as a
                // fresh var + a `Value::Node` `eq` goal that re-triggers the
                // unfold on its now-smaller arguments.
                let call = NodeOccurrence::new_expr(
                    Expr::Apply { functor, pos_args: pos, named_args: named, type_args: Vec::new() },
                    span,
                    None,
                );
                let anf = self.intern("_anf");
                let tvid = self.fresh_var(anf);
                let tvar = NodeOccurrence::new_expr(Expr::Var(Var::Global(tvid)), span, None);
                let eq_sym = self.eq_functor();
                let eq_goal = NodeOccurrence::new_expr(
                    Expr::Apply {
                        functor: eq_sym,
                        pos_args: vec![call, Rc::clone(&tvar)],
                        named_args: Vec::new(),
                        type_args: Vec::new(),
                    },
                    span,
                    None,
                );
                hoists.push(Value::Node(eq_goal));
                Some(tvar)
            }
            // `VarRef` is how an operation body spells a bare parameter / binder
            // reference (append's `nil -> ys`, the `cons(x, rest)` binders). Treat
            // it exactly like `Ref`/`Ident`: rename a pattern binder to its fresh
            // var, else keep the (already-substituted) reference.
            Expr::VarRef { name } => {
                let name = *name;
                Some(match rename.iter().rev().find(|(sy, _)| *sy == name) {
                    Some((_, vid)) => NodeOccurrence::new_expr(Expr::Var(Var::Global(*vid)), span, None),
                    None => NodeOccurrence::new_expr(Expr::Ref(name), span, None),
                })
            }
            _ => None,
        }
    }

    /// Collect all unbound VarIds in a term, walking through the substitution.
    fn collect_unbound_vars(&self, term: TermId, subst: &Substitution, out: &mut Vec<VarId>) {
        let walked = self.walk(term, subst);
        match self.terms.get(walked) {
            Term::Var(Var::Global(vid)) => {
                if !out.contains(vid) {
                    out.push(*vid);
                }
            }
            Term::Var(Var::DeBruijn(_)) => {}
            Term::Fn { pos_args, named_args, .. } => {
                let pos_args = pos_args.clone();
                let named_args = named_args.clone();
                for &arg in pos_args.iter() {
                    self.collect_unbound_vars(arg, subst, out);
                }
                for &(_, arg) in named_args.iter() {
                    self.collect_unbound_vars(arg, subst, out);
                }
            }
            _ => {}
        }
    }

    /// WI-246: the caller-var delay pre-check, run over a rule's opened
    /// occurrence body (`fresh_nodes`) rather than the term body — a step
    /// toward dropping `body: Vec<TermId>`.
    ///
    /// If a builtin delays on an internal variable (created fresh for this
    /// rule), other body goals may bind it — fine, no propagation needed. But
    /// if it delays on a caller variable (one that came from the query via
    /// `answer_links`), the whole rule should delay. `Not` is skipped (NAF
    /// delays via goal rotation at resolution time), `PushChoice` is skipped
    /// (a control primitive that fires immediately), and `Unify` is skipped
    /// (proposal 049: a bare-var first operand of `<=>` / `let ?v = e` is the
    /// variable the goal exists to BIND — pre-residualizing it would defeat the
    /// point), so the only delay condition checked is "the builtin's first arg
    /// resolves to a var". The
    /// chase goes through `resolve_as_value` (WI-348): a `Value::Term`-bound var
    /// follows the term chain as before, while a var bound to a concrete
    /// non-`Term` carrier (a `Value::Node`) resolves as *bound* — it is not a
    /// delaying variable.
    fn body_builtins_delay_on_caller_vars_nodes(
        &self,
        nodes: &[Rc<NodeOccurrence>],
        caller_fresh_vars: &[VarId],
        subst: &Substitution,
    ) -> bool {
        for node in nodes {
            let Some(tag) = self.get_builtin_view(node) else { continue };
            if tag == BuiltinTag::Not || tag == BuiltinTag::PushChoice || tag == BuiltinTag::Unify {
                continue;
            }
            let Some(arg) = node_first_pos_arg(node) else { continue };
            let mut unbound = Vec::new();
            // Value-arg delay: the builtin delays when its first arg resolves to
            // an unbound var (the occurrence twin of `builtin_would_delay`'s
            // non-`Not` arm). A compound first arg gives the builtin a concrete-
            // headed value structure, so it does NOT delay on value vars (the
            // builtin binds them via unification) — hence the bare-var gate.
            if self.occ_top_resolves_to_var(&arg, subst) {
                self.collect_unbound_vars_node(&arg, subst, &mut unbound);
            }
            // Type-position delay (WI-322): a caller var inside the first arg's
            // own `type_args` / `type_annotation` (`f[T = ?caller_var](…)`)
            // blocks a type-dispatching builtin even when its value structure is
            // ground — resolving the typed call needs `T` bound first. Unlike
            // value structure, a type-position var is NOT something the builtin
            // binds, so it must propagate delay. Latent until typer/simp
            // populates type_args at a builtin first-arg position.
            if let Some(expr) = arg.as_expr() {
                self.collect_expr_type_field_unbound_vars(expr, subst, &mut unbound);
            }
            if unbound.iter().any(|v| caller_fresh_vars.contains(v)) {
                return true;
            }
        }
        false
    }

    /// Mirror of `walk`'s var-detection without needing a `TermId`: chase a
    /// `Global` var through `Value::Term` bindings and report whether the chain
    /// ends at a variable (unbound, rigid, or DeBruijn) rather than a concrete
    /// term. Self-referential bindings terminate the chase.
    fn vid_resolves_to_var(&self, vid: VarId, subst: &Substitution) -> bool {
        let mut cur = vid;
        loop {
            match subst.resolve_as_value(cur) {
                None => return true,
                Some(Value::Term { id: t, .. }) => match self.terms.get(*t) {
                    Term::Var(Var::Global(w)) => {
                        if *w == cur {
                            return true; // self-referential var binding
                        }
                        cur = *w;
                    }
                    Term::Var(_) => return true,
                    _ => return false,
                },
                // Bound to a concrete non-`Term` carrier (a `Value::Node`
                // occurrence, a scalar) — the chain ends at something concrete,
                // NOT a variable.
                Some(_) => return false,
            }
        }
    }

    /// Occurrence twin of the non-`Not` `builtin_would_delay` arm: the first
    /// arg is a variable that stays a variable after substitution.
    fn occ_top_resolves_to_var(&self, arg: &Rc<NodeOccurrence>, subst: &Substitution) -> bool {
        match arg.as_expr() {
            Some(Expr::Var(Var::Global(vid))) => self.vid_resolves_to_var(*vid, subst),
            _ => false,
        }
    }

    /// Occurrence twin of [`Self::collect_unbound_vars`]: collect the `Global`
    /// vars in an occurrence arg that remain unbound under `subst`, chasing
    /// `Value::Term` bindings back into term-land (where the existing
    /// term-walker takes over).
    ///
    /// WI-298: descends into `NodeKind::Pattern` occurrences via
    /// `for_each_pattern_child` so a Global living in a pattern's nested
    /// type-annotation Expr leaf is counted; symmetric with
    /// `collect_occurrence_global_vars` / `occurrence_has_unbound_var`.
    fn collect_unbound_vars_node(
        &self,
        arg: &Rc<NodeOccurrence>,
        subst: &Substitution,
        out: &mut Vec<VarId>,
    ) {
        if let Some(pat) = arg.as_pattern() {
            node_occurrence::for_each_pattern_child(pat, |c| {
                self.collect_unbound_vars_node(c, subst, out)
            });
            return;
        }
        match arg.as_expr() {
            Some(Expr::Var(Var::Global(vid))) => match subst.resolve_as_value(*vid) {
                Some(Value::Term { id: t, .. }) => self.collect_unbound_vars(*t, subst, out),
                // Bound to a concrete non-`Term` carrier (a `Value::Node`) —
                // the var IS bound, so it is not collected as unbound.
                Some(_) => {}
                None => {
                    if !out.contains(vid) {
                        out.push(*vid);
                    }
                }
            },
            Some(expr) => {
                node_occurrence::for_each_child(expr, |c| {
                    self.collect_unbound_vars_node(c, subst, out)
                });
                // WI-322: `for_each_child` walks the value children but NOT the
                // TermId-typed type fields (`type_args` / `type_annotation`);
                // descend them too so a caller var living inside an op type-arg
                // (`f[T = ?caller_var](…)`) is counted. Symmetric with the
                // loader's `collect_occurrence_global_vars_ordered`, which pairs
                // `for_each_child` with `collect_expr_termid_field_vars`.
                self.collect_expr_type_field_unbound_vars(expr, subst, out);
            }
            None => {
                // Not an Expr or Pattern. A `Type`/`EffectExpr`-kind occurrence
                // reaching here (via the `Value::Node` type-arg arm of
                // `collect_type_value_unbound_vars`, or a `TypeChild::Node` of an
                // enclosing spine) descends subst-aware into the spine (WI-504) —
                // the resolve-time twin of the loader's
                // `collect_type_or_expr_node_vars` — so a caller var inside a
                // Type-kind Node type-arg is detected, not silently dropped (which
                // would under-delay the exact failure-class WI-322 closed). A
                // `RuleHead` (the only other non-Expr/non-Pattern kind) carries no
                // goal vars, so it is legitimately empty — matching the loader's
                // `RuleHead` arm.
                if let Some(tn) = arg.as_type() {
                    self.collect_type_node_unbound_vars(tn, subst, out);
                } else if let Some(en) = arg.as_effect_expr() {
                    self.collect_effect_node_unbound_vars(en, subst, out);
                }
            }
        }
    }

    /// WI-322: collect the unbound `Global` vars living in an `Expr`'s
    /// TermId-typed type fields — the `type_args` of an `Apply`/`ApplyWithin`
    /// and the `type_annotation` of a `Let`. The subst-aware twin of the
    /// loader's [`node_occurrence::collect_expr_termid_field_vars`]: it walks
    /// the SAME fields, but reads each type `Value` through the substitution so
    /// only vars still unbound here are reported. A `Value::Node` type spine /
    /// scalar carries no Global vars at resolution time (see the
    /// `Expr::Apply.type_args` doc), so it contributes nothing.
    fn collect_expr_type_field_unbound_vars(
        &self,
        expr: &Expr,
        subst: &Substitution,
        out: &mut Vec<VarId>,
    ) {
        match expr {
            Expr::Apply { type_args, .. } | Expr::ApplyWithin { type_args, .. } => {
                for (_, v) in type_args {
                    self.collect_type_value_unbound_vars(v, subst, out);
                }
            }
            Expr::Let { type_annotation: Some(v), .. } => {
                self.collect_type_value_unbound_vars(v, subst, out);
            }
            _ => {}
        }
    }

    /// Collect the unbound `Global` vars of a type `Value` (WI-322) — the
    /// subst-aware twin of the loader's `collect_value_type` (node_occurrence),
    /// walking the SAME carriers so collect / open / close / σ stay in lockstep
    /// over the type spine (the WI-378 invariant):
    /// - `Value::Term` is chased through the existing [`Self::collect_unbound_vars`]
    ///   term walker (the WI's stated mechanism), which follows var→var alias
    ///   chains so a type-arg aliased to a caller var is found. (A var bound to a
    ///   non-`Term` carrier is conservatively reported here — `walk` stops at it —
    ///   matching the term walker used by the value-arg path; at worst an
    ///   over-delay, never a missed one.)
    /// - `Value::Node` (a denoted / value-in-type spine) descends via the
    ///   occurrence walker [`Self::collect_unbound_vars_node`] — the loader twin
    ///   likewise descends `Value::Node` (via `collect_type_or_expr_node_vars`);
    ///   skipping it here would miss a caller var that `with_fresh_vars` opened
    ///   from a DeBruijn var inside the spine (under-delay). A `Type`/`EffectExpr`
    ///   -kind spine is walked subst-aware to its leaves (WI-504): the `None` arm
    ///   of `collect_unbound_vars_node` dispatches into
    ///   [`Self::collect_type_node_unbound_vars`] /
    ///   [`Self::collect_effect_node_unbound_vars`] — the resolve-time twins of
    ///   the loader's `collect_type_node_vars` / `collect_effect_node_vars` —
    ///   chasing a `TypeChild::Ground` term via [`Self::collect_unbound_vars`] and
    ///   recursing a `TypeChild::Node` back through the occurrence walker.
    /// - a tuple / named-tuple type value recurses into its element types.
    /// - scalars / runtime handles carry no type vars (the loader twin's tail
    ///   likewise skips them, and `Value::Var` — which never lands in a type
    ///   position, the opener leaves it inert — falls here too).
    fn collect_type_value_unbound_vars(
        &self,
        v: &Value,
        subst: &Substitution,
        out: &mut Vec<VarId>,
    ) {
        match v {
            Value::Term { id: t, .. } => self.collect_unbound_vars(*t, subst, out),
            Value::Node(occ) => self.collect_unbound_vars_node(occ, subst, out),
            Value::Entity { pos, named, .. } | Value::Tuple { pos, named, .. } => {
                for c in pos.iter() {
                    self.collect_type_value_unbound_vars(c, subst, out);
                }
                for (_, c) in named.iter() {
                    self.collect_type_value_unbound_vars(c, subst, out);
                }
            }
            _ => {}
        }
    }

    /// WI-504: collect the unbound `Global` vars of a `TypeNode` — the
    /// resolve-time, subst-aware twin of the loader's `collect_type_node_vars`
    /// (node_occurrence), walking the SAME children so collect / open / close / σ
    /// stay in lockstep over the type spine (the WI-378 invariant). Each child is
    /// routed through [`Self::collect_type_child_unbound_vars`], which reads
    /// ground terms / occurrence vars through the substitution so only vars still
    /// unbound here are reported. A `NamedTuple`'s `Value`-carried field list
    /// rides back through [`Self::collect_type_value_unbound_vars`].
    fn collect_type_node_unbound_vars(
        &self,
        tn: &TypeNode,
        subst: &Substitution,
        out: &mut Vec<VarId>,
    ) {
        match tn {
            TypeNode::Denoted { value } => self.collect_unbound_vars_node(value, subst, out),
            TypeNode::Parameterized { base, bindings } => {
                self.collect_type_child_unbound_vars(base, subst, out);
                for (_, c) in bindings {
                    self.collect_type_child_unbound_vars(c, subst, out);
                }
            }
            TypeNode::EffectsRows { effects_expr } => {
                self.collect_type_child_unbound_vars(effects_expr, subst, out)
            }
            TypeNode::Arrow { param, result, effects } => {
                self.collect_type_child_unbound_vars(param, subst, out);
                self.collect_type_child_unbound_vars(result, subst, out);
                self.collect_type_child_unbound_vars(effects, subst, out);
            }
            TypeNode::ExprCarried { value, member } => {
                self.collect_type_child_unbound_vars(value, subst, out);
                self.collect_type_child_unbound_vars(member, subst, out);
            }
            TypeNode::NamedTuple { fields } => {
                self.collect_type_value_unbound_vars(fields, subst, out)
            }
        }
    }

    /// WI-504: resolve-time, subst-aware twin of the loader's
    /// `collect_effect_node_vars` (node_occurrence) — walk an `EffectExprNode`'s
    /// children gathering the `Global` vars that remain unbound under `subst`.
    fn collect_effect_node_unbound_vars(
        &self,
        en: &EffectExprNode,
        subst: &Substitution,
        out: &mut Vec<VarId>,
    ) {
        match en {
            EffectExprNode::Merge { left, right } => {
                self.collect_type_child_unbound_vars(left, subst, out);
                self.collect_type_child_unbound_vars(right, subst, out);
            }
            EffectExprNode::Present { label } | EffectExprNode::Absent { label } => {
                self.collect_type_child_unbound_vars(label, subst, out)
            }
            EffectExprNode::Guarded { label, guard } => {
                self.collect_type_child_unbound_vars(label, subst, out);
                self.collect_type_value_unbound_vars(guard, subst, out);
            }
            EffectExprNode::Open { tail } => self.collect_type_child_unbound_vars(tail, subst, out),
            EffectExprNode::EmptyRow => {}
        }
    }

    /// WI-504: resolve-time, subst-aware twin of the loader's `collect_type_child`
    /// (node_occurrence). A `TypeChild::Ground` term is chased through the
    /// existing subst-aware term walker [`Self::collect_unbound_vars`] (so a
    /// ground `Term::Var(Global)` opened from a DeBruijn var — and any var→var
    /// alias chain it sits in — is resolved to its final var before the caller-var
    /// membership test). A `TypeChild::Node` recurses through the occurrence
    /// walker [`Self::collect_unbound_vars_node`], whose `None` arm re-dispatches
    /// a nested Type/EffectExpr spine.
    fn collect_type_child_unbound_vars(
        &self,
        child: &TypeChild,
        subst: &Substitution,
        out: &mut Vec<VarId>,
    ) {
        match child {
            TypeChild::Ground(t) => self.collect_unbound_vars(*t, subst, out),
            TypeChild::Node(n) => self.collect_unbound_vars_node(n, subst, out),
        }
    }

}

/// First positional child of a builtin occurrence goal (`eq(a, b)` → `a`).
fn node_first_pos_arg(node: &Rc<NodeOccurrence>) -> Option<Rc<NodeOccurrence>> {
    match node.as_expr()? {
        Expr::Apply { pos_args, .. } | Expr::Constructor { pos_args, .. } => {
            pos_args.first().map(Rc::clone)
        }
        _ => None,
    }
}

// ── Tests ───────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::intern::Symbol;
    use crate::kb::term::{Literal, Term};
    use smallvec::SmallVec;

    /// Build a `meta(simp: true)` term — the `[simp]` tag a loaded directional
    /// rewrite carries. `apply_eq_rules` fires only `[simp]`/`[unfold]`-tagged
    /// equations (WI-292, mirroring the typer's `simp_rewrite`), so a test that
    /// asserts an equation directly (bypassing the loader) must tag it to have it
    /// fire — exactly as `simp_rewrite.rs`'s `build_add_zero` does.
    fn simp_meta(kb: &mut KnowledgeBase) -> TermId {
        let simp_sym = kb.intern("simp");
        let meta_sym = kb.intern("meta");
        let tru = kb.alloc(Term::Const(Literal::Bool(true)));
        kb.alloc(Term::Fn {
            functor: meta_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(simp_sym, tru)]),
        })
    }

    // ── match_term tests (via discrim tree) ─────────────────────

    #[test]
    fn match_term_var_const() {
        let mut kb = KnowledgeBase::new();
        let x_sym = kb.intern("x");
        let vid = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vid)));
        let val = kb.alloc(Term::Const(Literal::Int(42)));

        let s = kb.match_term(var_x, val).expect("should match");
        assert_eq!(s.resolve_as_value(vid).map(|v| v.expect_term()), Some(val));
    }

    #[test]
    fn match_term_fn_structure() {
        let mut kb = KnowledgeBase::new();
        let f_sym = kb.intern("f");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let val = kb.alloc(Term::Const(Literal::Int(1)));

        let t1 = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let t2 = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        let s = kb.match_term(t1, t2).expect("should match");
        assert_eq!(s.resolve_as_value(vx).map(|v| v.expect_term()), Some(val));
    }

    #[test]
    fn match_term_mismatch() {
        let mut kb = KnowledgeBase::new();
        let v1 = kb.alloc(Term::Const(Literal::Int(1)));
        let v2 = kb.alloc(Term::Const(Literal::Int(2)));

        assert!(kb.match_term(v1, v2).is_none());
    }

    // ── bind_compressed chain tests ────────────────────────────

    #[test]
    fn bind_compressed_transitive_chain() {
        // x → y → z → 99: sequential bind_compressed calls should
        // compress all vars to point directly to 99.
        let mut kb = KnowledgeBase::new();
        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let z_sym = kb.intern("z");
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let vz = kb.fresh_var(z_sym);
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));
        let var_z = kb.alloc(Term::Var(Var::Global(vz)));
        let val = kb.alloc(Term::Const(Literal::Int(99)));

        let mut s = Substitution::new();

        // x → y
        s.bind_compressed([(vx, var_y)], &kb.terms);
        assert_eq!(s.resolve_as_value(vx).map(|v| v.expect_term()), Some(var_y));

        // y → z: should also compress x → z
        s.bind_compressed([(vy, var_z)], &kb.terms);
        assert_eq!(s.resolve_as_value(vy).map(|v| v.expect_term()), Some(var_z));
        assert_eq!(s.resolve_as_value(vx).map(|v| v.expect_term()), Some(var_z));

        // z → 99: should compress x → 99 and y → 99
        s.bind_compressed([(vz, val)], &kb.terms);
        assert_eq!(s.resolve_as_value(vz).map(|v| v.expect_term()), Some(val));
        assert_eq!(s.resolve_as_value(vy).map(|v| v.expect_term()), Some(val));
        assert_eq!(s.resolve_as_value(vx).map(|v| v.expect_term()), Some(val));
    }

    // ── Reify tests ─────────────────────────────────────────────

    #[test]
    fn reify_deep_chase() {
        let mut kb = KnowledgeBase::new();
        let f_sym = kb.intern("f");
        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));
        let val = kb.alloc(Term::Const(Literal::Int(42)));

        // f(?x) where x -> y -> 42
        let term = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let mut s = Substitution::new();
        s.bind(&kb, vx, var_y);
        s.bind(&kb, vy, val);

        let result = kb.reify(term, &s).expect_term();
        match kb.get_term(result) {
            Term::Fn { pos_args, .. } => {
                assert_eq!(pos_args[0], val);
            }
            other => panic!("expected Fn, got {:?}", other),
        }
    }

    // ── is_equation tests ───────────────────────────────────────

    #[test]
    fn is_equation_true() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");

        let lhs = kb.alloc(Term::Const(Literal::Int(1)));
        let rhs = kb.alloc(Term::Const(Literal::Int(1)));
        let head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, rhs]),
            named_args: SmallVec::new(),
        });

        let rid = kb.assert_fact(head, sort, domain, None);
        assert!(kb.is_equation(rid));
    }

    #[test]
    fn is_equation_false_for_rule() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let g_sym = kb.intern("g");

        let lhs = kb.alloc(Term::Const(Literal::Int(1)));
        let rhs = kb.alloc(Term::Const(Literal::Int(1)));
        let head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, rhs]),
            named_args: SmallVec::new(),
        });
        let body = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });

        let rid = kb.assert_rule(head, vec![body], sort, domain, None);
        assert!(!kb.is_equation(rid));
    }

    // ── SLD Resolution tests ────────────────────────────────────

    #[test]
    fn resolve_ground_fact() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let parent_sym = kb.intern("parent");

        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let bob = kb.alloc(Term::Const(Literal::String("bob".into())));

        let fact = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[alice, bob]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(fact, sort, domain, None);

        // Query: parent(?x, "bob")
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let goal = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_x, bob]),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal], &config);
        assert_eq!(results.len(), 1);
        // answer_subst is flat — resolve directly, no walk needed
        assert_eq!(results[0].subst.resolve_as_value(vx).map(|v| v.expect_term()), Some(alice));
    }

    /// WI-512: a non-linear goal (a query var repeated within one atom) must
    /// match only when the repeated positions are equal. `rel(?x, ?x)` matches
    /// the self-loop `rel("a","a")` but NOT `rel("a","b")` — the discrim walk
    /// binds `?x` to both positions (same global var), `resolve_leaf` flags the
    /// `a`≠`b` candidate as `is_contradiction`, and `step_choice` drops it.
    #[test]
    fn resolve_nonlinear_goal_drops_conflicting_match() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let rel = kb.intern("rel");

        let a = kb.alloc(Term::Const(Literal::String("a".into())));
        let b = kb.alloc(Term::Const(Literal::String("b".into())));

        let f_ab = kb.alloc(Term::Fn {
            functor: rel,
            pos_args: SmallVec::from_slice(&[a, b]),
            named_args: SmallVec::new(),
        });
        let f_aa = kb.alloc(Term::Fn {
            functor: rel,
            pos_args: SmallVec::from_slice(&[a, a]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f_ab, sort, domain, None);
        kb.assert_fact(f_aa, sort, domain, None);

        // Query: rel(?x, ?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let goal = kb.alloc(Term::Fn {
            functor: rel,
            pos_args: SmallVec::from_slice(&[var_x, var_x]),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal], &config);
        assert_eq!(results.len(), 1, "rel(?x,?x) must match only the self-loop rel(a,a)");
        assert_eq!(
            results[0].subst.resolve_as_value(vx).map(|v| v.expect_term()),
            Some(a),
        );
    }

    #[test]
    fn resolve_simple_rule() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let parent_sym = kb.intern("parent");
        let grandparent_sym = kb.intern("grandparent");

        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let bob = kb.alloc(Term::Const(Literal::String("bob".into())));
        let charlie = kb.alloc(Term::Const(Literal::String("charlie".into())));

        // Facts: parent("alice", "bob"), parent("bob", "charlie")
        let f1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[alice, bob]),
            named_args: SmallVec::new(),
        });
        let f2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[bob, charlie]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f1, sort, domain, None);
        kb.assert_fact(f2, sort, domain, None);

        // Rule: grandparent(?x, ?z) :- parent(?x, ?y), parent(?y, ?z)
        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let z_sym = kb.intern("z");
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let vz = kb.fresh_var(z_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));
        let var_z = kb.alloc(Term::Var(Var::Global(vz)));

        let head = kb.alloc(Term::Fn {
            functor: grandparent_sym,
            pos_args: SmallVec::from_slice(&[var_x, var_z]),
            named_args: SmallVec::new(),
        });
        let b1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_x, var_y]),
            named_args: SmallVec::new(),
        });
        let b2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[var_y, var_z]),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(head, vec![b1, b2], sort, domain, None);

        // Query: grandparent(?a, ?b)
        let a_sym = kb.intern("a");
        let b_sym = kb.intern("b");
        let va = kb.fresh_var(a_sym);
        let vb = kb.fresh_var(b_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(va)));
        let var_b = kb.alloc(Term::Var(Var::Global(vb)));
        let goal = kb.alloc(Term::Fn {
            functor: grandparent_sym,
            pos_args: SmallVec::from_slice(&[var_a, var_b]),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal], &config);
        assert_eq!(results.len(), 1);
        // Use reify to resolve through fresh var chains
        assert_eq!(kb.reify(var_a, &results[0].subst).expect_term(), alice);
        assert_eq!(kb.reify(var_b, &results[0].subst).expect_term(), charlie);
    }

    #[test]
    fn resolve_recursive_rule() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let parent_sym = kb.intern("parent");
        let ancestor_sym = kb.intern("ancestor");

        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let bob = kb.alloc(Term::Const(Literal::String("bob".into())));
        let charlie = kb.alloc(Term::Const(Literal::String("charlie".into())));

        // Facts
        let f1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[alice, bob]),
            named_args: SmallVec::new(),
        });
        let f2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[bob, charlie]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f1, sort, domain, None);
        kb.assert_fact(f2, sort, domain, None);

        // Rule 1: ancestor(?x, ?y) :- parent(?x, ?y)
        {
            let x_sym = kb.intern("x");
            let y_sym = kb.intern("y");
            let vx = kb.fresh_var(x_sym);
            let vy = kb.fresh_var(y_sym);
            let var_x = kb.alloc(Term::Var(Var::Global(vx)));
            let var_y = kb.alloc(Term::Var(Var::Global(vy)));

            let head = kb.alloc(Term::Fn {
                functor: ancestor_sym,
                pos_args: SmallVec::from_slice(&[var_x, var_y]),
                named_args: SmallVec::new(),
            });
            let body = kb.alloc(Term::Fn {
                functor: parent_sym,
                pos_args: SmallVec::from_slice(&[var_x, var_y]),
                named_args: SmallVec::new(),
            });
            kb.assert_rule(head, vec![body], sort, domain, None);
        }

        // Rule 2: ancestor(?x, ?z) :- parent(?x, ?y), ancestor(?y, ?z)
        {
            let x_sym = kb.intern("x");
            let y_sym = kb.intern("y");
            let z_sym = kb.intern("z");
            let vx = kb.fresh_var(x_sym);
            let vy = kb.fresh_var(y_sym);
            let vz = kb.fresh_var(z_sym);
            let var_x = kb.alloc(Term::Var(Var::Global(vx)));
            let var_y = kb.alloc(Term::Var(Var::Global(vy)));
            let var_z = kb.alloc(Term::Var(Var::Global(vz)));

            let head = kb.alloc(Term::Fn {
                functor: ancestor_sym,
                pos_args: SmallVec::from_slice(&[var_x, var_z]),
                named_args: SmallVec::new(),
            });
            let b1 = kb.alloc(Term::Fn {
                functor: parent_sym,
                pos_args: SmallVec::from_slice(&[var_x, var_y]),
                named_args: SmallVec::new(),
            });
            let b2 = kb.alloc(Term::Fn {
                functor: ancestor_sym,
                pos_args: SmallVec::from_slice(&[var_y, var_z]),
                named_args: SmallVec::new(),
            });
            kb.assert_rule(head, vec![b1, b2], sort, domain, None);
        }

        // Query: ancestor("alice", ?w)
        let w_sym = kb.intern("w");
        let vw = kb.fresh_var(w_sym);
        let var_w = kb.alloc(Term::Var(Var::Global(vw)));
        let goal = kb.alloc(Term::Fn {
            functor: ancestor_sym,
            pos_args: SmallVec::from_slice(&[alice, var_w]),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { max_depth: 20, ..Default::default() };
        let results = kb.resolve(&[goal], &config);

        // Should find: ancestor(alice, bob) and ancestor(alice, charlie)
        let bound: Vec<TermId> = results.iter()
            .map(|sol| kb.reify(var_w, &sol.subst).expect_term())
            .collect();
        assert_eq!(bound.len(), 2);
        assert!(bound.contains(&bob));
        assert!(bound.contains(&charlie));
    }

    #[test]
    fn resolve_multiple_solutions() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let likes_sym = kb.intern("likes");

        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let cats = kb.alloc(Term::Const(Literal::String("cats".into())));
        let dogs = kb.alloc(Term::Const(Literal::String("dogs".into())));

        let f1 = kb.alloc(Term::Fn {
            functor: likes_sym,
            pos_args: SmallVec::from_slice(&[alice, cats]),
            named_args: SmallVec::new(),
        });
        let f2 = kb.alloc(Term::Fn {
            functor: likes_sym,
            pos_args: SmallVec::from_slice(&[alice, dogs]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f1, sort, domain, None);
        kb.assert_fact(f2, sort, domain, None);

        // Query: likes("alice", ?what)
        let w_sym = kb.intern("what");
        let vw = kb.fresh_var(w_sym);
        let var_w = kb.alloc(Term::Var(Var::Global(vw)));
        let goal = kb.alloc(Term::Fn {
            functor: likes_sym,
            pos_args: SmallVec::from_slice(&[alice, var_w]),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal], &config);
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn resolve_max_solutions() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");

        for i in 0..5 {
            let val = kb.alloc(Term::Const(Literal::Int(i)));
            let fact = kb.alloc(Term::Fn {
                functor: f_sym,
                pos_args: SmallVec::from_elem(val, 1),
                named_args: SmallVec::new(),
            });
            kb.assert_fact(fact, sort, domain, None);
        }

        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let goal = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { max_solutions: 2, ..Default::default() };
        let results = kb.resolve(&[goal], &config);
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn resolve_depth_limit() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let loop_sym = kb.intern("loop");

        // Infinite loop: loop(?x) :- loop(?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let head = kb.alloc(Term::Fn {
            functor: loop_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let body = kb.alloc(Term::Fn {
            functor: loop_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(head, vec![body], sort, domain, None);

        let val = kb.alloc(Term::Const(Literal::Int(1)));
        let goal = kb.alloc(Term::Fn {
            functor: loop_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { max_depth: 5, ..Default::default() };
        let results = kb.resolve(&[goal], &config);
        assert!(results.is_empty());
    }

    #[test]
    fn wi628_naf_over_truncated_search_is_undecided_not_success() {
        // WI-628: `not(P)` must NOT read a DEPTH-TRUNCATED inner search as a
        // refutation of `P`. `loop(x) :- loop(x)` has no finite derivation, so a
        // bounded search for `loop(1)` TRUNCATES (it never refutes). The old
        // ground NAF branch treated the empty-but-truncated inner stream as "P has
        // no solution → P is false", so `not(loop(1))` wrongly SUCCEEDED with an
        // empty residual — a definite verdict from an incomplete search. The fix
        // consults the sub-stream's `truncated` flag (WI-616 substrate) and folds
        // truncation into the floundered/undecided branch.
        let mut kb = kb_with_builtins();
        let not_sym = kb.resolve_symbol("anthill.reflect.not");
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let loop_sym = kb.intern("loop");

        // loop(?x) :- loop(?x)  — non-terminating recursion (truncates, never
        // refutes).
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let head = kb.alloc(Term::Fn {
            functor: loop_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let body = kb.alloc(Term::Fn {
            functor: loop_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(head, vec![body], sort, domain, None);

        // not(loop(1)) under a small depth budget so loop(1) TRUNCATES.
        let one = kb.alloc(Term::Const(Literal::Int(1)));
        let loop_1 = kb.alloc(Term::Fn {
            functor: loop_sym,
            pos_args: SmallVec::from_elem(one, 1),
            named_args: SmallVec::new(),
        });
        let not_loop_1 = kb.alloc(Term::Fn {
            functor: not_sym,
            pos_args: SmallVec::from_elem(loop_1, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { max_depth: 8, ..Default::default() };
        let results = kb.resolve(&[not_loop_1], &config);
        // A truncated inner search is UNDECIDED: `not(loop(1))` must NOT yield a
        // DEFINITE (empty-residual) solution. Pre-fix it did (the bug); post-fix
        // any solution is a residual `[not(loop(1))]` carrying the undecidedness.
        assert!(
            !results.iter().any(|s| s.residual.is_empty()),
            "not(loop(1)) must not DECIDE from a truncated search — no \
             empty-residual (definite) solution allowed; got {} solution(s), {} definite",
            results.len(),
            results.iter().filter(|s| s.residual.is_empty()).count()
        );
        // Positive side: the honest undecided answer IS emitted — exactly one
        // solution carrying the single undischarged `not(loop(1))` as residual —
        // not the verdict dropped entirely (0 solutions), which the negative
        // assertion above would pass vacuously.
        assert_eq!(results.len(), 1, "expected exactly one (residual) solution for not(loop(1))");
        assert_eq!(
            results[0].residual.len(),
            1,
            "the undecided answer must carry the single undischarged not(loop(1)) as residual"
        );

        // Contrast (no over-flouncing): `not(g(1))` where `g` has NO rules/facts —
        // the inner search for g(1) COMPLETES empty (not truncated), so `not(g(1))`
        // must STILL succeed DEFINITELY. Guards the fix against breaking honest NAF.
        let g_sym = kb.intern("g");
        let g_1 = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(one, 1),
            named_args: SmallVec::new(),
        });
        let not_g_1 = kb.alloc(Term::Fn {
            functor: not_sym,
            pos_args: SmallVec::from_elem(g_1, 1),
            named_args: SmallVec::new(),
        });
        let results2 = kb.resolve(&[not_g_1], &config);
        assert_eq!(
            results2.len(),
            1,
            "not(g(1)) should succeed — g(1) is genuinely unprovable in a COMPLETE search"
        );
        assert!(
            results2[0].residual.is_empty(),
            "not(g(1)) must be DEFINITE (complete empty search), not floundered; got {:?}",
            results2[0].residual
        );
    }

    #[test]
    fn wi628_naf_truncation_propagates_to_outer_stream_under_definite_only() {
        // WI-628(b) piece (a): a nested `not(P)` whose inner search TRUNCATES must
        // taint the OUTER stream's `truncated` flag, so an eager consumer sees it.
        // This is the exact mechanism the `forall` guard relies on — it synthesizes
        // `not(body)` goals and resolves them under `definite_only: true`, where the
        // truncated `not(P)` frame is SKIPPED WITHOUT yielding a residual. Before
        // piece (a), the sub-stream's local `truncated` was dropped with the drained
        // verdict and the outer `resolve_goals_with_truncation` reported
        // `truncated == false` — so the guard read the empty result as a definite
        // refutation. Now `self.truncated |= v.truncated` folds it up and
        // `drain_all` surfaces it.
        let mut kb = kb_with_builtins();
        let not_sym = kb.resolve_symbol("anthill.reflect.not");
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let loop_sym = kb.intern("loop");

        // loop(?x) :- loop(?x) — non-terminating (truncates, never refutes).
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let head = kb.alloc(Term::Fn {
            functor: loop_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let body = kb.alloc(Term::Fn {
            functor: loop_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(head, vec![body], sort, domain, None);

        let one = kb.alloc(Term::Const(Literal::Int(1)));
        let mk_not = |kb: &mut KnowledgeBase, inner_functor: Symbol| {
            let inner = kb.alloc(Term::Fn {
                functor: inner_functor,
                pos_args: SmallVec::from_elem(one, 1),
                named_args: SmallVec::new(),
            });
            kb.alloc(Term::Fn {
                functor: not_sym,
                pos_args: SmallVec::from_elem(inner, 1),
                named_args: SmallVec::new(),
            })
        };
        let not_loop_1 = mk_not(&mut kb, loop_sym);

        // definite_only: true is the guard/quantifier discharge mode — the frame is
        // skipped WITHOUT a residual, so ONLY the surfaced `truncated` flag carries
        // the undecidedness.
        let config = ResolveConfig { max_depth: 8, definite_only: true, ..Default::default() };
        let (sols, truncated) = kb.resolve_goals_with_truncation(vec![Value::term(not_loop_1)], &config);
        assert!(
            truncated,
            "a truncated inner not(loop(1)) must set the OUTER stream's truncated flag \
             under definite_only (piece a) — else the guard decides from an incomplete search"
        );
        assert!(
            sols.is_empty(),
            "not(loop(1)) yields no DEFINITE solution under definite_only; the undecidedness \
             rides the truncated flag, not a residual solution"
        );

        // Contrast (no false-positive truncation): not(g(1)) where g is undefined —
        // the inner search COMPLETES empty, so not(g(1)) succeeds definitely and the
        // outer flag stays clear.
        let g_sym = kb.intern("g");
        let not_g_1 = mk_not(&mut kb, g_sym);
        let (sols2, truncated2) = kb.resolve_goals_with_truncation(vec![Value::term(not_g_1)], &config);
        assert!(
            !truncated2,
            "not(g(1)) completes (g undefined) — the outer truncated flag must stay clear"
        );
        assert_eq!(
            sols2.len(),
            1,
            "not(g(1)) succeeds definitely over a COMPLETE empty search"
        );
    }

    #[test]
    fn wi628_carrier_eq_truncation_taints_outer_stream() {
        // WI-628 REMAINING half: a guard goal routing through a carrier `eq` whose
        // CLOSED sub-proof TRUNCATES must taint the OUTER stream's `truncated` flag —
        // the SAME hole the NAF/guard fix closed, but for the semantic-`eq` path
        // (`prove_rule_predicate` → `sem_eq_dispatch`). Before this increment,
        // `sem_eq_dispatch` collapsed truncation into a plain `Delay`, whose
        // definite-only handler skips the frame WITHOUT setting `self.truncated`; a
        // guard draining the stream then read the empty result as a definite verdict.
        // Now the truncation rides a `DelayTruncated` and the step loop folds it up.
        let mut kb = kb_with_builtins();
        // Force truncation cheaply: a tiny sub-proof budget (vs the 100_000 default)
        // so the self-looping `myeq` truncates in a handful of steps, not 100k.
        kb.sem_eq_sub_depth = 32;
        let eq_sym = kb.resolve_symbol("anthill.prelude.PartialEq.eq");
        let sort = kb.make_name_term("Carrier");
        let domain = kb.make_name_term("test");

        // A rule-backed carrier `eq` that self-loops: `myeq(?a, ?b) :- myeq(?a, ?b)`
        // — a non-terminating sub-proof that TRUNCATES at SEM_EQ_SUB_DEPTH, never
        // refutes. `box` is its dispatch head (a `box(_)` operand routes eq→myeq).
        let myeq = kb.intern("myeq");
        let box_sym = kb.intern("box");
        let a_sym = kb.intern("a");
        let b_sym = kb.intern("b");
        let va = kb.fresh_var(a_sym);
        let vb = kb.fresh_var(b_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(va)));
        let var_b = kb.alloc(Term::Var(Var::Global(vb)));
        let myeq_head = kb.alloc(Term::Fn {
            functor: myeq,
            pos_args: SmallVec::from_slice(&[var_a, var_b]),
            named_args: SmallVec::new(),
        });
        let myeq_body = kb.alloc(Term::Fn {
            functor: myeq,
            pos_args: SmallVec::from_slice(&[var_a, var_b]),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(myeq_head, vec![myeq_body], sort, domain, None);
        kb.insert_eq_dispatch(box_sym, myeq);

        // `eq(box(1), box(2))` — two DISTINCT ground `box` operands (no reflexivity
        // shortcut), so dispatch fires `myeq(box(1), box(2))`, which truncates.
        let mk_box = |kb: &mut KnowledgeBase, n: i64| {
            let lit = kb.alloc(Term::Const(Literal::Int(n)));
            kb.alloc(Term::Fn {
                functor: box_sym,
                pos_args: SmallVec::from_elem(lit, 1),
                named_args: SmallVec::new(),
            })
        };
        let box1 = mk_box(&mut kb, 1);
        let box2 = mk_box(&mut kb, 2);
        let eq_goal = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[box1, box2]),
            named_args: SmallVec::new(),
        });

        // definite_only is the guard/quantifier discharge mode — the frame is skipped
        // WITHOUT a residual, so ONLY the surfaced `truncated` flag carries the
        // undecidedness. This is the exact path `eval_negation_guard` &co. drive.
        let config = ResolveConfig { definite_only: true, ..Default::default() };
        let (sols, truncated) =
            kb.resolve_goals_with_truncation(vec![Value::term(eq_goal)], &config);
        assert!(
            truncated,
            "a truncated carrier-eq sub-proof must set the OUTER stream's truncated flag \
             under definite_only — else a guard decides from an incomplete search"
        );
        assert!(
            sols.is_empty(),
            "eq(box(1), box(2)) yields no DEFINITE solution under definite_only; the \
             undecidedness rides the truncated flag, not a residual solution"
        );

        // Contrast (no false-positive truncation): `box0` has NO `myeq0` rule, so its
        // carrier-eq sub-proof COMPLETES empty → decided UNEQUAL (a definite Failure),
        // and the outer truncated flag must stay clear.
        let myeq0 = kb.intern("myeq0");
        let box0_sym = kb.intern("box0");
        kb.insert_eq_dispatch(box0_sym, myeq0);
        let mk_box0 = |kb: &mut KnowledgeBase, n: i64| {
            let lit = kb.alloc(Term::Const(Literal::Int(n)));
            kb.alloc(Term::Fn {
                functor: box0_sym,
                pos_args: SmallVec::from_elem(lit, 1),
                named_args: SmallVec::new(),
            })
        };
        let b0a = mk_box0(&mut kb, 1);
        let b0b = mk_box0(&mut kb, 2);
        let eq_goal0 = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[b0a, b0b]),
            named_args: SmallVec::new(),
        });
        let (sols0, truncated0) =
            kb.resolve_goals_with_truncation(vec![Value::term(eq_goal0)], &config);
        assert!(
            !truncated0,
            "a COMPLETE (unprovable) carrier-eq must leave the outer truncated flag clear"
        );
        assert!(
            sols0.is_empty(),
            "eq over unequal decided operands definitely fails — no solution"
        );

        // Default (NON-definite_only) delay mode: the truncating eq RESIDUALIZES —
        // it yields one solution carrying `eq(box(1),box(2))` as residual AND still
        // taints truncated (the fold runs before the delay_mode branch, so the flag
        // is set on the residualize path too, not only under definite_only).
        let default_cfg = ResolveConfig::default();
        let (sols_d, truncated_d) =
            kb.resolve_goals_with_truncation(vec![Value::term(eq_goal)], &default_cfg);
        assert!(
            truncated_d,
            "truncation must taint the outer flag in default delay mode too, not only definite_only"
        );
        assert_eq!(sols_d.len(), 1, "the truncating eq residualizes to exactly one solution");
        assert!(
            !sols_d[0].residual.is_empty(),
            "the residualized solution carries the undischarged eq goal, not a definite verdict"
        );
    }

    #[test]
    fn wi628_prove_rule_predicate_distinguishes_truncated_from_refuted() {
        // WI-628: the three-way `prove_rule_predicate` verdict must carry `truncated`
        // DISTINCTLY, so `sem_eq_dispatch` propagates a genuine depth-cut but not a
        // mere refutation. A self-looping `pr(?a, ?b) :- pr(?a, ?b)` TRUNCATES →
        // `Undecided { truncated: true }`; a predicate with no clause REFUTES over a
        // complete search → `Refuted` (flag would be false, never surfaced).
        let mut kb = KnowledgeBase::new();
        kb.sem_eq_sub_depth = 32; // truncate cheaply, not at the 100_000 default
        let sort = kb.make_name_term("T");
        let domain = kb.make_name_term("test");
        let pr = kb.intern("pr");
        let a_sym = kb.intern("a");
        let b_sym = kb.intern("b");
        let va = kb.fresh_var(a_sym);
        let vb = kb.fresh_var(b_sym);
        let at = kb.alloc(Term::Var(Var::Global(va)));
        let bt = kb.alloc(Term::Var(Var::Global(vb)));
        let head = kb.alloc(Term::Fn {
            functor: pr,
            pos_args: SmallVec::from_slice(&[at, bt]),
            named_args: SmallVec::new(),
        });
        let body = kb.alloc(Term::Fn {
            functor: pr,
            pos_args: SmallVec::from_slice(&[at, bt]),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(head, vec![body], sort, domain, None);

        let truncating = kb.prove_rule_predicate(pr, vec![Value::Int(1), Value::Int(2)]);
        assert!(
            matches!(truncating, PredicateProof::Undecided { truncated: true }),
            "a self-looping predicate truncates its sub-proof → Undecided{{truncated:true}}, got {truncating:?}",
        );

        // A predicate with NO clause: the search COMPLETES empty → definite refutation
        // (no truncation to propagate).
        let none = kb.intern("no_such_pred");
        let refuted = kb.prove_rule_predicate(none, vec![Value::Int(1), Value::Int(2)]);
        assert!(
            matches!(refuted, PredicateProof::Refuted),
            "a clause-less predicate refutes over a complete search, got {refuted:?}",
        );
    }

    #[test]
    fn wi628_floundered_carrier_eq_does_not_taint_outer_stream() {
        // WI-628 crux: distinguishing genuine TRUNCATION (propagate) from a
        // FLOUNDERED-but-COMPLETE sub-proof (WI-519 undecided, do NOT propagate).
        // A carrier `eq` whose rule body delays on an unbound inner goal FLOUNDERS
        // over a COMPLETE search (no depth cut), so `prove_rule_predicate` returns
        // Undecided{truncated:false} → plain `Delay` → the outer truncated flag must
        // stay CLEAR. If the truncated:false branch wrongly propagated, a guard would
        // suspend spuriously (the over-blocking direction); the Refuted contrast in
        // `wi628_carrier_eq_truncation_taints_outer_stream` can't catch this because
        // a Refuted eq maps to Failure, never a Delay.
        let mut kb = kb_with_builtins();
        let eq_sym = kb.resolve_symbol("anthill.prelude.PartialEq.eq");
        let sort = kb.make_name_term("Carrier");
        let domain = kb.make_name_term("test");

        // `myeq_f(?a, ?b) :- eq(?x, ?y)` — the body compares two FRESH unbound vars
        // (not bound by the head), so the inner `eq` DELAYS → the clause floundes to
        // a residual over a complete (non-truncated) search.
        let myeq_f = kb.intern("myeq_f");
        let box_f = kb.intern("box_f");
        let a_sym = kb.intern("a");
        let b_sym = kb.intern("b");
        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let va = kb.fresh_var(a_sym);
        let vb = kb.fresh_var(b_sym);
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(va)));
        let var_b = kb.alloc(Term::Var(Var::Global(vb)));
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));
        let head = kb.alloc(Term::Fn {
            functor: myeq_f,
            pos_args: SmallVec::from_slice(&[var_a, var_b]),
            named_args: SmallVec::new(),
        });
        let body_eq = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[var_x, var_y]),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(head, vec![body_eq], sort, domain, None);
        kb.insert_eq_dispatch(box_f, myeq_f);

        let mk_box = |kb: &mut KnowledgeBase, n: i64| {
            let lit = kb.alloc(Term::Const(Literal::Int(n)));
            kb.alloc(Term::Fn {
                functor: box_f,
                pos_args: SmallVec::from_elem(lit, 1),
                named_args: SmallVec::new(),
            })
        };
        let box1 = mk_box(&mut kb, 1);
        let box2 = mk_box(&mut kb, 2);

        // Direct: the closed sub-proof is UNDECIDED-but-COMPLETE — truncated:false.
        let proof = kb.prove_rule_predicate(myeq_f, vec![Value::term(box1), Value::term(box2)]);
        assert!(
            matches!(proof, PredicateProof::Undecided { truncated: false }),
            "a floundered-but-complete carrier-eq is Undecided{{truncated:false}}, got {proof:?}",
        );

        // End-to-end: the outer stream's truncated flag must stay CLEAR (the eq still
        // residualizes as an undecided delay, but that is a flounder, not truncation).
        let eq_goal = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[box1, box2]),
            named_args: SmallVec::new(),
        });
        let (sols, truncated) =
            kb.resolve_goals_with_truncation(vec![Value::term(eq_goal)], &ResolveConfig::default());
        assert!(
            !truncated,
            "a FLOUNDERED (complete) carrier-eq must NOT taint the outer truncated flag"
        );
        assert!(
            sols.iter().all(|s| !s.residual.is_empty()),
            "the floundered eq residualizes (undecided), it does not decide"
        );
    }

    #[test]
    fn resolve_no_solution() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");
        let g_sym = kb.intern("g");

        let val = kb.alloc(Term::Const(Literal::Int(1)));
        let fact = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(fact, sort, domain, None);

        // Query for g(1) — no matching facts
        let goal = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal], &config);
        assert!(results.is_empty());
    }

    // ── Equational rewriting tests ──────────────────────────────

    #[test]
    fn simplify_constant_equation() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");

        // Equation: eq(double(2), 4)
        let double_sym = kb.intern("double");
        let two = kb.alloc(Term::Const(Literal::Int(2)));
        let four = kb.alloc(Term::Const(Literal::Int(4)));
        let lhs = kb.alloc(Term::Fn {
            functor: double_sym,
            pos_args: SmallVec::from_elem(two, 1),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, four]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_fact(eq_head, sort, domain, Some(meta));

        // Simplify double(2) → should get 4
        let result = kb.simplify(lhs);
        assert_eq!(result, four);
    }

    #[test]
    fn simplify_variable_equation() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");

        // Equation: eq(negate(negate(?x)), ?x)
        let negate_sym = kb.intern("negate");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let inner_neg = kb.alloc(Term::Fn {
            functor: negate_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let double_neg = kb.alloc(Term::Fn {
            functor: negate_sym,
            pos_args: SmallVec::from_elem(inner_neg, 1),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[double_neg, var_x]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_fact(eq_head, sort, domain, Some(meta));

        // Simplify negate(negate(5)) → should get 5
        let five = kb.alloc(Term::Const(Literal::Int(5)));
        let neg5 = kb.alloc(Term::Fn {
            functor: negate_sym,
            pos_args: SmallVec::from_elem(five, 1),
            named_args: SmallVec::new(),
        });
        let double_neg5 = kb.alloc(Term::Fn {
            functor: negate_sym,
            pos_args: SmallVec::from_elem(neg5, 1),
            named_args: SmallVec::new(),
        });
        let result = kb.simplify(double_neg5);
        assert_eq!(result, five);
    }

    #[test]
    fn simplify_nested_subterms() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");

        // Equation: eq(double(?x), twice(?x))
        let double_sym = kb.intern("double");
        let twice_sym = kb.intern("twice");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let lhs = kb.alloc(Term::Fn {
            functor: double_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let rhs = kb.alloc(Term::Fn {
            functor: twice_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, rhs]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_fact(eq_head, sort, domain, Some(meta));

        // Simplify f(double(3)) → f(twice(3))
        let f_sym = kb.intern("f");
        let three = kb.alloc(Term::Const(Literal::Int(3)));
        let double_3 = kb.alloc(Term::Fn {
            functor: double_sym,
            pos_args: SmallVec::from_elem(three, 1),
            named_args: SmallVec::new(),
        });
        let term = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(double_3, 1),
            named_args: SmallVec::new(),
        });

        let result = kb.simplify(term);
        let expected_inner = kb.alloc(Term::Fn {
            functor: twice_sym,
            pos_args: SmallVec::from_elem(three, 1),
            named_args: SmallVec::new(),
        });
        let expected = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(expected_inner, 1),
            named_args: SmallVec::new(),
        });
        assert_eq!(result, expected);
    }

    #[test]
    fn simplify_no_match_passthrough() {
        let mut kb = KnowledgeBase::new();
        let f_sym = kb.intern("f");
        let val = kb.alloc(Term::Const(Literal::Int(42)));
        let term = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        // No equations in KB, term should pass through unchanged
        let result = kb.simplify(term);
        assert_eq!(result, term);
    }

    // ── Integration: resolve with equational fallback ────────────

    #[test]
    fn resolve_with_simplification() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let f_sym = kb.intern("f");
        let g_sym = kb.intern("g");

        // Equation: eq(f(?x), g(?x)) — f rewrites to g
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let f_x = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let g_x = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[f_x, g_x]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_fact(eq_head, sort, domain, Some(meta));

        // Fact: g(42)
        let val = kb.alloc(Term::Const(Literal::Int(42)));
        let g_42 = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(g_42, sort, domain, None);

        // Query: f(42) — with simplification, f(42) → g(42), which matches the fact
        let f_42 = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { simplify: true, ..Default::default() };
        let results = kb.resolve(&[f_42], &config);
        assert_eq!(results.len(), 1);
    }

    #[test]
    fn resolve_simplification_threads_caller_var() {
        // WI-634 end-to-end: a query var inside a redex must survive the [simp]
        // rewrite and bind through resolution. `[simp] eq(pick(?a, ?b), ?a)` over
        // goal `found(pick(?q, 99))` rewrites the subterm to `found(?q)`, which
        // the fact `found(7)` resolves — binding ?q = 7. Before WI-634's
        // threading the redex was SKIPPED (severing ?q), so the goal never
        // matched the fact → 0 solutions.
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Pick"); // requires-free → resolver fires
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let pick_sym = kb.intern("pick");
        let found_sym = kb.intern("found");

        // [simp] eq(pick(?a, ?b), ?a) — DeBruijn-closed (arity 2), the loaded
        // form; arity-0 Global-var heads never hit the var-RHS bug.
        let a_sym = kb.intern("a");
        let b_sym = kb.intern("b");
        let va = kb.fresh_var(a_sym);
        let vb = kb.fresh_var(b_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(va)));
        let var_b = kb.alloc(Term::Var(Var::Global(vb)));
        let pick_ab = kb.alloc(Term::Fn {
            functor: pick_sym,
            pos_args: SmallVec::from_slice(&[var_a, var_b]),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[pick_ab, var_a]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_rule_debruijn_with_nodes(eq_head, vec![], sort, domain, Some(meta));

        // Fact: found(7)
        let seven = kb.alloc(Term::Const(Literal::Int(7)));
        let found_7 = kb.alloc(Term::Fn {
            functor: found_sym,
            pos_args: SmallVec::from_elem(seven, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(found_7, sort, domain, None);

        // Query: found(pick(?q, 99)) — simplify rewrites pick(?q, 99) → ?q.
        let q_sym = kb.intern("q");
        let vq = kb.fresh_var(q_sym);
        let var_q = kb.alloc(Term::Var(Var::Global(vq)));
        let ninety_nine = kb.alloc(Term::Const(Literal::Int(99)));
        let pick_q99 = kb.alloc(Term::Fn {
            functor: pick_sym,
            pos_args: SmallVec::from_slice(&[var_q, ninety_nine]),
            named_args: SmallVec::new(),
        });
        let goal = kb.alloc(Term::Fn {
            functor: found_sym,
            pos_args: SmallVec::from_elem(pick_q99, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { simplify: true, ..Default::default() };
        let results = kb.resolve(&[goal], &config);
        assert_eq!(results.len(), 1, "rewritten found(?q) matches found(7)");
        assert_eq!(
            kb.reify(var_q, &results[0].subst).expect_term(),
            seven,
            "the caller's ?q binds to 7 through the rewrite (not severed)",
        );
    }

    #[test]
    fn resolve_whole_goal_var_redex_does_not_wildcard() {
        // WI-634 guard: when the WHOLE goal is a var-projecting simp redex
        // (`pick(?q, 99)` under `[simp] eq(pick(?a,?b), ?a)`), the rewrite is a
        // bare caller var `?q`. `step_init` must NOT re-query that bare var —
        // discrim routes a `Global` query head to EVERY leaf, so re-querying
        // would wildcard-match every fact and manufacture spurious solutions. A
        // bare-var goal is not resolvable → 0 solutions.
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Pick");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let pick_sym = kb.intern("pick");

        let a_sym = kb.intern("a");
        let b_sym = kb.intern("b");
        let va = kb.fresh_var(a_sym);
        let vb = kb.fresh_var(b_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(va)));
        let var_b = kb.alloc(Term::Var(Var::Global(vb)));
        let pick_ab = kb.alloc(Term::Fn {
            functor: pick_sym,
            pos_args: SmallVec::from_slice(&[var_a, var_b]),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[pick_ab, var_a]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_rule_debruijn_with_nodes(eq_head, vec![], sort, domain, Some(meta));

        // An unrelated fact the bare-var wildcard would spuriously match.
        let one = kb.alloc(Term::Const(Literal::Int(1)));
        let other_sym = kb.intern("other");
        let other_1 = kb.alloc(Term::Fn {
            functor: other_sym,
            pos_args: SmallVec::from_elem(one, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(other_1, sort, domain, None);

        // Whole-goal redex: pick(?q, 99) → ?q (bare var).
        let q_sym = kb.intern("q");
        let vq = kb.fresh_var(q_sym);
        let var_q = kb.alloc(Term::Var(Var::Global(vq)));
        let ninety_nine = kb.alloc(Term::Const(Literal::Int(99)));
        let goal = kb.alloc(Term::Fn {
            functor: pick_sym,
            pos_args: SmallVec::from_slice(&[var_q, ninety_nine]),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { simplify: true, ..Default::default() };
        let results = kb.resolve(&[goal], &config);
        assert_eq!(
            results.len(),
            0,
            "a whole-goal bare-var rewrite must not wildcard-match unrelated facts",
        );
    }

    #[test]
    fn apply_eq_rules_returns_changes() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Eq");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");

        // Equation: eq(double(2), 4)
        let double_sym = kb.intern("double");
        let two = kb.alloc(Term::Const(Literal::Int(2)));
        let four = kb.alloc(Term::Const(Literal::Int(4)));
        let lhs = kb.alloc(Term::Fn {
            functor: double_sym,
            pos_args: SmallVec::from_elem(two, 1),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, four]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_fact(eq_head, sort, domain, Some(meta));

        let (result, changes) = kb.apply_eq_rules(&Value::term(lhs), 100, &Substitution::new());
        assert_eq!(result.expect_term(), four);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].original.expect_term(), lhs);
        assert_eq!(changes[0].rewritten.expect_term(), four);
    }

    #[test]
    fn apply_eq_rules_instantiates_var_rhs() {
        // WI-584: a DeBruijn var-RHS equation (the loaded `[simp]` form, unlike
        // the arity-0 `assert_fact` Global-var form which never hit the bug)
        // must fire to its SUBSTITUTED RHS, not the raw `DeBruijn(n)` template.
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Pick"); // requires-free → resolver fires it
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq"); // matches `eq_functor()`'s bare fallback
        let pick_sym = kb.intern("pick");

        // Equation: eq(pick(?a, ?b), ?a) — projects the first argument.
        let a_sym = kb.intern("a");
        let b_sym = kb.intern("b");
        let va = kb.fresh_var(a_sym);
        let vb = kb.fresh_var(b_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(va)));
        let var_b = kb.alloc(Term::Var(Var::Global(vb)));
        let pick_ab = kb.alloc(Term::Fn {
            functor: pick_sym,
            pos_args: SmallVec::from_slice(&[var_a, var_b]),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[pick_ab, var_a]),
            named_args: SmallVec::new(),
        });
        // DeBruijn-close (arity 2) — the loader's form. assert_fact would store
        // arity-0 Global vars, which reify resolves directly (no bug). Tag `[simp]`
        // (WI-292): `apply_eq_rules` fires only directional rewrites.
        let meta = simp_meta(&mut kb);
        kb.assert_rule_debruijn_with_nodes(eq_head, vec![], sort, domain, Some(meta));

        // simplify(pick(5, 7)) → 5  (returned Var(DeBruijn(0)) before WI-584).
        let five = kb.alloc(Term::Const(Literal::Int(5)));
        let seven = kb.alloc(Term::Const(Literal::Int(7)));
        let pick_57 = kb.alloc(Term::Fn {
            functor: pick_sym,
            pos_args: SmallVec::from_slice(&[five, seven]),
            named_args: SmallVec::new(),
        });

        let (result, changes) = kb.apply_eq_rules(&Value::term(pick_57), 100, &Substitution::new());
        assert_eq!(result.expect_term(), five, "var-RHS rule must instantiate to the matched first arg");
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].rewritten.expect_term(), five);
    }

    #[test]
    fn apply_eq_rules_skips_inexpressible_query_var_links() {
        // WI-633 / WI-634 loud gate: a term rewrite can only express the
        // synthetic LHS-match entries. A NONLINEAR `[simp]` LHS over a
        // half-ground redex UNIFIES the repeated var's two matches (WI-633's
        // leaf unification) — a substitution effect (`?x = 42`) the rewrite
        // cannot carry — so the candidate must NOT fire (it would rewrite to
        // `0`, silently dropping the constraint). The doubly-ground redex
        // (synthetic entries only) fires as before.
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Sub"); // requires-free → resolver fires it
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let sub_sym = kb.intern("sub");
        let f_sym = kb.intern("f");

        // Equation: [simp] eq(sub(?a, ?a), 0) — nonlinear LHS.
        let a_sym = kb.intern("a");
        let va = kb.fresh_var(a_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(va)));
        let sub_aa = kb.alloc(Term::Fn {
            functor: sub_sym,
            pos_args: SmallVec::from_slice(&[var_a, var_a]),
            named_args: SmallVec::new(),
        });
        let zero = kb.alloc(Term::Const(Literal::Int(0)));
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[sub_aa, zero]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_rule_debruijn_with_nodes(eq_head, vec![], sort, domain, Some(meta));

        // Half-ground redex: sub(f(?x), f(42)) — the match links ?x = 42 → skip.
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let f_x = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let forty_two = kb.alloc(Term::Const(Literal::Int(42)));
        let f_42 = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(forty_two, 1),
            named_args: SmallVec::new(),
        });
        let redex = kb.alloc(Term::Fn {
            functor: sub_sym,
            pos_args: SmallVec::from_slice(&[f_x, f_42]),
            named_args: SmallVec::new(),
        });
        let (result, changes) = kb.apply_eq_rules(&Value::term(redex), 100, &Substitution::new());
        assert_eq!(result.expect_term(), redex, "half-ground nonlinear match must not rewrite (would drop ?x = 42)");
        assert!(changes.is_empty());

        // Doubly-ground redex: sub(f(42), f(42)) → 0.
        let redex_ground = kb.alloc(Term::Fn {
            functor: sub_sym,
            pos_args: SmallVec::from_slice(&[f_42, f_42]),
            named_args: SmallVec::new(),
        });
        let (result, changes) = kb.apply_eq_rules(&Value::term(redex_ground), 100, &Substitution::new());
        assert_eq!(result.expect_term(), zero, "ground nonlinear match still fires");
        assert_eq!(changes.len(), 1);
    }

    #[test]
    fn apply_eq_rules_threads_severing_var_redex() {
        // WI-634(a) completeness: `[simp] eq(pick(?a, ?b), ?a)` over redex
        // pick(?q, 7) projects the redex var `?q` into the RHS. `fire_simp_equation`
        // provides this via `match_view` — a one-way match leaves `?q` inert, so it
        // rides into the opened RHS bound to the caller's `?q` instead of a
        // disconnected fresh global — so the rewrite fires to `?q`, keeping it
        // bound through resolution (was skipped before the threading landed; the
        // earlier gate proved severing, not correctness).
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Pick");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let pick_sym = kb.intern("pick");

        let a_sym = kb.intern("a");
        let b_sym = kb.intern("b");
        let va = kb.fresh_var(a_sym);
        let vb = kb.fresh_var(b_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(va)));
        let var_b = kb.alloc(Term::Var(Var::Global(vb)));
        let pick_ab = kb.alloc(Term::Fn {
            functor: pick_sym,
            pos_args: SmallVec::from_slice(&[var_a, var_b]),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[pick_ab, var_a]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_rule_debruijn_with_nodes(eq_head, vec![], sort, domain, Some(meta));

        let q_sym = kb.intern("q");
        let vq = kb.fresh_var(q_sym);
        let var_q = kb.alloc(Term::Var(Var::Global(vq)));
        let seven = kb.alloc(Term::Const(Literal::Int(7)));
        let pick_q7 = kb.alloc(Term::Fn {
            functor: pick_sym,
            pos_args: SmallVec::from_slice(&[var_q, seven]),
            named_args: SmallVec::new(),
        });

        let (result, changes) = kb.apply_eq_rules(&Value::term(pick_q7), 100, &Substitution::new());
        assert_eq!(result.expect_term(), var_q, "a linear query-var link threads to the caller's ?q");
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].rewritten.expect_term(), var_q, "record keeps ?q, no DeBruijn leak");

        // Subterm case: g(pick(?q, 7)) rewrites innermost to g(?q), so the
        // parent keeps ?q — resolution binds it through the rewrite.
        let g_sym = kb.intern("g");
        let g_pick = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(pick_q7, 1),
            named_args: SmallVec::new(),
        });
        let g_q = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(var_q, 1),
            named_args: SmallVec::new(),
        });
        let (result, changes) = kb.apply_eq_rules(&Value::term(g_pick), 100, &Substitution::new());
        assert_eq!(result.expect_term(), g_q, "innermost rewrite of a subterm preserves ?q in the parent");
        assert_eq!(changes.len(), 1);
    }

    #[test]
    fn apply_eq_rules_skips_nonlinear_query_var_redex() {
        // WI-634 linearity guard: a NONLINEAR LHS whose repeated var meets a
        // query var (`[simp] eq(sub(?a, ?a), 0)` over sub(?q, f(42))) records a
        // query link at DB-0 AND a synthetic value at DB-0 — the constraint
        // `?q = f(42)` a rewrite cannot carry. Must skip, not silently thread
        // one and drop the other.
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Sub");
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let sub_sym = kb.intern("sub");
        let f_sym = kb.intern("f");

        let a_sym = kb.intern("a");
        let va = kb.fresh_var(a_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(va)));
        let sub_aa = kb.alloc(Term::Fn {
            functor: sub_sym,
            pos_args: SmallVec::from_slice(&[var_a, var_a]),
            named_args: SmallVec::new(),
        });
        let zero = kb.alloc(Term::Const(Literal::Int(0)));
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[sub_aa, zero]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_rule_debruijn_with_nodes(eq_head, vec![], sort, domain, Some(meta));

        // sub(?q, f(42)) — DB-0 is covered by both ?q (query link) and f(42)
        // (synthetic). Nonlinear constraint → skip.
        let q_sym = kb.intern("q");
        let vq = kb.fresh_var(q_sym);
        let var_q = kb.alloc(Term::Var(Var::Global(vq)));
        let forty_two = kb.alloc(Term::Const(Literal::Int(42)));
        let f_42 = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(forty_two, 1),
            named_args: SmallVec::new(),
        });
        let redex = kb.alloc(Term::Fn {
            functor: sub_sym,
            pos_args: SmallVec::from_slice(&[var_q, f_42]),
            named_args: SmallVec::new(),
        });
        let (result, changes) = kb.apply_eq_rules(&Value::term(redex), 100, &Substitution::new());
        assert_eq!(result.expect_term(), redex, "nonlinear query-var match must not rewrite (drops ?q = f(42))");
        assert!(changes.is_empty());
    }

    #[test]
    fn apply_eq_rules_deep_term_redex_does_not_overflow() {
        // WI-643 acceptance: a deeply-nested *term* redex now drives the SAME
        // shared iterative driver as the Node carrier, so it (a) can't overflow
        // the host stack and (b) reaches the innermost redex regardless of depth.
        // The former recursive term walk spent `fuel` on DESCENT DEPTH (`fuel - 1`
        // per level), so an innermost redex nested deeper than `fuel` (100) was
        // never reached — this test nests it far deeper and confirms it fires.
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Add"); // requires-free → the resolver fires it
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let add = kb.intern("add");
        let wrap = kb.intern("wrap");

        // [simp] eq(add(?x, 0), ?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let zero_t = kb.alloc(Term::Const(Literal::Int(0)));
        let add_x0 = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[var_x, zero_t]),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[add_x0, var_x]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_rule_debruijn_with_nodes(eq_head, vec![], sort, domain, Some(meta));

        // Redex term: wrap(wrap(…wrap(add(7, 0))…)) at a depth the recursive walk
        // could not reach (fuel-as-depth stopped it at 100).
        const DEPTH: usize = 200_000;
        let seven = kb.alloc(Term::Const(Literal::Int(7)));
        let zero = kb.alloc(Term::Const(Literal::Int(0)));
        let mut node = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[seven, zero]),
            named_args: SmallVec::new(),
        });
        for _ in 0..DEPTH {
            node = kb.alloc(Term::Fn {
                functor: wrap,
                pos_args: SmallVec::from_elem(node, 1),
                named_args: SmallVec::new(),
            });
        }

        let (result, changes) = kb.apply_eq_rules(&Value::term(node), 100, &Substitution::new());
        assert_eq!(changes.len(), 1, "exactly the innermost add(7, 0) should fire");

        // Walk down the wrap chain and confirm the innermost add(7, 0) → 7.
        let mut cur = result.expect_term();
        for _ in 0..DEPTH {
            cur = match kb.get_term(cur) {
                Term::Fn { functor, pos_args, .. } if *functor == wrap => pos_args[0],
                other => panic!("expected wrap(...), got {other:?}"),
            };
        }
        assert_eq!(cur, seven, "innermost add(7, 0) should have rewritten to 7");
    }

    #[test]
    fn apply_eq_rules_fires_unfold_only_kb() {
        // WI-643 regression: `apply_eq_rules` fires `[simp]` OR `[unfold]`
        // (`equation_is_directional_rewrite`), so it must NOT gate on a
        // simp-ONLY predicate. A KB with an `[unfold]`-tagged equation and ZERO
        // `[simp]` equations must still rewrite — an earlier `has_simp_equations`
        // short-circuit (simp-only) silently skipped every unfold rewrite here.
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Def"); // requires-free → the resolver fires it
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let unfold_me = kb.intern("unfold_me");
        let done = kb.intern("done");

        // [unfold] eq(unfold_me(?x), done(?x)) — NO [simp] rule anywhere.
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let lhs = kb.alloc(Term::Fn {
            functor: unfold_me,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let rhs = kb.alloc(Term::Fn {
            functor: done,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[lhs, rhs]),
            named_args: SmallVec::new(),
        });
        let unfold_sym = kb.intern("unfold");
        let meta_sym = kb.intern("meta");
        let tru = kb.alloc(Term::Const(Literal::Bool(true)));
        let meta = kb.alloc(Term::Fn {
            functor: meta_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::from_slice(&[(unfold_sym, tru)]),
        });
        kb.assert_rule_debruijn_with_nodes(eq_head, vec![], sort, domain, Some(meta));

        // simplify(unfold_me(7)) → done(7)
        let seven = kb.alloc(Term::Const(Literal::Int(7)));
        let redex = kb.alloc(Term::Fn {
            functor: unfold_me,
            pos_args: SmallVec::from_elem(seven, 1),
            named_args: SmallVec::new(),
        });
        let expected = kb.alloc(Term::Fn {
            functor: done,
            pos_args: SmallVec::from_elem(seven, 1),
            named_args: SmallVec::new(),
        });
        assert_eq!(
            kb.simplify(redex),
            expected,
            "an [unfold]-only KB (no [simp] rules) must still rewrite unfold_me(7) → done(7)"
        );
    }

    #[test]
    fn apply_eq_rules_gate_invalidates_when_rule_added() {
        // WI-646: the O(1) `has_directional_rewrite` gate is a KB-cached bit. A
        // gate computed `false` (no directional rule) MUST be invalidated when a
        // `[simp]` rule is later asserted, or `apply_eq_rules` would keep
        // short-circuiting and never rewrite. Exercises the compute-false →
        // invalidate-on-assert → recompute-true sequence.
        let mut kb = KnowledgeBase::new();
        let add = kb.intern("add");
        let seven = kb.alloc(Term::Const(Literal::Int(7)));
        let zero = kb.alloc(Term::Const(Literal::Int(0)));
        let redex = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[seven, zero]),
            named_args: SmallVec::new(),
        });

        // No directional rule yet: the gate computes (and caches) `false`, so
        // `simplify` returns the redex unchanged.
        assert_eq!(kb.simplify(redex), redex, "empty KB: add(7, 0) is left as-is");

        // Assert `[simp] eq(add(?x, 0), ?x)` — this must invalidate the cached
        // gate (via `push_value_head_entry`).
        let sort = kb.make_name_term("Add"); // requires-free → the resolver fires it
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
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
        kb.assert_rule_debruijn_with_nodes(eq_head, vec![], sort, domain, Some(meta));

        // Gate recomputes `true` on the next call: add(7, 0) → 7.
        assert_eq!(
            kb.simplify(redex),
            seven,
            "after asserting [simp] add(?x,0)=?x, the invalidated gate recomputes \
             true and add(7, 0) rewrites to 7"
        );
    }

    #[test]
    fn simp_gate_survives_unrelated_functor_mutation() {
        // WI-665: the simp gate depends ONLY on the `eq`/`unify` buckets, so a
        // mutation to any other functor must leave the cached bit intact —
        // functor-specific invalidation, superseding WI-646's drop-on-any-write.
        // Behaviourally a needless drop is invisible (it just recomputes the same
        // value), so this asserts on the cache field directly.
        let mut kb = KnowledgeBase::new();
        let add = kb.intern("add");
        let seven = kb.alloc(Term::Const(Literal::Int(7)));
        let zero = kb.alloc(Term::Const(Literal::Int(0)));
        let redex = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[seven, zero]),
            named_args: SmallVec::new(),
        });

        // First simplify computes and caches the gate (`Some(false)` — no rule).
        assert_eq!(kb.simplify(redex), redex);
        assert!(
            kb.simp_gate_cache.is_some(),
            "the gate is cached after the first simplify"
        );

        // Assert an UNRELATED functor's fact — this must NOT invalidate the gate.
        let foo = kb.intern("foo");
        let foo_head = kb.alloc(Term::Fn {
            functor: foo,
            pos_args: SmallVec::from_slice(&[seven]),
            named_args: SmallVec::new(),
        });
        let foo_sort = kb.make_name_term("Foo");
        let domain = kb.make_name_term("test");
        kb.assert_fact(foo_head, foo_sort, domain, None);
        assert!(
            kb.simp_gate_cache.is_some(),
            "asserting an unrelated functor must NOT invalidate the simp gate \
             (WI-665 functor-specific invalidation)"
        );

        // Asserting an `eq` [simp] rule DOES touch the gate's bucket → invalidated.
        let eq_sym = kb.intern("eq");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
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
        let sort = kb.make_name_term("Add");
        kb.assert_rule_debruijn_with_nodes(eq_head, vec![], sort, domain, Some(meta));
        assert!(
            kb.simp_gate_cache.is_none(),
            "asserting an `eq` [simp] rule DOES invalidate the gate"
        );
    }

    #[test]
    fn apply_eq_rules_deep_node_goal_does_not_overflow() {
        // WI-641 Phase 2 acceptance: a deeply-nested `Value::Node` occurrence
        // redex rewrites through the SHARED iterative driver
        // (`simp_rewrite::rewrite`) instead of the former recursive
        // `apply_eq_rules_occurrence`, so a Node prove-goal nested far deeper than
        // the host-stack budget simplifies without crashing — and the innermost
        // redex still fires. Mirrors the typer's
        // `deeply_nested_body_does_not_overflow_host_stack`, on the resolver path.
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Add"); // requires-free → the resolver fires it
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let add = kb.intern("add");
        let wrap = kb.intern("wrap");

        // [simp] eq(add(?x, 0), ?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let zero_t = kb.alloc(Term::Const(Literal::Int(0)));
        let add_x0 = kb.alloc(Term::Fn {
            functor: add,
            pos_args: SmallVec::from_slice(&[var_x, zero_t]),
            named_args: SmallVec::new(),
        });
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[add_x0, var_x]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_rule_debruijn_with_nodes(eq_head, vec![], sort, domain, Some(meta));

        // Goal occurrence: wrap(wrap(…wrap(add(7, 0))…)) at a depth the recursive
        // walk could not survive.
        const DEPTH: usize = 200_000;
        let span = crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);
        let seven = NodeOccurrence::new_expr(Expr::Const(Literal::Int(7)), span, None);
        let zero_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(0)), span, None);
        let mut node = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: add,
                pos_args: vec![std::rc::Rc::clone(&seven), zero_occ],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );
        for _ in 0..DEPTH {
            node = NodeOccurrence::new_expr(
                Expr::Apply { functor: wrap, pos_args: vec![node], named_args: vec![], type_args: vec![] },
                span,
                None,
            );
        }

        let (result, changes) = kb.apply_eq_rules(&Value::Node(node), 100, &Substitution::new());
        assert_eq!(changes.len(), 1, "exactly the innermost add(7, 0) should fire");

        // Walk down the wrap chain and confirm the innermost add(7, 0) → 7.
        let mut cur = match result {
            Value::Node(n) => n,
            other => panic!("expected a Node result, got {}", other.type_name()),
        };
        for _ in 0..DEPTH {
            cur = match cur.as_expr() {
                Some(Expr::Apply { functor, pos_args, .. }) if *functor == wrap => {
                    std::rc::Rc::clone(&pos_args[0])
                }
                other => panic!("expected wrap(...), got {other:?}"),
            };
        }
        assert!(
            matches!(cur.as_expr(), Some(Expr::Const(Literal::Int(7)))),
            "innermost add(7, 0) should have rewritten to 7, got {:?}",
            cur.as_expr()
        );
        assert!(std::rc::Rc::ptr_eq(&cur, &seven), "innermost redex should reuse the matched `7`");
    }

    #[test]
    fn apply_eq_rules_fires_bare_leaf_node_redex() {
        // WI-641 Phase 2 regression: the Node path routes through the shared
        // iterative driver, whose `visit_node` gates DESCENT on `is_rewritable`
        // but attempts a FIRE at every node — so a functor-less leaf redex (a
        // `Const`/`Ident`-LHS rewrite, which `fire_simp_equation` supports) still
        // fires, exactly as the former recursive walk's shared top-fire did.
        // Without the fire/descend split a `Const` leaf child would be skipped,
        // diverging from the term carrier (which still fires it).
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Lit"); // requires-free → resolver fires it
        let domain = kb.make_name_term("test");
        let eq_sym = kb.intern("eq");
        let wrap = kb.intern("wrap");

        // [simp] eq(1, 2) — a bare-Const LHS (stored_lhs_functor == None).
        let one = kb.alloc(Term::Const(Literal::Int(1)));
        let two = kb.alloc(Term::Const(Literal::Int(2)));
        let eq_head = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[one, two]),
            named_args: SmallVec::new(),
        });
        let meta = simp_meta(&mut kb);
        kb.assert_fact(eq_head, sort, domain, Some(meta));

        // Node goal: wrap(1) — the redex `1` is a Const LEAF child of wrap.
        let span = crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);
        let one_occ = NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None);
        let goal = NodeOccurrence::new_expr(
            Expr::Apply { functor: wrap, pos_args: vec![one_occ], named_args: vec![], type_args: vec![] },
            span,
            None,
        );

        let (result, changes) = kb.apply_eq_rules(&Value::Node(goal), 100, &Substitution::new());
        assert_eq!(changes.len(), 1, "the bare-Const leaf `1` should fire to `2`");
        match result {
            Value::Node(n) => match n.as_expr() {
                Some(Expr::Apply { functor, pos_args, .. }) => {
                    assert_eq!(*functor, wrap);
                    assert!(
                        matches!(pos_args[0].as_expr(), Some(Expr::Const(Literal::Int(2)))),
                        "leaf child `1` should have rewritten to `2`, got {:?}",
                        pos_args[0].as_expr()
                    );
                }
                other => panic!("expected wrap(2), got {other:?}"),
            },
            other => panic!("expected a Node result, got {}", other.type_name()),
        }
    }

    // ── Builtin dispatch + delay tests ─────────────────────────

    /// Helper: set up a KB with standard builtins registered.
    fn kb_with_builtins() -> KnowledgeBase {
        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        kb.register_standard_builtins();
        kb
    }

    #[test]
    fn nonvar_succeeds_on_bound_var() {
        // f(?x), anthill.reflect.nonvar(?x) where f("hello") exists → success, no residual
        let mut kb = kb_with_builtins();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");
        let nonvar_sym = kb.resolve_symbol("anthill.reflect.nonvar");

        let hello = kb.alloc(Term::Const(Literal::String("hello".into())));
        let f_hello = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(hello, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f_hello, sort, domain, None);

        // Query: f(?x), anthill.reflect.nonvar(?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let goal_f = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let goal_nonvar = kb.alloc(Term::Fn {
            functor: nonvar_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal_f, goal_nonvar], &config);
        assert_eq!(results.len(), 1);
        assert!(results[0].residual.is_empty());
        assert_eq!(kb.reify(var_x, &results[0].subst).expect_term(), hello);
    }

    #[test]
    fn nonvar_delays_then_succeeds() {
        // anthill.reflect.nonvar(?x), f(?x) → nonvar delays, f binds x, nonvar retried → success
        let mut kb = kb_with_builtins();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");
        let nonvar_sym = kb.resolve_symbol("anthill.reflect.nonvar");

        let hello = kb.alloc(Term::Const(Literal::String("hello".into())));
        let f_hello = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(hello, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f_hello, sort, domain, None);

        // Query: anthill.reflect.nonvar(?x), f(?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let goal_nonvar = kb.alloc(Term::Fn {
            functor: nonvar_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let goal_f = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal_nonvar, goal_f], &config);
        assert_eq!(results.len(), 1);
        assert!(results[0].residual.is_empty());
        assert_eq!(kb.reify(var_x, &results[0].subst).expect_term(), hello);
    }

    #[test]
    fn nonvar_residualizes_when_permanently_unbound() {
        // anthill.reflect.nonvar(?x) alone → residual contains the goal
        let mut kb = kb_with_builtins();
        let nonvar_sym = kb.resolve_symbol("anthill.reflect.nonvar");

        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let goal = kb.alloc(Term::Fn {
            functor: nonvar_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal], &config);
        assert_eq!(results.len(), 1);
        assert_eq!(results[0].residual.len(), 1);
        assert_eq!(results[0].residual[0].expect_term(), goal);
    }

    #[test]
    fn ground_succeeds_on_literal() {
        // f(?x), anthill.reflect.ground(?x) where f(42) exists → success
        let mut kb = kb_with_builtins();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");
        let ground_sym = kb.resolve_symbol("anthill.reflect.ground");

        let val = kb.alloc(Term::Const(Literal::Int(42)));
        let f_42 = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f_42, sort, domain, None);

        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let goal_f = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let goal_ground = kb.alloc(Term::Fn {
            functor: ground_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal_f, goal_ground], &config);
        assert_eq!(results.len(), 1);
        assert!(results[0].residual.is_empty());
    }

    #[test]
    fn ground_delays_on_partial_binding() {
        // f(?x), anthill.reflect.ground(?x) where f binds x to pair(?y) → ground delays, residualizes
        let mut kb = kb_with_builtins();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");
        let pair_sym = kb.intern("pair");
        let ground_sym = kb.resolve_symbol("anthill.reflect.ground");

        // Fact: f(pair(?y)) — not ground, has an unbound variable inside
        let y_sym = kb.intern("y");
        let vy = kb.fresh_var(y_sym);
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));
        let pair_y = kb.alloc(Term::Fn {
            functor: pair_sym,
            pos_args: SmallVec::from_elem(var_y, 1),
            named_args: SmallVec::new(),
        });
        let f_pair = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(pair_y, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f_pair, sort, domain, None);

        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let goal_f = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let goal_ground = kb.alloc(Term::Fn {
            functor: ground_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal_f, goal_ground], &config);
        assert_eq!(results.len(), 1);
        assert!(!results[0].residual.is_empty(), "ground should residualize when argument contains unbound var");
    }

    #[test]
    fn existing_resolve_unchanged() {
        // No builtins registered, basic resolution still works with empty residual
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");

        let val = kb.alloc(Term::Const(Literal::Int(1)));
        let fact = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(fact, sort, domain, None);

        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let goal = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[goal], &config);
        assert_eq!(results.len(), 1);
        assert!(results[0].residual.is_empty());
        assert_eq!(results[0].subst.resolve_as_value(vx).map(|v| v.expect_term()), Some(val));
    }

    #[test]
    fn builtin_precedence_over_rules() {
        // Rules can be asserted for builtin functors, but builtins always
        // take precedence at resolution time.
        let mut kb = kb_with_builtins();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let nonvar_sym = kb.resolve_symbol("anthill.reflect.nonvar");

        let val = kb.alloc(Term::Const(Literal::Int(1)));
        let head = kb.alloc(Term::Fn {
            functor: nonvar_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });
        // Asserting a fact with a builtin functor is allowed
        kb.assert_fact(head, sort, domain, None);

        // But the builtin still handles resolution (not the fact)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let goal = kb.alloc(Term::Fn {
            functor: nonvar_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        // nonvar(?x) with unbound ?x should delay (builtin behavior),
        // not succeed (which would happen if the ground fact were matched)
        let results = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(results.len(), 1, "should residualize");
        assert_eq!(results[0].residual.len(), 1, "nonvar(?x) should be in residual");
    }

    // ── Delay propagation through rules ────────────────────────

    #[test]
    fn delay_propagates_through_rule_body() {
        // Rule: check(?x) :- nonvar(?x), is_thing(?x)
        // Fact: is_thing(42)
        // Query: check(?a), bind_a(?a)  where bind_a(42) is a fact
        //
        // Without propagation: check(?a) fires rule, nonvar delays,
        //   is_thing enumerates, nonvar becomes vacuous (guard defeated).
        // With propagation: check(?a) delays (nonvar on caller var),
        //   bind_a binds ?a=42, check(42) retries → nonvar(42) succeeds.
        let mut kb = kb_with_builtins();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let nonvar_sym = kb.resolve_symbol("anthill.reflect.nonvar");
        let check_sym = kb.intern("check");
        let is_thing_sym = kb.intern("is_thing");
        let bind_a_sym = kb.intern("bind_a");

        // Fact: is_thing(42)
        let val_42 = kb.alloc(Term::Const(Literal::Int(42)));
        let is_thing_42 = kb.alloc(Term::Fn {
            functor: is_thing_sym,
            pos_args: SmallVec::from_elem(val_42, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(is_thing_42, sort, domain, None);

        // Fact: bind_a(42)
        let bind_a_42 = kb.alloc(Term::Fn {
            functor: bind_a_sym,
            pos_args: SmallVec::from_elem(val_42, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(bind_a_42, sort, domain, None);

        // Rule: check(?x) :- nonvar(?x), is_thing(?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let check_head = kb.alloc(Term::Fn {
            functor: check_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let nonvar_goal = kb.alloc(Term::Fn {
            functor: nonvar_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let is_thing_goal = kb.alloc(Term::Fn {
            functor: is_thing_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(check_head, vec![nonvar_goal, is_thing_goal], sort, domain, None);

        // Query: check(?a), bind_a(?a)
        let a_sym = kb.intern("a");
        let va = kb.fresh_var(a_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(va)));

        let q_check = kb.alloc(Term::Fn {
            functor: check_sym,
            pos_args: SmallVec::from_elem(var_a, 1),
            named_args: SmallVec::new(),
        });
        let q_bind = kb.alloc(Term::Fn {
            functor: bind_a_sym,
            pos_args: SmallVec::from_elem(var_a, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[q_check, q_bind], &config);
        assert_eq!(results.len(), 1);
        assert!(results[0].residual.is_empty());
        assert_eq!(kb.reify(var_a, &results[0].subst).expect_term(), val_42);
    }

    #[test]
    fn delay_propagation_residualizes_when_unresolvable() {
        // Rule: check(?x) :- nonvar(?x), is_thing(?x)
        // Query: check(?a) with ?a never bound → check(?a) delays, residualizes
        let mut kb = kb_with_builtins();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let nonvar_sym = kb.resolve_symbol("anthill.reflect.nonvar");
        let check_sym = kb.intern("check");
        let is_thing_sym = kb.intern("is_thing");

        // Fact: is_thing(42)
        let val_42 = kb.alloc(Term::Const(Literal::Int(42)));
        let is_thing_42 = kb.alloc(Term::Fn {
            functor: is_thing_sym,
            pos_args: SmallVec::from_elem(val_42, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(is_thing_42, sort, domain, None);

        // Rule: check(?x) :- nonvar(?x), is_thing(?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let check_head = kb.alloc(Term::Fn {
            functor: check_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let nonvar_goal = kb.alloc(Term::Fn {
            functor: nonvar_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let is_thing_goal = kb.alloc(Term::Fn {
            functor: is_thing_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(check_head, vec![nonvar_goal, is_thing_goal], sort, domain, None);

        // Query: check(?a) alone — ?a never bound
        let a_sym = kb.intern("a");
        let va = kb.fresh_var(a_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(va)));

        let q_check = kb.alloc(Term::Fn {
            functor: check_sym,
            pos_args: SmallVec::from_elem(var_a, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[q_check], &config);
        assert_eq!(results.len(), 1);
        assert!(!results[0].residual.is_empty(), "check(?a) should residualize when ?a is unbound");
    }

    #[test]
    fn nonvar_internal_var_still_reorders_in_body() {
        // Rule: foo(?x) :- bar(?y), nonvar(?y), baz(?y, ?x)
        // Here ?y is internal — nonvar(?y) should reorder within body (not propagate).
        // bar(?y) binds ?y, then nonvar succeeds.
        let mut kb = kb_with_builtins();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let nonvar_sym = kb.resolve_symbol("anthill.reflect.nonvar");
        let foo_sym = kb.intern("foo");
        let bar_sym = kb.intern("bar");
        let baz_sym = kb.intern("baz");

        // Fact: bar(10)
        let val_10 = kb.alloc(Term::Const(Literal::Int(10)));
        let bar_10 = kb.alloc(Term::Fn {
            functor: bar_sym,
            pos_args: SmallVec::from_elem(val_10, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(bar_10, sort, domain, None);

        // Fact: baz(10, 99)
        let val_99 = kb.alloc(Term::Const(Literal::Int(99)));
        let baz_10_99 = kb.alloc(Term::Fn {
            functor: baz_sym,
            pos_args: SmallVec::from_slice(&[val_10, val_99]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(baz_10_99, sort, domain, None);

        // Rule: foo(?x) :- bar(?y), nonvar(?y), baz(?y, ?x)
        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));

        let foo_head = kb.alloc(Term::Fn {
            functor: foo_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let bar_body = kb.alloc(Term::Fn {
            functor: bar_sym,
            pos_args: SmallVec::from_elem(var_y, 1),
            named_args: SmallVec::new(),
        });
        let nonvar_body = kb.alloc(Term::Fn {
            functor: nonvar_sym,
            pos_args: SmallVec::from_elem(var_y, 1),
            named_args: SmallVec::new(),
        });
        let baz_body = kb.alloc(Term::Fn {
            functor: baz_sym,
            pos_args: SmallVec::from_slice(&[var_y, var_x]),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(foo_head, vec![bar_body, nonvar_body, baz_body], sort, domain, None);

        // Query: foo(?a) — ?y is internal, bar binds it, nonvar reorders within body
        let a_sym = kb.intern("a");
        let va = kb.fresh_var(a_sym);
        let var_a = kb.alloc(Term::Var(Var::Global(va)));

        let q_foo = kb.alloc(Term::Fn {
            functor: foo_sym,
            pos_args: SmallVec::from_elem(var_a, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let results = kb.resolve(&[q_foo], &config);
        assert_eq!(results.len(), 1);
        assert!(results[0].residual.is_empty());
        assert_eq!(kb.reify(var_a, &results[0].subst).expect_term(), val_99);
    }

    // ── SearchStream (lazy) tests ───────────────────────────────

    #[test]
    fn search_stream_basic() {
        // split_first yields solutions one at a time
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");

        let v1 = kb.alloc(Term::Const(Literal::Int(1)));
        let v2 = kb.alloc(Term::Const(Literal::Int(2)));
        let f1 = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(v1, 1),
            named_args: SmallVec::new(),
        });
        let f2 = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(v2, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f1, sort, domain, None);
        kb.assert_fact(f2, sort, domain, None);

        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let goal = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let stream = kb.resolve_lazy(&[goal], &config);
        assert!(!stream.is_empty());

        let (sol1, stream) = stream.split_first(&mut kb).expect("should have first solution");
        assert!(sol1.residual.is_empty());

        let (sol2, stream) = stream.split_first(&mut kb).expect("should have second solution");
        assert!(sol2.residual.is_empty());

        // Exhausted
        assert!(stream.split_first(&mut kb).is_none());
    }

    #[test]
    fn search_stream_lazy() {
        // Consume only 2 of 5 solutions, verify stream not exhausted
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");
        let f_sym = kb.intern("f");

        for i in 0..5 {
            let val = kb.alloc(Term::Const(Literal::Int(i)));
            let fact = kb.alloc(Term::Fn {
                functor: f_sym,
                pos_args: SmallVec::from_elem(val, 1),
                named_args: SmallVec::new(),
            });
            kb.assert_fact(fact, sort, domain, None);
        }

        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let goal = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let stream = kb.resolve_lazy(&[goal], &config);

        let (_, stream) = stream.split_first(&mut kb).expect("sol 1");
        let (_, stream) = stream.split_first(&mut kb).expect("sol 2");

        // Stream should still have more solutions
        assert!(!stream.is_empty());
    }

    #[test]
    fn search_stream_empty() {
        // No matches → None immediately
        let mut kb = KnowledgeBase::new();
        let g_sym = kb.intern("g");
        let val = kb.alloc(Term::Const(Literal::Int(1)));
        let goal = kb.alloc(Term::Fn {
            functor: g_sym,
            pos_args: SmallVec::from_elem(val, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let stream = kb.resolve_lazy(&[goal], &config);
        assert!(stream.split_first(&mut kb).is_none());
    }

    #[test]
    fn search_stream_delay_residual() {
        // nonvar(?x) alone → residualized solution via stream
        let mut kb = kb_with_builtins();
        let nonvar_sym = kb.resolve_symbol("anthill.reflect.nonvar");

        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let goal = kb.alloc(Term::Fn {
            functor: nonvar_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig::default();
        let stream = kb.resolve_lazy(&[goal], &config);

        let (sol, stream) = stream.split_first(&mut kb).expect("should residualize");
        assert_eq!(sol.residual.len(), 1);
        assert_eq!(sol.residual[0].expect_term(), goal);

        // No more solutions
        assert!(stream.split_first(&mut kb).is_none());
    }

    #[test]
    fn search_stream_recursive_rule() {
        // ancestor via stream, both solutions yielded one at a time
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Rule");
        let domain = kb.make_name_term("test");
        let parent_sym = kb.intern("parent");
        let ancestor_sym = kb.intern("ancestor");

        let alice = kb.alloc(Term::Const(Literal::String("alice".into())));
        let bob = kb.alloc(Term::Const(Literal::String("bob".into())));
        let charlie = kb.alloc(Term::Const(Literal::String("charlie".into())));

        // Facts
        let f1 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[alice, bob]),
            named_args: SmallVec::new(),
        });
        let f2 = kb.alloc(Term::Fn {
            functor: parent_sym,
            pos_args: SmallVec::from_slice(&[bob, charlie]),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f1, sort, domain, None);
        kb.assert_fact(f2, sort, domain, None);

        // Rule 1: ancestor(?x, ?y) :- parent(?x, ?y)
        {
            let x_sym = kb.intern("x");
            let y_sym = kb.intern("y");
            let vx = kb.fresh_var(x_sym);
            let vy = kb.fresh_var(y_sym);
            let var_x = kb.alloc(Term::Var(Var::Global(vx)));
            let var_y = kb.alloc(Term::Var(Var::Global(vy)));

            let head = kb.alloc(Term::Fn {
                functor: ancestor_sym,
                pos_args: SmallVec::from_slice(&[var_x, var_y]),
                named_args: SmallVec::new(),
            });
            let body = kb.alloc(Term::Fn {
                functor: parent_sym,
                pos_args: SmallVec::from_slice(&[var_x, var_y]),
                named_args: SmallVec::new(),
            });
            kb.assert_rule(head, vec![body], sort, domain, None);
        }

        // Rule 2: ancestor(?x, ?z) :- parent(?x, ?y), ancestor(?y, ?z)
        {
            let x_sym = kb.intern("x");
            let y_sym = kb.intern("y");
            let z_sym = kb.intern("z");
            let vx = kb.fresh_var(x_sym);
            let vy = kb.fresh_var(y_sym);
            let vz = kb.fresh_var(z_sym);
            let var_x = kb.alloc(Term::Var(Var::Global(vx)));
            let var_y = kb.alloc(Term::Var(Var::Global(vy)));
            let var_z = kb.alloc(Term::Var(Var::Global(vz)));

            let head = kb.alloc(Term::Fn {
                functor: ancestor_sym,
                pos_args: SmallVec::from_slice(&[var_x, var_z]),
                named_args: SmallVec::new(),
            });
            let b1 = kb.alloc(Term::Fn {
                functor: parent_sym,
                pos_args: SmallVec::from_slice(&[var_x, var_y]),
                named_args: SmallVec::new(),
            });
            let b2 = kb.alloc(Term::Fn {
                functor: ancestor_sym,
                pos_args: SmallVec::from_slice(&[var_y, var_z]),
                named_args: SmallVec::new(),
            });
            kb.assert_rule(head, vec![b1, b2], sort, domain, None);
        }

        // Query: ancestor("alice", ?w)
        let w_sym = kb.intern("w");
        let vw = kb.fresh_var(w_sym);
        let var_w = kb.alloc(Term::Var(Var::Global(vw)));
        let goal = kb.alloc(Term::Fn {
            functor: ancestor_sym,
            pos_args: SmallVec::from_slice(&[alice, var_w]),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { max_depth: 20, ..Default::default() };
        let stream = kb.resolve_lazy(&[goal], &config);

        let (sol1, stream) = stream.split_first(&mut kb).expect("first ancestor");
        let r1 = kb.reify(var_w, &sol1.subst).expect_term();

        let (sol2, stream) = stream.split_first(&mut kb).expect("second ancestor");
        let r2 = kb.reify(var_w, &sol2.subst).expect_term();

        // Should find bob and charlie (in some order)
        let mut results = vec![r1, r2];
        results.sort_by_key(|t| t.index());
        assert!(results.contains(&bob));
        assert!(results.contains(&charlie));

        // No more solutions
        assert!(stream.split_first(&mut kb).is_none());
    }

    // ── Symbol builtin tests ──────────────────────────────────────

    #[test]
    fn builtin_qualified_name_binds_result() {
        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        kb.register_standard_builtins();

        // Define a symbol "foo.Bar" via the symbol table
        let global = kb.make_name_term("_global");
        kb.symbols.define("Bar", "foo.Bar", crate::intern::SymbolKind::Sort, global.raw());

        // Look up the symbol and build: qualified_name(Ref(Bar), ?result)
        let bar_sym = *kb.symbols.by_qualified_name.get("foo.Bar").unwrap();
        let bar_ref = kb.alloc(Term::Ref(bar_sym));

        let result_sym = kb.intern("?result");
        let result_vid = kb.fresh_var(result_sym);
        let result_var = kb.alloc(Term::Var(Var::Global(result_vid)));

        let qn_sym = kb.resolve_symbol("anthill.reflect.qualified_name");
        let goal = kb.alloc(Term::Fn {
            functor: qn_sym,
            pos_args: SmallVec::from_slice(&[bar_ref, result_var]),
            named_args: SmallVec::new(),
        });

        // (No fact needed — builtins are dispatched directly by the resolver)

        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "qualified_name should produce 1 solution");
        let resolved = solutions[0].subst.resolve_as_value(result_vid).map(|v| v.expect_term()).expect("result should be bound");
        match kb.get_term(resolved) {
            Term::Const(Literal::String(s)) => assert_eq!(s, "foo.Bar"),
            other => panic!("expected String const 'foo.Bar', got {:?}", other),
        }
    }

    #[test]
    fn builtin_short_name_binds_result() {
        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        kb.register_standard_builtins();

        let global = kb.make_name_term("_global");
        kb.symbols.define("Baz", "alpha.beta.Baz", crate::intern::SymbolKind::Sort, global.raw());

        let baz_sym = *kb.symbols.by_qualified_name.get("alpha.beta.Baz").unwrap();
        let baz_ref = kb.alloc(Term::Ref(baz_sym));

        let result_sym = kb.intern("?result");
        let result_vid = kb.fresh_var(result_sym);
        let result_var = kb.alloc(Term::Var(Var::Global(result_vid)));

        let sn_sym = kb.resolve_symbol("anthill.reflect.short_name");
        let goal = kb.alloc(Term::Fn {
            functor: sn_sym,
            pos_args: SmallVec::from_slice(&[baz_ref, result_var]),
            named_args: SmallVec::new(),
        });

        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1);
        let resolved = solutions[0].subst.resolve_as_value(result_vid).map(|v| v.expect_term()).expect("result should be bound");
        match kb.get_term(resolved) {
            Term::Const(Literal::String(s)) => assert_eq!(s, "Baz"),
            other => panic!("expected String const 'Baz', got {:?}", other),
        }
    }

    #[test]
    fn builtin_lookup_symbol_finds_existing() {
        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        kb.register_standard_builtins();

        let global = kb.make_name_term("_global");
        kb.symbols.define("Qux", "ns.Qux", crate::intern::SymbolKind::Sort, global.raw());
        let qux_sym = *kb.symbols.by_qualified_name.get("ns.Qux").unwrap();

        let name_str = kb.alloc(Term::Const(Literal::String("ns.Qux".into())));

        let result_sym = kb.intern("?result");
        let result_vid = kb.fresh_var(result_sym);
        let result_var = kb.alloc(Term::Var(Var::Global(result_vid)));

        let ls_sym = kb.resolve_symbol("anthill.reflect.lookup_symbol");
        let goal = kb.alloc(Term::Fn {
            functor: ls_sym,
            pos_args: SmallVec::from_slice(&[name_str, result_var]),
            named_args: SmallVec::new(),
        });

        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1);
        let resolved = solutions[0].subst.resolve_as_value(result_vid).map(|v| v.expect_term()).expect("result should be bound");
        match kb.get_term(resolved) {
            Term::Ref(sym) => assert_eq!(*sym, qux_sym),
            other => panic!("expected Ref(Qux), got {:?}", other),
        }
    }

    #[test]
    fn builtin_lookup_symbol_fails_for_unknown() {
        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        kb.register_standard_builtins();

        let name_str = kb.alloc(Term::Const(Literal::String("does.not.Exist".into())));

        let result_sym = kb.intern("?result");
        let result_vid = kb.fresh_var(result_sym);
        let result_var = kb.alloc(Term::Var(Var::Global(result_vid)));

        let ls_sym = kb.resolve_symbol("anthill.reflect.lookup_symbol");
        let goal = kb.alloc(Term::Fn {
            functor: ls_sym,
            pos_args: SmallVec::from_slice(&[name_str, result_var]),
            named_args: SmallVec::new(),
        });

        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 0, "lookup_symbol for unknown name should fail");
    }

    #[test]
    fn builtin_qualified_name_delays_on_unbound() {
        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        kb.register_standard_builtins();

        let sym_name = kb.intern("?sym");
        let sym_vid = kb.fresh_var(sym_name);
        let sym_var = kb.alloc(Term::Var(Var::Global(sym_vid)));

        let result_name = kb.intern("?result");
        let result_vid = kb.fresh_var(result_name);
        let result_var = kb.alloc(Term::Var(Var::Global(result_vid)));

        let qn_sym = kb.resolve_symbol("anthill.reflect.qualified_name");
        let goal = kb.alloc(Term::Fn {
            functor: qn_sym,
            pos_args: SmallVec::from_slice(&[sym_var, result_var]),
            named_args: SmallVec::new(),
        });

        // With only one goal that delays, it should residualize
        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "should residualize");
        assert!(!solutions[0].residual.is_empty(), "should have residual goal");
    }

    // ── Arithmetic and comparison builtin tests ──────────────────

    #[test]
    fn builtin_eq_succeeds_on_equal_ints() {
        let mut kb = kb_with_builtins();
        let eq_sym = kb.resolve_symbol("anthill.prelude.PartialEq.eq");
        let a = kb.alloc(Term::Const(Literal::Int(42)));
        let b = kb.alloc(Term::Const(Literal::Int(42)));
        let goal = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[a, b]),
            named_args: SmallVec::new(),
        });
        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "eq(42, 42) should succeed");
    }

    #[test]
    fn builtin_eq_fails_on_different_ints() {
        let mut kb = kb_with_builtins();
        let eq_sym = kb.resolve_symbol("anthill.prelude.PartialEq.eq");
        let a = kb.alloc(Term::Const(Literal::Int(1)));
        let b = kb.alloc(Term::Const(Literal::Int(2)));
        let goal = kb.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[a, b]),
            named_args: SmallVec::new(),
        });
        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 0, "eq(1, 2) should fail");
    }

    #[test]
    fn builtin_neq_succeeds_on_different() {
        let mut kb = kb_with_builtins();
        let neq_sym = kb.resolve_symbol("anthill.prelude.PartialEq.neq");
        let a = kb.alloc(Term::Const(Literal::String("hello".into())));
        let b = kb.alloc(Term::Const(Literal::String("world".into())));
        let goal = kb.alloc(Term::Fn {
            functor: neq_sym,
            pos_args: SmallVec::from_slice(&[a, b]),
            named_args: SmallVec::new(),
        });
        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "neq(\"hello\", \"world\") should succeed");
    }

    #[test]
    fn builtin_gt_on_ints() {
        let mut kb = kb_with_builtins();
        let gt_sym = kb.resolve_symbol("anthill.prelude.PartialOrd.gt");
        let five = kb.alloc(Term::Const(Literal::Int(5)));
        let three = kb.alloc(Term::Const(Literal::Int(3)));

        // gt(5, 3) should succeed
        let goal = kb.alloc(Term::Fn {
            functor: gt_sym,
            pos_args: SmallVec::from_slice(&[five, three]),
            named_args: SmallVec::new(),
        });
        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "gt(5, 3) should succeed");

        // gt(3, 5) should fail
        let goal2 = kb.alloc(Term::Fn {
            functor: gt_sym,
            pos_args: SmallVec::from_slice(&[three, five]),
            named_args: SmallVec::new(),
        });
        let solutions2 = kb.resolve(&[goal2], &ResolveConfig::default());
        assert_eq!(solutions2.len(), 0, "gt(3, 5) should fail");
    }

    #[test]
    fn builtin_add_three_arg_binds_result() {
        let mut kb = kb_with_builtins();
        let add_sym = kb.resolve_symbol("anthill.prelude.Numeric.add");
        let three = kb.alloc(Term::Const(Literal::Int(3)));
        let four = kb.alloc(Term::Const(Literal::Int(4)));
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        // add(3, 4, ?x) → ?x = 7
        let goal = kb.alloc(Term::Fn {
            functor: add_sym,
            pos_args: SmallVec::from_slice(&[three, four, var_x]),
            named_args: SmallVec::new(),
        });
        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "add(3, 4, ?x) should have 1 solution");
        let result = kb.reify(var_x, &solutions[0].subst).expect_term();
        assert_eq!(kb.get_term(result), &Term::Const(Literal::Int(7)));
    }

    #[test]
    fn builtin_comparison_delays_on_unbound() {
        let mut kb = kb_with_builtins();
        let gt_sym = kb.resolve_symbol("anthill.prelude.PartialOrd.gt");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let three = kb.alloc(Term::Const(Literal::Int(3)));

        // gt(?x, 3) with unbound ?x → should delay/residualize
        let goal = kb.alloc(Term::Fn {
            functor: gt_sym,
            pos_args: SmallVec::from_slice(&[var_x, three]),
            named_args: SmallVec::new(),
        });
        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "should residualize");
        assert!(!solutions[0].residual.is_empty(), "gt(?x, 3) should be in residual");
    }

    // ── NAF (negation-as-failure) tests ──────────────────────────

    #[test]
    fn not_succeeds_when_goal_fails() {
        // not(p(a)) with no p(a) fact → succeeds
        let mut kb = kb_with_builtins();
        let not_sym = kb.resolve_symbol("anthill.reflect.not");
        let p_sym = kb.intern("p");
        let a = kb.alloc(Term::Const(Literal::String("a".into())));

        let p_a = kb.alloc(Term::Fn {
            functor: p_sym,
            pos_args: SmallVec::from_elem(a, 1),
            named_args: SmallVec::new(),
        });
        let goal = kb.alloc(Term::Fn {
            functor: not_sym,
            pos_args: SmallVec::from_elem(p_a, 1),
            named_args: SmallVec::new(),
        });

        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "not(p(a)) should succeed when p(a) is absent");
        assert!(solutions[0].residual.is_empty(), "should have no residual");
    }

    #[test]
    fn not_fails_when_goal_succeeds() {
        // not(p(a)) with p(a) fact → fails (no solutions)
        let mut kb = kb_with_builtins();
        let not_sym = kb.resolve_symbol("anthill.reflect.not");
        let p_sym = kb.intern("p");
        let a = kb.alloc(Term::Const(Literal::String("a".into())));

        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");

        // Assert p(a) as a fact
        let p_a_fact = kb.alloc(Term::Fn {
            functor: p_sym,
            pos_args: SmallVec::from_elem(a, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(p_a_fact, sort, domain, None);

        // Query: not(p(a))
        let p_a_query = kb.alloc(Term::Fn {
            functor: p_sym,
            pos_args: SmallVec::from_elem(a, 1),
            named_args: SmallVec::new(),
        });
        let goal = kb.alloc(Term::Fn {
            functor: not_sym,
            pos_args: SmallVec::from_elem(p_a_query, 1),
            named_args: SmallVec::new(),
        });

        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 0, "not(p(a)) should fail when p(a) exists");
    }

    #[test]
    fn not_delays_on_unbound_var() {
        // not(p(?x)) with ?x unbound → residualizes
        let mut kb = kb_with_builtins();
        let not_sym = kb.resolve_symbol("anthill.reflect.not");
        let p_sym = kb.intern("p");
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let p_x = kb.alloc(Term::Fn {
            functor: p_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let goal = kb.alloc(Term::Fn {
            functor: not_sym,
            pos_args: SmallVec::from_elem(p_x, 1),
            named_args: SmallVec::new(),
        });

        let solutions = kb.resolve(&[goal], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "should residualize");
        assert!(!solutions[0].residual.is_empty(), "should have residual not(p(?x))");
    }

    #[test]
    fn not_succeeds_after_delay_reorder() {
        // Goals: [not(p(?x)), f(?x)] where f(a) exists and p(a) does not.
        // not(p(?x)) delays initially, f(?x) binds ?x=a, then not(p(a)) succeeds.
        let mut kb = kb_with_builtins();
        let not_sym = kb.resolve_symbol("anthill.reflect.not");
        let p_sym = kb.intern("p");
        let f_sym = kb.intern("f");
        let a = kb.alloc(Term::Const(Literal::String("a".into())));

        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");

        // Assert f(a)
        let f_a = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(a, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f_a, sort, domain, None);

        // Build goals
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let p_x = kb.alloc(Term::Fn {
            functor: p_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let not_p_x = kb.alloc(Term::Fn {
            functor: not_sym,
            pos_args: SmallVec::from_elem(p_x, 1),
            named_args: SmallVec::new(),
        });

        let f_x = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let solutions = kb.resolve(&[not_p_x, f_x], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "should have one solution");
        assert!(solutions[0].residual.is_empty(), "no residual expected");
        // ?x should be bound to a
        let bound = solutions[0].subst.resolve_as_value(vx).map(|v| v.expect_term());
        assert!(bound.is_some(), "?x should be bound");
    }

    // ── WI-629: NAF verdict honesty over carrier-neutral (Value-carried) goals ──

    #[test]
    fn wi629_value_entity_inner_delays_and_rotates() {
        // WI-629 gap (1)+(2): `[not(not(p(?x))), f(?x)]` with facts p(a), f(a).
        // The inner `not(p(?x))` is a `Value::Entity` (the `make_goal_value` shape
        // `lower_query` synthesizes for a `not` wrapper). Pre-fix `value_is_ground`
        // had no `Value::Entity` arm → read the non-ground inner as GROUND, so the
        // outer NAF neither delayed nor rotated: it sub-resolved `not(p(?x))` NOW
        // (floundered on the unbound `?x`) and yielded `residual:[not(not(p(?x)))]`,
        // SILENTLY DROPPING the tail `f(?x)` — a floundered, `?x`-unbound answer.
        // With deep groundness + carry-or-rotate: the outer delays-and-rotates,
        // `f(?x)` binds `?x = a`, then `not(not(p(a)))` decides DEFINITELY (p(a)
        // holds ⇒ not(p(a)) fails ⇒ not(not(p(a))) succeeds).
        let mut kb = kb_with_builtins();
        let not_sym = kb.resolve_symbol("anthill.reflect.not");
        let p_sym = kb.intern("p");
        let f_sym = kb.intern("f");
        let a = kb.alloc(Term::Const(Literal::String("a".into())));
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");

        // Facts p(a), f(a).
        let p_a = kb.alloc(Term::Fn {
            functor: p_sym,
            pos_args: SmallVec::from_elem(a, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(p_a, sort, domain, None);
        let f_a = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(a, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(f_a, sort, domain, None);

        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let p_x = kb.alloc(Term::Fn {
            functor: p_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        // Nested `not` wrappers as carrier-neutral `Value::Entity` goals.
        let inner_not = kb.make_goal_value(not_sym, vec![Value::term(p_x)]);
        let outer_not = kb.make_goal_value(not_sym, vec![inner_not]);
        let f_x = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let solutions =
            kb.resolve_goals(vec![outer_not, Value::term(f_x)], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "exactly one solution");
        assert!(
            solutions[0].residual.is_empty(),
            "DEFINITE (empty residual): the outer NAF must delay-and-rotate so \
             f(?x) binds ?x=a and not(not(p(a))) decides — not flounder with the \
             tail dropped. residual was: {:?}",
            solutions[0].residual
        );
        let bound = kb.reify(var_x, &solutions[0].subst).expect_term();
        assert_eq!(bound, a, "?x must be bound to a (f(?x) was attempted, not dropped)");
    }

    #[test]
    fn wi629_floundered_inner_does_not_drop_tail() {
        // WI-629 gap (2), isolated: a GROUND inner whose sub-resolution FLOUNDERS,
        // with a tail goal that must still be attempted. `r()` is ground and
        // flounders (its body `nonvar(?w)` delays forever on the body-local `?w`),
        // so `not(r())` reaches step_naf's ground/inner-floundered arm. The tail
        // `s(a)` FAILS (only `s(b)` is a fact). Pre-fix the floundered arm popped
        // and yielded `residual:[not(r())]`, silently dropping `s(a)` → 1 spurious
        // (floundered) answer. Carry-or-rotate makes it rotate the undecided
        // not(r()) behind the tail, so `s(a)` is attempted, fails, and the whole
        // conjunction correctly has NO solution.
        let mut kb = kb_with_builtins();
        let not_sym = kb.resolve_symbol("anthill.reflect.not");
        let nonvar_sym = kb.resolve_symbol("anthill.reflect.nonvar");
        let r_sym = kb.intern("r");
        let s_sym = kb.intern("s");
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");

        // Rule r() :- nonvar(?w).  (?w is body-local ⇒ r() is ground but flounders)
        let r_head = kb.alloc(Term::Fn {
            functor: r_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let w_sym = kb.intern("w");
        let vw = kb.fresh_var(w_sym);
        let var_w = kb.alloc(Term::Var(Var::Global(vw)));
        let r_body = kb.alloc(Term::Fn {
            functor: nonvar_sym,
            pos_args: SmallVec::from_elem(var_w, 1),
            named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[r_body]);
        kb.assert_rule_debruijn_with_nodes(r_head, body_nodes, sort, domain, None);

        // Fact s(b); the tail goal s(a) has no match ⇒ fails.
        let b = kb.alloc(Term::Const(Literal::String("b".into())));
        let a = kb.alloc(Term::Const(Literal::String("a".into())));
        let s_b = kb.alloc(Term::Fn {
            functor: s_sym,
            pos_args: SmallVec::from_elem(b, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(s_b, sort, domain, None);

        let r_call = kb.alloc(Term::Fn {
            functor: r_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let not_r = kb.make_goal_value(not_sym, vec![Value::term(r_call)]);
        let s_a = kb.alloc(Term::Fn {
            functor: s_sym,
            pos_args: SmallVec::from_elem(a, 1),
            named_args: SmallVec::new(),
        });

        let solutions =
            kb.resolve_goals(vec![not_r, Value::term(s_a)], &ResolveConfig::default());
        assert_eq!(
            solutions.len(),
            0,
            "no solution: the floundered not(r()) must NOT drop the failing tail \
             s(a); got solutions with residuals: {:?}",
            solutions.iter().map(|s| &s.residual).collect::<Vec<_>>()
        );
    }

    #[test]
    fn wi629_value_entity_ground_inner_still_decides() {
        // WI-629 guard: the deep-groundness fix must NOT over-delay a GROUND
        // `Value::Entity` inner. `not(not(p(a)))` — inner `not(p(a))` is a
        // `Value::Entity` whose only child is the ground `p(a)`. It must still be
        // read as ground and DECIDE: p(a) holds ⇒ not(p(a)) fails ⇒ not(not(p(a)))
        // succeeds, a single definite solution.
        let mut kb = kb_with_builtins();
        let not_sym = kb.resolve_symbol("anthill.reflect.not");
        let p_sym = kb.intern("p");
        let a = kb.alloc(Term::Const(Literal::String("a".into())));
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");

        let p_a_fact = kb.alloc(Term::Fn {
            functor: p_sym,
            pos_args: SmallVec::from_elem(a, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(p_a_fact, sort, domain, None);

        let p_a = kb.alloc(Term::Fn {
            functor: p_sym,
            pos_args: SmallVec::from_elem(a, 1),
            named_args: SmallVec::new(),
        });
        let inner_not = kb.make_goal_value(not_sym, vec![Value::term(p_a)]);
        let outer_not = kb.make_goal_value(not_sym, vec![inner_not]);

        let solutions = kb.resolve_goals(vec![outer_not], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "not(not(p(a))) succeeds (one solution)");
        assert!(
            solutions[0].residual.is_empty(),
            "a ground Value::Entity inner must DECIDE, not flounder; residual: {:?}",
            solutions[0].residual
        );
    }

    #[test]
    fn wi629_two_ground_floundering_nots_residualize_not_spin() {
        // WI-629 rotation TERMINATION: `[not(r()), not(u())]` where BOTH r() and
        // u() are ground yet flounder (bodies `nonvar(?w)` delay forever on a
        // body-local var). Each `not()` reaches the ground/inner-floundered arm and
        // rotates behind the other. The rotation counter MUST thread the incoming
        // delay_mode (1, then 2) so the `consecutive_delays >= goals.len()` gate in
        // step_init fires after both have rotated once — yielding ONE honest
        // floundered residual `[not(r()), not(u())]`. A hard-coded `consecutive_delays:
        // 1` pins the counter, so neither `>= 2`: the pair rotates until the depth
        // limit and returns ZERO solutions (verdict-dishonest — an UNDECIDED
        // conjunction read as refuted).
        let mut kb = kb_with_builtins();
        let not_sym = kb.resolve_symbol("anthill.reflect.not");
        let nonvar_sym = kb.resolve_symbol("anthill.reflect.nonvar");
        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");

        // Two ground-but-floundering nullary rules `r() :- nonvar(?w)`, `u() :- nonvar(?w2)`.
        let mut make_floundering_rule = |kb: &mut KnowledgeBase, name: &str, var: &str| -> Symbol {
            let sym = kb.intern(name);
            let head = kb.alloc(Term::Fn {
                functor: sym,
                pos_args: SmallVec::new(),
                named_args: SmallVec::new(),
            });
            let vsym = kb.intern(var);
            let vv = kb.fresh_var(vsym);
            let var_t = kb.alloc(Term::Var(Var::Global(vv)));
            let body = kb.alloc(Term::Fn {
                functor: nonvar_sym,
                pos_args: SmallVec::from_elem(var_t, 1),
                named_args: SmallVec::new(),
            });
            let body_nodes = kb.term_body_to_nodes(&[body]);
            kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);
            sym
        };
        let r_sym = make_floundering_rule(&mut kb, "r", "w");
        let u_sym = make_floundering_rule(&mut kb, "u", "w2");

        let r_call = kb.alloc(Term::Fn {
            functor: r_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let u_call = kb.alloc(Term::Fn {
            functor: u_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let not_r = kb.make_goal_value(not_sym, vec![Value::term(r_call)]);
        let not_u = kb.make_goal_value(not_sym, vec![Value::term(u_call)]);

        let solutions =
            kb.resolve_goals(vec![not_r, not_u], &ResolveConfig::default());
        assert_eq!(
            solutions.len(),
            1,
            "two ground-floundering not()s must residualize (one floundered \
             solution), not spin to the depth limit and vanish"
        );
        assert_eq!(
            solutions[0].residual.len(),
            2,
            "the honest residual carries BOTH undischarged not() goals, not one; \
             residual: {:?}",
            solutions[0].residual
        );
    }

    #[test]
    fn not_respects_depth_limit() {
        // Recursive rule inside not() must TERMINATE via the depth limit — and,
        // per WI-628, the resulting empty search is UNDECIDED, not a refutation.
        // r(x) :- r(x)  (non-terminating). Query: not(r(a)). The sub-resolution
        // for r(a) hits the depth limit (TRUNCATES) and finds no solution; a
        // truncated search proves nothing, so `not(r(a))` must NOT succeed
        // definitely — it residualizes as undecided. (Before WI-628 this test
        // asserted a DEFINITE success, i.e. the very decide-from-incomplete-search
        // bug: it read the truncated empty stream as "r(a) is refuted".)
        let mut kb = kb_with_builtins();
        let not_sym = kb.resolve_symbol("anthill.reflect.not");
        let r_sym = kb.intern("r");
        let a = kb.alloc(Term::Const(Literal::String("a".into())));

        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");

        // Assert recursive rule: r(?y) :- r(?y)
        let y_sym = kb.intern("y");
        let vy = kb.fresh_var(y_sym);
        let var_y = kb.alloc(Term::Var(Var::Global(vy)));
        let r_y_head = kb.alloc(Term::Fn {
            functor: r_sym,
            pos_args: SmallVec::from_elem(var_y, 1),
            named_args: SmallVec::new(),
        });
        let r_y_body = kb.alloc(Term::Fn {
            functor: r_sym,
            pos_args: SmallVec::from_elem(var_y, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(r_y_head, vec![r_y_body], sort, domain, None);

        // Query: not(r(a))
        let r_a = kb.alloc(Term::Fn {
            functor: r_sym,
            pos_args: SmallVec::from_elem(a, 1),
            named_args: SmallVec::new(),
        });
        let goal = kb.alloc(Term::Fn {
            functor: not_sym,
            pos_args: SmallVec::from_elem(r_a, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { max_depth: 20, ..ResolveConfig::default() };
        let solutions = kb.resolve(&[goal], &config);
        // Terminates (no hang) AND stays honest: no DEFINITE (empty-residual)
        // solution — the truncated inner search leaves `not(r(a))` undecided
        // (WI-628). The honest answer is exactly one residual `[not(r(a))]`, not
        // the verdict dropped (0 solutions), which the negative check alone would
        // pass vacuously.
        assert!(
            !solutions.iter().any(|s| s.residual.is_empty()),
            "not(r(a)) must not decide from a truncated search — no definite \
             solution allowed; got {} solution(s), {} definite",
            solutions.len(),
            solutions.iter().filter(|s| s.residual.is_empty()).count()
        );
        assert_eq!(solutions.len(), 1, "expected exactly one (residual) solution for not(r(a))");
        assert_eq!(
            solutions[0].residual.len(),
            1,
            "the undecided answer must carry the single undischarged not(r(a)) as residual"
        );
    }

    #[test]
    fn not_in_rule_body() {
        // safe(?x) :- thing(?x), not(dangerous(?x))
        // Facts: thing(a), thing(b), dangerous(b)
        // Expected: only ?x=a
        let mut kb = kb_with_builtins();
        let not_sym = kb.resolve_symbol("anthill.reflect.not");
        let thing_sym = kb.intern("thing");
        let dangerous_sym = kb.intern("dangerous");
        let safe_sym = kb.intern("safe");
        let a = kb.alloc(Term::Const(Literal::String("a".into())));
        let b = kb.alloc(Term::Const(Literal::String("b".into())));

        let sort = kb.make_name_term("Fact");
        let domain = kb.make_name_term("test");

        // Assert facts
        let thing_a = kb.alloc(Term::Fn {
            functor: thing_sym,
            pos_args: SmallVec::from_elem(a, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(thing_a, sort, domain, None);

        let thing_b = kb.alloc(Term::Fn {
            functor: thing_sym,
            pos_args: SmallVec::from_elem(b, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(thing_b, sort, domain, None);

        let dangerous_b = kb.alloc(Term::Fn {
            functor: dangerous_sym,
            pos_args: SmallVec::from_elem(b, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(dangerous_b, sort, domain, None);

        // Assert rule: safe(?x) :- thing(?x), not(dangerous(?x))
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));

        let safe_x = kb.alloc(Term::Fn {
            functor: safe_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let thing_x = kb.alloc(Term::Fn {
            functor: thing_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let dangerous_x = kb.alloc(Term::Fn {
            functor: dangerous_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let not_dangerous_x = kb.alloc(Term::Fn {
            functor: not_sym,
            pos_args: SmallVec::from_elem(dangerous_x, 1),
            named_args: SmallVec::new(),
        });

        kb.assert_rule(safe_x, vec![thing_x, not_dangerous_x], sort, domain, None);

        // Query: safe(?q)
        let q_sym = kb.intern("q");
        let vq = kb.fresh_var(q_sym);
        let var_q = kb.alloc(Term::Var(Var::Global(vq)));
        let safe_q = kb.alloc(Term::Fn {
            functor: safe_sym,
            pos_args: SmallVec::from_elem(var_q, 1),
            named_args: SmallVec::new(),
        });

        let solutions = kb.resolve(&[safe_q], &ResolveConfig::default());
        assert_eq!(solutions.len(), 1, "should have exactly one solution (safe(a))");
        assert!(solutions[0].residual.is_empty(), "no residual expected");
        // Reify to follow the full binding chain through fresh vars
        let resolved = kb.reify(var_q, &solutions[0].subst).expect_term();
        assert_eq!(resolved, a, "?q should resolve to 'a'");
    }

    /// Regression test for GitHub issue #1:
    /// with_fresh_vars must rename variables inside structured answer_links terms.
    ///
    /// Peano naturals: nat(zero()), nat(succ(?n)) :- nat(?n)
    /// Query: nat(?x) should yield zero(), succ(zero()), succ(succ(zero())), ...
    #[test]
    fn search_stream_infinite_rule() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Sort");
        let domain = kb.make_name_term("test");

        let nat_sym = kb.intern("nat");
        let zero_sym = kb.intern("zero");
        let succ_sym = kb.intern("succ");

        // fact: nat(zero())
        let zero_term = kb.alloc(Term::Fn {
            functor: zero_sym,
            pos_args: SmallVec::new(),
            named_args: SmallVec::new(),
        });
        let nat_zero = kb.alloc(Term::Fn {
            functor: nat_sym,
            pos_args: SmallVec::from_elem(zero_term, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(nat_zero, sort, domain, None);

        // rule: nat(succ(?n)) :- nat(?n)
        let n_sym = kb.intern("n");
        let vn = kb.fresh_var(n_sym);
        let var_n = kb.alloc(Term::Var(Var::Global(vn)));
        let succ_n = kb.alloc(Term::Fn {
            functor: succ_sym,
            pos_args: SmallVec::from_elem(var_n, 1),
            named_args: SmallVec::new(),
        });
        let nat_succ_n = kb.alloc(Term::Fn {
            functor: nat_sym,
            pos_args: SmallVec::from_elem(succ_n, 1),
            named_args: SmallVec::new(),
        });
        let body_nat_n = kb.alloc(Term::Fn {
            functor: nat_sym,
            pos_args: SmallVec::from_elem(var_n, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_rule(nat_succ_n, vec![body_nat_n], sort, domain, None);

        // query: nat(?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let query = kb.alloc(Term::Fn {
            functor: nat_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { max_depth: 20, max_solutions: 4, simplify: false, definite_only: false, ..Default::default() };
        let solutions = kb.resolve(&[query], &config);

        assert_eq!(solutions.len(), 4, "should get 4 solutions");

        // Solution 0: nat(zero()) → ?x = zero()
        let r0 = kb.reify(var_x, &solutions[0].subst).expect_term();
        assert_eq!(r0, zero_term, "first solution should be zero()");

        // Solution 1: nat(succ(zero())) → ?x = succ(zero())
        let r1 = kb.reify(var_x, &solutions[1].subst).expect_term();
        match kb.get_term(r1) {
            Term::Fn { functor, pos_args, .. } => {
                assert_eq!(*functor, succ_sym);
                assert_eq!(pos_args.len(), 1);
                assert_eq!(pos_args[0], zero_term, "succ arg should be zero()");
            }
            other => panic!("expected succ(zero()), got {:?}", other),
        }

        // Solution 2: nat(succ(succ(zero()))) → ?x = succ(succ(zero()))
        let r2 = kb.reify(var_x, &solutions[2].subst).expect_term();
        match kb.get_term(r2) {
            Term::Fn { functor, pos_args, .. } => {
                assert_eq!(*functor, succ_sym);
                match kb.get_term(pos_args[0]) {
                    Term::Fn { functor: f2, pos_args: p2, .. } => {
                        assert_eq!(*f2, succ_sym);
                        assert_eq!(p2[0], zero_term, "inner succ arg should be zero()");
                    }
                    other => panic!("expected succ(zero()), got {:?}", other),
                }
            }
            other => panic!("expected succ(succ(zero())), got {:?}", other),
        }
    }

    /// Regression: de Bruijn body substitution with multi-occurrence variable.
    ///
    /// Rule: shared(?x) :- check_a(?x), check_b(?x)
    /// Facts: check_a("yes"), check_a("no"), check_b("yes")
    ///
    /// Query shared("yes") → 1 solution (both body goals match "yes")
    /// Query shared("no")  → 0 solutions (check_b("no") doesn't exist)
    /// Query shared(?q)    → 1 solution (?q = "yes")
    ///
    /// Without body_concrete substitution, shared("no") would wrongly succeed:
    /// the fresh var acts as wildcard in check_a, matches "yes", then check_b("yes")
    /// succeeds — a false positive.
    #[test]
    fn debruijn_multi_occurrence_concrete_query() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Sort");
        let domain = kb.make_name_term("test");

        let shared_sym = kb.intern("shared");
        let check_a_sym = kb.intern("check_a");
        let check_b_sym = kb.intern("check_b");

        // Facts
        let yes = kb.alloc(Term::Const(Literal::String("yes".into())));
        let no = kb.alloc(Term::Const(Literal::String("no".into())));

        let ca_yes = kb.alloc(Term::Fn {
            functor: check_a_sym,
            pos_args: SmallVec::from_elem(yes, 1),
            named_args: SmallVec::new(),
        });
        let ca_no = kb.alloc(Term::Fn {
            functor: check_a_sym,
            pos_args: SmallVec::from_elem(no, 1),
            named_args: SmallVec::new(),
        });
        let cb_yes = kb.alloc(Term::Fn {
            functor: check_b_sym,
            pos_args: SmallVec::from_elem(yes, 1),
            named_args: SmallVec::new(),
        });
        kb.assert_fact(ca_yes, sort, domain, None);
        kb.assert_fact(ca_no, sort, domain, None);
        kb.assert_fact(cb_yes, sort, domain, None);

        // Rule: shared(?x) :- check_a(?x), check_b(?x)
        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let head = kb.alloc(Term::Fn {
            functor: shared_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let body_a = kb.alloc(Term::Fn {
            functor: check_a_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let body_b = kb.alloc(Term::Fn {
            functor: check_b_sym,
            pos_args: SmallVec::from_elem(var_x, 1),
            named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[body_a, body_b]);
        kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);

        let config = ResolveConfig::default();

        // Query 1: shared("yes") → should succeed
        let q_yes = kb.alloc(Term::Fn {
            functor: shared_sym,
            pos_args: SmallVec::from_elem(yes, 1),
            named_args: SmallVec::new(),
        });
        let sols = kb.resolve(&[q_yes], &config);
        assert_eq!(sols.len(), 1, "shared(\"yes\") should have 1 solution");

        // Query 2: shared("no") → should fail (check_b("no") doesn't exist)
        let q_no = kb.alloc(Term::Fn {
            functor: shared_sym,
            pos_args: SmallVec::from_elem(no, 1),
            named_args: SmallVec::new(),
        });
        let sols = kb.resolve(&[q_no], &config);
        assert_eq!(sols.len(), 0, "shared(\"no\") should have 0 solutions");

        // Query 3: shared(?q) → should yield 1 solution: ?q = "yes"
        let q_sym = kb.intern("q");
        let vq = kb.fresh_var(q_sym);
        let var_q = kb.alloc(Term::Var(Var::Global(vq)));
        let q_var = kb.alloc(Term::Fn {
            functor: shared_sym,
            pos_args: SmallVec::from_elem(var_q, 1),
            named_args: SmallVec::new(),
        });
        let sols = kb.resolve(&[q_var], &config);
        assert_eq!(sols.len(), 1, "shared(?q) should have 1 solution");
        let bound = kb.reify(var_q, &sols[0].subst).expect_term();
        assert_eq!(bound, yes, "?q should resolve to \"yes\"");
    }

    #[test]
    fn nested_var_goal_binds_against_ground_fact() {
        // WI-373 gap 3 (end-to-end): a goal with a variable at a NESTED position
        // must bind against a ground fact. Fact holds(state(active)); query
        // holds(state(?x)); expect ?x = active. Before the nested binding-
        // extraction the fact was found but ?x stayed unbound (silent wrong answer).
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Sort");
        let domain = kb.make_name_term("test");
        let holds = kb.intern("holds");
        let state = kb.intern("state");
        let active = kb.alloc(Term::Const(Literal::String("active".into())));
        let state_active = kb.alloc(Term::Fn {
            functor: state, pos_args: SmallVec::from_elem(active, 1), named_args: SmallVec::new(),
        });
        let fact = kb.alloc(Term::Fn {
            functor: holds, pos_args: SmallVec::from_elem(state_active, 1), named_args: SmallVec::new(),
        });
        kb.assert_fact(fact, sort, domain, None);

        let x_sym = kb.intern("x");
        let vx = kb.fresh_var(x_sym);
        let var_x = kb.alloc(Term::Var(Var::Global(vx)));
        let state_x = kb.alloc(Term::Fn {
            functor: state, pos_args: SmallVec::from_elem(var_x, 1), named_args: SmallVec::new(),
        });
        let query = kb.alloc(Term::Fn {
            functor: holds, pos_args: SmallVec::from_elem(state_x, 1), named_args: SmallVec::new(),
        });
        let config = ResolveConfig::default();
        let sols = kb.resolve(&[query], &config);
        assert_eq!(sols.len(), 1, "holds(state(?x)) should find the fact");
        let bound = kb.reify(var_x, &sols[0].subst).expect_term();
        assert_eq!(bound, active, "nested ?x must bind to active, got {:?}", bound);
    }

    /// Multiple anonymous variables get distinct DeBruijn indices.
    ///
    /// Rule: pair(?) :- left(?), right(?)
    /// Each ? is independent. With facts left("a"), left("b"), right("x"),
    /// right("y"), query pair(?) should yield 4 solutions (2×2 cross product),
    /// NOT 2 (which would happen if all ? shared an index).
    #[test]
    fn debruijn_multiple_anonymous_vars_independent() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Sort");
        let domain = kb.make_name_term("test");

        let pair_sym = kb.intern("pair");
        let left_sym = kb.intern("left");
        let right_sym = kb.intern("right");

        // Three anonymous variables — each gets a fresh VarId
        let anon = |kb: &mut KnowledgeBase| {
            let sym = kb.intern("_");
            let vid = kb.fresh_var(sym);
            kb.alloc(Term::Var(Var::Global(vid)))
        };

        let v1 = anon(&mut kb);
        let v2 = anon(&mut kb);
        let v3 = anon(&mut kb);

        // Rule: pair(?) :- left(?), right(?)
        let head = kb.alloc(Term::Fn {
            functor: pair_sym,
            pos_args: SmallVec::from_elem(v1, 1),
            named_args: SmallVec::new(),
        });
        let body_l = kb.alloc(Term::Fn {
            functor: left_sym,
            pos_args: SmallVec::from_elem(v2, 1),
            named_args: SmallVec::new(),
        });
        let body_r = kb.alloc(Term::Fn {
            functor: right_sym,
            pos_args: SmallVec::from_elem(v3, 1),
            named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[body_l, body_r]);
        kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);

        // Facts
        for val in &["a", "b"] {
            let v = kb.alloc(Term::Const(Literal::String(val.to_string())));
            let fact = kb.alloc(Term::Fn {
                functor: left_sym,
                pos_args: SmallVec::from_elem(v, 1),
                named_args: SmallVec::new(),
            });
            kb.assert_fact(fact, sort, domain, None);
        }
        for val in &["x", "y"] {
            let v = kb.alloc(Term::Const(Literal::String(val.to_string())));
            let fact = kb.alloc(Term::Fn {
                functor: right_sym,
                pos_args: SmallVec::from_elem(v, 1),
                named_args: SmallVec::new(),
            });
            kb.assert_fact(fact, sort, domain, None);
        }

        // Query: pair(?q)
        let q_sym = kb.intern("q");
        let vq = kb.fresh_var(q_sym);
        let var_q = kb.alloc(Term::Var(Var::Global(vq)));
        let query = kb.alloc(Term::Fn {
            functor: pair_sym,
            pos_args: SmallVec::from_elem(var_q, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { max_solutions: 10, ..ResolveConfig::default() };
        let solutions = kb.resolve(&[query], &config);
        // 3 independent anonymous vars → left has 2 facts, right has 2 facts
        // head ? is independent from body, so pair(?) matches any.
        // Body: left(?) × right(?) = 2 × 2 = 4 solutions.
        assert_eq!(solutions.len(), 4,
            "3 independent anonymous vars should yield 2×2=4 solutions, got {}",
            solutions.len());
    }

    /// Stress test: rule with N=1000 head args and N body goals.
    ///
    /// Validates DeBruijn opening + body_rename correctness at scale.
    /// The answer_links optimization (not leaking synthetic entries)
    /// prevents an O(n²) bind_compressed scan; the remaining O(n²) is
    /// inherent SLD (apply_subst_each on remaining goals after each match).
    ///
    /// Uses a spawned thread with large stack because the discrim tree
    /// query recurses once per positional arg.
    #[test]
    fn debruijn_large_head_and_body() {
        let result = std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let n: usize = 1000;

                let mut kb = KnowledgeBase::new();
                let sort = kb.make_name_term("Sort");
                let domain = kb.make_name_term("test");

                let big_sym = kb.intern("big");

                let f_syms: Vec<Symbol> = (0..n)
                    .map(|i| kb.intern(&format!("f_{i}")))
                    .collect();
                let vals: Vec<TermId> = (0..n)
                    .map(|i| kb.alloc(Term::Const(Literal::String(format!("v{i}")))))
                    .collect();
                let var_terms: Vec<TermId> = (0..n).map(|i| {
                    let sym = kb.intern(&format!("x{i}"));
                    let vid = kb.fresh_var(sym);
                    kb.alloc(Term::Var(Var::Global(vid)))
                }).collect();

                // Rule head: big(?v0, ..., ?v999)
                let head = kb.alloc(Term::Fn {
                    functor: big_sym,
                    pos_args: SmallVec::from_vec(var_terms.clone()),
                    named_args: SmallVec::new(),
                });

                // Body: f_i(?v_i) for each i
                let body: Vec<TermId> = (0..n).map(|i| {
                    kb.alloc(Term::Fn {
                        functor: f_syms[i],
                        pos_args: SmallVec::from_elem(var_terms[i], 1),
                        named_args: SmallVec::new(),
                    })
                }).collect();

                let body_nodes = kb.term_body_to_nodes(&body);
                kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);

                // Facts: f_i("val_i")
                for i in 0..n {
                    let fact = kb.alloc(Term::Fn {
                        functor: f_syms[i],
                        pos_args: SmallVec::from_elem(vals[i], 1),
                        named_args: SmallVec::new(),
                    });
                    kb.assert_fact(fact, sort, domain, None);
                }

                // Query: big("v0", ..., "v999") — all concrete
                let query = kb.alloc(Term::Fn {
                    functor: big_sym,
                    pos_args: SmallVec::from_vec(vals.clone()),
                    named_args: SmallVec::new(),
                });

                let config = ResolveConfig {
                    max_depth: usize::MAX,
                    max_solutions: 1,
                    simplify: false,
                    definite_only: false,
                    ..Default::default()
                };

                let start = std::time::Instant::now();
                let solutions = kb.resolve(&[query], &config);
                let elapsed = start.elapsed();

                assert_eq!(solutions.len(), 1, "should find exactly 1 solution");
                eprintln!("  1000-head-arg rule resolved in {}ms", elapsed.as_millis());

                // Debug build: ~800ms (dominated by SLD O(n²) apply_subst_each).
                // If DeBruijn adds extra O(n²), would exceed 5s.
                assert!(
                    elapsed.as_millis() < 5000,
                    "1000-head-arg rule took {}ms",
                    elapsed.as_millis()
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Build the same n-head/n-body fixture as `debruijn_large_head_and_body`
    /// but parametric in `n`. Returns `(kb, query)`.
    fn build_n_body_fixture(n: usize) -> (KnowledgeBase, TermId) {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Sort");
        let domain = kb.make_name_term("test");
        let big_sym = kb.intern("big");

        let f_syms: Vec<Symbol> = (0..n)
            .map(|i| kb.intern(&format!("f_{i}")))
            .collect();
        let vals: Vec<TermId> = (0..n)
            .map(|i| kb.alloc(Term::Const(Literal::String(format!("v{i}")))))
            .collect();
        let var_terms: Vec<TermId> = (0..n)
            .map(|i| {
                let sym = kb.intern(&format!("x{i}"));
                let vid = kb.fresh_var(sym);
                kb.alloc(Term::Var(Var::Global(vid)))
            })
            .collect();

        let head = kb.alloc(Term::Fn {
            functor: big_sym,
            pos_args: SmallVec::from_vec(var_terms.clone()),
            named_args: SmallVec::new(),
        });
        let body: Vec<TermId> = (0..n)
            .map(|i| {
                kb.alloc(Term::Fn {
                    functor: f_syms[i],
                    pos_args: SmallVec::from_elem(var_terms[i], 1),
                    named_args: SmallVec::new(),
                })
            })
            .collect();
        let body_nodes = kb.term_body_to_nodes(&body);
        kb.assert_rule_debruijn_with_nodes(head, body_nodes, sort, domain, None);

        for i in 0..n {
            let fact = kb.alloc(Term::Fn {
                functor: f_syms[i],
                pos_args: SmallVec::from_elem(vals[i], 1),
                named_args: SmallVec::new(),
            });
            kb.assert_fact(fact, sort, domain, None);
        }

        let query = kb.alloc(Term::Fn {
            functor: big_sym,
            pos_args: SmallVec::from_vec(vals.clone()),
            named_args: SmallVec::new(),
        });
        (kb, query)
    }

    /// Smoke test: confirms `ResolveStats` is wired and reports non-zero
    /// counters for the n-body workload. Always runs; intended as a
    /// telemetry sanity check, not a regression bound.
    #[test]
    fn resolve_stats_populated_on_n_body_query() {
        let (mut kb, query) = build_n_body_fixture(50);
        let config = ResolveConfig {
            max_depth: usize::MAX,
            max_solutions: 1,
            simplify: false,
            definite_only: false,
                    ..Default::default()
        };
        let (sols, stats) = kb.resolve_with_stats(&[query], &config);
        assert_eq!(sols.len(), 1);
        eprintln!(
            "  n=50: steps={} lazy_walk_calls={}",
            stats.steps, stats.lazy_walk_calls,
        );
        assert!(stats.steps > 0, "step counter must increment");
        assert!(
            stats.lazy_walk_calls > 0,
            "lazy_walk counter must increment whenever step_init selects a goal",
        );
    }

    /// **WI-030 acceptance test.** Drives the n-body fixture at two sizes
    /// and asserts that `lazy_walk_calls` grows roughly *linearly* with
    /// `n` — once the eager `apply_subst_each` walks were dropped, the
    /// remaining work is one walk per goal selection. Pre-WI-030 the
    /// equivalent metric (`apply_subst_each_goals`) scaled ~n²/2.
    #[test]
    fn wi030_apply_subst_should_be_linear() {
        // Discrim-tree query recurses once per positional arg, so n=400
        // overflows the default test stack — same workaround the
        // `debruijn_large_head_and_body` benchmark uses.
        std::thread::Builder::new()
            .stack_size(64 * 1024 * 1024)
            .spawn(|| {
                let small = 100usize;
                let large = 400usize;
                let config = ResolveConfig {
                    max_depth: usize::MAX,
                    max_solutions: 1,
                    simplify: false,
                    definite_only: false,
                    ..Default::default()
                };

                let run = |n: usize| -> ResolveStats {
                    let (mut kb, query) = build_n_body_fixture(n);
                    let (_sols, stats) = kb.resolve_with_stats(&[query], &config);
                    stats
                };

                let s_small = run(small);
                let s_large = run(large);

                eprintln!(
                    "  n={small}: lazy_walk_calls={}",
                    s_small.lazy_walk_calls,
                );
                eprintln!(
                    "  n={large}: lazy_walk_calls={}",
                    s_large.lazy_walk_calls,
                );

                // Linear bound: lazy_walk_calls must stay below 8·n. With
                // eager apply_subst_each in place, the equivalent metric
                // scaled ~n²/2 ≈ 5_000 (n=100) and ~80_000 (n=400) — far
                // beyond this bound.
                assert!(
                    s_large.lazy_walk_calls < 8 * large as u64,
                    "lazy_walk_calls={} for n={} should be O(n), not O(n²)",
                    s_large.lazy_walk_calls,
                    large,
                );

                // Ratio sanity check: large/small ought to be ≤ ~6× for
                // linear growth (allow constant slack), not ≥ ~16× as
                // quadratic gives.
                let ratio = s_large.lazy_walk_calls as f64
                    / s_small.lazy_walk_calls.max(1) as f64;
                assert!(
                    ratio < 6.0,
                    "growth ratio {ratio:.1}× between n={small} and \
                     n={large} indicates super-linear scaling \
                     (quadratic ≈ 16×)",
                );
            })
            .unwrap()
            .join()
            .unwrap();
    }

    /// Anonymous vars flow through rule chaining.
    ///
    /// f(?x) :- p(?x, ?, ?)
    /// p(?a, ?b, ?c) :- check(?a, ?b, ?c)
    ///
    /// The ? in f are anonymous to f, but p needs them as ?b, ?c.
    /// Verifies that anonymous vars participate in unification with
    /// called rules — they are "don't care" for the caller, not
    /// wildcards that skip binding.
    ///
    /// Also documents the redundant-solutions issue:
    /// found(?x) :- item(?x, ?, ?) with multiple items sharing ?x
    /// produces N solutions instead of 1 (WI-026).
    #[test]
    fn anonymous_vars_chain_through_rules() {
        let mut kb = KnowledgeBase::new();
        let sort = kb.make_name_term("Sort");
        let domain = kb.make_name_term("test");

        let check_sym = kb.intern("check");
        let p_sym = kb.intern("p");
        let f_sym = kb.intern("f");
        let item_sym = kb.intern("item");
        let found_sym = kb.intern("found");

        // Helper: make a fresh anonymous var
        let anon = |kb: &mut KnowledgeBase| {
            let s = kb.intern("_");
            let v = kb.fresh_var(s);
            kb.alloc(Term::Var(Var::Global(v)))
        };
        let named = |kb: &mut KnowledgeBase, name: &str| {
            let s = kb.intern(name);
            let v = kb.fresh_var(s);
            (v, kb.alloc(Term::Var(Var::Global(v))))
        };

        // Facts: check("ok", 1, 10), check("ok", 2, 20), check("fail", 1, 1)
        let ok = kb.alloc(Term::Const(Literal::String("ok".into())));
        let fail = kb.alloc(Term::Const(Literal::String("fail".into())));
        for (s, n1, n2) in [
            (ok, 1i64, 10i64),
            (ok, 2, 20),
            (fail, 1, 1),
        ] {
            let v1 = kb.alloc(Term::Const(Literal::Int(n1)));
            let v2 = kb.alloc(Term::Const(Literal::Int(n2)));
            let fact = kb.alloc(Term::Fn {
                functor: check_sym,
                pos_args: SmallVec::from_slice(&[s, v1, v2]),
                named_args: SmallVec::new(),
            });
            kb.assert_fact(fact, sort, domain, None);
        }

        // Rule: p(?a, ?b, ?c) :- check(?a, ?b, ?c)
        let (_, va) = named(&mut kb, "a");
        let (_, vb) = named(&mut kb, "b");
        let (_, vc) = named(&mut kb, "c");
        let p_head = kb.alloc(Term::Fn {
            functor: p_sym,
            pos_args: SmallVec::from_slice(&[va, vb, vc]),
            named_args: SmallVec::new(),
        });
        let p_body = kb.alloc(Term::Fn {
            functor: check_sym,
            pos_args: SmallVec::from_slice(&[va, vb, vc]),
            named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[p_body]);
        kb.assert_rule_debruijn_with_nodes(p_head, body_nodes, sort, domain, None);

        // Rule: f(?x) :- p(?x, ?, ?)
        let (_, vx) = named(&mut kb, "x");
        let a1 = anon(&mut kb);
        let a2 = anon(&mut kb);
        let f_head = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(vx, 1),
            named_args: SmallVec::new(),
        });
        let f_body = kb.alloc(Term::Fn {
            functor: p_sym,
            pos_args: SmallVec::from_slice(&[vx, a1, a2]),
            named_args: SmallVec::new(),
        });
        let body_nodes = kb.term_body_to_nodes(&[f_body]);
        kb.assert_rule_debruijn_with_nodes(f_head, body_nodes, sort, domain, None);

        // Query: f(?q)
        let (vq, var_q) = named(&mut kb, "q");
        let query = kb.alloc(Term::Fn {
            functor: f_sym,
            pos_args: SmallVec::from_elem(var_q, 1),
            named_args: SmallVec::new(),
        });

        let config = ResolveConfig { max_solutions: 10, ..ResolveConfig::default() };
        let solutions = kb.resolve(&[query], &config);

        // Anonymous ? in f's body correctly flow through to p's ?b, ?c.
        // check has 3 facts → p matches all 3 → f gets all 3.
        // Two have ?x="ok", one has ?x="fail".
        assert!(solutions.len() >= 2, "should find at least 2 solutions (ok + fail)");

        let mut xs: Vec<String> = solutions.iter()
            .filter_map(|sol| {
                let t = kb.reify(var_q, &sol.subst).expect_term();
                match kb.get_term(t) {
                    Term::Const(Literal::String(s)) => Some(s.clone()),
                    _ => None,
                }
            })
            .collect();
        xs.sort();
        xs.dedup();
        // Head-var dedup: "ok" and "fail" each appear once
        assert_eq!(xs, vec!["fail", "ok"],
            "head-var dedup should yield exactly 2 distinct solutions");
    }

    // ── WI-322: caller-var delay through op type_args ────────────

    /// A delayed builtin whose first arg is `g[T = ?caller_var](1)` — the
    /// caller var lives in the typed call's `type_args`, not its value
    /// structure. The delay pre-check must detect it through the type-arg
    /// `Value` and propagate rule delay (WI-322). Latent in the prelude (no
    /// builtin first-arg carries type_args yet), so this exercises it directly.
    #[test]
    fn delay_propagates_on_caller_var_in_type_args() {
        let mut kb = KnowledgeBase::new();
        let builtin_sym = kb.intern("test_builtin");
        // Register `test_builtin` as a non-Not/PushChoice builtin so the
        // pre-check classifies the goal (Eq is an arbitrary qualifying tag).
        kb.builtins.insert(builtin_sym, BuiltinTag::Eq);

        let g_sym = kb.intern("g");
        let t_sym = kb.intern("T");
        let caller_sym = kb.intern("caller");
        let caller_vid = kb.fresh_var(caller_sym);
        let caller_term = kb.alloc(Term::Var(Var::Global(caller_vid)));

        let span = crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);

        // g[T = ?caller_var](1) — concrete value arg, caller var only in type_args.
        let concrete = NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None);
        let g_call = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: g_sym,
                pos_args: vec![concrete],
                named_args: vec![],
                type_args: vec![(Some(t_sym), Value::term(caller_term))],
            },
            span,
            None,
        );
        // test_builtin( g[T = ?caller_var](1) )
        let goal = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: builtin_sym,
                pos_args: vec![g_call],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );

        let subst = Substitution::new();
        // ?caller_var IS a caller var → the rule must delay.
        assert!(
            kb.body_builtins_delay_on_caller_vars_nodes(
                std::slice::from_ref(&goal),
                &[caller_vid],
                &subst,
            ),
            "caller var inside the first arg's type_args must propagate delay"
        );
        // Control: not a caller var → no delay (the type-arg var is internal,
        // bindable by the rule's own body).
        assert!(
            !kb.body_builtins_delay_on_caller_vars_nodes(&[goal], &[], &subst),
            "an internal (non-caller) type-arg var must not force delay"
        );
    }

    /// Twin guard: a caller var in the first arg's *value* structure
    /// (`g(?caller_var)`, no type_args) must NOT propagate delay — a compound
    /// value arg is bound by the builtin via unification, so the bare-var gate
    /// deliberately excludes it (WI-322 keeps this behavior intact).
    #[test]
    fn no_delay_on_caller_var_in_value_structure() {
        let mut kb = KnowledgeBase::new();
        let builtin_sym = kb.intern("test_builtin");
        kb.builtins.insert(builtin_sym, BuiltinTag::Eq);

        let g_sym = kb.intern("g");
        let caller_sym = kb.intern("caller");
        let caller_vid = kb.fresh_var(caller_sym);

        let span = crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);

        // g(?caller_var) — caller var in a positional value slot, no type_args.
        let caller_occ = NodeOccurrence::new_expr(Expr::Var(Var::Global(caller_vid)), span, None);
        let g_call = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: g_sym,
                pos_args: vec![caller_occ],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );
        let goal = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: builtin_sym,
                pos_args: vec![g_call],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );

        let subst = Substitution::new();
        assert!(
            !kb.body_builtins_delay_on_caller_vars_nodes(&[goal], &[caller_vid], &subst),
            "a caller var in value structure (not a type position) must not force delay"
        );
    }

    /// Direct coverage of the WI-322 `collect_unbound_vars_node` extension: as a
    /// complete unbound-var collector it must report BOTH the value-structure
    /// var (`?y`, via `for_each_child`) AND the type-arg var (`?x`, via the new
    /// type-field descent) of `g[T = ?x](?y)`.
    #[test]
    fn collect_unbound_vars_node_descends_type_args() {
        let mut kb = KnowledgeBase::new();
        let g_sym = kb.intern("g");
        let t_sym = kb.intern("T");
        let x_sym = kb.intern("x");
        let y_sym = kb.intern("y");
        let vx = kb.fresh_var(x_sym);
        let vy = kb.fresh_var(y_sym);
        let x_term = kb.alloc(Term::Var(Var::Global(vx)));

        let span = crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);
        let y_occ = NodeOccurrence::new_expr(Expr::Var(Var::Global(vy)), span, None);
        let g_call = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: g_sym,
                pos_args: vec![y_occ],
                named_args: vec![],
                type_args: vec![(Some(t_sym), Value::term(x_term))],
            },
            span,
            None,
        );

        let subst = Substitution::new();
        let mut out = Vec::new();
        kb.collect_unbound_vars_node(&g_call, &subst, &mut out);
        out.sort_by_key(|v| v.raw());
        let mut expected = vec![vx, vy];
        expected.sort_by_key(|v| v.raw());
        assert_eq!(out, expected, "both the type-arg var and the value var must be collected");
    }

    /// WI-322 (review fix): a caller var inside a `Value::Node` type-arg spine —
    /// here a value-in-type that is itself a typed call `h[S = ?caller]` — must
    /// be detected. The collector descends `Value::Node` via the occurrence
    /// walker (the loader twin descends Node too); skipping it would under-delay
    /// a var that `with_fresh_vars` opened from a DeBruijn var in the spine.
    #[test]
    fn delay_propagates_on_caller_var_in_node_type_arg_spine() {
        let mut kb = KnowledgeBase::new();
        let builtin_sym = kb.intern("test_builtin");
        kb.builtins.insert(builtin_sym, BuiltinTag::Eq);

        let g_sym = kb.intern("g");
        let h_sym = kb.intern("h");
        let t_sym = kb.intern("T");
        let s_sym = kb.intern("S");
        let caller_sym = kb.intern("caller");
        let caller_vid = kb.fresh_var(caller_sym);
        let caller_term = kb.alloc(Term::Var(Var::Global(caller_vid)));

        let span = crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);

        // The Node-carried type-arg: a value-in-type `h[S = ?caller]` occurrence.
        let h_call = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: h_sym,
                pos_args: vec![],
                named_args: vec![],
                type_args: vec![(Some(s_sym), Value::term(caller_term))],
            },
            span,
            None,
        );
        // g[T = «Node(h[S = ?caller])»](1)
        let concrete = NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None);
        let g_call = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: g_sym,
                pos_args: vec![concrete],
                named_args: vec![],
                type_args: vec![(Some(t_sym), Value::Node(h_call))],
            },
            span,
            None,
        );
        let goal = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: builtin_sym,
                pos_args: vec![g_call],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );

        let subst = Substitution::new();
        assert!(
            kb.body_builtins_delay_on_caller_vars_nodes(
                std::slice::from_ref(&goal),
                &[caller_vid],
                &subst,
            ),
            "a caller var inside a Value::Node type-arg spine must propagate delay"
        );
    }

    /// WI-504: a caller var inside a `Value::Node` type-arg spine that is a
    /// `Type`-kind occurrence (not an `Expr` leaf) — here a parameterized type
    /// `List[Elem = ?caller]` whose binding rides a `TypeChild::Ground(Var)` — must
    /// be detected. Before the fix the occurrence walker's `None` arm dropped a
    /// Type/EffectExpr spine, so a caller var that `with_fresh_vars` opened from a
    /// DeBruijn var inside it would be silently missed (the exact under-delay
    /// failure-class WI-322 closed, for the Type-kind Node carrier only).
    #[test]
    fn delay_propagates_on_caller_var_in_type_node_spine() {
        let mut kb = KnowledgeBase::new();
        let builtin_sym = kb.intern("test_builtin");
        kb.builtins.insert(builtin_sym, BuiltinTag::Eq);

        let g_sym = kb.intern("g");
        let t_sym = kb.intern("T");
        let list_sym = kb.intern("List");
        let elem_sym = kb.intern("Elem");
        let caller_sym = kb.intern("caller");
        let caller_vid = kb.fresh_var(caller_sym);
        let caller_term = kb.alloc(Term::Var(Var::Global(caller_vid)));
        let list_ref = kb.alloc(Term::Ref(list_sym));

        let span = crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);

        // The Node-carried type-arg: a Type-kind occurrence `List[Elem = ?caller]`,
        // the caller var living in a `TypeChild::Ground(Var)` binding.
        let list_type = NodeOccurrence::new_type(
            TypeNode::Parameterized {
                base: TypeChild::Ground(list_ref),
                bindings: vec![(elem_sym, TypeChild::Ground(caller_term))],
            },
            span,
            None,
        );
        // g[T = «Type(List[Elem = ?caller])»](1)
        let concrete = NodeOccurrence::new_expr(Expr::Const(Literal::Int(1)), span, None);
        let g_call = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: g_sym,
                pos_args: vec![concrete],
                named_args: vec![],
                type_args: vec![(Some(t_sym), Value::Node(list_type))],
            },
            span,
            None,
        );
        let goal = NodeOccurrence::new_expr(
            Expr::Apply {
                functor: builtin_sym,
                pos_args: vec![g_call],
                named_args: vec![],
                type_args: vec![],
            },
            span,
            None,
        );

        let subst = Substitution::new();
        assert!(
            kb.body_builtins_delay_on_caller_vars_nodes(
                std::slice::from_ref(&goal),
                &[caller_vid],
                &subst,
            ),
            "a caller var inside a Type-kind Node type-arg spine must propagate delay"
        );
        // Control: an internal (non-caller) spine var must not force delay.
        assert!(
            !kb.body_builtins_delay_on_caller_vars_nodes(&[goal], &[], &subst),
            "an internal (non-caller) Type-spine var must not force delay"
        );
    }

    /// WI-504 (direct collector coverage): the Type/EffectExpr-spine walk is
    /// subst-aware — an unbound spine var IS collected while a spine var already
    /// bound to a concrete term under σ is NOT. Also exercises the `EffectExpr`
    /// arm (`effects_rows(present(label: ?var))`) and the `TypeChild::Node`
    /// recursion (a `Denoted` Expr leaf).
    #[test]
    fn collect_type_node_spine_is_subst_aware() {
        let mut kb = KnowledgeBase::new();
        let free_sym = kb.intern("free");
        let bound_sym = kb.intern("bound");
        let denoted_sym = kb.intern("denoted_free");
        let v_free = kb.fresh_var(free_sym);
        let v_bound = kb.fresh_var(bound_sym);
        let v_denoted = kb.fresh_var(denoted_sym);
        let free_term = kb.alloc(Term::Var(Var::Global(v_free)));
        let bound_term = kb.alloc(Term::Var(Var::Global(v_bound)));
        let concrete = kb.alloc(Term::Const(Literal::Int(7)));

        let span = crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 0);

        // effects_rows(present(label: ?free)) — caller var in an EffectExpr spine.
        let present = NodeOccurrence::new_effect_expr(
            EffectExprNode::Present { label: TypeChild::Ground(free_term) },
            span,
            None,
        );
        // A Denoted Expr leaf carrying ?denoted via a TypeChild::Node.
        let denoted_leaf =
            NodeOccurrence::new_expr(Expr::Var(Var::Global(v_denoted)), span, None);
        // arrow(param: «effects_rows…», result: Denoted(?denoted), effects: ?bound)
        // — three spine children of distinct kinds, plus a bound var.
        let arrow = Value::Node(NodeOccurrence::new_type(
            TypeNode::Arrow {
                param: TypeChild::Node(present),
                result: TypeChild::Node(NodeOccurrence::new_type(
                    TypeNode::Denoted { value: denoted_leaf },
                    span,
                    None,
                )),
                effects: TypeChild::Ground(bound_term),
            },
            span,
            None,
        ));

        // ?bound is already bound to a concrete term under σ.
        let mut subst = Substitution::new();
        subst.bind_term(&kb, v_bound, concrete);

        let mut out = Vec::new();
        kb.collect_type_value_unbound_vars(&arrow, &subst, &mut out);
        out.sort_by_key(|v| v.raw());
        let mut expected = vec![v_free, v_denoted];
        expected.sort_by_key(|v| v.raw());
        assert_eq!(
            out, expected,
            "the unbound EffectExpr-spine var and the Denoted-leaf var must be \
             collected; the σ-bound spine var must not be"
        );
    }
}

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

use super::subst::Substitution;
use super::node_occurrence::{
    self, EffectExprNode, Expr, NodeOccurrence, TypeChild, TypeNode,
};
use super::term::{Literal, Term, TermId, Var, VarId};
use super::term_view::{goal_fingerprint, GoalKey, ReflectedExpr, ReflectSyms, TermIdView, TermView, ViewHead, ViewItem};
use super::persist_subst::BindValue;
use crate::intern::Symbol;
use crate::eval::value::Value;
use super::RuleId;
use super::KnowledgeBase;

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
        BindValue::Term(t) => Value::Term(t),
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
    // ── Arithmetic and comparison builtins ───────────────────
    /// `anthill.prelude.Eq.eq(?a, ?b)` — structural equality (succeeds/fails).
    Eq,
    /// `anthill.prelude.Eq.neq(?a, ?b)` — structural inequality (succeeds/fails).
    Neq,
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
}

/// Result of executing a builtin.
enum BuiltinResult {
    /// Builtin succeeded; continue with current substitution unchanged.
    Success,
    /// Builtin succeeded and produced new variable bindings to merge.
    SuccessWithBindings(Substitution),
    /// Builtin cannot evaluate yet (argument still unbound); delay this goal.
    Delay,
    /// Builtin definitively failed (e.g. lookup_symbol for non-existent name).
    Failure,
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
    Continuation(Vec<TermId>),
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
}

impl Default for ResolveConfig {
    fn default() -> Self {
        Self {
            max_depth: 100,
            max_solutions: 0,
            simplify: false,
            definite_only: false,
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
}

// ── EqChange ────────────────────────────────────────────────────

/// Record of an equational rewrite step. `original` is the term-world input
/// (`apply_eq_rules` rewrites a `TermId`, so it is always a term); `rewritten`
/// is the RHS read back through `σ` carrier-faithfully as a [`Value`] (WI-348)
/// — an equation whose RHS binds a var to a `Value::Node` keeps it in the
/// record, instead of dropping to a bare var. (Such an RHS is unreachable until
/// value rule heads land, Phase C; faithful now.)
#[allow(dead_code)]
pub struct EqChange {
    pub rule_id: RuleId,
    pub original: TermId,
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
    assumed_facts: Vec<TermId>,
}

/// WI-246: reify a goal `Value` to a hash-consed `TermId` — a `Value::Term`
/// unwraps for free; a `Value::Node` occurrence goal is reified via
/// `occurrence_to_term`. Used only at genuine term/identity boundaries
/// (residual, dedup key, external-row handlers, assumed-fact matching), never
/// for the candidate match itself (which goes through `query_view`).
fn reify_goal_value(kb: &mut KnowledgeBase, g: &Value) -> TermId {
    match g {
        Value::Term(t) => *t,
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
}

/// Lazy search stream that yields one solution at a time via
/// `split_first`. Converts recursive DFS into an explicit choice-point
/// stack.
pub struct SearchStream {
    stack: Vec<Frame>,
    config: ResolveConfig,
    /// Per-query cache: goal TermId → discrim tree query results.
    /// Safe because facts/rules don't change during a single resolve call.
    query_cache: HashMap<TermId, Vec<(RuleId, Substitution)>>,
    /// Telemetry (see `ResolveStats`).
    stats: ResolveStats,
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

    /// Check if the stream is obviously exhausted (empty stack).
    pub fn is_empty(&self) -> bool {
        self.stack.is_empty()
    }

    /// Read-only access to telemetry (see `ResolveStats`).
    pub fn stats(&self) -> &ResolveStats {
        &self.stats
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

    /// Handle a frame in `Init` state — classify the current goal.
    fn step_init(&mut self, kb: &mut KnowledgeBase) -> Option<StepResult> {
        let frame = self.stack.last().unwrap();
        let depth = frame.depth;
        let delay_mode = match &frame.state {
            FrameState::Init { delay_mode } => delay_mode.clone(),
            _ => unreachable!(),
        };

        // 1. Depth limit exceeded → pop
        if depth > self.config.max_depth {
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
        // no lowering); a `Value::Term` goal via `apply_subst`. `goal_t` is the
        // term form when the goal has one — used by the synthetic term-only
        // markers (pop_assumption / forall_impl) that are never occurrences.
        let goal_val: Value = {
            let f = self.stack.last().unwrap();
            if f.subst.is_empty() {
                f.goals[0].clone()
            } else {
                let subst = f.subst.clone();
                let g0 = f.goals[0].clone();
                let walked = match g0 {
                    Value::Term(t) => Value::Term(kb.apply_subst(t, &subst)),
                    Value::Node(occ) => {
                        Value::Node(node_occurrence::substitute_occurrence(kb, &occ, &subst))
                    }
                    other => other,
                };
                self.stack.last_mut().unwrap().goals[0] = walked.clone();
                walked
            }
        };
        // The hash-consed `TermId` carrier of the goal, if any — a `Value::Node`
        // occurrence goal has none and is lowered on demand via `reify_goal_value`
        // below.
        let goal_t = match &goal_val {
            Value::Term(t) => Some(*t),
            _ => None,
        };
        let frame = self.stack.last().unwrap();

        // Scoping / hereditary-Harrop markers (`__pop_assumption`,
        // `forall_impl`, WI-108). Detected by functor so they work for
        // occurrence goals too (a rule-body `forall …` is a `Value::Node`);
        // these handlers are term-structured, so reify only when matched.
        let is_marker = match goal_val.head(kb) {
            ViewHead::Functor { functor: Some(f), .. } => {
                let n = kb.resolve_sym(f);
                n == "__pop_assumption" || n == "forall_impl"
            }
            _ => false,
        };
        if is_marker {
            let goal = goal_t.unwrap_or_else(|| reify_goal_value(kb, &goal_val));
            // 3.4 __pop_assumption(N) — pops N entries off assumed_facts.
            if let Some(n) = Self::pop_assumption_arg(kb, goal) {
                let f = self.stack.last_mut().unwrap();
                let drop_from = f.assumed_facts.len().saturating_sub(n);
                f.assumed_facts.truncate(drop_from);
                f.goals.remove(0);
                f.depth += 1;
                f.state = FrameState::Init { delay_mode: delay_mode.reset() };
                return Some(StepResult::Continue);
            }
            // 3.5 forall_impl(binders, antecedents, consequent) — skolemise,
            // push antecedents as scoped assumptions, prepend consequents.
            if Self::is_forall_impl(kb, goal, &frame.subst) {
                return self.step_forall_impl(kb, goal, depth, delay_mode);
            }
        }

        // 4. Builtin goal — classify by functor read through TermView.
        if let Some(tag) = kb.get_builtin_view(&goal_val) {
            // NAF needs sub-resolution context — handle it specially
            if tag == BuiltinTag::Not {
                return self.step_naf(kb, &goal_val, depth, delay_mode);
            }
            // HO predicate application: replace goal with the applied term.
            // `resolve_ho_apply` is term-structured; reify a Node goal (rare at
            // a rule-body HoApply position) to a term for it.
            if tag == BuiltinTag::HoApply {
                let subst = frame.subst.clone();
                let goal = goal_t.unwrap_or_else(|| reify_goal_value(kb, &goal_val));
                if let Some(applied) = self.resolve_ho_apply(kb, goal, &subst) {
                    let f = self.stack.last_mut().unwrap();
                    f.goals[0] = Value::Term(applied);
                    f.state = FrameState::Init { delay_mode };
                    return Some(StepResult::Continue);
                } else {
                    // Predicate var still unbound — fail (can't apply unbound predicate)
                    self.stack.pop();
                    return Some(StepResult::Continue);
                }
            }
            // Bypasses execute_builtin: push_choice's effect is on the
            // choice-point stack, not on σ — like Not/HoApply. Term-structured;
            // reify a Node goal for arg extraction.
            if tag == BuiltinTag::PushChoice {
                let subst = frame.subst.clone();
                let goal = goal_t.unwrap_or_else(|| reify_goal_value(kb, &goal_val));
                if let Some((goal_a, goal_b)) =
                    Self::resolve_push_choice_args(kb, goal, &subst)
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
                    };
                    return Some(StepResult::Continue);
                } else {
                    self.stack.pop();
                    return Some(StepResult::Continue);
                }
            }
            match kb.execute_builtin(tag, &goal_val, &frame.subst) {
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
                    // Iterate Value-typed bindings; use bind_value so we
                    // don't force everything through Value::Term.
                    let new_goals = frame.goals[1..].to_vec();
                    let mut new_subst = frame.subst.clone();
                    for (var, val) in extra.bindings.iter() {
                        new_subst.bind_value(kb, *var, val.clone());
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
                BuiltinResult::Delay => {
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

        // 5. (WI-251) Expression-typed query path: the legacy
        // the legacy occurrence by-functor index lookup is gone. Reflection queries
        // that materialized expression occurrences now read from
        // `kb.op_bodies` (NodeOccurrence trees) at the reflection-op
        // layer, not via Resolve's candidate selection.
        let mut candidates: Vec<Candidate> = Vec::new();

        // 6. Non-builtin goal → query discrimination tree via `TermView`
        // (no lowering — a `Value::Node` goal matches Term-indexed heads).
        // Cache only ground *term* goals: the cache is keyed on hash-consed
        // `TermId`, so occurrence goals and goals with variables aren't cached.
        let cache_key = goal_t.filter(|&t| kb.collect_vars(t).is_empty());
        let rule_candidates = match cache_key.and_then(|t| self.query_cache.get(&t).cloned()) {
            Some(cached) => cached,
            None => {
                let mut rc = kb.query_view(&goal_val);
                // [simp] resolution-phase rewrite — term goals only.
                if self.config.simplify {
                    if let Some(goal) = goal_t {
                        let has_non_eq = rc.iter().any(|(rid, _)| !kb.is_equation(*rid));
                        if !has_non_eq {
                            let (rewritten, changes) = kb.apply_eq_rules(goal, 100);
                            if !changes.is_empty() {
                                rc = kb.query(rewritten);
                            }
                        }
                    }
                }
                rc.retain(|(rid, _)| !kb.is_equation(*rid));
                if let Some(t) = cache_key {
                    self.query_cache.insert(t, rc.clone());
                }
                rc
            }
        };

        candidates.extend(rule_candidates.into_iter().map(|(rid, s)| Candidate::Rule(rid, s)));

        // External-source rows (proposal 007 §11 + 026.1 Q4 Stage B). If the
        // goal head functor has a registered route handler, drain its stream
        // and add each matching row as an ExternalRow candidate. Term-
        // structured; reify a Node goal for the handler + row match.
        let functor = match goal_val.head(kb) {
            ViewHead::Functor { functor: Some(f), .. } => Some(f),
            _ => None,
        };
        if let Some(functor) = functor {
            if kb.route_handler_for(functor).is_some() {
                let goal = goal_t.unwrap_or_else(|| reify_goal_value(kb, &goal_val));
                let stream_opt = kb.route_handler_for(functor).map(|h| h.retrieve(kb, goal));
                if let Some(mut stream) = stream_opt {
                    while let Some(row) = stream.next() {
                        if let Some(subst) = kb.match_view(goal, &row) {
                            if !subst.is_contradiction() {
                                candidates.push(Candidate::ExternalRow(subst));
                            }
                        }
                    }
                }
            }
        }

        // Frame-scoped assumed facts (WI-108). Reify the goal through the
        // current substitution carrier-faithfully (WI-348), then unify each
        // assumed fact against it via the `TermView` matcher — so a goal
        // carrying a `Value::Node` matches by its structure instead of being
        // lowered to a hash-consed term that drops the occurrence.
        let assumed = self.stack.last().unwrap().assumed_facts.clone();
        if !assumed.is_empty() {
            let frame_subst = self.stack.last().unwrap().subst.clone();
            let goal_value = kb.reify_value(&goal_val, &frame_subst);
            for assumed_fact in assumed {
                if let Some(subst) = kb.match_view(assumed_fact, &goal_value) {
                    if !subst.is_contradiction() {
                        candidates.push(Candidate::Assumption(subst));
                    }
                }
            }
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
        };
        Some(StepResult::Continue)
    }

    /// Handle `not(Goal)` — negation-as-failure.
    ///
    /// - If the inner goal is not ground after applying the current substitution,
    ///   delay (floundering prevention).
    /// - Otherwise, run sub-resolution: if the inner goal has ANY solution,
    ///   `not(Goal)` fails; if it has NO solutions, `not(Goal)` succeeds.
    /// True if `goal` is a `forall_impl(...)` body goal. Walks the goal
    /// to handle the case where it sits behind a flex var binding.
    fn is_forall_impl(kb: &KnowledgeBase, goal: TermId, subst: &Substitution) -> bool {
        let walked = kb.walk(goal, subst);
        match kb.terms.get(walked) {
            Term::Fn { functor, .. } => kb.resolve_sym(*functor) == "forall_impl",
            _ => false,
        }
    }

    /// Discharge a `forall_impl(binders, antecedents, consequent)` body
    /// goal: skolemise the binders into fresh `Var::Rigid` witnesses,
    /// substitute throughout antecedents and consequent, push antecedents
    /// as scoped assumptions on the next frame, and prepend consequents
    /// to the goal stream.
    fn step_forall_impl(
        &mut self,
        kb: &mut KnowledgeBase,
        goal: TermId,
        depth: usize,
        delay_mode: DelayMode,
    ) -> Option<StepResult> {
        let frame = self.stack.last().unwrap();
        let walked = kb.walk(goal, &frame.subst);
        let pos_args = match kb.terms.get(walked) {
            Term::Fn { pos_args, .. } if pos_args.len() == 3 => pos_args.clone(),
            _ => {
                // Malformed forall_impl term — treat as failure
                self.stack.pop();
                return Some(StepResult::Continue);
            }
        };

        let binder_tids = Self::unwrap_tuple_args(kb, pos_args[0]);
        let antecedent_tids = Self::unwrap_tuple_args(kb, pos_args[1]);
        let consequent_tids = Self::unwrap_tuple_args(kb, pos_args[2]);

        // Build the Global → Rigid substitution map from the binders.
        let mut skolem_map: HashMap<u32, TermId> = HashMap::new();
        for &b in &binder_tids {
            let walked_b = kb.walk(b, &frame.subst);
            if let Term::Var(Var::Global(vid)) = kb.terms.get(walked_b) {
                let vid = *vid;
                let fresh = kb.fresh_var(vid.name());
                let rigid_term = kb.alloc(Term::Var(Var::Rigid(fresh)));
                skolem_map.insert(vid.raw(), rigid_term);
            }
        }

        // Substitute Global → Rigid in antecedents and consequents.
        // Also try to lower top-level ho_apply forms in antecedents so
        // they share a functor with whatever the consequent's resolution
        // will eventually look up (the resolver's HoApply path lowers
        // the goal-side; we lower the assumption-side here for parity).
        let frame = self.stack.last().unwrap();
        let subst = frame.subst.clone();
        let mut skolemized_antecedents: Vec<TermId> = Vec::with_capacity(antecedent_tids.len());
        for &t in &antecedent_tids {
            let sk = Self::subst_globals(kb, t, &skolem_map);
            let lowered = Self::lower_ho_apply(kb, sk, &subst).unwrap_or(sk);
            skolemized_antecedents.push(lowered);
        }
        let skolemized_consequents: Vec<TermId> = consequent_tids.iter()
            .map(|&t| Self::subst_globals(kb, t, &skolem_map))
            .collect();

        // Append a pop_assumption marker after the consequents so the
        // assumed antecedents go out of scope before the surrounding
        // rule's remaining goals run (WI-108 scoping invariant).
        let frame = self.stack.last().unwrap();
        let n_assumed = skolemized_antecedents.len();
        let mut new_goals: Vec<Value> =
            skolemized_consequents.into_iter().map(Value::Term).collect();
        if n_assumed > 0 {
            let marker = Self::make_pop_assumption_marker(kb, n_assumed);
            new_goals.push(Value::Term(marker));
        }
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

    /// If `term` is a top-level `ho_apply(?P, args...)` with `?P` walking
    /// to a concrete symbol under `subst`, return the lowered form
    /// `pred_sym(args...)`. Otherwise `None`.
    fn lower_ho_apply(kb: &mut KnowledgeBase, term: TermId, subst: &Substitution) -> Option<TermId> {
        let (pos_args, _named) = match kb.terms.get(term) {
            Term::Fn { functor, pos_args, named_args, .. }
                if kb.resolve_sym(*functor) == "ho_apply" =>
                (pos_args.clone(), named_args.clone()),
            _ => return None,
        };
        if pos_args.is_empty() { return None; }
        let Some(pred) = kb.walk_arg_term(pos_args[0], subst) else { return None };
        let pred_sym = match kb.terms.get(pred) {
            Term::Ref(s) => *s,
            Term::Fn { functor, pos_args: pa, named_args: na, .. }
                if pa.is_empty() && na.is_empty() => *functor,
            _ => return None,
        };
        let remaining: SmallVec<[TermId; 4]> = pos_args[1..].into();
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

    /// Walk both args of a `push_choice(?a, ?b)` goal through σ and
    /// return them as `(goal_a, goal_b)`. Returns `None` if the goal is
    /// malformed (wrong arity). Proposal 033 / WI-075.
    fn resolve_push_choice_args(
        kb: &KnowledgeBase,
        goal: TermId,
        subst: &Substitution,
    ) -> Option<(TermId, TermId)> {
        match kb.terms.get(goal) {
            Term::Fn { pos_args, named_args, .. }
                if pos_args.len() == 2 && named_args.is_empty() =>
            {
                let goal_a = kb.walk(pos_args[0], subst);
                let goal_b = kb.walk(pos_args[1], subst);
                Some((goal_a, goal_b))
            }
            _ => None,
        }
    }

    /// Recognise `__pop_assumption(N)` and return N. Returns None for
    /// anything else.
    fn pop_assumption_arg(kb: &KnowledgeBase, goal: TermId) -> Option<usize> {
        match kb.terms.get(goal) {
            Term::Fn { functor, pos_args, named_args, .. }
                if kb.resolve_sym(*functor) == "__pop_assumption"
                    && pos_args.len() == 1
                    && named_args.is_empty() =>
            {
                match kb.terms.get(pos_args[0]) {
                    Term::Const(crate::kb::term::Literal::Int(n)) if *n >= 0 => Some(*n as usize),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    /// Extract the positional args of a `tuple(...)` Fn term. Returns an
    /// empty vec if the term isn't a tuple.
    fn unwrap_tuple_args(kb: &KnowledgeBase, id: TermId) -> Vec<TermId> {
        match kb.terms.get(id) {
            Term::Fn { functor, pos_args, .. } if kb.resolve_sym(*functor) == "tuple" => {
                pos_args.iter().copied().collect()
            }
            _ => Vec::new(),
        }
    }

    /// Walk a term, replacing every `Var::Global(vid)` whose raw id is
    /// in `subst_map` with the mapped term. Allocates new Fn terms only
    /// where children change.
    fn subst_globals(
        kb: &mut KnowledgeBase,
        term: TermId,
        subst_map: &HashMap<u32, TermId>,
    ) -> TermId {
        match kb.terms.get(term).clone() {
            Term::Var(Var::Global(vid)) => {
                subst_map.get(&vid.raw()).copied().unwrap_or(term)
            }
            Term::Fn { functor, pos_args, named_args } => {
                let new_pos: SmallVec<[TermId; 4]> = pos_args.iter()
                    .map(|&t| Self::subst_globals(kb, t, subst_map))
                    .collect();
                let new_named: SmallVec<[(Symbol, TermId); 2]> = named_args.iter()
                    .map(|&(s, t)| (s, Self::subst_globals(kb, t, subst_map)))
                    .collect();
                if new_pos.iter().zip(pos_args.iter()).all(|(a, b)| a == b)
                    && new_named.iter().zip(named_args.iter())
                        .all(|(a, b)| a.1 == b.1)
                {
                    return term;
                }
                kb.alloc(Term::Fn { functor, pos_args: new_pos, named_args: new_named })
            }
            _ => term,
        }
    }

    /// Resolve ho_apply(?P, args...) by walking ?P through the substitution.
    /// If ?P resolves to a concrete symbol, construct Fn(sym, args) and return it.
    fn resolve_ho_apply(&self, kb: &mut KnowledgeBase, goal: TermId, subst: &Substitution) -> Option<TermId> {
        let (pos_args, _named_args) = match kb.get_term(goal) {
            Term::Fn { pos_args, named_args, .. } => (pos_args.clone(), named_args.clone()),
            _ => return None,
        };
        if pos_args.is_empty() { return None; }

        // First pos_arg is the predicate variable — walk it
        let Some(pred_tid) = kb.walk_arg_term(pos_args[0], subst) else { return None };
        let pred_sym = match kb.get_term(pred_tid) {
            Term::Ref(s) => *s,
            Term::Fn { functor, pos_args: pa, named_args: na, .. }
                if pa.is_empty() && na.is_empty() => *functor,
            _ => return None, // still a variable or complex term — can't apply
        };

        // Construct the applied goal: pred_sym(remaining_args)
        let remaining: SmallVec<[TermId; 4]> = pos_args[1..].into();
        let result = kb.alloc(Term::Fn {
            functor: pred_sym,
            pos_args: remaining,
            named_args: SmallVec::new(),
        });
        Some(result)
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

        // Groundness check: NAF on non-ground goals would be unsound.
        if !kb.value_is_ground(&inner, &subst) {
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
                        let f = self.stack.last_mut().unwrap();
                        let mut rotated: Vec<Value> = f.goals[1..].to_vec();
                        rotated.push(goal.clone());
                        f.goals = rotated;
                        f.depth = depth + 1;
                        f.state = FrameState::Init {
                            delay_mode: DelayMode::Delayed { consecutive_delays: 1 },
                        };
                        return Some(StepResult::Continue);
                    }
                }
                DelayMode::Delayed { consecutive_delays } => {
                    let f = self.stack.last_mut().unwrap();
                    let mut rotated: Vec<Value> = f.goals[1..].to_vec();
                    rotated.push(goal.clone());
                    f.goals = rotated;
                    f.depth = depth + 1;
                    f.state = FrameState::Init {
                        delay_mode: DelayMode::Delayed {
                            consecutive_delays: consecutive_delays + 1,
                        },
                    };
                    return Some(StepResult::Continue);
                }
            }
        } else {
            // Ground: classify the inner goal P three ways (WI-519). Pull the
            // inner stream until a DEFINITE (empty-residual) solution appears (P
            // holds → stop early) or it is exhausted, tracking whether any
            // FLOUNDERED (residual) solution was seen. `definite_only` is OFF for
            // this sub-search so residuals stay observable for the flounder check.
            let goal_v = kb.reify_value(&inner, &subst);
            let remaining_depth = self.config.max_depth.saturating_sub(depth);
            let sub_config = ResolveConfig {
                max_depth: remaining_depth,
                max_solutions: 0,
                simplify: self.config.simplify,
                definite_only: false,
            };
            let mut sub_stream = kb.resolve_lazy_goals(vec![goal_v], &sub_config);
            let mut inner_definite = false;
            let mut inner_floundered = false;
            while let Some((sol, rest)) = sub_stream.split_first(kb) {
                if sol.is_definite() {
                    inner_definite = true;
                    break;
                }
                inner_floundered = true;
                sub_stream = rest;
            }

            if inner_definite {
                // P has a definite solution → P holds → not(P) FAILS — backtrack.
                self.stack.pop();
                return Some(StepResult::Continue);
            } else if inner_floundered {
                // P only FLOUNDERED (a residual, no definite solution) → P is
                // undecided, so `not(P)` is undecided too: it must NOT silently
                // succeed (the old `is_some()` instead treated the residual as
                // "P holds" and made `not` wrongly FAIL). Propagate the
                // undecidedness as a residual `not(P)` — or skip it in
                // definite-only mode (a floundered goal is not a definite
                // solution). WI-519.
                self.stack.pop();
                if self.config.definite_only {
                    return Some(StepResult::Continue);
                }
                let residual = vec![goal.clone()];
                self.record_solution_in_ancestors();
                return Some(StepResult::YieldSolution(Solution { subst, residual }));
            } else {
                // P has no solution at all → P is false → not(P) SUCCEEDS.
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
            new_goals.extend(body.into_iter().map(Value::Term));
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
        // `resolve_leaf` records the conflict as `is_contradiction()` (the same
        // machinery the simp matcher honors); a contradictory candidate is a FALSE
        // match, so drop it rather than count it as a solution.
        if tree_subst.is_contradiction() {
            return Some(StepResult::Continue);
        }

        // A fact (empty body) or a non-rule candidate (external row / no rid).
        let is_fact = opt_rid.map_or(true, |rid| kb.is_fact(rid));

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
            let term_pairs: Vec<(VarId, TermId)> = tree_subst.iter_terms().collect();
            merged.bind_compressed(term_pairs.into_iter(), &kb.terms);
            // Non-Term bindings (`Value::Entity` from external rows, etc.)
            // bypass path compression and bind directly. This is the
            // proposal 026.1 §"Lineage-preserving bindings" guarantee:
            // an external row enters σ as its raw `Value` shape.
            for (vid, val) in tree_subst.iter() {
                if !matches!(val, Value::Term(_)) {
                    merged.bind_value(kb, *vid, val.clone());
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
            // [WI-030] No eager apply_subst_each here. The body itself is
            // already concretised through `body_rename` inside
            // `with_fresh_vars`, and caller-side bindings flow into
            // `frame.subst` via the `bind_compressed` call below; remaining
            // goals are walked lazily in `step_init`.
            let remaining = frame.goals[1..].to_vec();

            let caller_fresh_vars: Vec<VarId> = answer_links
                .iter_terms()
                .filter_map(|(_, tid)| match kb.terms.get(tid) {
                    Term::Var(Var::Global(vid)) => Some(*vid),
                    _ => None,
                })
                .collect();

            let mut merged = frame.subst.clone();
            // Path compression over the Value::Term subset of the link
            // bindings. Non-Term variants don't participate in caller-var
            // linkage, so filtering them out matches the pre-refactor
            // behavior exactly.
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

            // WI-246: opened rule-body atoms enter the goal stream as
            // `Value::Node` occurrences (carrying any typer dot-rewrites),
            // matched/resolved through `TermView` — no lowering to terms.
            let mut new_goals: Vec<Value> = Vec::with_capacity(fresh_nodes.len() + remaining.len());
            new_goals.extend(fresh_nodes.into_iter().map(Value::Node));
            new_goals.extend(remaining);
            let new_delay = delay_mode.reset();
            let inherited = frame.assumed_facts.clone();
            self.stack.push(Frame {
                goals: new_goals,
                subst: merged,
                depth: frame.depth + 1,
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
            .any(|(_, v)| !matches!(v, Value::Term(_) | Value::Node(_)));
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
            },
            query_cache: HashMap::new(),
            stats: ResolveStats::default(),
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
        let mut stream = self.resolve_lazy_goals(goals, config);
        let mut solutions = Vec::new();
        loop {
            match stream.split_first(self) {
                Some((sol, rest)) => {
                    solutions.push(sol);
                    if config.max_solutions > 0 && solutions.len() >= config.max_solutions {
                        return solutions;
                    }
                    stream = rest;
                }
                None => return solutions,
            }
        }
    }

    /// Like `resolve`, but also returns telemetry from the underlying
    /// search stream (see `ResolveStats`). Used by performance-oriented
    /// tests; production callers can stick with `resolve`.
    pub fn resolve_with_stats<V: TermView>(
        &mut self,
        goals: &[V],
        config: &ResolveConfig,
    ) -> (Vec<Solution>, ResolveStats) {
        let mut stream = self.resolve_lazy(goals, config);
        let mut solutions = Vec::new();
        let mut stats = ResolveStats::default();
        loop {
            match stream.split_first(self) {
                Some((sol, rest)) => {
                    solutions.push(sol);
                    stats = rest.stats().clone();
                    if config.max_solutions > 0
                        && solutions.len() >= config.max_solutions
                    {
                        return (solutions, stats);
                    }
                    stream = rest;
                }
                None => return (solutions, stats),
            }
        }
    }


    // ── Equational Rewriting ────────────────────────────────────

    /// Simplify a term using equational rules in the KB.
    ///
    /// Strategy: innermost (simplify subterms first, then try rewriting
    /// at the top level). Uses fuel to prevent non-termination from
    /// divergent rewrite systems.
    pub fn simplify(&mut self, term: TermId) -> TermId {
        let (result, _) = self.apply_eq_rules(term, 100);
        result
    }

    /// Apply equational rules to rewrite a term.
    ///
    /// Strategy: innermost — rewrite subterms first, then try top level.
    /// Returns `(rewritten_term, changes)`.
    pub fn apply_eq_rules(&mut self, term: TermId, fuel: usize) -> (TermId, Vec<EqChange>) {
        if fuel == 0 {
            return (term, vec![]);
        }

        let mut changes = Vec::new();

        // 1. Innermost: try rewriting subterms first
        let current = match self.terms.get(term).clone() {
            Term::Fn { functor, pos_args, named_args } => {
                let new_pos: SmallVec<[TermId; 4]> = pos_args
                    .iter()
                    .map(|&id| {
                        let (rewritten, sub_changes) = self.apply_eq_rules(id, fuel - 1);
                        changes.extend(sub_changes);
                        rewritten
                    })
                    .collect();
                let new_named: SmallVec<[(crate::intern::Symbol, TermId); 2]> = named_args
                    .iter()
                    .map(|&(sym, id)| {
                        let (rewritten, sub_changes) = self.apply_eq_rules(id, fuel - 1);
                        changes.extend(sub_changes);
                        (sym, rewritten)
                    })
                    .collect();
                self.alloc(Term::Fn { functor, pos_args: new_pos, named_args: new_named })
            }
            _ => term,
        };

        // 2. Try rewriting at top level using eq(current, ?result) pattern
        let r_sym = self.intern("_r");
        let r_vid = self.fresh_var(r_sym);
        let result_var = self.alloc(Term::Var(Var::Global(r_vid)));

        // The canonical equational functors — the symbols loaded equations
        // carry (`anthill.prelude.Eq.eq` for `=`, `anthill.kernel.unify` for the
        // `<=>` head, proposal 049), not a freshly-interned bare name. Querying
        // under each lets the resolver's equational fallback find loaded `[simp]`
        // rules of either spelling — discrim selection stays indexed (the
        // functor pins the trie root), matching the typer firing site
        // (`simp_rewrite`) — "one rewriter, two phases" (WI-283). Both queries
        // run while WI-526's `=`→`<=>` relabel is in flight; the inactive one
        // returns nothing.
        let eq_sym = self.eq_functor();
        let unify_sym = self.unify_functor();
        let mk_pattern = |kb: &mut Self, functor: Symbol| {
            kb.alloc(Term::Fn {
                functor,
                pos_args: SmallVec::from_slice(&[current, result_var]),
                named_args: SmallVec::new(),
            })
        };
        let eq_pattern = mk_pattern(self, eq_sym);
        let mut candidates = self.query(eq_pattern);
        if unify_sym != eq_sym {
            let unify_pattern = mk_pattern(self, unify_sym);
            candidates.extend(self.query(unify_pattern));
        }

        for (rid, tree_subst) in candidates {
            if !self.is_equation(rid) {
                continue;
            }
            // WI-283: a rule scoped to a sort that declares `requires`
            // carries an implicit type-directed guard (the sort's
            // `requires`, proposal 043 §4.1). Honoring it needs the
            // receiver's `min_sort`, which only the typer has — the
            // resolver holds type-erased terms. So the resolver fires only
            // *type-independent* identities and leaves requires-guarded
            // rules to the typer (`simp_rewrite`); firing one here would
            // rewrite where the requirement may be unmet (unsound). When a
            // reflect bridge later exposes `min_sort` over resolved
            // expressions, the guard can move here too.
            if self.equation_is_requires_guarded(rid) {
                continue;
            }

            // Read the result variable's binding back carrier-faithfully
            // (WI-348): an all-term RHS rebuilds its hash-consed term; a
            // `Value::Node` RHS keeps its identity in the recorded change. The
            // term-world rewrite continuation narrows to a term — a non-term RHS
            // is unreachable today and not further term-rewritable (Phase C).
            let rhs_value = self.reify(result_var, &tree_subst);
            let rhs = match &rhs_value {
                Value::Term(t) => *t,
                // A non-term RHS is unreachable today and not further term-rewritable
                // (Phase C); narrow to the result var so the continuation stays in
                // the term world.
                _ => result_var,
            };

            changes.push(EqChange {
                rule_id: rid,
                original: current,
                rewritten: rhs_value,
            });

            // Continue rewriting the result
            let (final_term, more_changes) = self.apply_eq_rules(rhs, fuel - 1);
            changes.extend(more_changes);
            return (final_term, changes);
        }

        (current, changes)
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
        // The symbol-reflection builtins (qualified_name, short_name,
        // lookup_symbol, resolve_sort_inst_param) operate on term-shaped symbol
        // data and keep their hash-consed `TermId` goal signature. A rule-body
        // goal arrives as a `Value::Node` occurrence (WI-246); lower it to a
        // term here so they handle it uniformly (no panic narrow). `field_access`
        // is fully `TermView`-migrated below (WI-482) — it reads its receiver
        // carrier-agnostically, so a `Value::Node` receiver (a denoted entity)
        // is projected without lowering.
        let as_term = |kb: &mut KnowledgeBase, g: &Value| match g {
            Value::Term(t) => *t,
            _ => reify_goal_value(kb, g),
        };
        match tag {
            BuiltinTag::NonVar => self.builtin_nonvar(goal, answer_subst),
            BuiltinTag::Ground => self.builtin_ground(goal, answer_subst),
            BuiltinTag::QualifiedName => { let t = as_term(self, goal); self.builtin_qualified_name(t, answer_subst) }
            BuiltinTag::ShortName => { let t = as_term(self, goal); self.builtin_short_name(t, answer_subst) }
            BuiltinTag::LookupSymbol => { let t = as_term(self, goal); self.builtin_lookup_symbol(t, answer_subst) }
            BuiltinTag::IsEntityOf => self.builtin_is_entity_of(goal, answer_subst),
            BuiltinTag::ExtractSort => self.builtin_extract_sort(goal, answer_subst),
            BuiltinTag::Not => unreachable!("Not is handled in step_init, not execute_builtin"),
            BuiltinTag::HoApply => unreachable!("HoApply is handled in step_init, not execute_builtin"),
            BuiltinTag::PushChoice => unreachable!("PushChoice is handled in step_init, not execute_builtin"),
            BuiltinTag::ResolveSortInstParam => { let t = as_term(self, goal); self.builtin_resolve_sort_inst_param(t, answer_subst) }
            BuiltinTag::Scope => self.builtin_scope(goal, answer_subst),
            BuiltinTag::Kind => self.builtin_kind(goal, answer_subst),
            BuiltinTag::Provenance => self.builtin_provenance(goal, answer_subst),
            BuiltinTag::FieldAccess => self.builtin_field_access(goal, answer_subst),
            BuiltinTag::Eq => self.builtin_eq(goal, answer_subst),
            BuiltinTag::Neq => self.builtin_neq(goal, answer_subst),
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
        }
    }

    /// Resolve a builtin goal argument (read through [`TermView`]) to a
    /// `Value` under σ — the representation-agnostic analog of
    /// `walk(builtin_first_arg(goal), σ)`. A term child is `walk_view`d; an
    /// occurrence child that is a bound `Global` var leaf is resolved via σ,
    /// otherwise kept as-is (WI-246). `None` ⇒ the arg slot is absent.
    fn walk_arg(&self, item: Option<ViewItem>, subst: &Substitution) -> Option<Value> {
        Some(match item? {
            ViewItem::Term(t) => self.walk_view(t, subst),
            ViewItem::Value(Value::Term(t)) => self.walk_view(*t, subst),
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
            Value::Term(t) => matches!(self.terms.get(*t), Term::Var(_)),
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
            Some(v) if self.value_is_unbound_var(&v) => BuiltinResult::Delay,
            Some(_) => BuiltinResult::Success,
        }
    }

    /// `ground(?x)`: succeeds if `?x` is fully ground (no unbound variables anywhere).
    fn builtin_ground<V: TermView>(&self, goal: &V, subst: &Substitution) -> BuiltinResult {
        match self.walk_arg(goal.pos_arg(self, 0), subst) {
            None => BuiltinResult::Failure,
            Some(v) if self.value_is_ground(&v, subst) => BuiltinResult::Success,
            Some(_) => BuiltinResult::Delay,
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
            Value::Term(t) => matches!(self.is_ground(*t, subst), GroundCheck::Ground),
            Value::Node(occ) => !node_occurrence::occurrence_has_unbound_var(occ),
            Value::Var(_) => false,
            _ => true,
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

    /// Extract the first positional argument from a builtin goal term.
    fn builtin_first_arg(&self, goal: TermId) -> TermId {
        match self.terms.get(goal) {
            Term::Fn { pos_args, .. } => {
                debug_assert!(!pos_args.is_empty(), "builtin goal must have at least one argument");
                pos_args[0]
            }
            _ => panic!("builtin_first_arg called on non-Fn term"),
        }
    }

    /// Extract the second positional argument from a builtin goal term.
    fn builtin_second_arg(&self, goal: TermId) -> TermId {
        match self.terms.get(goal) {
            Term::Fn { pos_args, .. } => {
                debug_assert!(pos_args.len() >= 2, "builtin goal must have at least two arguments");
                pos_args[1]
            }
            _ => panic!("builtin_second_arg called on non-Fn term"),
        }
    }

    /// `qualified_name(?sym, ?result)` — if `?sym` is bound to a Ref, bind `?result`
    /// to the full qualified name string. Delay if `?sym` is unbound.
    /// Return the fully-qualified name for a symbol.
    /// Resolved symbols use their `qualified_name`; unresolved ones get `_unresolved.<name>`.
    fn symbol_qualified_name(&self, sym: crate::intern::Symbol) -> String {
        match self.symbols.get(sym) {
            crate::intern::SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            crate::intern::SymbolDef::Unresolved { name } => format!("_unresolved.{}", name),
        }
    }

    /// Walk a builtin argument to a `TermId`, narrowing the carrier (WI-348
    /// directive #3 / proposal Phase D). The symbol/name/ref/result builtins
    /// (`qualified_name`, `short_name`, `lookup_symbol`,
    /// `resolve_sort_instantiation_param`, `field_access`, `ho_apply`) operate on
    /// term-shaped data; a var bound to a non-`Term` carrier (a `Value::Node`
    /// denoted/occurrence, a scalar) is a type error for them — `None` here,
    /// which each caller turns into its failure path. Reads through `walk_view`
    /// (the carrier-faithful chase) so a Node binding is *seen and rejected*, not
    /// silently chased past to the bare var (the former `walk`, which would then
    /// `Delay` on an already-bound arg). Latent today — the resolve_with_term
    /// removal diagnostic proved no rule body binds a non-`Term` into a builtin
    /// arg; this makes that boundary explicit and forward-correct.
    fn walk_arg_term(&self, arg: TermId, subst: &Substitution) -> Option<TermId> {
        // Narrow to the hash-consed `Term` carrier; a var bound to a non-`Term`
        // (a `Value::Node` denoted/occurrence, a scalar) is `None` here, which each
        // caller turns into its failure path (see the doc above).
        match self.walk_view(arg, subst) {
            Value::Term(t) => Some(t),
            _ => None,
        }
    }

    fn builtin_qualified_name(&mut self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let sym_arg = self.builtin_first_arg(goal);
        let result_arg = self.builtin_second_arg(goal);
        let Some(walked_sym) = self.walk_arg_term(sym_arg, subst) else {
            return BuiltinResult::Failure;
        };
        match self.terms.get(walked_sym).clone() {
            Term::Ref(sym) | Term::Ident(sym) => {
                let name = self.symbol_qualified_name(sym);
                let str_term = self.alloc(Term::Const(super::term::Literal::String(name)));
                let Some(walked_result) = self.walk_arg_term(result_arg, subst) else {
                    return BuiltinResult::Failure;
                };
                match self.terms.get(walked_result) {
                    Term::Var(Var::Global(vid)) => {
                        let vid = *vid;
                        let mut extra = Substitution::new();
                        extra.bind(self, vid, str_term);
                        BuiltinResult::SuccessWithBindings(extra)
                    }
                    _ => {
                        // Result already bound — succeed if it matches
                        if walked_result == str_term {
                            BuiltinResult::Success
                        } else {
                            BuiltinResult::Failure
                        }
                    }
                }
            }
            Term::Var(_) => BuiltinResult::Delay,
            _ => BuiltinResult::Failure,
        }
    }

    /// `short_name(?sym, ?result)` — if `?sym` is bound to a Ref, bind `?result`
    /// to the last dot-separated segment. Delay if `?sym` is unbound.
    fn builtin_short_name(&mut self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let sym_arg = self.builtin_first_arg(goal);
        let result_arg = self.builtin_second_arg(goal);
        let Some(walked_sym) = self.walk_arg_term(sym_arg, subst) else {
            return BuiltinResult::Failure;
        };
        match self.terms.get(walked_sym).clone() {
            Term::Ref(sym) | Term::Ident(sym) => {
                let full = self.symbols.resolve(sym);
                let short = full.rsplit('.').next().unwrap_or(full).to_string();
                let str_term = self.alloc(Term::Const(super::term::Literal::String(short)));
                let Some(walked_result) = self.walk_arg_term(result_arg, subst) else {
                    return BuiltinResult::Failure;
                };
                match self.terms.get(walked_result) {
                    Term::Var(Var::Global(vid)) => {
                        let vid = *vid;
                        let mut extra = Substitution::new();
                        extra.bind(self, vid, str_term);
                        BuiltinResult::SuccessWithBindings(extra)
                    }
                    _ => {
                        if walked_result == str_term {
                            BuiltinResult::Success
                        } else {
                            BuiltinResult::Failure
                        }
                    }
                }
            }
            Term::Var(_) => BuiltinResult::Delay,
            _ => BuiltinResult::Failure,
        }
    }

    /// `lookup_symbol(?name_str, ?result)` — if `?name_str` is a bound String,
    /// search the symbol table for that qualified name. Bind `?result` to
    /// `Term::Ref(symbol)` if found, fail if not. Delay if `?name_str` is unbound.
    fn builtin_lookup_symbol(&mut self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let name_arg = self.builtin_first_arg(goal);
        let result_arg = self.builtin_second_arg(goal);
        let Some(walked_name) = self.walk_arg_term(name_arg, subst) else {
            return BuiltinResult::Failure;
        };
        match self.terms.get(walked_name).clone() {
            Term::Const(super::term::Literal::String(name)) => {
                // Look up the symbol by qualified name (read-only)
                match self.symbols.by_qualified_name.get(&name).copied() {
                    Some(sym) => {
                        let ref_term = self.alloc(Term::Ref(sym));
                        let Some(walked_result) = self.walk_arg_term(result_arg, subst) else {
                            return BuiltinResult::Failure;
                        };
                        match self.terms.get(walked_result) {
                            Term::Var(Var::Global(vid)) => {
                                let vid = *vid;
                                let mut extra = Substitution::new();
                                extra.bind(self, vid, ref_term);
                                BuiltinResult::SuccessWithBindings(extra)
                            }
                            _ => {
                                if walked_result == ref_term {
                                    BuiltinResult::Success
                                } else {
                                    BuiltinResult::Failure
                                }
                            }
                        }
                    }
                    None => BuiltinResult::Failure,
                }
            }
            Term::Var(_) => BuiltinResult::Delay,
            _ => BuiltinResult::Failure,
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
            return BuiltinResult::Delay;
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

    /// WI-246: collapse a `Value::Node` arg to `Value::Term` (via
    /// `occurrence_to_term`); scalars and terms pass through. Lets the
    /// scalar/term-comparison builtins (`eq`/`neq`/`cmp`) treat a literal
    /// occurrence arg uniformly.
    fn normalize_value(&mut self, v: Value) -> Value {
        match v {
            // Reuse the single Node→term path; cf. `reify_goal_value` (the
            // bare-`TermId` variant for goal-identity boundaries).
            Value::Node(_) => Value::Term(reify_goal_value(self, &v)),
            other => other,
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
            return BuiltinResult::Delay;
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        let walked_inst = reify_goal_value(self, &inst);

        // Extract the sort symbol from various term shapes
        let sort_sym = match self.terms.get(walked_inst).clone() {
            // Simple Ref: the sort itself
            Term::Ref(sym) => Some(sym),
            // SortView(sort_name_term, bindings...) — first pos arg is the sort name
            Term::Fn { ref functor, ref pos_args, .. } => {
                let functor_name = self.symbols.name(*functor);
                if functor_name == "SortView" && !pos_args.is_empty() {
                    // First pos arg is the sort name term (e.g. Eq())
                    let name_term = pos_args[0];
                    match self.terms.get(name_term) {
                        Term::Fn { functor: inner_f, .. } => Some(*inner_f),
                        Term::Ref(sym) => Some(*sym),
                        _ => None,
                    }
                } else {
                    // Direct functor (e.g. Eq() or SortInfo(...))
                    Some(*functor)
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
            return BuiltinResult::Delay;
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        let walked = reify_goal_value(self, &place_val);
        // A `Symbol` value is a `Term::Ref`; a canonical sort/place reference is
        // a nullary `Fn` — accept either, mirroring `builtin_kind`.
        let sym = match self.terms.get(walked) {
            Term::Ref(s) => *s,
            Term::Fn { functor, .. } => *functor,
            _ => return BuiltinResult::Failure,
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

    /// Shared front-half for the occurrence builtins (WI-297): walk arg0 to the
    /// subject occurrence and reify arg1 to a result/pattern term under σ.
    /// `Err(_)` carries the early `BuiltinResult` (Delay on an unbound subject,
    /// Failure on a missing/non-occurrence subject or a missing arg1). On `Ok`,
    /// the caller produces its target term/view and unifies the returned
    /// pattern against it via [`KnowledgeBase::match_view`].
    fn occurrence_arg_and_pattern<V: TermView>(
        &mut self,
        goal: &V,
        subst: &Substitution,
    ) -> Result<(Rc<NodeOccurrence>, TermId), BuiltinResult> {
        // arg0 — the subject occurrence.
        let occ = match self.walk_arg(goal.pos_arg(self, 0), subst) {
            None => return Err(BuiltinResult::Failure),
            Some(v) if self.value_is_unbound_var(&v) => return Err(BuiltinResult::Delay),
            Some(Value::Node(rc)) => rc,
            // Not an occurrence — nothing to reflect.
            Some(_) => return Err(BuiltinResult::Failure),
        };
        // arg1 — extract an owned pattern source so the immutable borrow from
        // `pos_arg` ends before the `&mut self` reify below.
        let mut pat_term: Option<TermId> = None;
        let mut pat_node = None;
        match goal.pos_arg(self, 1) {
            Some(ViewItem::Term(t)) => pat_term = Some(t),
            Some(ViewItem::Value(Value::Term(t))) => pat_term = Some(*t),
            Some(ViewItem::Node(o)) => pat_node = Some(o),
            Some(ViewItem::Value(_)) | None => return Err(BuiltinResult::Failure),
        }
        // Reify the pattern to a term (keeping its unbound vars), then resolve
        // any vars already bound earlier in the body. A child-bearing reflect
        // pattern (`if_expr`/`let_expr`/`lambda`/`match_expr`) has no goal-term
        // shape and isn't yet handled by the lens — fail (no match) rather than
        // trip `occurrence_to_term`'s goal-form assertion (WI-297).
        let pattern = match (pat_term, pat_node) {
            (Some(t), _) => t,
            (None, Some(o)) => match node_occurrence::try_occurrence_to_term(self, &o) {
                Some(t) => t,
                None => return Err(BuiltinResult::Failure),
            },
            (None, None) => return Err(BuiltinResult::Failure),
        };
        Ok((occ, self.apply_subst(pattern, subst)))
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
        match self.match_view(pattern, &ReflectedExpr::new(occ, syms)) {
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
        match self.match_view(pattern, &TermIdView(span_term)) {
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
        match self.match_view(pattern, &TermIdView(owner)) {
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
        match self.match_view(pattern, &Value::Node(list)) {
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
            Some(v) if self.value_is_unbound_var(&v) => return BuiltinResult::Delay,
            Some(v) => v,
        };
        // arg0 must be a term-shaped Symbol (Ref/Ident/Fn-functor). A non-term
        // Value (Node / scalar / tuple) is simply not an operation symbol — fail
        // cleanly rather than panic (don't route through `reify_goal_value`).
        let op_sym = match &op_val {
            Value::Term(t) => match self.terms.get(*t) {
                Term::Ref(s) | Term::Ident(s) => *s,
                Term::Fn { functor, .. } => *functor,
                _ => return BuiltinResult::Failure,
            },
            _ => return BuiltinResult::Failure,
        };
        // arg1 — the result pattern (mirror occurrence_arg_and_pattern's arg1 block).
        let mut pat_term: Option<TermId> = None;
        let mut pat_node = None;
        match goal.pos_arg(self, 1) {
            Some(ViewItem::Term(t)) => pat_term = Some(t),
            Some(ViewItem::Value(Value::Term(t))) => pat_term = Some(*t),
            Some(ViewItem::Node(o)) => pat_node = Some(o),
            Some(ViewItem::Value(_)) | None => return BuiltinResult::Failure,
        }
        let pattern = match (pat_term, pat_node) {
            (Some(t), _) => t,
            (None, Some(o)) => match node_occurrence::try_occurrence_to_term(self, &o) {
                Some(t) => t,
                None => return BuiltinResult::Failure,
            },
            (None, None) => return BuiltinResult::Failure,
        };
        let pattern = self.apply_subst(pattern, subst);
        // Build the Option result as a Value::Node occurrence (like sub_occurrences
        // builds its list-node): some(value: <body>) or none().
        let result_node = match self.op_body_node(op_sym).cloned() {
            Some(node) => {
                let some_sym = self.resolve_symbol("anthill.prelude.Option.some");
                let value_sym = self.intern("value");
                let mut named = vec![(value_sym, node.clone())];
                self.sort_named_canonical(some_sym, &mut named);
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
        match self.match_view(pattern, &Value::Node(result_node)) {
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

    /// Sort named args into the functor's canonical (declared field) order —
    /// the order the loader canonicalizes patterns to (`load.rs` via
    /// `entity_field_names`). The discrim tree matches named args positionally
    /// (`discrim.rs`: it descends `NamedKey(query_keys[i])` against the tree's
    /// i-th pattern key), so a built term must use the same order as the loaded
    /// pattern or it silently fails to match. Falls back to interning order
    /// when the functor has no registered field list. Generic over the value
    /// type so it serves both `Term::Fn` (`TermId`) and occurrence
    /// (`Rc<NodeOccurrence>`) builders.
    pub(crate) fn sort_named_canonical<T>(&self, functor: Symbol, named: &mut [(Symbol, T)]) {
        match self.entity_field_names(functor) {
            Some(fields) => {
                let order: HashMap<Symbol, usize> =
                    fields.iter().enumerate().map(|(i, &s)| (s, i)).collect();
                named.sort_by_key(|(s, _)| order.get(s).copied().unwrap_or(usize::MAX));
            }
            None => named.sort_by_key(|(s, _)| s.index()),
        }
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

    /// `resolve_sort_instantiation_param(?spec, ?param_name, ?value)` —
    /// given a SortView term and a Ref(sym) for the param name,
    /// find the corresponding named arg value. Delays if either arg is unbound.
    fn builtin_resolve_sort_inst_param(&mut self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let (inst_arg, param_arg, value_arg) = match self.terms.get(goal) {
            Term::Fn { pos_args, .. } if pos_args.len() >= 3 => {
                (pos_args[0], pos_args[1], pos_args[2])
            }
            _ => return BuiltinResult::Failure,
        };

        let Some(walked_inst) = self.walk_arg_term(inst_arg, subst) else {
            return BuiltinResult::Failure;
        };
        let Some(walked_param) = self.walk_arg_term(param_arg, subst) else {
            return BuiltinResult::Failure;
        };

        // Delay if either arg is unbound
        if matches!(self.terms.get(walked_inst), Term::Var(_)) {
            return BuiltinResult::Delay;
        }
        if matches!(self.terms.get(walked_param), Term::Var(_)) {
            return BuiltinResult::Delay;
        }

        // Extract the param symbol from the param arg (must be Ref)
        let param_sym = match self.terms.get(walked_param) {
            Term::Ref(sym) => *sym,
            Term::Fn { functor, .. } => *functor,
            _ => return BuiltinResult::Failure,
        };

        // Walk spec — must be SortView(sort_name, named_args...)
        let value_tid = match self.terms.get(walked_inst).clone() {
            Term::Fn { ref functor, ref named_args, .. } => {
                let functor_name = self.symbols.name(*functor);
                if functor_name == "SortView" {
                    // Search named_args for the matching param symbol
                    named_args.iter()
                        .find(|(sym, _)| *sym == param_sym)
                        .map(|(_, tid)| *tid)
                } else {
                    None
                }
            }
            _ => None,
        };

        match value_tid {
            Some(val) => {
                let Some(walked_value) = self.walk_arg_term(value_arg, subst) else {
                    return BuiltinResult::Failure;
                };
                match self.terms.get(walked_value) {
                    Term::Var(Var::Global(vid)) => {
                        let vid = *vid;
                        let mut extra = Substitution::new();
                        extra.bind(self, vid, val);
                        BuiltinResult::SuccessWithBindings(extra)
                    }
                    _ => {
                        if walked_value == val {
                            BuiltinResult::Success
                        } else {
                            BuiltinResult::Failure
                        }
                    }
                }
            }
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
            EqOperands::Delay => BuiltinResult::Delay,
            EqOperands::Ready(a, b) => {
                if self.values_equal(&a, &b) { BuiltinResult::Success } else { BuiltinResult::Failure }
            }
            EqOperands::Absent => BuiltinResult::Failure,
        }
    }

    /// `neq(?a, ?b)` — structural inequality after walking.
    fn builtin_neq<V: TermView>(&mut self, goal: &V, subst: &Substitution) -> BuiltinResult {
        match self.eq_operands(goal, subst) {
            EqOperands::Delay => BuiltinResult::Delay,
            EqOperands::Ready(a, b) => {
                if self.values_equal(&a, &b) { BuiltinResult::Failure } else { BuiltinResult::Success }
            }
            EqOperands::Absent => BuiltinResult::Failure,
        }
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
        // (substitution transparency), not silently mismatches. Checked BEFORE
        // `normalize_value`, which would materialize the op-call `Node` into a
        // `Term` and hide it from `is_unreduced_op_call`.
        if self.is_unreduced_op_call(&a) || self.is_unreduced_op_call(&b) {
            return EqOperands::Delay;
        }
        // Reify literal occurrence args to terms so structural_eq compares
        // them by hash-consed identity (a Node-vs-Node compare is otherwise
        // conservatively false).
        let a = self.normalize_value(a);
        let b = self.normalize_value(b);
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
            UnifyOutcome::Delay => BuiltinResult::Delay,
            UnifyOutcome::Fail => BuiltinResult::Failure,
            // A binding to two structurally-distinct values surfaces as a
            // `work` contradiction (the chase prevents it on the linear-var
            // path; this is the carrier-edge backstop) — no unifier.
            UnifyOutcome::Ok if work.is_contradiction() => BuiltinResult::Failure,
            UnifyOutcome::Ok if work.bindings.is_empty() => BuiltinResult::Success,
            UnifyOutcome::Ok => BuiltinResult::SuccessWithBindings(work),
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
        match self.unify_values(Value::Term(a), Value::Term(b), &mut work) {
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
        // Rigid (skolem) / DeBruijn vars head as `Opaque` but carry a comparable
        // identity — mirror [`views_structurally_equal`] (WI-108): two occurrences
        // of the SAME such var unify (reflexivity, no binding); a rigid var vs a
        // different var or a concrete term does NOT (a skolem must never bind, per
        // `Var::Rigid`'s "unifies only with another Rigid carrying the same id").
        // Flex `Global` vars were already bound by `unify_values` before reaching
        // here; without this arm `!k <=> !k` would wrongly hit the `_ => Fail`
        // catch-all below, diverging from `eq`.
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
    fn occurs_in_value(&self, vid: VarId, value: &Value, work: &Substitution) -> bool {
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
            return BuiltinResult::Delay;
        }
        // Reify literal occurrence args (a numeric literal in the goal reads
        // as `Value::Node`) so `value_num` can extract from `Value::Term`.
        let a = self.normalize_value(a);
        let b = self.normalize_value(b);
        let ord = match (self.value_num(&a), self.value_num(&b)) {
            (Some(Num::Int(x)), Some(Num::Int(y))) => x.cmp(&y),
            (Some(Num::Big(x)), Some(Num::Big(y))) => x.cmp(&y),
            (Some(Num::Float(x)), Some(Num::Float(y))) => x.cmp(&y),
            // unbound handled above; cross-type / non-numeric → fail
            _ => return BuiltinResult::Failure,
        };
        if pred(ord) { BuiltinResult::Success } else { BuiltinResult::Failure }
    }

    /// Extract a comparable number from a σ-walked `Value` — an unboxed
    /// scalar, or a numeric `Const` inside a `Value::Term`. `None` for
    /// non-numeric values (cmp then fails, matching the original).
    fn value_num(&self, v: &Value) -> Option<Num> {
        match v {
            Value::Int(n) => Some(Num::Int(*n)),
            Value::BigInt(n) => Some(Num::Big(n.clone())),
            Value::Float(f) => Some(Num::Float(ordered_float::OrderedFloat(*f))),
            Value::Term(t) => match self.terms.get(*t) {
                Term::Const(Literal::Int(n)) => Some(Num::Int(*n)),
                Term::Const(Literal::BigInt(n)) => Some(Num::Big(n.clone())),
                Term::Const(Literal::Float(f)) => Some(Num::Float(*f)),
                _ => None,
            },
            _ => None,
        }
    }

    /// The `Var::Global` id of a σ-walked `Value`, if it is one — `Term::Var`
    /// or `Expr::Var` occurrence leaf. Used to decide whether a result arg is
    /// an unbound var to bind.
    fn value_global_var(&self, v: &Value) -> Option<VarId> {
        match v {
            Value::Term(t) => match self.terms.get(*t) {
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
    /// var, or check equality against an already-bound result (reifying a
    /// `Value::Node` literal result arg to a term first).
    fn finish_result(&mut self, target: ResultTarget, value: TermId) -> BuiltinResult {
        match target {
            ResultTarget::Bind(vid) => {
                let mut extra = Substitution::new();
                extra.bind(self, vid, value);
                BuiltinResult::SuccessWithBindings(extra)
            }
            ResultTarget::Compare(Some(v)) => {
                let bound = self.normalize_value(v);
                if matches!(bound, Value::Term(t) if t == value) {
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
            return BuiltinResult::Delay;
        }
        let target = (pos_arity >= 3).then(|| self.resolve_result_target(goal.pos_arg(self, 2), subst));

        // Reify literal occurrence operands (a numeric literal written in a rule
        // body reads as `Value::Node`) so `value_num` can extract from
        // `Value::Term` — the same normalization `cmp`/`eq` apply (WI-482).
        let a = self.normalize_value(a);
        let b = self.normalize_value(b);
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
            return BuiltinResult::Delay;
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        let value = match self.value_num(&arg) {
            Some(Num::Int(n)) => self.alloc(Term::Const(Literal::BigInt(num_bigint::BigInt::from(n)))),
            // Already a BigInt — pass the term through, or promote a scalar.
            Some(Num::Big(n)) => match &arg {
                Value::Term(t) => *t,
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
            return BuiltinResult::Delay;
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
            return BuiltinResult::Delay;
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        let walked_sym = reify_goal_value(self, &sym_val);
        // Extract the symbol from Ref or Fn term
        let sym = match self.terms.get(walked_sym) {
            Term::Ref(s) => *s,
            Term::Fn { functor, .. } => *functor,
            _ => return BuiltinResult::Failure,
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
            return BuiltinResult::Delay;
        }
        let target = self.resolve_result_target(goal.pos_arg(self, 1), subst);
        let walked_sym = reify_goal_value(self, &sym_val);
        let sym = match self.terms.get(walked_sym) {
            Term::Ref(s) => *s,
            Term::Fn { functor, .. } => *functor,
            _ => return BuiltinResult::Failure,
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
            return BuiltinResult::Delay;
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
            Value::Term(_) | Value::Node(_) => Some(reify_goal_value(self, v)),
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
            Some(val) => Value::Term(val),
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
        // σ-walk each POSITIONAL call arg to a Value (mirrors the receiver walk in
        // `reduce_dot_value`). The WI-279/WI-282 method dispatch puts the receiver
        // + positional args here; a NAMED-arg method call (`?b.m(k: 1)`) leaves a
        // param without a positional arg → the fold leaves the call un-ground
        // (residualizes), safe per the WI-483 leave-uninterpreted rule.
        let mut param_args: HashMap<Symbol, Value> = HashMap::new();
        for (i, &p) in params.iter().enumerate() {
            match self.walk_arg(occ.pos_arg(self, i), subst) {
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
            Value::Node(_) => v,
            other => other,
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
                Some(Value::Term(t)) => match self.terms.get(*t) {
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
                Some(Value::Term(t)) => self.collect_unbound_vars(*t, subst, out),
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
            Value::Term(t) => self.collect_unbound_vars(*t, subst, out),
            Value::Node(occ) => self.collect_unbound_vars_node(occ, subst, out),
            Value::Entity { pos, named, .. } | Value::Tuple { pos, named } => {
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
        kb.assert_fact(eq_head, sort, domain, None);

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
        kb.assert_fact(eq_head, sort, domain, None);

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
        kb.assert_fact(eq_head, sort, domain, None);

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
        kb.assert_fact(eq_head, sort, domain, None);

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
        kb.assert_fact(eq_head, sort, domain, None);

        let (result, changes) = kb.apply_eq_rules(lhs, 100);
        assert_eq!(result, four);
        assert_eq!(changes.len(), 1);
        assert_eq!(changes[0].original, lhs);
        assert_eq!(changes[0].rewritten.expect_term(), four);
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
        let eq_sym = kb.resolve_symbol("anthill.prelude.Eq.eq");
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
        let eq_sym = kb.resolve_symbol("anthill.prelude.Eq.eq");
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
        let neq_sym = kb.resolve_symbol("anthill.prelude.Eq.neq");
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
        let gt_sym = kb.resolve_symbol("anthill.prelude.Ordered.gt");
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
        let gt_sym = kb.resolve_symbol("anthill.prelude.Ordered.gt");
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

    #[test]
    fn not_respects_depth_limit() {
        // Recursive rule inside not() should terminate via depth limit.
        // r(x) :- r(x)  (infinite loop)
        // Query: not(r(a)) — sub-resolution should hit depth limit and find no solutions
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
        // The recursive rule never produces a solution (depth limit), so not() succeeds
        assert_eq!(solutions.len(), 1, "not(r(a)) should succeed since r(a) has no solutions");
        assert!(solutions[0].residual.is_empty(), "no residual expected");
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

        let config = ResolveConfig { max_depth: 20, max_solutions: 4, simplify: false, definite_only: false };
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
                type_args: vec![(Some(t_sym), Value::Term(caller_term))],
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
                type_args: vec![(Some(t_sym), Value::Term(x_term))],
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
                type_args: vec![(Some(s_sym), Value::Term(caller_term))],
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

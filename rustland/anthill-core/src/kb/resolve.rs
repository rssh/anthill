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

use smallvec::SmallVec;

use super::subst::Substitution;
use super::term::{Term, TermId, Var, VarId};
use crate::intern::Symbol;
use super::occurrence::OccurrenceId;
use super::RuleId;
use super::KnowledgeBase;

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
    /// `anthill.reflect.typing.extract_sort_ref(?inst, ?result)` — extract functor as Ref from instantiation term.
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

/// A resolution candidate — either a regular KB rule/fact or an occurrence.
#[derive(Clone)]
enum Candidate {
    /// Regular KB rule or fact.
    Rule(RuleId, Substitution),
    /// Occurrence (always a ground fact — no body).
    Occurrence(OccurrenceId, Substitution),
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
}

impl Default for ResolveConfig {
    fn default() -> Self {
        Self {
            max_depth: 100,
            max_solutions: 0,
            simplify: false,
        }
    }
}

// ── Solution ────────────────────────────────────────────────────

/// A successful resolution result: variable bindings collected during proof.
///
/// The substitution is always flat (path-compressed) — use `subst.resolve_with_term(vid)`
/// directly, no `walk` needed.
///
/// `residual` contains delayed goals that could not be resolved (e.g., a
/// `nonvar(?x)` where `?x` was never bound by any other goal).
pub struct Solution {
    pub subst: Substitution,
    pub residual: Vec<TermId>,
}

// ── EqChange ────────────────────────────────────────────────────

/// Record of an equational rewrite step.
#[allow(dead_code)]
pub struct EqChange {
    pub rule_id: RuleId,
    pub original: TermId,
    pub rewritten: TermId,
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
        original_goal: TermId,
        candidates: Vec<Candidate>,
        next: usize,
        any_delayed: bool,
        child_solutions: usize,
        /// Seen ground goals: reified goal TermIds from yielded solutions.
        /// Hash-consing guarantees same structure = same TermId.
        seen_goals: HashSet<TermId>,
    },
}

/// A choice point on the explicit stack.
#[derive(Clone)]
struct Frame {
    goals: Vec<TermId>,
    subst: Substitution,
    depth: usize,
    state: FrameState,
    /// Antecedents assumed under a `forall_impl` discharge that landed in
    /// this frame's goal stream. Consulted as zero-body facts during the
    /// proof of the consequent goals; popped when the frame pops. WI-108.
    assumed_facts: Vec<TermId>,
}

/// Result of a single step in the search loop.
enum StepResult {
    /// Keep stepping.
    Continue,
    /// A solution has been found; yield it.
    YieldSolution(Solution),
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

    /// Execute one step of the search. Returns `None` when the stack is
    /// empty (no more work).
    fn step(&mut self, kb: &mut KnowledgeBase) -> Option<StepResult> {
        let frame = self.stack.last_mut()?;
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
                let sol = Solution {
                    subst: frame.subst.clone(),
                    residual: frame.goals.clone(),
                };
                self.stack.pop();
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

        let goal = frame.goals[0];

        // 3.4 __pop_assumption(N) — scoping marker emitted by
        // step_forall_impl. Pops N entries off the frame's
        // assumed_facts and consumes the marker. WI-108.
        if let Some(n) = Self::pop_assumption_arg(kb, goal) {
            let f = self.stack.last_mut().unwrap();
            let drop_from = f.assumed_facts.len().saturating_sub(n);
            f.assumed_facts.truncate(drop_from);
            f.goals.remove(0);
            f.depth += 1;
            f.state = FrameState::Init { delay_mode: delay_mode.reset() };
            return Some(StepResult::Continue);
        }

        // 3.5 forall_impl(binders, antecedents, consequent) — hereditary
        // Harrop discharge. Skolemise binders, push antecedents as scoped
        // assumptions, prepend consequents to the goal stream. WI-108.
        if Self::is_forall_impl(kb, goal, &frame.subst) {
            return self.step_forall_impl(kb, goal, depth, delay_mode);
        }

        // 4. Builtin goal
        if let Some(tag) = kb.get_builtin(goal) {
            // NAF needs sub-resolution context — handle it specially
            if tag == BuiltinTag::Not {
                return self.step_naf(kb, goal, depth, delay_mode);
            }
            // HO predicate application: replace goal with the applied term
            if tag == BuiltinTag::HoApply {
                if let Some(applied) = self.resolve_ho_apply(kb, goal, &frame.subst) {
                    let f = self.stack.last_mut().unwrap();
                    f.goals[0] = applied;
                    f.state = FrameState::Init { delay_mode };
                    return Some(StepResult::Continue);
                } else {
                    // Predicate var still unbound — fail (can't apply unbound predicate)
                    self.stack.pop();
                    return Some(StepResult::Continue);
                }
            }
            // Bypasses execute_builtin: push_choice's effect is on the
            // choice-point stack, not on σ — like Not/HoApply.
            if tag == BuiltinTag::PushChoice {
                if let Some((goal_a, goal_b)) =
                    Self::resolve_push_choice_args(kb, goal, &frame.subst)
                {
                    let candidates = vec![
                        Candidate::Continuation(vec![goal_a]),
                        Candidate::Continuation(vec![goal_b]),
                    ];
                    let f = self.stack.last_mut().unwrap();
                    f.state = FrameState::ChoicePoint {
                        delay_mode,
                        original_goal: goal,
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
            match kb.execute_builtin(tag, goal, &frame.subst) {
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
                        new_subst.bind_value(*var, val.clone());
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
                                // Only goal — residualize
                                let sol = Solution {
                                    subst: frame.subst.clone(),
                                    residual: vec![goal],
                                };
                                self.stack.pop();
                                self.record_solution_in_ancestors();
                                return Some(StepResult::YieldSolution(sol));
                            } else {
                                // Rotate to end, enter Delayed mode
                                let mut rotated: Vec<TermId> = frame.goals[1..].to_vec();
                                rotated.push(goal);
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
                            let mut rotated: Vec<TermId> = frame.goals[1..].to_vec();
                            rotated.push(goal);
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

        // 5. Check OccurrenceStore for expression-typed goals
        let mut candidates: Vec<Candidate> = Vec::new();
        let mut occurrence_terms: HashSet<TermId> = HashSet::new();

        if let Term::Fn { functor, .. } = kb.terms.get(goal) {
            let functor = *functor;
            let occ_ids = kb.occurrences.by_functor(functor);
            for &occ_id in occ_ids {
                if !kb.occurrences.is_expr(occ_id) { continue; }
                let head = kb.occurrences.term(occ_id);
                if let Some(subst) = kb.match_term(goal, head) {
                    candidates.push(Candidate::Occurrence(occ_id, subst));
                    occurrence_terms.insert(head);
                }
            }
        }

        // 6. Non-builtin goal → query discrimination tree.
        // Cache ground goals (no variables) — their TermId is stable and
        // may recur. Goals with variables get unique fresh VarIds so
        // caching them wastes memory without hits.
        let is_ground = kb.collect_vars(goal).is_empty();
        let rule_candidates = if is_ground {
            if let Some(cached) = self.query_cache.get(&goal) {
                cached.clone()
            } else {
                let mut rc = kb.query(goal);
                if self.config.simplify {
                    let has_non_eq = rc.iter().any(|(rid, _)| !kb.is_equation(*rid));
                    if !has_non_eq {
                        let (rewritten, changes) = kb.apply_eq_rules(goal, 100);
                        if !changes.is_empty() {
                            rc = kb.query(rewritten);
                        }
                    }
                }
                rc.retain(|(rid, _)| !kb.is_equation(*rid));
                self.query_cache.insert(goal, rc.clone());
                rc
            }
        } else {
            let mut rc = kb.query(goal);
            if self.config.simplify {
                let has_non_eq = rc.iter().any(|(rid, _)| !kb.is_equation(*rid));
                if !has_non_eq {
                    let (rewritten, changes) = kb.apply_eq_rules(goal, 100);
                    if !changes.is_empty() {
                        rc = kb.query(rewritten);
                    }
                }
            }
            rc.retain(|(rid, _)| !kb.is_equation(*rid));
            rc
        };

        candidates.extend(rule_candidates.into_iter().map(|(rid, s)| Candidate::Rule(rid, s)));

        // Frame-scoped assumed facts (WI-108). Reify the goal through
        // the current substitution first so that goal-side flex vars
        // bound to rigids appear in their concrete form. Then try
        // unifying each assumed fact against the reified goal.
        let assumed = self.stack.last().unwrap().assumed_facts.clone();
        let frame_subst = self.stack.last().unwrap().subst.clone();
        let reified_goal = kb.reify(goal, &frame_subst);
        for assumed_fact in assumed {
            if let Some(subst) = kb.match_term(assumed_fact, reified_goal) {
                if !subst.is_contradiction() {
                    candidates.push(Candidate::Assumption(subst));
                }
            }
        }

        // Transition to ChoicePoint
        let f = self.stack.last_mut().unwrap();
        f.state = FrameState::ChoicePoint {
            delay_mode,
            original_goal: goal,
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
        let mut new_goals: Vec<TermId> = skolemized_consequents;
        if n_assumed > 0 {
            let marker = Self::make_pop_assumption_marker(kb, n_assumed);
            new_goals.push(marker);
        }
        new_goals.extend(frame.goals[1..].iter().copied());
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
        let pred = kb.walk(pos_args[0], subst);
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
        let pred_tid = kb.walk(pos_args[0], subst);
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
        goal: TermId,
        depth: usize,
        delay_mode: DelayMode,
    ) -> Option<StepResult> {
        let frame = self.stack.last().unwrap();
        let goals = frame.goals.clone();
        let subst = frame.subst.clone();

        let inner_goal = kb.builtin_first_arg(goal);
        let reified = kb.reify(inner_goal, &subst);

        // Groundness check: NAF on non-ground goals would be unsound
        match kb.is_ground(reified, &Substitution::new()) {
            GroundCheck::HasVar => {
                // Delay — same mechanism as other builtins
                match delay_mode {
                    DelayMode::Normal => {
                        if goals.len() == 1 {
                            let sol = Solution {
                                subst,
                                residual: vec![goal],
                            };
                            self.stack.pop();
                            self.record_solution_in_ancestors();
                            return Some(StepResult::YieldSolution(sol));
                        } else {
                            let mut rotated: Vec<TermId> = goals[1..].to_vec();
                            rotated.push(goal);
                            let f = self.stack.last_mut().unwrap();
                            f.goals = rotated;
                            f.depth = depth + 1;
                            f.state = FrameState::Init {
                                delay_mode: DelayMode::Delayed { consecutive_delays: 1 },
                            };
                            return Some(StepResult::Continue);
                        }
                    }
                    DelayMode::Delayed { consecutive_delays } => {
                        let mut rotated: Vec<TermId> = goals[1..].to_vec();
                        rotated.push(goal);
                        let f = self.stack.last_mut().unwrap();
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
            }
            GroundCheck::Ground => {
                // Sub-resolution: check if the inner goal has any solution
                let remaining_depth = self.config.max_depth.saturating_sub(depth);
                let sub_config = ResolveConfig {
                    max_depth: remaining_depth,
                    max_solutions: 1,
                    simplify: self.config.simplify,
                };
                let sub_stream = kb.resolve_lazy(&[reified], &sub_config);
                let has_solution = sub_stream.split_first(kb).is_some();

                if has_solution {
                    // Inner goal succeeded → not() FAILS — backtrack
                    self.stack.pop();
                    return Some(StepResult::Continue);
                } else {
                    // Inner goal has no solutions → not() SUCCEEDS
                    let new_goals = goals[1..].to_vec();
                    let new_delay = delay_mode.reset();
                    let f = self.stack.last_mut().unwrap();
                    f.goals = new_goals;
                    f.subst = subst;
                    f.depth = depth + 1;
                    f.state = FrameState::Init { delay_mode: new_delay };
                    return Some(StepResult::Continue);
                }
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
                    *original_goal,
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
                let mut rotated: Vec<TermId> = goals[1..].to_vec();
                rotated.push(original_goal);
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
            let mut new_goals = body;
            new_goals.extend_from_slice(&frame.goals[1..]);
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
            Candidate::Occurrence(_occ_id, subst) => (None, subst),
            Candidate::Rule(rid, subst) => (Some(rid), subst),
            Candidate::Assumption(subst) => (None, subst),
            Candidate::Continuation(_) => unreachable!("handled above"),
        };

        let body = opt_rid.map_or(Vec::new(), |rid| kb.rule_body(rid).to_vec());

        let frame = self.stack.last().unwrap();

        if body.is_empty() {
            // Ground fact (occurrence or rule with empty body)
            let remaining = kb.apply_subst_each(&frame.goals[1..], &tree_subst);
            let mut merged = frame.subst.clone();
            // bind_compressed wants (VarId, TermId) pairs; filter to the
            // Value::Term subset — path compression is TermId-only.
            let term_pairs: Vec<(VarId, TermId)> = tree_subst.iter_terms().collect();
            merged.bind_compressed(term_pairs.into_iter(), &kb.terms);
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
            let (fresh_body, answer_links) = kb.with_fresh_vars(rid, &tree_subst);
            let remaining = kb.apply_subst_each(&frame.goals[1..], &tree_subst);

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

            // Pre-check: delay propagation on caller vars
            if !caller_fresh_vars.is_empty()
                && kb.body_builtins_delay_on_caller_vars(&fresh_body, &caller_fresh_vars, &merged)
            {
                let f = self.stack.last_mut().unwrap();
                match &mut f.state {
                    FrameState::ChoicePoint { any_delayed, .. } => *any_delayed = true,
                    _ => unreachable!(),
                }
                return Some(StepResult::Continue);
            }

            let mut new_goals = fresh_body;
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

    /// Check if a solution is a duplicate by reifying the nearest ancestor
    /// ChoicePoint's goal through the solution substitution. The reified
    /// goal is a ground TermId (hash-consed) — same structure = same id.
    fn is_duplicate_projection(&mut self, kb: &mut KnowledgeBase, sol: &Solution) -> bool {
        for frame in self.stack.iter_mut().rev() {
            if let FrameState::ChoicePoint { original_goal, seen_goals, .. } = &mut frame.state {
                let reified = kb.reify(*original_goal, &sol.subst);
                return !seen_goals.insert(reified);
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

// ── SLD Resolution ──────────────────────────────────────────────

impl KnowledgeBase {
    /// Create a lazy search stream for the given goals.
    pub fn resolve_lazy(&self, goals: &[TermId], config: &ResolveConfig) -> SearchStream {
        let initial_frame = Frame {
            goals: goals.to_vec(),
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
            },
            query_cache: HashMap::new(),
        }
    }

    /// Resolve a list of goals using SLD resolution.
    ///
    /// Returns all solutions (up to `config.max_solutions`) that satisfy all
    /// goals simultaneously. Each solution contains variable bindings from
    /// the original query variables to ground terms.
    pub fn resolve(&mut self, goals: &[TermId], config: &ResolveConfig) -> Vec<Solution> {
        let mut stream = self.resolve_lazy(goals, config);
        let mut solutions = Vec::new();
        while let Some((sol, rest)) = stream.split_first(self) {
            solutions.push(sol);
            if config.max_solutions > 0 && solutions.len() >= config.max_solutions {
                break;
            }
            stream = rest;
        }
        solutions
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

        let eq_sym = self.intern("eq");
        let pattern = self.alloc(Term::Fn {
            functor: eq_sym,
            pos_args: SmallVec::from_slice(&[current, result_var]),
            named_args: SmallVec::new(),
        });

        let candidates = self.query(pattern);

        for (rid, tree_subst) in candidates {
            if !self.is_equation(rid) {
                continue;
            }

            // Reify the result variable to get the RHS
            let rhs = self.reify(result_var, &tree_subst);

            changes.push(EqChange {
                rule_id: rid,
                original: current,
                rewritten: rhs,
            });

            // Continue rewriting the result
            let (final_term, more_changes) = self.apply_eq_rules(rhs, fuel - 1);
            changes.extend(more_changes);
            return (final_term, changes);
        }

        (current, changes)
    }

    // ── Builtin execution ──────────────────────────────────────

    /// Dispatch a builtin by tag. The goal has already been identified as a
    /// builtin; this evaluates it against the current substitution.
    fn execute_builtin(
        &mut self,
        tag: BuiltinTag,
        goal: TermId,
        answer_subst: &Substitution,
    ) -> BuiltinResult {
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
            BuiltinTag::ResolveSortInstParam => self.builtin_resolve_sort_inst_param(goal, answer_subst),
            BuiltinTag::Scope => self.builtin_scope(goal, answer_subst),
            BuiltinTag::Kind => self.builtin_kind(goal, answer_subst),
            BuiltinTag::FieldAccess => self.builtin_field_access(goal, answer_subst),
            BuiltinTag::Eq => self.builtin_eq(goal, answer_subst),
            BuiltinTag::Neq => self.builtin_neq(goal, answer_subst),
            BuiltinTag::Gt => self.builtin_cmp(goal, answer_subst, |ord| ord == std::cmp::Ordering::Greater),
            BuiltinTag::Lt => self.builtin_cmp(goal, answer_subst, |ord| ord == std::cmp::Ordering::Less),
            BuiltinTag::Gte => self.builtin_cmp(goal, answer_subst, |ord| ord != std::cmp::Ordering::Less),
            BuiltinTag::Lte => self.builtin_cmp(goal, answer_subst, |ord| ord != std::cmp::Ordering::Greater),
            BuiltinTag::Add => self.builtin_arith(goal, answer_subst, |a, b| a + b, |a, b| a + b, |a, b| a + b),
            BuiltinTag::Sub => self.builtin_arith(goal, answer_subst, |a, b| a - b, |a, b| a - b, |a, b| a - b),
            BuiltinTag::Mul => self.builtin_arith(goal, answer_subst, |a, b| a * b, |a, b| a * b, |a, b| a * b),
            BuiltinTag::ToBigInt => self.builtin_to_bigint(goal, answer_subst),
            BuiltinTag::ToInt => self.builtin_to_int(goal, answer_subst),
            // Occurrence builtins — stubs returning Delay until Phase 2
            BuiltinTag::OccurrenceTerm
            | BuiltinTag::OccurrenceSpan
            | BuiltinTag::OccurrenceOwner
            | BuiltinTag::SubOccurrences => BuiltinResult::Delay,
        }
    }

    /// `nonvar(?x)`: succeeds if `?x` is bound to a non-variable after walking.
    fn builtin_nonvar(&self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let arg = self.builtin_first_arg(goal);
        let walked = self.walk(arg, subst);
        match self.terms.get(walked) {
            Term::Var(_) => BuiltinResult::Delay,
            _ => BuiltinResult::Success,
        }
    }

    /// `ground(?x)`: succeeds if `?x` is fully ground (no unbound variables anywhere).
    fn builtin_ground(&self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let arg = self.builtin_first_arg(goal);
        match self.is_ground(arg, subst) {
            GroundCheck::Ground => BuiltinResult::Success,
            GroundCheck::HasVar => BuiltinResult::Delay,
        }
    }

    /// Recursive groundness check: walk the term, then check all subterms.
    fn is_ground(&self, term: TermId, subst: &Substitution) -> GroundCheck {
        let walked = self.walk(term, subst);
        match self.terms.get(walked) {
            Term::Var(_) => GroundCheck::HasVar,
            Term::Const(_) | Term::Ref(_) | Term::Bottom | Term::Ident(_) => GroundCheck::Ground,
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

    fn builtin_qualified_name(&mut self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let sym_arg = self.builtin_first_arg(goal);
        let result_arg = self.builtin_second_arg(goal);
        let walked_sym = self.walk(sym_arg, subst);
        match self.terms.get(walked_sym).clone() {
            Term::Ref(sym) | Term::Ident(sym) => {
                let name = self.symbol_qualified_name(sym);
                let str_term = self.alloc(Term::Const(super::term::Literal::String(name)));
                let walked_result = self.walk(result_arg, subst);
                match self.terms.get(walked_result) {
                    Term::Var(Var::Global(vid)) => {
                        let vid = *vid;
                        let mut extra = Substitution::new();
                        extra.bind(vid, str_term);
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
        let walked_sym = self.walk(sym_arg, subst);
        match self.terms.get(walked_sym).clone() {
            Term::Ref(sym) | Term::Ident(sym) => {
                let full = self.symbols.resolve(sym);
                let short = full.rsplit('.').next().unwrap_or(full).to_string();
                let str_term = self.alloc(Term::Const(super::term::Literal::String(short)));
                let walked_result = self.walk(result_arg, subst);
                match self.terms.get(walked_result) {
                    Term::Var(Var::Global(vid)) => {
                        let vid = *vid;
                        let mut extra = Substitution::new();
                        extra.bind(vid, str_term);
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
        let walked_name = self.walk(name_arg, subst);
        match self.terms.get(walked_name).clone() {
            Term::Const(super::term::Literal::String(name)) => {
                // Look up the symbol by qualified name (read-only)
                match self.symbols.by_qualified_name.get(&name).copied() {
                    Some(sym) => {
                        let ref_term = self.alloc(Term::Ref(sym));
                        let walked_result = self.walk(result_arg, subst);
                        match self.terms.get(walked_result) {
                            Term::Var(Var::Global(vid)) => {
                                let vid = *vid;
                                let mut extra = Substitution::new();
                                extra.bind(vid, ref_term);
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
    fn builtin_is_entity_of(&self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let sub_arg = self.builtin_first_arg(goal);
        let sup_arg = self.builtin_second_arg(goal);
        let walked_sub = self.walk(sub_arg, subst);
        let walked_sup = self.walk(sup_arg, subst);
        match (self.terms.get(walked_sub), self.terms.get(walked_sup)) {
            (Term::Var(_), _) | (_, Term::Var(_)) => BuiltinResult::Delay,
            _ => {
                if self.is_entity_of(walked_sub, walked_sup) {
                    BuiltinResult::Success
                } else {
                    BuiltinResult::Failure
                }
            }
        }
    }

    /// `extract_sort_ref(?inst, ?result)`: given a term like `Eq[T = Int]` (represented as
    /// `ParameterizedType(Eq(), T=Int())`) or a simple `Ref(Eq)`, extract the sort symbol
    /// and bind `?result` to `Ref(sort_sym)`. Delays if `?inst` is unbound.
    fn builtin_extract_sort(&mut self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let inst_arg = self.builtin_first_arg(goal);
        let result_arg = self.builtin_second_arg(goal);
        let walked_inst = self.walk(inst_arg, subst);

        // Extract the sort symbol from various term shapes
        let sort_sym = match self.terms.get(walked_inst).clone() {
            Term::Var(_) => return BuiltinResult::Delay,
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
                let ref_term = self.alloc(Term::Ref(sym));
                let walked_result = self.walk(result_arg, subst);
                match self.terms.get(walked_result) {
                    Term::Var(Var::Global(vid)) => {
                        let vid = *vid;
                        let mut extra = Substitution::new();
                        extra.bind(vid, ref_term);
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

        let walked_inst = self.walk(inst_arg, subst);
        let walked_param = self.walk(param_arg, subst);

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
                let walked_value = self.walk(value_arg, subst);
                match self.terms.get(walked_value) {
                    Term::Var(Var::Global(vid)) => {
                        let vid = *vid;
                        let mut extra = Substitution::new();
                        extra.bind(vid, val);
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

    /// Try to bind a result argument to a computed value.
    /// If the result is an unbound Var, bind it. If already bound, check equality.
    fn try_bind_result(&self, result_arg: TermId, value: TermId, subst: &Substitution) -> BuiltinResult {
        let walked_result = self.walk(result_arg, subst);
        match self.terms.get(walked_result) {
            Term::Var(Var::Global(vid)) => {
                let vid = *vid;
                let mut extra = Substitution::new();
                extra.bind(vid, value);
                BuiltinResult::SuccessWithBindings(extra)
            }
            _ => {
                if walked_result == value {
                    BuiltinResult::Success
                } else {
                    BuiltinResult::Failure
                }
            }
        }
    }

    // ── Equality and comparison builtins ─────────────────────

    /// `eq(?a, ?b)` — structural equality after walking. Succeeds if both
    /// args resolve to the same TermId (hash-consed identity = structural equality).
    /// Delays only on flex (`Var::Global`); rigid vars compare by TermId
    /// identity (hash-consing ensures `Rigid(a) == Rigid(a)`).
    fn builtin_eq(&self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let a = self.walk(self.builtin_first_arg(goal), subst);
        let b = self.walk(self.builtin_second_arg(goal), subst);
        if Self::is_flex(self.terms.get(a)) || Self::is_flex(self.terms.get(b)) {
            return BuiltinResult::Delay;
        }
        if a == b { BuiltinResult::Success } else { BuiltinResult::Failure }
    }

    /// `neq(?a, ?b)` — structural inequality after walking.
    fn builtin_neq(&self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let a = self.walk(self.builtin_first_arg(goal), subst);
        let b = self.walk(self.builtin_second_arg(goal), subst);
        if Self::is_flex(self.terms.get(a)) || Self::is_flex(self.terms.get(b)) {
            return BuiltinResult::Delay;
        }
        if a != b { BuiltinResult::Success } else { BuiltinResult::Failure }
    }

    fn is_flex(t: &Term) -> bool {
        matches!(t, Term::Var(Var::Global(_)))
    }

    /// Generic comparison builtin for gt/lt/gte/lte.
    /// Compares Int or Float constants; delays if unbound, fails on type mismatch.
    fn builtin_cmp(
        &self,
        goal: TermId,
        subst: &Substitution,
        pred: impl Fn(std::cmp::Ordering) -> bool,
    ) -> BuiltinResult {
        let a = self.walk(self.builtin_first_arg(goal), subst);
        let b = self.walk(self.builtin_second_arg(goal), subst);
        match (self.terms.get(a), self.terms.get(b)) {
            (Term::Var(_), _) | (_, Term::Var(_)) => BuiltinResult::Delay,
            (Term::Const(super::term::Literal::Int(x)),
             Term::Const(super::term::Literal::Int(y))) => {
                if pred(x.cmp(y)) { BuiltinResult::Success } else { BuiltinResult::Failure }
            }
            (Term::Const(super::term::Literal::BigInt(x)),
             Term::Const(super::term::Literal::BigInt(y))) => {
                if pred(x.cmp(y)) { BuiltinResult::Success } else { BuiltinResult::Failure }
            }
            (Term::Const(super::term::Literal::Float(x)),
             Term::Const(super::term::Literal::Float(y))) => {
                if pred(x.cmp(y)) { BuiltinResult::Success } else { BuiltinResult::Failure }
            }
            _ => BuiltinResult::Failure,
        }
    }

    // ── Arithmetic builtins ──────────────────────────────────

    /// Generic arithmetic builtin for add/sub/mul.
    /// If 2 positional args: used as an equation builtin (reduces term to result).
    /// If 3 positional args: binds the 3rd arg to the computed result.
    /// Operates on Int, BigInt, or Float constants.
    fn builtin_arith(
        &mut self,
        goal: TermId,
        subst: &Substitution,
        int_op: impl Fn(i64, i64) -> i64,
        bigint_op: impl Fn(&num_bigint::BigInt, &num_bigint::BigInt) -> num_bigint::BigInt,
        float_op: impl Fn(f64, f64) -> f64,
    ) -> BuiltinResult {
        let (arg_a, arg_b, result_arg) = match self.terms.get(goal) {
            Term::Fn { pos_args, .. } if pos_args.len() >= 3 => {
                (pos_args[0], pos_args[1], Some(pos_args[2]))
            }
            Term::Fn { pos_args, .. } if pos_args.len() >= 2 => {
                (pos_args[0], pos_args[1], None)
            }
            _ => return BuiltinResult::Failure,
        };

        let a = self.walk(arg_a, subst);
        let b = self.walk(arg_b, subst);

        // Extract numeric values first (immutable borrow), then alloc (mutable).
        enum NumPair { Ints(i64, i64), BigInts(num_bigint::BigInt, num_bigint::BigInt), Floats(f64, f64) }
        let pair = match (self.terms.get(a), self.terms.get(b)) {
            (Term::Var(_), _) | (_, Term::Var(_)) => return BuiltinResult::Delay,
            (Term::Const(super::term::Literal::Int(x)),
             Term::Const(super::term::Literal::Int(y))) => NumPair::Ints(*x, *y),
            (Term::Const(super::term::Literal::BigInt(x)),
             Term::Const(super::term::Literal::BigInt(y))) => NumPair::BigInts(x.clone(), y.clone()),
            (Term::Const(super::term::Literal::Float(x)),
             Term::Const(super::term::Literal::Float(y))) => NumPair::Floats(x.0, y.0),
            _ => return BuiltinResult::Failure,
        };

        let result_term = match pair {
            NumPair::Ints(x, y) => {
                self.alloc(Term::Const(super::term::Literal::Int(int_op(x, y))))
            }
            NumPair::BigInts(x, y) => {
                self.alloc(Term::Const(super::term::Literal::BigInt(bigint_op(&x, &y))))
            }
            NumPair::Floats(x, y) => {
                use ordered_float::OrderedFloat;
                self.alloc(Term::Const(super::term::Literal::Float(
                    OrderedFloat(float_op(x, y)),
                )))
            }
        };

        match result_arg {
            Some(r) => self.try_bind_result(r, result_term, subst),
            // 2-arg form: succeeds as a ground test (both args are concrete constants)
            None => BuiltinResult::Success,
        }
    }

    // ── Conversion builtins ────────────────────────────────────

    /// `to_bigint(?n, ?result)` — convert Int to BigInt.
    fn builtin_to_bigint(&mut self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let arg = self.walk(self.builtin_first_arg(goal), subst);
        let result_arg = self.builtin_second_arg(goal);
        match self.terms.get(arg) {
            Term::Var(_) => BuiltinResult::Delay,
            Term::Const(super::term::Literal::Int(n)) => {
                let n = *n;
                let big = self.alloc(Term::Const(super::term::Literal::BigInt(
                    num_bigint::BigInt::from(n),
                )));
                self.try_bind_result(result_arg, big, subst)
            }
            Term::Const(super::term::Literal::BigInt(_)) => {
                // Already BigInt — pass through
                self.try_bind_result(result_arg, arg, subst)
            }
            _ => BuiltinResult::Failure,
        }
    }

    /// `to_int(?n, ?result)` — convert BigInt to Int. Wraps in some/none.
    fn builtin_to_int(&mut self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let arg = self.walk(self.builtin_first_arg(goal), subst);
        let result_arg = self.builtin_second_arg(goal);
        match self.terms.get(arg).clone() {
            Term::Var(_) => BuiltinResult::Delay,
            Term::Const(super::term::Literal::BigInt(n)) => {
                use std::convert::TryFrom;
                let result = if let Ok(small) = i64::try_from(&n) {
                    let int_term = self.alloc(Term::Const(super::term::Literal::Int(small)));
                    super::load::build_some(self, int_term)
                } else {
                    super::load::build_none(self)
                };
                self.try_bind_result(result_arg, result, subst)
            }
            Term::Const(super::term::Literal::Int(_)) => {
                // Already Int — wrap in some
                let result = super::load::build_some(self, arg);
                self.try_bind_result(result_arg, result, subst)
            }
            _ => BuiltinResult::Failure,
        }
    }

    /// `scope(?sym, ?result)` — if `?sym` is bound to a Ref or Fn, bind `?result`
    /// to the enclosing scope term (Fn). Fails if scope is _global (top-level).
    fn builtin_scope(&mut self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let sym_arg = self.builtin_first_arg(goal);
        let result_arg = self.builtin_second_arg(goal);

        let walked_sym = self.walk(sym_arg, subst);
        // Extract the symbol from Ref or Fn term
        let sym = match self.terms.get(walked_sym) {
            Term::Var(_) => return BuiltinResult::Delay,
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
                self.try_bind_result(result_arg, scope_tid, subst)
            }
            _ => BuiltinResult::Failure,
        }
    }

    /// `kind(?sym, ?result)` — if `?sym` is bound to a Ref, bind `?result`
    /// to a string describing the symbol's kind ("Sort", "Entity", etc.).
    fn builtin_kind(&mut self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let sym_arg = self.builtin_first_arg(goal);
        let result_arg = self.builtin_second_arg(goal);

        let walked_sym = self.walk(sym_arg, subst);
        let sym = match self.terms.get(walked_sym) {
            Term::Var(_) => return BuiltinResult::Delay,
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
                    crate::intern::SymbolKind::Namespace => "Namespace",
                    crate::intern::SymbolKind::Fact => "Fact",
                    crate::intern::SymbolKind::Rule => "Rule",
                    crate::intern::SymbolKind::Constraint => "Constraint",
                    crate::intern::SymbolKind::Param => "Param",
                    crate::intern::SymbolKind::Field => "Field",
                    crate::intern::SymbolKind::Goal => "Goal",
                }
            }
            _ => return BuiltinResult::Failure,
        };

        let kind_term = self.alloc(Term::Const(super::term::Literal::String(kind_str.to_owned())));
        self.try_bind_result(result_arg, kind_term, subst)
    }

    /// `field_access(?object, ?field, ?result)` — dot projection builtin.
    ///
    /// Two dispatch modes based on the object term:
    /// 1. Entity instance: object is `Fn { functor, named_args, .. }` where functor
    ///    is in the `entity_fields` registry → extract the named field from args.
    /// 2. Sort component: object is `Fn { functor, .. }` where functor is a sort →
    ///    look up field in the sort's scope via qualified name.
    ///
    /// When the goal has only 2 args (from desugared `?x.y`), the builtin
    /// cannot bind a result — it succeeds only for structural matching.
    fn builtin_field_access(&mut self, goal: TermId, subst: &Substitution) -> BuiltinResult {
        let (obj_arg, field_arg, result_arg) = match self.terms.get(goal) {
            Term::Fn { pos_args, .. } if pos_args.len() >= 3 => {
                (pos_args[0], pos_args[1], Some(pos_args[2]))
            }
            Term::Fn { pos_args, .. } if pos_args.len() >= 2 => {
                (pos_args[0], pos_args[1], None)
            }
            _ => return BuiltinResult::Failure,
        };

        let walked_obj = self.walk(obj_arg, subst);
        let walked_field = self.walk(field_arg, subst);

        // Extract field symbol from Ref, Ident, or Fn
        let field_sym = match self.terms.get(walked_field) {
            Term::Ref(s) | Term::Ident(s) => *s,
            Term::Fn { functor, .. } => *functor,
            Term::Var(_) => return BuiltinResult::Delay,
            _ => return BuiltinResult::Failure,
        };

        // Object must be a bound Fn term
        let (functor, named_args) = match self.terms.get(walked_obj) {
            Term::Var(_) => return BuiltinResult::Delay,
            Term::Fn { functor, named_args, .. } => (*functor, named_args.clone()),
            _ => return BuiltinResult::Failure,
        };

        // Get the field's short name for matching (owned to avoid borrow conflicts)
        let field_name = self.symbols.name(field_sym).to_owned();

        // Dispatch 1: Entity field access — functor is in entity_fields registry
        if self.entity_fields.contains_key(&functor) {
            // Look up by short name match in named_args
            for &(arg_sym, arg_val) in named_args.iter() {
                if self.symbols.name(arg_sym) == field_name {
                    return self.bind_or_succeed(result_arg, arg_val, subst);
                }
            }
            return BuiltinResult::Failure;
        }

        // Dispatch 2: Sort component access — look up field in functor's scope
        let functor_qname = match self.symbols.get(functor) {
            crate::intern::SymbolDef::Resolved { qualified_name, .. } => qualified_name.clone(),
            _ => return BuiltinResult::Failure,
        };
        let target_qname = format!("{}.{}", functor_qname, field_name);
        if let Some(&resolved_sym) = self.symbols.by_qualified_name.get(&target_qname) {
            // Found the component — return as nullary Fn for sorts/entities, Ref otherwise
            let result_term = match self.symbols.get(resolved_sym) {
                crate::intern::SymbolDef::Resolved { kind, .. }
                    if matches!(kind, crate::intern::SymbolKind::Sort | crate::intern::SymbolKind::Entity) =>
                {
                    self.make_name_term_from_sym(resolved_sym)
                }
                _ => self.alloc(Term::Ref(resolved_sym)),
            };
            return self.bind_or_succeed(result_arg, result_term, subst);
        }

        BuiltinResult::Failure
    }

    /// Bind a value to an optional result arg, or succeed if no result arg.
    fn bind_or_succeed(&self, result_arg: Option<TermId>, value: TermId, subst: &Substitution) -> BuiltinResult {
        match result_arg {
            Some(ra) => self.try_bind_result(ra, value, subst),
            None => BuiltinResult::Success,
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

    /// Check if a builtin would delay given the current substitution (read-only).
    fn builtin_would_delay(&self, tag: BuiltinTag, goal: TermId, subst: &Substitution) -> bool {
        match tag {
            BuiltinTag::Not => {
                let inner = self.builtin_first_arg(goal);
                // NAF delays if inner goal is not ground after applying subst
                matches!(self.is_ground(inner, subst), GroundCheck::HasVar)
            }
            _ => {
                let arg = self.builtin_first_arg(goal);
                let walked = self.walk(arg, subst);
                matches!(self.terms.get(walked), Term::Var(_))
            }
        }
    }

    /// Check if any builtin in a rule body would delay on a caller-originated
    /// variable (one that came from the query via answer_links).
    ///
    /// If a builtin delays on an internal variable (created fresh for this rule),
    /// other body goals may bind it — that's fine, no propagation needed.
    /// But if it delays on a caller variable, the whole rule should delay.
    fn body_builtins_delay_on_caller_vars(
        &self,
        body: &[TermId],
        caller_fresh_vars: &[VarId],
        subst: &Substitution,
    ) -> bool {
        for &goal in body {
            if let Some(tag) = self.get_builtin(goal) {
                // NAF handles delay via goal rotation at resolution time;
                // other body goals may bind vars before not() is retried.
                if tag == BuiltinTag::Not {
                    continue;
                }
                // PushChoice is a control primitive — it always fires
                // immediately at step_init, never delays. Variable args
                // become goals that delay in their own step if unbound.
                if tag == BuiltinTag::PushChoice {
                    continue;
                }
                if self.builtin_would_delay(tag, goal, subst) {
                    let arg = self.builtin_first_arg(goal);
                    let mut unbound = Vec::new();
                    self.collect_unbound_vars(arg, subst, &mut unbound);
                    if unbound.iter().any(|v| caller_fresh_vars.contains(v)) {
                        return true;
                    }
                }
            }
        }
        false
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
        assert_eq!(s.resolve_with_term(vid), Some(val));
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
        assert_eq!(s.resolve_with_term(vx), Some(val));
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
        assert_eq!(s.resolve_with_term(vx), Some(var_y));

        // y → z: should also compress x → z
        s.bind_compressed([(vy, var_z)], &kb.terms);
        assert_eq!(s.resolve_with_term(vy), Some(var_z));
        assert_eq!(s.resolve_with_term(vx), Some(var_z));

        // z → 99: should compress x → 99 and y → 99
        s.bind_compressed([(vz, val)], &kb.terms);
        assert_eq!(s.resolve_with_term(vz), Some(val));
        assert_eq!(s.resolve_with_term(vy), Some(val));
        assert_eq!(s.resolve_with_term(vx), Some(val));
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
        s.bind(vx, var_y);
        s.bind(vy, val);

        let result = kb.reify(term, &s);
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
        assert_eq!(results[0].subst.resolve_with_term(vx), Some(alice));
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
        assert_eq!(kb.reify(var_a, &results[0].subst), alice);
        assert_eq!(kb.reify(var_b, &results[0].subst), charlie);
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
            .map(|sol| kb.reify(var_w, &sol.subst))
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
        assert_eq!(changes[0].rewritten, four);
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
        assert_eq!(kb.reify(var_x, &results[0].subst), hello);
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
        assert_eq!(kb.reify(var_x, &results[0].subst), hello);
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
        assert_eq!(results[0].residual[0], goal);
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
        assert_eq!(results[0].subst.resolve_with_term(vx), Some(val));
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
        assert_eq!(kb.reify(var_a, &results[0].subst), val_42);
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
        assert_eq!(kb.reify(var_a, &results[0].subst), val_99);
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
        assert_eq!(sol.residual[0], goal);

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
        let r1 = kb.reify(var_w, &sol1.subst);

        let (sol2, stream) = stream.split_first(&mut kb).expect("second ancestor");
        let r2 = kb.reify(var_w, &sol2.subst);

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
        let resolved = solutions[0].subst.resolve_with_term(result_vid).expect("result should be bound");
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
        let resolved = solutions[0].subst.resolve_with_term(result_vid).expect("result should be bound");
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
        let resolved = solutions[0].subst.resolve_with_term(result_vid).expect("result should be bound");
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
        let result = kb.reify(var_x, &solutions[0].subst);
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
        let bound = solutions[0].subst.resolve_with_term(vx);
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
        let resolved = kb.reify(var_q, &solutions[0].subst);
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

        let config = ResolveConfig { max_depth: 20, max_solutions: 4, simplify: false };
        let solutions = kb.resolve(&[query], &config);

        assert_eq!(solutions.len(), 4, "should get 4 solutions");

        // Solution 0: nat(zero()) → ?x = zero()
        let r0 = kb.reify(var_x, &solutions[0].subst);
        assert_eq!(r0, zero_term, "first solution should be zero()");

        // Solution 1: nat(succ(zero())) → ?x = succ(zero())
        let r1 = kb.reify(var_x, &solutions[1].subst);
        match kb.get_term(r1) {
            Term::Fn { functor, pos_args, .. } => {
                assert_eq!(*functor, succ_sym);
                assert_eq!(pos_args.len(), 1);
                assert_eq!(pos_args[0], zero_term, "succ arg should be zero()");
            }
            other => panic!("expected succ(zero()), got {:?}", other),
        }

        // Solution 2: nat(succ(succ(zero()))) → ?x = succ(succ(zero()))
        let r2 = kb.reify(var_x, &solutions[2].subst);
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
        kb.assert_rule_debruijn(head, vec![body_a, body_b], sort, domain, None);

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
        let bound = kb.reify(var_q, &sols[0].subst);
        assert_eq!(bound, yes, "?q should resolve to \"yes\"");
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
        kb.assert_rule_debruijn(head, vec![body_l, body_r], sort, domain, None);

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

                kb.assert_rule_debruijn(head, body, sort, domain, None);

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
        kb.assert_rule_debruijn(p_head, vec![p_body], sort, domain, None);

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
        kb.assert_rule_debruijn(f_head, vec![f_body], sort, domain, None);

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
                let t = kb.reify(var_q, &sol.subst);
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
}

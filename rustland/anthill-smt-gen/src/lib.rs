//! anthill-smt-gen — emit SMT-LIB 2.6 from anthill knowledge bases.
//!
//! v0 scope: discharge a single linear-arithmetic obligation by
//! - declaring user-asserted fact fields as `Real` constants,
//! - translating one named rule's body to an SMT-LIB definition,
//! - asserting the negation of an upper bound on the rule's head,
//! - asking Z3 to prove `(check-sat) → unsat`.
//!
//! The first target is `safety::comm_delay_max` from the lf1
//! example: five linear arithmetic operations over five floats from
//! `LinkParameters` and `KinematicAssumptions`. If that round-trips,
//! scaling to the rest of the obligations (`step_distance_bound`,
//! `inductive_invariant`, full reachability) is mostly more of the
//! same machinery — quantifiers and induction get layered on top.
//!
//! Mapping reference: `docs/smtlib-forward-mapping.md`.

pub mod cache;
pub mod outcome;
pub mod policy;
pub mod tactic_emit;

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::extent::{BodiedRulePolicy, ExtentReadError};
use anthill_core::kb::node_occurrence::{materialize_from_handle, Expr, NodeOccurrence};
use anthill_core::kb::term::{Literal, Term, Var};
use anthill_core::kb::{KnowledgeBase, ProgramClause};

#[derive(Debug)]
pub struct SmtGenError {
    pub message: String,
}

impl SmtGenError {
    fn new(s: impl Into<String>) -> Self {
        Self { message: s.into() }
    }
}

/// Caller-supplied overrides forwarded to the SMT preamble.
#[derive(Debug, Clone, Default)]
pub struct ProofConfig {
    /// SMT-LIB logic, e.g. "QF_LRA". Defaults to the auto-detected one.
    pub logic: Option<String>,
    /// Emitted as `(set-option :timeout N)` before `(set-logic …)`.
    pub timeout_ms: Option<u32>,
    /// Anthill QN → SMT operator/identifier overrides (currently
    /// stored but not consulted; default mapping covers lf1).
    pub mapping: BTreeMap<String, String>,
    /// Optional Z3 tactic expression. When `Some`, the emitted
    /// document closes with `(check-sat-using <expr>)`; when `None`,
    /// with the canonical `(check-sat)`.
    pub tactic_expr: Option<String>,
    /// Emit `(set-option :produce-models true)` + `(get-model)`. The
    /// solver's model text becomes available for parsing into a
    /// `ProofCounterexample` fact when the verdict is `sat`. WI-099.
    pub produce_models: bool,
    /// Emit `(set-option :produce-unsat-cores true)` + `(get-unsat-core)`.
    /// Populates `ProofCore` for `unsat` verdicts. WI-099.
    pub produce_unsat_cores: bool,
    /// Emit `(set-option :produce-interpolants true)` + `(get-interpolants)`.
    /// Reserved — Z3's interpolant API takes additional setup; for now
    /// the flag wires the option through but the get-interpolants form
    /// is left as a follow-up. WI-099.
    pub produce_interpolants: bool,
    /// Pre-rendered SMT-LIB clauses to splice into the preamble as
    /// extra `(assert <clause>)` blocks. Each entry is the raw S-expr
    /// content (without the surrounding `(assert …)`). Used by the
    /// prove driver when a `proof X using Y by …` block fires —
    /// driver renders Y's body into clauses, hands them in here, and
    /// smt-gen injects them so Z3 has Y's claim as a hypothesis when
    /// discharging X. Smt-gen does not parse / validate these strings;
    /// it trusts the caller. Order is preserved.
    pub assumptions: Vec<String>,
    /// AbstractLift mode: when true, `process_body_goal` does NOT
    /// chase rule-call goals into their defining bodies. The call's
    /// vars stay free; ambient cited-rule lifts constrain them.
    /// Set by `dispatch_structured` for the conclude-clause discharge
    /// so the parent's body doesn't drag transitive nonlinear /
    /// fact-bound arithmetic into the consumer's preamble.
    pub abstract_body: bool,
}

/// One obligation to discharge: prove `<rule>(?result) ≤ <bound>`
/// for *every* binding of the rule's body. Translates to
/// `(assert (not (<= rule_result bound)))` + `(check-sat)` —
/// Z3 should answer `unsat`.
///
/// Matched against rules whose head is `<rule_name>(?result)` —
/// exactly one logic-variable arg, captured as the rule's "result".
#[derive(Debug, Clone)]
pub struct Obligation {
    /// Qualified name of the rule whose head's first arg is the
    /// expression we want bounded.
    pub rule_qn: String,
    /// Upper bound to prove.
    pub upper_bound: f64,
}

/// Emit a self-contained SMT-LIB document for one obligation.
/// The KB must already have the rule and any facts it depends on
/// loaded. Logic is `QF_LRA` (quantifier-free linear real
/// arithmetic) — decidable, fast.
pub fn emit_obligation(kb: &KnowledgeBase, obligation: &Obligation) -> Result<String, SmtGenError> {
    emit_obligation_with(kb, obligation, &ProofConfig::default())
}

/// Like `emit_obligation`, but with an explicit `ProofConfig` for
/// logic, timeout, or mapping overrides.
pub fn emit_obligation_with(
    kb: &KnowledgeBase,
    obligation: &Obligation,
    config: &ProofConfig,
) -> Result<String, SmtGenError> {
    let mut emitter = Emitter::new(kb);
    emitter.collect_rule(&obligation.rule_qn)?;
    emitter.collect_facts_for_referenced_entities()?;
    Ok(emitter.render_upper_bound_with(obligation, config))
}

/// Emit a satisfiability check for a rule's body, framed as a
/// proof obligation: if Z3 reports `unsat`, the body's joint
/// constraints can't all hold (typically meaning a "violation rule"
/// is vacuous → the safety property holds). If `sat`, Z3 found a
/// counterexample.
///
/// Use this for rules that encode the negation of a property — e.g.
/// `lower_bound_violation` whose body is the inductive
/// preconditions plus `lt(d_next, d_min)`. `unsat` proves no
/// (d_prev, step) can drive d_next below d_min.
pub fn emit_satisfiability_check(kb: &KnowledgeBase, rule_qn: &str) -> Result<String, SmtGenError> {
    emit_satisfiability_check_with(kb, rule_qn, &ProofConfig::default())
}

/// Like `emit_satisfiability_check`, but with an explicit `ProofConfig`.
pub fn emit_satisfiability_check_with(
    kb: &KnowledgeBase,
    rule_qn: &str,
    config: &ProofConfig,
) -> Result<String, SmtGenError> {
    let mut emitter = Emitter::new(kb);
    emitter.abstract_mode = config.abstract_body;
    emitter.collect_rule(rule_qn)?;
    emitter.collect_facts_for_referenced_entities()?;
    Ok(emitter.render_satisfiability_with(rule_qn, config))
}

/// Like `emit_satisfiability_check_with` but additionally returns the
/// set of rule QNs visited during emission — the proof's dependency
/// set, used for staleness tracking when one of them changes.
pub fn emit_satisfiability_check_with_deps(
    kb: &KnowledgeBase,
    rule_qn: &str,
    config: &ProofConfig,
) -> Result<(String, Vec<String>), SmtGenError> {
    let mut emitter = Emitter::new(kb);
    emitter.abstract_mode = config.abstract_body;
    emitter.collect_rule(rule_qn)?;
    emitter.collect_facts_for_referenced_entities()?;
    let smt = emitter.render_satisfiability_with(rule_qn, config);
    let deps: Vec<String> = emitter.visited_rules.into_iter().collect();
    Ok((smt, deps))
}

/// Lift a positive-form rule (`R(args) :- premises -: conclusion`)
/// into SMT-LIB *implication clauses* suitable for splicing into a
/// downstream proof's `ProofConfig.assumptions`.
///
/// Deterministic semantics — the `:-` clause is the premise set, the
/// `-:` clause is the conclusion. No heuristic, no last-clause guess.
/// The author has explicitly named what they want to prove.
///
/// Each returned clause is shaped like
/// `(assert (forall ((var_d Real)) (=> (and <premises>) <conclusion>)))`;
/// when there is exactly one premise the `(and …)` wrapper is dropped.
///
/// Labeled multi-head rules (`rule X: H1, H2 :- B`) resolve to N
/// labeled rules sharing label X; one clause is emitted per head, so
/// `using X` splices both `B ⇒ H1` and `B ⇒ H2` into the consumer.
///
/// **Refuses any rule without a `-:` conclusion clause.** Classical
/// violation-shape rules (no `-:`) are unciteable today: their
/// theorem statement is implicitly "the body is unsat", not a
/// premises ⇒ conclusion implication. The author who wants to cite
/// such a rule must rewrite it in positive form.
///
/// Field consts (define-fun lines from entity destructure) are NOT
/// re-emitted here — the consumer's preamble already declares them
/// since the consumer chases the same facts.
///
/// **Caller-side discharge gate (proposal 030 phase γ.1):** this
/// function only emits the lifted statement; the caller MUST first
/// confirm the cited rule's ProofRecord is Discharged (or that
/// it's a kernel-derived ScopeAxiom / Specialization). The prove
/// driver's `cite_status` does this gate before invoking the lift;
/// direct callers from new code must enforce the same contract or
/// they reintroduce silent-axiom-acceptance.
pub fn lift_rule_to_implication_clause(
    kb: &KnowledgeBase,
    rule_qn: &str,
) -> Result<Vec<String>, SmtGenError> {
    let clauses = kb.program_clauses_by_qn(rule_qn);
    if clauses.is_empty() {
        return Err(SmtGenError::new(format!("rule '{rule_qn}' not found")));
    }
    clauses
        .into_iter()
        .map(|clause| lift_one_clause(kb, rule_qn, clause))
        .collect()
}

fn lift_one_clause(
    kb: &KnowledgeBase,
    rule_qn: &str,
    clause: ProgramClause,
) -> Result<String, SmtGenError> {
    let mut emitter = Emitter::new(kb);
    // Cited-rule lifts are inherently abstract: chasing the cited
    // rule's body would condition its truth on facts the consumer
    // doesn't quote (unsound for a universal claim) and would also
    // drag in transitive nonlinearity that breaks LRA discharges.
    emitter.abstract_mode = true;
    emitter.collect_rule_clause(rule_qn, &clause)?;
    emitter.collect_facts_for_referenced_entities()?;

    if emitter.conclusion_assertions.is_empty() {
        return Err(SmtGenError::new(format!(
            "rule '{rule_qn}' is not citable: no `-:` (then) clause. \
             Citable rules must state their conclusion explicitly via \
             the `-:` separator. Classical violation-shape rules (body \
             unsat) are not lifted as implications."
        )));
    }

    let premises = match emitter.assertions.len() {
        0 => "true".to_string(),
        1 => emitter.assertions[0].clone(),
        _ => format!("(and {})", emitter.assertions.join(" ")),
    };
    let conclusion = match emitter.conclusion_assertions.len() {
        1 => emitter.conclusion_assertions[0].clone(),
        _ => format!("(and {})", emitter.conclusion_assertions.join(" ")),
    };

    let imp = format!("(=> {} {})", premises, conclusion);

    // For step rules synthesized in a parent's frame, the leading
    // DeBruijn slots 0..shared_arity refer to the parent's preamble
    // declarations; only step-introduced vars (≥ shared_arity) need
    // to be emitted, as fresh declare-consts, alongside a ground
    // implication. shared_arity == 0 falls through to a classic
    // universally-quantified lift.
    let shared_arity = clause.shared_arity;

    if shared_arity == 0 {
        if emitter.free_vars.is_empty() {
            return Ok(format!("(assert {imp})"));
        }
        let decls: Vec<String> = emitter
            .free_vars
            .iter()
            .map(|v| format!("({v} Real)"))
            .collect();
        return Ok(format!("(assert (forall ({}) {imp}))", decls.join(" ")));
    }

    // shared_arity > 0: emit declare-consts for step-new vars +
    // a ground assert for the implication.
    let mut step_new: Vec<&String> = emitter
        .free_vars
        .iter()
        .filter(|v| parse_synthetic_var_name(v).map_or(false, |idx| idx >= shared_arity))
        .collect();
    step_new.sort();
    let mut block = String::new();
    for v in &step_new {
        block.push_str(&format!("(declare-const {v} Real)\n"));
    }
    block.push_str(&format!("(assert {imp})"));
    Ok(block)
}

// ── Implementation ──────────────────────────────────────────────────

/// Outcome of classifying a rule's head for SMT translation.
enum HeadShape {
    /// `⊥` denial form — no result var, no conclusion.
    Bottom,
    /// Predicate / equation / entity destructure (e.g. `gte(?x, 3.0)`,
    /// `?a = ?b`, `LinkParameters(...)`). Head IS the conclusion under
    /// proposal 032; routed through `process_body_goal`.
    Predicate,
    /// `rule_qn(?result)` — single DeBruijn pos_arg as the result
    /// variable. Used by upper-bound obligations.
    FunctionLike { result_idx: u32 },
    /// Shape the v0 emitter cannot translate; the carried message is
    /// surfaced as a `SmtGenError` to the caller.
    Unsupported(String),
}

struct Emitter<'kb> {
    kb: &'kb KnowledgeBase,
    /// `(field_const, value)` to emit at the top of the document.
    /// `BTreeMap` for deterministic order.
    field_consts: BTreeMap<String, f64>,
    /// Entities seen on rule body LHS that we'll need to materialise.
    /// Each is the entity's qualified name; we resolve facts at
    /// `collect_facts_for_referenced_entities` time.
    referenced_entities: BTreeSet<String>,
    /// Final translated body equation: `(define-fun <result> () Real <expr>)`.
    body_smtlib: String,
    /// Name of the rule's result variable (the `?tau` in
    /// `comm_delay_max(?tau)`). Used in the obligation assertion.
    /// Empty string for rules whose head is bare (no result arg —
    /// the rule is a property/violation predicate that we feed to
    /// `render_satisfiability`).
    result_var: String,
    /// Inequality body goals (`lte`, `lt`, `gte`, `gt`) collected as
    /// SMT-LIB constraint expressions. Emitted as `(assert ...)`
    /// inside `render_satisfiability`. Order-preserving so
    /// counterexample SMT reads in the user's authored order.
    assertions: Vec<String>,
    /// Conclusion clauses from the rule's `-:` (then) clause. Each
    /// is the SMT-LIB rendering of one conclusion goal. For SMT
    /// discharge they are negated and AND-conjoined into one
    /// `(assert (not (and …)))`; for `using`-clause lift they are
    /// emitted directly inside the implication's right-hand side.
    /// Empty for facts and classical violation-shape rules.
    conclusion_assertions: Vec<String>,
    /// Free SMT vars introduced because of body bindings whose
    /// definition is missing (e.g. `?d_prev` is talked about by
    /// inequality goals but never bound by an `=` clause). These
    /// must be `(declare-const ... Real)`'d for satisfiability mode.
    free_vars: BTreeSet<String>,
    /// QNs of every rule visited (top-level + transitive). The
    /// CLI surfaces these as the proof's staleness dependency set.
    pub(crate) visited_rules: BTreeSet<String>,
    /// Entity-typed bindings: synthetic var name → entity TermId
    /// (e.g. `var_2` → `Pose(position: Vec3(...), ...)`). Populated
    /// when a rule-call is fact-matched (or inlined) and a positional
    /// arg of the call is a DeBruijn var while the corresponding
    /// fact arg is a constructor (`Expr::Constructor` / entity `Apply`).
    /// Consumed by `translate_expr` when it encounters `field_access(?var, ...)`.
    /// WI-246: the bound entity is a `NodeOccurrence` (the rule-body
    /// substrate), materialized from a fact head where it originates as a
    /// term and used directly where it originates as a call-arg occurrence.
    entity_bindings: BTreeMap<String, Rc<NodeOccurrence>>,
    /// Set when an emitted SMT expression uses `anthill_abs`. Triggers
    /// emission of the `(define-fun anthill_abs ...)` prelude in the
    /// rendered script. SMT-LIB has no built-in `abs` for Real; we
    /// synthesise it via `(ite (< x 0) (- x) x)`.
    uses_abs: bool,
    /// SMT argument strings θ for which `cos(θ)`/`sin(θ)` were rendered
    /// (WI-681). Trigonometric functions have no SMT-LIB Real form, so
    /// they emit as the uninterpreted functions `anthill_cos`/`anthill_sin`;
    /// for each θ seen, the render adds the Pythagorean identity
    /// `cos(θ)² + sin(θ)² = 1` — the ONE nonlinear fact a norm-preserving
    /// 2-D rotation needs (QF_NRA-decidable). Deterministic order.
    trig_args: BTreeSet<String>,
    /// AbstractLift mode: when true, `process_body_goal` skips
    /// rule-call expansion (single-arg shorthand and multi-pos-arg
    /// fact-match/inline) — those vars stay free in the rendered
    /// SMT. Used by `lift_rule_to_implication_clause` (always) and
    /// by structured-proof parent discharges (via ProofConfig).
    abstract_mode: bool,
    /// [`SMT_BUILTINS`] resolved against `kb` (WI-897). WHICH OPERATION MEANS
    /// WHICH SMT FORM, decided by symbol identity — see the table's own doc for
    /// why this is not a name compare.
    builtins: SmtBuiltinTable,
}

impl<'kb> Emitter<'kb> {
    fn new(kb: &'kb KnowledgeBase) -> Self {
        Self {
            kb,
            field_consts: BTreeMap::new(),
            referenced_entities: BTreeSet::new(),
            body_smtlib: String::new(),
            result_var: String::new(),
            assertions: Vec::new(),
            conclusion_assertions: Vec::new(),
            free_vars: BTreeSet::new(),
            visited_rules: BTreeSet::new(),
            entity_bindings: BTreeMap::new(),
            uses_abs: false,
            trig_args: BTreeSet::new(),
            abstract_mode: false,
            builtins: SmtBuiltinTable::resolve(kb),
        }
    }

    /// Find the rule by qualified name. Walk its body and produce
    /// the SMT-LIB equation that defines the head's result variable.
    /// Picks the first rule resolved by label / by-functor — for
    /// labeled multi-head rules (multiple rids per label) the
    /// per-clause path [`Self::collect_rule_clause`] should be used by
    /// the caller iterating over `kb.program_clauses_by_qn(rule_qn)`.
    fn collect_rule(&mut self, rule_qn: &str) -> Result<(), SmtGenError> {
        let clause = self
            .kb
            .program_clauses_by_qn(rule_qn)
            .into_iter()
            .next()
            .ok_or_else(|| SmtGenError::new(format!("rule '{rule_qn}' not found")))?;
        self.collect_rule_clause(rule_qn, &clause)
    }

    /// Walk the given rule's body. Used by the lift fanout to
    /// process each rid of a labeled multi-head rule independently.
    fn collect_rule_clause(
        &mut self,
        rule_qn: &str,
        clause: &ProgramClause,
    ) -> Result<(), SmtGenError> {
        self.visited_rules.insert(rule_qn.to_string());

        // Loaded rules use de Bruijn-indexed variables (the parser's
        // `?name` form is interned to a position; the user-given
        // name is dropped). Each index gets a synthetic SMT
        // identifier `var_<i>` — unreadable but unambiguous, and Z3
        // only sees consts and ops so the names don't matter for
        // soundness.
        //
        // Head shapes the dispatcher recognises (see `classify_head`):
        //  - `rule_qn(?result)` (FunctionLike) — single pos_arg, the
        //    result var. Used by upper-bound obligations.
        //  - `gte(?x, 3.0)` / `LinkParameters(...)` / `?a = ?b`
        //    (Predicate) — head IS the conclusion (proposal 032 unified
        //    encoding); routed through `process_body_goal` and split
        //    off into `conclusion_assertions`.
        //  - `⊥` (Bottom) — denial form, conclusion stays empty.
        let Value::Term { id: head, .. } = &clause.head else {
            return Err(SmtGenError::new(format!(
                "SMT v0 cannot compile a non-term rule head for `{rule_qn}`"
            )));
        };
        let head_shape = self.classify_head(*head);
        if let HeadShape::FunctionLike { result_idx } = head_shape {
            self.result_var = synthetic_var_name(result_idx);
        } else if let HeadShape::Unsupported(msg) = &head_shape {
            return Err(SmtGenError::new(msg.clone()));
        }

        // Walk the body. Three clause shapes we accept:
        //   <Entity>(field: ?var, ...) — destructure a fact's fields
        //   ?var = <arith>             — bind ?var to an SMT term
        //   <Ord.op>(a, b)         — inequality assertion
        //                                  (lte/lt/gte/gt)
        // Plus rule calls (`<rule_qn>(?var)`) — chase the dependency.
        let mut local_bindings: BTreeMap<String, String> = BTreeMap::new();
        for goal in &clause.body_nodes {
            self.process_body_goal(goal, &mut local_bindings)?;
        }

        // Conclusion goals: under the unified encoding the rule head
        // IS the conclusion (Predicate shape) and is routed through
        // `process_body_goal`. Each goal is translated through the
        // same machinery as the body; the resulting assertions are
        // siphoned into `conclusion_assertions` instead of
        // `assertions`. Discharge and lift consume the two buckets
        // differently — see render_satisfiability_with /
        // lift_rule_to_implication_clause.
        // The head is still a hash-consed term (heads stay terms — they are
        // SEARCHED in the discrimination tree). Materialize it to the
        // occurrence substrate so it flows through the same occurrence-based
        // `process_body_goal` as the body goals (WI-246).
        let conclusion_goals: Vec<Rc<NodeOccurrence>> = match head_shape {
            HeadShape::Bottom => Vec::new(),
            HeadShape::FunctionLike { .. } => Vec::new(),
            HeadShape::Predicate => vec![materialize_from_handle(self.kb, *head)],
            HeadShape::Unsupported(_) => unreachable!("returned above"),
        };
        if !conclusion_goals.is_empty() {
            let body_count = self.assertions.len();
            for goal in &conclusion_goals {
                self.process_body_goal(goal, &mut local_bindings)?;
            }
            self.conclusion_assertions = self.assertions.split_off(body_count);
        }

        // For upper-bound mode the result var must be bound by the
        // body. For satisfiability mode (no result var) it's fine if
        // every body var is either bound or free.
        if !self.result_var.is_empty() {
            let result_smt = local_bindings.get(&self.result_var).ok_or_else(|| {
                SmtGenError::new(format!(
                    "rule body never bound the result variable '?{}'",
                    self.result_var
                ))
            })?;
            self.body_smtlib = format!(
                "(define-fun {} () Real {})",
                sanitize_smt_id(&self.result_var),
                result_smt
            );
        }

        // Compute free vars: any var_<i> referenced by an assertion
        // expression (body OR conclusion) that has no binding entry.
        // Those need `(declare-const ... Real)` in satisfiability mode
        // — and become the forall-quantified parameters in the lift.
        // `body_smtlib` is scanned too (WI-680): a `FunctionLike` result bound to
        // an `ite` over an otherwise-unused input (`?w = ite(gte(?x,0), ?x, 0)`)
        // puts a genuinely-free `var_x` only into the `(define-fun var_w …)`
        // string; without this it would emit undeclared and z3 would error. The
        // result var itself is in `local_bindings`, so it is skipped (never
        // double-declared), and `free_vars` are rendered before `body_smtlib`.
        let scan = self
            .assertions
            .iter()
            .chain(self.conclusion_assertions.iter())
            .chain(std::iter::once(&self.body_smtlib));
        for assertion in scan {
            for tok in assertion.split(|c: char| !c.is_alphanumeric() && c != '_') {
                if parse_synthetic_var_name(tok).is_some() && !local_bindings.contains_key(tok) {
                    self.free_vars.insert(tok.to_string());
                }
            }
        }

        // Soundness guard (WI-681): the uninterpreted-trig relaxation
        // (cos/sin free except cos²+sin²=1) is an OVER-approximation — sound
        // in body (positive) position, where dropping true trig facts only
        // enlarges the model set. But a `-:` conclusion is emitted NEGATED
        // (`(assert (not …))`), where the same relaxation UNDER-approximates:
        // it could eliminate the witness of a real violation and report a
        // false `unsat`. No obligation needs both today (the lf1 GPS proofs
        // are violation-shape, no `-:`); refuse the combination loudly rather
        // than silently emit an unsound query.
        if !self.trig_args.is_empty() && !self.conclusion_assertions.is_empty() {
            return Err(SmtGenError::new(
                "cos/sin (uninterpreted-trig over-approximation) in an obligation \
                 with a `-:` conclusion is unsound: the relaxation under-approximates \
                 under the conclusion's negation. State the property as a violation \
                 rule (body unsat), not a positive-form `-:` rule.",
            ));
        }
        Ok(())
    }

    /// Process one rule-body goal.
    fn process_body_goal(
        &mut self,
        goal: &Rc<NodeOccurrence>,
        bindings: &mut BTreeMap<String, String>,
    ) -> Result<(), SmtGenError> {
        let Some((functor, pos_args, named_args)) = occ_as_fn(goal) else {
            return Err(SmtGenError::new(format!(
                "non-Fn body goal: {:?}",
                goal.as_expr().map(std::mem::discriminant)
            )));
        };
        let qn = self.kb.qualified_name_of(functor);

        // Equation goal: `?var = <expr>` binds the DeBruijn index of
        // ?var to the SMT translation of <expr>. Variable references
        // elsewhere in the body get substituted inline at translate
        // time.
        if self.is_eq_functor(functor) {
            if pos_args.len() != 2 {
                return Err(SmtGenError::new(format!(
                    "= goal: expected 2 pos_args, got {}",
                    pos_args.len()
                )));
            }
            // Bare-DeBruijn LHS → string binding (cheap inline substitution
            // for downstream uses). Anything else (e.g. `?d * ?d = ?d_sq`)
            // → emit as a free assertion `(= <lhs> <rhs>)`. This keeps the
            // bindings map small and lets nonlinear equalities flow into
            // QF_NRA naturally.
            if let Some(Expr::Var(Var::DeBruijn(i))) = pos_args[0].as_expr() {
                // Entity-constructor RHS (`?target = Vec3(...)`, WI-681):
                // bind the LHS to the entity for later field access instead
                // of translating it as an arithmetic expression (a
                // constructor is not a Real). CLOSE it over this frame's
                // entity bindings so any callee-frame param var inside the
                // constructor is substituted out before the entity is
                // propagated across an inline boundary (where the frame's
                // DeBruijn indices no longer mean the same thing).
                if let Some((rhs_functor, _, _)) = occ_as_fn(&pos_args[1]) {
                    if self.is_known_entity(rhs_functor) {
                        // Close over this frame's two channels: the entity
                        // bindings (WI-681) for entity-typed fields, and
                        // `bindings` — the scalar string map — for a field
                        // computed from a scalar op param (WI-686, e.g.
                        // `upc: ite(…upc…)`). `close_occ` only reads
                        // `entity_bindings` (it is `&self`), so borrow it in
                        // place; the `insert` below re-borrows mutably after
                        // the closed value is owned.
                        let closed =
                            self.close_occ(&pos_args[1], &self.entity_bindings, bindings)?;
                        self.entity_bindings.insert(synthetic_var_name(*i), closed);
                        return Ok(());
                    }
                }
                let rhs_smt = self.translate_expr(&pos_args[1], bindings)?;
                bindings.insert(synthetic_var_name(*i), rhs_smt);
                return Ok(());
            }
            let rhs_smt = self.translate_expr(&pos_args[1], bindings)?;
            let lhs_smt = self.translate_expr(&pos_args[0], bindings)?;
            self.assertions.push(format!("(= {lhs_smt} {rhs_smt})"));
            return Ok(());
        }

        // Inequality body goals: `lte/lt/gte/gt(a, b)` become SMT
        // assertions on the constraint set. The rule body's joint
        // satisfiability is exactly the conjunction of these
        // inequalities + the equation-derived bindings.
        if let Some(smt_op) = self.builtins.inequality(functor) {
            if pos_args.len() != 2 {
                return Err(SmtGenError::new(format!(
                    "{qn}: expected 2 pos_args, got {}",
                    pos_args.len()
                )));
            }
            let a = self.translate_expr(&pos_args[0], bindings)?;
            let b = self.translate_expr(&pos_args[1], bindings)?;
            self.assertions.push(format!("({smt_op} {a} {b})"));
            return Ok(());
        }

        // Entity-destructure goal: `EntityName(field: ?bind_var, ...)`.
        // For v0 we only handle named-arg destructures. Each
        // ?bind_var becomes an SMT const bound to the corresponding
        // field's value from the matching ground fact.
        if self.is_known_entity(functor) {
            let entity_qn = qn.to_string();
            self.referenced_entities.insert(entity_qn.clone());
            for (field_sym, val_occ) in named_args {
                let bind_idx = match val_occ.as_expr() {
                    Some(Expr::Var(Var::DeBruijn(i))) => *i,
                    _ => continue, // non-var slots (`field: ?` wildcards / literals)
                };
                let field_name = self.kb.local_name_of(*field_sym).to_string();
                let const_name = sanitize_smt_id(&field_name);
                bindings.insert(synthetic_var_name(bind_idx), const_name.clone());
                self.field_consts.entry(const_name).or_insert(0.0); // resolved later
            }
            return Ok(());
        }

        // Abstract mode: don't chase rule calls into their bodies.
        // Avoids fact-bound ground arithmetic and transitive
        // nonlinearity (e.g. `position_distance_sq`'s `var*var`)
        // polluting the consumer's preamble. The call's vars stay
        // free; ambient cited-rule lifts constrain them.
        //
        // A RULE CALL IS THE ONLY THING THIS MAY SKIP, and `program_clauses_by_functor`
        // is what says so. Until WI-897 the branch skipped whatever reached it, which is
        // a different act entirely: an unrecognised PREMISE was dropped, and since a
        // lift renders the body as an implication's antecedent, dropping one WEAKENS the
        // antecedent — the lemma spliced into the consumer is then stronger than
        // anything that was proved. MEASURED (`wi897_symbol_identity_test`): a
        // `String.lte(?name, "z")` premise vanished and the clause came back
        // `(=> (<= var_1 5.0) (<= var_1 100.0))`, its first premise simply gone. A rule
        // call is safe to skip for the opposite reason — it CONSTRAINS nothing here, its
        // vars stay free, and an ambient lift is what re-states it. Everything else falls
        // through to the loud `unhandled body goal functor` below.
        if self.abstract_mode && !self.kb.program_clauses_by_functor(functor).is_empty() {
            self.visited_rules.insert(qn.to_string());
            return Ok(());
        }

        // Rule call: `<rule_qn>(?result_var)` — single-arg shorthand
        // that yields one inline SMT expression. Used by call sites
        // like `step_distance_bound(?delta)`.
        if pos_args.len() == 1
            && named_args.is_empty()
            && self
                .kb
                .program_clauses_by_functor(functor)
                .iter()
                .any(|clause| !clause.is_fact())
        {
            let bind_idx = match pos_args[0].as_expr() {
                Some(Expr::Var(Var::DeBruijn(i))) => *i,
                other => {
                    return Err(SmtGenError::new(format!(
                        "v0: rule call's pos arg must be a DeBruijn var, got {:?}",
                        other.map(std::mem::discriminant)
                    )))
                }
            };
            let inlined = self.translate_called_rule(qn)?;
            bindings.insert(synthetic_var_name(bind_idx), inlined);
            return Ok(());
        }

        // Multi-pos-arg rule call: `<rule>(<a1>, ..., <aN>)`.
        // Two paths:
        //   (1) Fact match — the rule has at least one ground fact
        //       (rule with empty body) whose pos_args structurally
        //       agree with the call. Each call-side DeBruijn var
        //       gets bound to the matched fact slot (literal → string
        //       binding, entity occurrence → entity_bindings).
        //   (2) Inline — the rule has a defining body. Open it with
        //       caller→callee parameter substitution; process its
        //       goals as if inlined here.
        // No named_args path yet — multi-pos-arg with named_args is
        // a v1 concern.
        if !pos_args.is_empty() && named_args.is_empty() {
            let call_args: Vec<Rc<NodeOccurrence>> = pos_args.to_vec();
            if self.try_match_fact_call(functor, &call_args, bindings)? {
                return Ok(());
            }
            if self.try_inline_rule_call(qn, &call_args, bindings)? {
                return Ok(());
            }
        }

        Err(SmtGenError::new(format!(
            "v0: unhandled body goal functor '{qn}'"
        )))
    }

    /// Try to match a multi-pos-arg call against any ground fact
    /// (rule with empty body) of the same functor. On match, bind
    /// each call-side DeBruijn var to the corresponding fact slot —
    /// literal → string binding, entity-shaped occurrence →
    /// entity_bindings (consumed by `field_access` lowering).
    /// Returns Ok(true) if a fact matched (and bindings were applied);
    /// Ok(false) if no fact matched (caller falls through to inline).
    ///
    /// The fact head is still a hash-consed term (heads stay terms); it is
    /// materialized to the occurrence substrate so the call args (occurrences)
    /// and fact slots compare occ-vs-occ (WI-246).
    fn try_match_fact_call(
        &mut self,
        functor: Symbol,
        call_args: &[Rc<NodeOccurrence>],
        bindings: &mut BTreeMap<String, String>,
    ) -> Result<bool, SmtGenError> {
        let candidates = self.kb.program_clauses_by_functor(functor);
        // Record the functor's QN in visited_rules so the cache key
        // observes any change to its defining facts (initial-geometry
        // edits invalidate downstream proofs).
        let functor_qn = self.kb.qualified_name_of(functor).to_string();
        for clause in candidates {
            if !clause.is_fact() {
                continue;
            }
            self.visited_rules.insert(functor_qn.clone());
            let Value::Term { id: head, .. } = clause.head else {
                return Err(SmtGenError::new(format!(
                    "v0: fact call `{functor_qn}` has a non-term program head"
                )));
            };
            let head_occ = materialize_from_handle(self.kb, head);
            let Some((_, fpos, fnamed)) = occ_as_fn(&head_occ) else {
                continue;
            };
            if !fnamed.is_empty() {
                continue;
            }
            if fpos.len() != call_args.len() {
                continue;
            }

            // Probe — does every concrete call slot equal the
            // corresponding fact slot? Variable slots match anything.
            let mut bind_pairs: Vec<(u32, Rc<NodeOccurrence>)> = Vec::new();
            let mut matched = true;
            for (call_occ, fact_occ) in call_args.iter().zip(fpos.iter()) {
                if let Some(Expr::Var(Var::DeBruijn(i))) = call_occ.as_expr() {
                    bind_pairs.push((*i, Rc::clone(fact_occ)));
                    continue;
                }
                if !self.occs_match(call_occ, fact_occ) {
                    matched = false;
                    break;
                }
            }
            if !matched {
                continue;
            }

            // Apply bindings.
            for (idx, fact_occ) in bind_pairs {
                let synth = synthetic_var_name(idx);
                match fact_occ.as_expr() {
                    Some(Expr::Const(Literal::Float(f))) => {
                        bindings.insert(synth, format_real(f.into_inner()));
                    }
                    Some(Expr::Const(Literal::Int(i))) => {
                        bindings.insert(synth, format_real(*i as f64));
                    }
                    _ if occ_as_fn(&fact_occ).is_some() => {
                        // Entity (Pose, Vec3, …) — defer until
                        // field_access reads it.
                        self.entity_bindings.insert(synth, fact_occ);
                    }
                    Some(Expr::Ref(_)) | Some(Expr::Ident(_)) => {
                        // Nullary symbol like `Leader`. Skip — it
                        // can't appear in arithmetic expressions
                        // and there's no field projection over it.
                    }
                    _ => { /* skip for v0 */ }
                }
            }
            return Ok(true);
        }
        Ok(false)
    }

    /// Inline a rule call's body at the call site. `call_args` are
    /// the caller-side occurrences bound positionally to the callee's
    /// head DeBruijn vars. The callee's local DeBruijn indices are
    /// renamed into a per-call namespace so they don't collide with
    /// the caller's; entity-typed arguments propagate into the
    /// callee's entity_bindings.
    fn try_inline_rule_call(
        &mut self,
        callee_qn: &str,
        call_args: &[Rc<NodeOccurrence>],
        caller_bindings: &mut BTreeMap<String, String>,
    ) -> Result<bool, SmtGenError> {
        let sym = match self.kb.try_resolve_symbol(callee_qn) {
            Some(s) => s,
            None => return Ok(false),
        };
        let clause = match self
            .kb
            .program_clauses_by_functor(sym)
            .into_iter()
            .find(|clause| !clause.is_fact())
        {
            Some(clause) => clause,
            None => return Ok(false),
        };
        self.visited_rules.insert(callee_qn.to_string());

        // Head stays a term (searched in the discrim tree); materialize it to
        // the occurrence substrate to read its De Bruijn param vars (WI-246).
        let Value::Term { id: head, .. } = clause.head else {
            return Err(SmtGenError::new(format!(
                "v0: inlined rule '{callee_qn}' has a non-term head"
            )));
        };
        let head_occ = materialize_from_handle(self.kb, head);
        let head_pos: Vec<Rc<NodeOccurrence>> = match occ_as_fn(&head_occ) {
            Some((_, pos, named)) if named.is_empty() => pos.to_vec(),
            _ => {
                return Err(SmtGenError::new(format!(
                    "v0: inlined rule '{callee_qn}' must have only pos args in head"
                )))
            }
        };
        if head_pos.len() != call_args.len() {
            return Err(SmtGenError::new(format!(
                "rule call arity mismatch for '{callee_qn}': expected {}, got {}",
                head_pos.len(),
                call_args.len()
            )));
        }

        // Prepare callee-local bindings: each head ?DeBruijn becomes
        // either the caller's already-translated SMT string (for
        // arithmetic-typed args) or an entry in the per-call
        // entity_bindings (for entity-typed args).
        //
        // We also remember `head_caller`: head DeBruijn idx → the
        // caller-side DeBruijn synth name (when the call arg is a
        // var). After body processing, if the body bound the head
        // (e.g. `?d_sq = ?dx * ?dx + ...`), we copy that final value
        // back into `caller_bindings[caller_synth]` — otherwise the
        // caller would see the head var as unconstrained and Z3
        // would treat it as free. This is the propagation that
        // makes inlining behave like substitution in the caller's
        // joint constraint set.
        let mut callee_str: BTreeMap<String, String> = BTreeMap::new();
        let mut callee_ent: BTreeMap<String, Rc<NodeOccurrence>> = BTreeMap::new();
        let mut head_caller: Vec<(u32, String)> = Vec::new();
        for (head_arg, call_arg) in head_pos.iter().zip(call_args.iter()) {
            self.bind_head_arg(
                callee_qn,
                head_arg,
                call_arg,
                caller_bindings,
                &mut callee_str,
                &mut callee_ent,
                &mut head_caller,
            )?;
        }

        // Process the callee's body. We share the global
        // `assertions` / `field_consts` / `referenced_entities` /
        // `free_vars` accumulators (the inlined rule's facts and
        // assertions belong to the caller's SMT document), but we
        // give the callee its own bindings + entity_bindings so its
        // local DeBruijn indices stay isolated. After processing we
        // restore the caller's entity_bindings.
        let body_goals = clause.body_nodes;
        let saved_ent = std::mem::take(&mut self.entity_bindings);
        self.entity_bindings = callee_ent;
        let mut local = callee_str;
        let mut err: Option<SmtGenError> = None;
        for goal in &body_goals {
            if let Err(e) = self.process_body_goal(goal, &mut local) {
                err = Some(e);
                break;
            }
        }
        // Capture the (possibly grown) callee entity_bindings before
        // restoring the caller's view — fact_match calls deeper in
        // the body can bind head DeBruijns to entity terms (e.g.
        // `real_pose_at(0, Leader, ?l)` binds ?l → Pose), and the
        // caller needs those propagated to its own synthetic names.
        let final_ent = std::mem::replace(&mut self.entity_bindings, saved_ent);
        if let Some(e) = err {
            return Err(e);
        }

        // Propagate body-bound head values back to the caller — both
        // arithmetic strings and entity_bindings.
        for (head_idx, caller_synth) in head_caller {
            let head_synth = synthetic_var_name(head_idx);
            if let Some(value) = local.get(&head_synth) {
                // Skip the trivial forwarding entry — body never
                // overrode it, so there's nothing new to push back.
                if *value != caller_synth {
                    caller_bindings.insert(caller_synth.clone(), value.clone());
                }
            }
            if let Some(entity_occ) = final_ent.get(&head_synth) {
                self.entity_bindings
                    .insert(caller_synth, Rc::clone(entity_occ));
            }
        }
        Ok(true)
    }

    /// Bind one head argument of an inlined rule against its call argument,
    /// populating the callee's string / entity binding maps.
    ///
    /// A **bare De Bruijn** head arg is the generic case: bind it to the call
    /// arg's already-translated SMT string (a var forwards its synth name — the
    /// caller declares it free if unbound — a literal renders directly), and, for
    /// an entity-typed arg, propagate the concrete construction into
    /// `callee_ent` for downstream field access.
    ///
    /// A **constructor-shaped** head arg — `some(?0)` / `TFS(prev_distance:
    /// some(?0), …)` — arises from the WI-687 per-call-site match specialization,
    /// whose synthesized rule head carries the argument's constructor spine. It
    /// is bound STRUCTURALLY: resolve the call arg to its concrete construction
    /// (the arg itself, or — when the call passed a var already bound to an
    /// entity — its `entity_bindings` value), check the functors and arities
    /// agree, and recurse on the aligned fields (positional by index, named by
    /// field short-name). Each leaf bottoms out at the De Bruijn case, so a
    /// head leaf `?0` inside `some(?0)` binds to the caller's inner sub-term.
    #[allow(clippy::too_many_arguments)]
    fn bind_head_arg(
        &self,
        callee_qn: &str,
        head_arg: &Rc<NodeOccurrence>,
        call_arg: &Rc<NodeOccurrence>,
        caller_bindings: &BTreeMap<String, String>,
        callee_str: &mut BTreeMap<String, String>,
        callee_ent: &mut BTreeMap<String, Rc<NodeOccurrence>>,
        head_caller: &mut Vec<(u32, String)>,
    ) -> Result<(), SmtGenError> {
        // A nullary constructor CONSTANT in head position (`none`, spelled as a
        // bare `Ref`/`Ident` or an arg-less `Fn`) is ground — nothing to BIND, but
        // it must still MATCH the call (WI-687). `try_inline_rule_call` selects one
        // synth rule per functor regardless of the call's shape, so a `none` head
        // meeting a `some(…)` call must fail LOUDLY — symmetric with the `some(?0)`
        // head direction, which already errors at `resolve_call_ctor` / the functor
        // check below. Verify the call denotes the same nullary constructor.
        if let Some(h_null) = nullary_ctor_sym(head_arg) {
            let call_null = self
                .resolve_call_ctor(call_arg)
                .and_then(|cc| nullary_ctor_sym(&cc))
                .or_else(|| nullary_ctor_sym(call_arg));
            if call_null == Some(h_null) {
                return Ok(());
            }
            return Err(SmtGenError::new(format!(
                "WI-687: nullary head constructor `{}` inlining '{callee_qn}' does not match \
                 the call argument {:?} (the specialized arm does not apply to this call)",
                self.kb.qualified_name_of(h_null),
                call_arg.as_expr().map(std::mem::discriminant)
            )));
        }

        // Constructor-shaped head arg (WI-687): structurally match the call. The
        // arity-0 case is already handled by the nullary check above, so `hpos` /
        // `hnamed` here are non-empty.
        if !matches!(head_arg.as_expr(), Some(Expr::Var(Var::DeBruijn(_)))) {
            let Some((hf, hpos, hnamed)) = occ_as_fn(head_arg) else {
                return Err(SmtGenError::new(format!(
                    "v0: inlined rule '{callee_qn}' head arg must be a De Bruijn var \
                     or a constructor, got {:?}",
                    head_arg.as_expr().map(std::mem::discriminant)
                )));
            };
            let Some(cc) = self.resolve_call_ctor(call_arg) else {
                return Err(SmtGenError::new(format!(
                    "WI-687: '{callee_qn}' expects a concrete `{}` construction at a \
                     constructor-shaped head arg, but the call supplied {:?}",
                    self.kb.qualified_name_of(hf),
                    call_arg.as_expr().map(std::mem::discriminant)
                )));
            };
            let Some((cf, cpos, cnamed)) = occ_as_fn(&cc) else {
                return Err(SmtGenError::new(format!(
                    "WI-687: '{callee_qn}' call arg resolved to a non-construction"
                )));
            };
            if hf != cf || hpos.len() != cpos.len() || hnamed.len() != cnamed.len() {
                return Err(SmtGenError::new(format!(
                    "WI-687: structural head mismatch inlining '{callee_qn}': head `{}` \
                     vs call `{}`",
                    self.kb.qualified_name_of(hf),
                    self.kb.qualified_name_of(cf)
                )));
            }
            for (hp, cp) in hpos.iter().zip(cpos.iter()) {
                self.bind_head_arg(
                    callee_qn,
                    hp,
                    cp,
                    caller_bindings,
                    callee_str,
                    callee_ent,
                    head_caller,
                )?;
            }
            for (hs, hv) in hnamed {
                let short = self.kb.local_name_of(*hs).rsplit('.').next();
                let Some((_, cv)) = cnamed
                    .iter()
                    .find(|(cs, _)| self.kb.local_name_of(*cs).rsplit('.').next() == short)
                else {
                    return Err(SmtGenError::new(format!(
                        "WI-687: constructor-shaped head field '{}' absent in call arg to \
                         '{callee_qn}'",
                        self.kb.local_name_of(*hs)
                    )));
                };
                self.bind_head_arg(
                    callee_qn,
                    hv,
                    cv,
                    caller_bindings,
                    callee_str,
                    callee_ent,
                    head_caller,
                )?;
            }
            return Ok(());
        }

        // Leaf: a bare De Bruijn head param.
        let head_idx = match head_arg.as_expr() {
            Some(Expr::Var(Var::DeBruijn(i))) => *i,
            _ => unreachable!("guarded by the matches! above"),
        };
        let head_synth = synthetic_var_name(head_idx);
        match call_arg.as_expr() {
            Some(Expr::Var(Var::DeBruijn(j))) => {
                let caller_synth = synthetic_var_name(*j);
                head_caller.push((head_idx, caller_synth.clone()));
                if let Some(s) = caller_bindings.get(&caller_synth) {
                    callee_str.insert(head_synth.clone(), s.clone());
                } else {
                    // Forward the synthetic name (caller will
                    // declare it free if it remains unbound).
                    callee_str.insert(head_synth.clone(), caller_synth.clone());
                }
                if let Some(t) = self.entity_bindings.get(&caller_synth) {
                    callee_ent.insert(head_synth, Rc::clone(t));
                }
            }
            Some(Expr::Const(Literal::Float(f))) => {
                callee_str.insert(head_synth, format_real(f.into_inner()));
            }
            Some(Expr::Const(Literal::Int(i))) => {
                callee_str.insert(head_synth, format_real(*i as f64));
            }
            Some(Expr::Ref(_)) | Some(Expr::Ident(_)) => {
                // Nullary symbol — not arithmetic; ignore.
            }
            _ if occ_as_fn(call_arg).is_some_and(|(f, _, _)| {
                self.kb.entity_field_types(f).is_some() || self.kb.is_constructor_symbol(f)
            }) =>
            {
                // Concrete entity / constructor at the call site — expose it for
                // field_access on the callee side.
                callee_ent.insert(head_synth, Rc::clone(call_arg));
            }
            _ if occ_as_fn(call_arg).is_some() => {
                // A COMPUTED (non-entity) argument — an arithmetic / operation
                // application (`?a + ?b`) — at a head leaf. `bind_head_arg` can't
                // translate it (it holds `&self`, not the `&mut` `translate_expr`
                // needs), and routing it to `entity_bindings` would silently drop
                // its value (the callee would see a free Z3 var, not the sum). Fail
                // loud (WI-687): pass a variable, literal, or entity construction.
                return Err(SmtGenError::new(format!(
                    "WI-687: '{callee_qn}' head leaf bound to a computed (non-entity) \
                     argument {:?}; pass a variable, literal, or entity construction",
                    call_arg.as_expr().map(std::mem::discriminant)
                )));
            }
            _ => {}
        }
        Ok(())
    }

    /// Resolve a call argument to its concrete construction occurrence for the
    /// WI-687 structural head binding: the argument itself when it is already a
    /// construction (an inline `TFS(…)` / `some(?x)` call arg), or — when the
    /// call passed a variable previously bound to an entity (`?state = TFS(…)`
    /// then `step(?state, …)`) — its `entity_bindings` value. `None` when neither
    /// holds (a bare scalar var / literal against a constructor-shaped head).
    fn resolve_call_ctor(&self, call_arg: &Rc<NodeOccurrence>) -> Option<Rc<NodeOccurrence>> {
        if occ_as_fn(call_arg).is_some() {
            return Some(Rc::clone(call_arg));
        }
        if let Some(Expr::Var(Var::DeBruijn(j))) = call_arg.as_expr() {
            return self.entity_bindings.get(&synthetic_var_name(*j)).cloned();
        }
        None
    }

    /// Structural equality of two occurrences for fact-match probing.
    /// `Rc::ptr_eq` is the fast path (a shared subtree); otherwise compare
    /// leaves and `Fn`-shaped forms structurally. Int/Float are compared by
    /// numeric value (literal-as-Real coercion). The occurrence twin of the
    /// former `terms_match` (WI-246).
    fn occs_match(&self, a: &Rc<NodeOccurrence>, b: &Rc<NodeOccurrence>) -> bool {
        if Rc::ptr_eq(a, b) {
            return true;
        }
        match (a.as_expr(), b.as_expr()) {
            (Some(Expr::Const(Literal::Float(x))), Some(Expr::Const(Literal::Float(y)))) => x == y,
            (Some(Expr::Const(Literal::Int(x))), Some(Expr::Const(Literal::Int(y)))) => x == y,
            (Some(Expr::Const(Literal::Int(i))), Some(Expr::Const(Literal::Float(f))))
            | (Some(Expr::Const(Literal::Float(f))), Some(Expr::Const(Literal::Int(i)))) => {
                (*i as f64) == f.into_inner()
            }
            (Some(Expr::Var(Var::DeBruijn(x))), Some(Expr::Var(Var::DeBruijn(y)))) => x == y,
            (Some(Expr::Ref(x) | Expr::Ident(x)), Some(Expr::Ref(y) | Expr::Ident(y))) => x == y,
            _ => match (occ_as_fn(a), occ_as_fn(b)) {
                (Some((fx, px, nx)), Some((fy, py, ny))) => {
                    fx == fy
                        && px.len() == py.len()
                        && nx.len() == ny.len()
                        && px.iter().zip(py.iter()).all(|(a, b)| self.occs_match(a, b))
                        && nx
                            .iter()
                            .zip(ny.iter())
                            .all(|((sa, ta), (sb, tb))| sa == sb && self.occs_match(ta, tb))
                }
                _ => false,
            },
        }
    }

    /// Recursively translate a *called* rule's body to a single
    /// SMT-LIB expression — the rule's result, fully inlined. The
    /// caller binds its rule-call goal's pos arg to this expression
    /// so subsequent uses of the variable substitute it directly.
    /// Each called rule's body uses its own DeBruijn indices, so
    /// fresh local bindings don't collide with the caller's.
    fn translate_called_rule(&mut self, callee_qn: &str) -> Result<String, SmtGenError> {
        self.visited_rules.insert(callee_qn.to_string());
        let sym = self
            .kb
            .try_resolve_symbol(callee_qn)
            .ok_or_else(|| SmtGenError::new(format!("rule call '{callee_qn}' not found")))?;
        let clause = self
            .kb
            .program_clauses_by_functor(sym)
            .into_iter()
            .find(|clause| !clause.is_fact())
            .ok_or_else(|| {
                SmtGenError::new(format!("rule call '{callee_qn}' has no defining clauses"))
            })?;

        let Value::Term { id: head, .. } = clause.head else {
            return Err(SmtGenError::new(format!(
                "v0: called rule '{callee_qn}' has a non-term head"
            )));
        };
        let head_occ = materialize_from_handle(self.kb, head);
        let result_idx = match occ_as_fn(&head_occ) {
            Some((_, pos_args, _)) if pos_args.len() == 1 => match pos_args[0].as_expr() {
                Some(Expr::Var(Var::DeBruijn(i))) => *i,
                _ => {
                    return Err(SmtGenError::new(format!(
                        "v0: called rule '{callee_qn}' head must be ?DeBruijn"
                    )))
                }
            },
            _ => {
                return Err(SmtGenError::new(format!(
                    "v0: called rule '{callee_qn}' must have exactly one pos arg in head"
                )))
            }
        };
        let mut local_bindings: BTreeMap<String, String> = BTreeMap::new();
        for goal in &clause.body_nodes {
            self.process_body_goal(goal, &mut local_bindings)?;
        }
        local_bindings
            .get(&synthetic_var_name(result_idx))
            .cloned()
            .ok_or_else(|| {
                SmtGenError::new(format!(
                    "called rule '{callee_qn}' never bound its result var"
                ))
            })
    }

    /// Translate an arithmetic expression (anthill prelude ops) to
    /// an SMT-LIB term. Variables resolve through `bindings` which
    /// substitutes already-defined locals inline. Mutates `self` to
    /// record `uses_abs` when an `abs` call is rendered.
    fn translate_expr(
        &mut self,
        occ: &Rc<NodeOccurrence>,
        bindings: &BTreeMap<String, String>,
    ) -> Result<String, SmtGenError> {
        match occ.as_expr() {
            Some(Expr::Const(Literal::Float(f))) => Ok(format_real(f.into_inner())),
            Some(Expr::Const(Literal::Int(i))) => Ok(format_real(*i as f64)),
            // A pre-rendered SMT fragment injected by `close_occ` for a scalar
            // operation parameter resolved across an inline boundary (WI-686 —
            // via `scalar_param_occ`). It is already in the caller's frame and
            // SMT syntax (a field const like `upc`, a literal like `(- 5.0)`, or
            // a compound); emit it verbatim. A genuine anthill `String` field
            // read into arithmetic position is a type error that does not occur
            // here; were one to reach this arm it would emit as a bare token and
            // fail loudly at the solver, not silently mis-evaluate.
            Some(Expr::Const(Literal::String(s))) => Ok(s.clone()),
            Some(Expr::Var(Var::DeBruijn(i))) => {
                let synth = synthetic_var_name(*i);
                Ok(bindings.get(&synth).cloned().unwrap_or(synth))
            }
            Some(Expr::Var(other)) => Err(SmtGenError::new(format!(
                "v0: expected DeBruijn var in expression, got {other:?}"
            ))),
            Some(Expr::Ref(s)) | Some(Expr::Ident(s)) => {
                Ok(sanitize_smt_id(self.kb.local_name_of(*s)))
            }
            // Conditional in expression position (WI-680): a bodied op's `if`
            // reduces to an `Expr::If` occurrence (the WI-669 defining-equation
            // refold feeds exactly this). Lower to SMT-LIB `(ite cond t e)` —
            // the condition is Bool, the branches Real. SMT-LIB `ite` is
            // polymorphic in the branch sort, so it works in LRA/NRA/LIA alike.
            Some(Expr::If {
                condition,
                then_branch,
                else_branch,
            }) => {
                let c = self.translate_condition(condition, bindings)?;
                let t = self.translate_expr(then_branch, bindings)?;
                let e = self.translate_expr(else_branch, bindings)?;
                Ok(format!("(ite {c} {t} {e})"))
            }
            _ => {
                // Entity field projection: `?p.field` reaches us as
                // `field_access(?p, Ident(field))` (an `Expr::Apply`) or,
                // post-WI-278, as a value-receiver `Expr::DotApply` with no
                // method args. Resolve through the entity_bindings populated by
                // fact match / rule inline to a concrete value occurrence (or
                // recurse on a nested entity field).
                if self.as_field_access(occ).is_some() {
                    let resolved = self.resolve_field_access(occ)?;
                    return self.translate_expr(&resolved, bindings);
                }
                let Some((functor, pos_args, _named)) = occ_as_fn(occ) else {
                    return Err(SmtGenError::new(format!(
                        "v0: unhandled expression: {:?}",
                        occ.as_expr().map(std::mem::discriminant)
                    )));
                };
                let op = self.kb.qualified_name_of(functor);
                // `ite(cond, then, else)` functor form (WI-680): the surface
                // `if` is not expressible in a rule body (parser-gated to op
                // bodies), so a hand-written defining twin spells the
                // conditional `ite(...)`. Same lowering as `Expr::If`. (stdlib's
                // `<=>` twins — `sign`/`max`/`min` — also spell it `ite`, but are
                // stored as EQUATIONS, not reached by this op-call inline path; a
                // separate `<=>`-twin lowering, out of WI-680's scope.)
                if self.builtins.is_ite(functor) {
                    if pos_args.len() != 3 {
                        return Err(SmtGenError::new(format!(
                            "ite: expected 3 pos_args, got {}",
                            pos_args.len()
                        )));
                    }
                    let c = self.translate_condition(&pos_args[0], bindings)?;
                    let t = self.translate_expr(&pos_args[1], bindings)?;
                    let e = self.translate_expr(&pos_args[2], bindings)?;
                    return Ok(format!("(ite {c} {t} {e})"));
                }
                // Trigonometric functions (WI-681): no SMT-LIB Real form, so
                // `cos(θ)`/`sin(θ)` render as the uninterpreted functions
                // `anthill_cos`/`anthill_sin`. The render adds the Pythagorean
                // identity `cos(θ)²+sin(θ)²=1` for each θ seen — the one
                // nonlinear fact norm-preservation of a 2-D rotation needs.
                if let Some(trig) = self.builtins.trig(functor) {
                    if pos_args.len() != 1 {
                        return Err(SmtGenError::new(format!(
                            "{op}: expected 1 pos_arg, got {}",
                            pos_args.len()
                        )));
                    }
                    let a = self.translate_expr(&pos_args[0], bindings)?;
                    self.trig_args.insert(a.clone());
                    return Ok(format!("({trig} {a})"));
                }
                if let Some(smt_op) = self.builtins.unary(functor) {
                    if pos_args.len() != 1 {
                        return Err(SmtGenError::new(format!(
                            "{op}: expected 1 pos_arg, got {}",
                            pos_args.len()
                        )));
                    }
                    let a = self.translate_expr(&pos_args[0], bindings)?;
                    if smt_op == "anthill_abs" {
                        self.uses_abs = true;
                    }
                    return Ok(format!("({smt_op} {a})"));
                }
                let smt_op = match self.builtins.arith(functor) {
                    Some(o) => o,
                    None => {
                        return Err(SmtGenError::new(format!(
                            "v0: unhandled arithmetic op '{op}'"
                        )))
                    }
                };
                if pos_args.len() != 2 {
                    return Err(SmtGenError::new(format!(
                        "{op}: expected 2 pos_args, got {}",
                        pos_args.len()
                    )));
                }
                let a = self.translate_expr(&pos_args[0], bindings)?;
                let b = self.translate_expr(&pos_args[1], bindings)?;
                Ok(format!("({smt_op} {a} {b})"))
            }
        }
    }

    /// Translate a Bool-valued occurrence to an SMT-LIB *formula* — the
    /// condition slot of an `ite`/`if` (WI-680). SMT-LIB segregates Bool from
    /// Real, so a condition can't go through `translate_expr` (which yields a
    /// Real term); this is the Bool sibling. Handles the relational ops
    /// (`gte`/`lte`/`gt`/`lt`), equality (`=`/`eq`), and the Bool connectives
    /// (`and`/`or`/`not`) recursively; a bare `true`/`false` literal folds
    /// directly. Any other shape (including a bare Bool variable, which this
    /// Real-typed emitter can't yet carry) is a *loud* error, not a guess.
    fn translate_condition(
        &mut self,
        occ: &Rc<NodeOccurrence>,
        bindings: &BTreeMap<String, String>,
    ) -> Result<String, SmtGenError> {
        if let Some(Expr::Const(Literal::Bool(b))) = occ.as_expr() {
            return Ok(if *b {
                "true".to_string()
            } else {
                "false".to_string()
            });
        }
        let Some((functor, pos_args, _named)) = occ_as_fn(occ) else {
            return Err(SmtGenError::new(format!(
                "v0: unhandled condition shape: {:?}",
                occ.as_expr().map(std::mem::discriminant)
            )));
        };
        let qn = self.kb.qualified_name_of(functor);
        // Relational comparison → SMT-LIB predicate over Real operands.
        if let Some(smt_op) = self.builtins.inequality(functor) {
            if pos_args.len() != 2 {
                return Err(SmtGenError::new(format!(
                    "{qn}: expected 2 pos_args in condition, got {}",
                    pos_args.len()
                )));
            }
            let a = self.translate_expr(&pos_args[0], bindings)?;
            let b = self.translate_expr(&pos_args[1], bindings)?;
            return Ok(format!("({smt_op} {a} {b})"));
        }
        // Equality → `(= a b)` over Real operands.
        if self.is_eq_functor(functor) {
            if pos_args.len() != 2 {
                return Err(SmtGenError::new(format!(
                    "=: expected 2 pos_args in condition, got {}",
                    pos_args.len()
                )));
            }
            let a = self.translate_expr(&pos_args[0], bindings)?;
            let b = self.translate_expr(&pos_args[1], bindings)?;
            return Ok(format!("(= {a} {b})"));
        }
        // Bool connective → recurse into sub-conditions.
        if let Some(conn) = self.builtins.bool_connective(functor) {
            let arity = if conn == "not" { 1 } else { 2 };
            if pos_args.len() != arity {
                return Err(SmtGenError::new(format!(
                    "{qn}: expected {arity} pos_args in condition, got {}",
                    pos_args.len()
                )));
            }
            let subs: Result<Vec<String>, _> = pos_args
                .iter()
                .map(|p| self.translate_condition(p, bindings))
                .collect();
            return Ok(format!("({conn} {})", subs?.join(" ")));
        }
        Err(SmtGenError::new(format!(
            "v0: unhandled condition functor '{qn}' (expected a relational op, \
             `=`, or a Bool connective and/or/not)"
        )))
    }

    /// Substitute `env` (this frame's entity bindings: synth var name →
    /// entity occurrence) and `str_env` (this frame's scalar bindings: synth
    /// var name → already-translated SMT fragment) into `occ`, returning a
    /// structurally-closed copy (WI-681, WI-686). A body-derived constructor
    /// (e.g. `desired_position`'s `Vec3(x: add(leader.position.x, …), …)`)
    /// carries the op's parameters as callee-frame DeBruijn vars; once the
    /// constructor is bound as an entity and propagated to a caller (or read
    /// by a later-inlined rule), those indices no longer denote the same
    /// frame. Substituting the param vars here — while still in the frame that
    /// bound them — closes the constructor: field access then bottoms out at
    /// ground values, never a dangling callee var.
    ///
    /// A DeBruijn var is closed by (in order): its `env` entity binding
    /// (WI-681 — an entity-typed param, e.g. `leader`/`offset`); else its
    /// `str_env` scalar binding (WI-686 — a scalar-typed param whose value is
    /// a caller-frame SMT fragment, e.g. `TransponderFollowerState{ upc:
    /// ite(…upc…) }`); else a loud error (a param with no binding on either
    /// channel can't be closed across the boundary). See [`scalar_param_occ`]
    /// for how a scalar fragment becomes a (frozen) substitute occurrence.
    /// Loud error on an occurrence shape a defining-equation body should never
    /// contain.
    fn close_occ(
        &self,
        occ: &Rc<NodeOccurrence>,
        env: &BTreeMap<String, Rc<NodeOccurrence>>,
        str_env: &BTreeMap<String, String>,
    ) -> Result<Rc<NodeOccurrence>, SmtGenError> {
        let Some(expr) = occ.as_expr() else {
            return Ok(Rc::clone(occ));
        };
        let rebuilt = match expr {
            Expr::Var(Var::DeBruijn(i)) => {
                let synth = synthetic_var_name(*i);
                // A param var MUST resolve to a binding on one of the two
                // channels: a body-derived constructor's free vars are its op's
                // parameters, and closing them is the whole point (leaving one
                // live would let a callee-frame index dangle into the caller — a
                // silently-wrong value, not a loud failure). Entity-typed params
                // resolve via `env` (WI-681); scalar-typed params via `str_env`
                // (WI-686). A DeBruijn absent from BOTH is a param with no
                // binding at all — error loudly rather than clone it across the
                // boundary.
                if let Some(bound) = env.get(&synth) {
                    return Ok(Rc::clone(bound));
                }
                return match str_env.get(&synth) {
                    Some(smt) => Ok(scalar_param_occ(smt, occ.span, occ.owner)),
                    None => Err(SmtGenError::new(format!(
                        "close_occ: parameter ?{i} in a body-derived entity is bound \
                         on neither the entity nor the scalar channel — it cannot be \
                         closed across the inline boundary"
                    ))),
                };
            }
            Expr::Var(_) | Expr::Const(_) | Expr::Ref(_) | Expr::Ident(_) => {
                return Ok(Rc::clone(occ));
            }
            Expr::Apply {
                functor,
                pos_args,
                named_args,
                type_args,
            } => Expr::Apply {
                functor: *functor,
                pos_args: self.close_all(pos_args, env, str_env)?,
                named_args: self.close_named(named_args, env, str_env)?,
                type_args: type_args.clone(),
            },
            // Proposal 055 — a nominal type value closes like the two shapes it
            // replaced: the BARE face was an `Expr::Ref` and passed through as a leaf,
            // the APPLIED face was an `Expr::Apply` and closed its children. Both are
            // this one arm (a bare one simply has no children). Without it a `[simp]`
            // body that merely MENTIONS a type would reach the loud `other =>` arm
            // below and fail SMT lowering, where it lowered fine before.
            Expr::TypeValue {
                head,
                pos_args,
                named_args,
            } => Expr::TypeValue {
                head: *head,
                pos_args: self.close_all(pos_args, env, str_env)?,
                named_args: self.close_named(named_args, env, str_env)?,
            },
            Expr::Constructor {
                name,
                pos_args,
                named_args,
                from_projection,
            } => Expr::Constructor {
                name: *name,
                pos_args: self.close_all(pos_args, env, str_env)?,
                named_args: self.close_named(named_args, env, str_env)?,
                from_projection: *from_projection,
            },
            Expr::Instantiation {
                name,
                pos_args,
                named_args,
            } => Expr::Instantiation {
                name: *name,
                pos_args: self.close_all(pos_args, env, str_env)?,
                named_args: self.close_named(named_args, env, str_env)?,
            },
            Expr::DotApply {
                receiver,
                name,
                pos_args,
                named_args,
            } => Expr::DotApply {
                receiver: self.close_occ(receiver, env, str_env)?,
                name: *name,
                pos_args: self.close_all(pos_args, env, str_env)?,
                named_args: self.close_named(named_args, env, str_env)?,
            },
            Expr::If {
                condition,
                then_branch,
                else_branch,
            } => Expr::If {
                condition: self.close_occ(condition, env, str_env)?,
                then_branch: self.close_occ(then_branch, env, str_env)?,
                else_branch: self.close_occ(else_branch, env, str_env)?,
            },
            other => {
                return Err(SmtGenError::new(format!(
                    "close_occ: unhandled occurrence shape in a defining-equation \
                 body: {:?}",
                    std::mem::discriminant(other)
                )))
            }
        };
        Ok(NodeOccurrence::new_expr(rebuilt, occ.span, occ.owner))
    }

    fn close_all(
        &self,
        occs: &[Rc<NodeOccurrence>],
        env: &BTreeMap<String, Rc<NodeOccurrence>>,
        str_env: &BTreeMap<String, String>,
    ) -> Result<Vec<Rc<NodeOccurrence>>, SmtGenError> {
        occs.iter()
            .map(|o| self.close_occ(o, env, str_env))
            .collect()
    }

    fn close_named(
        &self,
        named: &[(Symbol, Rc<NodeOccurrence>)],
        env: &BTreeMap<String, Rc<NodeOccurrence>>,
        str_env: &BTreeMap<String, String>,
    ) -> Result<Vec<(Symbol, Rc<NodeOccurrence>)>, SmtGenError> {
        named
            .iter()
            .map(|(s, o)| Ok((*s, self.close_occ(o, env, str_env)?)))
            .collect()
    }

    /// Resolve `field_access(?obj, Ident(field))` (possibly nested)
    /// to the projected value's occurrence. The chain bottoms out either
    /// at a literal (`Expr::Const`) or a value that itself goes back through
    /// translate_expr — typically a leaf Float in an entity's named args.
    ///
    /// Resolution rules:
    /// - root `?var` → look up `entity_bindings[var_<i>]`. The bound
    ///   occurrence is expected to be a constructor with named args (an
    ///   entity instance).
    /// - root `field_access(...)` → recurse on the nested chain.
    /// - root entity constructor occurrence → use directly.
    fn resolve_field_access(
        &self,
        occ: &Rc<NodeOccurrence>,
    ) -> Result<Rc<NodeOccurrence>, SmtGenError> {
        let (object_occ, field_name) = self.as_field_access(occ).ok_or_else(|| {
            SmtGenError::new(format!(
                "resolve_field_access: not a field projection: {:?}",
                occ.as_expr().map(std::mem::discriminant)
            ))
        })?;

        // Step 1: resolve the object to an entity constructor occurrence.
        let entity_occ: Rc<NodeOccurrence> = match object_occ.as_expr() {
            Some(Expr::Var(Var::DeBruijn(i))) => {
                let synth = synthetic_var_name(*i);
                self.entity_bindings.get(&synth).cloned().ok_or_else(|| {
                    SmtGenError::new(format!(
                        "field_access on '?{synth}': no entity binding\
                         (caller did not supply a concrete entity)"
                    ))
                })?
            }
            _ => {
                // A nested projection (`?p.position.x`) — the object is
                // itself a `field_access` / value-receiver `dot_apply`; else
                // it is a directly-supplied entity constructor.
                if self.as_field_access(&object_occ).is_some() {
                    self.resolve_field_access(&object_occ)?
                } else if occ_as_fn(&object_occ).is_some() {
                    object_occ
                } else {
                    return Err(SmtGenError::new(format!(
                        "field_access: cannot resolve object: {:?}",
                        object_occ.as_expr().map(std::mem::discriminant)
                    )));
                }
            }
        };

        // Step 2: project into the entity's named_args by short-name match.
        let Some((_, _, named_args)) = occ_as_fn(&entity_occ) else {
            return Err(SmtGenError::new(format!(
                "field_access: object resolved to non-Fn occurrence: {:?}",
                entity_occ.as_expr().map(std::mem::discriminant)
            )));
        };
        for (sym, val_occ) in named_args.iter() {
            if self.kb.local_name_of(*sym) == field_name {
                return Ok(Rc::clone(val_occ));
            }
        }
        Err(SmtGenError::new(format!(
            "field_access: field '{field_name}' not found in entity"
        )))
    }

    /// Recognize a field projection in either occurrence representation and
    /// return `(object_occurrence, field_name)`:
    ///   - `Expr::Apply { functor: field_access, pos_args: [obj, field] }`
    ///     — the desugared reflect form (`field_access` is not a materialize
    ///     key, so it round-trips to an `Apply`). The field selector is either
    ///     an `Ident`/`Ref` symbol (the parse-IR form for `?p.field` in a rule
    ///     body) or a `Const(String)` — the form a *reduced operation body*
    ///     produces (the reflect builtin takes the field name as a string; see
    ///     `reflect_field_access`), which WI-681's body-derived Vec3 carries.
    ///   - `Expr::DotApply { receiver, name, .. }` — the WI-278 value-receiver
    ///     dot form. Only an EMPTY arg list is a field access; a non-empty
    ///     `pos_args`/`named_args` is a method call (returns `None`).
    fn as_field_access(&self, occ: &Rc<NodeOccurrence>) -> Option<(Rc<NodeOccurrence>, String)> {
        match occ.as_expr()? {
            Expr::DotApply {
                receiver,
                name,
                pos_args,
                named_args,
            } => {
                if !pos_args.is_empty() || !named_args.is_empty() {
                    return None;
                }
                Some((
                    Rc::clone(receiver),
                    self.kb.local_name_of(*name).to_string(),
                ))
            }
            _ => {
                let (functor, pos_args, _named) = occ_as_fn(occ)?;
                let op = self.kb.qualified_name_of(functor);
                if op == "anthill.reflect.field_access" || op == "field_access" {
                    if let [obj, field] = pos_args {
                        let field_name = match field.as_expr()? {
                            Expr::Ref(s) | Expr::Ident(s) => self.kb.local_name_of(*s).to_string(),
                            Expr::Const(Literal::String(name)) => name.clone(),
                            _ => return None,
                        };
                        return Some((Rc::clone(obj), field_name));
                    }
                }
                None
            }
        }
    }

    /// True if `sym` is the equation predicate. The loader desugars a goal-position
    /// `=` to `anthill.prelude.PartialEq.eq` (WI-644 put `eq` on the `PartialEq` base
    /// for the same reason the comparisons sit on `PartialOrd`), which is the
    /// [`SmtBuiltin::Eq`] row; a `Term::Fn` may still carry the bare OPERATOR
    /// spelling `=`, which no declaration can mint and so nothing can collide with.
    ///
    /// WI-897 — THE SHORT NAME `eq` NO LONGER COUNTS. Matching it turned a user's own
    /// `Widget.eq` into SMT equality over Reals: WI-680's hazard, in the one table
    /// that was already shaped to take a `Symbol`. The `anthill.prelude.Eq.eq` arm
    /// went with it — MEASURED against a stdlib KB, that name resolves to nothing.
    fn is_eq_functor(&self, sym: anthill_core::intern::Symbol) -> bool {
        if self.builtins.is_eq(sym) {
            return true;
        }
        self.kb.qualified_name_of(sym) == "=" || self.kb.local_name_of(sym) == "="
    }

    /// True if the symbol resolves to an entity declaration.
    fn is_known_entity(&self, sym: anthill_core::intern::Symbol) -> bool {
        self.kb.entity_field_types(sym).is_some()
    }

    /// Classify a rule's head for the `collect_rule` dispatcher. The
    /// classification mirrors what `process_body_goal` would do if
    /// asked to translate the head as a goal: predicate-like heads
    /// (`gte/lte/eq/...` or entity destructures) become the
    /// conclusion under proposal 032; function-like heads
    /// (`rule_qn(?result)`) drive upper-bound mode.
    fn classify_head(&self, head: anthill_core::kb::term::TermId) -> HeadShape {
        let term = self.kb.get_term(head);
        let (functor, pos_args) = match term {
            Term::Bottom => return HeadShape::Bottom,
            Term::Fn {
                functor, pos_args, ..
            } => (*functor, pos_args.clone()),
            other => {
                return HeadShape::Unsupported(format!(
                    "rule head must be Fn or Bottom, got {other:?}"
                ))
            }
        };
        let qn = self.kb.qualified_name_of(functor);
        if self.is_eq_functor(functor)
            || self.builtins.inequality(functor).is_some()
            || self.is_known_entity(functor)
        {
            return HeadShape::Predicate;
        }
        if pos_args.len() == 1 {
            let result_idx = match self.kb.get_term(pos_args[0]) {
                Term::Var(Var::DeBruijn(i)) => *i,
                other => {
                    return HeadShape::Unsupported(format!(
                        "v0: function-like rule head's pos_arg must be DeBruijn var, got {other:?}"
                    ))
                }
            };
            return HeadShape::FunctionLike { result_idx };
        }
        if pos_args.is_empty() {
            // 0-arg predicate head (e.g. `rule status_ok :- ...`);
            // body walks for free vars only, no conclusion.
            return HeadShape::Bottom;
        }
        HeadShape::Unsupported(format!(
            "v0: rule head shape not supported (functor={qn}, pos_args={})",
            pos_args.len()
        ))
    }

    /// For each entity referenced in the rule body, find its
    /// (single) ground fact in the KB and resolve every field to a
    /// Real value. Multi-fact handling is a v1 concern.
    ///
    /// Errs on any BODIED rule whose head is a referenced entity
    /// (WI-772): this reader head-matches facts and never evaluates a
    /// body, so `rule LinkParameters(mass: 2.0, …) :- heavy_variant()`
    /// would feed mass=2.0 into the encoding whether or not the guard
    /// holds — a proof discharged from a guarded premise is unsound.
    /// The refusal fires even when a ground fact ALSO exists for the
    /// entity: candidate order (insertion order — source/file-load
    /// order) would otherwise decide which head the harvest picks.
    fn collect_facts_for_referenced_entities(&mut self) -> Result<(), SmtGenError> {
        for entity_qn in self.referenced_entities.clone() {
            let Some(sym) = self.kb.try_resolve_symbol(&entity_qn) else {
                continue;
            };
            let candidates = self
                .kb
                .read_facts(sym, &[], BodiedRulePolicy::Refuse)
                .map_err(|e| match e {
                    ExtentReadError::BodiedRule { .. } => SmtGenError::new(format!(
                        "bodied rule for referenced entity `{entity_qn}` refused: {e} — \
                         guarded field values would enter the SMT encoding unconditionally (WI-772)"
                    )),
                    _ => SmtGenError::new(format!(
                        "referenced entity `{entity_qn}` read failed: {e}"
                    )),
                })?;
            // Accept the first fact whose named_args resolve to numeric
            // literals — that's a ground data fact. (WI-515: only data
            // facts remain; the entity-declaration row with abstract
            // field types is no longer asserted.) Multi-fact
            // disambiguation is a v1 concern; for v0 we expect at most
            // one fact per entity.
            for row in candidates {
                let Value::Term { id: head, .. } = row else {
                    return Err(SmtGenError::new(format!(
                        "referenced entity `{entity_qn}` has a non-term fact row; \
                         SMT v0 requires term-carried numeric fields"
                    )));
                };
                let Term::Fn { named_args, .. } = self.kb.get_term(head) else {
                    continue;
                };
                let any_concrete = named_args
                    .iter()
                    .any(|(_, t)| literal_as_real(self.kb.get_term(*t)).is_some());
                if !any_concrete {
                    continue;
                }
                for (field_sym, val_term) in named_args {
                    let field_name = self.kb.local_name_of(*field_sym).to_string();
                    let const_name = sanitize_smt_id(&field_name);
                    if !self.field_consts.contains_key(&const_name) {
                        continue;
                    }
                    if let Some(v) = literal_as_real(self.kb.get_term(*val_term)) {
                        self.field_consts.insert(const_name, v);
                    }
                }
                break;
            }
        }
        Ok(())
    }

    fn render_upper_bound_with(&self, obligation: &Obligation, config: &ProofConfig) -> String {
        let logic = config.logic.as_deref().unwrap_or("QF_LRA");
        let mut out = String::new();
        out.push_str(&format!(
            "; Generated by anthill-smt-gen for obligation {}.\n",
            obligation.rule_qn
        ));
        out.push_str(&format!("; Logic: {logic}.\n"));
        if let Some(t) = config.timeout_ms {
            out.push_str(&format!("(set-option :timeout {t})\n"));
        }
        emit_outcome_options(&mut out, config);
        out.push_str(&format!("(set-logic {logic})\n\n"));

        emit_abs_prelude(&mut out, self.uses_abs, config);

        for (name, value) in &self.field_consts {
            out.push_str(&format!(
                "(define-fun {name} () Real {})\n",
                format_real(*value)
            ));
        }
        out.push('\n');

        emit_trig_prelude(&mut out, &self.trig_args);

        emit_assumptions(&mut out, config);

        out.push_str(&self.body_smtlib);
        out.push_str("\n\n");

        out.push_str(&format!(
            "; Obligation: {} <= {}\n",
            self.result_var, obligation.upper_bound
        ));
        out.push_str(&format!(
            "(assert (not (<= {} {})))\n",
            sanitize_smt_id(&self.result_var),
            format_real(obligation.upper_bound)
        ));
        match &config.tactic_expr {
            Some(expr) => out.push_str(&format!("(check-sat-using {expr})\n")),
            None => out.push_str("(check-sat)\n"),
        }
        emit_outcome_getters(&mut out, config);
        out
    }

    fn render_satisfiability_with(&self, rule_qn: &str, config: &ProofConfig) -> String {
        // `LRA` is the default for satisfiability mode (handles `abs`
        // via the standard if-then-else encoding Z3 applies).
        let logic = config.logic.as_deref().unwrap_or("LRA");
        let mut out = String::new();
        out.push_str(&format!(
            "; Generated by anthill-smt-gen — satisfiability check for rule {rule_qn}.\n"
        ));
        out.push_str("; `unsat` ⇒ rule body has no solution ⇒ encoded property holds.\n");
        if let Some(t) = config.timeout_ms {
            out.push_str(&format!("(set-option :timeout {t})\n"));
        }
        emit_outcome_options(&mut out, config);
        out.push_str(&format!("(set-logic {logic})\n\n"));

        emit_abs_prelude(&mut out, self.uses_abs, config);

        for (name, value) in &self.field_consts {
            out.push_str(&format!(
                "(define-fun {name} () Real {})\n",
                format_real(*value)
            ));
        }
        out.push('\n');

        // Free vars (`?d_prev`, `?step`, etc. that appear in
        // assertions but aren't bound by an `=` clause) become
        // existentially-quantified inputs to the satisfiability
        // check — declared as global Real consts so `(check-sat)`
        // picks values for them if any exist.
        for v in &self.free_vars {
            out.push_str(&format!("(declare-const {v} Real)\n"));
        }
        out.push('\n');

        emit_trig_prelude(&mut out, &self.trig_args);

        emit_assumptions(&mut out, config);

        // Body equations bound the result vars; emit them as
        // define-funs so subsequent assertions can reference them.
        // For satisfiability mode we don't have a single result var
        // but intermediate bindings still matter.
        if !self.body_smtlib.is_empty() {
            out.push_str(&self.body_smtlib);
            out.push_str("\n\n");
        }

        for assertion in &self.assertions {
            out.push_str(&format!("(assert {assertion})\n"));
        }
        // Conclusion clauses (from the `-:` separator) are NEGATED
        // for the discharge: prove `body ∧ ¬conclusion` unsat ⇒
        // `body ⇒ conclusion`. AND-conjoined into a single
        // negation so the verdict cleanly mirrors the lemma's
        // theorem statement.
        if !self.conclusion_assertions.is_empty() {
            out.push_str("; Negated conclusion (from `-:` clause).\n");
            let conj = if self.conclusion_assertions.len() == 1 {
                self.conclusion_assertions[0].clone()
            } else {
                format!("(and {})", self.conclusion_assertions.join(" "))
            };
            out.push_str(&format!("(assert (not {conj}))\n"));
        }
        match &config.tactic_expr {
            Some(expr) => out.push_str(&format!("\n(check-sat-using {expr})\n")),
            None => out.push_str("\n(check-sat)\n"),
        }
        emit_outcome_getters(&mut out, config);
        out
    }
}

/// Splice cited-lemma clauses into the preamble. Each entry in
/// `config.assumptions` is wrapped in `(assert …)` and emitted
/// after field consts but before the body / assertions, so the
/// hypothesis is in scope when Z3 decides the goal. Order is
/// preserved to keep cache keys stable.
/// Emit the `anthill_abs` define-fun prelude when any rendered
/// expression (the rule's own body via `uses_abs`, or any cited
/// lemma's assumption block) references it. SMT-LIB has no built-in
/// `abs` for Real in LRA/NRA/QF_*; without this prelude `(abs x)`
/// degenerates to an uninterpreted function (silent unsoundness or
/// `unknown` verdicts).
fn emit_abs_prelude(out: &mut String, uses_abs: bool, config: &ProofConfig) {
    let needs = uses_abs
        || config
            .assumptions
            .iter()
            .any(|a| a.contains("anthill_abs "));
    if needs {
        out.push_str("(define-fun anthill_abs ((x Real)) Real (ite (< x 0) (- x) x))\n\n");
    }
}

/// Emit the trigonometric prelude (WI-681): declare `anthill_cos`/`anthill_sin`
/// as uninterpreted `(Real) Real` functions and, for each argument θ seen,
/// assert the Pythagorean identity `cos(θ)²+sin(θ)²=1`. That single nonlinear
/// fact is what lets QF_NRA prove a 2-D rotation preserves norm; the functions
/// are otherwise uninterpreted, so the proof holds for EVERY θ (yaw-independent)
/// rather than assuming a concrete angle. No-op when no trig was rendered.
fn emit_trig_prelude(out: &mut String, trig_args: &BTreeSet<String>) {
    if trig_args.is_empty() {
        return;
    }
    out.push_str("; Trig as uninterpreted reals + Pythagorean identity (WI-681).\n");
    out.push_str("(declare-fun anthill_cos (Real) Real)\n");
    out.push_str("(declare-fun anthill_sin (Real) Real)\n");
    for a in trig_args {
        out.push_str(&format!(
            "(assert (= (+ (* (anthill_cos {a}) (anthill_cos {a})) \
             (* (anthill_sin {a}) (anthill_sin {a}))) 1.0))\n"
        ));
    }
    out.push('\n');
}

fn emit_assumptions(out: &mut String, config: &ProofConfig) {
    if config.assumptions.is_empty() {
        return;
    }
    out.push_str("; Cited-lemma assumptions (from `using` clause).\n");
    // Dedupe `(declare-const var_<i> Real)` lines across all
    // assumptions — different cited step rules may share step-new
    // vars (the converter shares VarIds across consecutive steps in
    // a structured proof body), and Z3 rejects
    // a duplicate constant declaration.
    let mut seen_decls: BTreeSet<String> = BTreeSet::new();
    for clause in &config.assumptions {
        for line in clause.split('\n') {
            if line.trim().is_empty() {
                continue;
            }
            if line.starts_with("(declare-const ") {
                if !seen_decls.insert(line.to_string()) {
                    continue;
                }
            }
            out.push_str(line);
            out.push('\n');
        }
    }
    out.push('\n');
}

/// Append `(set-option :produce-* true)` lines to the preamble for
/// any outcome flags set in `config`. Z3 requires the option to be
/// set BEFORE `(set-logic ...)`.
fn emit_outcome_options(out: &mut String, config: &ProofConfig) {
    if config.produce_models {
        out.push_str("(set-option :produce-models true)\n");
    }
    if config.produce_unsat_cores {
        out.push_str("(set-option :produce-unsat-cores true)\n");
    }
    if config.produce_interpolants {
        out.push_str("(set-option :produce-interpolants true)\n");
    }
}

/// Append `(get-model)` / `(get-unsat-core)` after `(check-sat)` for
/// any outcome flags set in `config`. Z3 only honours these when the
/// matching `:produce-*` option was set; the parser-side outcome
/// reader tolerates missing blocks.
fn emit_outcome_getters(out: &mut String, config: &ProofConfig) {
    if config.produce_models {
        out.push_str("(get-model)\n");
    }
    if config.produce_unsat_cores {
        out.push_str("(get-unsat-core)\n");
    }
    // `(get-interpolants)` is intentionally not emitted: Z3's
    // interpolant API takes named (assert! ... :named ...) annotations
    // that the current emitter doesn't produce. Phase 5 follow-up.
}

/// View an occurrence as a function-application-shaped goal/expression —
/// `(functor, pos_args, named_args)`. Covers the occurrence analogues of
/// `Term::Fn` that a rule-body atom or arithmetic expression takes: the
/// native body shape `Expr::Apply`, entity `Expr::Constructor`,
/// `Expr::Instantiation`, and their requirements-carrying `*Within`
/// variants. Returns `None` for leaves, control-flow forms, and
/// `Expr::DotApply` (the dot field/method form — handled by
/// `Emitter::as_field_access`).
fn occ_as_fn(
    occ: &NodeOccurrence,
) -> Option<(
    Symbol,
    &[Rc<NodeOccurrence>],
    &[(Symbol, Rc<NodeOccurrence>)],
)> {
    match occ.as_expr()? {
        Expr::Apply {
            functor,
            pos_args,
            named_args,
            ..
        }
        // Proposal 055 — the applied face answers with its head and type arguments,
        // which is what it answered as an `Expr::Apply` before it was classified. The
        // bare face answers through this arm too, with empty argument lists, which is
        // what `nullary_ctor_sym` needs to keep reading its symbol.
        | Expr::TypeValue {
            head: functor,
            pos_args,
            named_args,
        } => Some((*functor, pos_args, named_args)),
        Expr::Constructor {
            name,
            pos_args,
            named_args,
            ..
        }
        | Expr::Instantiation {
            name,
            pos_args,
            named_args,
        }
        | Expr::ConstructorWithin {
            name,
            pos_args,
            named_args,
            ..
        } => Some((*name, pos_args, named_args)),
        Expr::ApplyWithin {
            functor,
            args,
            named_args,
            ..
        } => Some((*functor, args, named_args)),
        _ => None,
    }
}

/// The functor of a NULLARY constructor occurrence — a bare `Ref`/`Ident`, or an
/// arg-less `Fn`/`Constructor` (`none` / `Fn{none, [], []}`) — else `None` (a De
/// Bruijn var, a literal, or an arity-bearing construction). Used by
/// `bind_head_arg` to verify a nullary head constructor against the call arg.
fn nullary_ctor_sym(occ: &Rc<NodeOccurrence>) -> Option<Symbol> {
    match occ.as_expr()? {
        Expr::Ref(s) | Expr::Ident(s) => Some(*s),
        _ => match occ_as_fn(occ) {
            Some((f, pos, named)) if pos.is_empty() && named.is_empty() => Some(f),
            _ => None,
        },
    }
}

/// Synthetic SMT identifier for a de Bruijn-indexed variable. The
/// loaded rule has dropped the user-given names, so we use the index
/// directly. Output is deterministic and collision-free with field
/// names (which never start with `var_<digit>`).
fn synthetic_var_name(idx: u32) -> String {
    format!("var_{idx}")
}

/// Inverse of `synthetic_var_name` — parse `"var_<i>"` back to `i`.
/// Returns None for any other string shape.
fn parse_synthetic_var_name(s: &str) -> Option<u32> {
    s.strip_prefix("var_").and_then(|n| n.parse::<u32>().ok())
}

/// WI-686 — re-encode a scalar operation parameter's caller-frame SMT
/// fragment as a substitute occurrence, so `close_occ` can close a
/// body-derived constructor whose field is computed from that scalar param
/// (e.g. `TransponderFollowerState{ upc: ite(…upc…) }`). The fragment is the
/// value `try_inline_rule_call` threaded into the callee string map: already
/// translated and, at the point it is captured, fully resolved into the
/// caller's frame (a forwarded free var `var_j`, a field const `upc`, a
/// literal `(- 5.0)`, or a compound `(+ …)`). It is FROZEN verbatim as a
/// `Const::String` fragment that `translate_expr` emits as-is.
///
/// Freezing (rather than re-encoding a `var_j` back to a live `Var::DeBruijn`)
/// is deliberate: the fragment is the param's value at the binding point, and
/// every token it names is a caller-frame identifier the caller already
/// declares (the free-var text scan picks up a bare `var_j`; a field const /
/// literal is self-contained). A frozen fragment is also frame-stable — it
/// carries no live index that a later inline level could re-resolve against
/// the wrong frame — and it cannot misread a field const that happens to spell
/// `var_<digits>` as a de Bruijn index.
fn scalar_param_occ(
    smt: &str,
    span: anthill_core::span::SourceSpan,
    owner: Option<Symbol>,
) -> Rc<NodeOccurrence> {
    NodeOccurrence::new_expr(Expr::Const(Literal::String(smt.to_string())), span, owner)
}

/// WHICH ANTHILL OPERATION MEANS WHICH SMT-LIB FORM (WI-897) — one row per
/// operation, keyed by QUALIFIED NAME and matched by SYMBOL IDENTITY.
///
/// Every one of these decisions used to be a string compare against
/// `qualified_name_of(functor)`, and each table spelled a fully-qualified /
/// sort-qualified / bare TRIPLE (`"anthill.prelude.Numeric.add" | "Numeric.add" |
/// "add"`). WI-680 recorded what the bare arm costs: a user's own `add` is
/// indistinguishable from the prelude's and is silently reinterpreted as SMT `+`.
/// WI-894 made the principled form reachable by giving a rule-introduced functor
/// (`ite`) a qualified identity of its own; this table is the form.
///
/// THE OTHER TWO SPELLINGS ARE GONE, AND NEITHER MEANT WHAT THE OLD TABLES TOOK IT
/// TO MEAN.
///
/// The SORT-QUALIFIED one (`Numeric.add`) could be resolved — just never to the
/// prelude. A TOP-LEVEL `sort Numeric` is legal, and the stdlib writes its own the
/// same way, only dotted (`sort anthill.prelude.Numeric`); an undotted one
/// qualifies its members as `Numeric.add` verbatim. That is WI-680's hazard with a
/// real program behind it, and it is what `wi897_symbol_identity_test` drives.
///
/// The BARE one (`add`) could only come from a `SymbolDef::Unresolved` functor —
/// `by_qualified_name` holds fully qualified names only — i.e. a name the loader
/// never resolved. That is not hypothetical either: it was LIVE in this repo's own
/// lf1 example. `safety_common.anthill` wrote `abs(?d_next - ?d_prev)` without
/// importing it, and since `abs` is a member of BOTH `Float` and `Int64` the bare
/// name resolves to neither; nothing reported it (its two uses sit in a `-:` clause
/// and a proof step, not the call sites WI-1056 checks), and this table lowered it
/// anyway off the short-name arm. Deleting the arm surfaced it as `unhandled
/// arithmetic op 'abs'` in `prove_tactic_test::legacy_lf1_proofs_unchanged`, and
/// the fix was to make the name real — the spec now imports
/// `anthill.prelude.Float.{abs}`, as its `safety_gps.anthill` sibling already did.
/// A loud refusal is the whole point: the emitter cannot know which carrier's `abs`
/// an unresolved name meant, and a proof obligation is the last place to guess.
///
/// MEASURED, not assumed, for the rows that are ABSENT here: `anthill.prelude.Ord.
/// {gt,lt,gte,lte}` and `anthill.prelude.Eq.eq` — all five carried by the old
/// tables — resolve to NOTHING against a stdlib KB. WI-644/WI-1109 moved the four
/// comparisons onto `PartialOrd` and `eq` onto `PartialEq`, and left no aliases
/// behind: `import anthill.prelude.Ord.{gte}` resolves THROUGH the tower to
/// `anthill.prelude.PartialOrd.gte`, which is the row below. A dead row would be
/// indistinguishable from a live one here (`resolve` just skips what it cannot
/// find), so they are omitted rather than carried on trust.
const SMT_BUILTINS: &[(&str, SmtBuiltin)] = &[
    // Arithmetic. Linear-arithmetic only (`/` against a Real constant is still
    // linear in QF_LRA). `Int64`/`Float` do not declare their own `add`/`sub`/`mul`
    // — they provide `Numeric`, so those three resolve to the SPEC op's symbol for
    // every carrier; `div` is declared per carrier and needs two rows.
    //
    // WI-20260824-VT8CF — AND `anthill.prelude.Divisible.div` IS DELIBERATELY ABSENT,
    // which is a REFUSAL and not an oversight. That ticket made `div` a spec operation
    // as well as a per-carrier one, so a BARE `/` — with no import naming a carrier's
    // `div` — now resolves to the spec op: ONE symbol serving both carriers. This emitter
    // keys on the functor alone and has no operand sort at the site, and the two carriers
    // need DIFFERENT SMT operators: `div` is SMT-LIB INTEGER division, `/` is Real. A row
    // either way would be silently wrong for the other carrier, on a proof obligation —
    // the last place to guess, as this table's `abs` note already argues. So a bare `/`
    // fails loudly with `unhandled arithmetic op 'div'`.
    //
    // BOTH HALVES REGRESSED, and the integer one is the easier to overlook. A bare
    // `a / b` over `Float` never worked at all before (the tier pointed at `Int64.div`,
    // so it was a type error); a bare `a / b` over `Int64` DID work and emitted SMT-LIB
    // `div`, and now needs an `import anthill.prelude.Int64.{div}` it never needed. The
    // repair is a carrier-naming import either way — `Float.{div}` for the float half, as
    // `examples/webots-modelling/lf1/safety_gps.anthill` and the `comm_delay` /
    // `step_distance` tests already write, and `Int64.{div}` for the integer half. NO
    // in-tree `.anthill` file is affected (censused: every bare `/` in the stdlib, the
    // examples and the binding dirs is inside a comment or a string), so this is
    // user-facing only.
    //
    // Lowering the spec op needs the emitter to carry the operand sort; that is its own
    // change, with its own census of what else keys on a functor alone.
    // WI-20260825-1WBZT — the SYNTAX CATEGORY that declares each, not the `Numeric`
    // bundle that used to. Keyed by qualified name, so a moved declaration is a moved key
    // or the lowering silently stops (`+` would emit an uninterpreted function instead of
    // SMT `+`, and the discharge would just get weaker).
    ("anthill.prelude.Additive.add", SmtBuiltin::Arith("+")),
    ("anthill.prelude.Additive.sub", SmtBuiltin::Arith("-")),
    ("anthill.prelude.Multiplicative.mul", SmtBuiltin::Arith("*")),
    // WI-20260825-KD9SW — A MINTED `/` NAMES `Divisible.div`, AND THE REFUSAL ABOVE STILL
    // STANDS. That ticket made an operator uncapturable, so the `import
    // anthill.prelude.Float.{div}` that `safety_gps.anthill` writes no longer retargets a
    // minted `/` — which means the lf1 discharge was relying on exactly the capture KD9SW
    // removes. The repair is the one VT8CF's paragraph already prescribes and §5.5 now
    // states: NAME THE CARRIER at the site (`Float.div(a, b)`), not a spec-op row here.
    // Adding one was tried and is UNSOUND: `operation q() -> Int64 = 7 / 2` loads clean
    // (driven), so a single row lowers Int64 division to SMT-LIB REAL `/`. Found by
    // `/code-review`.
    // The three rows above were re-keyed onto their syntax categories by WI-1WBZT; `/`
    // was left on the CARRIERS because until KD9SW a minted `/` resolved its short
    // functor by SCOPE, so a file writing `import anthill.prelude.Float.{div}` made it
    // mean `Float.div` — which is exactly the capture that ticket removes. Driven: the
    // lf1 spec does write that import, and its `/` emitted SMT `/` only through it.
    //
    // BOTH CARRIER ROWS STAY. They are what a WRITTEN `Float.div(a, b)` still resolves
    // to, and dropping them would silently weaken every discharge that spells it out.
    ("anthill.prelude.Float.div", SmtBuiltin::Arith("/")),
    ("anthill.prelude.Int64.div", SmtBuiltin::Arith("div")),
    // Trigonometry (WI-681). SMT-LIB's Real logics have no transcendental cos/sin,
    // so they ride as uninterpreted `anthill_cos`/`anthill_sin` reals; the ONLY
    // fact the emitter injects about them is the Pythagorean identity
    // `cos(θ)²+sin(θ)²=1` per argument (see `emit_trig_prelude`) — sufficient for
    // the norm-preservation of a 2-D rotation, and nothing more is claimed.
    ("anthill.prelude.Float.cos", SmtBuiltin::Trig("anthill_cos")),
    ("anthill.prelude.Float.sin", SmtBuiltin::Trig("anthill_sin")),
    // Unary. `abs` is emitted as `anthill_abs` — a `(define-fun anthill_abs
    // ((x Real)) Real (ite (< x 0) (- x) x))` prelude is added to the final SMT
    // script when any call site renders it, because SMT-LIB has no built-in `abs`
    // for Real in the LRA/NRA logics most discharges run under.
    (
        "anthill.prelude.Float.abs",
        SmtBuiltin::Unary("anthill_abs"),
    ),
    (
        "anthill.prelude.Int64.abs",
        SmtBuiltin::Unary("anthill_abs"),
    ),
    ("anthill.prelude.Additive.neg", SmtBuiltin::Unary("-")),
    ("anthill.prelude.Float.neg", SmtBuiltin::Unary("-")),
    ("anthill.prelude.Int64.neg", SmtBuiltin::Unary("-")),
    // `ite` (WI-680). The refolded defining-equation body uses the `Expr::If`
    // occurrence directly; this covers the hand-written / stdlib `ite(...)`
    // spelling of the same conditional. BOTH SPELLINGS ARE LIVE. `ite` is a
    // RULE-INTRODUCED functor rather than an operation (WI-887) — it cannot be an
    // operation at its signature, since a call would evaluate both branches — and
    // WI-894 is what scopes it to `Bool` and so lets it be named here at all.
    ("anthill.prelude.Bool.ite", SmtBuiltin::Ite),
    // Bool connectives for the condition slot of an `ite`/`if` (WI-680).
    // `and`/`or` are binary, `not` unary — the caller checks arity.
    ("anthill.prelude.Bool.and", SmtBuiltin::BoolConn("and")),
    ("anthill.prelude.Bool.or", SmtBuiltin::BoolConn("or")),
    ("anthill.prelude.Bool.not", SmtBuiltin::BoolConn("not")),
    // Comparisons, THREE ROWS DEEP PER OPERATOR because three different sorts
    // declare them and a call resolves to whichever one it named.
    //
    // WI-644 / proposal 004 put gt/lt/gte/lte on the `PartialOrd` base, because IEEE
    // `Float` is comparable but not totally ordered — that is the row a generic or
    // `import anthill.prelude.Ord.{...}` call lands on. But `Float` and `Int64` also
    // DECLARE ALL FOUR themselves (`float.anthill`, `int64.anthill`: host-backed, so a
    // scalar comparison is one host call and `PartialOrd`'s `compare`-based default
    // body has a floor to bottom out on — it reads `Int64.gt` on `compare`'s result).
    // Those are distinct symbols, so `Float.lte(a, b)` — the spelling WI-565's
    // diagnostic tells a user to write — reaches none of the `PartialOrd` rows.
    ("anthill.prelude.PartialOrd.lte", SmtBuiltin::Ineq("<=")),
    ("anthill.prelude.PartialOrd.lt", SmtBuiltin::Ineq("<")),
    ("anthill.prelude.PartialOrd.gte", SmtBuiltin::Ineq(">=")),
    ("anthill.prelude.PartialOrd.gt", SmtBuiltin::Ineq(">")),
    ("anthill.prelude.Float.lte", SmtBuiltin::Ineq("<=")),
    ("anthill.prelude.Float.lt", SmtBuiltin::Ineq("<")),
    ("anthill.prelude.Float.gte", SmtBuiltin::Ineq(">=")),
    ("anthill.prelude.Float.gt", SmtBuiltin::Ineq(">")),
    ("anthill.prelude.Int64.lte", SmtBuiltin::Ineq("<=")),
    ("anthill.prelude.Int64.lt", SmtBuiltin::Ineq("<")),
    ("anthill.prelude.Int64.gte", SmtBuiltin::Ineq(">=")),
    ("anthill.prelude.Int64.gt", SmtBuiltin::Ineq(">")),
    // NOT `String` and NOT `BigInt`, which declare the same four (MEASURED: the
    // prelude's `gt`/`gte`/`lt`/`lte` declarations live in `ordered`, `float`,
    // `int64`, `string`, `bigint`). This emitter models EVERY operand as SMT `Real`,
    // so `<=` is the right lowering exactly where the carrier is a Real-modelled
    // scalar. A lexicographic `String.lte` is not that, and lowering it to `(<= …)`
    // would be a false claim rather than an unsupported one. Nor the abstract
    // algebraic specs over an arbitrary `T` — `Ring.add`/`Field.div` are a carrier's
    // operation only once the carrier is known, and this table cannot know it.
    // Both refuse loudly at the call site, which is the correct answer for them.
    // Equality. WI-644 put `eq` on the `PartialEq` base for the same reason the
    // comparisons sit on `PartialOrd`; the loader desugars a goal-position `=` to
    // exactly this operation. See [`Emitter::is_eq_functor`] for the one spelling
    // that is NOT a symbol — the bare operator `=` a `Term::Fn` may still carry.
    ("anthill.prelude.PartialEq.eq", SmtBuiltin::Eq),
];

/// The SMT-LIB meaning one anthill operation carries. The payload is the emitted
/// SMT operator; `Ite` has none because its rendering is a three-slot form, not an
/// operator applied to translated arguments.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum SmtBuiltin {
    /// Binary arithmetic over Real: `(+ a b)`.
    Arith(&'static str),
    /// Uninterpreted trigonometric function: `(anthill_cos θ)`.
    Trig(&'static str),
    /// Unary arithmetic: `(anthill_abs a)`, `(- a)`.
    Unary(&'static str),
    /// Bool connective in CONDITION position: `(and c d)`.
    BoolConn(&'static str),
    /// Relational predicate over Real operands: `(<= a b)`.
    Ineq(&'static str),
    /// `(ite c t e)`.
    Ite,
    /// `(= a b)` over Real operands.
    Eq,
}

/// [`SMT_BUILTINS`] resolved against one KB — the only thing that decides what an
/// operation MEANS to this emitter. Built once per [`Emitter`]; a lookup is a
/// `Symbol` hash, and a user's own `add` (a different `Symbol`, whatever it is
/// spelled) is simply absent from it.
#[derive(Debug)]
struct SmtBuiltinTable {
    by_symbol: HashMap<Symbol, SmtBuiltin>,
}

impl SmtBuiltinTable {
    /// Resolve every row against `kb` — ALL OF THEM OR NONE OF THEM.
    ///
    /// None is a legitimate KB: one that never loaded the prelude has no builtins,
    /// and every call site's own "unhandled ..." error then says so. A PARTIAL
    /// resolution is not legitimate — it means the prelude IS loaded and the stdlib
    /// moved an operation out from under a row, silently disabling that builtin. The
    /// symptom would surface far away (an `unhandled arithmetic op` on a program that
    /// used to lower, or a premise quietly dropped from an abstract lift), so it is
    /// caught HERE, where the cause is. This is exactly the drift WI-644/WI-1109
    /// already caused once: they moved the four comparisons onto `PartialOrd` and
    /// `eq` onto `PartialEq`, leaving five rows in the old tables that matched
    /// nothing, and nothing noticed because a dead row is silent.
    fn resolve(kb: &KnowledgeBase) -> Self {
        let mut by_symbol = HashMap::with_capacity(SMT_BUILTINS.len());
        let mut missing: Vec<&str> = Vec::new();
        for (qn, builtin) in SMT_BUILTINS {
            let Some(sym) = kb.try_resolve_symbol(qn) else {
                missing.push(qn);
                continue;
            };
            // Two rows collapsing onto one symbol would make this table's meaning
            // depend on row order. It cannot happen with the rows above (each names
            // a distinct declaration), so it is a TABLE bug, not a KB one — loud.
            if let Some(prev) = by_symbol.insert(sym, *builtin) {
                assert_eq!(
                    prev, *builtin,
                    "WI-897: SMT_BUILTINS rows disagree on one symbol ({qn})"
                );
            }
        }
        assert!(
            by_symbol.is_empty() || missing.is_empty(),
            "WI-897: the prelude is loaded but {} SMT_BUILTINS row(s) resolve to \
             nothing — {missing:?}. An operation moved and its row is now dead; \
             point the row at the new declaration.",
            missing.len()
        );
        Self { by_symbol }
    }

    fn get(&self, sym: Symbol) -> Option<SmtBuiltin> {
        self.by_symbol.get(&sym).copied()
    }

    fn arith(&self, sym: Symbol) -> Option<&'static str> {
        match self.get(sym) {
            Some(SmtBuiltin::Arith(op)) => Some(op),
            _ => None,
        }
    }

    fn trig(&self, sym: Symbol) -> Option<&'static str> {
        match self.get(sym) {
            Some(SmtBuiltin::Trig(op)) => Some(op),
            _ => None,
        }
    }

    fn unary(&self, sym: Symbol) -> Option<&'static str> {
        match self.get(sym) {
            Some(SmtBuiltin::Unary(op)) => Some(op),
            _ => None,
        }
    }

    fn bool_connective(&self, sym: Symbol) -> Option<&'static str> {
        match self.get(sym) {
            Some(SmtBuiltin::BoolConn(op)) => Some(op),
            _ => None,
        }
    }

    fn inequality(&self, sym: Symbol) -> Option<&'static str> {
        match self.get(sym) {
            Some(SmtBuiltin::Ineq(op)) => Some(op),
            _ => None,
        }
    }

    fn is_ite(&self, sym: Symbol) -> bool {
        self.get(sym) == Some(SmtBuiltin::Ite)
    }

    fn is_eq(&self, sym: Symbol) -> bool {
        self.get(sym) == Some(SmtBuiltin::Eq)
    }
}

/// Read a `Term::Const(Literal::{Float,Int})` as an f64. Anything
/// else returns `None`.
fn literal_as_real(term: &Term) -> Option<f64> {
    match term {
        Term::Const(Literal::Float(f)) => Some(f.into_inner()),
        Term::Const(Literal::Int(i)) => Some(*i as f64),
        _ => None,
    }
}

/// SMT-LIB number formatter. Uses `(- x)` for negatives because
/// SMT-LIB doesn't accept literal `-1.0`.
fn format_real(v: f64) -> String {
    if v < 0.0 {
        format!("(- {})", format_real(-v))
    } else if v == v.trunc() && v.abs() < 1e15 {
        format!("{:.1}", v)
    } else {
        format!("{:.}", v)
    }
}

/// Replace characters that aren't valid in an unquoted SMT-LIB
/// identifier. Conservative: anthill names use a-z, A-Z, 0-9, `.`,
/// `_`, `-` — we keep the alphanumerics and `_`, replace the rest.
fn sanitize_smt_id(name: &str) -> String {
    let mut out = String::with_capacity(name.len());
    for c in name.chars() {
        match c {
            'a'..='z' | 'A'..='Z' | '0'..='9' | '_' => out.push(c),
            _ => out.push('_'),
        }
    }
    out
}

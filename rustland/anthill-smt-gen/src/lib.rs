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

use std::collections::{BTreeMap, BTreeSet};

use anthill_core::kb::term::{Literal, Term, TermId, Var};
use anthill_core::kb::KnowledgeBase;

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
    emitter.collect_facts_for_referenced_entities();
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
pub fn emit_satisfiability_check(
    kb: &KnowledgeBase,
    rule_qn: &str,
) -> Result<String, SmtGenError> {
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
    emitter.collect_facts_for_referenced_entities();
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
    emitter.collect_facts_for_referenced_entities();
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
    let rids = kb.rule_ids_by_qn(rule_qn);
    if rids.is_empty() {
        return Err(SmtGenError::new(format!("rule '{rule_qn}' not found")));
    }
    rids.into_iter()
        .map(|rid| lift_one_rid(kb, rule_qn, rid))
        .collect()
}

fn lift_one_rid(
    kb: &KnowledgeBase,
    rule_qn: &str,
    rid: anthill_core::kb::RuleId,
) -> Result<String, SmtGenError> {
    let mut emitter = Emitter::new(kb);
    // Cited-rule lifts are inherently abstract: chasing the cited
    // rule's body would condition its truth on facts the consumer
    // doesn't quote (unsound for a universal claim) and would also
    // drag in transitive nonlinearity that breaks LRA discharges.
    emitter.abstract_mode = true;
    emitter.collect_rule_for_rid(rule_qn, rid)?;
    emitter.collect_facts_for_referenced_entities();

    if emitter.conclusion_assertions.is_empty() {
        return Err(SmtGenError::new(format!(
            "rule '{rule_qn}' is not citable: no `-:` (then) clause. \
             Citable rules must state their conclusion explicitly via \
             the `-:` separator. Classical violation-shape rules (body \
             unsat) are not lifted as implications.")));
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
    let shared_arity = kb.rule_shared_arity(rid);

    if shared_arity == 0 {
        if emitter.free_vars.is_empty() {
            return Ok(format!("(assert {imp})"));
        }
        let decls: Vec<String> = emitter.free_vars.iter()
            .map(|v| format!("({v} Real)"))
            .collect();
        return Ok(format!(
            "(assert (forall ({}) {imp}))",
            decls.join(" ")
        ));
    }

    // shared_arity > 0: emit declare-consts for step-new vars +
    // a ground assert for the implication.
    let mut step_new: Vec<&String> = emitter.free_vars.iter()
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
    /// fact arg is a constructor `Term::Fn`. Consumed by
    /// `translate_expr` when it encounters `field_access(?var, ...)`.
    entity_bindings: BTreeMap<String, TermId>,
    /// Set when an emitted SMT expression uses `anthill_abs`. Triggers
    /// emission of the `(define-fun anthill_abs ...)` prelude in the
    /// rendered script. SMT-LIB has no built-in `abs` for Real; we
    /// synthesise it via `(ite (< x 0) (- x) x)`.
    uses_abs: bool,
    /// AbstractLift mode: when true, `process_body_goal` skips
    /// rule-call expansion (single-arg shorthand and multi-pos-arg
    /// fact-match/inline) — those vars stay free in the rendered
    /// SMT. Used by `lift_rule_to_implication_clause` (always) and
    /// by structured-proof parent discharges (via ProofConfig).
    abstract_mode: bool,
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
            abstract_mode: false,
        }
    }

    /// Find the rule by qualified name. Walk its body and produce
    /// the SMT-LIB equation that defines the head's result variable.
    /// Picks the first rule resolved by label / by-functor — for
    /// labeled multi-head rules (multiple rids per label) the
    /// per-rid path [`Self::collect_rule_for_rid`] should be used by
    /// the caller iterating over `kb.rule_ids_by_qn(rule_qn)`.
    fn collect_rule(&mut self, rule_qn: &str) -> Result<(), SmtGenError> {
        let rid = self.kb.rule_id_by_qn(rule_qn)
            .ok_or_else(|| SmtGenError::new(format!("rule '{rule_qn}' not found")))?;
        self.collect_rule_for_rid(rule_qn, rid)
    }

    /// Walk the given rule's body. Used by the lift fanout to
    /// process each rid of a labeled multi-head rule independently.
    fn collect_rule_for_rid(
        &mut self,
        rule_qn: &str,
        rid: anthill_core::kb::RuleId,
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
        let head = self.kb.rule_head(rid);
        let head_shape = self.classify_head(rid);
        if let HeadShape::FunctionLike { result_idx } = head_shape {
            self.result_var = synthetic_var_name(result_idx);
        } else if let HeadShape::Unsupported(msg) = &head_shape {
            return Err(SmtGenError::new(msg.clone()));
        }

        // Walk the body. Three clause shapes we accept:
        //   <Entity>(field: ?var, ...) — destructure a fact's fields
        //   ?var = <arith>             — bind ?var to an SMT term
        //   <Ordered.op>(a, b)         — inequality assertion
        //                                  (lte/lt/gte/gt)
        // Plus rule calls (`<rule_qn>(?var)`) — chase the dependency.
        let body = self.kb.rule_body(rid);
        let mut local_bindings: BTreeMap<String, String> = BTreeMap::new();
        for goal in body {
            self.process_body_goal(*goal, &mut local_bindings)?;
        }

        // Conclusion goals: under the unified encoding the rule head
        // IS the conclusion (Predicate shape) and is routed through
        // `process_body_goal`. Each goal is translated through the
        // same machinery as the body; the resulting assertions are
        // siphoned into `conclusion_assertions` instead of
        // `assertions`. Discharge and lift consume the two buckets
        // differently — see render_satisfiability_with /
        // lift_rule_to_implication_clause.
        let conclusion_goals: Vec<TermId> = match head_shape {
            HeadShape::Bottom => Vec::new(),
            HeadShape::FunctionLike { .. } => Vec::new(),
            HeadShape::Predicate => vec![head],
            HeadShape::Unsupported(_) => unreachable!("returned above"),
        };
        if !conclusion_goals.is_empty() {
            let body_count = self.assertions.len();
            for goal in &conclusion_goals {
                self.process_body_goal(*goal, &mut local_bindings)?;
            }
            self.conclusion_assertions = self.assertions.split_off(body_count);
        }

        // For upper-bound mode the result var must be bound by the
        // body. For satisfiability mode (no result var) it's fine if
        // every body var is either bound or free.
        if !self.result_var.is_empty() {
            let result_smt = local_bindings.get(&self.result_var).ok_or_else(||
                SmtGenError::new(format!(
                    "rule body never bound the result variable '?{}'",
                    self.result_var)))?;
            self.body_smtlib = format!(
                "(define-fun {} () Real {})",
                sanitize_smt_id(&self.result_var),
                result_smt);
        }

        // Compute free vars: any var_<i> referenced by an assertion
        // expression (body OR conclusion) that has no binding entry.
        // Those need `(declare-const ... Real)` in satisfiability mode
        // — and become the forall-quantified parameters in the lift.
        let scan = self.assertions.iter().chain(self.conclusion_assertions.iter());
        for assertion in scan {
            for tok in assertion.split(|c: char| !c.is_alphanumeric() && c != '_') {
                if parse_synthetic_var_name(tok).is_some()
                    && !local_bindings.contains_key(tok)
                {
                    self.free_vars.insert(tok.to_string());
                }
            }
        }
        Ok(())
    }

    /// Process one rule-body goal.
    fn process_body_goal(
        &mut self,
        goal: TermId,
        bindings: &mut BTreeMap<String, String>,
    ) -> Result<(), SmtGenError> {
        let term = self.kb.get_term(goal);
        let Term::Fn { functor, named_args, pos_args } = term else {
            return Err(SmtGenError::new(format!("non-Fn body goal: {term:?}")));
        };
        let qn = self.kb.qualified_name_of(*functor);

        // Equation goal: `?var = <expr>` binds the DeBruijn index of
        // ?var to the SMT translation of <expr>. Variable references
        // elsewhere in the body get substituted inline at translate
        // time.
        if is_eq_functor(self.kb, *functor) {
            if pos_args.len() != 2 {
                return Err(SmtGenError::new(format!(
                    "= goal: expected 2 pos_args, got {}", pos_args.len())));
            }
            let lhs_term = self.kb.get_term(pos_args[0]);
            let rhs_smt = self.translate_expr(pos_args[1], bindings)?;
            // Bare-DeBruijn LHS → string binding (cheap inline substitution
            // for downstream uses). Anything else (e.g. `?d * ?d = ?d_sq`)
            // → emit as a free assertion `(= <lhs> <rhs>)`. This keeps the
            // bindings map small and lets nonlinear equalities flow into
            // QF_NRA naturally.
            if let Term::Var(Var::DeBruijn(i)) = lhs_term {
                bindings.insert(synthetic_var_name(*i), rhs_smt);
                return Ok(());
            }
            let lhs_smt = self.translate_expr(pos_args[0], bindings)?;
            self.assertions.push(format!("(= {lhs_smt} {rhs_smt})"));
            return Ok(());
        }

        // Inequality body goals: `lte/lt/gte/gt(a, b)` become SMT
        // assertions on the constraint set. The rule body's joint
        // satisfiability is exactly the conjunction of these
        // inequalities + the equation-derived bindings.
        if let Some(smt_op) = map_inequality_op(qn) {
            if pos_args.len() != 2 {
                return Err(SmtGenError::new(format!(
                    "{qn}: expected 2 pos_args, got {}", pos_args.len())));
            }
            let a = self.translate_expr(pos_args[0], bindings)?;
            let b = self.translate_expr(pos_args[1], bindings)?;
            self.assertions.push(format!("({smt_op} {a} {b})"));
            return Ok(());
        }

        // Entity-destructure goal: `EntityName(field: ?bind_var, ...)`.
        // For v0 we only handle named-arg destructures. Each
        // ?bind_var becomes an SMT const bound to the corresponding
        // field's value from the matching ground fact.
        if self.is_known_entity(*functor) {
            let entity_qn = qn.to_string();
            self.referenced_entities.insert(entity_qn.clone());
            for (field_sym, val_term) in named_args {
                let field_name = self.kb.resolve_sym(*field_sym).to_string();
                let bind_idx = match self.kb.get_term(*val_term) {
                    Term::Var(Var::DeBruijn(i)) => *i,
                    _ => continue, // non-var slots (`field: ?` wildcards / literals)
                };
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
        if self.abstract_mode {
            self.visited_rules.insert(qn.to_string());
            return Ok(());
        }

        // Rule call: `<rule_qn>(?result_var)` — single-arg shorthand
        // that yields one inline SMT expression. Used by call sites
        // like `step_distance_bound(?delta)`.
        if pos_args.len() == 1 && named_args.is_empty()
            && self.kb.by_functor(*functor).iter()
                .any(|rid| !self.kb.rule_body(*rid).is_empty())
        {
            let bind_idx = match self.kb.get_term(pos_args[0]) {
                Term::Var(Var::DeBruijn(i)) => *i,
                _ => return Err(SmtGenError::new(format!(
                    "v0: rule call's pos arg must be a DeBruijn var, got {:?}",
                    self.kb.get_term(pos_args[0])))),
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
        //       binding, entity Fn → entity_bindings).
        //   (2) Inline — the rule has a defining body. Open it with
        //       caller→callee parameter substitution; process its
        //       goals as if inlined here.
        // No named_args path yet — multi-pos-arg with named_args is
        // a v1 concern.
        if !pos_args.is_empty() && named_args.is_empty() {
            let call_args: Vec<TermId> = pos_args.iter().copied().collect();
            if self.try_match_fact_call(*functor, &call_args, bindings)? {
                return Ok(());
            }
            if self.try_inline_rule_call(qn, &call_args, bindings)? {
                return Ok(());
            }
        }

        Err(SmtGenError::new(format!(
            "v0: unhandled body goal functor '{qn}'")))
    }

    /// Try to match a multi-pos-arg call against any ground fact
    /// (rule with empty body) of the same functor. On match, bind
    /// each call-side DeBruijn var to the corresponding fact slot —
    /// literal → string binding, entity-shaped Term::Fn →
    /// entity_bindings (consumed by `field_access` lowering).
    /// Returns Ok(true) if a fact matched (and bindings were applied);
    /// Ok(false) if no fact matched (caller falls through to inline).
    fn try_match_fact_call(
        &mut self,
        functor: anthill_core::intern::Symbol,
        call_args: &[TermId],
        bindings: &mut BTreeMap<String, String>,
    ) -> Result<bool, SmtGenError> {
        let candidates = self.kb.by_functor(functor);
        // Record the functor's QN in visited_rules so the cache key
        // observes any change to its defining facts (initial-geometry
        // edits invalidate downstream proofs).
        let functor_qn = self.kb.qualified_name_of(functor).to_string();
        for rid in candidates {
            if !self.kb.rule_body(rid).is_empty() { continue; }
            self.visited_rules.insert(functor_qn.clone());
            let head = self.kb.rule_head(rid);
            let Term::Fn { pos_args: fpos, named_args: fnamed, .. } = self.kb.get_term(head)
                else { continue };
            if !fnamed.is_empty() { continue; }
            if fpos.len() != call_args.len() { continue; }

            // Probe — does every concrete call slot equal the
            // corresponding fact slot? Variable slots match anything.
            let mut bind_pairs: Vec<(u32, TermId)> = Vec::new();
            let mut matched = true;
            for (call_t, fact_t) in call_args.iter().zip(fpos.iter()) {
                if let Term::Var(Var::DeBruijn(i)) = self.kb.get_term(*call_t) {
                    bind_pairs.push((*i, *fact_t));
                    continue;
                }
                if !self.terms_match(*call_t, *fact_t) {
                    matched = false;
                    break;
                }
            }
            if !matched { continue; }

            // Apply bindings.
            for (idx, fact_term_id) in bind_pairs {
                let synth = synthetic_var_name(idx);
                match self.kb.get_term(fact_term_id) {
                    Term::Const(Literal::Float(f)) => {
                        bindings.insert(synth, format_real(f.into_inner()));
                    }
                    Term::Const(Literal::Int(i)) => {
                        bindings.insert(synth, format_real(*i as f64));
                    }
                    Term::Fn { .. } => {
                        // Entity (Pose, Vec3, …) — defer until
                        // field_access reads it.
                        self.entity_bindings.insert(synth, fact_term_id);
                    }
                    Term::Ref(_) | Term::Ident(_) => {
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
    /// the caller-side TermIds bound positionally to the callee's
    /// head DeBruijn vars. The callee's local DeBruijn indices are
    /// renamed into a per-call namespace so they don't collide with
    /// the caller's; entity-typed arguments propagate into the
    /// callee's entity_bindings.
    fn try_inline_rule_call(
        &mut self,
        callee_qn: &str,
        call_args: &[TermId],
        caller_bindings: &mut BTreeMap<String, String>,
    ) -> Result<bool, SmtGenError> {
        let sym = match self.kb.try_resolve_symbol(callee_qn) {
            Some(s) => s,
            None => return Ok(false),
        };
        let rid = match self.kb.by_functor(sym).into_iter()
            .find(|r| !self.kb.rule_body(*r).is_empty())
        {
            Some(r) => r,
            None => return Ok(false),
        };
        self.visited_rules.insert(callee_qn.to_string());

        let head = self.kb.rule_head(rid);
        let head_pos: Vec<TermId> = match self.kb.get_term(head) {
            Term::Fn { pos_args, named_args, .. } if named_args.is_empty() => {
                pos_args.iter().copied().collect()
            }
            _ => return Err(SmtGenError::new(format!(
                "v0: inlined rule '{callee_qn}' must have only pos args in head"))),
        };
        if head_pos.len() != call_args.len() {
            return Err(SmtGenError::new(format!(
                "rule call arity mismatch for '{callee_qn}': expected {}, got {}",
                head_pos.len(), call_args.len())));
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
        let mut callee_ent: BTreeMap<String, TermId> = BTreeMap::new();
        let mut head_caller: Vec<(u32, String)> = Vec::new();
        for (head_arg, call_arg) in head_pos.iter().zip(call_args.iter()) {
            let head_idx = match self.kb.get_term(*head_arg) {
                Term::Var(Var::DeBruijn(i)) => *i,
                _ => return Err(SmtGenError::new(format!(
                    "v0: inlined rule '{callee_qn}' head args must be DeBruijn vars"))),
            };
            let head_synth = synthetic_var_name(head_idx);
            match self.kb.get_term(*call_arg) {
                Term::Var(Var::DeBruijn(j)) => {
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
                        callee_ent.insert(head_synth, *t);
                    }
                }
                Term::Const(Literal::Float(f)) => {
                    callee_str.insert(head_synth, format_real(f.into_inner()));
                }
                Term::Const(Literal::Int(i)) => {
                    callee_str.insert(head_synth, format_real(*i as f64));
                }
                Term::Fn { .. } => {
                    // Concrete entity literal at the call site —
                    // expose it for field_access on the callee side.
                    callee_ent.insert(head_synth, *call_arg);
                }
                Term::Ref(_) | Term::Ident(_) => {
                    // Nullary symbol — not arithmetic; ignore.
                }
                _ => {}
            }
        }

        // Process the callee's body. We share the global
        // `assertions` / `field_consts` / `referenced_entities` /
        // `free_vars` accumulators (the inlined rule's facts and
        // assertions belong to the caller's SMT document), but we
        // give the callee its own bindings + entity_bindings so its
        // local DeBruijn indices stay isolated. After processing we
        // restore the caller's entity_bindings.
        let body_goals: Vec<TermId> = self.kb.rule_body(rid).iter().copied().collect();
        let saved_ent = std::mem::take(&mut self.entity_bindings);
        self.entity_bindings = callee_ent;
        let mut local = callee_str;
        let mut err: Option<SmtGenError> = None;
        for goal in body_goals {
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
        if let Some(e) = err { return Err(e); }

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
            if let Some(entity_tid) = final_ent.get(&head_synth) {
                self.entity_bindings.insert(caller_synth, *entity_tid);
            }
        }
        Ok(true)
    }

    /// Structural equality of two TermIds for fact-match probing.
    /// Hash-consing makes this an id-equality fast path; the helper
    /// exists so future changes (e.g. literal-as-Real coercions) have
    /// one place to gate.
    fn terms_match(&self, a: TermId, b: TermId) -> bool {
        if a == b { return true; }
        match (self.kb.get_term(a), self.kb.get_term(b)) {
            (Term::Const(Literal::Float(x)), Term::Const(Literal::Float(y))) => x == y,
            (Term::Const(Literal::Int(x)),   Term::Const(Literal::Int(y)))   => x == y,
            (Term::Const(Literal::Int(i)),   Term::Const(Literal::Float(f)))
            | (Term::Const(Literal::Float(f)), Term::Const(Literal::Int(i))) => {
                (*i as f64) == f.into_inner()
            }
            (Term::Ref(x) | Term::Ident(x), Term::Ref(y) | Term::Ident(y)) => x == y,
            (Term::Fn { functor: fx, pos_args: px, named_args: nx },
             Term::Fn { functor: fy, pos_args: py, named_args: ny }) => {
                fx == fy
                    && px.len() == py.len()
                    && nx.len() == ny.len()
                    && px.iter().zip(py.iter()).all(|(a, b)| self.terms_match(*a, *b))
                    && nx.iter().zip(ny.iter()).all(|((sa, ta), (sb, tb))|
                        sa == sb && self.terms_match(*ta, *tb))
            }
            _ => false,
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
        let sym = self.kb.try_resolve_symbol(callee_qn)
            .ok_or_else(|| SmtGenError::new(format!("rule call '{callee_qn}' not found")))?;
        let rid = self.kb.by_functor(sym).into_iter()
            .find(|r| !self.kb.rule_body(*r).is_empty())
            .ok_or_else(|| SmtGenError::new(format!(
                "rule call '{callee_qn}' has no defining clauses")))?;

        let head = self.kb.rule_head(rid);
        let result_idx = match self.kb.get_term(head) {
            Term::Fn { pos_args, .. } if pos_args.len() == 1 => {
                match self.kb.get_term(pos_args[0]) {
                    Term::Var(Var::DeBruijn(i)) => *i,
                    _ => return Err(SmtGenError::new(format!(
                        "v0: called rule '{callee_qn}' head must be ?DeBruijn"))),
                }
            }
            _ => return Err(SmtGenError::new(format!(
                "v0: called rule '{callee_qn}' must have exactly one pos arg in head"))),
        };
        let mut local_bindings: BTreeMap<String, String> = BTreeMap::new();
        for goal in self.kb.rule_body(rid) {
            self.process_body_goal(*goal, &mut local_bindings)?;
        }
        local_bindings.get(&synthetic_var_name(result_idx))
            .cloned()
            .ok_or_else(|| SmtGenError::new(format!(
                "called rule '{callee_qn}' never bound its result var")))
    }

    /// Translate an arithmetic expression (anthill prelude ops) to
    /// an SMT-LIB term. Variables resolve through `bindings` which
    /// substitutes already-defined locals inline. Mutates `self` to
    /// record `uses_abs` when an `abs` call is rendered.
    fn translate_expr(
        &mut self,
        term: TermId,
        bindings: &BTreeMap<String, String>,
    ) -> Result<String, SmtGenError> {
        match self.kb.get_term(term) {
            Term::Const(Literal::Float(f)) => Ok(format_real(f.into_inner())),
            Term::Const(Literal::Int(i)) => Ok(format_real(*i as f64)),
            Term::Var(Var::DeBruijn(i)) => {
                let synth = synthetic_var_name(*i);
                Ok(bindings.get(&synth).cloned().unwrap_or(synth))
            }
            Term::Var(other) => Err(SmtGenError::new(format!(
                "v0: expected DeBruijn var in expression, got {other:?}"))),
            Term::Ref(s) | Term::Ident(s) => {
                Ok(sanitize_smt_id(self.kb.resolve_sym(*s)))
            }
            Term::Fn { functor, pos_args, .. } => {
                let op = self.kb.qualified_name_of(*functor);
                // Entity field projection: `?p.field` desugars to
                // `field_access(?p, Ident(field))`. Resolve through
                // the entity_bindings populated by fact match / rule
                // inline to a concrete literal (or recurse on a
                // nested entity field).
                if op == "anthill.reflect.field_access" || op == "field_access" {
                    let resolved = self.resolve_field_access(term)?;
                    return self.translate_expr(resolved, bindings);
                }
                if let Some(smt_op) = map_unary_op(op) {
                    if pos_args.len() != 1 {
                        return Err(SmtGenError::new(format!(
                            "{op}: expected 1 pos_arg, got {}", pos_args.len())));
                    }
                    let a = self.translate_expr(pos_args[0], bindings)?;
                    if smt_op == "anthill_abs" {
                        self.uses_abs = true;
                    }
                    return Ok(format!("({smt_op} {a})"));
                }
                let smt_op = match map_arith_op(op) {
                    Some(o) => o,
                    None => return Err(SmtGenError::new(format!(
                        "v0: unhandled arithmetic op '{op}'"))),
                };
                if pos_args.len() != 2 {
                    return Err(SmtGenError::new(format!(
                        "{op}: expected 2 pos_args, got {}", pos_args.len())));
                }
                let a = self.translate_expr(pos_args[0], bindings)?;
                let b = self.translate_expr(pos_args[1], bindings)?;
                Ok(format!("({smt_op} {a} {b})"))
            }
            other => Err(SmtGenError::new(format!(
                "v0: unhandled term in expression: {other:?}"))),
        }
    }

    /// Resolve `field_access(?obj, Ident(field))` (possibly nested)
    /// to the projected value's TermId. The chain bottoms out either
    /// at a literal (Const) or a value that itself goes back through
    /// translate_expr — typically a leaf Float in an entity's named
    /// args.
    ///
    /// Resolution rules:
    /// - root `?var` → look up `entity_bindings[var_<i>]`. The bound
    ///   term is expected to be a Term::Fn with named_args (an
    ///   entity instance).
    /// - root `field_access(...)` → recurse on the nested chain.
    /// - root entity Term::Fn → use directly.
    fn resolve_field_access(&self, term: TermId) -> Result<TermId, SmtGenError> {
        let Term::Fn { functor, pos_args, .. } = self.kb.get_term(term) else {
            return Err(SmtGenError::new(format!(
                "field_access: expected Fn, got {:?}", self.kb.get_term(term))));
        };
        let op = self.kb.qualified_name_of(*functor);
        if !(op == "anthill.reflect.field_access" || op == "field_access") {
            return Err(SmtGenError::new(format!(
                "resolve_field_access called on non-field_access functor '{op}'")));
        }
        if pos_args.len() != 2 {
            return Err(SmtGenError::new(format!(
                "field_access: expected 2 pos_args, got {}", pos_args.len())));
        }
        let object_tid = pos_args[0];
        let field_tid = pos_args[1];

        // Step 1: resolve the object to an entity Term::Fn.
        let entity_tid = match self.kb.get_term(object_tid) {
            Term::Var(Var::DeBruijn(i)) => {
                let synth = synthetic_var_name(*i);
                *self.entity_bindings.get(&synth).ok_or_else(||
                    SmtGenError::new(format!(
                        "field_access on '?{synth}': no entity binding\
                         (caller did not supply a concrete entity)")))?
            }
            Term::Fn { functor: f2, .. } => {
                let q2 = self.kb.qualified_name_of(*f2);
                if q2 == "anthill.reflect.field_access" || q2 == "field_access" {
                    self.resolve_field_access(object_tid)?
                } else {
                    object_tid
                }
            }
            other => return Err(SmtGenError::new(format!(
                "field_access: cannot resolve object: {other:?}"))),
        };

        // Step 2: extract the field name.
        let field_sym = match self.kb.get_term(field_tid) {
            Term::Ref(s) | Term::Ident(s) => *s,
            other => return Err(SmtGenError::new(format!(
                "field_access: field must be Ident/Ref, got {other:?}"))),
        };
        let field_name = self.kb.resolve_sym(field_sym).to_string();

        // Step 3: project into the entity's named_args by short-name match.
        let Term::Fn { named_args, .. } = self.kb.get_term(entity_tid) else {
            return Err(SmtGenError::new(format!(
                "field_access: object resolved to non-Fn term: {:?}",
                self.kb.get_term(entity_tid))));
        };
        for (sym, val_tid) in named_args.iter() {
            if self.kb.resolve_sym(*sym) == field_name {
                return Ok(*val_tid);
            }
        }
        Err(SmtGenError::new(format!(
            "field_access: field '{field_name}' not found in entity")))
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
    fn classify_head(&self, rid: anthill_core::kb::RuleId) -> HeadShape {
        let head = self.kb.rule_head(rid);
        let term = self.kb.get_term(head);
        let (functor, pos_args) = match term {
            Term::Bottom => return HeadShape::Bottom,
            Term::Fn { functor, pos_args, .. } => (*functor, pos_args.clone()),
            other => return HeadShape::Unsupported(format!(
                "rule head must be Fn or Bottom, got {other:?}")),
        };
        let qn = self.kb.qualified_name_of(functor);
        if is_eq_functor(self.kb, functor)
            || map_inequality_op(&qn).is_some()
            || self.is_known_entity(functor)
        {
            return HeadShape::Predicate;
        }
        if pos_args.len() == 1 {
            let result_idx = match self.kb.get_term(pos_args[0]) {
                Term::Var(Var::DeBruijn(i)) => *i,
                other => return HeadShape::Unsupported(format!(
                    "v0: function-like rule head's pos_arg must be DeBruijn var, got {other:?}")),
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
            pos_args.len()))
    }

    /// For each entity referenced in the rule body, find its
    /// (single) ground fact in the KB and resolve every field to a
    /// Real value. Multi-fact handling is a v1 concern.
    fn collect_facts_for_referenced_entities(&mut self) {
        for entity_qn in self.referenced_entities.clone() {
            let Some(sym) = self.kb.try_resolve_symbol(&entity_qn) else { continue };
            // `by_functor(sym)` returns BOTH the entity declaration
            // (named_args have abstract field types) and any
            // `fact ...` instances (named_args have concrete
            // values). Walk every rule and accept the first one
            // whose named_args resolve to numeric literals — that's
            // a ground fact. Multi-fact disambiguation is a v1
            // concern; for v0 we expect at most one fact per entity.
            for rid in self.kb.by_functor(sym) {
                let head = self.kb.rule_head(rid);
                let Term::Fn { named_args, .. } = self.kb.get_term(head) else { continue };
                let any_concrete = named_args.iter().any(|(_, t)|
                    literal_as_real(self.kb.get_term(*t)).is_some());
                if !any_concrete { continue; }
                for (field_sym, val_term) in named_args {
                    let field_name = self.kb.resolve_sym(*field_sym).to_string();
                    let const_name = sanitize_smt_id(&field_name);
                    if !self.field_consts.contains_key(&const_name) { continue; }
                    if let Some(v) = literal_as_real(self.kb.get_term(*val_term)) {
                        self.field_consts.insert(const_name, v);
                    }
                }
                break;
            }
        }
    }

    fn render_upper_bound_with(&self, obligation: &Obligation, config: &ProofConfig) -> String {
        let logic = config.logic.as_deref().unwrap_or("QF_LRA");
        let mut out = String::new();
        out.push_str(&format!(
            "; Generated by anthill-smt-gen for obligation {}.\n",
            obligation.rule_qn));
        out.push_str(&format!("; Logic: {logic}.\n"));
        if let Some(t) = config.timeout_ms {
            out.push_str(&format!("(set-option :timeout {t})\n"));
        }
        emit_outcome_options(&mut out, config);
        out.push_str(&format!("(set-logic {logic})\n\n"));

        emit_abs_prelude(&mut out, self.uses_abs, config);

        for (name, value) in &self.field_consts {
            out.push_str(&format!("(define-fun {name} () Real {})\n", format_real(*value)));
        }
        out.push('\n');

        emit_assumptions(&mut out, config);

        out.push_str(&self.body_smtlib);
        out.push_str("\n\n");

        out.push_str(&format!(
            "; Obligation: {} <= {}\n",
            self.result_var, obligation.upper_bound));
        out.push_str(&format!(
            "(assert (not (<= {} {})))\n",
            sanitize_smt_id(&self.result_var),
            format_real(obligation.upper_bound)));
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
            "; Generated by anthill-smt-gen — satisfiability check for rule {rule_qn}.\n"));
        out.push_str("; `unsat` ⇒ rule body has no solution ⇒ encoded property holds.\n");
        if let Some(t) = config.timeout_ms {
            out.push_str(&format!("(set-option :timeout {t})\n"));
        }
        emit_outcome_options(&mut out, config);
        out.push_str(&format!("(set-logic {logic})\n\n"));

        emit_abs_prelude(&mut out, self.uses_abs, config);

        for (name, value) in &self.field_consts {
            out.push_str(&format!("(define-fun {name} () Real {})\n", format_real(*value)));
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
        || config.assumptions.iter().any(|a| a.contains("anthill_abs "));
    if needs {
        out.push_str("(define-fun anthill_abs ((x Real)) Real (ite (< x 0) (- x) x))\n\n");
    }
}

fn emit_assumptions(out: &mut String, config: &ProofConfig) {
    if config.assumptions.is_empty() { return; }
    out.push_str("; Cited-lemma assumptions (from `using` clause).\n");
    // Dedupe `(declare-const var_<i> Real)` lines across all
    // assumptions — different cited step rules may share step-new
    // vars (the converter shares VarIds across consecutive steps in
    // a structured proof body), and Z3 rejects
    // a duplicate constant declaration.
    let mut seen_decls: BTreeSet<String> = BTreeSet::new();
    for clause in &config.assumptions {
        for line in clause.split('\n') {
            if line.trim().is_empty() { continue; }
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

/// Map anthill arithmetic functor qualified names to SMT-LIB ops.
/// Linear-arithmetic only (`/` against a Real constant is still
/// linear in QF_LRA).
fn map_arith_op(qn: &str) -> Option<&'static str> {
    match qn {
        "anthill.prelude.Numeric.add" | "Numeric.add" | "add" => Some("+"),
        "anthill.prelude.Numeric.sub" | "Numeric.sub" | "sub" => Some("-"),
        "anthill.prelude.Numeric.mul" | "Numeric.mul" | "mul" => Some("*"),
        "anthill.prelude.Float.div"   | "Float.div"   | "div" => Some("/"),
        "anthill.prelude.Int.div"     | "Int.div"             => Some("div"),
        _ => None,
    }
}

/// Map unary anthill ops (abs, neg) to SMT-LIB.
/// `abs` is emitted as `anthill_abs` — a (define-fun anthill_abs
/// ((x Real)) Real (ite (< x 0) (- x) x)) prelude is added to the
/// final SMT script when any call site renders `anthill_abs`.
/// SMT-LIB has no built-in `abs` for Real in the LRA/NRA logics
/// most discharges run under, so we synthesise it.
fn map_unary_op(qn: &str) -> Option<&'static str> {
    match qn {
        "anthill.prelude.Float.abs" | "Float.abs" | "abs" => Some("anthill_abs"),
        "anthill.prelude.Int.abs" => Some("anthill_abs"),
        "anthill.prelude.Float.neg" | "Float.neg" => Some("-"),
        "anthill.prelude.Int.neg" | "Int.neg" => Some("-"),
        _ => None,
    }
}

/// Map anthill comparison ops to SMT-LIB. Used as body-goal
/// assertions (not embedded in arithmetic expressions, since
/// SMT-LIB segregates Bool from Real cleanly).
fn map_inequality_op(qn: &str) -> Option<&'static str> {
    match qn {
        "anthill.prelude.Ordered.lte" | "Ordered.lte" | "lte" => Some("<="),
        "anthill.prelude.Ordered.lt"  | "Ordered.lt"  | "lt"  => Some("<"),
        "anthill.prelude.Ordered.gte" | "Ordered.gte" | "gte" => Some(">="),
        "anthill.prelude.Ordered.gt"  | "Ordered.gt"  | "gt"  => Some(">"),
        _ => None,
    }
}

/// True if `sym` names the equation predicate. Loader desugars `=`
/// to `anthill.prelude.Eq.eq` in goal position; `Term::Fn` may also
/// carry the unqualified short form during construction.
fn is_eq_functor(kb: &KnowledgeBase, sym: anthill_core::intern::Symbol) -> bool {
    let qn = kb.qualified_name_of(sym);
    if qn == "=" || qn == "anthill.prelude.Eq.eq" { return true; }
    let short = kb.resolve_sym(sym);
    short == "=" || short == "eq"
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

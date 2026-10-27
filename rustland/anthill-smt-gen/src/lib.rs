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
pub mod sort;
pub mod tactic_emit;

pub use sort::{lower_spec_law, Declarations, LoweredLaw, SmtSort};

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::rc::Rc;

use anthill_core::eval::Value;
use anthill_core::intern::Symbol;
use anthill_core::kb::extent::{BodiedRulePolicy, ExtentReadError};
use anthill_core::kb::node_occurrence::{
    for_each_child, materialize_from_handle, Expr, NodeOccurrence,
};
use anthill_core::kb::term::{Literal, Term, TermId, Var, VarId};
use anthill_core::kb::typing::is_typed_head_domain_goal;
use anthill_core::kb::{ClauseKind, KnowledgeBase, ProgramClause};
use anthill_core::parse::desugar_target as dt;

use sort::{document_logic, smt_tokens};

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
    /// A call that is the premise of a lemma the proof cites is not chased either,
    /// and is STATED (WI-20261012-CDHSQ, `BodyIs`).
    pub abstract_body: bool,
    /// WI-20261012-ZZ7PH — the LAWS of the requirements of the proof's enclosing
    /// scopes, each a whole `(assert (forall …))` as [`lower_spec_law`] gives it. They
    /// are hypotheses as `assumptions` are, and are not of the `using` list: a
    /// requirement is a scope axiom, read off its declaration.
    pub laws: Vec<String>,
    /// What `laws` and `assumptions` use and the theory does not have — the sort a
    /// scope's abstract parameter is, a spec's operations on it. Declared with what the
    /// proof's own body uses, each once.
    pub declarations: Declarations,
    /// WHERE `laws` CAME FROM, as entries of the proof's dependency set
    /// (`cache::visited_laws_of` a spec, `cache::visited_requires_of` a scope). A law is
    /// no rule the proof visits, so without these the state a proof's record is hashed
    /// over did not hold what it was proved from: a law weakened, or the `requires`
    /// clause removed, left the record current and the lemma citable.
    pub law_sources: Vec<String>,
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
    emitter.result_required = true;
    emitter.collect_rule(&obligation.rule_qn)?;
    if emitter.result_var.is_empty() {
        // AN OBLIGATION IS `<rule>(?result) <= bound`, so a head that binds no result
        // variable has nothing to bound. `render_upper_bound_with` interpolates
        // `result_var` unguarded and emitted `(assert (not (<=  5.0)))` — invalid SMT-LIB
        // returned as `Ok`, which a solver runner then reports as "not unsat" rather than
        // as an error. Measured on all three head shapes that leave it empty: a nullary
        // head (`Bottom` since WI-20260902-CZJ2N gave `classify_head` its `Term::Ref` arm),
        // a named-arg-only `Term::Fn` head (`Bottom`, and the shape that says the hole
        // predates that arm), and an entity-headed rule (`Predicate`).
        //
        // Keyed on the empty `result_var` rather than on a head shape, because that is
        // what the renderer actually depends on. scaland's `emitObligationWith` carries
        // the same guard and the same message shape (WI-20260902-EQG4F) — found there by
        // /code-review, and measured here rather than assumed.
        return Err(SmtGenError::new(format!(
            "obligation on '{}': its head binds no result variable (only a function-like \
             head `rule f(?r) :- …` can carry an upper bound)",
            obligation.rule_qn
        )));
    }
    emitter.collect_facts_for_referenced_entities()?;
    emitter.declarations.merge(&config.declarations)?;
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
    emit_satisfiability_check_with_deps(kb, rule_qn, config).map(|(smt, _)| smt)
}

/// Like `emit_satisfiability_check_with` but additionally returns the
/// set of rule QNs visited during emission — the proof's dependency
/// set, used for staleness tracking when one of them changes.
pub fn emit_satisfiability_check_with_deps(
    kb: &KnowledgeBase,
    rule_qn: &str,
    config: &ProofConfig,
) -> Result<(String, Vec<String>), SmtGenError> {
    let worlds = read_worlds(kb, |emitter| {
        emitter.abstract_mode = config.abstract_body;
        emitter.body_is = BodyIs::hypotheses_of(config);
        emitter.collect_rule(rule_qn)?;
        emitter.collect_facts_for_referenced_entities()?;
        emitter.declarations.merge(&config.declarations)
    })?;
    let smt = match worlds.as_slice() {
        [one] => one.render_satisfiability_with(rule_qn, config),
        several => render_worlds(several, rule_qn, config)?,
    };
    // What the proof was handed that no rule it visits names (`ProofConfig::law_sources`)
    // is of its dependency set too.
    let deps: Vec<String> = worlds
        .into_iter()
        .flat_map(|world| world.visited_rules)
        .chain(config.law_sources.iter().cloned())
        .collect::<BTreeSet<String>>()
        .into_iter()
        .collect();
    Ok((smt, deps))
}

/// WI-20261013-1KF32 — A BODY READ IN EVERY WORLD ITS CHOICES MAKE. A call several
/// clauses can answer holds when any of them does, so the body means the disjunction of
/// its readings: one for each combination of the clauses its choice points take
/// ([`Emitter::choose`]). Each is `read` by an emitter of its own — the whole body and the
/// conclusion, so what a clause binds is bound for everything after it, and a later call
/// is selected by it — and the document is unsatisfiable when every world is
/// ([`render_worlds`]). A body that meets no choice point is ONE world, read as it was.
///
/// The worlds are enumerated depth-first by REPLAYING the walk with a longer prefix of
/// choices: the walk is deterministic, so a prefix reaches the points it names again and
/// the points beyond it take their first clause, and each of their other clauses is a
/// prefix still to be read. In the order of the choices, the first clause's world first.
/// More than [`WORLD_CAP`] worlds are refused.
fn read_worlds<'kb>(
    kb: &'kb KnowledgeBase,
    read: impl Fn(&mut Emitter<'kb>) -> Result<(), SmtGenError>,
) -> Result<Vec<Emitter<'kb>>, SmtGenError> {
    let builtins = SmtBuiltinTable::resolve(kb);
    let mut pending: Vec<Vec<usize>> = vec![Vec::new()];
    let mut worlds: Vec<Emitter<'kb>> = Vec::new();
    while let Some(prefix) = pending.pop() {
        let mut emitter = Emitter::with_builtins(kb, builtins.clone());
        emitter.choices = Some(Choices {
            taken: prefix.clone(),
            met: Vec::new(),
        });
        // An inlined rule's own variable is named past every name of the DOCUMENT, and
        // the worlds are one document: by the names alone, two worlds inlining different
        // clauses gave theirs one name, and one of two sorts was refused
        // (WI-20261012-BR7P3, /code-review).
        emitter.next_own_variable = worlds.last().and_then(|world| world.next_own_variable);
        let outcome = read(&mut emitter);
        let met = emitter
            .choices
            .as_ref()
            .map(|choices| choices.met.clone())
            .unwrap_or_default();
        if let Err(refused) = outcome {
            return Err(match describe_world(&met, &prefix) {
                Some(world) => SmtGenError::new(format!("{} (in the world where {world})", refused.message)),
                None => refused,
            });
        }
        assert!(
            met.len() >= prefix.len(),
            "a reading met {} choice points where the world it was asked for names {}: the \
             walk is not deterministic",
            met.len(),
            prefix.len()
        );
        let path: Vec<usize> = (0..met.len())
            .map(|at| prefix.get(at).copied().unwrap_or(0))
            .collect();
        let mut beyond = Vec::new();
        for at in (prefix.len()..met.len()).rev() {
            for clause in 1..met[at].of {
                let mut sibling = path[..at].to_vec();
                sibling.push(clause);
                beyond.push(sibling);
            }
        }
        pending.extend(beyond.into_iter().rev());
        worlds.push(emitter);
        if worlds.len() + pending.len() > WORLD_CAP {
            let points: Vec<String> = met
                .iter()
                .map(|point| format!("{} — {} {}s", point.what, point.of, point.answered_by))
                .collect();
            return Err(SmtGenError::new(format!(
                "the body is read in more than {WORLD_CAP} worlds — one for each combination \
                 of the clauses that answer its calls, and each repeats the body \
                 (WI-20261013-1KF32). The choices of the world being read when the count \
                 passed it: {}. Give the cases this proof is about predicates of their own, or \
                 arguments that select their clauses",
                points.join("; ")
            )));
        }
    }
    Ok(worlds)
}

/// The choices of a world, as a document's comment and a refusal name them; `None` for
/// a world that met no choice point.
fn describe_world(met: &[ChoicePoint], taken: &[usize]) -> Option<String> {
    if met.is_empty() {
        return None;
    }
    let choices: Vec<String> = met
        .iter()
        .enumerate()
        .map(|(at, point)| {
            let pick = taken.get(at).copied().unwrap_or(0);
            format!(
                "{} is answered by its {} {} of {}",
                point.what,
                point.answered_by,
                pick + 1,
                point.of
            )
        })
        .collect();
    Some(choices.join("; "))
}

/// WI-20261013-1KF32 — THE DOCUMENT OF A BODY READ IN SEVERAL WORLDS ([`read_worlds`]):
/// what each declares, once — a free variable is one constant of the document whoever
/// names it, which is sound because the worlds are DISJUNCTS, each existentially closed
/// on its own (`∃x. A ∨ B` is `(∃x. A) ∨ (∃x. B)`) — and their disjunction, each world the
/// conjunction of its hypotheses and its negated conclusion, read in its own bindings.
/// `unsat` where every world is: the proof the document would be if it were split by the
/// choice of clause, and still ONE document, so the record, the cache key and the witness
/// are of one.
fn render_worlds(
    worlds: &[Emitter<'_>],
    rule_qn: &str,
    config: &ProofConfig,
) -> Result<String, SmtGenError> {
    let mut declarations = Declarations::default();
    let mut field_consts: BTreeMap<&str, f64> = BTreeMap::new();
    let mut free: BTreeMap<&str, &SmtSort> = BTreeMap::new();
    let mut trig_args: BTreeSet<String> = BTreeSet::new();
    let mut uses_abs = false;
    for world in worlds {
        declarations.merge(&world.declarations)?;
        for (name, value) in &world.field_consts {
            if let Some(other) = field_consts.insert(name.as_str(), *value) {
                if other != *value {
                    return Err(SmtGenError::new(format!(
                        "the constant `{name}` is {} in one world of the body and {} in \
                         another, and the document has one",
                        format_real(other),
                        format_real(*value)
                    )));
                }
            }
        }
        let result = world.result_value.as_ref().map(|_| &world.result_var);
        for name in world.free_vars.iter().chain(result) {
            let sort = world.var_sorts.get(name).unwrap_or(&SmtSort::Real);
            if let Some(other) = free.insert(name.as_str(), sort) {
                if other != sort {
                    return Err(SmtGenError::new(format!(
                        "the variable `{name}` is of sort {other} in one world of the body and \
                         of {sort} in another, and the document declares it once"
                    )));
                }
            }
        }
        trig_args.extend(world.trig_args.iter().cloned());
        uses_abs |= world.uses_abs;
    }

    let mut hypotheses = String::from("(assert (or\n");
    for (at, world) in worlds.iter().enumerate() {
        let choices = world.choices.as_ref().expect("a world is read with its choices");
        let described = describe_world(&choices.met, &choices.taken)
            .expect("a document of several worlds is of choices met");
        hypotheses.push_str(&format!("  ; {}: {described}\n", at + 1));
        let mut conjuncts: Vec<String> = Vec::new();
        if let Some(value) = &world.result_value {
            conjuncts.push(format!("(= {} {value})", sanitize_smt_id(&world.result_var)));
        }
        conjuncts.extend(world.assertions.iter().cloned());
        conjuncts.extend(world.negated_conclusion());
        let conjunction = match conjuncts.as_slice() {
            [] => "true".to_owned(),
            [one] => one.clone(),
            several => format!("(and {})", several.join(" ")),
        };
        hypotheses.push_str(&format!("  {conjunction}\n"));
    }
    hypotheses.push_str("))\n");
    Ok(render_check(
        rule_qn,
        config,
        CheckParts {
            note: Some(format!(
                "; The body is read in {} worlds, one for each choice of the clauses that \
                 answer its\n; calls, and holds in one of them (WI-20261013-1KF32).\n",
                worlds.len()
            )),
            declarations: &declarations,
            uses_abs,
            field_consts: field_consts.into_iter().collect(),
            free: free.into_iter().collect(),
            trig_args: &trig_args,
            hypotheses,
        },
    ))
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
/// **A premise that is a rule's predicate** (`conclusion :- related(?a, ?b)` — a
/// bodied rule's, a fact's, a one-argument rule's alike) is neither chased into its
/// body nor passed over: it is `(related a b)`, the uninterpreted relation of the
/// predicate's name, which [`lift_rule`]'s declarations carry to the consumer
/// (WI-20261012-CDHSQ, `BodyIs`). The consumer discharges it by its own
/// call of the predicate.
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
    let lifted = lift_rule(kb, rule_qn)?;
    // The clauses alone are a whole hypothesis only where they use nothing a document
    // must declare. One that names a carrier's sort, a spec's operation at it, or the
    // relation of a rule's predicate is half of what the consumer needs — the relation
    // undeclared is a solver error, and a consumer not told of it never states its own
    // call — so it is not handed out by this door.
    if !lifted.declarations.is_empty() {
        return Err(SmtGenError::new(format!(
            "the lift of '{rule_qn}' uses what its consumer's document must declare — a \
             carrier's sort, an operation at it, or the relation of a rule's predicate: \
             take it with its declarations (`lift_rule`)"
        )));
    }
    Ok(lifted.clauses)
}

/// What a cited lemma gives its consumer's document: the clauses
/// [`lift_rule_to_implication_clause`] describes, and — WI-20261012-ZZ7PH — what they
/// use and the theory does not have. A lemma about a scope's abstract parameter
/// quantifies over the parameter's own sort and names a spec's operations on it, and
/// the consumer declares both, once, with what its own body uses. And a lemma with a
/// premise that is a rule's predicate names that relation (WI-20261012-CDHSQ), which
/// the consumer declares and writes its own calls with.
#[derive(Debug, Clone, Default)]
pub struct Lifted {
    pub clauses: Vec<String>,
    pub declarations: Declarations,
}

/// THE CLAUSES A NAME STATES — a rule's, a fact's, a constraint's — and not a
/// declaration that shares the name (WI-20261012-KF2SD). A rule named as the last
/// segment of its namespace has the namespace's symbol for the functor of its head, so
/// the namespace's own clause is under the name too, and FIRST: measured, `rule
/// legacy(?m) :- Cfg(scale: ?s), gt(?s, 99), eq(?m, ?s)` in `namespace
/// test.outcome.legacy` was proved as that clause — an EMPTY document, which is `sat`,
/// a COUNTEREXAMPLE — where the same rule under another name proved. Found when a
/// proof began to count the clauses of its rule, and this one was two.
fn stated_clauses(kb: &KnowledgeBase, rule_qn: &str) -> Vec<ProgramClause> {
    kb.program_clauses_by_qn(rule_qn)
        .into_iter()
        .filter(|clause| {
            matches!(
                clause.clause_kind,
                ClauseKind::Rule | ClauseKind::Fact | ClauseKind::Constraint
            )
        })
        .collect()
}

/// [`lift_rule_to_implication_clause`], with the declarations the clauses need.
pub fn lift_rule(kb: &KnowledgeBase, rule_qn: &str) -> Result<Lifted, SmtGenError> {
    let clauses = stated_clauses(kb, rule_qn);
    if clauses.is_empty() {
        return Err(SmtGenError::new(format!("rule '{rule_qn}' not found")));
    }
    let mut lifted = Lifted::default();
    for clause in clauses {
        let (text, declarations) = lift_one_clause(kb, rule_qn, clause)?;
        lifted.clauses.push(text);
        lifted.declarations.merge(&declarations)?;
    }
    Ok(lifted)
}

fn lift_one_clause(
    kb: &KnowledgeBase,
    rule_qn: &str,
    clause: ProgramClause,
) -> Result<(String, Declarations), SmtGenError> {
    let mut emitter = Emitter::new(kb);
    // Cited-rule lifts are inherently abstract: chasing the cited
    // rule's body would condition its truth on facts the consumer
    // doesn't quote (unsound for a universal claim) and would also
    // drag in transitive nonlinearity that breaks LRA discharges.
    emitter.abstract_mode = true;
    // WI-20261012-CDHSQ — and nothing of the body is passed over with what is not
    // chased: a premise that is a rule's predicate is the relation of its name.
    emitter.body_is = BodyIs::Antecedent;
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
            return Ok((format!("(assert {imp})"), emitter.declarations));
        }
        // Each variable at the sort its bound or a signature gave it — a `Real` where
        // neither did, as every one was.
        let decls = emitter.quantifier_declarations();
        return Ok((
            format!("(assert (forall ({decls}) {imp}))"),
            emitter.declarations,
        ));
    }

    // shared_arity > 0: emit declare-consts for step-new vars +
    // a ground assert for the implication.
    let mut step_new: Vec<String> = emitter
        .free_vars
        .iter()
        .filter(|v| parse_synthetic_var_name(v).map_or(false, |idx| idx >= shared_arity))
        .cloned()
        .collect();
    step_new.sort();
    let mut block = String::new();
    for v in &step_new {
        let sort = emitter.declared_var_sort(v);
        block.push_str(&format!("(declare-const {v} {sort})\n"));
    }
    block.push_str(&format!("(assert {imp})"));
    Ok((block, emitter.declarations))
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
    /// WI-20261012-ZZ7PH — an EQUATION, `lhs <=> rhs`, stored with the head
    /// `anthill.kernel.unify(lhs, rhs)`. The head is the conclusion `(= lhs rhs)`, each
    /// side a formula or a value by its own shape. It was `Unsupported` ("rule head
    /// shape not supported"), so no law of a spec lifted: 21 of the standard library's
    /// 22 are equations.
    Equation,
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
    /// Whether a call so skipped is STATED is `body_is`'.
    abstract_mode: bool,
    /// [`SMT_BUILTINS`] resolved against `kb` (WI-897). WHICH OPERATION MEANS
    /// WHICH SMT FORM, decided by symbol identity — see the table's own doc for
    /// why this is not a name compare.
    builtins: SmtBuiltinTable,
    /// WI-20261012-ZZ7PH — THE SORT OF EACH VARIABLE OF THE FRAME BEING READ, by its
    /// name in the document, where a bound or a signature says it (`sort.rs`). One that
    /// is absent is a `Real`, as every variable was — or refused
    /// ([`Self::refusal_subject`]).
    var_sorts: BTreeMap<String, SmtSort>,
    /// What the document must declare before it uses it: the sorts the theory does not
    /// have and the functions on them.
    declarations: Declarations,
    /// LOWERING A LAW: what the requirement binds each type parameter to, for an
    /// operand group no operand decides (`Emitter::seed_param_defaults`). Empty for a
    /// proof's own body and for a cited lemma, which get no such reading.
    param_defaults: HashMap<Symbol, SmtSort>,
    /// LOWERING A LAW ([`lower_spec_law`]): the requirement it is lowered at, as its
    /// text. A law is read as a cited lemma is, with three differences that each hang
    /// on this: its own bound names the SPEC's parameter, which is what the requirement
    /// binds it to; a premise that is a rule's predicate is refused, where a lemma's is
    /// stated; and a variable nothing gives a sort is refused whatever scope it is in.
    lowering_law: Option<String>,
    /// The clause read is a STEP of a structured proof (`ProgramClause::shared_arity`),
    /// which says what a refusal can advise: a step writes no bound.
    reading_step: bool,
    /// The variables of a stored fact's term being lowered (a `constraint` law), which
    /// are the loader's own and no frame's: each with the name it goes by here.
    global_names: Vec<(VarId, String)>,
    /// An OBLIGATION bounds the head's result variable, so the body must bind it. A
    /// satisfiability check does not: there a head variable the body leaves unbound is
    /// the rule's parameter, and free in the document like any other.
    result_required: bool,
    /// WI-20261012-CDHSQ — what the body being read is to the document, which says
    /// what may be left out of it.
    body_is: BodyIs,
    /// The rules whose bodies are being read INLINED into the clause, outermost first.
    /// Inside one a name is not what it is in the clause's own frame: the rule's head
    /// variables are written as what the caller passed, and a variable of its own by a
    /// name past the clause's ([`Self::name_own_variables`]; by its index it was the
    /// caller's variable of that index, WI-20261012-BR7P3). Each with the arity it was
    /// called at: `span/2` beside `span/3` is two predicates, and a clause of one calling
    /// the other is no recursion (WI-20261013-1KF32, /code-review).
    inlining: Vec<InlinedFrame>,
    /// WI-20261013-1KF32 — THE WORLD BEING READ: which clause answers each call that
    /// several can ([`Self::choose`]). `None` where the document is not split by them —
    /// an obligation, whose document is one term's bound, and a lift, which reads no
    /// call — and there a call several clauses can answer is refused.
    choices: Option<Choices>,
    /// The value the body bound the result variable of a function-like head to, beside
    /// `body_smtlib`, which defines it: a document of several worlds equates it in each.
    result_value: Option<String>,
    /// THE NAME THE NEXT VARIABLE OF AN INLINED RULE'S OWN IS GIVEN: `var_<n>`, `n` past
    /// the clause's own variables ([`frame_size`]) and every such variable named before
    /// it. A variable of a rule read inlined that its head does not pass is named so when
    /// the rule's frame is opened ([`Self::name_own_variables`]); by its index it would
    /// be the clause's variable of that index, and the document would relate two
    /// variables as one. `None` until a clause is opened; a world of a document of
    /// several starts where the world read before it ended ([`read_worlds`]).
    next_own_variable: Option<u32>,
    /// The sorts of those variables, by the names they are given: an inlined rule's
    /// frame keeps its sorts by its own indices, and is closed before the document's
    /// free variables are declared.
    own_variable_sorts: BTreeMap<String, SmtSort>,
    /// The variables [`Self::bind_variable`] equated with a value, which stay constants
    /// of the document: a one-argument rule's result given its value so is given one
    /// ([`Self::translate_called_rule`]).
    equated: BTreeSet<String>,
}

/// A rule whose body is being read inlined ([`Emitter::inlining`]).
struct InlinedFrame {
    rule: String,
    /// The arity it was called at.
    arity: usize,
    /// The name each variable of its frame went by when the frame was opened — the
    /// variable its caller passed, or the name it was given
    /// ([`Emitter::name_own_variables`]). A variable bound to another name since is an
    /// ALIAS of that variable ([`Emitter::bind_variable`]). In the clause's own frame a
    /// variable goes by its index, and is bound to no name of its own.
    names: BTreeMap<String, String>,
}

impl InlinedFrame {
    /// The frame of `rule`, called at `arity`, as `frame` binds it when it is opened.
    fn opened(rule: &str, arity: usize, frame: &BTreeMap<String, String>) -> Self {
        let names = frame
            .iter()
            .filter(|(_, bound)| parse_synthetic_var_name(bound).is_some())
            .map(|(local, bound)| (local.clone(), bound.clone()))
            .collect();
        Self {
            rule: rule.to_owned(),
            arity,
            names,
        }
    }
}

/// WI-20261013-1KF32 — THE MOST WORLDS A DOCUMENT IS READ IN (decided with the user,
/// 2026-10-14). Each repeats the whole body, and the count is the PRODUCT of the clauses
/// each choice had, so two tables of eight rows are 64. Beyond it the proof is refused.
const WORLD_CAP: usize = 64;

/// WI-20261013-1KF32 — the choices of one reading of a body ([`read_worlds`]).
#[derive(Debug, Default)]
struct Choices {
    /// The clause taken at each choice point, in the order the points are met: the
    /// prefix this reading was asked for. A point beyond it takes the first.
    taken: Vec<usize>,
    /// Every point this reading met, in order.
    met: Vec<ChoicePoint>,
}

/// A call — or an entity premise — that several clauses can answer, met in a reading.
#[derive(Debug, Clone)]
struct ChoicePoint {
    /// How many can answer it.
    of: usize,
    /// What it is a call of, as the document's comment and a refusal name it.
    what: String,
    /// What answers it: a `clause` of a predicate, a `fact` of an entity.
    answered_by: &'static str,
}

/// WI-20261012-CDHSQ — WHAT A CLAUSE'S BODY IS TO THE DOCUMENT BEING WRITTEN, which
/// says what may be left out of it.
///
/// A cited lemma `conclusion :- related(?a, ?b)` is handed to its consumer as an
/// implication, and `related(?a, ?b)` is its antecedent. The lift does not read the
/// predicate's body — that would condition the lemma on facts the consumer does not
/// quote — and it may not pass the call over either, which hands the consumer the
/// conclusion unconditionally. So the predicate is a relation the document declares and
/// nothing interprets ([`Emitter::state_predicate_call`]): the lift's premise is written
/// with it, and so is the consumer's own call, which is what discharges the premise.
enum BodyIs {
    /// THE ANTECEDENT of a cited lemma's lift. A goal left out of it is a premise
    /// dropped, and the lemma handed on then says more than was proved: every call of a
    /// rule's predicate is stated, and a goal that cannot be written whole is refused.
    Antecedent,
    /// THE HYPOTHESES of the proof being discharged. A conjunct left out of a
    /// satisfiability check can only lose an `unsat`, so a rule call may go unread
    /// (`abstract_mode`). What the proof states is its own calls of the relations the
    /// lemmas it cites declared ([`Declarations::predicates`]) — a call it skips and one
    /// it reads the body of alike — and no other, so a proof that cites no such lemma
    /// has the document it had. None for a law, which is refused such a premise before
    /// this is asked, and for an obligation (`emit_obligation_with`), whose document
    /// holds none of its body's assertions.
    Hypotheses { cited: BTreeSet<String> },
}

impl BodyIs {
    /// The body of a proof under `config`: it states what its hypotheses declared.
    fn hypotheses_of(config: &ProofConfig) -> Self {
        Self::Hypotheses {
            cited: config
                .declarations
                .predicates()
                .map(str::to_owned)
                .collect(),
        }
    }

    /// Is a call of `relation` (`ns.related/2`) stated?
    fn states(&self, relation: &str) -> bool {
        match self {
            Self::Antecedent => true,
            Self::Hypotheses { cited } => cited.contains(relation),
        }
    }
}

/// WI-20261012-KF2SD — the clause a call is read by ([`Emitter::answering_clause`]):
/// the one of the call's arity that can answer it, its head written by position.
struct Answer {
    clause: ProgramClause,
    /// The head's arguments, as many as the call's.
    head_args: Vec<Rc<NodeOccurrence>>,
}

/// What an argument of a call, or of a clause's head, is KNOWN to be — which is what
/// one may be told apart from another by ([`Emitter::admits`]). A variable, a computed
/// term (`?k + 1`) and a name that is no constructor are not known. Neither is a
/// string: the occurrence of one is also how a pre-rendered SMT fragment is carried
/// across an inline boundary (WI-686), which is a number.
enum Known<'a> {
    Number(f64),
    Truth(bool),
    /// A construction: a constructor or an entity, applied — to nothing, for `Leader`.
    Built(
        Symbol,
        &'a [Rc<NodeOccurrence>],
        &'a [(Symbol, Rc<NodeOccurrence>)],
    ),
}

impl<'kb> Emitter<'kb> {
    fn new(kb: &'kb KnowledgeBase) -> Self {
        Self::with_builtins(kb, SmtBuiltinTable::resolve(kb))
    }

    /// An emitter over `kb` whose [`SmtBuiltinTable`] is resolved already: the worlds of
    /// one document share one ([`read_worlds`]).
    fn with_builtins(kb: &'kb KnowledgeBase, builtins: SmtBuiltinTable) -> Self {
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
            builtins,
            var_sorts: BTreeMap::new(),
            declarations: Declarations::default(),
            param_defaults: HashMap::new(),
            lowering_law: None,
            reading_step: false,
            global_names: Vec::new(),
            result_required: false,
            body_is: BodyIs::Hypotheses {
                cited: BTreeSet::new(),
            },
            inlining: Vec::new(),
            choices: None,
            result_value: None,
            next_own_variable: None,
            own_variable_sorts: BTreeMap::new(),
            equated: BTreeSet::new(),
        }
    }

    /// WI-20261013-1KF32 — WHICH OF `of` CLAUSES ANSWERS THE CHOICE POINT MET NOW: the
    /// one the world being read names, or the first where the point is beyond what it
    /// names ([`read_worlds`] then reads the others). Where the document is not split by
    /// choices (`choices` is `None`), `refusal`.
    fn choose(
        &mut self,
        of: usize,
        answered_by: &'static str,
        what: impl FnOnce() -> String,
        refusal: impl FnOnce() -> SmtGenError,
    ) -> Result<usize, SmtGenError> {
        let Some(choices) = self.choices.as_mut() else {
            return Err(refusal());
        };
        let pick = choices.taken.get(choices.met.len()).copied().unwrap_or(0);
        choices.met.push(ChoicePoint {
            of,
            what: what(),
            answered_by,
        });
        Ok(pick)
    }

    /// Find the rule by qualified name. Walk its body and produce
    /// the SMT-LIB equation that defines the head's result variable.
    ///
    /// ONE CLAUSE, OR REFUSED (WI-20261012-KF2SD, /code-review). A name may resolve to
    /// several: a rule written with several heads is a clause for each under the one
    /// label, and so is a predicate written as several rules. The first was read and the
    /// rest were not — the defect of this ticket at the root of a proof. Measured: `rule
    /// both: gte(?x, 0.0), gte(?x, 5.0) :- gte(?x, 1.0)` proved, its document the first
    /// head's; its LIFT is of every head ([`lift_rule`]), so `gte(?y, 5.0) :- gte(?y,
    /// 1.0)` proved `using both`; and `rule viol(?w) :- gte(?w, 1.0), lte(?w, 0.0)`
    /// beside `rule viol(?w) :- gte(?w, 0.0)` proved by its first body.
    ///
    /// The heads of one rule are conclusions of one body, and their conjunction is what
    /// is owed — but each clause numbers its variables by its OWN head first (measured:
    /// `gte(?x, 0.0), gte(?y, 0.0) :- gte(?x, 1.0), gte(?y, 2.0)` is `?x` = `var_1` in
    /// one clause and `var_0` in the other), so one clause's head is not written in
    /// another's bindings. Until each is read in a frame of its own the proof is
    /// refused, and says how many clauses it is of.
    fn collect_rule(&mut self, rule_qn: &str) -> Result<(), SmtGenError> {
        let mut clauses = stated_clauses(self.kb, rule_qn).into_iter();
        let clause = clauses
            .next()
            .ok_or_else(|| SmtGenError::new(format!("rule '{rule_qn}' not found")))?;
        let further = clauses.count();
        if further > 0 {
            return Err(SmtGenError::new(format!(
                "the rule '{rule_qn}' is {} clauses — a rule written with several heads is \
                 one for each, and so is a predicate written as several rules — and a proof \
                 is ONE document: it would be of the first alone, and the rule is cited as \
                 all of them. Prove each under a name of its own",
                further + 1
            )));
        }
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
        let past_the_clause = frame_size(self.kb, clause, *head);
        self.next_own_variable =
            Some(self.next_own_variable.map_or(past_the_clause, |next| next.max(past_the_clause)));
        let head_shape = self.classify_head(*head);
        if let HeadShape::FunctionLike { result_idx } = head_shape {
            self.result_var = synthetic_var_name(result_idx);
        } else if let HeadShape::Unsupported(msg) = &head_shape {
            return Err(SmtGenError::new(msg.clone()));
        }

        // The head is still a hash-consed term (heads stay terms — they are
        // SEARCHED in the discrimination tree). Materialize it to the
        // occurrence substrate so it flows through the same occurrence-based
        // `process_body_goal` as the body goals (WI-246).
        let head_occ = match head_shape {
            HeadShape::Predicate | HeadShape::Equation => {
                Some(materialize_from_handle(self.kb, *head))
            }
            _ => None,
        };

        // WI-20261012-ZZ7PH — the sorts of the clause's variables, before any goal is
        // translated: what the head's bounds say, and what follows from them through
        // the signatures of the operations the clause applies (`sort.rs`).
        self.seed_bounds(clause)?;
        if clause.shared_arity > 0 {
            self.reading_step = true;
            self.seed_parent_bounds(rule_qn)?;
        }
        let sorted: Vec<Rc<NodeOccurrence>> =
            clause.body_nodes.iter().chain(&head_occ).cloned().collect();
        self.infer_var_sorts(&sorted)?;

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
        match (&head_shape, &head_occ) {
            (HeadShape::Predicate, Some(goal)) => {
                let body_count = self.assertions.len();
                self.process_body_goal(goal, &mut local_bindings)?;
                self.conclusion_assertions = self.assertions.split_off(body_count);
            }
            (HeadShape::Equation, Some(equation)) => {
                let Some((_, [lhs, rhs], _)) = occ_as_fn(equation) else {
                    unreachable!("`classify_head` answers `Equation` for two operands");
                };
                let lhs = self.translate_term(lhs, &local_bindings)?;
                let rhs = self.translate_term(rhs, &local_bindings)?;
                self.conclusion_assertions = vec![format!("(= {lhs} {rhs})")];
            }
            _ => {}
        }

        // For upper-bound mode the result var must be bound by the
        // body. In satisfiability mode a head variable the body does not bind is
        // the rule's PARAMETER (`rule irreflexive(?a: T) :- neq(?a, ?a)`), free in
        // the document like any other variable its goals name (WI-20261012-ZZ7PH:
        // it was "rule body never bound the result variable" there too).
        if !self.result_var.is_empty() {
            match local_bindings.get(&self.result_var) {
                Some(result_smt) => {
                    let sort = self.declared_var_sort(&self.result_var.clone());
                    self.body_smtlib = format!(
                        "(define-fun {} () {sort} {})",
                        sanitize_smt_id(&self.result_var),
                        result_smt
                    );
                    self.result_value = Some(result_smt.clone());
                }
                None if self.result_required => {
                    return Err(SmtGenError::new(format!(
                        "rule body never bound the result variable '?{}'",
                        self.result_var
                    )))
                }
                None => self.result_var.clear(),
            }
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
        //
        // WI-20261012-BR7P3 — a variable of a rule read inlined is one of them where the
        // document writes it, at the sort that rule's frame gave it: its name is past the
        // clause's own, so it is no key of the clause's sorts.
        for (named, sort) in std::mem::take(&mut self.own_variable_sorts) {
            let clause_had = self.var_sorts.insert(named, sort);
            debug_assert!(clause_had.is_none(), "an own variable is named past the clause's");
        }
        self.note_free_vars(&local_bindings)?;

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

    /// The clause's FREE variables: any `var_<i>` an assertion (body or conclusion) or
    /// `body_smtlib` names that `bindings` does not bind. See the note at its one
    /// caller in [`Self::collect_rule_clause`] for why `body_smtlib` is scanned.
    ///
    /// WI-20261012-ZZ7PH — and each has a sort, or is refused where one that has none
    /// is ([`Self::refusal_subject`]). A variable is a whole TOKEN of the fragment
    /// ([`smt_tokens`]): a document names declared functions by qualified names now, and
    /// a segment of one spelled `var_1` is no variable.
    fn note_free_vars(&mut self, bindings: &BTreeMap<String, String>) -> Result<(), SmtGenError> {
        let scan = self
            .assertions
            .iter()
            .chain(self.conclusion_assertions.iter())
            .chain(std::iter::once(&self.body_smtlib));
        for assertion in scan {
            for tok in smt_tokens(assertion) {
                if parse_synthetic_var_name(tok).is_some() && !bindings.contains_key(tok) {
                    self.free_vars.insert(tok.to_string());
                }
            }
        }
        if let Some(unsorted) = self
            .free_vars
            .iter()
            .find(|v| !self.var_sorts.contains_key(*v))
        {
            if let Some(of) = self.refusal_subject() {
                return Err(sort::no_sort_refusal(&of, unsorted, self.reading_step));
            }
        }
        // What the free variables are of is declared with the document.
        let free: Vec<String> = self.free_vars.iter().cloned().collect();
        for v in &free {
            self.declared_var_sort(v);
        }
        Ok(())
    }

    /// Process one rule-body goal.
    fn process_body_goal(
        &mut self,
        goal: &Rc<NodeOccurrence>,
        bindings: &mut BTreeMap<String, String>,
    ) -> Result<(), SmtGenError> {
        // WI-20261012-ZZ7PH — a goal the loader GENERATED for a typed head (the type
        // test in front of the body, the fill behind it) says what the variable's
        // bound says, and the bound is read where the clause is opened
        // (`seed_bounds`): the variable has that sort. Until this every proof whose
        // rule wrote a bound was refused here — "unhandled body goal functor
        // 'anthill.kernel.__domain_guard'", for `?x: Float` as for `?a: T`.
        if is_typed_head_domain_goal(self.kb, goal) {
            return Ok(());
        }
        // WI-20261012-CDHSQ (/code-review) — A RULE'S PREDICATE OF NO ARGUMENTS, named
        // bare, is the call `ready()` is: the two spellings are one term, and a step of a
        // structured proof stores the bare one. It was "non-Fn body goal" where `ready()`
        // in a rule's body was read, so one premise had two treatments.
        let bare_call = match goal.as_expr() {
            Some(Expr::Ref(name) | Expr::Ident(name))
                if self.kb.rules_by_functor_iter(*name).next().is_some() =>
            {
                Some(*name)
            }
            _ => None,
        };
        let Some((functor, pos_args, named_args)) = bare_call
            .map(|name| (name, &[][..], &[][..]))
            .or_else(|| occ_as_fn(goal))
        else {
            return Err(SmtGenError::new(format!(
                "non-Fn body goal: {:?}",
                goal.as_expr().map(std::mem::discriminant)
            )));
        };
        let qn = self.kb.qualified_name_of(functor);

        // An operation at a declared sort is an uninterpreted function, and as a goal
        // it is asserted. BEFORE the theory's readings below: `eq` at an abstract
        // carrier is the carrier's relation, not `=` and not a binding.
        if let Some((applied, sort)) =
            self.uninterpreted_call(functor, pos_args, named_args, None, bindings)?
        {
            if sort != SmtSort::Bool {
                return Err(SmtGenError::new(format!(
                    "the goal `{qn}` is of sort {sort}, and a goal is a formula"
                )));
            }
            self.assertions.push(applied);
            return Ok(());
        }

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
                let bound = synthetic_var_name(*i);
                // WI-20261012-ZZ7PH — `?x = <a term that names ?x>` defines nothing: it is
                // a CONDITION on `?x`. Taken for a definition, `eq(?x, ?x)` bound the
                // variable to itself, and a bound variable is not declared: the document
                // named a constant it never declared, and the solver said so ("unknown
                // constant var_1") where a verdict was expected.
                //
                // WI-20261012-CDHSQ (/code-review) — ASKED OF THE TERM, NOT OF ITS TEXT. The
                // text is in the names of the frame the document is written in, and inside
                // an inlined rule that is the caller's: `rule dbl(?a, ?r) :- ?r = ?a + ?a`
                // called `dbl(?x, ?r)` has the right side `(+ var_0 var_0)`, which is the
                // caller's `?x`, and the callee's `?r` is `var_0` by its own index. Read
                // off the text, the definition was a CONDITION on the caller's `?x` —
                // `(= var_0 (+ var_0 var_0))`, so x = 0 — and `lt(?x, 0.0)` beside it
                // proved unsatisfiable. The variable is written as this frame reads it.
                let names_itself = debruijn_vars_of([&pos_args[1]]).contains(i);
                if names_itself {
                    let itself = self.translate_expr(&pos_args[0], bindings)?;
                    self.assertions.push(format!("(= {itself} {rhs_smt})"));
                    return Ok(());
                }
                self.bind_variable(bound, rhs_smt, bindings);
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
            // WI-20261012-CDHSQ (/code-review) — IN A LIFT A SLOT THAT IS NO VARIABLE IS
            // REFUSED. `Mode(kind: 2.0, cap: ?c)` says which fact it is of, and the loop
            // below passes that slot over: the lift came back `(=> (>= var_1 cap) …)`,
            // its `kind` premise gone, and a proof about the `Mode` of another kind
            // proved by citing it (measured). In a proof's own body the slot left out
            // is a hypothesis left out, which can only lose an `unsat`.
            if matches!(self.body_is, BodyIs::Antecedent) {
                let unread = named_args
                    .iter()
                    .find(|(_, slot)| !matches!(slot.as_expr(), Some(Expr::Var(_))));
                if let Some((field, _)) = unread {
                    return Err(SmtGenError::new(format!(
                        "the premise `{qn}` is an entity and its field `{}` is given a value \
                         that is no variable, which is not read into a lift, and is not \
                         passed over: a cited lemma's entity premise binds its fields to \
                         variables",
                        self.kb.local_name_of(*field)
                    )));
                }
            }
            let entity_qn = qn.to_string();
            // WI-20261013-1KF32 — AN ENTITY OF SEVERAL FACTS is the table of a call in an
            // entity's spelling: a world for each fact the premise's slots admit, its
            // fields bound in that world ([`Self::read_by_rows`]). Where the document is
            // not split (a lift, an obligation), the harvest refuses it as before.
            if self.choices.is_some() {
                let rows = self.entity_rows(&entity_qn)?;
                if self.read_by_rows(&rows, named_args) {
                    return self.read_entity_row(&entity_qn, &rows, named_args, bindings);
                }
            }
            self.referenced_entities.insert(entity_qn.clone());
            for (field_sym, val_occ) in named_args {
                let bind_idx = match val_occ.as_expr() {
                    Some(Expr::Var(Var::DeBruijn(i))) => *i,
                    _ => continue, // non-var slots (`field: ?` wildcards / literals)
                };
                let field_name = self.kb.local_name_of(*field_sym).to_string();
                let const_name = sanitize_smt_id(&field_name);
                self.bind_variable(synthetic_var_name(bind_idx), const_name.clone(), bindings);
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
        //
        // WI-20261012-CDHSQ — AND THAT REASON IS THE PROOF'S OWN BODY'S, NOT A LIFT'S. A
        // conjunct left out of a satisfiability check can only lose an `unsat`. In a
        // lift the same call is a PREMISE, and passing it over is the act the paragraph
        // above made loud for a premise it could not read — only the rule call was left
        // silent. MEASURED: `rule lemma: gte(?a, ?b) :- related(?a, ?b)` lifted to
        // `(=> true (>= var_1 var_0))`, and a proof citing it proved `gte(?c, 5.0) :-
        // gte(0.0, ?c)`. So a lift STATES the call, as the uninterpreted relation of the
        // predicate's name, and a proof's body states its own call of a predicate a
        // lemma it cites declared — which is how the premise is discharged
        // ([`Self::state_predicate_call`], [`BodyIs`]).
        if self.abstract_mode && self.kb.rules_by_functor_iter(functor).next().is_some() {
            // WI-20261012-ZZ7PH — AND NOT IN A LAW AT ALL. A law is assumed, not proved,
            // and is of every provider; one with a premise that is a rule's predicate is
            // left out, and said: `eq(weight(?a), weight(?b)) :- related(?a, ?b)` with
            // the premise passed over became "every two weights are equal", and a claim
            // that needed it proved.
            if self.lowering_law.is_some() {
                return Err(SmtGenError::new(format!(
                    "the law's premise `{qn}` is a rule's predicate, which is not read into \
                     the law: without it the law would state more than its spec does"
                )));
            }
            self.visited_rules.insert(qn.to_string());
            return self.state_predicate_call(functor, pos_args, named_args, bindings);
        }

        // A rule call READ: `<rule>(<a1>, ..., <aN>)`, by THE CLAUSE THAT ANSWERS IT in
        // the world being read (WI-20261012-KF2SD, WI-20261013-1KF32,
        // [`Self::answering_clause`]) — three ways, by what that clause is:
        //   (1) A fact — a rule with an empty body. Each call-side
        //       DeBruijn var gets bound to the fact's slot (literal →
        //       string binding, entity occurrence → entity_bindings).
        //   (2) A bodied clause of ONE argument — the single-arg shorthand
        //       `<rule_qn>(?result_var)` that yields one inline SMT
        //       expression. Used by call sites like `step_distance_bound(?delta)`.
        //   (3) A bodied clause of several. Open it with caller→callee
        //       parameter substitution; process its goals as if inlined here.
        // No named_args path yet — a call with named_args is a v1 concern.
        if !pos_args.is_empty() && named_args.is_empty() {
            if let Some(answer) = self.answering_clause(functor, pos_args, bindings)? {
                // The functor's QN is of the proof's dependency set, so the cache key
                // observes any change to its defining facts (initial-geometry edits
                // invalidate downstream proofs) and to its body.
                self.visited_rules.insert(qn.to_string());
                if answer.clause.is_fact() {
                    self.bind_fact_call(qn, &answer, pos_args, bindings)?;
                } else if self
                    .inlining
                    .iter()
                    .any(|frame| frame.rule == qn && frame.arity == pos_args.len())
                {
                    // WI-20261013-1KF32 — A RECURSIVE CLAUSE IS NOT UNFOLDED (decided with
                    // the user, 2026-10-14). The call stands in a clause of its own
                    // predicate being read, and reading the clause that answers it reads
                    // that call again: a step beside its base case (`at(?k_next, …) :-
                    // at(?k, …), …`) is a world for each depth there is, and a predicate
                    // of one such clause has no base case to stop at — measured on
                    // 79a6703f, `rule loop(?x) :- loop(?x), gte(?x, 0.0)` under a proof
                    // overflowed the stack and aborted the CLI (exit 134).
                    let site = self.inlining.last().map_or(String::new(), |frame| {
                        format!(", in the body of `{}` (read inlined),", frame.rule)
                    });
                    return Err(SmtGenError::new(format!(
                        "the call of `{qn}/{}`{site} is answered by a clause of `{qn}` with a \
                         body while a clause of `{qn}` is being read: a recursive predicate is \
                         not unfolded into a proof's document (WI-20261013-1KF32). Prove the \
                         claim by induction, or give the case this proof is about a predicate \
                         of its own; a rule stated with a label and this predicate for its \
                         head is one of its clauses",
                        pos_args.len()
                    )));
                } else if pos_args.len() == 1 {
                    let bind_idx = match pos_args[0].as_expr() {
                        Some(Expr::Var(Var::DeBruijn(i))) => *i,
                        other => {
                            return Err(SmtGenError::new(format!(
                                "v0: rule call's pos arg must be a DeBruijn var, got {:?}",
                                other.map(std::mem::discriminant)
                            )))
                        }
                    };
                    let inlined = self.translate_called_rule(qn, &answer)?;
                    self.bind_variable(synthetic_var_name(bind_idx), inlined, bindings);
                } else {
                    self.inline_rule_call(qn, &answer, pos_args, bindings)?;
                }
                // WI-20261012-CDHSQ — and the call itself is held, beside what was read
                // of it: a cited lemma whose premise it is has the relation and not the
                // body. AFTER the reading, so an argument the reading bound is written
                // as its value.
                return self.state_predicate_call(functor, pos_args, named_args, bindings);
            }
        }

        Err(self
            .unsorted_operand_refusal(functor, pos_args, named_args)
            .unwrap_or_else(|| SmtGenError::new(format!("v0: unhandled body goal functor '{qn}'"))))
    }

    /// WI-20261012-KF2SD — THE ONE CLAUSE THAT ANSWERS A CALL, and a refusal where
    /// more than one can.
    ///
    /// A rule call in a proved body is a HYPOTHESIS, and a predicate of several clauses
    /// holds when ANY of them does. Each reading of a call takes one clause, so read as
    /// the first of several the hypothesis was stronger than the rule states, and what
    /// was proved was less than the record says. Measured: `related(?a, ?b) :-
    /// gte(?a, ?b)` beside `related(?a, ?b) :- lte(?a, ?b)` proved `gte(?a, ?b) :-
    /// related(?a, ?b)`, which `related(1, 2)` refutes; `fact start(5.0)` beside `fact
    /// start(-1.0)` proved `gte(?d, 0.0) :- start(?d)`.
    ///
    /// WHICH CLAUSES CAN ANSWER: those of the call's arity whose head no argument of
    /// the call rules out ([`Self::admits`]). So a ground argument selects among facts
    /// — `initial_pose(Leader, ?l)` has one — and a bodied clause whose head is all
    /// variables answers every call of its arity: lf1's `real_pose_at` was two base
    /// facts and such a step, and each of its six calls was read as a base fact.
    /// A clause of another arity is no candidate, so `span/2` beside `span/3` is two
    /// predicates here, where the first bodied clause's arity used to refuse the other's
    /// calls.
    ///
    /// EVERY CLAUSE UNDER THE FUNCTOR, a lemma too: a rule written with a label and the
    /// predicate for its head (`rule safe_weaken: safe(?x, ?n) :- …`) is a clause of the
    /// predicate, as the resolver has it, and what it adds is not read by reading the
    /// definition beside it.
    ///
    /// SEVERAL: A CHOICE POINT (WI-20261013-1KF32). The call means the disjunction of
    /// the clauses' readings, and the document is read once for each — a WORLD, the
    /// rest of the body read in it as well ([`read_worlds`]) — so a variable a clause
    /// binds is bound by substitution in its world, an entity is an occurrence there, and
    /// a later call is selected by what the world bound. This returns the clause the
    /// world being read takes. Where the document is not split (an obligation), refused.
    ///
    /// `None` where the functor has no clause with arguments at all: the caller's error.
    fn answering_clause(
        &mut self,
        functor: Symbol,
        call_args: &[Rc<NodeOccurrence>],
        bindings: &BTreeMap<String, String>,
    ) -> Result<Option<Answer>, SmtGenError> {
        let kb = self.kb;
        let qn = kb.qualified_name_of(functor);
        let arity = call_args.len();
        let mut other_arities: BTreeSet<usize> = BTreeSet::new();
        let mut of_this_arity = 0usize;
        // What can answer, and whether its head is written by position.
        let mut answering: Vec<(Answer, bool)> = Vec::new();
        for clause in kb.program_clauses_by_functor(functor) {
            let Value::Term { id: head, .. } = clause.head else {
                return Err(SmtGenError::new(format!(
                    "v0: rule call `{qn}` has a clause with a non-term program head"
                )));
            };
            // The arity off the term, before anything is built for a clause of another.
            let (head_arity, named) = match self.kb.get_term(head) {
                Term::Fn {
                    pos_args,
                    named_args,
                    ..
                } => (pos_args.len() + named_args.len(), named_args.len()),
                _ => (0, 0),
            };
            if head_arity != arity {
                if head_arity > 0 {
                    other_arities.insert(head_arity);
                }
                continue;
            }
            of_this_arity += 1;
            // Head stays a term (searched in the discrim tree); materialize it to the
            // occurrence substrate so the call args (occurrences) and the head's
            // compare occ-vs-occ (WI-246).
            let head_occ = materialize_from_handle(self.kb, head);
            let head_args: Vec<Rc<NodeOccurrence>> = match occ_as_fn(&head_occ) {
                Some((_, pos, _)) => pos.to_vec(),
                None => Vec::new(),
            };
            // A head written with named arguments has no order to compare by: it is
            // not ruled out, and read alone it is refused.
            let positional = named == 0;
            let admitted = !positional
                || (call_args
                    .iter()
                    .zip(head_args.iter())
                    .all(|(call, head)| self.admits(head, call, bindings))
                    && self.one_number_each(&head_args, call_args, bindings));
            if admitted {
                answering.push((Answer { clause, head_args }, positional));
            }
        }
        // Where the call stands, when it is not the proof's own: the proof names a
        // rule, and the call refused may be three rules down.
        let site = match self.inlining.last() {
            Some(frame) => format!(", in the body of `{}` (read inlined),", frame.rule),
            None => String::new(),
        };
        let pick = match answering.len() {
            // Not "the body never holds": a clause may be an operation's body
            // specialized to ANOTHER call's arguments (WI-687 synthesizes one for a
            // functor, for whichever proof ran first), and then the operation is
            // defined at this call and its clause for it is not here. So a world in
            // which a call has none is refused, and not dropped as `false`.
            0 if of_this_arity > 0 => {
                return Err(SmtGenError::new(format!(
                    "the call of `{qn}/{arity}`{site} can be answered by no clause of the \
                     predicate: each of its {of_this_arity} has in its head an argument the \
                     call's rules out. Where those clauses are the predicate, the body never \
                     holds; a clause that is an operation's body specialized to another call's \
                     arguments (WI-687) does not apply to this call"
                )))
            }
            0 if other_arities.is_empty() => return Ok(None),
            0 => {
                return Err(SmtGenError::new(format!(
                    "rule call arity mismatch for '{qn}': the call has {arity} argument(s), \
                     and its clauses have {}",
                    other_arities
                        .iter()
                        .map(usize::to_string)
                        .collect::<Vec<_>>()
                        .join(" or ")
                )))
            }
            1 => 0,
            several => {
                let facts = answering
                    .iter()
                    .filter(|(answer, _)| answer.clause.is_fact())
                    .count();
                let bodied = several - facts;
                self.choose(
                    several,
                    "clause",
                    || {
                        format!(
                            "`{qn}/{arity}`{site} ({facts} fact(s), {bodied} with a body)",
                            site = site.trim_end_matches(',')
                        )
                    },
                    || {
                        SmtGenError::new(format!(
                            "the call of `{qn}/{arity}`{site} can be answered by {several} \
                             clauses of the predicate ({facts} fact(s), {bodied} with a body), \
                             and an obligation bounds ONE term: the call holds when ANY of them \
                             does, and its document is not split by them (WI-20261013-1KF32). \
                             State it as a proof of the rule, or give the case it is about a \
                             predicate of its own"
                        ))
                    },
                )?
            }
        };
        match answering.swap_remove(pick) {
            (answer, true) => Ok(Some(answer)),
            (_, false) => Err(SmtGenError::new(format!(
                "v0: the clause of '{qn}' that answers this call must have only pos args in head"
            ))),
        }
    }

    /// Does `head`, an argument of a clause's head, admit `call`, the call's argument
    /// at that position? NO only where both are KNOWN and differ ([`Known`]): what is
    /// not known — a variable, a computed term, a name that is no constructor — is
    /// admitted, so a clause is never ruled out on a guess.
    fn admits(
        &self,
        head: &Rc<NodeOccurrence>,
        call: &Rc<NodeOccurrence>,
        bindings: &BTreeMap<String, String>,
    ) -> bool {
        match (self.known(head), self.known_argument(call, bindings)) {
            (Some(head), Some(call)) => self.agree(&head, &call),
            _ => true,
        }
    }

    /// WI-20261013-1KF32 (/code-review) — A VARIABLE THE CALL WRITES TWICE MEETS ONE NUMBER:
    /// where the head has a number at two of its positions, they agree. Each position is
    /// admitted on its own ([`Self::admits`]) and a variable nothing knows rules nothing
    /// out, so `twice(?k, ?k, ?r)` admitted `rule twice(0, 1, ?r) :- …`, and its world was
    /// then refused whole — the first number bound `?k`, and the second was not it — where
    /// the clause cannot answer the call; and `pair(?x, ?x)` read `fact pair(1.0, 2.0)` as
    /// `?x` = 2.0, the second slot overwriting the first.
    fn one_number_each(
        &self,
        head_args: &[Rc<NodeOccurrence>],
        call_args: &[Rc<NodeOccurrence>],
        bindings: &BTreeMap<String, String>,
    ) -> bool {
        let mut met: BTreeMap<u32, f64> = BTreeMap::new();
        call_args.iter().zip(head_args).all(|(call, head)| {
            match (call.as_expr(), self.known(head)) {
                (Some(Expr::Var(Var::DeBruijn(index))), Some(Known::Number(number)))
                    if self.known_argument(call, bindings).is_none() =>
                {
                    *met.entry(*index).or_insert(number) == number
                }
                _ => true,
            }
        })
    }

    /// What the call's argument `call` is known to be, in the frame being read
    /// (`bindings`, `self.entity_bindings`).
    ///
    /// THE CALL'S OWN VARIABLE is known where this frame has bound it: to a
    /// construction (`?state = TFS(…)` before `step(?state, …)`, WI-687) or to a number
    /// (`?k = 0` before `at(?k, ?x)`). ONLY that one — a variable INSIDE a construction
    /// is not looked up (/code-review). A construction handed across an inline boundary
    /// kept its caller's variables, and read in this frame they were other variables of
    /// the same index (WI-20261012-BR7P3): measured, `wrap(?o, ?r) :- ?z = some(1.0),
    /// pick(?o, ?r)` called `wrap(some(?y), ?r)` took the caller's free `?y` for its own
    /// `?z`, ruled the `some(none)` clause of `pick` out by it, and a claim false at `?y
    /// = none` proved. Such a construction crosses closed over its caller's frame now
    /// ([`Self::bind_head_arg`]), its variables the SMT text of what they are there.
    fn known_argument<'a>(
        &'a self,
        call: &'a Rc<NodeOccurrence>,
        bindings: &BTreeMap<String, String>,
    ) -> Option<Known<'a>> {
        let Some(Expr::Var(Var::DeBruijn(index))) = call.as_expr() else {
            return self.known(call);
        };
        let name = synthetic_var_name(*index);
        match self.entity_bindings.get(&name) {
            Some(bound) => self.known(bound),
            None => bindings
                .get(&name)
                .and_then(|term| numeral(term))
                .map(Known::Number),
        }
    }

    /// The name of `call`, a call's argument, where it is a variable nothing has given a
    /// value: one this frame has bound to no term and no construction, or one bound to a
    /// VARIABLE — a head's parameter an inlined rule was passed the caller's free variable
    /// for, which it goes by the name of (/code-review: `wrap(?k, ?r) :- mode(?k, ?r)`
    /// refused `?k` as "not known" where `mode(?k, ?r)` read it).
    fn free_variable(
        &self,
        call: &Rc<NodeOccurrence>,
        bindings: &BTreeMap<String, String>,
    ) -> Option<String> {
        let Some(Expr::Var(Var::DeBruijn(index))) = call.as_expr() else {
            return None;
        };
        let name = synthetic_var_name(*index);
        if self.entity_bindings.contains_key(&name) {
            return None;
        }
        match bindings.get(&name) {
            None => Some(name),
            Some(term) if parse_synthetic_var_name(term).is_some() => Some(name),
            Some(_) => None,
        }
    }

    /// WI-20261013-1KF32 (/code-review) — `name`, a variable of the frame being read, IS
    /// `value`: a fact's slot, a head's number or an entity's field says so in the world
    /// being read. ONE place for the three, which each substituted, and each lost what the
    /// variable already was:
    ///   * DEFINED as a term (`?k = ?j + 1.0`, then `start(?k)`): the definition was
    ///     overwritten and the equation dropped, so a true claim was a COUNTEREXAMPLE.
    ///     Now `(= <term> value)`, and a numeral that is the value says nothing;
    ///   * NAMED ALREADY by a goal read before (`lte(?d, 10.0), start(?d)`): the goal kept
    ///     `var_d`, which the substitution then left undeclared — z3's "unknown constant"
    ///     (so on 79a6703f, for one fact) — or, declared by another world that does not
    ///     bind it, unconstrained. Now the variable stays a constant of the document, and
    ///     `(= var_d value)` is asserted.
    ///
    /// WI-20261014-FHEEK — AND EVERY OTHER PLACE A VARIABLE IS GIVEN A VALUE: an equation
    /// (`?x = <term>`), a one-argument rule's result, an entity's field read by its
    /// constant, and the value an inlined rule hands back to its caller — each
    /// substituted, and each left a variable the document had already written
    /// undeclared: `?e = ?d + 1.0, p(?d)`, `p` answering `?d` by a fact, was z3's "unknown
    /// constant", the caller's definition of `?e` naming `?d` where `p`'s frame, which
    /// bound it, does not see it. The hand-back is asked in the CALLER's frame, whose
    /// definitions those are.
    ///
    /// Otherwise it is bound by substitution, as it always was: such a document is the one
    /// it was. A variable bound to a variable — an inlined rule's parameter, which goes by
    /// its caller's name, or a variable of its own, which goes by the name it was given
    /// ([`Self::name_own_variables`]) — is asked of that name. That name is the variable's
    /// alone (WI-20261012-BR7P3): before, an inlined rule's own variable went by the name
    /// of the clause's variable of the same index, and an equation asked of that text
    /// equated the two — `q2(?x, ?w) :- start(?y), ?x = ?w` called beside `lte(?c, 3.0)`
    /// equated `?y` with `?c`, and a false claim proved.
    fn bind_variable(
        &mut self,
        name: String,
        value: String,
        bindings: &mut BTreeMap<String, String>,
    ) {
        let term = match bindings.get(&name) {
            None => name.clone(),
            Some(variable) if parse_synthetic_var_name(variable).is_some() => {
                let goes_by = self.inlining.last().and_then(|frame| frame.names.get(&name));
                if goes_by != Some(variable) {
                    // An ALIAS: an equation (`?x = ?y`) or what an inlined rule handed back
                    // made `name` the variable `variable`, which is written where `name`
                    // is not — its own occurrences, read later, among them. A value put in
                    // `name`'s place lost the alias: `?x = ?y, start(?x)` left `?y` free,
                    // and a true claim of `?y` was a COUNTEREXAMPLE.
                    self.assertions.push(format!("(= {variable} {value})"));
                    self.equated.insert(variable.clone());
                    return;
                }
                variable.clone()
            }
            Some(defined) => {
                if !(numeral(defined).is_some() && numeral(defined) == numeral(&value)) {
                    self.assertions.push(format!("(= {defined} {value})"));
                }
                return;
            }
        };
        if term == value {
            return;
        }
        if self.is_written(&term, &name, bindings) {
            self.assertions.push(format!("(= {term} {value})"));
            self.equated.insert(term);
        } else {
            bindings.insert(name, value);
        }
    }

    /// Is `variable`, a variable of the document, written where a value given it by
    /// substitution would not reach — an assertion, what this frame binds another of its
    /// variables (`except` is the one being bound) to, or a construction this frame holds,
    /// whose fields carry their caller's text ([`Self::close_occ`])?
    fn is_written(
        &self,
        variable: &str,
        except: &str,
        bindings: &BTreeMap<String, String>,
    ) -> bool {
        let names = |text: &str| smt_tokens(text).contains(&variable);
        self.assertions.iter().any(|text| names(text))
            || bindings
                .iter()
                .any(|(other, defined)| other != except && names(defined))
            || self
                .entity_bindings
                .values()
                .any(|entity| any_fragment(entity, &names))
    }

    /// WI-20261012-BR7P3 — NAME THE VARIABLES OF A RULE READ INLINED THAT ITS FRAME DOES
    /// NOT BIND YET: those its head was not passed a value or a variable for — its own,
    /// and one passed a construction, which is held as an entity and has no name. `frame`
    /// gets each `var_<i>` (its index) bound to a name past every name the document has
    /// (`next_own_variable`), in the order `occs` first name them; returned, `(var_<i>,
    /// the name)`. Read in the rule's frame, such a variable was `var_<i>`, the clause's
    /// variable of that index: `helper(?x, ?w) :- lt(?x, ?y), lt(?y, ?w)` called
    /// `helper(?a, ?b)` related `?y` as `?b`, and a satisfiable body was `unsat`. So in an
    /// inlined rule's frame every variable has a name of the document, and the clause's
    /// own frame is the one where a variable nothing binds goes by its index
    /// ([`Self::translate_expr`]).
    fn name_own_variables<'a>(
        &mut self,
        occs: impl IntoIterator<Item = &'a Rc<NodeOccurrence>>,
        frame: &mut BTreeMap<String, String>,
    ) -> Result<Vec<(String, String)>, SmtGenError> {
        let mut own = Vec::new();
        for index in debruijn_vars_of(occs) {
            let local = synthetic_var_name(index);
            if frame.contains_key(&local) {
                continue;
            }
            let next = self.next_own_variable.as_mut().ok_or_else(|| {
                SmtGenError::new(
                    "a rule is read inlined before the clause it is read into is opened, so \
                     its own variables have no names past the clause's",
                )
            })?;
            let named = synthetic_var_name(*next);
            *next += 1;
            frame.insert(local.clone(), named.clone());
            own.push((local, named));
        }
        Ok(own)
    }

    /// The sorts the frame being closed gave its own variables (`own`, from
    /// [`Self::name_own_variables`]), kept by the names they go by in the document.
    fn keep_own_variable_sorts(&mut self, own: &[(String, String)]) {
        for (local, named) in own {
            if let Some(sort) = self.var_sorts.get(local) {
                self.own_variable_sorts.insert(named.clone(), sort.clone());
            }
        }
    }

    /// Could two known values be one? Another constructor says no; of one constructor,
    /// a slot BOTH write and know says no — a variable in a slot, on either side, says
    /// nothing, and is not looked up ([`Self::known_argument`]). One the call does not
    /// write is not known, and neither is a construction written by position against one
    /// written by name.
    fn agree(&self, head: &Known<'_>, call: &Known<'_>) -> bool {
        let slot = |h: &Rc<NodeOccurrence>, c: &Rc<NodeOccurrence>| {
            match (self.known(h), self.known(c)) {
                (Some(h), Some(c)) => self.agree(&h, &c),
                _ => true,
            }
        };
        match (head, call) {
            (Known::Number(h), Known::Number(c)) => h == c,
            (Known::Truth(h), Known::Truth(c)) => h == c,
            (Known::Built(hf, hpos, hnamed), Known::Built(cf, cpos, cnamed)) => {
                hf == cf
                    && (hpos.len() != cpos.len() || hpos.iter().zip(*cpos).all(|(h, c)| slot(h, c)))
                    && hnamed.iter().all(|(field, h)| {
                        self.field_of(cnamed, *field).is_none_or(|c| slot(h, c))
                    })
            }
            _ => false,
        }
    }

    /// What `occ` is known to be, where it is ([`Known`]).
    fn known<'a>(&self, occ: &'a Rc<NodeOccurrence>) -> Option<Known<'a>> {
        match occ.as_expr()? {
            Expr::Const(Literal::Float(f)) => Some(Known::Number(f.into_inner())),
            Expr::Const(Literal::Int(i)) => Some(Known::Number(*i as f64)),
            Expr::Const(Literal::Bool(b)) => Some(Known::Truth(*b)),
            Expr::Ref(name) | Expr::Ident(name) if self.is_construction(*name) => {
                Some(Known::Built(*name, &[], &[]))
            }
            _ => occ_as_fn(occ)
                .filter(|(functor, _, _)| self.is_construction(*functor))
                .map(|(functor, pos, named)| Known::Built(functor, pos, named)),
        }
    }

    /// Does `sym` build a value — a constructor of a sort, or an entity?
    fn is_construction(&self, sym: Symbol) -> bool {
        // A constructor's type face shares its declaration's fields but builds no value
        // (WI-20260902-JB6RS): a type in a data slot is not a construction.
        !sym.is_type_face()
            && (self.kb.entity_field_types(sym).is_some() || self.kb.is_constructor_symbol(sym))
    }

    /// The value `named` gives the field `field`, by the field's SHORT name: a head is
    /// materialized from a term and a call is an occurrence, and the two may qualify a
    /// field differently.
    fn field_of<'a>(
        &self,
        named: &'a [(Symbol, Rc<NodeOccurrence>)],
        field: Symbol,
    ) -> Option<&'a Rc<NodeOccurrence>> {
        let short = |sym: Symbol| self.kb.local_name_of(sym).rsplit('.').next();
        named
            .iter()
            .find(|(written, _)| short(*written) == short(field))
            .map(|(_, value)| value)
    }

    /// Bind a call to the FACT that answers it: each call-side DeBruijn
    /// var to the corresponding fact slot — literal → string binding,
    /// construction → entity_bindings (consumed by `field_access`
    /// lowering, and by what the variable selects later). A slot of the
    /// call that is no variable is the fact's, which is what selected the
    /// fact.
    fn bind_fact_call(
        &mut self,
        functor_qn: &str,
        fact: &Answer,
        call_args: &[Rc<NodeOccurrence>],
        bindings: &mut BTreeMap<String, String>,
    ) -> Result<(), SmtGenError> {
        // A VARIABLE in the fact's slot (`fact dflt(?who, 5.0)`) is every value there:
        // the call's argument is one of them, and nothing is bound. One the fact names
        // TWICE equates the call's arguments at the two, which is not written.
        let fact_vars: Vec<&Var> = fact
            .head_args
            .iter()
            .filter_map(|slot| match slot.as_expr() {
                Some(Expr::Var(var)) => Some(var),
                _ => None,
            })
            .collect();
        if let Some(twice) = (1..fact_vars.len()).find(|&at| fact_vars[..at].contains(&fact_vars[at])) {
            return Err(SmtGenError::new(format!(
                "the call of `{functor_qn}` is answered by a fact that names one variable in \
                 two slots ({:?}), which equates the call's arguments there: not written",
                fact_vars[twice]
            )));
        }
        for (at, (call_occ, fact_occ)) in call_args.iter().zip(fact.head_args.iter()).enumerate() {
            if matches!(fact_occ.as_expr(), Some(Expr::Var(_))) {
                continue;
            }
            let Some(Expr::Var(Var::DeBruijn(idx))) = call_occ.as_expr() else {
                // ADMITTED IS NOT EQUAL: a term over variables (`?k + 1`, `Vec3(x: ?a, …)`)
                // against the fact's slot is an equation this does not write, and a
                // fact so read would be a hypothesis left out. It was passed over as a
                // fact that did not match.
                if !self.occs_match(call_occ, fact_occ) {
                    return Err(SmtGenError::new(format!(
                        "the call of `{functor_qn}` is answered by a fact, and its argument \
                         {} is a term the fact's slot is not compared with: an argument \
                         read against a fact is a variable, or the fact's own value",
                        at + 1
                    )));
                }
                continue;
            };
            let synth = synthetic_var_name(*idx);
            match fact_occ.as_expr() {
                Some(Expr::Const(Literal::Float(f))) => {
                    self.bind_variable(synth, format_real(f.into_inner()), bindings);
                }
                Some(Expr::Const(Literal::Int(i))) => {
                    self.bind_variable(synth, format_real(*i as f64), bindings);
                }
                // Entity (Pose, Vec3, …) — defer until field_access reads it. And a
                // NULLARY CONSTRUCTOR (`Leader`): it has no SMT term
                // (WI-20261013-PR8SP), and the variable IS it — held as a construction
                // is, so what the variable selects later (a fact by its drone, a clause
                // by its head) it selects. It was passed over, and the variable left
                // bound to nothing.
                _ if self.known(fact_occ).is_some_and(|slot| matches!(slot, Known::Built(..))) => {
                    self.entity_bindings.insert(synth, Rc::clone(fact_occ));
                }
                // What a variable is not bound to: a string, a boolean, a big integer,
                // a name that is no constructor, a computed term. It was passed over
                // ("skip for v0"), the variable free in a body that says what it is.
                _ => {
                    return Err(SmtGenError::new(format!(
                        "the call of `{functor_qn}` is answered by a fact, and the fact's slot \
                         {} is a value the call's variable there is not bound to: a variable \
                         is bound to a number or to a construction",
                        at + 1
                    )))
                }
            }
        }
        Ok(())
    }

    /// Inline a rule call's body at the call site. `call_args` are
    /// the caller-side occurrences bound positionally to the callee's
    /// head DeBruijn vars. The callee's local DeBruijn indices are
    /// renamed into a per-call namespace so they don't collide with
    /// the caller's; entity-typed arguments propagate into the
    /// callee's entity_bindings.
    fn inline_rule_call(
        &mut self,
        callee_qn: &str,
        callee: &Answer,
        call_args: &[Rc<NodeOccurrence>],
        caller_bindings: &mut BTreeMap<String, String>,
    ) -> Result<(), SmtGenError> {
        let clause = &callee.clause;

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
        for (head_arg, call_arg) in callee.head_args.iter().zip(call_args.iter()) {
            // WI-20261013-1KF32 — A NUMBER IN THE HEAD MET BY A FREE VARIABLE OF THE CALL
            // BINDS IT, as a fact's slot does ([`Self::bind_fact_call`]; decided with the
            // user, 2026-10-14): the clause answers the call only where the variable is
            // that number. So a definition by cases written by its numbers (`rule mode(0,
            // ?r) :- …`, `rule mode(1, ?r) :- …`) called `mode(?k, ?r)` is a world for
            // each, `?k` the number of its clause. A variable bound to a computed term, and
            // a computed term, against a number are still refused ([`Self::bind_head_arg`]).
            if let (Some(Known::Number(in_head)), Some(free)) = (
                self.known(head_arg),
                self.free_variable(call_arg, caller_bindings),
            ) {
                self.bind_variable(free, format_real(in_head), caller_bindings);
                continue;
            }
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

        // WI-20261012-BR7P3 — the variables of its own, named apart from every variable
        // of the document before any goal of the body writes one.
        let own = self.name_own_variables(
            callee.head_args.iter().chain(&clause.body_nodes),
            &mut callee_str,
        )?;

        // Process the callee's body. We share the global
        // `assertions` / `field_consts` / `referenced_entities` /
        // `free_vars` accumulators (the inlined rule's facts and
        // assertions belong to the caller's SMT document), but we
        // give the callee its own bindings + entity_bindings so its
        // local DeBruijn indices stay isolated. After processing we
        // restore the caller's entity_bindings.
        let body_goals = clause.body_nodes.clone();
        let saved_ent = std::mem::take(&mut self.entity_bindings);
        self.entity_bindings = callee_ent;
        // WI-20261012-ZZ7PH — and its own SORTS: a head variable is of the sort of the
        // caller's variable it stands for, and of its own bound, which must agree; what
        // follows from those through the callee's goals is the callee's.
        let callee_sorts: BTreeMap<String, SmtSort> = head_caller
            .iter()
            .filter_map(|(head_idx, caller_synth)| {
                let sort = self.var_sorts.get(caller_synth)?;
                Some((synthetic_var_name(*head_idx), sort.clone()))
            })
            .collect();
        let saved_sorts = std::mem::replace(&mut self.var_sorts, callee_sorts);
        let mut local = callee_str;
        let mut err: Option<SmtGenError> = self
            .seed_bounds(clause)
            .and_then(|()| self.infer_var_sorts(&body_goals))
            .err();
        if err.is_none() {
            self.inlining
                .push(InlinedFrame::opened(callee_qn, call_args.len(), &local));
            for goal in &body_goals {
                if let Err(e) = self.process_body_goal(goal, &mut local) {
                    err = Some(e);
                    break;
                }
            }
            self.inlining.pop();
        }
        self.keep_own_variable_sorts(&own);
        self.var_sorts = saved_sorts;
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
        // arithmetic strings and entity_bindings. WI-20261014-FHEEK — a value is given
        // the caller's variable as any value is ([`Self::bind_variable`]), in the
        // CALLER's frame: the caller may have written the variable already, in a goal or
        // in what it defined another variable as, and a substitution here left that text
        // naming a variable the document no longer declares.
        for (head_idx, caller_synth) in head_caller {
            let head_synth = synthetic_var_name(head_idx);
            if let Some(value) = local.get(&head_synth) {
                // Skip the trivial forwarding entry — body never
                // overrode it, so there's nothing new to push back.
                let passed = caller_bindings.get(&caller_synth).unwrap_or(&caller_synth);
                if value != passed {
                    self.bind_variable(caller_synth.clone(), value.clone(), caller_bindings);
                }
            }
            if let Some(entity_occ) = final_ent.get(&head_synth) {
                self.entity_bindings
                    .insert(caller_synth, Rc::clone(entity_occ));
            }
        }
        Ok(())
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
        // A NUMBER in head position (`rule mode(0, ?r) :- …`, the base clause
        // `real_pose_at(0, ?drone, ?pose)`) is ground, as a nullary constructor is:
        // nothing to bind, and it must BE the call's — which is what selected this
        // clause where the call's is known ([`Self::admits`]). A call's free variable
        // or a computed term there is an equation this does not write, and says so
        // (WI-20261012-KF2SD, /code-review: the clause was selected by its number and
        // then refused as "head arg must be a De Bruijn var or a constructor"). A FREE
        // variable of the call there is bound to the number before this is asked
        // ([`Self::inline_rule_call`], WI-20261013-1KF32); one inside a construction is
        // not looked up ([`Self::known_argument`]), and is refused here.
        if let Some(Known::Number(in_head)) = self.known(head_arg) {
            return match self.known_argument(call_arg, caller_bindings) {
                Some(Known::Number(passed)) if passed == in_head => Ok(()),
                _ => Err(SmtGenError::new(format!(
                    "'{callee_qn}' has the number {} for an argument of its head, and the \
                     call's argument there is not known to be it: a computed term, or a \
                     variable defined as one, against a number in a head is an equation that \
                     is not written. Pass the number, a variable defined as it, or a variable \
                     nothing defines",
                    format_real(in_head)
                ))),
            };
        }

        // A nullary constructor CONSTANT in head position (`none`, spelled as a
        // bare `Ref`/`Ident` or an arg-less `Fn`) is ground — nothing to BIND, but
        // it must still MATCH the call (WI-687). The clause read is the one no
        // argument of the call RULES OUT ([`Self::answering_clause`]), and a call's
        // free variable rules out nothing, so a `none` head may still meet a call
        // that is not known to be `none` — and must fail LOUDLY, symmetric with the
        // `some(?0)` head direction, which errors at `resolve_call_ctor` / the functor
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
                let Some(cv) = self.field_of(cnamed, *hs) else {
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
            _ if occ_as_fn(call_arg).is_some_and(|(f, _, _)| self.is_construction(f)) => {
                // Concrete entity / constructor at the call site — expose it for
                // field_access on the callee side. WI-20261012-BR7P3 — CLOSED over the
                // caller's frame first: its variables are the caller's, and read in the
                // callee's frame by their indices they were the callee's — `fx(?p, ?r) :- ?r
                // = ?p.x` called `fx(P(x: ?a, y: 0.0), ?r)` read `?a` as `fx`'s own `?r`, and
                // the call said `r = r`.
                let closed = self.close_occ(call_arg, &self.entity_bindings, caller_bindings)?;
                callee_ent.insert(head_synth, closed);
            }
            // A field of a construction closed over its caller's frame ([`Self::close_occ`]):
            // the SMT text of what the caller passed there. It was passed over, and the
            // head's variable left bound to nothing.
            Some(Expr::Const(Literal::String(passed))) => {
                callee_str.insert(head_synth, passed.clone());
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
    fn translate_called_rule(
        &mut self,
        callee_qn: &str,
        callee: &Answer,
    ) -> Result<String, SmtGenError> {
        let clause = &callee.clause;
        // The head has the call's one argument, and the result is the variable there.
        let result_idx = match callee.head_args.first().and_then(|arg| arg.as_expr()) {
            Some(Expr::Var(Var::DeBruijn(i))) => *i,
            _ => {
                return Err(SmtGenError::new(format!(
                    "v0: called rule '{callee_qn}' head must be ?DeBruijn"
                )))
            }
        };
        // The callee's frame is its own, and so are its variables' sorts
        // (WI-20261012-ZZ7PH) — and its ENTITIES (WI-20261012-KF2SD, /code-review). The
        // caller's stayed installed, so the callee's variable of an index was "bound" to
        // whatever construction the caller's variable of that index held, which a
        // clause is now selected by: measured, `bound(?d) :- gain(?o, ?d)` called beside
        // an unrelated `?s = some(2.0)` read `gain` by its `some` clause for the free
        // `?o`. The same leak, the other way, handed the callee's entities back.
        //
        // WI-20261012-BR7P3 — and every variable of it, its result too, is its own: named
        // apart from the document's before the body is read ([`Self::name_own_variables`]).
        let mut local_bindings: BTreeMap<String, String> = BTreeMap::new();
        let own = self.name_own_variables(
            callee.head_args.iter().chain(&clause.body_nodes),
            &mut local_bindings,
        )?;
        let saved_sorts = std::mem::take(&mut self.var_sorts);
        let saved_entities = std::mem::take(&mut self.entity_bindings);
        self.inlining
            .push(InlinedFrame::opened(callee_qn, 1, &local_bindings));
        let walked = (|| {
            self.seed_bounds(clause)?;
            self.infer_var_sorts(&clause.body_nodes)?;
            for goal in &clause.body_nodes {
                self.process_body_goal(goal, &mut local_bindings)?;
            }
            Ok(())
        })();
        self.inlining.pop();
        self.keep_own_variable_sorts(&own);
        self.var_sorts = saved_sorts;
        self.entity_bindings = saved_entities;
        walked?;
        // The result is what the body gave it: a value, or — given one where the body
        // had written it already — the variable it was named, equated with the value. A
        // body that gives it none defines nothing.
        let result = synthetic_var_name(result_idx);
        let value = local_bindings.get(&result).ok_or_else(|| {
            SmtGenError::new(format!(
                "the result of '{callee_qn}' has no name in its frame, where every variable \
                 is named before its body is read"
            ))
        })?;
        let named = own
            .iter()
            .find(|(local, _)| *local == result)
            .map(|(_, named)| named);
        if named == Some(value) && !self.equated.contains(value) {
            return Err(SmtGenError::new(format!(
                "called rule '{callee_qn}' never bound its result var"
            )));
        }
        Ok(value.clone())
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
            // WI-20261012-BR7P3 — a variable nothing binds is the clause's own, and goes by
            // its index. In an inlined rule's frame every variable is bound, to the text
            // its caller passed or to a name of its own ([`Self::name_own_variables`]): by
            // its index it would be the clause's variable of that index.
            Some(Expr::Var(Var::DeBruijn(i))) => {
                let synth = synthetic_var_name(*i);
                if self.entity_bindings.contains_key(&synth) {
                    return Err(SmtGenError::new(format!(
                        "`?{synth}` is a construction, which has no SMT term: written as one it \
                         would be a variable nothing ties to it"
                    )));
                }
                match bindings.get(&synth) {
                    Some(bound) => Ok(bound.clone()),
                    None if self.inlining.is_empty() => Ok(synth),
                    None => Err(SmtGenError::new(format!(
                        "`?{synth}` of `{}`, read inlined, has no name in the document: every \
                         variable of an inlined rule is named when its frame is opened",
                        self.inlining.last().map_or("", |frame| frame.rule.as_str())
                    ))),
                }
            }
            Some(Expr::Var(other)) => match self.var_name(other) {
                // A variable of a stored fact's term that the reader of that fact named
                // (a `constraint` law's, WI-20261012-ZZ7PH).
                Some(named) => Ok(bindings.get(&named).cloned().unwrap_or(named)),
                None => Err(SmtGenError::new(format!(
                    "v0: expected DeBruijn var in expression, got {other:?}"
                ))),
            },
            Some(Expr::Ref(s)) | Some(Expr::Ident(s)) => {
                // A nullary operation of a law's spec, named bare (`zero`), at the
                // sort the law is lowered at.
                if let Some(constant) = self.nullary_constant(*s, None)? {
                    return Ok(constant);
                }
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
                let Some((functor, pos_args, named_args)) = occ_as_fn(occ) else {
                    return Err(SmtGenError::new(format!(
                        "v0: unhandled expression: {:?}",
                        occ.as_expr().map(std::mem::discriminant)
                    )));
                };
                let op = self.kb.qualified_name_of(functor);
                // WI-20261012-ZZ7PH — at a declared sort an operation is an
                // uninterpreted function, whatever row it has at a theory sort.
                if let Some((applied, _)) =
                    self.uninterpreted_call(functor, pos_args, named_args, None, bindings)?
                {
                    return Ok(applied);
                }
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
                        return Err(self
                            .unsorted_operand_refusal(functor, pos_args, named_args)
                            .unwrap_or_else(|| {
                                SmtGenError::new(format!("v0: unhandled arithmetic op '{op}'"))
                            }))
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
        let Some((functor, pos_args, named_args)) = occ_as_fn(occ) else {
            return Err(SmtGenError::new(format!(
                "v0: unhandled condition shape: {:?}",
                occ.as_expr().map(std::mem::discriminant)
            )));
        };
        let qn = self.kb.qualified_name_of(functor);
        // WI-20261012-ZZ7PH — a `Bool`-valued operation at a declared sort: the
        // carrier's own relation, `eq` and the comparisons included.
        if let Some((applied, sort)) =
            self.uninterpreted_call(functor, pos_args, named_args, None, bindings)?
        {
            if sort != SmtSort::Bool {
                return Err(SmtGenError::new(format!(
                    "`{qn}` is of sort {sort} where a condition stands"
                )));
            }
            return Ok(applied);
        }
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
        Err(self
            .unsorted_operand_refusal(functor, pos_args, named_args)
            .unwrap_or_else(|| {
                SmtGenError::new(format!(
                    "v0: unhandled condition functor '{qn}' (expected a relational op, \
                     `=`, or a Bool connective and/or/not)"
                ))
            }))
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
                //
                // WI-20261012-BR7P3 — EXCEPT A VARIABLE OF THE CLAUSE'S OWN FRAME, which no
                // inlined rule reads: its name in the document is its index's, so it closes
                // to that name. Inside an inlined rule every variable is bound on one of the
                // two channels — its head's from the call, its own named apart
                // ([`Self::name_own_variables`]) — and one that is not is the error above.
                if let Some(bound) = env.get(&synth) {
                    return Ok(Rc::clone(bound));
                }
                return match str_env.get(&synth) {
                    Some(smt) => Ok(scalar_param_occ(smt, occ.span, occ.owner)),
                    None if self.inlining.is_empty() => {
                        Ok(scalar_param_occ(&synth, occ.span, occ.owner))
                    }
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
                recv_type,
            } => Expr::Apply {
                functor: *functor,
                pos_args: self.close_all(pos_args, env, str_env)?,
                named_args: self.close_named(named_args, env, str_env)?,
                type_args: type_args.clone(),
                // WI-20260829-W6JH0: closing rewrites the CHILDREN; the call's own result
                // type is not one of them and rides through unchanged, exactly as
                // `type_args` does beside it.
                recv_type: recv_type.clone(),
            },
            // Proposal 055 — a nominal type value closes like the two shapes it
            // replaced: the BARE face was an `Expr::Ref` and passed through as a leaf,
            // the APPLIED face was an `Expr::Apply` and closed its children. Both are
            // this one arm (a bare one simply has no children). Without it a `@[simp]`
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
                recv_type,
                type_args,
            } => Expr::Constructor {
                name: *name,
                pos_args: self.close_all(pos_args, env, str_env)?,
                named_args: self.close_named(named_args, env, str_env)?,
                from_projection: *from_projection,
                recv_type: recv_type.clone(),
                type_args: type_args.clone(),
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
                type_args,
            } => Expr::DotApply {
                receiver: self.close_occ(receiver, env, str_env)?,
                name: *name,
                pos_args: self.close_all(pos_args, env, str_env)?,
                named_args: self.close_named(named_args, env, str_env)?,
                type_args: type_args.clone(),
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
    ///     `pos_args`/`named_args`, or a bracket, is a method call (returns `None`).
    fn as_field_access(&self, occ: &Rc<NodeOccurrence>) -> Option<(Rc<NodeOccurrence>, String)> {
        match occ.as_expr()? {
            Expr::DotApply {
                receiver,
                name,
                pos_args,
                named_args,
                type_args,
            } => {
                if !pos_args.is_empty() || !named_args.is_empty() || !type_args.is_empty() {
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
                if dt::is(op, dt::FIELD_ACCESS) {
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
        // An instance's head, so never a type face (WI-20260902-JB6RS).
        !sym.is_type_face() && self.kb.entity_field_types(sym).is_some()
    }

    /// Classify a rule's head for the `collect_rule` dispatcher. The
    /// classification mirrors what `process_body_goal` would do if
    /// asked to translate the head as a goal: predicate-like heads
    /// (`gte/lte/eq/...` or entity destructures) become the
    /// conclusion under proposal 032; function-like heads
    /// (`rule_qn(?result)`) drive upper-bound mode.
    fn classify_head(&self, head: anthill_core::kb::term::TermId) -> HeadShape {
        let term = self.kb.get_term(head);
        let (functor, pos_args, named_args_empty) = match term {
            Term::Bottom => return HeadShape::Bottom,
            Term::Fn {
                functor,
                pos_args,
                named_args,
            } => (*functor, pos_args.clone(), named_args.is_empty()),
            // WI-20260902-CZJ2N — A NULLARY HEAD IS STORED BARE, so `rule status_ok :-
            // …` arrives as `Term::Ref` and not as an argument-less `Term::Fn`. Without
            // this arm it fell to `Unsupported`, which the caller turns into a HARD
            // `SmtGenError` — so an obligation whose rule (or any rule it chases) has a
            // nullary head aborted SMT emission entirely, and the 0-arg arm below became
            // dead code. `Term::Ident` is included for the same reason
            // `head_arg_count` includes it: the two spellings are one head.
            Term::Ref(s) | Term::Ident(s) => (*s, smallvec::SmallVec::new(), true),
            other => {
                return HeadShape::Unsupported(format!(
                    "rule head must be an application or Bottom, got {other:?}"
                ))
            }
        };
        let qn = self.kb.qualified_name_of(functor);
        // The connective's own address, whole: `<=>` names no functor a source can
        // write (`desugar_target::NO_SURFACE_FUNCTOR`), so a short `unify` is another
        // symbol and is not asked about here.
        if qn == "anthill.kernel.unify" && pos_args.len() == 2 {
            return HeadShape::Equation;
        }
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
        // WI-20261012-ZZ7PH — a head of SEVERAL VARIABLES, `rule p(?a: T, ?b: T) :- …`:
        // the rule's parameters, and no conclusion. A bound is written on a head variable
        // and nowhere else, so this is the one way a violation rule gives two variables a
        // sort; it was "rule head shape not supported". The one-variable head is read
        // above, as the result an obligation bounds — and in a satisfiability check, where
        // the body does not bind it, as a parameter too (`collect_rule_clause`).
        if named_args_empty
            && pos_args
                .iter()
                .all(|arg| matches!(self.kb.get_term(*arg), Term::Var(Var::DeBruijn(_))))
        {
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
            // WI-20261012-KF2SD (/code-review) — ONE SUCH FACT, OR REFUSED. "For v0 we
            // expect at most one fact per entity" was a comment, and the loop broke at
            // the first: an entity of several facts was read as its first, whichever
            // the premise's own slots named. Measured: `fact Limit(cap: 5.0)`, `fact
            // Limit(cap: -1.0)` proved `gte(?c, 0.0) :- Limit(cap: ?c)`; and over
            // `Mode(kind: 1.0, cap: 5.0)`, `Mode(kind: 2.0, cap: -1.0)` the premise
            // `Mode(kind: 2.0, cap: ?c)` proved it with the cap of kind 1 — a slot
            // that is no variable is not read, and a field's constant is one for the
            // document. It is the call of several facts in an entity's spelling, and a
            // proof's document reads it as one: a world for each fact
            // ([`Self::read_entity_row`], WI-20261013-1KF32). What reaches this with
            // several is a document that is not split by them.
            let rows = self.entity_rows(&entity_qn)?;
            if rows.len() > 1 {
                return Err(SmtGenError::new(format!(
                    "the entity `{entity_qn}` has several facts, and a premise here reads its \
                     fields off ONE: it would be the first, whichever fact the premise's own \
                     slots name. A proof's document reads each fact in a world of its own \
                     (WI-20261013-1KF32); a cited lemma's lift and an obligation are not \
                     split by them"
                )));
            }
            let Some(&head) = rows.first() else {
                continue;
            };
            let Term::Fn { named_args, .. } = self.kb.get_term(head) else {
                unreachable!("`entity_rows` keeps a row that is an application");
            };
            for (field_sym, val_term) in named_args {
                let field_name = self.kb.local_name_of(*field_sym).to_string();
                let const_name = sanitize_smt_id(&field_name);
                if !self.field_consts.contains_key(&const_name) {
                    continue;
                }
                // WI-20261013-1KF32 (/code-review) — A FIELD THAT IS NO NUMBER IS REFUSED,
                // and not left at the 0.0 its constant was made with: `fact Lim(cap: ?any)`
                // was `cap` = 0.0, and proved `gte(?c, 0.0) :- Lim(cap: ?c)`. A proof's
                // document reads such a fact by its row ([`Self::read_by_rows`]); what
                // reaches this is a lift or an obligation.
                let Some(v) = literal_as_real(self.kb.get_term(*val_term)) else {
                    return Err(SmtGenError::new(format!(
                        "the premise `{entity_qn}` reads the field `{field_name}` of the entity's \
                         fact, whose value there is no number, as a constant of the document"
                    )));
                };
                self.field_consts.insert(const_name, v);
            }
        }
        Ok(())
    }

    /// THE FACTS OF AN ENTITY, by its qualified name: each a row of its fields. A bodied
    /// rule for it is refused (WI-772).
    ///
    /// EVERY ROW (WI-20261013-1KF32, /code-review). Only a row with a field that is a number
    /// was kept, so a row whose field is a variable — every value there — was no row:
    /// measured on 79a6703f, `fact Lim(cap: ?any)` beside `fact Lim(cap: 5.0)` was the one
    /// fact `cap` = 5, and alone it was `cap` = 0.0, the default of a constant no row set;
    /// both proved `gte(?c, 0.0) :- Lim(cap: ?c)`, which `Lim(cap: -1.0)` refutes. (WI-515:
    /// the entity-declaration row with abstract field types is no longer asserted.)
    fn entity_rows(&self, entity_qn: &str) -> Result<Vec<TermId>, SmtGenError> {
        let Some(sym) = self.kb.try_resolve_symbol(entity_qn) else {
            return Ok(Vec::new());
        };
        let candidates = self
            .kb
            .read_facts(sym, &[], BodiedRulePolicy::Refuse)
            .map_err(|e| match e {
                ExtentReadError::BodiedRule { .. } => SmtGenError::new(format!(
                    "bodied rule for referenced entity `{entity_qn}` refused: {e} — \
                     guarded field values would enter the SMT encoding unconditionally (WI-772)"
                )),
                _ => SmtGenError::new(format!("referenced entity `{entity_qn}` read failed: {e}")),
            })?;
        let mut rows = Vec::new();
        for row in candidates {
            let Value::Term { id: head, .. } = row else {
                return Err(SmtGenError::new(format!(
                    "referenced entity `{entity_qn}` has a non-term fact row; \
                     SMT v0 requires term-carried numeric fields"
                )));
            };
            if matches!(self.kb.get_term(head), Term::Fn { .. }) {
                rows.push(head);
            }
        }
        Ok(rows)
    }

    /// The value `row`, a fact of an entity, gives the field `slot` — by its short name, as
    /// a premise and a fact may qualify a field differently ([`Self::field_of`]).
    fn row_field(&self, row: TermId, slot: Symbol) -> Option<TermId> {
        let short = |sym: Symbol| self.kb.local_name_of(sym).rsplit('.').next().map(str::to_owned);
        let Term::Fn { named_args, .. } = self.kb.get_term(row) else {
            return None;
        };
        named_args
            .iter()
            .find(|(name, _)| short(*name) == short(slot))
            .map(|(_, value)| *value)
    }

    /// Is a premise of the entity read by its rows, and not by the constants of its one
    /// fact? Where it has several — a world for each — and where its one fact gives a
    /// field the premise binds something that is no number, which the constant would be
    /// 0.0 for.
    fn read_by_rows(&self, rows: &[TermId], slots: &[(Symbol, Rc<NodeOccurrence>)]) -> bool {
        match rows {
            [] => false,
            [row] => slots.iter().any(|(slot, occ)| {
                matches!(occ.as_expr(), Some(Expr::Var(Var::DeBruijn(_))))
                    && self
                        .row_field(*row, *slot)
                        .is_none_or(|value| literal_as_real(self.kb.get_term(value)).is_none())
            }),
            _ => true,
        }
    }

    /// WI-20261013-1KF32 — AN ENTITY PREMISE READ BY THE ENTITY'S ROWS (`Limit(cap: ?c)` over
    /// `fact Limit(cap: 5.0)`, `fact Limit(cap: -1.0)`): the rows its slots admit, and,
    /// where several are left, a choice point among them. In the world being read each
    /// variable slot is the chosen row's field ([`Self::bind_variable`]), and a field that
    /// is a variable is every value — the slot's variable is free there. A field of the
    /// entity is no constant of the document here — `cap` would be one name for every
    /// row's — so the one-fact reading (`(define-fun cap …)`) is not this one's.
    ///
    /// ADMITTED: a slot known to be a number rules out a row whose field is another, and a
    /// variable written in two slots rules out a row whose two fields are two numbers
    /// (/code-review: `M(kind: ?x, cap: ?x)` had a world for a row of kind 1 and cap 5).
    /// A slot that is neither a variable nor a number — a computed term, a construction —
    /// is an equation that is not written, and is refused: it was passed over, and every
    /// row admitted.
    fn read_entity_row(
        &mut self,
        entity_qn: &str,
        rows: &[TermId],
        slots: &[(Symbol, Rc<NodeOccurrence>)],
        bindings: &mut BTreeMap<String, String>,
    ) -> Result<(), SmtGenError> {
        let kb = self.kb;
        if let Some((slot, _)) = slots.iter().find(|(_, occ)| {
            !matches!(occ.as_expr(), Some(Expr::Var(_)))
                && !matches!(self.known_argument(occ, bindings), Some(Known::Number(_)))
        }) {
            return Err(SmtGenError::new(format!(
                "the premise `{entity_qn}` gives its field `{}` a value that is neither a \
                 variable nor a number, which the entity's facts are not compared with: an \
                 equation that is not written",
                kb.local_name_of(*slot)
            )));
        }
        let number = |row: TermId, slot: Symbol| {
            self.row_field(row, slot)
                .and_then(|value| literal_as_real(kb.get_term(value)))
        };
        let admitted: Vec<TermId> = rows
            .iter()
            .copied()
            .filter(|&row| {
                let mut met: BTreeMap<u32, f64> = BTreeMap::new();
                slots.iter().all(|(slot, occ)| {
                    let Some(field) = number(row, *slot) else {
                        return true;
                    };
                    match (self.known_argument(occ, bindings), occ.as_expr()) {
                        (Some(Known::Number(premise)), _) => premise == field,
                        (_, Some(Expr::Var(Var::DeBruijn(index)))) => {
                            *met.entry(*index).or_insert(field) == field
                        }
                        _ => true,
                    }
                })
            })
            .collect();
        let pick = match admitted.len() {
            0 => {
                return Err(SmtGenError::new(format!(
                    "the premise `{entity_qn}` is answered by none of the entity's {} facts: \
                     each has a field that is another number than the premise's slot",
                    rows.len()
                )))
            }
            1 => 0,
            several => self.choose(
                several,
                "fact",
                || format!("the entity `{entity_qn}` ({several} facts)"),
                || unreachable!("asked only where the document is split by choices"),
            )?,
        };
        let row = admitted[pick];
        for (slot, occ) in slots {
            // A number selected the row, above; `?` is every value.
            let Some(Expr::Var(Var::DeBruijn(index))) = occ.as_expr() else {
                continue;
            };
            let field_name = kb.local_name_of(*slot);
            let Some(value) = self.row_field(row, *slot) else {
                return Err(SmtGenError::new(format!(
                    "the premise `{entity_qn}` reads the field `{field_name}`, which a fact of \
                     the entity does not give"
                )));
            };
            match kb.get_term(value) {
                Term::Var(_) => {} // every value: the variable is free in this world
                term => {
                    let Some(number) = literal_as_real(term) else {
                        return Err(SmtGenError::new(format!(
                            "the premise `{entity_qn}` reads the field `{field_name}` of a fact \
                             whose value there is no number, which a variable is not bound to"
                        )));
                    };
                    self.bind_variable(synthetic_var_name(*index), format_real(number), bindings);
                }
            }
        }
        Ok(())
    }

    /// The logic the document is checked under ([`check_logic`]).
    fn logic_for(&self, config: &ProofConfig, default: &str) -> String {
        check_logic(config, default, &self.declarations)
    }

    fn render_upper_bound_with(&self, obligation: &Obligation, config: &ProofConfig) -> String {
        let logic = self.logic_for(config, "QF_LRA");
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
        self.declarations.render(&mut out);

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
        // Body equations bound the result vars; emit them as
        // define-funs so subsequent assertions can reference them.
        // For satisfiability mode we don't have a single result var
        // but intermediate bindings still matter.
        let mut hypotheses = String::new();
        if !self.body_smtlib.is_empty() {
            hypotheses.push_str(&self.body_smtlib);
            hypotheses.push_str("\n\n");
        }
        for assertion in &self.assertions {
            hypotheses.push_str(&format!("(assert {assertion})\n"));
        }
        // Conclusion clauses (from the `-:` separator) are NEGATED
        // for the discharge: prove `body ∧ ¬conclusion` unsat ⇒
        // `body ⇒ conclusion`. AND-conjoined into a single
        // negation so the verdict cleanly mirrors the lemma's
        // theorem statement.
        if let Some(conclusion) = self.negated_conclusion() {
            hypotheses.push_str("; Negated conclusion (from `-:` clause).\n");
            hypotheses.push_str(&format!("(assert {conclusion})\n"));
        }
        render_check(
            rule_qn,
            config,
            CheckParts {
                note: None,
                declarations: &self.declarations,
                uses_abs: self.uses_abs,
                field_consts: self.field_consts.iter().map(|(n, v)| (n.as_str(), *v)).collect(),
                // Free vars (`?d_prev`, `?step`, etc. that appear in
                // assertions but aren't bound by an `=` clause) become
                // existentially-quantified inputs to the satisfiability
                // check — declared as global consts so `(check-sat)`
                // picks values for them if any exist. Each at the sort its bound or a
                // signature gave it, and a `Real` where neither did (WI-20261012-ZZ7PH).
                free: self
                    .free_vars
                    .iter()
                    .map(|v| (v.as_str(), self.var_sorts.get(v).unwrap_or(&SmtSort::Real)))
                    .collect(),
                trig_args: &self.trig_args,
                hypotheses,
            },
        )
    }

    /// `(not C)` of the conclusion, its goals conjoined; `None` where the rule has none.
    fn negated_conclusion(&self) -> Option<String> {
        match self.conclusion_assertions.as_slice() {
            [] => None,
            [one] => Some(format!("(not {one})")),
            several => Some(format!("(not (and {}))", several.join(" "))),
        }
    }
}

/// What a satisfiability check's document declares and asserts, of one world or of
/// several ([`render_check`]).
struct CheckParts<'a> {
    /// A comment of the header's, after what every check's says.
    note: Option<String>,
    declarations: &'a Declarations,
    uses_abs: bool,
    field_consts: Vec<(&'a str, f64)>,
    free: Vec<(&'a str, &'a SmtSort)>,
    trig_args: &'a BTreeSet<String>,
    /// What stands between the cited lemmas and `(check-sat)`: the body and the negated
    /// conclusion.
    hypotheses: String,
}

/// THE DOCUMENT OF A SATISFIABILITY CHECK, from what one world or several declare and
/// assert — one renderer, so a document of several worlds has the preamble a document of
/// one has (WI-20261013-1KF32, /code-review).
fn render_check(rule_qn: &str, config: &ProofConfig, parts: CheckParts<'_>) -> String {
    // `LRA` is the default for satisfiability mode (handles `abs`
    // via the standard if-then-else encoding Z3 applies).
    let logic = check_logic(config, "LRA", parts.declarations);
    let mut out = String::new();
    out.push_str(&format!(
        "; Generated by anthill-smt-gen — satisfiability check for rule {rule_qn}.\n"
    ));
    out.push_str("; `unsat` ⇒ rule body has no solution ⇒ encoded property holds.\n");
    if let Some(note) = &parts.note {
        out.push_str(note);
    }
    if let Some(t) = config.timeout_ms {
        out.push_str(&format!("(set-option :timeout {t})\n"));
    }
    emit_outcome_options(&mut out, config);
    out.push_str(&format!("(set-logic {logic})\n\n"));

    emit_abs_prelude(&mut out, parts.uses_abs, config);
    parts.declarations.render(&mut out);
    for (name, value) in &parts.field_consts {
        out.push_str(&format!(
            "(define-fun {name} () Real {})\n",
            format_real(*value)
        ));
    }
    out.push('\n');
    for (name, sort) in &parts.free {
        out.push_str(&format!("(declare-const {name} {sort})\n"));
    }
    out.push('\n');
    emit_trig_prelude(&mut out, parts.trig_args);
    emit_assumptions(&mut out, config);
    out.push_str(&parts.hypotheses);
    match &config.tactic_expr {
        Some(expr) => out.push_str(&format!("\n(check-sat-using {expr})\n")),
        None => out.push_str("\n(check-sat)\n"),
    }
    emit_outcome_getters(&mut out, config);
    out
}

/// The logic a document is checked under: the one the proof wrote, or `default`, and what
/// the document needs beyond it ([`document_logic`]).
fn check_logic(config: &ProofConfig, default: &str, declarations: &Declarations) -> String {
    let quantified = config
        .laws
        .iter()
        .chain(&config.assumptions)
        .any(|hypothesis| hypothesis.contains("(forall "));
    document_logic(
        config.logic.as_deref().unwrap_or(default),
        declarations,
        quantified,
    )
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
            .laws
            .iter()
            .chain(&config.assumptions)
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
    // WI-20261012-ZZ7PH — the laws of the requirements the proof stands under: each
    // already a whole `(assert (forall …))`.
    if !config.laws.is_empty() {
        out.push_str("; Laws of the specs the enclosing scopes require.\n");
        for law in &config.laws {
            out.push_str(law);
            out.push('\n');
        }
        out.push('\n');
    }
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

/// How many variables the frame of `clause` has, whose head is `head`: one past the
/// greatest index its head, its body, its bounds and its type parameters name. The
/// clause's own variables are `var_0` to `var_<size - 1>` in its document, and a
/// variable of a rule read inlined into it is named past them
/// ([`Emitter::name_own_variables`]).
fn frame_size(kb: &KnowledgeBase, clause: &ProgramClause, head: TermId) -> u32 {
    let head = materialize_from_handle(kb, head);
    debruijn_vars_of(std::iter::once(&head).chain(&clause.body_nodes))
        .into_iter()
        .chain(clause.type_bounds.iter().map(|(index, _)| *index))
        .chain(clause.frame_type_params.iter().map(|(index, _)| *index))
        .map(|index| index + 1)
        .chain(std::iter::once(clause.shared_arity))
        .max()
        .unwrap_or(0)
}

/// Does some SMT text a closed construction carries in its fields, at any depth
/// ([`scalar_param_occ`]), say `holds` of itself?
fn any_fragment(occ: &Rc<NodeOccurrence>, holds: &impl Fn(&str) -> bool) -> bool {
    match occ.as_expr() {
        Some(Expr::Const(Literal::String(text))) => holds(text),
        Some(expr) => {
            let mut found = false;
            for_each_child(expr, |child| found = found || any_fragment(child, holds));
            found
        }
        None => false,
    }
}

/// The clause variables `occs` name, at any depth, by frame index: each once, in the
/// order they are first met.
fn debruijn_vars_of<'a>(occs: impl IntoIterator<Item = &'a Rc<NodeOccurrence>>) -> Vec<u32> {
    fn walk(occ: &Rc<NodeOccurrence>, met: &mut Vec<u32>) {
        match occ.as_expr() {
            Some(Expr::Var(Var::DeBruijn(index))) => {
                if !met.contains(index) {
                    met.push(*index);
                }
            }
            Some(expr) => for_each_child(expr, |child| walk(child, met)),
            None => {}
        }
    }
    let mut met = Vec::new();
    for occ in occs {
        walk(occ, &mut met);
    }
    met
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
/// value `inline_rule_call` threaded into the callee string map: already
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
    // BOTH SPELLINGS, and the KERNEL one is not a second-best (WI-20260825-P9Y67).
    // `not`/`or`/`and` are POSITION-DIRECTED (kernel §6.6): a goal means the resolver
    // primitive, a value expression means the dispatched `Bool` op. A CONDITION is a
    // value — but it sits in a rule body's data slot, and the loader leaves a data
    // slot's spelling alone on purpose, because a term's spelling is its identity and
    // it cannot tell a condition from a reified goal being STORED (`fact
    // holdsN(not(true))`). Rewriting there was tried and regressed exactly that: the
    // rule body stopped matching the fact, exit 0, no diagnostic.
    //
    // So the position knowledge belongs HERE, at a consumer that knows what it is
    // reading. `translate_condition` is only ever called on a condition, so the two
    // spellings denote one function at this site and both must lower. Before
    // WI-20260825-KD9SW/P9Y67 gave operators an address, a rule body reached the
    // `Bool` row only when the author had written `import anthill.prelude.Bool.{not}`
    // and the import CAPTURED the operator — so this table's coverage was an accident
    // of the fixture's imports, and `wi680_ite_lowering_test` is what made that
    // visible when the capture went away.
    ("anthill.kernel.and", SmtBuiltin::BoolConn("and")),
    ("anthill.kernel.or", SmtBuiltin::BoolConn("or")),
    ("anthill.kernel.not", SmtBuiltin::BoolConn("not")),
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
#[derive(Debug, Clone)]
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

/// The number an SMT term IS, where it is one as [`format_real`] writes it: digits and
/// a point, or `(- <that>)`. Anything else — a variable's name, a field's constant, a
/// compound — is no number here, whatever a parser of floats would make of its text.
fn numeral(term: &str) -> Option<f64> {
    if let Some(negated) = term.strip_prefix("(- ").and_then(|rest| rest.strip_suffix(')')) {
        return numeral(negated).map(|value| -value);
    }
    let written = !term.is_empty() && term.bytes().all(|b| b.is_ascii_digit() || b == b'.');
    if written {
        term.parse().ok()
    } else {
        None
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

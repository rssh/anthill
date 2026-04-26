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
    let mut emitter = Emitter::new(kb);
    emitter.collect_rule(&obligation.rule_qn)?;
    emitter.collect_facts_for_referenced_entities();
    Ok(emitter.render(obligation))
}

// ── Implementation ──────────────────────────────────────────────────

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
    result_var: String,
}

impl<'kb> Emitter<'kb> {
    fn new(kb: &'kb KnowledgeBase) -> Self {
        Self {
            kb,
            field_consts: BTreeMap::new(),
            referenced_entities: BTreeSet::new(),
            body_smtlib: String::new(),
            result_var: String::new(),
        }
    }

    /// Find the rule by qualified name. Walk its body and produce
    /// the SMT-LIB equation that defines the head's result variable.
    fn collect_rule(&mut self, rule_qn: &str) -> Result<(), SmtGenError> {
        let sym = self.kb.try_resolve_symbol(rule_qn)
            .ok_or_else(|| SmtGenError::new(format!("rule '{rule_qn}' not found")))?;
        let rules = self.kb.by_functor(sym);
        let rid = *rules.first().ok_or_else(||
            SmtGenError::new(format!("rule '{rule_qn}' has no clauses")))?;

        // Loaded rules use de Bruijn-indexed variables (the parser's
        // `?name` form is interned to a position; the user-given
        // name is dropped). Each index gets a synthetic SMT
        // identifier `var_<i>` — unreadable but unambiguous, and Z3
        // only sees consts and ops so the names don't matter for
        // soundness.
        let head = self.kb.rule_head(rid);
        let result_idx = match self.kb.get_term(head) {
            Term::Fn { pos_args, .. } if pos_args.len() == 1 => {
                match self.kb.get_term(pos_args[0]) {
                    Term::Var(Var::DeBruijn(i)) => *i,
                    other => return Err(SmtGenError::new(format!(
                        "v0: rule head's first pos_arg must be a DeBruijn var, got {other:?}"))),
                }
            }
            _ => return Err(SmtGenError::new(
                "v0: rule head must have exactly one positional arg (the result)")),
        };
        self.result_var = synthetic_var_name(result_idx);

        // Walk the body. Two clause shapes we accept:
        //   <Entity>(field: ?var, ...) — destructure a fact's fields
        //                               into local SMT consts
        //   ?var = <arith>             — bind ?var to an SMT term
        let body = self.kb.rule_body(rid);
        let mut local_bindings: BTreeMap<String, String> = BTreeMap::new();
        for goal in body {
            self.process_body_goal(*goal, &mut local_bindings)?;
        }

        let result_smt = local_bindings.get(&self.result_var).ok_or_else(||
            SmtGenError::new(format!(
                "rule body never bound the result variable '?{}'",
                self.result_var)))?;
        self.body_smtlib = format!(
            "(define-fun {} () Real {})",
            sanitize_smt_id(&self.result_var),
            result_smt);
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
        // time. The loader treats `=` in goal position as
        // `anthill.prelude.Eq.eq(lhs, rhs)`, so we recognise that
        // functor (and its short forms) too.
        if qn == "=" || qn == "anthill.prelude.Eq.eq"
            || self.kb.resolve_sym(*functor) == "=" || self.kb.resolve_sym(*functor) == "eq"
        {
            if pos_args.len() != 2 {
                return Err(SmtGenError::new(format!(
                    "= goal: expected 2 pos_args, got {}", pos_args.len())));
            }
            let lhs = self.kb.get_term(pos_args[0]);
            let rhs_smt = self.translate_expr(pos_args[1], bindings)?;
            let lhs_idx = match lhs {
                Term::Var(Var::DeBruijn(i)) => *i,
                _ => return Err(SmtGenError::new(format!(
                    "v0: = goal's LHS must be a DeBruijn var, got {lhs:?}"))),
            };
            bindings.insert(synthetic_var_name(lhs_idx), rhs_smt);
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

        // Rule call: `<rule_qn>(?result_var)` — chase the dependency.
        // We accept exactly one positional arg (the result binding),
        // matching the same v0 shape we accept for the obligation's
        // own rule head. The called rule is translated against a
        // FRESH local-bindings map (so its own intermediate
        // `?var = ...` equations don't collide with ours), and its
        // body's facts / referenced entities accumulate into our
        // own `field_consts` and `referenced_entities`.
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

        Err(SmtGenError::new(format!(
            "v0: unhandled body goal functor '{qn}'")))
    }

    /// Recursively translate a *called* rule's body to a single
    /// SMT-LIB expression — the rule's result, fully inlined. The
    /// caller binds its rule-call goal's pos arg to this expression
    /// so subsequent uses of the variable substitute it directly.
    /// Each called rule's body uses its own DeBruijn indices, so
    /// fresh local bindings don't collide with the caller's.
    fn translate_called_rule(&mut self, callee_qn: &str) -> Result<String, SmtGenError> {
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
    /// substitutes already-defined locals inline.
    fn translate_expr(
        &self,
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

    /// True if the symbol resolves to an entity declaration.
    fn is_known_entity(&self, sym: anthill_core::intern::Symbol) -> bool {
        self.kb.entity_field_types(sym).is_some()
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

    fn render(&self, obligation: &Obligation) -> String {
        let mut out = String::new();
        out.push_str(&format!(
            "; Generated by anthill-smt-gen for obligation {}.\n",
            obligation.rule_qn));
        out.push_str("; Logic: QF_LRA (quantifier-free linear real arithmetic).\n");
        out.push_str("(set-logic QF_LRA)\n\n");

        for (name, value) in &self.field_consts {
            out.push_str(&format!("(define-fun {name} () Real {})\n", format_real(*value)));
        }
        out.push('\n');

        out.push_str(&self.body_smtlib);
        out.push_str("\n\n");

        out.push_str(&format!(
            "; Obligation: {} <= {}\n",
            self.result_var, obligation.upper_bound));
        out.push_str(&format!(
            "(assert (not (<= {} {})))\n",
            sanitize_smt_id(&self.result_var),
            format_real(obligation.upper_bound)));
        out.push_str("(check-sat)\n");
        out
    }
}

/// Synthetic SMT identifier for a de Bruijn-indexed variable. The
/// loaded rule has dropped the user-given names, so we use the index
/// directly. Output is deterministic and collision-free with field
/// names (which never start with `var_<digit>`).
fn synthetic_var_name(idx: u32) -> String {
    format!("var_{idx}")
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

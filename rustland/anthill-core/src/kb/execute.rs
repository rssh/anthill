//! Value-integrated KB query execution (proposal 026.1 §Query-lowering at execute).
//!
//! This module is the **input boundary** between runtime `Value`s and the
//! resolver's `TermId`-based goals. A reified `LogicalQuery` (expressed as
//! a `Value` tree of `pattern_query`, `conjunction`, ... constructors) is
//! lowered to a list of goal `TermId`s and dispatched through the existing
//! `SearchStream`. Answers come back with `Value`-typed bindings —
//! `Substitution::lookup` surfaces the raw `Value`.
//!
//! `alloc_from_value` is the sole place at which a non-`Term`-variant
//! `Value` is hash-consed into the `TermStore`. All other call sites in
//! the resolver consume `Value` via the lineage-preserving `TermView`
//! abstraction.
//!
//! Scope: the KB-side API lives here. The matching eval builtin under
//! `anthill.reflect.KB.execute` needs a `Value::Stream` handle wrapping
//! a `SearchStream`, which depends on the M4 stream arena — that lives
//! in the `LogicalStream` milestone, not here.

use smallvec::SmallVec;

use crate::eval::value::Value;
use crate::intern::Symbol;

use super::resolve::{ResolveConfig, SearchStream};
use super::term::{Literal, Term, TermId};
use super::KnowledgeBase;

/// Reason a `Value` could not be lowered into a KB query.
#[derive(Clone, Debug)]
pub enum LowerError {
    /// A `Value` variant with no `TermId` equivalent reached
    /// `alloc_from_value` (e.g. `Closure`, `Stream`, `Lazy`, `Unit`).
    UnsupportedVariant(&'static str),
    /// The `Value` passed to `lower_query` is not a `LogicalQuery` entity
    /// (e.g. a bare literal or an entity whose functor isn't one of the
    /// constructors declared in `anthill.reflect.LogicalQuery`).
    NotALogicalQuery { got: String },
    /// A `LogicalQuery` constructor was recognized but its payload is
    /// missing a required named argument.
    MissingField { entity: &'static str, field: &'static str },
    /// `sort_query(sort_name)` was called with a `String` that doesn't
    /// resolve to any defined sort symbol.
    UnknownSort(String),
    /// A constructor in `LogicalQuery` hasn't been wired through to the
    /// resolver yet. Kept separate from `UnsupportedVariant` so call sites
    /// can distinguish "design hole" from "garbage input".
    NotYetImplemented(&'static str),
}

impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LowerError::UnsupportedVariant(v) =>
                write!(f, "cannot lower Value::{} into a KB term", v),
            LowerError::NotALogicalQuery { got } =>
                write!(f, "expected a LogicalQuery entity, got {}", got),
            LowerError::MissingField { entity, field } =>
                write!(f, "LogicalQuery::{} missing field `{}`", entity, field),
            LowerError::UnknownSort(name) =>
                write!(f, "sort_query: unknown sort `{}`", name),
            LowerError::NotYetImplemented(what) =>
                write!(f, "LogicalQuery lowering not yet implemented: {}", what),
        }
    }
}

impl std::error::Error for LowerError {}

// ── Resolved LogicalQuery constructor symbols ──────────────────

/// Cached `Symbol`s for every `LogicalQuery` entity, resolved once per
/// `lower_query` call. `Option<Symbol>` so a partial KB (test harness
/// without reflect loaded) still works — an unresolved constructor just
/// can't appear in a query. Field-name symbols are unconditionally
/// interned at resolve time, since interning is idempotent.
///
/// Several entity slots (quantifiers, aggregations) and their field keys
/// are resolved here so the loop below can `Some(functor) ==` against
/// them, even though their current codepath is a [`LowerError::NotYetImplemented`]
/// exit — wiring them up now keeps the later activation diff small.
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub(crate) struct LogicalQuerySymbols {
    pub empty_query: Option<Symbol>,
    pub pattern_query: Option<Symbol>,
    pub sort_query: Option<Symbol>,
    pub conjunction: Option<Symbol>,
    pub disjunction: Option<Symbol>,
    pub negation: Option<Symbol>,
    pub guarded: Option<Symbol>,
    pub projected: Option<Symbol>,
    pub limited: Option<Symbol>,
    pub forall_q: Option<Symbol>,
    pub some_q: Option<Symbol>,
    pub one_q: Option<Symbol>,
    pub lone_q: Option<Symbol>,
    pub no_q: Option<Symbol>,
    pub count_q: Option<Symbol>,
    pub sum_q: Option<Symbol>,
    pub min_q: Option<Symbol>,
    pub max_q: Option<Symbol>,

    // Field keys used by LogicalQuery payloads.
    pub term: Symbol,
    pub sort_name: Symbol,
    pub left: Symbol,
    pub right: Symbol,
    pub query: Symbol,
    pub condition: Symbol,
    pub count: Symbol,
    pub vars: Symbol,
    pub var: Symbol,
    pub body: Symbol,

    // `is_entity_of` — synthesized by `sort_query`.
    pub is_entity_of: Option<Symbol>,
    // `not` — synthesized by `negation`.
    pub not: Option<Symbol>,
    // `anthill.kernel.or` — synthesized by `disjunction` (proposal 033).
    pub or: Option<Symbol>,
}

impl LogicalQuerySymbols {
    pub(crate) fn resolve(kb: &mut KnowledgeBase) -> Self {
        let r = |kb: &KnowledgeBase, q: &str| kb.try_resolve_symbol(q);
        Self {
            empty_query: r(kb, "anthill.reflect.LogicalQuery.empty_query"),
            pattern_query: r(kb, "anthill.reflect.LogicalQuery.pattern_query"),
            sort_query: r(kb, "anthill.reflect.LogicalQuery.sort_query"),
            conjunction: r(kb, "anthill.reflect.LogicalQuery.conjunction"),
            disjunction: r(kb, "anthill.reflect.LogicalQuery.disjunction"),
            negation: r(kb, "anthill.reflect.LogicalQuery.negation"),
            guarded: r(kb, "anthill.reflect.LogicalQuery.guarded"),
            projected: r(kb, "anthill.reflect.LogicalQuery.projected"),
            limited: r(kb, "anthill.reflect.LogicalQuery.limited"),
            forall_q: r(kb, "anthill.reflect.LogicalQuery.forall_q"),
            some_q: r(kb, "anthill.reflect.LogicalQuery.some_q"),
            one_q: r(kb, "anthill.reflect.LogicalQuery.one_q"),
            lone_q: r(kb, "anthill.reflect.LogicalQuery.lone_q"),
            no_q: r(kb, "anthill.reflect.LogicalQuery.no_q"),
            count_q: r(kb, "anthill.reflect.LogicalQuery.count_q"),
            sum_q: r(kb, "anthill.reflect.LogicalQuery.sum_q"),
            min_q: r(kb, "anthill.reflect.LogicalQuery.min_q"),
            max_q: r(kb, "anthill.reflect.LogicalQuery.max_q"),

            term: kb.intern("term"),
            sort_name: kb.intern("sort_name"),
            left: kb.intern("left"),
            right: kb.intern("right"),
            query: kb.intern("query"),
            condition: kb.intern("condition"),
            count: kb.intern("count"),
            vars: kb.intern("vars"),
            var: kb.intern("var"),
            body: kb.intern("body"),

            is_entity_of: r(kb, "anthill.reflect.typing.is_entity_of"),
            not: r(kb, "anthill.reflect.not"),
            or: r(kb, "anthill.kernel.or"),
        }
    }
}

// ── Public API on KnowledgeBase ────────────────────────────────

impl KnowledgeBase {
    /// Recursively promote a runtime `Value` into a hash-consed `TermId`.
    ///
    /// This is the **sole** input-boundary hash-cons site described in
    /// proposal 026.1 §"One input boundary, one output boundary". Every
    /// other call into the resolver goes through `TermView` and preserves
    /// lineage.
    ///
    /// `Value::Term(tid)` returns the existing `tid` verbatim (no walk,
    /// no extra refcount). Scalar variants are looked up in the dedup
    /// index. `Value::Entity` recurses into its args and sorts named
    /// fields canonically. `Value::Unit`, `Value::Tuple`, and the
    /// interpreter-owned handles (`Closure`, `Stream`, `Lazy`) have no
    /// term equivalent and error rather than round-trip through a
    /// synthetic representation.
    pub fn alloc_from_value(&mut self, v: &Value) -> Result<TermId, LowerError> {
        match v {
            Value::Int(n) => Ok(self.terms.alloc(Term::Const(Literal::Int(*n)))),
            Value::BigInt(n) => Ok(self.terms.alloc(Term::Const(Literal::BigInt(n.clone())))),
            Value::Float(f) => Ok(self.terms.alloc(Term::Const(
                Literal::Float(ordered_float::OrderedFloat(*f)),
            ))),
            Value::Bool(b) => Ok(self.terms.alloc(Term::Const(Literal::Bool(*b)))),
            Value::Str(s) => Ok(self.terms.alloc(Term::Const(Literal::String(s.clone())))),
            Value::Term(tid) => Ok(*tid),
            // WI-109: a value-level logic variable lowers back to `Term::Var`,
            // making the round-trip lossless.
            Value::Var(var) => Ok(self.terms.alloc(Term::Var(*var))),
            Value::Entity { functor, pos, named } => {
                let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
                for p in pos.iter() {
                    pos_args.push(self.alloc_from_value(p)?);
                }
                let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                for (sym, nv) in named.iter() {
                    named_args.push((*sym, self.alloc_from_value(nv)?));
                }
                // Sort named_args to match the loader's canonical form
                // (load.rs:1730) — declaration order for registered entities,
                // falling back to Symbol::index() for functors with no
                // recorded field ordering (anonymous tuples, ad-hoc
                // structures). Linear scan over the field list beats a
                // HashMap here — entities are typically 2-5 fields.
                if let Some(order) = self.entity_field_names(*functor) {
                    named_args.sort_by_key(|(s, _)| {
                        order.iter().position(|f| f == s).unwrap_or(usize::MAX)
                    });
                } else {
                    named_args.sort_by_key(|(s, _)| s.index());
                }
                Ok(self.terms.alloc(Term::Fn {
                    functor: *functor,
                    pos_args,
                    named_args,
                }))
            }
            Value::Unit => Err(LowerError::UnsupportedVariant("Unit")),
            Value::Tuple { .. } => Err(LowerError::UnsupportedVariant("Tuple")),
            Value::Closure(_) => Err(LowerError::UnsupportedVariant("Closure")),
            Value::OpRef { .. } => Err(LowerError::UnsupportedVariant("OpRef")),
            Value::Stream(_) => Err(LowerError::UnsupportedVariant("Stream")),
            Value::Lazy(_) => Err(LowerError::UnsupportedVariant("Lazy")),
            Value::Substitution(_) => Err(LowerError::UnsupportedVariant("Substitution")),
            Value::Map(_) => Err(LowerError::UnsupportedVariant("Map")),
            Value::Cell(_) => Err(LowerError::UnsupportedVariant("Cell")),
            Value::Requirement(_) => Err(LowerError::UnsupportedVariant("Requirement")),
            Value::Node(_) => Err(LowerError::UnsupportedVariant("Node")),
        }
    }

    /// Lift a multi-goal body into a single goal by synthesizing a fresh
    /// rule `_synth_N(?vars) :- body`, where `?vars` are the free Globals
    /// across `body`. Returns the head term — a single TermId callers can
    /// pass to `not`, `or`, etc. Proposal 033 / WI-076.
    fn synthesize_conjunction_rule(&mut self, body: Vec<TermId>) -> TermId {
        let mut free_vars: Vec<super::term::VarId> = Vec::new();
        for &g in &body {
            for v in self.collect_vars(g) {
                if !free_vars.iter().any(|fv| fv.raw() == v.raw()) {
                    free_vars.push(v);
                }
            }
        }
        let id = self.rules.len();
        let synth_sym = self.symbols.intern(&format!("_synth_{id}"));
        let pos_args: SmallVec<[TermId; 4]> = free_vars.iter()
            .map(|&v| self.terms.alloc(Term::Var(super::term::Var::Global(v))))
            .collect();
        let head = self.terms.alloc(Term::Fn {
            functor: synth_sym,
            pos_args,
            named_args: SmallVec::new(),
        });
        let rule_sort = self.make_name_term("Rule");
        let domain = self.make_name_term("_global");
        let body_nodes = self.term_body_to_nodes(&body);
        self.assert_rule_debruijn_with_nodes(head, body_nodes, rule_sort, domain, None);
        head
    }

    /// Reduce a lowered branch to a single goal: single-goal verbatim,
    /// multi-goal via `synthesize_conjunction_rule`, empty rejected because
    /// the trivial-collapse semantics (empty body succeeds → wrapping
    /// disjunction unconditionally true / wrapping negation unconditionally
    /// false) is almost always a caller bug rather than intent.
    fn coerce_to_single_goal(
        &mut self,
        goals: Vec<TermId>,
        empty_err: &'static str,
    ) -> Result<TermId, LowerError> {
        match goals.len() {
            0 => Err(LowerError::NotYetImplemented(empty_err)),
            1 => Ok(goals[0]),
            _ => Ok(self.synthesize_conjunction_rule(goals)),
        }
    }

    /// Walk a reified `LogicalQuery` value and produce a goal list for the
    /// resolver. Errors surface unsupported shapes cleanly (rather than
    /// silently evaluating to "always true").
    ///
    /// Cross-constructor notes:
    /// - `empty_query` → `[]` (no constraints = vacuously true).
    /// - `pattern_query(t)` → `[alloc_from_value(t)]`.
    /// - `conjunction(l, r)` → `lower(l) ++ lower(r)` — shared variables
    ///   form a natural join because goals all live in the same
    ///   substitution frame.
    /// - `sort_query(name)` → a synthetic `is_entity_of(?fresh, name)`
    ///   goal; fresh variable names are lexically scoped to this call
    ///   (no leak into the caller's query-level variables).
    /// - `negation(q)` → `[not(g)]` where `g` is the inner's single goal,
    ///   or `[not(_synth_N(?vars))]` for multi-goal bodies — the synthesized
    ///   rule is `_synth_N(?vars) :- inner_goals` (proposal 033 §M4 / WI-076).
    ///   Empty inner is rejected as it almost always indicates a caller bug.
    /// - `disjunction(l, r)` → `[or(l_goal, r_goal)]` via the same
    ///   single-goal coercion; `or` is the rule-form lift over push_choice
    ///   (proposal 033 §M3).
    /// - `guarded(q, cond)` → `lower(q) ++ [alloc_from_value(cond)]`.
    /// - `projected(q, _)` / `limited(q, _)` → for the resolver-level
    ///   view, projection and cardinality limits are post-processing on
    ///   the solution stream; here we return the underlying query's
    ///   goals and document that the caller must honor the wrapper's
    ///   semantics downstream (tracked in the wrapper Value, not the
    ///   lowered TermId list).
    ///
    /// Quantifiers (`forall_q` / `some_q` / ...) and aggregations
    /// (`count_q` / ...) remain `NotYetImplemented` pending M4's
    /// `LogicalStream` plumbing (WI-048), which is where their semantics
    /// need a streaming execution context rather than a flat goal list.
    pub fn lower_query(&mut self, q: &Value) -> Result<Vec<TermId>, LowerError> {
        let syms = LogicalQuerySymbols::resolve(self);
        self.lower_query_with(q, &syms)
    }

    fn lower_query_with(
        &mut self,
        q: &Value,
        syms: &LogicalQuerySymbols,
    ) -> Result<Vec<TermId>, LowerError> {
        let (functor, named) = match q {
            Value::Entity { functor, named, .. } => (*functor, &named[..]),
            Value::Term(_) => {
                // Bare Term values are not LogicalQuery constructors.
                return Err(LowerError::NotALogicalQuery { got: "Term".into() });
            }
            other => return Err(LowerError::NotALogicalQuery {
                got: other.type_name().into(),
            }),
        };

        // `empty_query` has no fields, handle up-front.
        if Some(functor) == syms.empty_query {
            return Ok(Vec::new());
        }

        if Some(functor) == syms.pattern_query {
            let term_v = find_named(named, syms.term)
                .ok_or(LowerError::MissingField {
                    entity: "pattern_query", field: "term",
                })?;
            return Ok(vec![self.alloc_from_value(term_v)?]);
        }

        if Some(functor) == syms.conjunction {
            let left = find_named(named, syms.left).ok_or(LowerError::MissingField {
                entity: "conjunction", field: "left",
            })?;
            let right = find_named(named, syms.right).ok_or(LowerError::MissingField {
                entity: "conjunction", field: "right",
            })?;
            let mut goals = self.lower_query_with(left, syms)?;
            goals.extend(self.lower_query_with(right, syms)?);
            return Ok(goals);
        }

        if Some(functor) == syms.guarded {
            let inner = find_named(named, syms.query).ok_or(LowerError::MissingField {
                entity: "guarded", field: "query",
            })?;
            let cond = find_named(named, syms.condition).ok_or(LowerError::MissingField {
                entity: "guarded", field: "condition",
            })?;
            let mut goals = self.lower_query_with(inner, syms)?;
            goals.push(self.alloc_from_value(cond)?);
            return Ok(goals);
        }

        if Some(functor) == syms.sort_query {
            let name_v = find_named(named, syms.sort_name).ok_or(LowerError::MissingField {
                entity: "sort_query", field: "sort_name",
            })?;
            let name = match name_v {
                Value::Str(s) => s.clone(),
                other => return Err(LowerError::NotALogicalQuery {
                    got: format!("sort_query sort_name = {}", other.type_name()),
                }),
            };
            let sort_sym = self.try_resolve_symbol(&name)
                .ok_or_else(|| LowerError::UnknownSort(name.clone()))?;
            let is_entity_of = syms.is_entity_of.ok_or(LowerError::NotYetImplemented(
                "sort_query without loaded anthill.reflect.typing.is_entity_of",
            ))?;
            let fresh_name = self.intern("_sq");
            let fresh = self.fresh_var(fresh_name);
            let var_term = self.terms.alloc(Term::Var(super::term::Var::Global(fresh)));
            let sort_ref = self.terms.alloc(Term::Ref(sort_sym));
            let goal = self.terms.alloc(Term::Fn {
                functor: is_entity_of,
                pos_args: SmallVec::from_slice(&[var_term, sort_ref]),
                named_args: SmallVec::new(),
            });
            return Ok(vec![goal]);
        }

        if Some(functor) == syms.negation {
            let inner = find_named(named, syms.query).ok_or(LowerError::MissingField {
                entity: "negation", field: "query",
            })?;
            let inner_goals = self.lower_query_with(inner, syms)?;
            let not_sym = syms.not.ok_or(LowerError::NotYetImplemented(
                "negation without loaded anthill.reflect.not",
            ))?;
            let arg = self.coerce_to_single_goal(
                inner_goals,
                "negation of empty_query (semantically `false`)",
            )?;
            let goal = self.terms.alloc(Term::Fn {
                functor: not_sym,
                pos_args: SmallVec::from_slice(&[arg]),
                named_args: SmallVec::new(),
            });
            return Ok(vec![goal]);
        }

        // `or` is the rule-lifted form of push_choice; no extra lifting needed.
        // Multi-goal branches synthesize a fresh conjunction-rule head
        // (proposal 033 §M4 / WI-076).
        if Some(functor) == syms.disjunction {
            let left = find_named(named, syms.left).ok_or(LowerError::MissingField {
                entity: "disjunction", field: "left",
            })?;
            let right = find_named(named, syms.right).ok_or(LowerError::MissingField {
                entity: "disjunction", field: "right",
            })?;
            let l_goals = self.lower_query_with(left, syms)?;
            let r_goals = self.lower_query_with(right, syms)?;
            let or_sym = syms.or.ok_or(LowerError::NotYetImplemented(
                "disjunction without loaded anthill.kernel.or",
            ))?;
            let empty_msg = "disjunction with empty_query branch (empty branch trivially succeeds)";
            let l = self.coerce_to_single_goal(l_goals, empty_msg)?;
            let r = self.coerce_to_single_goal(r_goals, empty_msg)?;
            let goal = self.terms.alloc(Term::Fn {
                functor: or_sym,
                pos_args: SmallVec::from_slice(&[l, r]),
                named_args: SmallVec::new(),
            });
            return Ok(vec![goal]);
        }

        // Projection / limit are wrappers over the inner stream. Flatten
        // to the inner query's goals; the caller is responsible for
        // applying projection/limit semantics on the resulting solution
        // sequence — the resolver itself has nothing to do differently.
        if Some(functor) == syms.projected || Some(functor) == syms.limited {
            let inner = find_named(named, syms.query).ok_or(LowerError::MissingField {
                entity: "projected/limited", field: "query",
            })?;
            return self.lower_query_with(inner, syms);
        }

        // Quantifiers / aggregations: pending M4 LogicalStream (WI-048).
        // Return a recognizable error for now so callers don't silently
        // get the wrong semantics.
        for (quantifier_sym, label) in [
            (syms.forall_q, "forall_q"),
            (syms.some_q, "some_q"),
            (syms.one_q, "one_q"),
            (syms.lone_q, "lone_q"),
            (syms.no_q, "no_q"),
            (syms.count_q, "count_q"),
            (syms.sum_q, "sum_q"),
            (syms.min_q, "min_q"),
            (syms.max_q, "max_q"),
        ] {
            if Some(functor) == quantifier_sym {
                return Err(LowerError::NotYetImplemented(label));
            }
        }

        // Unknown functor — not a LogicalQuery constructor at all.
        let name = self.qualified_name_of(functor).to_string();
        Err(LowerError::NotALogicalQuery { got: format!("entity {}", name) })
    }

    /// Construct a lazy search stream over the lowered goals of the given
    /// `LogicalQuery`. Uses [`ResolveConfig::default`] — callers that want
    /// custom depth or solution caps should use `lower_query` + `resolve_lazy`
    /// directly.
    ///
    /// Per proposal 026.1 §"Query-lowering at execute": this is the sole
    /// public entry for value-driven KB queries. Every reflect operation
    /// with value args compiles down to assembling a `LogicalQuery` and
    /// calling this function.
    pub fn execute_logical_query(&mut self, q: &Value) -> Result<SearchStream, LowerError> {
        let goals = self.lower_query(q)?;
        Ok(self.resolve_lazy(&goals, &ResolveConfig::default()))
    }

}

fn find_named<'a>(named: &'a [(Symbol, Value)], key: Symbol) -> Option<&'a Value> {
    named.iter().find(|(s, _)| *s == key).map(|(_, v)| v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kb::term::{Var, VarId};

    /// WI-109: `Value::Var` lowers back to `Term::Var` losslessly — the
    /// kind and id survive (`VarId` ignores the display name on compare).
    #[test]
    fn value_var_lowers_to_term_var() {
        let mut kb = KnowledgeBase::new();
        let name = kb.intern("x");
        for var in [
            Var::Global(VarId::new(3, name)),
            Var::DeBruijn(5),
            Var::Rigid(VarId::new(7, name)),
        ] {
            let tid = kb.alloc_from_value(&Value::Var(var)).expect("lowers");
            assert_eq!(*kb.get_term(tid), Term::Var(var), "round-trips to the same Var");
        }
    }
}

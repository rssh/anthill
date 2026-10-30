//! Value-integrated KB query execution (proposal 026.1 §Query-lowering at execute).
//!
//! This module is the **input boundary** between runtime `Value`s and the
//! resolver's goals. A reified `LogicalQuery` (expressed as a `Value` tree of
//! `pattern_query`, `conjunction`, ... constructors) is lowered to a list of
//! goal `Value`s, each on the carrier it came on, and dispatched through the
//! existing `SearchStream`. Answers come back with `Value`-typed bindings —
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

use super::resolve::{PositionalPlan, ResolveConfig, SearchStream};
use super::term::{Literal, Term, TermId};
use super::term_view::{TermView, ViewHead};
use super::KnowledgeBase;

/// Reason a `Value` could not be lowered into a KB query.
#[derive(Clone, Debug)]
pub enum LowerError {
    /// A `Value` variant with no `TermId` equivalent reached
    /// `alloc_from_value` (e.g. `Closure`, `Stream`, `Unit`).
    UnsupportedVariant(&'static str),
    /// The `Value` passed to `lower_query` is not a `LogicalQuery` entity
    /// (e.g. a bare literal or an entity whose functor isn't one of the
    /// constructors declared in `anthill.reflect.LogicalQuery`).
    NotALogicalQuery { got: String },
    /// A `LogicalQuery` constructor was recognized but its payload is
    /// missing a required named argument.
    MissingField {
        entity: &'static str,
        field: &'static str,
    },
    /// A `sort_query`'s `sort` field is present but does not name a sort by
    /// reference (WI-632): a literal, a variable, or an aggregate carrier that
    /// `value_functor` can't resolve to a functor symbol. The query shape is
    /// valid — only this field is malformed — so this is distinct from
    /// `NotALogicalQuery`.
    NotASortReference { got: String },
    /// A constructor in `LogicalQuery` hasn't been wired through to the
    /// resolver yet. Kept separate from `UnsupportedVariant` so call sites
    /// can distinguish "design hole" from "garbage input".
    NotYetImplemented(&'static str),
    /// WI-500: a runtime-built positional constructor has more positional args
    /// than the entity has unfilled fields. Lowering it would store a positional
    /// term that silently never matches the canonical named pattern, so fail
    /// loudly (the loud-error principle; the loader rejects the same shape at
    /// load time).
    OverArityConstructor {
        functor: String,
        given: usize,
        unfilled: usize,
        declared: String,
    },
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
            LowerError::NotASortReference { got } =>
                write!(f, "sort_query `sort` field is not a sort reference: {}", got),
            LowerError::NotYetImplemented(what) =>
                write!(f, "LogicalQuery lowering not yet implemented: {}", what),
            LowerError::OverArityConstructor { functor, given, unfilled, declared } =>
                write!(
                    f,
                    "constructor '{}' given {} positional argument(s) but has {} unfilled field(s) (declares: {})",
                    functor, given, unfilled, declared,
                ),
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
    pub sort: Symbol,
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
    // `anthill.kernel.push_and` — a multi-goal branch of `negation` / `disjunction`.
    pub push_and: Option<Symbol>,
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
            sort: kb.intern("sort"),
            left: kb.intern("left"),
            right: kb.intern("right"),
            query: kb.intern("query"),
            condition: kb.intern("condition"),
            count: kb.intern("count"),
            vars: kb.intern("vars"),
            var: kb.intern("var"),
            body: kb.intern("body"),

            is_entity_of: r(kb, "anthill.reflect.typing.is_entity_of"),
            not: r(kb, "anthill.kernel.not"),
            or: r(kb, "anthill.kernel.or"),
            push_and: r(kb, "anthill.kernel.push_and"),
        }
    }
}

// ── Public API on KnowledgeBase ────────────────────────────────

impl Value {
    /// WI-1023 — does [`KnowledgeBase::alloc_from_value`] lower `self` to a **LEAF**
    /// term, losslessly and infallibly? The one reader of that half of its accept
    /// set, stated HERE — against the function it describes — rather than at the
    /// caller, which is how the old `Value::Term | SymbolRef` list came to miss five
    /// carriers this answers `true` for.
    ///
    /// EXHAUSTIVENESS CATCHES A NEW VARIANT, NOT A MOVED ONE. Adding a `Value` arm
    /// breaks compilation here and at `alloc_from_value` both; but moving an
    /// existing variant between that function's `Ok` and `Err` groups would leave
    /// this silently stale, and no type can see that. `leaf_lowering_agrees_with_alloc`
    /// is what does — it drives every variant through both and compares.
    ///
    /// It is deliberately three questions collapsed into one BOOLEAN, and the
    /// distinction is what the arms record:
    ///
    ///  - **LEAF.** `Value::Entity` lowers, and losslessly, but to an APPLICATION.
    ///    A caller asking this is choosing between a hash-consed `Term::Fn` and a
    ///    `Value::Entity` for the whole application; a compound child is exactly the
    ///    case where that choice is not free.
    ///  - **LOSSLESS.** `Value::Node` is excluded by `alloc_from_value` itself
    ///    (`UnsupportedVariant`), and must be: lowering an occurrence drops its
    ///    identity/span, which is why `value_to_term` — a DIFFERENT boundary, the
    ///    `Node`-aware one — exists separately.
    ///  - **INFALLIBLE.** No arm answering `true` has a failure mode, which is what
    ///    lets [`KnowledgeBase::fn_value`] treat an `Err` as a broken invariant and
    ///    panic. `Entity` would break that too: `positional_to_named_plan` can
    ///    answer `OverArityConstructor` on real input.
    ///
    /// Exhaustive with no `_` arm, so a new `Value` variant is a compile error here
    /// AND at `alloc_from_value` rather than a silent `false`.
    pub(crate) fn lowers_to_leaf_term(&self) -> bool {
        match self {
            // The leaf arms of `alloc_from_value`, every one an infallible
            // `Ok(alloc(<leaf>))`. `Term` returns its own id unchanged; `Var` and
            // `SymbolRef` are the two round-trip-lossless non-scalar leaves
            // (WI-109 / WI-1016).
            Value::Int(_)
            | Value::BigInt(_)
            | Value::Float(_)
            | Value::Bool(_)
            | Value::Str(_)
            | Value::Term { .. }
            | Value::Var(_)
            | Value::SymbolRef(_) => true,
            // Lowers, but not to a leaf, and not infallibly — see above.
            //
            // WI-20260902-CZJ2N — A 0-FIELD ENTITY IS THE ONE CASE WHERE THIS IS
            // CONSERVATIVE RATHER THAN EXACT, and it is stated because an earlier cut of
            // this ticket made the arm `pos.is_empty() && named.is_empty()` and that was
            // WRONG. Whether a nullary entity lowers to a leaf depends on the FUNCTOR: the
            // canon stores `Fn{f, [], []}` as `Term::Ref(f)` — a leaf — for every name
            // since WI-20260902-JB6RS but the three collection-literal reflect forms, whose
            // empty application stays a `Term::Fn` (`()` is `TupleLiteral()`). This
            // signature has no `KnowledgeBase` to ask, so the honest answer is the
            // conservative one.
            //
            // WHAT `false` COSTS: `KnowledgeBase::fn_value` builds a `Value::Entity`
            // rather than a hash-consed `Term::Fn` for a parent whose child is a
            // 0-field entity — a CARRIER choice, never a wrong answer, since the two
            // read identically through `TermView`. What the arity-aware version cost
            // was a predicate that CLAIMED a leaf `alloc_from_value` does not produce,
            // which is the unsound direction.
            Value::Entity { .. } => false,
            // A tuple lowers to its `TupleLiteral(…)` application, which is no leaf.
            Value::Unit | Value::Tuple { .. } => false,
            // `alloc_from_value` answers `UnsupportedVariant` for all of these: the
            // interpreter-owned handles have no faithful term form, and `Node` has one
            // only through the separate occurrence-aware boundary.
            Value::Closure(_)
            | Value::OpRef { .. }
            | Value::Stream(_)
            | Value::Substitution(_)
            | Value::Map(_)
            | Value::Cell(_)
            | Value::Kb(_)
            | Value::FactRef(_)
            | Value::Node(_)
            | Value::Relation { .. } => false,
        }
    }
}

impl KnowledgeBase {
    /// A tuple value — `Value::Tuple`, and `Value::Unit`, the tuple of no components — as
    /// the term a rule writes for the same text, `TupleLiteral(_1: …, name: …)`: every
    /// component named, a positional one under its `_N` label, in the order written, which
    /// is the order the tuple view reads it in. Each component is lowered by `lower`.
    pub(crate) fn tuple_value_term(
        &mut self,
        pos: &[Value],
        named: &[(Symbol, Value)],
        lower: impl Fn(&mut KnowledgeBase, &Value) -> Result<TermId, LowerError>,
    ) -> Result<TermId, LowerError> {
        let functor = self.resolve_symbol(crate::parse::desugar_target::qualified(
            crate::parse::desugar_target::TUPLE_LITERAL,
        ));
        let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
        for (i, p) in pos.iter().enumerate() {
            let label = self.intern(&crate::intern::positional_label(i));
            named_args.push((label, lower(self, p)?));
        }
        for (sym, v) in named.iter() {
            named_args.push((*sym, lower(self, v)?));
        }
        Ok(self.alloc(Term::Fn {
            functor,
            pos_args: SmallVec::new(),
            named_args,
        }))
    }

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
    /// fields canonically. A tuple value lowers to the term a rule writes for it
    /// ([`Self::tuple_value_term`]). The interpreter-owned handles (`Closure`,
    /// `Stream`) have no term equivalent and error rather than round-trip through a
    /// synthetic representation.
    pub fn alloc_from_value(&mut self, v: &Value) -> Result<TermId, LowerError> {
        match v {
            Value::Int(n) => Ok(self.terms.alloc(Term::Const(Literal::Int(*n)))),
            Value::BigInt(n) => Ok(self.terms.alloc(Term::Const(Literal::BigInt(n.clone())))),
            Value::Float(f) => Ok(self
                .terms
                .alloc(Term::Const(Literal::Float(ordered_float::OrderedFloat(*f))))),
            Value::Bool(b) => Ok(self.terms.alloc(Term::Const(Literal::Bool(*b)))),
            Value::Str(s) => Ok(self.terms.alloc(Term::Const(Literal::String(s.clone())))),
            Value::Term { id: tid, .. } => Ok(*tid),
            // WI-109: a value-level logic variable lowers back to `Term::Var`,
            // making the round-trip lossless.
            Value::Var(var) => Ok(self.terms.alloc(Term::Var(*var))),
            // Same round-trip losslessness for the other leaf: a `Value::SymbolRef`
            // lowers back to the `Term::Ref` it views as.
            Value::SymbolRef(sym) => Ok(self.terms.alloc(Term::Ref(*sym))),
            Value::Entity {
                functor,
                pos,
                named,
                ..
            } => {
                let mut pos_args: SmallVec<[TermId; 4]> = SmallVec::new();
                for p in pos.iter() {
                    pos_args.push(self.alloc_from_value(p)?);
                }
                let mut named_args: SmallVec<[(Symbol, TermId); 2]> = SmallVec::new();
                for (sym, nv) in named.iter() {
                    named_args.push((*sym, self.alloc_from_value(nv)?));
                }
                // WI-500: desugar positional → named (declaration order,
                // fields-not-named) so a runtime-built positional entity lowers to
                // the SAME canonical named term the loader produces — the shape
                // `assert_fact` / the discrim tree keys on. Without it the stored
                // fact stays positional and never unifies with a named pattern (the
                // WI-433 never-match on the persist/value→term path).
                let named_syms: SmallVec<[Symbol; 2]> =
                    named_args.iter().map(|(s, _)| *s).collect();
                match self.positional_to_named_plan(*functor, &named_syms, pos_args.len()) {
                    PositionalPlan::Skip => {}
                    PositionalPlan::Assign(fields) => {
                        for (i, pv) in std::mem::take(&mut pos_args).into_iter().enumerate() {
                            named_args.push((fields[i], pv));
                        }
                    }
                    PositionalPlan::OverArity { declared, unfilled } => {
                        return Err(LowerError::OverArityConstructor {
                            functor: self.local_name_of(*functor).to_string(),
                            given: pos_args.len(),
                            unfilled,
                            declared: declared
                                .iter()
                                .map(|s| self.local_name_of(*s).to_string())
                                .collect::<Vec<_>>()
                                .join(", "),
                        });
                    }
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
                    named_args.sort_by_key(|(s, _)| s.to_bits());
                }
                // WI-511: route through `alloc` so a 0-ary constructor entity
                // lowers to the canonical `Ref(c)`, not a divergent `Fn{c}`.
                Ok(self.alloc(Term::Fn {
                    functor: *functor,
                    pos_args,
                    named_args,
                }))
            }
            Value::Unit => self.tuple_value_term(&[], &[], Self::alloc_from_value),
            Value::Tuple { pos, named } => {
                self.tuple_value_term(pos, named, Self::alloc_from_value)
            }
            Value::Closure(_) => Err(LowerError::UnsupportedVariant("Closure")),
            Value::OpRef { .. } => Err(LowerError::UnsupportedVariant("OpRef")),
            Value::Stream(_) => Err(LowerError::UnsupportedVariant("Stream")),
            Value::Substitution(_) => Err(LowerError::UnsupportedVariant("Substitution")),
            Value::Map(_) => Err(LowerError::UnsupportedVariant("Map")),
            Value::Cell(_) => Err(LowerError::UnsupportedVariant("Cell")),
            Value::Kb(_) => Err(LowerError::UnsupportedVariant("KB")),
            Value::FactRef(_) => Err(LowerError::UnsupportedVariant("FactRef")),
            Value::Node(_) => Err(LowerError::UnsupportedVariant("Node")),
            // WI-714: a `Relation` is an intensional query value — it is RUN
            // (`Relation.splitFirst` → `execute_logical_query`), never lowered to a
            // data term. Its `query` payload IS a lowerable `LogicalQuery`, but the
            // relation wrapper itself has no term equivalent.
            Value::Relation { .. } => Err(LowerError::UnsupportedVariant("Relation")),
        }
    }

    /// Reduce a lowered branch to the one goal a `not`/`or` wrapper takes (WI-513): a
    /// single goal verbatim, on its own carrier; several as their conjunction,
    /// `push_and(g₁, push_and(g₂, …))` over the goals as they are; none rejected,
    /// because the trivial-collapse semantics (an empty body succeeds, so the wrapping
    /// disjunction is unconditionally true and the wrapping negation unconditionally
    /// false) is almost always a caller bug rather than intent.
    ///
    /// Several goals were a synthesized rule, `_synth_N(?vars) :- goals` (proposal
    /// 033 §M4), memoized on a structural key of the body, and its head was the goal.
    /// The stored body lowered each goal to a term, so a closure or a lambda in it
    /// refused the query (WI-20261030-BXMPK); `push_and` (WI-20260822-J38JE) is the
    /// conjunction as a goal, so nothing is stored and nothing is lowered.
    fn coerce_to_single_goal_value(
        &mut self,
        goals: Vec<Value>,
        syms: &LogicalQuerySymbols,
        empty_err: &'static str,
    ) -> Result<Value, LowerError> {
        if goals.len() < 2 {
            return goals
                .into_iter()
                .next()
                .ok_or(LowerError::NotYetImplemented(empty_err));
        }
        let push_and = syms.push_and.ok_or(LowerError::NotYetImplemented(
            "conjunction without loaded anthill.kernel.push_and",
        ))?;
        let mut rest = goals.into_iter().rev();
        let last = rest.next().expect("two goals or more");
        Ok(rest.fold(last, |goal, g| self.make_goal_value(push_and, vec![g, goal])))
    }

    /// Build a goal `Value` `functor(args...)` as a `Value::Entity` (WI-513) — the
    /// `not` / `or` / `push_and` wrappers `lower_query` builds, and the resolver's own
    /// rewritten goals (an applied `ho_apply`, an `eq(…, true)`). The entity carrier
    /// keeps each argument on its own carrier (an occurrence stays an occurrence, a
    /// closure a closure), and the resolver classifies a builtin by reading `functor`
    /// through `TermView` (`get_builtin_view`).
    pub(crate) fn make_goal_value(&self, functor: Symbol, args: Vec<Value>) -> Value {
        Value::Entity {
            functor,
            pos: std::rc::Rc::from(args),
            named: std::rc::Rc::from(Vec::<(Symbol, Value)>::new()),
        }
    }

    /// Walk a reified `LogicalQuery` value and produce a goal list for the
    /// resolver. Errors surface unsupported shapes cleanly (rather than
    /// silently evaluating to "always true").
    ///
    /// WI-513: carrier-neutral — goals are `Value`s, not `TermId`s. A leaf
    /// (`pattern_query` term / `guarded` condition) passes through
    /// [`Self::lower_leaf`], which keeps it on the carrier it came on (an occurrence
    /// resolves via `query_view`, preserving WI-518). This is the SINGLE lowerer shared
    /// by the eval-side [`Self::execute_logical_query`] and the guard engine
    /// (`evaluate_guard` and the quantifier evaluators in `kb/mod.rs`), replacing
    /// the guard engine's old partial `lower_logical_query` re-implementation.
    ///
    /// Cross-constructor notes:
    /// - `empty_query` → `[]` (no constraints = vacuously true).
    /// - `pattern_query(t)` → `[lower_leaf(t)]`.
    /// - `conjunction(l, r)` → `lower(l) ++ lower(r)` — shared variables
    ///   form a natural join because goals all live in the same
    ///   substitution frame.
    /// - `sort_query(sort)` → a synthetic `is_entity_of(?fresh, sort)`
    ///   goal, where `sort` is a by-reference `Term::Ref` (WI-632); fresh
    ///   variable names are lexically scoped to this call (no leak into the
    ///   caller's query-level variables).
    /// - `negation(q)` → `[not(g)]` where `g` is the inner's single goal,
    ///   or `[not(push_and(g₁, push_and(g₂, …)))]` for a multi-goal body
    ///   ([`Self::coerce_to_single_goal_value`]). Empty inner is rejected as it
    ///   almost always indicates a caller bug.
    /// - `disjunction(l, r)` → `[or(l_goal, r_goal)]` via the same
    ///   single-goal coercion; `or` is the rule-form lift over push_choice
    ///   (proposal 033 §M3).
    /// - `guarded(q, cond)` → `lower(q) ++ [lower_leaf(cond)]`.
    /// - `projected(q, _)` / `limited(q, _)` → for the resolver-level
    ///   view, projection and cardinality limits are post-processing on
    ///   the solution stream; here we return the underlying query's
    ///   goals and document that the caller must honor the wrapper's
    ///   semantics downstream (tracked in the wrapper Value, not the
    ///   lowered goal list).
    ///
    /// Quantifiers (`forall_q` / `some_q` / ...) and aggregations
    /// (`count_q` / ...) remain `NotYetImplemented` here pending M4's
    /// `LogicalStream` plumbing (WI-048); the guard engine evaluates the
    /// counting/forall quantifiers itself (it calls this lowerer only on the
    /// quantifier's non-quantifier condition/body sub-queries).
    pub fn lower_query(&mut self, q: &Value) -> Result<Vec<Value>, LowerError> {
        let syms = LogicalQuerySymbols::resolve(self);
        self.lower_query_with(q, &syms)
    }

    /// Lower a single goal-atom leaf (WI-513): the leaf IS the goal, on the carrier it
    /// came on. An occurrence resolves as an occurrence goal via `query_view` (WI-518),
    /// and keeps its source spans; an entity an operation built resolves as an entity
    /// goal; a term as a term. A carrier that is no goal at all — a closure, a stream —
    /// is refused, loudly, as before.
    ///
    /// NOTHING IS LOWERED TO A TERM (WI-20261030-BXMPK). A leaf went through
    /// `value_to_term`, and a part of it with no term form refused the whole query: an
    /// operation run by the SLD→eval bridge receives a rule-body operand on its own
    /// carrier (WI-20260827-3ZNBC), so `g(f) = keep(f).head.c`, reached from
    /// `?r <=> Driver.g(lambda (x: Int64) -> Int64.add(x, 1))`, built `keep(<lambda>, ?c)`
    /// and raised `malformed_query`: one undecided row where `keep` answers 1. Before
    /// that, through `alloc_from_value`, a nested occurrence refused it the same way
    /// (WI-20260925-PRVA2).
    pub(crate) fn lower_leaf(&mut self, v: &Value) -> Result<Value, LowerError> {
        if let ViewHead::Opaque = v.head(self) {
            return Err(LowerError::UnsupportedVariant(v.type_name()));
        }
        Ok(self.canonical_spine(v)?.unwrap_or_else(|| v.clone()))
    }

    /// `v` with every entity in its value spine in the form a fact is stored in, or `None`
    /// when it is in that form already: a positional argument of a declared entity is its
    /// named field and the named arguments stand in declaration order (WI-500, through
    /// [`Self::positional_to_named_plan`] and `canonicalize_record_named_args`), at every
    /// depth, on the carriers the parts ride. Rebuilt only where something moved.
    ///
    /// The evaluator builds an entity so already; a host builtin or a bridge need not
    /// (`project_field`'s positional arm says the same). `value_to_term` made this desugar
    /// while it lowered a leaf, and a leaf that is no longer lowered still owes it: MEASURED,
    /// `Point(7, 8)` built positionally answered nothing against `fact Point(x: 7, y: 8)`
    /// until this was here. An occurrence and a term are in that form by construction.
    fn canonical_spine(&mut self, v: &Value) -> Result<Option<Value>, LowerError> {
        match v {
            Value::Entity {
                functor,
                pos,
                named,
            } => {
                let mut moved = false;
                let mut new_pos: Vec<Value> = Vec::with_capacity(pos.len());
                for p in pos.iter() {
                    let c = self.canonical_spine(p)?;
                    moved |= c.is_some();
                    new_pos.push(c.unwrap_or_else(|| p.clone()));
                }
                let mut new_named: Vec<(Symbol, Value)> = Vec::with_capacity(named.len());
                for (k, nv) in named.iter() {
                    let c = self.canonical_spine(nv)?;
                    moved |= c.is_some();
                    new_named.push((*k, c.unwrap_or_else(|| nv.clone())));
                }
                let named_syms: SmallVec<[Symbol; 2]> =
                    new_named.iter().map(|(s, _)| *s).collect();
                match self.positional_to_named_plan(*functor, &named_syms, new_pos.len()) {
                    PositionalPlan::Skip => {}
                    PositionalPlan::Assign(fields) => {
                        moved = true;
                        for (i, pv) in std::mem::take(&mut new_pos).into_iter().enumerate() {
                            new_named.push((fields[i], pv));
                        }
                    }
                    PositionalPlan::OverArity { declared, unfilled } => {
                        return Err(LowerError::OverArityConstructor {
                            functor: self.local_name_of(*functor).to_string(),
                            given: new_pos.len(),
                            unfilled,
                            declared: declared
                                .iter()
                                .map(|s| self.local_name_of(*s).to_string())
                                .collect::<Vec<_>>()
                                .join(", "),
                        });
                    }
                }
                self.canonicalize_record_named_args(*functor, &mut new_named);
                moved |= new_named
                    .iter()
                    .map(|(s, _)| *s)
                    .ne(named.iter().map(|(s, _)| *s));
                Ok(moved.then(|| Value::Entity {
                    functor: *functor,
                    pos: new_pos.into(),
                    named: new_named.into(),
                }))
            }
            Value::Tuple { pos, named } => {
                let mut moved = false;
                let mut new_pos: Vec<Value> = Vec::with_capacity(pos.len());
                for p in pos.iter() {
                    let c = self.canonical_spine(p)?;
                    moved |= c.is_some();
                    new_pos.push(c.unwrap_or_else(|| p.clone()));
                }
                let mut new_named: Vec<(Symbol, Value)> = Vec::with_capacity(named.len());
                for (k, nv) in named.iter() {
                    let c = self.canonical_spine(nv)?;
                    moved |= c.is_some();
                    new_named.push((*k, c.unwrap_or_else(|| nv.clone())));
                }
                Ok(moved.then(|| Value::Tuple {
                    pos: new_pos.into(),
                    named: new_named.into(),
                }))
            }
            _ => Ok(None),
        }
    }

    /// Read a named field of a `LogicalQuery` value carrier-agnostically through
    /// `TermView`, as an owned `Value` (WI-513). Works for both a `Value::Entity`
    /// (eval path) and a `Value::Term` hash-consed LogicalQuery (loader/guard
    /// path) — the latter is why the structure read can't pattern-match `Entity`.
    fn lq_field(&self, q: &Value, field: Symbol) -> Option<Value> {
        super::term_view::TermView::named_arg(q, self, field).map(|c| c.to_value())
    }

    pub(crate) fn lower_query_with(
        &mut self,
        q: &Value,
        syms: &LogicalQuerySymbols,
    ) -> Result<Vec<Value>, LowerError> {
        // WI-513: read the LogicalQuery structure carrier-agnostically through
        // `TermView`, so this single lowerer accepts BOTH a `Value::Entity` (the
        // eval-side reflect path) and a `Value::Term` hash-consed LogicalQuery
        // (the loader/guard path — `build_logical_query` builds `Term::Fn{no_q,…}`).
        // The old `match q { Value::Entity … }` rejected the term carrier, which is
        // why the guard engine needed its own parallel `lower_logical_query`.
        let functor = super::term_view::TermView::head(q, self)
            .functor_sym()
            .ok_or_else(|| LowerError::NotALogicalQuery {
                got: q.type_name().into(),
            })?;

        // `empty_query` has no fields, handle up-front.
        if Some(functor) == syms.empty_query {
            return Ok(Vec::new());
        }

        if Some(functor) == syms.pattern_query {
            let term_v = self
                .lq_field(q, syms.term)
                .ok_or(LowerError::MissingField {
                    entity: "pattern_query",
                    field: "term",
                })?;
            return Ok(vec![self.lower_leaf(&term_v)?]);
        }

        if Some(functor) == syms.conjunction {
            let left = self
                .lq_field(q, syms.left)
                .ok_or(LowerError::MissingField {
                    entity: "conjunction",
                    field: "left",
                })?;
            let right = self
                .lq_field(q, syms.right)
                .ok_or(LowerError::MissingField {
                    entity: "conjunction",
                    field: "right",
                })?;
            let mut goals = self.lower_query_with(&left, syms)?;
            goals.extend(self.lower_query_with(&right, syms)?);
            return Ok(goals);
        }

        if Some(functor) == syms.guarded {
            let inner = self
                .lq_field(q, syms.query)
                .ok_or(LowerError::MissingField {
                    entity: "guarded",
                    field: "query",
                })?;
            let cond = self
                .lq_field(q, syms.condition)
                .ok_or(LowerError::MissingField {
                    entity: "guarded",
                    field: "condition",
                })?;
            let mut goals = self.lower_query_with(&inner, syms)?;
            goals.push(self.lower_leaf(&cond)?);
            return Ok(goals);
        }

        if Some(functor) == syms.sort_query {
            // WI-632: `sort_query` carries the sort BY REFERENCE (a `Term::Ref`),
            // resolved at the caller's write site with real scope — not a
            // runtime-resolved name string. Extract its already-qualified functor
            // symbol via `value_functor` (the `facts_of` precedent); a `sort`
            // field that names no functor (a literal, a var, an aggregate) is a
            // caller bug, surfaced loudly.
            let sort_v = self
                .lq_field(q, syms.sort)
                .ok_or(LowerError::MissingField {
                    entity: "sort_query",
                    field: "sort",
                })?;
            let sort_sym = crate::eval::eval::type_value_decl(self, &sort_v).ok_or_else(|| {
                LowerError::NotASortReference {
                    got: sort_v.type_name().to_string(),
                }
            })?;
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
            return Ok(vec![Value::term(goal)]);
        }

        if Some(functor) == syms.negation {
            let inner = self
                .lq_field(q, syms.query)
                .ok_or(LowerError::MissingField {
                    entity: "negation",
                    field: "query",
                })?;
            let inner_goals = self.lower_query_with(&inner, syms)?;
            let not_sym = syms.not.ok_or(LowerError::NotYetImplemented(
                "negation without loaded anthill.kernel.not",
            ))?;
            let arg = self.coerce_to_single_goal_value(
                inner_goals,
                syms,
                "negation of empty_query (semantically `false`)",
            )?;
            return Ok(vec![self.make_goal_value(not_sym, vec![arg])]);
        }

        // `or` is the rule-lifted form of push_choice; no extra lifting needed.
        // A multi-goal branch is its `push_and` conjunction.
        if Some(functor) == syms.disjunction {
            let left = self
                .lq_field(q, syms.left)
                .ok_or(LowerError::MissingField {
                    entity: "disjunction",
                    field: "left",
                })?;
            let right = self
                .lq_field(q, syms.right)
                .ok_or(LowerError::MissingField {
                    entity: "disjunction",
                    field: "right",
                })?;
            let l_goals = self.lower_query_with(&left, syms)?;
            let r_goals = self.lower_query_with(&right, syms)?;
            let or_sym = syms.or.ok_or(LowerError::NotYetImplemented(
                "disjunction without loaded anthill.kernel.or",
            ))?;
            let empty_msg = "disjunction with empty_query branch (empty branch trivially succeeds)";
            // `or` lowers to the stdlib rule `or(?a, ?b) :- push_choice(?a, ?b)`, built as
            // a goal over its two branches as they are, as `not` is. It was a hash-consed
            // `Term::Fn` with each branch lowered to a `TermId`, which a branch holding a
            // closure or a lambda refused (WI-20261030-BXMPK); `push_choice` reads its
            // branches through the view since WI-692.
            let l_val = self.coerce_to_single_goal_value(l_goals, syms, empty_msg)?;
            let r_val = self.coerce_to_single_goal_value(r_goals, syms, empty_msg)?;
            return Ok(vec![self.make_goal_value(or_sym, vec![l_val, r_val])]);
        }

        // Projection / limit are wrappers over the inner stream. Flatten
        // to the inner query's goals; the caller is responsible for
        // applying projection/limit semantics on the resulting solution
        // sequence — the resolver itself has nothing to do differently.
        if Some(functor) == syms.projected || Some(functor) == syms.limited {
            let inner = self
                .lq_field(q, syms.query)
                .ok_or(LowerError::MissingField {
                    entity: "projected/limited",
                    field: "query",
                })?;
            return self.lower_query_with(&inner, syms);
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
        Err(LowerError::NotALogicalQuery {
            got: format!("entity {}", name),
        })
    }

    /// Construct a lazy search stream over the lowered goals of the given
    /// `LogicalQuery`. Callers that want custom depth or solution caps should use
    /// `lower_query` + `resolve_lazy` directly.
    ///
    /// Per proposal 026.1 §"Query-lowering at execute": this is the sole
    /// public entry for value-driven KB queries. Every reflect operation
    /// with value args compiles down to assembling a `LogicalQuery` and
    /// calling this function.
    ///
    /// **THE STREAM IS A BAG OF PROOFS, NOT A SET OF ANSWERS** (WI-FFPGD), which is
    /// why this is the one place that turns `dedup_answers` off. Both consumers say
    /// so in their own types: `Relation.splitFirst` materializes each solution as a
    /// row, and `KB.execute` is typed `Stream[Solution]`. Proposal 052 fixes the
    /// semantics — §"Open questions" 6 pins consumption to "the resolver's stream
    /// as-is", a zero-column membership relation's `multiplicity = number of
    /// proofs`, and "a relation is an unordered bag", with `Relation.set` the
    /// explicit collapse. Deduping here would make `union(r, r)` yield one row and
    /// a recursive clause's re-derivation vanish.
    ///
    /// The default (`dedup_answers: true`) is right for the OTHER face — a query
    /// asking what `?t` can be — and stays on for every `kb.resolve` caller.
    ///
    /// CONTROL, MEASURED by deleting the `config` here and passing
    /// `ResolveConfig::default()` again: SIX tests go red, and they are the whole
    /// population — `wi714_relation_reference_test::wi714_union_is_a_bag`
    /// (`["alice"]`, not `["alice","alice"]`),
    /// `wi714_drain_test::wi714_set_dedups_while_the_drain_keeps_the_bag` (3, not 5),
    /// `wi_yqb1y_one_column_relation_test::yqb1y_join_with_a_membership_operand_is_a_filter`
    /// (one row, not two), `wi741_spec_typed_column_test::wi741_a_spec_typed_column_joins_a_concrete_one`
    /// (1, not 2 — the two clauses deriving `root` collapse),
    /// `wi733_relation_head_eval_test::wi733_head_reads_an_unboundedly_generating_relation`
    /// (2, not 3 — the recursive clause's re-derivation vanishes) and
    /// `wi737_floundered_relation_test::wi737_same_guard_drains_when_its_vars_are_bound_by_the_body`
    /// (1, not 6 — a zero-column relation's multiplicity IS its proof count).
    pub fn execute_logical_query(&mut self, q: &Value) -> Result<SearchStream, LowerError> {
        let goals = self.lower_query(q)?;
        let config = ResolveConfig {
            dedup_answers: false,
            ..ResolveConfig::default()
        };
        Ok(self.resolve_lazy(&goals, &config))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::rc::Rc;
    use crate::kb::node_occurrence::NodeOccurrence;
    use crate::kb::term::{Var, VarId};

    /// WI-1023 — [`Value::lowers_to_leaf_term`] agrees with what
    /// [`KnowledgeBase::alloc_from_value`] actually DOES, variant by variant.
    ///
    /// The predicate restates that function's leaf arms, and exhaustiveness only
    /// catches a variant being ADDED. This catches one being MOVED — an arm going
    /// `Err` → `Ok`, or a leaf arm becoming a recursive one — which is the drift
    /// that would put one logical fact in both of `assert_fact_value`'s disjoint
    /// key spaces.
    ///
    /// One representative per `Value` variant, built by a `match` with NO `_` arm,
    /// so a new variant fails to compile here too rather than going unsampled.
    ///
    /// CONTROL, MEASURED by moving `Value::Unit` from `alloc_from_value`'s `Err`
    /// group to `Ok(self.terms.alloc(Term::Bottom))`: `disagreed: ["Unit"]`.
    #[test]
    fn leaf_lowering_agrees_with_alloc() {
        let mut kb = KnowledgeBase::new();
        crate::kb::load::register_prelude(&mut kb);
        let mut interp = crate::eval::Interpreter::new(kb);
        let s = interp.kb_mut().intern("wi1023");
        let tid = interp.kb_mut().alloc(Term::Ref(s));
        let vid = VarId::new(1, s);
        let span = crate::span::SourceSpan::new(crate::span::SourceId::from_raw(0), 0, 1);
        let samples: Vec<Value> = vec![
            Value::Int(1),
            Value::BigInt(2.into()),
            Value::Float(1.0),
            Value::Bool(true),
            Value::Str("s".into()),
            Value::Unit,
            Value::Tuple {
                pos: Rc::from(vec![Value::Int(1)]),
                named: Rc::from(vec![]),
            },
            Value::Entity {
                functor: s,
                pos: Rc::from(vec![]),
                named: Rc::from(vec![]),
            },
            Value::OpRef {
                spread_labels: None,
                op: s,
                dict: None,
                named: None,
                op_reqs: None,
            },
            Value::Substitution(interp.alloc_subst(crate::kb::subst::Substitution::new())),
            Value::Map(interp.alloc_map(crate::eval::map_arena::MapBody::new())),
            Value::Cell(interp.alloc_cell(Value::Int(0))),
            Value::Relation {
                query: Rc::new(Value::Unit),
                columns: Rc::from(vec![]),
            },
            Value::FactRef(crate::kb::extent::FactRef::resident(
                crate::kb::RuleId::from_raw(0),
            )),
            Value::term(tid),
            Value::Var(Var::Global(vid)),
            Value::SymbolRef(s),
            Value::Node(NodeOccurrence::new_expr(
                crate::kb::node_occurrence::Expr::Ref(s),
                span,
                None,
            )),
        ];
        // Coverage is asserted, not eyeballed: `variant_name` below has no `_`
        // arm, so a new `Value` variant fails to compile there, and this set
        // comparison then fails until it is sampled. `Closure` and `Stream` are
        // the two the unit level cannot mint — their handles come from evaluating a
        // lambda / opening a stream — and both sit in `alloc_from_value`'s
        // `UnsupportedVariant` group next to `Map`/`Cell`/`Substitution`/`FactRef`,
        // which ARE sampled, so the group is driven even though those two are not.
        let covered: std::collections::BTreeSet<&str> = samples.iter().map(variant_name).collect();
        let expected: std::collections::BTreeSet<&str> = [
            "Int",
            "BigInt",
            "Float",
            "Bool",
            "Str",
            "Unit",
            "Tuple",
            "Entity",
            "OpRef",
            "Substitution",
            "Map",
            "Cell",
            "Relation",
            "FactRef",
            "Term",
            "Var",
            "SymbolRef",
            "Node",
        ]
        .into_iter()
        .collect();
        assert_eq!(
            covered, expected,
            "every constructible Value variant is sampled"
        );

        let kb = interp.kb_mut();
        // "Lowers to a LEAF" = `alloc_from_value` succeeds AND the term it produced has
        // no children — both halves read off the function itself rather than assumed.
        let is_leaf = |kb: &mut KnowledgeBase, v: &Value| match kb.alloc_from_value(v) {
            Ok(t) => !matches!(kb.get_term(t), Term::Fn { .. }),
            Err(_) => false,
        };

        // THE SOUND DIRECTION, over every variant: a `true` must be TRUE. This is what
        // `fn_value` relies on when it treats an `Err` as a broken invariant, and it is
        // the half that a leaf arm becoming recursive would break.
        let overclaimed: Vec<&str> = samples
            .iter()
            .filter(|v| v.lowers_to_leaf_term() && !is_leaf(kb, v))
            .map(variant_name)
            .collect();
        assert!(
            overclaimed.is_empty(),
            "predicate claims a leaf `alloc_from_value` does not produce: {overclaimed:?}"
        );

        // AND EXACT EVERYWHERE BUT `Entity` and `Unit`, which are deliberately
        // conservative (WI-20260902-CZJ2N — a NULLARY application's answer depends on the
        // functor's kind, which `lowers_to_leaf_term` has no `KnowledgeBase` to ask). `Unit`
        // is the nullary `TupleLiteral()`, kept an application where the entity is
        // free-standing — a loaded KB — and its bare name in this prelude-only one.
        // Excluding them by NAME rather than weakening the oracle for every variant: an
        // `Err` → `Ok` move anywhere else still fails here.
        let underclaimed: Vec<&str> = samples
            .iter()
            .filter(|v| !v.lowers_to_leaf_term() && is_leaf(kb, v))
            .map(variant_name)
            .filter(|n| *n != "Entity" && *n != "Unit")
            .collect();
        assert!(
            underclaimed.is_empty(),
            "predicate refuses a leaf `alloc_from_value` does produce: {underclaimed:?}"
        );
    }

    /// WI-20260902-CZJ2N — THE ONE CASE `leaf_lowering_agrees_with_alloc` excludes, driven
    /// so the exclusion is a measurement and not a hole.
    ///
    /// A 0-field `Value::Entity` lowers to a LEAF (`Term::Ref`) whatever its functor's kind
    /// — a sort's nullary application has been its bare name since WI-20260902-JB6RS — but
    /// for the canon's one exception, the three collection-literal reflect forms, whose
    /// empty application stays an APPLICATION (`()` is `TupleLiteral()`).
    /// `Value::lowers_to_leaf_term` cannot tell them apart (no `KnowledgeBase` in scope) and
    /// answers `false` for all, which is conservative in the safe direction: it costs
    /// `fn_value` a carrier choice, never correctness.
    #[test]
    fn a_nullary_entity_lowers_by_its_functors_kind() {
        use crate::intern::SymbolKind;
        let mut interp = crate::eval::Interpreter::new(KnowledgeBase::new());
        let kb = interp.kb_mut();
        let g = kb.global_scope();
        let plain = kb.define_symbol("plainlk", "plainlk", SymbolKind::Entity, g);
        let sorted = kb.define_symbol("SortedLk", "SortedLk", SymbolKind::Sort, g);
        // The reflect form, declared as the stdlib declares it: a free-standing entity, so
        // `Sort` and `Entity`, under its qualified name.
        let tuple_form = kb.define_symbol(
            "TupleLiteral",
            crate::parse::desugar_target::qualified(crate::parse::desugar_target::TUPLE_LITERAL),
            SymbolKind::Sort,
            g,
        );
        kb.symbols.add_kind(tuple_form, SymbolKind::Entity);

        for (label, functor, want_leaf) in [
            ("no type reading", plain, true),
            ("a SORT", sorted, true),
            ("a collection-literal form", tuple_form, false),
        ] {
            let v = Value::Entity {
                functor,
                pos: Rc::from(Vec::<Value>::new()),
                named: Rc::from(Vec::<(Symbol, Value)>::new()),
            };
            let t = kb.alloc_from_value(&v).expect("a 0-field entity lowers");
            assert_eq!(
                !matches!(kb.get_term(t), Term::Fn { .. }),
                want_leaf,
                "{label}: the canon decides whether a nullary entity lowers to a leaf"
            );
            assert!(
                !v.lowers_to_leaf_term(),
                "{label}: and the predicate answers `false` for BOTH — conservative, \
                 which is why the oracle above excludes `Entity`"
            );
        }
    }

    /// The exhaustiveness anchor for [`leaf_lowering_agrees_with_alloc`] — no `_`
    /// arm, so a new `Value` variant is a compile error here.
    fn variant_name(v: &Value) -> &'static str {
        match v {
            Value::Int(_) => "Int",
            Value::BigInt(_) => "BigInt",
            Value::Float(_) => "Float",
            Value::Bool(_) => "Bool",
            Value::Str(_) => "Str",
            Value::Unit => "Unit",
            Value::Tuple { .. } => "Tuple",
            Value::Entity { .. } => "Entity",
            Value::Closure(_) => "Closure",
            Value::OpRef { .. } => "OpRef",
            Value::Stream(_) => "Stream",
            Value::Substitution(_) => "Substitution",
            Value::Map(_) => "Map",
            Value::Cell(_) => "Cell",
            Value::Kb(_) => "KB",
            Value::FactRef(_) => "FactRef",
            Value::Term { .. } => "Term",
            Value::Var(_) => "Var",
            Value::SymbolRef(_) => "SymbolRef",
            Value::Node(_) => "Node",
            Value::Relation { .. } => "Relation",
        }
    }

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
            assert_eq!(
                *kb.get_term(tid),
                Term::Var(var),
                "round-trips to the same Var"
            );
        }
    }
}

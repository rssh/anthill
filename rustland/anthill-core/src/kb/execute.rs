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

use std::rc::Rc;

use smallvec::SmallVec;

use crate::eval::value::Value;
use crate::intern::Symbol;

use super::node_occurrence::NodeOccurrence;
use super::resolve::{PositionalPlan, ResolveConfig, SearchStream};
use super::term::{Literal, Term, TermId, Var, VarId};
use super::term_view::{TermView, ViewHead};
use super::KnowledgeBase;

/// WI-169: a stable, hash-consing-independent structural fingerprint of a
/// synthesized conjunction-rule body — the `synth_rule_memo` key, one body
/// rendered to a `Vec<SynthKey>` by [`KnowledgeBase::append_synth_key`].
///
/// Built from PERMANENT parts only — interned `Symbol`s (never recycled) and
/// De Bruijn-style positional var indices — so, unlike a `Vec<TermId>` key (slot
/// ids a future term GC could recycle into an unrelated term), it can never
/// dangle and needs no liveness invariant. Unlike a discrimination key (where
/// pattern vars are wildcard `var_edges`, deliberately over-approximating), it
/// keys each variable by its first-occurrence position, so it PRESERVES variable
/// sharing: `p(?v), q(?v)` and `p(?v), q(?w)` produce distinct keys and never
/// collapse onto one rule.
///
/// The encoding is a fully-bracketed pre-order serialization: every `Fn` emits
/// `Functor` … `EndFn`, with positional children inline and each named child
/// prefixed by `Named`. The `EndFn` close marker makes each `Fn` (and so its
/// named-arg section) self-delimiting, which is load-bearing for INJECTIVITY:
/// without it `f(g(?x), k: ?v)` and `f(g(?x, k: ?v))` would serialize
/// identically and collide onto one rule. Distinct variants for every leaf
/// carrier (`Var` position vs `DeBruijnVar` index vs `Rigid`/`RawVar` identity)
/// keep the token stream injective by construction.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub(crate) enum SynthKey {
    /// Boundary before each top-level body goal — keeps the goal-list framing
    /// unambiguous regardless of each goal's head shape.
    Goal,
    Functor(Symbol),
    /// Closes the nearest open `Functor` — makes every `Fn`'s child list (and
    /// its named-arg section in particular) self-delimiting.
    EndFn,
    /// A named-arg field name; the value's tokens follow.
    Named(Symbol),
    /// A free `Global`, by first-occurrence position across the body
    /// (De Bruijn-style) — preserves sharing, erases the query-specific `VarId`.
    Var(u32),
    /// A bound `DeBruijn` index — a SEPARATE namespace from `Var` so a stored-rule
    /// fragment's `DeBruijn(i)` can never alias a free var at position `i`. Does
    /// not appear in lowered query goals today; kept distinct for totality.
    DeBruijnVar(u32),
    /// A `Rigid`/skolem var, keyed by identity (a constant, like `Ref`). Does
    /// not appear in lowered query goals today; kept distinct for totality.
    Rigid(u32),
    /// Should-never-fire fallback: a body `Global` not collected into `free_vars`
    /// (a broken `collect_vars`/`append_synth_key` walk-parity invariant —
    /// `debug_assert`ed at the call site). Keyed by raw id so two distinct such
    /// vars never collapse (no false reuse); it merely forgoes a memo hit.
    RawVar(u32),
    Lit(Literal),
    Ref(Symbol),
    Ident(Symbol),
    Bottom,
}

/// A `TermView` whose `head()` arity disagrees with its `pos_arg`/`named_arg`
/// accessors. Impossible for every carrier: each derives `head`'s `pos_arity`
/// from its positional-child count and `named_arity`/`named_keys` from its named
/// children, so `pos_arg(i < pos_arity)` and `named_arg(k in named_keys)` always
/// hit an existing child (verified for `TermId`/`Value::Entity`, and every goal
/// occurrence kind — Apply/Constructor/Instantiation, and the synthesized
/// DotApply/VarRef children; a reflect-unloaded DotApply/VarRef reads `Opaque`,
/// not `Functor`, so the child loops never run). The goal-structure walkers
/// [`KnowledgeBase::append_synth_key`] and [`KnowledgeBase::collect_goal_view_vars`]
/// `debug_assert` on it as a backstop against a future carrier that breaks the
/// contract — never a live path.
const VIEW_ARITY_DESYNC: &str =
    "TermView head() arity disagrees with pos_arg/named_arg accessor (broken carrier)";

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
    MissingField { entity: &'static str, field: &'static str },
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
    /// interpreter-owned handles (`Closure`, `Stream`) have no
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
            Value::Term { id: tid, .. } => Ok(*tid),
            // WI-109: a value-level logic variable lowers back to `Term::Var`,
            // making the round-trip lossless.
            Value::Var(var) => Ok(self.terms.alloc(Term::Var(*var))),
            Value::Entity { functor, pos, named, .. } => {
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
                            functor: self.resolve_sym(*functor).to_string(),
                            given: pos_args.len(),
                            unfilled,
                            declared: declared
                                .iter()
                                .map(|s| self.resolve_sym(*s).to_string())
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
                    named_args.sort_by_key(|(s, _)| s.index());
                }
                // WI-511: route through `alloc` so a 0-ary constructor entity
                // lowers to the canonical `Ref(c)`, not a divergent `Fn{c}`.
                Ok(self.alloc(Term::Fn {
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
            Value::Substitution(_) => Err(LowerError::UnsupportedVariant("Substitution")),
            Value::Map(_) => Err(LowerError::UnsupportedVariant("Map")),
            Value::Cell(_) => Err(LowerError::UnsupportedVariant("Cell")),
            Value::Requirement(_) => Err(LowerError::UnsupportedVariant("Requirement")),
            Value::Node(_) => Err(LowerError::UnsupportedVariant("Node")),
        }
    }

    /// Lift a multi-goal body into a single goal by synthesizing a fresh
    /// rule `_synth_N(?vars) :- goals`, where `?vars` are the free Globals
    /// across `goals`. Returns the head as a `Value` callers can pass to `not`,
    /// `or`, etc. Proposal 033 / WI-076.
    ///
    /// WI-678: carrier-agnostic — the goals stay `Value`s (an occurrence
    /// `Value::Node` NEVER round-trips through a `TermId`). Free vars and the memo
    /// key are read through `TermView`, and the stored rule body is the goal
    /// carriers themselves, so the former occurrence→`TermId`→occurrence detour
    /// (`goal_value_to_term` + `term_body_to_nodes`) drops out. The synth head
    /// itself is a genuinely synthetic `_synth_N(?vars)` application (no occurrence
    /// source), so it stays a hash-consed `Term::Fn` carried as a `Value::Term` —
    /// the exact head/rule shape the term path produced, so the De Bruijn frame is
    /// byte-identical.
    fn synthesize_conjunction_rule(&mut self, goals: Vec<Value>) -> Result<Value, LowerError> {
        // Free Globals across the goals, in first-occurrence order — these are
        // the synth head's parameters and define the De Bruijn frame.
        // `collect_goal_view_vars` walks each goal through the SAME `TermView`
        // traversal as `append_synth_key` below, so the head params and the memo
        // key's `Var(pos)` slots are collected in lockstep — walk parity holds by
        // construction (both share one traversal), for every carrier and however
        // the goal nests. It is deliberately STRUCTURAL: a Global living only in a
        // type-position field of an occurrence goal (`p[T = ?v](..)`) is NOT a head
        // param — the resolver never matches type positions (they are not
        // `TermView` children) — so `assert_rule_debruijn_with_nodes` re-collects
        // it off the stored body occurrence and closes it as a sound body-local De
        // Bruijn var. Byte-identical to the former term path, which reified each
        // goal — dropping type positions (`occ_build_fn`) — before collecting.
        let mut free_vars: Vec<VarId> = Vec::new();
        let mut seen = std::collections::HashSet::new();
        for g in &goals {
            self.collect_goal_view_vars(g, &mut free_vars, &mut seen);
        }

        // WI-169: memoize on the body's structural fingerprint so a repeated
        // multi-goal query reuses one synth rule instead of minting a fresh
        // `_synth_N` (+ symbol + rule slot + discrim entry) every time. The key
        // (`Vec<SynthKey>`) is built from PERMANENT parts only — interned symbols
        // and De Bruijn-style positional var indices — so it is storage-neutral:
        // it never depends on `TermId` slot identity (which a future term GC could
        // recycle), so a key can never dangle, AND it preserves variable sharing
        // (`p(?v),q(?v)` ≠ `p(?v),q(?w)`). Two structurally-identical bodies,
        // differing only in which fresh Globals a query opened, produce the SAME
        // key; a hit re-applies the memoized head functor to THIS query's
        // free-vars. Converts the leak from unbounded-in-#queries to
        // bounded-by-#distinct-multi-goal-bodies. The synth rule is a permanent
        // lowering artifact (never retracted — `_synth_N` is a generated symbol no
        // source can name), so the memo never goes stale and needs no
        // invalidation; like `fact_dedup` it must be reset alongside `rules` by
        // any future KB clone/reset. WI-678: the key is walked off each goal's
        // carrier through `TermView`, byte-identically to the former term walk (an
        // occurrence reifies to its `Term::Fn` twin with the same functor / child
        // order, WI-425), so dedup is unchanged.
        let mut key: Vec<SynthKey> = Vec::new();
        for g in &goals {
            key.push(SynthKey::Goal);
            self.append_synth_key(g, &free_vars, &mut key);
        }
        let (synth_sym, fresh) = match self.synth_rule_memo.get(&key) {
            Some(&sym) => (sym, false),
            None => {
                let id = self.rules.len();
                (self.symbols.intern(&format!("_synth_{id}")), true)
            }
        };

        // The head applies the (fresh or memoized) functor to THIS query's
        // free-vars — built once and used both as the asserted rule head (on a
        // miss) and as the returned goal. On a hit it is the only allocation;
        // the rule itself is reused.
        let pos_args: SmallVec<[TermId; 4]> = free_vars.iter()
            .map(|&v| self.terms.alloc(Term::Var(Var::Global(v))))
            .collect();
        let head = self.terms.alloc(Term::Fn {
            functor: synth_sym,
            pos_args,
            named_args: SmallVec::new(),
        });

        if fresh {
            let rule_sort = self.make_name_term("Rule");
            let domain = self.make_name_term("_global");
            // WI-678: the stored body is the goal carriers themselves — an
            // occurrence goal is used directly (its spans/types preserved, no
            // reify), a term/entity goal materializes to an occurrence exactly as
            // the former `term_body_to_nodes(reified)` did.
            let mut body_nodes: Vec<Rc<NodeOccurrence>> = Vec::with_capacity(goals.len());
            for g in &goals {
                body_nodes.push(self.goal_value_to_node(g)?);
            }
            self.assert_rule_debruijn_with_nodes(head, body_nodes, rule_sort, domain, None);
            self.synth_rule_memo.insert(key, synth_sym);
        }
        Ok(Value::term(head))
    }

    /// Collect a goal `view`'s free `Var::Global`s in first-occurrence order, the
    /// head twin of [`Self::append_synth_key`] (WI-678). It walks the IDENTICAL
    /// `TermView` traversal — head, then positional children, then named children —
    /// so every Global the key encodes as `Var(pos)` is collected here at exactly
    /// that `pos`. Keeping the two on ONE shared traversal makes the WI-169
    /// walk-parity invariant hold by construction (rather than by two collectors
    /// happening to agree): a Global the key would emit can never be missing from
    /// `free_vars`, so the `debug_assert` there is a redundant backstop, and a var
    /// the traversal does NOT reach (a Rigid/DeBruijn constant, or a Global living
    /// only in an occurrence's type-position / pattern field that `TermView` does
    /// not expose) is uniformly absent from both — never a head param, and closed
    /// as a body-local De Bruijn var off the stored occurrence instead.
    fn collect_goal_view_vars<V: TermView>(
        &self,
        view: &V,
        vars: &mut Vec<VarId>,
        seen: &mut std::collections::HashSet<u32>,
    ) {
        match view.head(self) {
            ViewHead::Functor { functor: Some(_), pos_arity, .. } => {
                for i in 0..pos_arity {
                    match view.pos_arg(self, i) {
                        Some(child) => self.collect_goal_view_vars(&child, vars, seen),
                        None => debug_assert!(false, "{}", VIEW_ARITY_DESYNC),
                    }
                }
                for name in view.named_keys(self) {
                    match view.named_arg(self, name) {
                        Some(child) => self.collect_goal_view_vars(&child, vars, seen),
                        None => debug_assert!(false, "{}", VIEW_ARITY_DESYNC),
                    }
                }
            }
            ViewHead::Var(Var::Global(vid)) => {
                if seen.insert(vid.raw()) {
                    vars.push(vid);
                }
            }
            // Every non-`Global` head — a `Rigid`/`DeBruijn` constant, a literal /
            // ref / ident leaf, a functor-less aggregate, an opaque carrier — binds
            // no synth head parameter. `append_synth_key` emits a corresponding
            // non-`Var` token for each, so the two walks stay in lockstep.
            _ => {}
        }
    }

    /// WI-169: append `view`'s structural fingerprint to `out` (see [`SynthKey`]).
    /// `free_vars` is the body's free Globals in first-occurrence order; a Global
    /// is keyed by its position there (De Bruijn-style), which erases the
    /// query-specific `VarId` while preserving variable sharing. A pre-order walk
    /// over interned symbols / literals / positions only — no term allocation and
    /// no `TermId` slot identity, so the resulting key is stable for the KB's
    /// lifetime.
    ///
    /// WI-678: carrier-agnostic — reads structure through [`TermView`], so a goal
    /// rides as a hash-consed `TermId` (a `Value::Term`), a `Value::Entity`, or a
    /// reflect-`Expr` occurrence (`Value::Node`) and produces the SAME key. This is
    /// byte-identical to the former `TermId`-only walk: a `Term::Fn` reads as a
    /// `ViewHead::Functor` with its stored (canonical) child order; an occurrence
    /// reads as its `Term::Fn` twin's head with the same child order (WI-425); a
    /// 0-ary constructor reads as `Ref` under both carriers (WI-436, canonicalized
    /// at `alloc`). Named children are walked in `named_keys` (carrier-stored)
    /// order — matching the term path, which reads `Term::Fn.named_args` in that
    /// same stored order (this walk is NOT the sorted `goal_fingerprint`). The old
    /// path's reify of a `Value::Node` goal (`occ_build_fn`) does NOT re-sort — it
    /// preserves the occurrence's named slice order — so the former reified-`Node`
    /// key used that identical order; there is no term-vs-occurrence sort skew here.
    fn append_synth_key<V: TermView>(&self, view: &V, free_vars: &[VarId], out: &mut Vec<SynthKey>) {
        match view.head(self) {
            // A functor application (`Term::Fn` / `Value::Entity` / an
            // Apply/Constructor occurrence). Positional children inline, each named
            // child prefixed by `Named`, and a closing `EndFn` — so the node (and
            // its named-arg section) is self-delimiting and the stream stays
            // injective.
            ViewHead::Functor { functor: Some(functor), pos_arity, .. } => {
                out.push(SynthKey::Functor(functor));
                for i in 0..pos_arity {
                    match view.pos_arg(self, i) {
                        Some(child) => self.append_synth_key(&child, free_vars, out),
                        None => debug_assert!(false, "{}", VIEW_ARITY_DESYNC),
                    }
                }
                for name in view.named_keys(self) {
                    out.push(SynthKey::Named(name));
                    match view.named_arg(self, name) {
                        Some(child) => self.append_synth_key(&child, free_vars, out),
                        None => debug_assert!(false, "{}", VIEW_ARITY_DESYNC),
                    }
                }
                out.push(SynthKey::EndFn);
            }
            ViewHead::Const(lit) => out.push(SynthKey::Lit(lit)),
            ViewHead::Var(Var::Global(vid)) => match free_vars.iter().position(|v| *v == vid) {
                Some(pos) => out.push(SynthKey::Var(pos as u32)),
                None => {
                    // Walk-parity invariant: `collect_goal_view_vars` collects
                    // `free_vars` via this EXACT `TermView` traversal, so every
                    // Global reached here is present by construction. A miss would
                    // mean the two walks desynced — scream in debug; in release key
                    // by raw id so distinct vars still never collapse (correct, just
                    // no memo hit).
                    debug_assert!(
                        false,
                        "WI-169: body Global {} missing from free_vars — \
                         collect_goal_view_vars/append_synth_key walk parity broken",
                        vid.raw()
                    );
                    out.push(SynthKey::RawVar(vid.raw()));
                }
            },
            ViewHead::Var(Var::DeBruijn(i)) => out.push(SynthKey::DeBruijnVar(i)),
            ViewHead::Var(Var::Rigid(vid)) => out.push(SynthKey::Rigid(vid.raw())),
            ViewHead::Ref(s) => out.push(SynthKey::Ref(s)),
            ViewHead::Ident(s) => out.push(SynthKey::Ident(s)),
            ViewHead::Bottom => out.push(SynthKey::Bottom),
            // A 0-ary constructor reads as `Ref` (WI-436), so `functor: None` here
            // is a functor-less aggregate (`Value::Tuple`/`Unit`) and `Opaque` a
            // runtime carrier (Closure/Stream/…). Neither is a valid goal shape —
            // `lower_leaf`/`alloc_from_value` reject them upstream — so this is
            // unreachable; scream in debug. In release a benign `Bottom` keeps the
            // key well-formed: the body is re-materialized from the same goals, so
            // a degraded key at worst forgoes a memo hit, never an unsound reuse.
            ViewHead::Functor { functor: None, .. } | ViewHead::Opaque => {
                debug_assert!(
                    false,
                    "WI-678: non-goal carrier (aggregate/opaque) reached synth body key"
                );
                out.push(SynthKey::Bottom);
            }
        }
    }

    /// Reduce a lowered branch to a single goal: single-goal verbatim,
    /// multi-goal via `synthesize_conjunction_rule`, empty rejected because
    /// the trivial-collapse semantics (empty body succeeds → wrapping
    /// disjunction unconditionally true / wrapping negation unconditionally
    /// false) is almost always a caller bug rather than intent.
    /// Carrier-neutral single-goal coercion (WI-513): collapse a goal list into
    /// one goal `Value` for a `not`/`or` wrapper. A single goal passes through as
    /// its `Value` (Term OR occurrence Node); multiple goals synthesize a fresh
    /// `_synth_N(?vars) :- goals` conjunction-rule head, returned as a
    /// `Value::Term`. WI-678: the goals stay `Value`s all the way into
    /// `synthesize_conjunction_rule` (no reify-to-`TermId` here — an occurrence
    /// goal never round-trips). Empty is rejected (almost always a caller bug).
    fn coerce_to_single_goal_value(
        &mut self,
        goals: Vec<Value>,
        empty_err: &'static str,
    ) -> Result<Value, LowerError> {
        match goals.len() {
            0 => Err(LowerError::NotYetImplemented(empty_err)),
            1 => Ok(goals.into_iter().next().unwrap()),
            _ => self.synthesize_conjunction_rule(goals),
        }
    }

    /// Materialize a goal `Value` as an occurrence for a synthesized rule's body
    /// (WI-678). A `Value::Node` occurrence is used DIRECTLY — no reify — which is
    /// the round-trip this cleanup removes (and preserves the occurrence's
    /// spans/types). A term/entity goal has no occurrence source, so it reifies to
    /// a `TermId` and materializes to an occurrence exactly as the former
    /// `term_body_to_nodes(goal_value_to_term(g))` chain did — including the
    /// pre-existing limitation that a builtin-wrapper entity over a BARE occurrence
    /// child (`not(occ)`, from a negated single occurrence goal) cannot reify
    /// (`alloc_from_value` rejects a `Value::Node` child) and surfaces the same
    /// `LowerError` the term path raised. This materialization runs only on a memo
    /// MISS (see the caller's `if fresh`), so that error — like the whole body
    /// build — is bounded to once per distinct multi-goal body.
    fn goal_value_to_node(&mut self, v: &Value) -> Result<Rc<NodeOccurrence>, LowerError> {
        match v {
            Value::Node(occ) => Ok(Rc::clone(occ)),
            other => {
                let t = self.goal_value_to_term(other)?;
                Ok(super::node_occurrence::materialize_from_handle(self, t))
            }
        }
    }

    /// Reify a goal `Value` to a hash-consed `TermId` at a genuine term boundary
    /// (the multi-goal conjunction-rule synthesis). A `Value::Node` occurrence
    /// materializes via `occurrence_to_term`; every other carrier goes through
    /// `alloc_from_value` (loud on a non-goal carrier).
    fn goal_value_to_term(&mut self, v: &Value) -> Result<TermId, LowerError> {
        match v {
            Value::Node(occ) => Ok(super::node_occurrence::occurrence_to_term(self, occ)),
            other => self.alloc_from_value(other),
        }
    }

    /// Build a builtin-goal `Value` `functor(args...)` as a `Value::Entity`
    /// (WI-513) — used for the `not`/`or` wrappers `lower_query` synthesizes. The
    /// entity carrier keeps the wrapped goals carrier-faithful (a `Value::Node`
    /// occurrence stays an occurrence), and the resolver classifies the builtin
    /// by reading `functor` through `TermView` (`get_builtin_view`).
    pub(crate) fn make_goal_value(&mut self, functor: Symbol, args: Vec<Value>) -> Value {
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
    /// [`Self::lower_leaf`]: an occurrence (`Value::Node`) stays an occurrence
    /// goal (resolves via `query_view`, preserving WI-518), every other carrier
    /// reifies to a canonical `Value::Term`. This is the SINGLE lowerer shared
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
    ///   or `[not(_synth_N(?vars))]` for multi-goal bodies — the synthesized
    ///   rule is `_synth_N(?vars) :- inner_goals` (proposal 033 §M4 / WI-076).
    ///   Empty inner is rejected as it almost always indicates a caller bug.
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

    /// Lower a single goal-atom leaf carrier-neutrally (WI-513). An occurrence
    /// (`Value::Node`) is kept as-is — it resolves as an occurrence goal via
    /// `query_view` (WI-518) and must not be reified (reifying would discard its
    /// source spans, and `alloc_from_value` rejects it anyway). Every other
    /// carrier reifies to a canonical `Value::Term` via `alloc_from_value`,
    /// which also surfaces a non-goal carrier (Closure/Stream/…) loudly.
    pub(crate) fn lower_leaf(&mut self, v: &Value) -> Result<Value, LowerError> {
        match v {
            Value::Node(_) => Ok(v.clone()),
            other => Ok(Value::term(self.alloc_from_value(other)?)),
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
        let functor = super::term_view::TermView::head(q, self).functor_sym()
            .ok_or_else(|| LowerError::NotALogicalQuery { got: q.type_name().into() })?;

        // `empty_query` has no fields, handle up-front.
        if Some(functor) == syms.empty_query {
            return Ok(Vec::new());
        }

        if Some(functor) == syms.pattern_query {
            let term_v = self.lq_field(q, syms.term)
                .ok_or(LowerError::MissingField {
                    entity: "pattern_query", field: "term",
                })?;
            return Ok(vec![self.lower_leaf(&term_v)?]);
        }

        if Some(functor) == syms.conjunction {
            let left = self.lq_field(q, syms.left).ok_or(LowerError::MissingField {
                entity: "conjunction", field: "left",
            })?;
            let right = self.lq_field(q, syms.right).ok_or(LowerError::MissingField {
                entity: "conjunction", field: "right",
            })?;
            let mut goals = self.lower_query_with(&left, syms)?;
            goals.extend(self.lower_query_with(&right, syms)?);
            return Ok(goals);
        }

        if Some(functor) == syms.guarded {
            let inner = self.lq_field(q, syms.query).ok_or(LowerError::MissingField {
                entity: "guarded", field: "query",
            })?;
            let cond = self.lq_field(q, syms.condition).ok_or(LowerError::MissingField {
                entity: "guarded", field: "condition",
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
            let sort_v = self.lq_field(q, syms.sort).ok_or(LowerError::MissingField {
                entity: "sort_query", field: "sort",
            })?;
            let sort_sym = crate::eval::eval::value_functor(self, &sort_v)
                .ok_or_else(|| LowerError::NotASortReference {
                    got: sort_v.type_name().to_string(),
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
            let inner = self.lq_field(q, syms.query).ok_or(LowerError::MissingField {
                entity: "negation", field: "query",
            })?;
            let inner_goals = self.lower_query_with(&inner, syms)?;
            let not_sym = syms.not.ok_or(LowerError::NotYetImplemented(
                "negation without loaded anthill.reflect.not",
            ))?;
            let arg = self.coerce_to_single_goal_value(
                inner_goals,
                "negation of empty_query (semantically `false`)",
            )?;
            return Ok(vec![self.make_goal_value(not_sym, vec![arg])]);
        }

        // `or` is the rule-lifted form of push_choice; no extra lifting needed.
        // Multi-goal branches synthesize a fresh conjunction-rule head
        // (proposal 033 §M4 / WI-076).
        if Some(functor) == syms.disjunction {
            let left = self.lq_field(q, syms.left).ok_or(LowerError::MissingField {
                entity: "disjunction", field: "left",
            })?;
            let right = self.lq_field(q, syms.right).ok_or(LowerError::MissingField {
                entity: "disjunction", field: "right",
            })?;
            let l_goals = self.lower_query_with(&left, syms)?;
            let r_goals = self.lower_query_with(&right, syms)?;
            let or_sym = syms.or.ok_or(LowerError::NotYetImplemented(
                "disjunction without loaded anthill.kernel.or",
            ))?;
            let empty_msg = "disjunction with empty_query branch (empty branch trivially succeeds)";
            // `or` lowers to the stdlib rule `or(?a, ?b) :- push_choice(?a, ?b)`,
            // and push_choice's arg extraction (`resolve_push_choice_args`) is
            // term-based (`kb.walk` → `TermId`). So the `or` wrapper must be a
            // hash-consed `Term::Fn`, not a carrier-neutral `Value::Entity` — a
            // `Value::Entity` branch arg would not flow through push_choice (a
            // nested `or` branch would be silently lost). Disjunction is an
            // eval-side form whose branches are always reifiable goals (never
            // occurrences), so reifying each branch to a `TermId` here is sound.
            let l_val = self.coerce_to_single_goal_value(l_goals, empty_msg)?;
            let r_val = self.coerce_to_single_goal_value(r_goals, empty_msg)?;
            let l = self.goal_value_to_term(&l_val)?;
            let r = self.goal_value_to_term(&r_val)?;
            let goal = self.terms.alloc(Term::Fn {
                functor: or_sym,
                pos_args: SmallVec::from_slice(&[l, r]),
                named_args: SmallVec::new(),
            });
            return Ok(vec![Value::term(goal)]);
        }

        // Projection / limit are wrappers over the inner stream. Flatten
        // to the inner query's goals; the caller is responsible for
        // applying projection/limit semantics on the resulting solution
        // sequence — the resolver itself has nothing to do differently.
        if Some(functor) == syms.projected || Some(functor) == syms.limited {
            let inner = self.lq_field(q, syms.query).ok_or(LowerError::MissingField {
                entity: "projected/limited", field: "query",
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

    /// WI-169 injectivity: the structural memo key's named-arg section must be
    /// self-delimiting. `f(g(?x), k: ?v)` (where `k:?v` is f's named arg) and
    /// `f(g(?x, k: ?v))` (where `k:?v` is g's) differ ONLY in that nesting; a
    /// non-self-delimiting encoding serialized both identically and would
    /// collapse them onto one synth rule → wrong query results. The `EndFn`
    /// close marker keeps them distinct.
    #[test]
    fn synth_key_named_section_is_self_delimiting() {
        let mut kb = KnowledgeBase::new();
        let f = kb.intern("f");
        let g = kb.intern("g");
        let k = kb.intern("k");
        let x_sym = kb.intern("x");
        let v_sym = kb.intern("v");
        let xid = kb.fresh_var(x_sym);
        let vid = kb.fresh_var(v_sym);
        let vx = kb.alloc(Term::Var(Var::Global(xid)));
        let vv = kb.alloc(Term::Var(Var::Global(vid)));

        let mk = |kb: &mut KnowledgeBase,
                  functor,
                  pos: &[TermId],
                  named: &[(Symbol, TermId)]| {
            kb.alloc(Term::Fn {
                functor,
                pos_args: SmallVec::from_slice(pos),
                named_args: SmallVec::from_slice(named),
            })
        };

        // A: f(g(?x), k: ?v) — k:?v belongs to f.
        let g_x = mk(&mut kb, g, &[vx], &[]);
        let a = mk(&mut kb, f, &[g_x], &[(k, vv)]);
        // B: f(g(?x, k: ?v)) — k:?v belongs to g.
        let g_xk = mk(&mut kb, g, &[vx], &[(k, vv)]);
        let b = mk(&mut kb, f, &[g_xk], &[]);

        let free = [xid, vid];
        let (mut ka, mut kb_) = (Vec::new(), Vec::new());
        kb.append_synth_key(&a, &free, &mut ka);
        kb.append_synth_key(&b, &free, &mut kb_);
        assert_ne!(ka, kb_, "pos/named nesting must produce distinct keys");

        // Canonicalization: the SAME shape as `a` built with FRESH vars must
        // produce an IDENTICAL key (rename-invariance — the dedup property).
        let x2 = kb.fresh_var(x_sym);
        let v2 = kb.fresh_var(v_sym);
        let vx2 = kb.alloc(Term::Var(Var::Global(x2)));
        let vv2 = kb.alloc(Term::Var(Var::Global(v2)));
        let g_x2 = mk(&mut kb, g, &[vx2], &[]);
        let a2 = mk(&mut kb, f, &[g_x2], &[(k, vv2)]);
        let mut ka2 = Vec::new();
        kb.append_synth_key(&a2, &[x2, v2], &mut ka2);
        assert_eq!(ka, ka2, "same shape with fresh vars must produce an identical key");
    }

    /// WI-678 regression: a Global living ONLY in an occurrence goal's
    /// type-position field (`p[T = ?b](?a)`) must NOT become a synth head
    /// parameter. `collect_goal_view_vars` (head params) and `append_synth_key`
    /// (memo key) both read through `TermView`, which does not expose `type_args`,
    /// so `?b` is uniformly absent from both — head arity and the key positions
    /// stay in lockstep. The type-arg-AWARE `collect_value_head_vars` (the right
    /// tool for a STORED rule, where `?b` must be closed as a body-local var) would
    /// instead count `?b`; using it for the synth head — as the first draft did —
    /// inflated head arity past what the key encoded, so two bodies differing only
    /// in a type-arg var collided onto one synth rule with a mismatched arity.
    #[test]
    fn synth_head_ignores_type_position_only_var() {
        use crate::kb::node_occurrence::{Expr, NodeOccurrence};
        use crate::span::{SourceId, SourceSpan};
        let span = SourceSpan::new(SourceId::from_raw(0), 0, 0);

        let mut kb = KnowledgeBase::new();
        let p = kb.intern("p");
        let t_param = kb.intern("T");
        let (a_sym, b_sym) = (kb.intern("a"), kb.intern("b"));
        let (a, b) = (kb.fresh_var(a_sym), kb.fresh_var(b_sym));

        // `?a` as a positional-arg occurrence; `?b` only in the `[T = ?b]` type arg.
        let occ_a = NodeOccurrence::new_expr(Expr::Var(Var::Global(a)), span, None);
        let vb = Value::term(kb.alloc(Term::Var(Var::Global(b))));
        let goal = Value::Node(NodeOccurrence::new_expr(
            Expr::Apply {
                functor: p,
                pos_args: vec![occ_a],
                named_args: vec![],
                type_args: vec![(Some(t_param), vb)],
            },
            span,
            None,
        ));

        // Synth head params (the fix): ONLY the structural `?a` — `?b` is absent.
        let mut free_vars = Vec::new();
        let mut seen = std::collections::HashSet::new();
        kb.collect_goal_view_vars(&goal, &mut free_vars, &mut seen);
        assert_eq!(free_vars, vec![a], "type-position ?b must not be a synth head param");

        // The type-arg-aware stored-rule collector DOES see `?b` — confirming the
        // divergence the fix sidesteps (that collector stays correct for a stored
        // body, where `?b` is closed as a body-local De Bruijn var).
        let (mut occ_vars, mut occ_seen) = (Vec::new(), std::collections::HashSet::new());
        kb.collect_value_head_vars(&goal, &mut occ_vars, &mut occ_seen);
        assert_eq!(occ_vars, vec![a, b], "occurrence collector counts the type-arg var");

        // The memo key references only `Var(0)` (=`?a`) and never the `RawVar`
        // fallback: key positions and `free_vars` are in lockstep, no arity gap.
        let mut key = Vec::new();
        kb.append_synth_key(&goal, &free_vars, &mut key);
        assert!(
            key.iter().all(|t| !matches!(t, SynthKey::RawVar(_))),
            "no Global escaped free_vars: {key:?}"
        );
        assert!(
            key.iter().any(|t| matches!(t, SynthKey::Var(0))),
            "?a keyed at position 0: {key:?}"
        );
        assert!(
            key.iter().all(|t| !matches!(t, SynthKey::Var(pos) if *pos >= free_vars.len() as u32)),
            "every keyed Var indexes a real free-var slot: {key:?}"
        );
    }
}
